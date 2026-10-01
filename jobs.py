#!/usr/bin/env python3
"""
jobs.py - Daily job watcher (alternance / CDI).

Reads its settings from jobs_config.toml (API key, search window, sites,
job titles, location, contract types), runs plain-keyword Google searches
through the Serper.dev API, then cleans the results:
  - drops links that aren't on the configured sites or aren't offer pages
  - counts language variants of the same offer (/fr/, /en/, ...) only once
  - keeps only offers whose title matches one of the job titles
  - extracts company, city, contract type, remote and posting date
For sites with `expand = "hellowork"` it also opens the HelloWork pages Google
returned (directly, no Serper credits): drops offers marked as expired and
collects the "similar offers" cards listed on those pages.

Outputs:
  offers.csv             running tracker of every offer ever found (also the
                         dedup memory). Add your own status/notes, they are kept.
  reports/offers.html    filterable page over the whole tracker
  reports/jobs_<date>.txt  today's new offers, grouped (also sent to Telegram)

Setup:
    pip install requests
    edit jobs_config.toml (put your Serper key in api_key), then:
    chmod 600 jobs_config.toml
    # optional Telegram notifications:
    export TELEGRAM_BOT_TOKEN="123:abc"
    export TELEGRAM_CHAT_ID="123456789"

Run:
    python3 jobs.py                     # uses jobs_config.toml next to the script
    python3 jobs.py other_config.toml   # or another config file
    python3 jobs.py --only hellowork    # only sites whose name contains "hellowork"
    python3 jobs.py --html-only         # rebuild reports/offers.html, no searches
"""

import argparse
import csv
import html
import json
import os
import re
import sys
import time
import tomllib
import unicodedata
from collections import Counter, defaultdict
from datetime import date, datetime, timedelta
from pathlib import Path
from urllib.parse import urljoin, urlparse

import requests

# ---------------------------------------------------------------------------
# Configuration
# ---------------------------------------------------------------------------

DEFAULT_CONFIG = Path(__file__).with_name("jobs_config.toml")
OFFERS_CSV = Path(__file__).with_name("offers.csv")
HTML_TEMPLATE = Path(__file__).with_name("report_template.html")
REPORT_DIR = Path(__file__).with_name("reports")

SERPER_URL = "https://google.serper.dev/search"

CSV_FIELDS = [
    "found", "posted", "contract", "job", "matched", "title", "company", "city",
    "country", "remote", "salary", "site", "source", "status", "notes", "url",
]

# Direct page fetches (HelloWork expansion) identify themselves honestly
PAGE_HEADERS = {
    "User-Agent": "Mozilla/5.0 (X11; Linux x86_64) jobs.py personal job watcher",
    "Accept-Language": "fr-FR,fr;q=0.9",
}

# Checked in order: an offer titled "Stage / Alternance" counts as Alternance.
CONTRACT_RULES = [
    ("Alternance", ["alternance", "alternant", "alternante", "apprenti", "apprentie",
                    "apprentissage", "apprentice", "apprenticeship", "work study",
                    "contrat pro", "contrat de professionnalisation"]),
    ("Stage", ["stage", "stagiaire", "intern", "internship", "trainee"]),
    ("CDI", ["cdi"]),
    ("CDD", ["cdd"]),
    ("Freelance", ["freelance", "independant"]),
]
CONTRACT_ORDER = [name for name, _ in CONTRACT_RULES] + ["Inconnu"]

REMOTE_RULES = [
    ("Remote", ["full remote", "teletravail complet", "100 remote", "remote"]),
    ("Hybride", ["hybride", "hybrid", "teletravail"]),
]

# Hosts whose first subdomain is the company (acme.teamtailor.com -> acme)
COMPANY_SUBDOMAIN_HOSTS = ["myworkdayjobs.com", "teamtailor.com", "recruitee.com", "jobs.personio.com"]
# Hosts whose first path segment is the company (jobs.lever.co/acme/...)
COMPANY_PATH_HOSTS = ["jobs.lever.co", "jobs.ashbyhq.com", "jobs.smartrecruiters.com"]

LANG_SEGMENT = re.compile(r"[a-z]{2}(-[a-zA-Z]{2})?")


def norm(text: str) -> str:
    """Lowercase, strip accents, collapse punctuation to single spaces, pad with spaces
    so that ' term ' substring checks behave as whole-word matches."""
    text = unicodedata.normalize("NFKD", text or "")
    text = "".join(c for c in text if not unicodedata.combining(c))
    return " " + re.sub(r"[^a-z0-9]+", " ", text.lower()).strip() + " "


def has_term(haystack: str, term: str) -> bool:
    term = norm(term).strip()
    return bool(term) and f" {term} " in haystack


def date_filter(days: int) -> str:
    # Google "tbs" date filter: "qdr:d" = past 24h, "qdr:d7" = past 7 days, "" = none.
    # Permanent pages (e.g. HelloWork category listings) rarely pass a date filter.
    if days < 0:
        raise ValueError("days must be >= 0")
    return "" if days == 0 else "qdr:d" if days == 1 else f"qdr:d{days}"


def load_config(path: Path) -> dict:
    with path.open("rb") as f:
        cfg = tomllib.load(f)

    api_key = str(cfg.get("api_key", "")).strip()
    if not api_key or api_key == "PUT-YOUR-SERPER-KEY-HERE":
        raise ValueError(f"set api_key in {path}")

    days = int(cfg.get("days", 7))
    if days < 1:
        raise ValueError("days must be >= 1")

    location = cfg.get("location", {})
    jobs = cfg.get("jobs", {})
    titles = jobs.get("titles", [])
    synonyms = jobs.get("synonyms", {})
    sites = cfg.get("sites", [])
    contracts = cfg.get("contract_types", [])
    filters = cfg.get("filters", {})
    if not titles or not sites or not contracts:
        raise ValueError("need at least one job title, one site and one contract type")
    for t in jobs.get("search_synonyms", []):
        if t not in titles:
            raise ValueError(f"search_synonyms: {t!r} is not one of the job titles")
    for site in sites:
        if not site.get("domains"):
            raise ValueError(f"site {site.get('name', '?')!r} has no domains")
        site["offer_res"] = [re.compile(p) for p in site.get("offer_paths", [])]
        # Per-site date filter overrides the global one; 0 = no date filter
        site["tbs"] = date_filter(int(site["days"])) if "days" in site else date_filter(days)

    cities = location.get("cities") or []
    priority = location.get("priority_cities") or [c for c in cities if c]
    known_cities = list(dict.fromkeys(location.get("known_cities", []) + [c for c in cities if c] + priority))

    hw_pages = []
    for i, p in enumerate(cfg.get("hellowork_pages", []), 1):
        url = str(p.get("url", "")).strip()
        if not url:
            raise ValueError(f"hellowork_pages #{i} has no url")
        if not on_allowed_domain(url_parts(url)[0], ["hellowork.com"]):
            raise ValueError(f"hellowork_pages #{i}: {url} is not a hellowork.com URL")
        if "?" in url:
            raise ValueError(f"hellowork_pages #{i}: {url} contains '?', which HelloWork's robots.txt forbids")
        if p.get("enabled", True):
            hw_pages.append({"name": p.get("name") or url, "url": url})

    return {
        "api_key": api_key,
        "num": int(cfg.get("results_per_query", 20)),
        "country": location.get("country", ""),
        "country_code": location.get("country_code", "fr"),
        # [""] = one pass with no city, i.e. the whole country
        "cities": cities or [""],
        "known_cities": known_cities,
        "priority_cities": priority,
        "titles": titles,
        # (job title, term) pairs; each title also matches its own name
        "terms": [(t, term) for t in titles for term in [t] + synonyms.get(t, [])],
        # Words actually sent to Google: each title, plus the synonyms of titles
        # listed in search_synonyms
        "search_terms": [term for t in titles for term in
                         [t] + (synonyms.get(t, []) if t in jobs.get("search_synonyms", []) else [])],
        "sites": sites,
        "contracts": contracts,
        "require_title_match": bool(filters.get("require_title_match", True)),
        "hide_contracts": {c.lower() for c in filters.get("hide_contracts", [])},
        "hellowork_pages": hw_pages,
    }


def build_searches(cfg: dict) -> list[tuple[str, dict]]:
    # One plain-keyword query per site x contract x search term x city (search terms =
    # job titles + synonyms of titles in search_synonyms). Serper's free plan rejects
    # operators (site:, OR, quotes), so the site restriction is applied locally on
    # each result's domain instead.
    searches = []
    for site in cfg["sites"]:
        for contract in cfg["contracts"]:
            for title in cfg["search_terms"]:
                for city in cfg["cities"]:
                    words = [site.get("keyword", ""), contract, title, city, cfg["country"]]
                    query = " ".join(w for w in words if w)
                    searches.append((query, site))
    return searches


# ---------------------------------------------------------------------------
# Result cleaning and field extraction
# ---------------------------------------------------------------------------

def url_parts(url: str) -> tuple[str, list[str]]:
    p = urlparse(url)
    host = (p.hostname or "").lower().removeprefix("www.")
    segs = [s for s in p.path.split("/") if s]
    # Drop a leading language segment (/fr/, /en-GB/, /fr-fr/) so translations
    # of the same offer collapse to one
    if segs and LANG_SEGMENT.fullmatch(segs[0]):
        segs = segs[1:]
    return host, segs


def offer_key(url: str) -> str:
    # Dedup key: host + path without language segment, query string or fragment
    host, segs = url_parts(url)
    return (host + "/" + "/".join(segs)).lower()


def on_allowed_domain(host: str, domains: list[str]) -> bool:
    return any(host == d or host.endswith("." + d) for d in domains)


def is_offer_page(url: str, site: dict) -> bool:
    if not site["offer_res"]:
        return True
    path = urlparse(url).path
    return any(r.search(path) for r in site["offer_res"])


def pretty(slug: str) -> str:
    words = re.sub(r"[-_]+", " ", slug).strip()
    return words.title() if words.islower() else words


def extract_company(host: str, segs: list[str]) -> str:
    for marker in ("companies", "entreprises"):
        if marker in segs[:-1]:
            return pretty(segs[segs.index(marker) + 1])
    for base in COMPANY_SUBDOMAIN_HOSTS:
        if host.endswith("." + base):
            return pretty(host.split(".")[0])
    if host in COMPANY_PATH_HOSTS and segs:
        # SmartRecruiters adds digits to company ids (Ubisoft2, AECOM2)
        return pretty(re.sub(r"\d+$", "", segs[0]))
    return ""


def extract_city(host: str, segs: list[str], texts: list[str], known: list[str]) -> str:
    # Welcome to the Jungle ends job slugs with _<city>
    if host.endswith("welcometothejungle.com") and segs and "_" in segs[-1]:
        slug = segs[-1].rsplit("_", 1)[1]
        # Prefer the known spelling (clermont-ferrand -> Clermont-Ferrand)
        return next((c for c in known if norm(c) == norm(slug)), pretty(slug))
    for text in texts:  # most reliable first: title, then URL, then snippet
        for city in known:
            if has_term(text, city):
                return city
    return ""


def first_rule(rules: list, texts: list[str], default: str = "") -> str:
    for text in texts:
        for name, words in rules:
            if any(has_term(text, w) for w in words):
                return name
    return default


def match_jobs(text: str, terms: list[tuple[str, str]]) -> tuple[str, list[str]]:
    """Return (primary job, all matched jobs). The primary is the job whose
    matching term is longest, so 'Data Engineer' wins over 'Data'.
    A hit doesn't count when its term is only part of a longer hit for another job:
    in "Data Scientist NLP", 'data' sits inside 'data scientist', so the job is
    Data Scientist + NLP, not also Data."""
    hits = [(norm(term).strip(), job) for job, term in terms if has_term(text, term)]
    kept = [(t, job) for t, job in hits
            if not any(o_job != job and len(o) > len(t) and f" {t} " in f" {o} " for o, o_job in hits)]
    if not kept:
        return "", []
    primary = max(kept, key=lambda h: len(h[0]))[1]
    matched = list(dict.fromkeys(job for _, job in kept))
    return primary, matched


MONTHS = [("janv", 1), ("jan", 1), ("fev", 2), ("feb", 2), ("mars", 3), ("mar", 3),
          ("avr", 4), ("apr", 4), ("mai", 5), ("may", 5), ("juin", 6), ("jun", 6),
          ("juil", 7), ("jul", 7), ("aou", 8), ("aug", 8), ("sep", 9), ("oct", 10),
          ("nov", 11), ("dec", 12)]
RELATIVE_UNITS = {"min": 0, "minute": 0, "hour": 0, "heure": 0, "day": 1, "jour": 1,
                  "week": 7, "semaine": 7, "month": 30, "mois": 30}


def parse_posted(raw: str, today: date) -> str:
    """Best-effort conversion of Google's date ('3 days ago', 'il y a 2 jours',
    'Sep 28, 2026', '28 sept. 2026') to ISO. Unparsed values are returned as-is."""
    s = norm(raw).strip()
    if not s:
        return ""
    if s in ("yesterday", "hier"):
        return (today - timedelta(days=1)).isoformat()
    m = re.search(r"(\d+) (min|minute|hour|heure|day|jour|week|semaine|month|mois)", s)
    if m:
        return (today - timedelta(days=int(m.group(1)) * RELATIVE_UNITS[m.group(2)])).isoformat()
    m = re.fullmatch(r"(\d{1,2}) ([a-z]+) (\d{4})", s) or re.fullmatch(r"([a-z]+) (\d{1,2}) (\d{4})", s)
    if m:
        day_s, mon_s = (m.group(1), m.group(2)) if m.group(1).isdigit() else (m.group(2), m.group(1))
        month = next((n for prefix, n in MONTHS if mon_s.startswith(prefix)), None)
        if month:
            try:
                return date(int(m.group(3)), month, int(day_s)).isoformat()
            except ValueError:
                pass
    return raw.strip()


def rematch_rows(rows: list[dict], cfg: dict) -> int:
    """Recompute job/matched for offers already in the tracker, so changes to the
    matching rules, titles or synonyms also apply to old offers. Both columns are
    derived from title + URL only; user columns (status, notes, ...) are untouched.
    Returns how many rows changed."""
    changed = 0
    for r in rows:
        _, segs = url_parts(r.get("url", ""))
        job, matched = match_jobs(norm(r.get("title", "")) + norm(" ".join(segs)), cfg["terms"])
        if (job, ", ".join(matched)) != (r.get("job", ""), r.get("matched", "")):
            r["job"], r["matched"] = job, ", ".join(matched)
            changed += 1
    return changed


def build_offer(r: dict, site: dict, cfg: dict, today: date) -> dict:
    url = r.get("link", "")
    host, segs = url_parts(url)
    title = r.get("title", "") or "(no title)"
    t_title, t_url, t_snip = norm(title), norm(" ".join(segs)), norm(r.get("snippet", ""))
    job, matched = match_jobs(t_title + t_url, cfg["terms"])
    return {
        "found": today.isoformat(),
        "posted": parse_posted(r.get("date", ""), today),
        "contract": first_rule(CONTRACT_RULES, [t_title + t_url, t_snip], "Inconnu"),
        "job": job,
        "matched": ", ".join(matched),
        "title": title,
        "company": extract_company(host, segs),
        "city": extract_city(host, segs, [t_title, t_url, t_snip], cfg["known_cities"]),
        "country": cfg["country"],
        "remote": first_rule(REMOTE_RULES, [t_title + t_url + t_snip]),
        "salary": "",
        "site": site.get("name", host),
        "source": "Google",
        "status": "",
        "notes": "",
        "url": url,
    }


# ---------------------------------------------------------------------------
# HelloWork expansion: read the pages Google returned, directly on hellowork.com
# (robots.txt allows offer and listing pages for generic crawlers; it forbids the
# search page and any URL with a query string, which this never requests).
# ---------------------------------------------------------------------------

# Each "similar offer" card is an <a data-cy="offerTitle"> whose aria-label holds
# "Voir offre de <title> à <city>, chez <company>, pour un <contract>, avec un salaire de <salary>, en <time>"
HW_CARD = re.compile(r'<a\b[^>]*\bdata-cy="offerTitle"[^>]*>', re.S)
HW_ATTR = re.compile(r'([\w-]+)="([^"]*)"')
HW_OFFER_HREF = re.compile(r"/fr-fr/emplois/\d+\.html")
HW_EXPIRED = re.compile(r"n(?:'|’|&#x27;|&#39;)est plus disponible")
HW_POSTED = re.compile(r"il y a \d+ (?:minute|heure|jour|semaine|mois)s?|aujourd'hui|hier", re.I)


def parse_hellowork_card(aria: str, title_attr: str) -> dict:
    m = re.search(r", chez (.+?), pour une? ", aria)
    company = m.group(1) if m else ""
    # title attribute is "<title> - <company>"
    suffix = f" - {company}"
    title = title_attr[: -len(suffix)] if company and title_attr.endswith(suffix) else title_attr
    rest = aria.removeprefix(f"Voir offre de {title}")
    m = re.match(r" à (.+?), chez ", rest)
    city = re.sub(r"\s*-\s*\d{2,3}$", "", m.group(1)) if m else ""   # "Cergy - 95" -> "Cergy"
    city = re.sub(r"^(Paris|Lyon|Marseille) \d{1,2}(?:e|er)$", r"\1", city)  # "Paris 14e" -> "Paris"
    m = re.search(r", pour une? (.+?)(?:, avec un salaire de |, en |$)", aria)
    contract = m.group(1) if m else ""
    m = re.search(r", avec un salaire de (.+?)(?:, en |$)", aria)
    salary = m.group(1).replace(" ", " ") if m else ""
    return {"title": title, "company": company, "city": city, "contract": contract, "salary": salary}


def parse_hellowork_page(page: str, page_url: str) -> tuple[bool, list[dict]]:
    """Return (page says the offer expired, similar-offer cards on the page)."""
    expired = bool(HW_EXPIRED.search(page))
    anchors = list(HW_CARD.finditer(page))
    cards, seen = [], set()
    for i, a in enumerate(anchors):
        attrs = {k: html.unescape(v) for k, v in HW_ATTR.findall(a.group(0))}
        href = attrs.get("href", "")
        if not HW_OFFER_HREF.fullmatch(href) or href in seen:
            continue
        seen.add(href)
        card = parse_hellowork_card(attrs.get("aria-label", ""), attrs.get("title", ""))
        # "il y a 2 jours" sits in the card body, between this card's link and the next one
        end = anchors[i + 1].start() if i + 1 < len(anchors) else a.end() + 5000
        body = html.unescape(re.sub(r"<[^>]+>", " ", page[a.end():end]))
        posted = HW_POSTED.search(body)
        card["url"] = urljoin(page_url, href)
        card["posted"] = posted.group(0) if posted else ""
        cards.append(card)
    return expired, cards


def card_to_offer(card: dict, site: dict, cfg: dict, today: date, source: str) -> dict:
    r = {"link": card["url"], "title": card["title"], "snippet": "", "date": card["posted"]}
    offer = build_offer(r, site, cfg, today)
    # The card states these explicitly: trust them over guesses from the title
    if card["contract"]:
        offer["contract"] = first_rule(CONTRACT_RULES, [norm(card["contract"])], card["contract"])
    if card["company"]:
        offer["company"] = card["company"]
    if card["city"]:
        offer["city"] = next((c for c in cfg["known_cities"] if norm(c) == norm(card["city"])), card["city"])
    offer["salary"] = card["salary"]
    offer["source"] = source
    return offer


def fetch_page(url: str) -> str:
    resp = requests.get(url, headers=PAGE_HEADERS, timeout=20)
    resp.raise_for_status()
    return resp.text


# ---------------------------------------------------------------------------
# Storage and reports
# ---------------------------------------------------------------------------

def load_offers() -> tuple[list[dict], list[str], str]:
    """Read offers.csv, keeping any extra columns and the delimiter
    (LibreOffice/Excel in French locale may save it with ';')."""
    if not OFFERS_CSV.exists():
        return [], list(CSV_FIELDS), ","
    text = OFFERS_CSV.read_text(encoding="utf-8-sig")
    header = text.splitlines()[0] if text else ""
    delim = ";" if header.count(";") > header.count(",") else ","
    reader = csv.DictReader(text.splitlines(), delimiter=delim)
    fields = list(CSV_FIELDS) + [f for f in (reader.fieldnames or []) if f not in CSV_FIELDS]
    return list(reader), fields, delim


def save_offers(rows: list[dict], fields: list[str], delim: str) -> None:
    with OFFERS_CSV.open("w", encoding="utf-8-sig", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=fields, delimiter=delim, extrasaction="ignore")
        writer.writeheader()
        writer.writerows(rows)


def sort_offers(offers: list[dict], titles: list[str]) -> list[dict]:
    # Two stable sorts: newest posting first (unparsed/missing dates last),
    # then grouped by contract type and job title in config order
    def posted(o):
        return o["posted"] if re.fullmatch(r"\d{4}-\d{2}-\d{2}", o["posted"] or "") else ""

    def group(o):
        contract = CONTRACT_ORDER.index(o["contract"]) if o["contract"] in CONTRACT_ORDER else len(CONTRACT_ORDER)
        job = titles.index(o["job"]) if o["job"] in titles else len(titles)
        return (contract, job)

    return sorted(sorted(offers, key=posted, reverse=True), key=group)


def is_priority(o: dict, priority_cities: list[str]) -> bool:
    return any(norm(o.get("city", "")) == norm(c) for c in priority_cities)


def report_section(header: str, offers: list[dict], titles: list[str], with_contract: bool) -> list[str]:
    # Offers grouped by job title, under one "━━ HEADER (n)" banner
    lines = [f"━━ {header} ({len(offers)}) " + "━" * 40]
    groups = defaultdict(list)
    for o in sort_offers(offers, titles):
        groups[o["job"] or "Autre"].append(o)
    for job, items in groups.items():
        lines += ["", job]
        for o in items:
            parts = ([o["contract"]] if with_contract else []) + [
                o["company"], o["city"], o["remote"], o.get("salary", ""), o["posted"]]
            meta = " · ".join(x for x in parts if x)
            lines.append(f"  • {o['title']}" + (f"  [{meta}]" if meta else ""))
            lines.append(f"    {o['url']}")
    return lines + [""]


def text_report(new: list[dict], titles: list[str], today: str, priority_cities: list[str]) -> str:
    per_site = Counter(o["site"] for o in new)
    lines = [
        f"{len(new)} nouvelle(s) offre(s) - {today}",
        "  (" + " · ".join(f"{s} {n}" for s, n in per_site.most_common()) + ")",
        "",
    ]
    # Priority cities first (all contract types together), then the rest by contract
    prio = [o for o in new if is_priority(o, priority_cities)]
    if priority_cities:
        names = " · ".join(priority_cities)
        if prio:
            lines += report_section(f"★ PRIORITÉ {names}", prio, titles, with_contract=True)
        else:
            lines += [f"━━ ★ PRIORITÉ {names}: aucune nouvelle offre aujourd'hui", ""]
    rest = [o for o in new if o not in prio]
    for contract in CONTRACT_ORDER + sorted({o["contract"] for o in rest} - set(CONTRACT_ORDER)):
        offers = [o for o in rest if o["contract"] == contract]
        if offers:
            lines += report_section(contract.upper(), offers, titles, with_contract=False)
    return "\n".join(lines)


def write_html(rows: list[dict], cfg: dict, today: str) -> Path | None:
    if not HTML_TEMPLATE.exists():
        print(f"Warning: {HTML_TEMPLATE.name} missing, HTML report skipped.", file=sys.stderr)
        return None
    data = {
        "generated": datetime.now().strftime("%Y-%m-%d %H:%M"),
        "today": today,
        "titles": cfg["titles"],
        "contracts": CONTRACT_ORDER,
        "priority_cities": cfg["priority_cities"],
        "offers": rows,
    }
    # "</" escaped so an offer title can never close the <script> tag
    payload = json.dumps(data, ensure_ascii=False).replace("</", "<\\/")
    html = HTML_TEMPLATE.read_text(encoding="utf-8").replace("__OFFERS_DATA__", payload)
    out = REPORT_DIR / "offers.html"
    out.write_text(html, encoding="utf-8")
    return out


def search(query: str, cfg: dict, tbs: str) -> list[dict]:
    payload = {
        "q": query,
        "gl": cfg["country_code"],  # results from this country
        "hl": cfg["country_code"],  # interface language
        # Google currently returns 10 organic results whatever num asks for
        "num": cfg["num"],
    }
    if tbs:
        payload["tbs"] = tbs        # date filter
    headers = {"X-API-KEY": cfg["api_key"], "Content-Type": "application/json"}
    resp = requests.post(SERPER_URL, headers=headers, json=payload, timeout=30)
    resp.raise_for_status()
    return resp.json().get("organic", [])


def send_telegram(text: str) -> None:
    token = os.environ.get("TELEGRAM_BOT_TOKEN")
    chat_id = os.environ.get("TELEGRAM_CHAT_ID")
    if not token or not chat_id:
        return
    # Telegram messages are limited to 4096 chars: send in chunks
    for i in range(0, len(text), 4000):
        requests.post(
            f"https://api.telegram.org/bot{token}/sendMessage",
            json={"chat_id": chat_id, "text": text[i:i + 4000], "disable_web_page_preview": True},
            timeout=30,
        )




# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(description="Daily job watcher")
    p.add_argument("config", nargs="?", type=Path, default=DEFAULT_CONFIG, help="config file (TOML)")
    p.add_argument("--only", metavar="TEXT",
                   help="run only the sites whose name contains TEXT (case-insensitive), e.g. --only hellowork")
    p.add_argument("--html-only", action="store_true",
                   help="no searches, no page reads: just rebuild reports/offers.html from offers.csv "
                        "(after editing report_template.html, statuses or matching rules)")
    return p.parse_args()


def slug(text: str) -> str:
    # "Ingénieur IA" -> "ingenieur-ia", the form HelloWork uses in mot-cle_<slug>.html
    return norm(text).strip().replace(" ", "-")


def direct_pages(site: dict, cfg: dict) -> list[tuple[str, str, str]]:
    """HelloWork pages to open on every run, without going through Google, as
    (url, name, kind): the [[hellowork_pages]] entries ("configured"), plus one
    mot-cle_<title> page per contract x job title when auto_pages is on ("guess";
    guesses that don't exist just return 404 and are skipped quietly)."""
    pages = [(p["url"], p["name"], "configured") for p in cfg["hellowork_pages"]]
    if site.get("auto_pages", False):
        pages += [(f"https://www.hellowork.com/fr-fr/{slug(c)}/mot-cle_{slug(t)}.html",
                   f"mot-cle {t}", "guess")
                  for c in cfg["contracts"] for t in cfg["titles"]]
    unique = {}
    for url, name, kind in pages:
        unique.setdefault(offer_key(url), (url, name, kind))
    return list(unique.values())


def expand_pages(queue: list, pending: dict, known: set, new: list, stats: dict,
                 cfg: dict, today: date) -> None:
    """Open queued HelloWork pages: drop expired pending offers, collect the offer cards.
    Queue items are (priority, url, site, pending_key, source, kind); lower priority
    is read first. kind: "found" (Google result), "configured" ([[hellowork_pages]],
    a 404 there is worth a warning) or "guess" (auto_pages, a 404 is expected)."""
    queue.sort(key=lambda q: q[0])
    read = Counter()
    blocked = set()
    for _, url, site, pkey, source, kind in queue:
        name = site["name"]
        st = stats[name]
        if name in blocked or read[name] >= int(site.get("max_pages", 30)):
            st["pages skipped"] += 1
            continue
        if read[name]:
            time.sleep(float(site.get("page_delay", 1.5)))
        read[name] += 1
        try:
            page = fetch_page(url)
        except requests.RequestException as e:
            code = e.response.status_code if e.response is not None else None
            if kind == "guess" and code == 404:
                st["pages missing"] += 1
                continue
            if kind == "configured" and code in (404, 410):
                st["pages missing"] += 1
                print(f"Warning: HelloWork page {source.split(': ', 1)[-1]!r} no longer exists ({code}): {url}\n"
                      f"  -> fix or disable it in [[hellowork_pages]] in the config", file=sys.stderr)
                continue
            if code in (404, 410):
                # 410 Gone / 404: the offer was taken down. Google still lists it, but
                # it's dead: treat it like the "n'est plus disponible" banner.
                if pkey in pending:
                    del pending[pkey]
                    st["expired"] += 1
                else:
                    st["pages missing"] += 1
                continue
            st["page errors"] += 1
            print(f"Page fetch failed: {url}\n  -> {e}", file=sys.stderr)
            if code in (403, 429):
                # Blocked or rate-limited: stop hitting this site for the rest of the run
                blocked.add(name)
            continue
        st["pages read"] += 1

        expired, cards = parse_hellowork_page(page, url)
        if expired and pkey in pending:
            del pending[pkey]
            st["expired"] += 1
        for card in cards:
            st["cards found"] += 1
            key = offer_key(card["url"])
            if key in known:
                continue
            offer = card_to_offer(card, site, cfg, today, source)
            if cfg["require_title_match"] and not offer["job"]:
                continue
            if offer["contract"].lower() in cfg["hide_contracts"]:
                continue
            known.add(key)
            new.append(offer)
            st["cards kept"] += 1


def main() -> int:
    args = parse_args()
    try:
        cfg = load_config(args.config)
    except (OSError, tomllib.TOMLDecodeError, ValueError, re.error) as e:
        print(f"Error in config {args.config}: {e}", file=sys.stderr)
        return 1
    if args.only:
        cfg["sites"] = [s for s in cfg["sites"] if args.only.lower() in s["name"].lower()]
        if not cfg["sites"]:
            print(f"Error: no site name contains {args.only!r}", file=sys.stderr)
            return 1

    if args.html_only:
        # Offline: no Serper credits, no requests to job sites
        rows, fields, delim = load_offers()
        if n := rematch_rows(rows, cfg):
            save_offers(rows, fields, delim)
            print(f"Updated the job/matched columns of {n} tracked offer(s).", file=sys.stderr)
        REPORT_DIR.mkdir(exist_ok=True)
        html_path = write_html(rows, cfg, date.today().isoformat())
        if html_path:
            print(f"HTML report rebuilt from {OFFERS_CSV.name} ({len(rows)} offers): {html_path}", file=sys.stderr)
        return 0

    searches = build_searches(cfg)
    print(f"Running {len(searches)} searches (1 Serper credit each)...", file=sys.stderr)

    rows, fields, delim = load_offers()
    if n := rematch_rows(rows, cfg):
        print(f"Updated the job/matched columns of {n} tracked offer(s) to the current matching rules.",
              file=sys.stderr)
    known = {offer_key(r.get("url", "")) for r in rows}
    today = date.today()
    new = []
    # Per site: how many results came back and why each was dropped
    stats = defaultdict(Counter)
    # HelloWork pages to open after the searches, and the offers waiting on that check
    queue, queued, pending = [], set(), {}
    SIMILAR, LISTING, DIRECT = "HelloWork (offres similaires)", "HelloWork (liste via Google)", "HelloWork (page directe)"
    # Pages opened on every run regardless of what Google returns
    for site in cfg["sites"]:
        if site.get("expand") == "hellowork":
            for url, name, kind in direct_pages(site, cfg):
                queued.add(offer_key(url))
                queue.append((0.5, url, site, None, f"{DIRECT}: {name}", kind))

    for query, site in searches:
        try:
            results = search(query, cfg, site["tbs"])
        except requests.RequestException as e:
            # The status line alone doesn't say why; Serper puts the reason in the body
            body = e.response.text if e.response is not None else ""
            print(f"Search failed for: {query}\n  -> {e}\n  -> {body}", file=sys.stderr)
            continue

        st = stats[site["name"]]
        for r in results:
            st["returned"] += 1
            url = r.get("link", "")
            host, _ = url_parts(url)
            if not url or not on_allowed_domain(host, site["domains"]):
                st["other site"] += 1
                continue
            key = offer_key(url)
            if key in known:
                st["already seen"] += 1
                continue
            expandable = site.get("expand") == "hellowork" and host.endswith("hellowork.com")

            def enqueue(priority, source, pkey=None):
                if expandable and key not in queued:
                    queued.add(key)
                    queue.append((priority, url, site, pkey, source, "found"))

            # Pages read first: on-topic offers (needed for the expiry check), then the
            # direct pages, then listings Google found, then off-topic offers (their
            # similar offers rarely match)
            if not is_offer_page(url, site):
                st["listing page"] += 1
                enqueue(1, LISTING)
                continue
            offer = build_offer(r, site, cfg, today)
            if cfg["require_title_match"] and not offer["job"]:
                st["off-topic"] += 1
                enqueue(2, SIMILAR)
                continue
            if offer["contract"].lower() in cfg["hide_contracts"]:
                st["hidden contract"] += 1
                enqueue(1, SIMILAR)
                continue
            known.add(key)
            if expandable:
                pending[key] = offer
                enqueue(0, SIMILAR, key)
            else:
                new.append(offer)
                st["new"] += 1

    if queue:
        print(f"Reading {len(queue)} HelloWork page(s) directly (no Serper credits)...", file=sys.stderr)
        expand_pages(queue, pending, known, new, stats, cfg, today)
    # Pending offers that weren't found expired (or weren't read) are kept
    for offer in pending.values():
        new.append(offer)
        stats[offer["site"]]["new"] += 1

    print_stats(stats)

    rows.extend(new)
    save_offers(rows, fields, delim)
    REPORT_DIR.mkdir(exist_ok=True)
    html_path = write_html(rows, cfg, today.isoformat())

    if not new:
        print(f"[{today}] No new offers.")
    else:
        report = text_report(new, cfg["titles"], today.isoformat(), cfg["priority_cities"])
        print(report)
        (REPORT_DIR / f"jobs_{today}.txt").write_text(report, encoding="utf-8")
        send_telegram(report)

    print(f"Tracker: {OFFERS_CSV.name} ({len(rows)} offers)", file=sys.stderr)
    if html_path:
        print(f"HTML report: {html_path}", file=sys.stderr)
    return 0


def print_stats(stats: dict) -> None:
    cols = ["returned", "other site", "already seen", "listing page", "off-topic", "hidden contract",
            "new", "pages read", "expired", "cards found", "cards kept"]
    width = max([len(s) for s in stats] + [4])
    print("\n" + "site".ljust(width) + "".join(c.rjust(15) for c in cols), file=sys.stderr)
    for name, st in stats.items():
        print(name.ljust(width) + "".join(str(st[c]).rjust(15) for c in cols), file=sys.stderr)
    extra = {n: st for n, st in stats.items() if st["page errors"] or st["pages skipped"] or st["pages missing"]}
    for name, st in extra.items():
        print(f"{name}: {st['page errors']} page error(s), {st['pages skipped']} page(s) skipped (max_pages), "
              f"{st['pages missing']} page(s) not found (404/410: guessed mot-cle pages or removed listings, normal)", file=sys.stderr)
    print(file=sys.stderr)


if __name__ == "__main__":
    sys.exit(main())
