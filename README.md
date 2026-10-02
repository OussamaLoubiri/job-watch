# job-watch

Finds alternance / CDI / CDD offers for AI & data job titles (Welcome to the Jungle,
JobTeaser, HelloWork), keeps a running tracker in `offers.csv`, and builds a
filterable HTML page where you can mark offers as *Applied* or *Not interested*.

## Setup

Requires **Python 3.11+**.

```bash
pip install requests
```

Then edit `jobs_config.toml`: put your [Serper](https://serper.dev) key in `api_key`,
and adjust job titles, cities, sites and HelloWork pages. Every setting is commented
in the file. Keep it private (`chmod 600 jobs_config.toml`); it is git-ignored.

## Run

| Command | Serper credits | What it does |
|---|---|---|
| `python3 job_search.py` | ~168 | Full run: Google searches on all sites + HelloWork pages |
| `python3 job_search.py --offline` | **0** | Only the HelloWork pages listed in `[[hellowork_pages]]` |
| `python3 job_search.py --only hellowork` | per site | Only the sites whose name contains the text |
| `python3 job_search.py --serve` | **0** | Opens the tracker in your browser; the Applied / Not interested buttons save to `offers.csv`, and the **Search** buttons (free / full / one site) start a run from the page. Ctrl+C to stop |
| `python3 job_search.py --html-only` | **0** | Rebuilds `reports/offers.html` from `offers.csv` |

On Windows, use `py` instead of `python3`.

A good rhythm: `--offline` daily, a full run once or twice a week (searches look back
`days` days, and offers already seen are never shown twice).

## Files

| File | |
|---|---|
| `offers.csv` | Every offer ever found + your `status` / `applied_on` / `notes`. Edits you make are kept |
| `reports/offers.html` | The tracker page (read-only when opened directly; use `--serve` to edit) |
| `reports/jobs_<date>.txt` | New offers of the day, priority cities first |
| `report_template.html` | Template the HTML page is built from |

## Notes

- `--serve` listens on `127.0.0.1` only. If `offers.csv` is open in Excel (Windows),
  close it before clicking a button.
- The Serper credit count of a run is printed first: `Running N searches ...`.
