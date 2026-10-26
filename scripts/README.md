# scripts/

Run every script from the repository root. The entry points are in this folder; the helpers they call are in the subfolders.

## Entry points

| Script | What it does | Run by |
|---|---|---|
| `check-conventions.sh` | The text-only convention checks of CONTRIBUTING.md (layout, docstrings, axioms, layering, ...); `--staged LIST` runs the per-file rules only | CI, `.githooks/pre-commit` |
| `check-references.py` | The `references/` ledger: tables, links, BibTeX entries, counts, `experiments/paper/formalization-stats.json`; `--fix` rewrites stale counts | CI, pre-commit hook |
| `check-findings.py` | The CORA findings in the coverage tables: the departures table, every `cora-issue` note and its `experiments/paper/cora-bugs.json` entry | CI |
| `formalization-stats.py` | Regenerates the paper's formalization data (`experiments/paper/*.json`, `experiments/paper/latex/` figures and appendices); `--check` fails when stale | CI, `experiments/repeatability.sh`, by hand |
| `check-axioms.sh`, `check-axioms.lean` | Asks Lean which axioms the library's proofs use | CI |
| `check-demo.sh` | Runs `Examples/Demo.lean` and diffs against `expected/demo-expected.txt` | CI |
| `check-runcheck.sh` | Runs `lake exe runcheck` through the interpreter and diffs against `expected/runcheck-expected.txt` | CI |
| `review.py` | Picks a Lean file whose author block says `Reviewed: ---` and records the human review; `--status` counts the reviewed files | VS Code tasks, CI (`--status`) |
| `gl.py` | GitLab issue and merge-request client | by hand |

## Folders

| Folder | Contents | Run by |
|---|---|---|
| `conventions/` | The Python helpers of `check-conventions.sh` (one rule each, `check-*.py`), `satellites.py` (the unit of an algorithm and its theorem files, #227), `precommit-scope.py` (what a commit has to check), `find-python.sh` (finds a working Python 3.8+) | `check-conventions.sh`, the hook |
| `paper/` | Generators behind `formalization-stats.py` and the ledger: `errors-table.py`, `cora-bugs-table.py`, `refentry.py` (a page's BibTeX entry), `render-references.py` (rewrites the entries on the pages) | `formalization-stats.py`, `check-references.py`; `render-references.py` by hand |
| `build/` | FLINT and oracle tooling: `install-flint.sh`, `build-flint-shim.sh`, `release-oracle.sh`, and `prune-lake-cache.py` (trims the CI Lake cache) | CI, by hand |
| `tools/` | `author-blocks.py` (back-fills the author block of Lean files), `stale-claims.py` (finds docstrings that explain an absence that has been filled; not in CI) | by hand |
| `expected/` | The committed outputs `check-demo.sh` and `check-runcheck.sh` compare against | `check-demo.sh`, `check-runcheck.sh` |

The data these generate lives in `experiments/paper/` (the formalization JSON files) and `experiments/paper/latex/` (the figures and appendices).
