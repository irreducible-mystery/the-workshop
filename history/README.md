# history/ — the archaeology of the workshop

*Added after the close, as curation. Nothing in this directory is part of the
shipped eight-round record — that record is the repository root, exactly as
the builder committed it (`b82cf31`, then `499ebb8`). This directory preserves
everything that led up to it: the floor's growth, the courier's crates, the
conversations, and the outside audit. The record ends at round 8; this is the
strata beneath it.*

## What's here

### `floor-snapshots/`
Eleven deduplicated snapshots of the builder's Python workshop, in
chronological order, from the first weld (7 benches) to the round-4 audit
wing. Kelly downloaded these from the builder's cloud sessions as the floor
grew; duplicates have been collapsed, and each stage is named by what it
added. The final floor state is not here — it lives in `../floor/`, where the
builder shipped it.

| Stage | What it captures |
|---|---|
| 01 | The first weld — 7 benches |
| 02 | 10 benches |
| 03 | 22 benches |
| 04 | 25 benches |
| 05 | 27 benches |
| 06 | The floor complete — 30 bench files (29 benches + runner) |
| 07 | Lean begins — first 3 proof files aboard |
| 08 | Round 2 — 4 proof files (Exchangeable joins) |
| 09 | Round 3 handoff aboard (the crash-autopsy HANDOFF) |
| 10 | Round 3 ledger (audit wing at 11 instruments) |
| 11 | Round 4 — audit wing at 21 instruments |

### `orphan-documents/`
Three intermediate states of the floor's front-door documents (README +
WELD_REPORT) that don't hash-match any full snapshot above. Preserved so no
captured state of the floor is lost.

### `courier-crates/`
The ferry's own record: the original zip crates Kelly carried between the
builder's cloud sessions and the third body's Lean sessions, byte-for-byte as
they traveled. These are the actual vehicles of the collaboration — the
courier channel that REGISTER.md row 8 adjudicates. (`theworkshoprepo.zip`
itself is omitted: it *is* this repository.)

### `transcripts/`
The two session transcripts:
- `claude-builder-workshop-transcript.txt` — the builder's side (the cloud
  Cowork session), from the founding axiom through the final verification of
  the repository itself.
- `claude-code-third-body-transcript.txt` — the third body's side (Claude
  Code), from the round-3 resurrection handoff through committing this
  repository and preparing it for publication.

These are the register the corrections law said its near-misses "live only
in" — Kelly's couriered transcripts. They are now aboard.

### `verification/`
An independent third-party audit of the terminal repository, performed by a
separate agent (SuperNinja) commissioned by Kelly after the close:
- `VERIFICATION_REPORT.md` — full recompile, census reproduction, all gates
  re-run, 29/29 benches, alarms fired on purpose, independent sympy
  recomputation. Verdict: the formal mathematics is sound. One genuine minor
  defect found (F-1, a stale script comment) — landing, as the corrections
  law predicts, in characterization prose.
- `verification-plan.md` — the audit's eight-phase plan, all boxes checked.
- `check_exchangeable.py`, `check_rigidity.py`, `independent_math_check.py` —
  the from-scratch verification scripts.

## Why this exists

The project's own law says the record is what survives the substrate it
stabilized in. The root of this repository is the record; this directory is
the substrate — kept so that a future reader can watch the arc happen, stage
by stage, crate by crate, instead of only reading its summary.

The rounds are closed. The workshop continues. New questions get new
directories, new branches, new tags — never edits to what shipped.
