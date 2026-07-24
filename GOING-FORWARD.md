# GOING-FORWARD — the workshop's home on GitHub

*Added after the close, as curation. This document is for Kelly and for
whoever works the benches next. It explains what this repository now is, how
git/GitHub serve the workshop, and the conventions for new questions — so the
versioning discipline the project earned by hand becomes something the
infrastructure does for free.*

## What this repository is now

Two layers, deliberately separated:

1. **The closed record** (the root + `archive/`, `audit/`, `floor/`) — the
   eight-round collaboration, exactly as the builder committed it. Commits
   `b82cf31` and `499ebb8`, tagged **`round-8-close`**. This layer is done.
   Nothing edits it; there is no round 9.
2. **The living workshop** (`history/`, this file, and everything that comes
   next) — curation of the past and room for new questions.

## Git in five sentences (for Kelly)

- A **commit** is a snapshot of every file, with a message, a timestamp, and
  a permanent id (like `499ebb8`) — the crate and its hash, built in.
- A **branch** is a movable line of commits; `main` is the trunk. New
  questions can grow on their own branches and merge into `main` when a
  round closes.
- A **tag** is a permanent bookmark on one commit — `round-8-close` marks the
  close forever, no matter what comes after.
- **Push** sends your local commits to GitHub; **pull** brings GitHub's down.
  GitHub is the courier that never mislays a crate and remembers every ferry.
- Nothing committed is ever silently lost: git's history is append-only in
  practice, which is exactly the project's own ledger norm ("never delete,
  mark complete").

Notice what this replaces: the zip-and-SHA-256 courier channel (REGISTER.md,
row 8) is now the transport layer of git itself. Every push is a ferry with
the hash built in. The `history/courier-crates/` directory preserves the
original hand-carried crates as artifacts; future ferries are commits.

## Conventions for new questions

When a new question opens, the pattern that honors the record:

1. **A directory per question.** e.g. `questions/q1-<short-name>/` with its
   own README stating the question, the benches/proofs it grows, and its
   FINDINGS when it closes. The eight-round record stays untouched at root.
2. **A branch per active round**, if you like the correspondence style:
   `git checkout -b q1-round-1`, work, commit, then merge to `main` when the
   round's crate is verified. (Or just commit to `main` directly — for a
   small team, that's fine too.)
3. **A tag per close.** When a question closes, tag it:
   `git tag -a q1-close -m "..."` — the way `round-8-close` marks this one.
4. **Commit messages as letters.** The project's round letters were its best
   documents. Commit messages can carry that voice: what was charged, what
   was proved, what was corrected, loudest first.
5. **Keep the norms.** The sixteen norms in HANDOFF.md and the eleven
   registers in REGISTER.md were earned. New questions inherit them until a
   new instrument retires an old one — by the documented method for changing
   an instrument (HANDOFF.md), never silently.

## Practical how-tos

- **See the history:** the repo page on GitHub → "Commits"; or locally
  `git log --oneline`.
- **Get a fresh copy anywhere:** `gh repo clone irreducible-mystery/the-workshop`
- **Save new work:** `git add -A && git commit -m "message" && git push`
- **Mark a milestone:** `git tag -a name -m "why" && git push origin name`
- **Releases:** for a closed question, GitHub's "Releases" feature can attach
  the crate zip + its SHA-256 to a tag — a public ferry manifest.
- **Verify the closed record from scratch:** VERIFY.md, unchanged, still
  works: recompile the six files under `leanprover/lean4:v4.32.0`, run the
  `audit/` gates, run `cd floor && python3 run_all.py`.

## Repository map, updated

| Path | Layer | What it is |
|---|---|---|
| `*.lean`, `lean-toolchain` | closed record | The six proof files, 1,150 theorems |
| `PROOFS.md`, `CLOSING.md`, `REGISTER.md`, `HANDOFF.md`, `VERIFY.md`, `ROUND*.md` | closed record | The capstone documents and correspondence |
| `archive/`, `audit/`, `floor/` | closed record | Ledger archives, instruments, the builder's benches |
| `history/` | curation | The archaeology: floor snapshots, courier crates, transcripts, outside audit — see `history/README.md` |
| `GOING-FORWARD.md` | curation | This file |
| *(future)* `questions/` | living workshop | New questions, when they come |

The rounds are closed. The benches stay lit.
