# REGISTER — every artifact class, and what adjudicates it

*Adopted round 6, from the builder's Q5 answer: **every new artifact class
ships with its adjudicator named at birth** — one line saying what checks
sentences of this kind, and one saying what that check does not cover.*

The point is not bookkeeping. Five rounds of corpus showed that no register in
this project has ever shipped a defect **past** its adjudicator; the defects
land, every round, in whatever class was born that round and did not yet have
one. Writing the adjudicator down at birth converts the frontier from
*discovered next round* to *declared now* — and makes the first round that
births nothing unadjudicated a real experiment, because it should ship zero.

**The alarm to watch is not the count.** It is **register age**: a defect
younger than its adjudicator is the frontier, priced and expected. A defect
*older* than its adjudicator has never happened. If one ever does, that is the
finding, and this file is where you check.

---

| # | artifact class | born | adjudicator | what it does NOT cover |
|---|---|---|---|---|
| 1 | **Lean theorem statements** | r1 | the kernel: `lean FILE.lean`, exit 0 and zero bytes (norm 10) | whether the theorem is the *interesting* one, or whether its name and docstring match it |
| 2 | **Proof-term hygiene** | r2 | `audit/axioms.sh` — `#print axioms` on every theorem; exits 1 on `sorryAx > 0` or `Classical.choice > 0` | axiom *attribution* prose. The column is a toolchain-relative over-approximation, and says so in its own header |
| 3 | **Compile claims** | r3 | `audit/transcript.sh` — exit 0 and zero bytes required; `.olean` must exist; source SHA-256 stamped into the output | wall-clock, which is explicitly not load-bearing. Two rounds of near-misses came from treating it as evidence |
| 4 | **The shipped crate** | r4 | `audit/ship.sh` — builds with one tool, re-reads with another, hash-matches every required file against the tree, refuses STALE | that the crate is the *right round*. The round argument is required precisely because there is no safe default |
| 5 | **Ledger counts, hashes, dates** | r5 | `audit/views.sh` — the block is rendered from instrument output; `check` diffs it and exits 1 on drift | prose *outside* VIEW blocks. That exclusion is exactly where the round-6 defects landed |
| 6 | **Pointer prose** | **r6** | `audit/pointers.sh` — every backticked identifier resolves to a declaration, file or view; exits 1 otherwise | **binding**: whether the pointer points at the *right* thing. A name resolves whether or not the sentence describes it correctly |
| 7 | **Binding and characterization prose** | **r6, UNADJUDICATED** | the builder's source audit plus the round-over-round prediction loop. No script. | most of what a reader wants. This is the declared frontier — see below |
| 8 | **The courier channel** | r4–r5 | zip ferried as a file, SHA-256 pasted **outside** it in the message; the builder re-reads with a spec-following extractor and reports the manifest back | nothing known. Ran clean on its first live test |
| 9 | **This register** | **r6** | `audit/pointers.sh` reads it like any other document — names must resolve; `audit/numerals.sh` checks its numbers | whether a row's *adjudicator claim* is true. Nothing checks that a row is honest about its own coverage |
| 10 | **Cross-file transcription** | **r6** | `audit/transcription.sh` — definitions `Rigidity.lean` copies from `Anyon.lean` must be byte-identical, modulo a declared exception list; exits 1 on drift | the declared exceptions themselves. Each is a human claim that a change preserves meaning; the script verifies only that the change is *the one declared* |
| 11 | **Numeral prose** | **r7** | `audit/numerals.sh` — every multi-digit number in the ledger prose matches an instrument output or a labeled exemption; flags the rest for review | single digits, numbers in code/VIEW blocks, and whether a flagged number is *wrong*. A flag is a review item (norm 16), not a verdict |

**A note on the Python re-verifications** (`audit/*.py`). Five re-verifications
ride in this crate for the record, not run on this side (no Python here):
`audit_c1_check.py`, `verify_anyon.py`, `verify_anyon_r2.py`, `verify_c3.py`,
`verify_exchangeable_r2.py`. The builder ran all five against the round-7 tree
and reports **all five exit 0**.

**Round-8 finding H1, recorded against the row that now covers it.** An earlier
draft of this note said "some now exit nonzero on newer sources because facts
they treated as open became theorems." That reason is *false of the five
instruments named above* — the builder measured them exiting 0. It was true of
the builder's **own** r3–r5 instrument population, which did not ride in the
round-7 crate; the reason clause had been transplanted from a different artifact
set. A correct-looking justification, wrong about the artifacts it names,
invisible to every gate — the round-8 prediction (a false reason on a
correctly-formatted note; the instruments check membership, nothing checks the
reason column) scoring *in the register that exists to name adjudicators*.
Corrected here to the measured fact, and the prediction is logged CONFIRMED in
the capstone. As of round 8 the crate is **ferried in both directions**, so the
builder's own r3–r7 instruments — the population the transplanted reason was
actually true of — now ride here too, under `audit/`, pinned to their rounds.

---

## The declared frontier, round 6

**Class 7 is the live one, and it is named here rather than discovered next
round.** Rounds 4–6 each landed their defect exactly one register further out
than the last instrument reached:

- **r4** — counts and dates in the ledger. Fixed by views (class 5).
- **r5** — prose *pointing at* views. Fixed by the resolver (class 6).
- **r6** — I predicted "a pointer naming the wrong view, or a sentence
  characterizing a view's content in a way the view does not support."
  Confirmed, and one layer further out than I named: a sentence in which every
  noun resolved and the *number* was lifted from the wrong token.

So class 7 — sentences that *characterize* something correctly-named — has no
script and is not getting one this round, on the builder's advice that round 6
buys mathematics rather than instruments. Its adjudicator is the audit loop,
and its known failure mode is that the loop runs once per round rather than
once per sentence.

**Two honest boundaries on this file itself.** Nothing checks whether a row
above is *true* about its own coverage — a wrong adjudicator claim would read
exactly like a right one, which is class 7 applied to the register. And row 9
is self-referential in a way that cannot be fully cashed out: the register is
checked by an instrument the register describes.

## Class 10, and the first time this norm paid before the round shipped

Class 10 exists because **round 6's own architecture created it.** Adding
`Rigidity.lean` as a fifth deliverable was correct and followed the standing
rule (never trade zero-imports; duplicate the ring layer instead). The cost
nobody named when that rule was written:

> `Rigidity.lean` copies the pentagon machinery from `Anyon.lean` and — having
> zero imports by construction — **cannot state, let alone prove, that its copy
> agrees with the original.** Its docstrings say "verbatim from `Anyon.lean`"
> and "same content, same convention". Those are cross-file claims. No theorem
> in either file can reach them.

If a copied definition ever drifts, every theorem in `Rigidity.lean` stays
true — **of a different pentagon.** Fully kernel-checked, entirely sound, and
about the wrong object. That is the worst failure shape available to this
project, and it is invisible to every instrument that existed before this
round: the kernel is happy, the census is clean, the transcript is silent.

It was found by hand-checking the transcription before shipping, which is not a
method. `audit/transcription.sh` is now the method: six copied definitions
compared byte-for-byte, three declared exceptions reported rather than silently
passed, and the two halves of `pentResid` checked against `pentagonCheck`'s
`beq` arguments individually so the *declared* `Rng.neg` wrapper passes while any change
to either expression fails. Verified to bite: swap `fuse a y` to `fuse y a` in
the copied `Fs` — a two-character change — and it reports DRIFTED and exits 1.

**The boundary that remains** is the one the script's own header states: it
cannot check that `pentOK` and `pentagonCheck` *agree*, because that is a
semantic claim across two files with no shared vocabulary. That one stays with
the builder's source audit, and is named here rather than left implicit.
