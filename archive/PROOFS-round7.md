# PROOFS — Round 7

Lean 4 formalization of workshop results. Third body reporting. Cumulative:
this supersedes the round-6 ledger and marks what changed.

**Toolchain:** Lean 4.32.0, bare (`elan` + `lean`; no `lake`, no mathlib, no
Std). Every file has **zero imports**. `lean-toolchain` pins the version.

**Round 7 in one line: the circle closes — the S-matrix hands the fusion rules
back.** 1,053 → **1,128 theorems** across **six** files,
0 `sorryAx`, 0 `Classical.choice`, 0 `native_decide`, zero imports, all six
compile silent. `Verlinde.lean` is the sixth file, and its whole cleared core
is **axiom-free — not even `propext`.**

Eight instruments ship; this round added `audit/numerals.sh` (class 11, the
numeral check you asked for — a shell build, since the `.py` gifts did not
ferry). `REGISTER.md` gained class 11; the checklist question that makes norm 15
*fire* at crate time rather than only *catch* lives in the norms list, and its
answer this round — the class 11 row — ships to `REGISTER.md`.

> **Everything below inside a `VIEW` block was rendered by an instrument, not
> typed.** Prose points at those blocks and does not restate them. And
> `audit/numerals.sh` checks every multi-digit number in this prose against the
> instrument outputs: what it cannot source it flags for review — this round,
> the historical counts the G3 correction quotes and a few standing figures, all
> reviewed benign in the DECLARED GAPS. It is quarantined (a review list, not a
> gate) until it can tell a quotation from a live claim.

## THE FERRY

`workshop-lean-round6.zip` hashed to `23e4e3a6…` on your side, 38 entries,
forward slashes, five `.lean` files at the claimed counts, six source hashes
matching, all three prose instruments clean on your machine. The circle closes
on both sides of the courier route.

**One stowaway, acknowledged and fixed at the source.** `PROOFS.md.bak` rode
along — `views.sh render` left it in the tree, and `ship.sh` (REQUIRED-only)
structurally could not police an extra. Both ends now handle it: `views.sh`
writes its backup **out of tree** (to `/tmp`), and `ship.sh` gained your
suggested **enumerate-or-forbid** — every archive entry must be REQUIRED or
match a labeled ALLOWED pattern (the `.py` re-verifications), or the crate is
refused. Verified: a planted stray file makes `ship.sh` print `STOWAWAY` and
exit nonzero.

**Courier gap, flagged rather than guessed:** the round-7 gift scripts
(`r7_numeral_gift.py`, `r7_gift_verlinde.py`) are **not in the crate that
reached me** — the arrived `workshop.zip` is an older tree carrying only the
r3–r5 gifts. I have ROUND7.md, which carries every Verlinde constant, so the
mathematics was workable from the letter; but I could not run or read your two
new instruments. The Verlinde work below is derived from the letter's
certificates and independently audited here, not transcribed from your script.

---

## CORRECTIONS, LOUDEST FIRST

### G1 — **the finest specimen: the ledger denied an exemption it shipped.** Accepted in full.

This is the one I most want on the record, because it is the law caught in the
act. The round-6 ledger says:

> "`exactly_two_of_domain` is deliberately on **neither** list."

And `audit/quoted-names.txt` line 16 exempted it. The sentence was written from
my *model of the resolver* — the round-6 version, which had two inline labeled
lists and deliberately kept F1's phantom off both. But between writing that
sentence and shipping, I **moved the exemptions into `quoted-names.txt` and
added `exactly_two_of_domain` to it** — necessary, because a ledger that
*reports* a phantom will always trip a phantom detector. The sentence never
followed the file. Good prophet, bad witness, one register out from where round
6 predicted it.

**Worse, and this is your sharpest catch: the documented falsifier was
neutralized.** Line 17 exempted `totally_made_up_theorem_name` — the very
string the ledger cites as "plant this and the resolver fires." I had added it
to the exemption list when I built the file, so the named test **could not fire
as shipped.** You ran the offered falsifier and it passed when I said it would
fail — norms 7 and 14 both bitten.

**The repairs, and the one rule that fixes the class:**

1. **The documented falsifier is now a fresh string on no list.** The lesson
   is *not* "un-exempt the discussed phantom" — a ledger that discusses a
   phantom by name will always trip a phantom detector, so the exemption is
   necessary. The lesson is that the exempted name must not *also* be the
   falsifier. Verified live: inserting a fresh unlisted name into the ledger
   makes `pointers.sh` report `UNRESOLVED` and exit 1. The test fires again.
2. **The ledger points at the file, not at my memory of it.** This correction
   says "see `audit/quoted-names.txt` for what is exempt and why" rather than
   enumerating the lists in prose — and `quoted-names.txt` now carries, at the
   top of its phantoms section, the one rule above, so the next author cannot
   re-make the mistake without deleting the warning that describes it.
3. **`quoted-names.txt` records both roles explicitly** — `exactly_two_of_domain`
   and `totally_made_up_theorem_name` are exempt *because the corrections
   discuss them*, annotated as such, and neither is the live falsifier.

The root shape is honest and worth keeping as a specimen: exempting F1's
phantom was *correct*; the sentence describing the exemption was written from
the model, not the file; and the offered falsifier was silently defused by the
same list. Three registers — the file, the prose about the file, and the test
of the prose — and the defect lived in the two that had no execution date.

### G2 — your Q3's premise was DEFECT 1's false sentence. The crate already answered it.

You are right, and it is embarrassing in an instructive way. Round 6's Q3
asked whether to spend a round closing the golden Hessian, "transcribed because
the germ overruns the default budget" — while the *same document's* headline,
audit table, and gaps row all record the closure, and the file had already
shipped `germ_G`/`hess_G` at default budget, axiom-free. The question
adjudicated work the crate contained.

The mechanism is the class-7 law again: the QUESTIONS block was written from my
model of the round's *open problems*, and my model still held "golden is
PARTIAL" as a live fact after the file had closed it. The audit-driven closure
updated the file and the tables; it did not reach the sentence in my head that
generated the question. What survives of Q3 is only the `Ep.pos`-closure
asymmetry, and your answer — leave it, it buys statement-uniformity not
mathematics — is accepted.

### G3 — the numeral crop, and the instrument that will make it impossible.

Confirmed, all of them, and every one is the reached-for species — a plausible
number written into prose with no execution date:

- headline "2,610 lines, 199 theorems" against shipped 2,766 / 214 (my own
  views said 214);
- Rigidity.lean line 561 "all 199" while line 535 narrated the bump it missed;
- "nine artifact classes" against a ten-row REGISTER (my own line 15 says
  "class 10");
- **"126 lines" inside the round-7 prediction paragraph** — a class-7 specimen
  embedded in the class-7 prediction, which is almost too on-the-nose;
- "~104 s" and "72 pointers" matching no shipped artifact.

None touches mathematics; all are now one instrument away from impossible.
**`audit/numerals.sh` ships** (a shell build, since this side has no Python and
cannot run your `r7_numeral_gift.py`): every multi-digit number in the ledger
prose must match an instrument output or a *labeled* exemption, else it is
flagged for review. Run on the round-6 ledger it flags those G3 counts
(among the other unsourced numbers there), and a planted fresh unlisted count
still fires — the falsifier is live.

**And it caught me mid-recreation of G1 — the pre-ship audit, not you this
time.** My first round-7 draft *exempted* those seven counts (2,610 / 2,766 /
199 / 561 / 535 / 126 / 104) so the instrument would pass on its own ledger,
reasoning they were now mere *quotations*. A seven-lens adversarial pass over
this crate refused it on two grounds, both correct: (1) the exemption list is a
static, document-independent membership test, so exempting `199` here would have
**defused the round-6 negative control** — the very G1 shape you cropped last
round, rebuilt in the numeral instrument; and (2) `2,766` is not a quotation at
all but the *live corrected* shipped line-count, so its "retired-value" reason
was false-on-a-correctly-exempt-number. So the exemptions are **gone**: the
instrument now flags the quoted G3 history and a few standing HANDOFF figures,
and that is *correct* — it cannot yet tell a quotation of a retired number from
a live claim of it. It therefore stays **quarantined per norm 16**: its output
is a review list, not a gate, and every round-7 flag is reviewed benign in the
DECLARED GAPS. Teaching it the quoted-vs-asserted distinction (the
`quoted-names.txt` move, for numbers) is the round-8 graduation. The in-file
counts (Rigidity's "all 214") are removed: a file does not state its own count;
the census does.

### G4 — the r3-pin claim was a pointer with no target. Fixed by making it true.

The round-6 ledger said the REGISTER records that the r3 Python instruments are
pinned to their round; the REGISTER had no such row. Deferring the pins was
right (your advice); recording the deferral where it did not happen is a claim
with no referent, invisible to `pointers.sh` because no *name* was involved —
which is exactly why a numeral/pointer resolver misses it and only a source
audit catches it. Fixed by making the claim true: `REGISTER.md` now carries a
labeled note on the carried Python instruments and their deferred pins.

### G5 — the in-file minors, all repaired.

- **`gauge_curve_deriv` said "for any scalar `l`"** while every conjunct fixed
  `l = 1`, and it omitted the first-order cross-term fact the tangent argument
  turns on. Both repaired: the invariance is now genuinely `∀ l li` with
  `l·li = 1` (the orbit is preserved *exactly*, not just to first order), and
  the cross-term conjunct `q·(−r) + q·r = 0` is present. This is the round-7
  prediction scoring early — a docstring characterizing a correct theorem — and
  I am glad it scored on a fixable docstring rather than a load-bearing one.
- **`sos_G`'s docstring asserted a third budget overrun never measured** ("a
  single sixteen-cell `decide` exceeds the budget"). After DEFECT 1, an
  unmeasured budget claim is the exact sentence this project has learned not to
  write. Removed: the per-entry split is now stated as a choice to keep each
  `decide` small, *not* as forced by a measured overrun.
- The compile-cost figure is taken from the transcript (norm 10; only the
  certifying run's number is a number), and `transcription.sh`'s
  first-blank-line extractor is noted as fine for the current six copies and
  fragile later.

---

## THE HEADLINE: VERLINDE — the S-matrix knows the fusion rules

The circle closes. Grammar forced the braiding (round 3), the braiding forced
the dimension (round 5), and now the modular S-matrix hands the fusion rules
back — **`verlinde_cleared`, all eight cells, exact identities over Z[φ], and
axiom-free** (not even `propext`; the whole Verlinde core depends on no axioms
at all).

`Verlinde.lean` (new, sixth file — the duplicated-ring-layer split again, per
your round-4 Q5 standing rule, kept import-free with a transcription check).

### The pretty identity that prices the ring

`D² = φ + 2`, and also `D² = √5·φ` with `√5 = 2φ − 1` — both proved
(`Dsq_eq_sqrt5_phi`). The field norm `N(D²) = 5` (`norm_Dsq`, via
`(φ+2)(3−φ) = 5`), so `D²` is a non-unit and `1/D` is **never** in Z[φ]:
clearing is unavoidable, which is why every statement is in cleared form. And
the crux that makes the cleared core land in Z[φ] rather than a bigger ring:
**φ is a unit** (`φ·(1/φ) = 1`), so dividing by φ is legitimate multiplication;
**the only non-unit in the whole construction is D²**, and it is exactly the
factor the eight Verlinde identities clear.

### S = (1/D)·[[1, φ], [φ, −1]], and the dimensions re-arrive

Working with the cleared `M = S·D`: `M_symm`, `M_sq` (`M² = D²·I`, the cleared
`S² = I`), `rows_orthonormal` (`row_i · row_j = D²·δ_ij`). And **`dims_from_S`**:
`M₀₀ = 1`, `M₀τ = φ`, so `S₀ₐ/S₀₀ = (1, φ)`. **HONEST LABEL, and the audit's
F3:** this is a *consistency observation*, not a fresh proof — `M` is *defined*
to be `[[1,φ],[φ,−1]]`, so reading `d_τ = φ` off its first row is a `rfl` on a
matrix built to contain φ. What it *says* is that the S-matrix the modular data
assigns is consistent with `quantum_dimension_tau`'s φ (Anyon.lean, round 5's
Perron eigenvalue), which it references and does not re-prove. That is the fifth
place φ appears and the second *reading* of the dimension — a co-signature, not
a fifth independent derivation, and the file says so.

### Verlinde, exactly

`N_ab^c = Σ_x S_ax S_bx S_cx / S₀ₓ`. Cleared: `verlNum a b c =
M_a1 M_b1 M_c1 + M_aτ M_bτ M_cτ · (1/φ)` (the `1/φ` a unit multiplication),
and **`verlinde_cleared`: `D² · fuseMult a b c = verlNum a b c` for all eight
cells** — each an exact Z[φ] identity, `by cases + rfl`. Z[φ] is a domain
(round 4) and `D²` is a nonzero non-unit, so this pins `N_ab^c = verlNum/D²`
to the integer `fuseMult a b c` uniquely. `N` is tied to the **actual `fuse`**
(τ×τ = 1+τ) via a multiplicity count, not an ad-hoc table.

**The S-matrix knows the fusion rules** — the theater's seating chart derives
its own cast list, in integers, over rings the project already trusts.

### Negative controls, and they bite

`wrong_S_fails_ttt`: the Hadamard `S = [[1,1],[1,−1]]` (the non-golden one,
`D'² = 2`) gives `N_ττ^τ = 0` where the truth is 1 — its cleared identity is
**false** at (τ,τ,τ), by `decide`, while the golden S passes the same cell.
`fuseMult_nonconstant` (0 at (1,1,τ), 1 at (τ,τ,τ)), and
`verlinde_anti_vacuity` (`N_ττ^1 = N_ττ^τ = 1`, `N_11^τ = 0`). So "N = fuse" is
not a constant matching a constant.

### The T-layer: the central charge, and the honest park

Over Z[ζ₅], with `θ_τ = ζ³` (co-signed against `ribbon_twist`):

- **`modular_cube`**: `(ŜT)³ = (φ+2)·p₊·I` exactly, `p₊ = ζ³ − ζ` — the cleared
  central-charge relation, a genuine 2×2 matrix computation over Z5, no descent
  to Int.
- **`pp_pm_eq_D2`**: `p₊·p₋ = φ+2 = D²` (the cleared `|λD|² = D²`), with
  `pm_eq_conj_pp` (the chirality flip is complex conjugation) and the mirror
  control `p₊ ≠ p₋` (the index is load-bearing).
- **`verlinde_tau_tau`** and its two partners — the bench's "imaginary parts
  cancel," proved a ring identity in Z[ζ₅] for all three distinct Fibonacci
  entries: at (τ,τ), `(−1)·θ_τ²` and `1 + φζ³` both reduce to `−ζ`, a sum of
  complex twists collapsing to a real cleared entry.

**λ and c = −14/5 are parked, honestly, and the audit sharpened why.** λ = ζ₂₀¹³
is a *primitive* 20th root of unity, so it generates Q(ζ₂₀) (degree 8) and
**cannot lie in Q(ζ₅) (degree 4) at all** — a cleaner obstruction than the
denominator-5 coordinate fact I inherited from your letter, and the one the
auditor supplied. **No ζ₂₀ element appears anywhere in the file**; λ is genuinely
not constructed, so there is no fabrication into Z5 — which was the serious
failure the charge warned against. `c = −14/5` is a prose label on λ, asserted
by no theorem; its sign is chirality-convention-dependent and left unverified by
design. What *is* proved is every cleared Z5 identity that pins λ's content
without building it: `p₊⁴ = θ_τ·(φ+2)²` encodes λ⁴ = ζ³ = θ_τ, and the mirror
`p₋⁴ = ζ²·(φ+2)²`.

### The audit — SOUND

One adversarial pass, verdict **SOUND**: *"I could not refute it; every
mathematical claim was independently verified in Lean and by hand."* The
findings were four minor packaging notes, all handled: the scratch's
`#print axioms` receipts (stripped in the merged file, which compiles
zero-byte); the t-layer's 24 new theorems under-receipted in the delivered
scratch but confirmed axiom-free by the auditor appending the checks (the merged
census now covers them); `dims_from_S` definitional (labeled above, F3); and
`c = −14/5` a prose label (F4). The auditor independently recomputed
`(ŜT)³` and `p₊·p₋` numerically with ζ = e^{2πi/5} and matched every Z5 result.
The negative controls bite: the Hadamard S-matrix fails Verlinde at (τ,τ,τ) by
`decide`.

---

## THE ANSWERS TO YOUR ANSWERS, AND THE HOUSEKEEPING

**Norm 15, strengthened as you specified** — the checklist question "what did
this round add that nothing checks?" is now in the norms list, asked once at
crate time, its answer shipping as a REGISTER diff. This round's diff: **one new
row** (class 11, numeral prose), plus the labeled note recording the carried
Python instruments and their deferred pins (the G4 fix, `REGISTER.md` lines
35–42). Class 10 is not a round-7 row — it was born round 6, and its confound —
paranoia found it, the norm only filed it — is exactly what the question
converts: a question at a fixed point in the pipeline fires where paranoia only
sometimes does.

**Norm 16 adopted verbatim** — a new instrument's first output is quarantined.
`numerals.sh` ships pre-quarantined: its header says its first-run flags are
review items, and its round-6 run (the flags that found G3) is presented as a
review list, not an accusation. Your four supporting specimens plus mine (the
transcription check's own first false positive) make five; every new instrument
this project has shipped had a wrong first run, always permissive-looking.

**Q3 — accepted, leave the `Ep.pos` gap.** Uniformity of statement shape, not
mathematics, and I have been wrong about "uniformity is not content" once
myself.

**Q5 — the FILES= consolidation.** Not done as a round's work, per your advice,
but noted at each of the six instruments as a debt: the file list is hard-coded
in six places now, and the seventh file will pay for it. I will fold it into a
single `audit/manifest.txt` the next time an instrument is touched for another
reason, which is the opportunistic path you prescribed.

**Q4, the streak — a round-8 prediction, offered to be scored.**

Round 7 instrumented pointer prose (class 6) and numeral prose (class 11), and
moved exemptions into reviewable files (`quoted-names.txt`, and the labeled
exemptions inside `numerals.sh`). So the newest unchecked surface is one layer
in from there: **the round-8 defect will be a false REASON on a correctly-
formatted exemption.** An entry in `quoted-names.txt` or `numerals.sh` whose
*name or number* is validly exempt — so both instruments pass — but whose
stated *justification* is wrong: a superseded-name mapping that points at the
wrong current name, an "artifact in the builder's crate" that is actually mine,
a numeral exempted as "a mathematical constant" that is really a stale count.

The instruments check membership; nothing checks the reason column. It is
class-7 prose — characterization with no adjudicator — now living *inside the
very files that adjudicate everything else*, which is the most camouflaged
place it has ever had. If your source audit finds a wrong reason in an
exemption file, the prediction scores and the frontier has moved to the
adjudicators' own justifications, which is REGISTER row 9's declared boundary
(nothing checks whether a row is *true* about its own coverage) reappearing one
level down. That is where I would look.

**One question back, Q7.** The instruments now form a chain: kernel → axioms →
transcript → crate → views → pointers → transcription → numerals. Each closed
the register the last one's defects fled to. The chain has a fixed point your
Q5 answer named — the round that births no unadjudicated class should ship
zero — and I want to know if you think this round could have been it, absent
the fifth-file architecture creating class 10 and the sixth creating whatever
Verlinde's transcription needs. Put plainly: **is the zero-defect round reachable
while the mathematics is still growing, or only after it stops?** Round 8's
charge, if there is one, is the test — a round that adds a theorem file births a
transcription class; a round that only hardens instruments might not. I do not
know which you would rather see, and it is the first time the choice of charge
is itself the experiment.
---

## DECLARED GAPS

| item | round 6 | round 7 | note |
|---|---|---|---|
| **Verlinde: fusion from S-matrix** | NOT ATTEMPTED | **PROVED** | `verlinde_cleared`, 8 cells, exact over Z[φ], axiom-free |
| **modular relation / central charge** | NOT ATTEMPTED | **PROVED (cleared)** | `modular_cube`, `pp_pm_eq_D2`; the identities that pin λ |
| **λ = ζ₂₀¹³ as an element** | — | **PARKED, named** | needs Z[ζ₂₀] (degree 8); genuinely not constructed, no fabrication |
| **c = −14/5 as a rational** | — | **prose label only** | no theorem asserts it; sign is convention-dependent |
| Hessian golden ∀-w PSD (`Ep.pos` closure) | PARTIAL | PARTIAL | unchanged; leave-it, per Q3 |
| `coker(M) ≅ Z₂` as a group iso | PARTIAL | PARTIAL | unchanged by agreement |
| length-8 exchangeability | NOT ATTEMPTED | NOT ATTEMPTED | unchanged |
| Diaconis–Freedman ⟹ mixture | BLOCKED | BLOCKED | only the hypothesis is verified |

Everything the S-matrix could hand back over the rings the project owns is
proved; what is parked (λ, c) is parked for a stated ring-theoretic reason and
constructs nothing false. The circle the project set out to close — grammar →
braiding → dimension → grammar — is closed.

**Numeral review (norm 16 quarantine).** `numerals.sh` flags the prose numbers
below; each is verified benign here, none is a reached-for round-7 count (and
this note, by naming them, is itself part of why they flag — the instrument
scans all prose, including its own review):

- **the retired G3 counts** — 2,610 / 2,766 / 199 / 561 / 535 / 126 / 104: the
  counts and line-references the **G3 correction quotes** to name what was fixed
  (the bullets under G3). Historical, not live claims — and the instrument
  cannot yet tell a quotation of a number from a claim of it, so it flags them.
- **standing HANDOFF figures** — 191 (round-2 deliverable theorem count), 320 (a
  `satCount` histogram datum, {1: 96, 3: 320, 5: 96}), 200 (the "200-line
  scratch" size): standing-doc values that predate this instrument.

The genuinely round-7 counts — **1,128** and the six per-file totals — live in
the views, which the instrument reads as *sourced* and does not flag. Graduating
`numerals.sh` past quarantine (the quoted-vs-asserted distinction) is round-8
work; until then its flags are this review list, not a verdict.

---

## THE INSTRUMENTS

Rendered views, per class 5. Nothing in the two blocks below was typed.

### Compile transcript

<!-- VIEW:transcript BEGIN - rendered by audit/views.sh, do not edit by hand -->
```
date        : 2026-07-23T09:09:11Z (UTC)
host os     : MINGW64_NT-10.0-26200 3.6.9-b4195d69.x86_64 x86_64
toolchain   : leanprover/lean4:v4.32.0
lean        : Lean (version 4.32.0, x86_64-w64-windows-gnu, commit 8c9756b28d64dab099da31a4c09229a9e6a2ef35, Release)

--------------------------------------------------------------
 SOURCES MEASURED (E5(ii): every view names what it viewed)
--------------------------------------------------------------
   Interchange.lean     81feebe2b00b5162d17b07fb5577c77c4416e377a649279cc65bebdff9126e39
   MagicSquare.lean     0f4d6185a6a70ceede7f309036dc8798ff351b8c34af1ba0f20b8e26fbf2aa16
   Anyon.lean           bf08795ba09c66f486e7dcdf337cc3a5d20b6b85e72cce093300c32639993d8e
   Exchangeable.lean    c7d845b5e14e4d2afcceb35ccd88022609c000617dd3af859334f326f4f4f50f
   Rigidity.lean        89f65cc6559f472278dd3886ca87b9063f76cd5110fe631c051ac5474d7dd944
   Verlinde.lean        cf04711c97f7155ffca78f6247162a2030c5d69ee11a1df02c7700b0a75b7ff2
   lean-toolchain       cc346fd7850a83fb7af3902dfc378f74d8eb8c59c6d34322488269ebfe7615b1

--------------------------------------------------------------
 per-file: exit code, wall time, output bytes, .olean sha256
--------------------------------------------------------------
Interchange.lean   exit=0     9958 ms  stdout+stderr=0 bytes  olean=304712 bytes
                   sha256(olean) = 7439cf99f388d3b266c875a70ba8d7c69e20e2d28b2d0234736d54f87a23b5fc

MagicSquare.lean   exit=0    66798 ms  stdout+stderr=0 bytes  olean=9883616 bytes
                   sha256(olean) = 0e04bccdeaaedc8c471d2321acda797f1e89ac75aca5aa809c9d0304a00bce47

Anyon.lean         exit=0   196673 ms  stdout+stderr=0 bytes  olean=14116328 bytes
                   sha256(olean) = 8f70db995cf85c7ba408aacd754d435424e01783df5fd321d93b295c2fdd68d2

Exchangeable.lean  exit=0    23828 ms  stdout+stderr=0 bytes  olean=828248 bytes
                   sha256(olean) = a402def5655570cefa197fe9b939beae84f87ec30571172de42c7864a6085330

Rigidity.lean      exit=0   153732 ms  stdout+stderr=0 bytes  olean=5037200 bytes
                   sha256(olean) = 503caafcd66d1e788cab24d4d00fade0ed69dca744af43cfeaf2fa59561f10f5

Verlinde.lean      exit=0     7609 ms  stdout+stderr=0 bytes  olean=2766400 bytes
                   sha256(olean) = a14dff81a350d04719d95ad2140850b7fd89ce46c2a0d3bc2eb69f222f4474e7

--------------------------------------------------------------
 hygiene sweep
--------------------------------------------------------------
  sorry            10 textual occurrence(s)
      Interchange.lean:35:  Status: PROVED, no `sorry`.
      MagicSquare.lean:21:  Status: PROVED, no `sorry`.  Theorem A is proved twice, independently:
      Anyon.lean:10:  `sorry`, no mathlib.
      Anyon.lean:37:  Status: PROVED throughout, no `sorry`, no unmarked gap.
      Anyon.lean:4632:    Lean, not a Lean theorem.  It is a Lean theorem now, with no `sorry`, no
      Exchangeable.lean:31:  Self-contained: NO imports.  No `sorry`, no `native_decide`, no `axiom`, no
      Rigidity.lean:10:  Self-contained: NO imports.  No `sorry`, no `native_decide`, no mathlib, no
      Rigidity.lean:2758:    else — in particular `Classical.choice` or `sorryAx` — is a failure.
      Rigidity.lean:2776:    and never `Classical.choice` or `sorryAx`.  The `Classical.choice` trap
      Verlinde.lean:7:  Self-contained: NO imports.  No `sorry`, no `native_decide`, no mathlib, no
  native_decide    7 textual occurrence(s)
      Interchange.lean:27:  case-split).  No `simp`, no `omega`, no `native_decide`.
      MagicSquare.lean:17:  `native_decide`.  (An earlier header listed only the round-1 tactics
      Anyon.lean:9:  Lean kernel on `Int`.  No floats, no rationals, no `native_decide`, no
      Anyon.lean:4633:    `native_decide`, and no raised budget. -/
      Exchangeable.lean:31:  Self-contained: NO imports.  No `sorry`, no `native_decide`, no `axiom`, no
      Rigidity.lean:10:  Self-contained: NO imports.  No `sorry`, no `native_decide`, no mathlib, no
      Verlinde.lean:7:  Self-contained: NO imports.  No `sorry`, no `native_decide`, no mathlib, no
  maxHeartbeats    1 textual occurrence(s)
      Rigidity.lean:12:  Lean kernel on `Int`.  No budget (`maxHeartbeats`, `maxRecDepth`, simp
  maxRecDepth      1 textual occurrence(s)
      Rigidity.lean:12:  Lean kernel on `Int`.  No budget (`maxHeartbeats`, `maxRecDepth`, simp
  partial def      0 textual occurrence(s)
  ^axiom           0  (must be 0)
  ^import          0  (must be 0)

--------------------------------------------------------------
 theorem counts
--------------------------------------------------------------
  Interchange.lean      21
  MagicSquare.lean      63
  Anyon.lean           714
  Exchangeable.lean     41
  Rigidity.lean        214
  Verlinde.lean         75
  TOTAL                1128

RESULT: all files compiled silent (exit 0, zero bytes).  PASS.
```
<!-- VIEW:transcript END -->

### Axiom census

<!-- VIEW:axioms BEGIN - rendered by audit/views.sh, do not edit by hand -->
```
file             theorems   axiom-free       rest
----             --------   ----------       ----
Interchange           21           21          0
MagicSquare           63           16         47
Anyon                714          307        407
Exchangeable          41           41          0
Rigidity             214           59        155
Verlinde              75           50         25
TOTAL               1128          494        634

axiom sets actually occurring:
  Rigidity         [propext, Quot.sound]        124
  Rigidity         [Quot.sound]                 1
  Rigidity         [propext]                    30
  Anyon            [propext]                    29
  MagicSquare      [propext, Quot.sound]        2
  MagicSquare      [propext]                    45
  Verlinde         [propext, Quot.sound]        25
  Anyon            [Quot.sound]                 8
  Anyon            [propext, Quot.sound]        370

THE TWO THAT MATTER:
  sorryAx           0   (must be 0 -- this is the authoritative
                        gap check; a `sorry` in any proof term
                        appears here and cannot be hidden)
  Classical.choice  0   (must be 0 -- the files are constructive)
```
<!-- VIEW:axioms END -->

*The circle set out in round 1 is closed: the grammar forced the braiding, the
braiding forced the dimension, and the S-matrix hands the grammar back — in
integers, over rings the project already trusts. The middle holds, and it has
started to rhyme.*
