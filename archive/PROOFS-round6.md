# PROOFS — Round 6

Lean 4 formalization of workshop results. Third body reporting. Cumulative:
this supersedes the round-5 ledger and marks what changed.

**Toolchain:** Lean 4.32.0, bare (`elan` + `lean`; no `lake`, no mathlib, no
Std). Every file has **zero imports**. `lean-toolchain` pins the version.

**Round 6 in one line: the dial's stiffness is a theorem, with the symmetry
half subtracted.** 839 → **1053 theorems** across **five** files,
0 `sorryAx`, 0 `Classical.choice`, 0 `native_decide`, zero imports, all five
compile silent.

Seven instruments now ship, and this round added two: `audit/pointers.sh`
(class 6 — pointer prose) and `audit/transcription.sh` (class 10 — cross-file
transcription, a class this round's own architecture created). `REGISTER.md`
is new: every artifact class, its adjudicator, and what that adjudicator does
not cover.

> **Everything below inside a `VIEW` block was rendered by an instrument, not
> typed.** Prose points at those blocks and does not restate them.

## CORRECTIONS, LOUDEST FIRST

### F1 — **the phantom, and what it actually was.** Accepted; the class is now instrumented.

`exactly_two_of_domain` appears as a named theorem row in the round-4 ledger's
assembly table and as a citation in HANDOFF, and exists in no source. You are
right, and the honest account is more specific than "a name that never landed":

It was a **scratch-file name**. Round 4 developed the "exactly two" algebra
against the domain property *as a hypothesis* — that is the technique HANDOFF
was recommending in the sentence that cites it — and then, on merge, discharged
the hypothesis. The theorem landed as `hexagon_exactly_two`, which applies
`Q_factors` and the domain bridge directly. **The content always shipped; the
scaffolding dissolved and the citation did not.**

That makes it D1's species with a twist worth recording: the sentence was
*true about the development* and false about the artifact. My model was
describing the working state, which is exactly the "good prophet, bad witness"
diagnosis running in the temporal direction.

**The class is now adjudicated.** `audit/pointers.sh` (new, in the crate)
resolves every backticked identifier and pointer in PROOFS.md, HANDOFF.md and
REGISTER.md against the universe of real declarations, files and view names,
and exits 1 on any that does not resolve.

**It caught F1 on its first run** — and one more you did not have: a stale
`Nswap_perron_is_one` in my own round-5 ledger, in the very paragraph where I
recorded renaming it to `Nswap_has_positive_eigenvalue_one` as part of the N3
repair. The repair reached the file and not the sentence describing the repair.

**It also failed its own doctrine on that first run, and that mattered.** It
threw eight false positives — Lean core names (`Classical.choice`,
`Fin.instOfNat`), file basenames (`ship.sh` where the tree says
`audit/ship.sh`), and names quoted *because* they are wrong (the round-2
misnomers HANDOFF records under C3′). Its own header comment says false
positives are worse than false negatives, because they train the reader to
ignore the instrument. So the exemptions are two **labeled** registers rather
than one flat allowlist:

- **externals** — Lean core and non-Lean tokens, short and justified;
- **superseded names, quoted as history** — with a comment mapping each to its
  current name. That list turned out to be worth having on its own: it is a
  small rename register, and it is the only place the project records that
  `sepPar_noncommutative → sepPar_not_comm` and friends ever happened.

`exactly_two_of_domain` is deliberately on **neither** list. Whitelisting a
finding inside the instrument that found it would be the worst thing that file
could do, and the comment says so.

Verified to bite after the fix: clean pass at 72 pointers; plant
`totally_made_up_theorem_name` in the ledger and it reports UNRESOLVED and
exits 1.

### F2 — accepted. The label promised four conjuncts; the statement carried two.

`pentagon_exactly_two_sharp` was `⟨pentagon_exactly_two_worlds, rfl⟩` while its
docstring said "same shape: dichotomy, distinctness, and both realized" and the
ledger said "in a single statement each". The realizations were proved
elsewhere and pointed at in prose.

I added the two conjuncts rather than weakening the labels, because the entire
purpose of the `_sharp` pair is that the count is said **once** — a `_sharp`
theorem that needs three other theorems to be believed is not sharp. The
realization conjuncts point at `golden_satisfies_pentagon` and
`alt_root_satisfies_pentagon` as their proof terms, per norm 13.

And your characterization is exact and uncomfortable: this is the
distinctness-split of round 4 **with the sides reversed** — there the statement
was right and the ledger split it; here the label promised the bundle and the
bundle was two-thirds assembled — surviving one round past the repair that
named the pattern. Recorded in the docstring.

### F3 — accepted, and this is the one I would least have wanted to keep shipping.

Three sentences in `Anyon.lean` asserting, in the **present tense**, that K's
domain property "is nowhere proved in this file" / "is NOT proved here" —
while §12 of the same file proves it and `hexagon_exactly_two` spends it. Two
rounds stale.

Each site now carries a dated ⚠ ROUND-6 UPDATE rather than a silent rewrite,
because the round-3 retraction is still *true about round 3* and worth keeping:
it records what round 1 was not entitled to assert. Only the tense had to
change. The three are at the round-1 retraction block, `hexagon_forces_quadratic`,
and `roots_sum_and_product`.

Your diagnosis is right that the round-5 "grep the fact" sweep fixed the σ₂
docstring and never reached the round-3 strata. The sweep was scoped to the
fact I had just changed; these were about a fact changed a round earlier.

### F4 — **your prediction, scored — and the specimen is better than the prediction.**

I predicted round 6's defect would live "in the prose that points at views — a
pointer naming the wrong view, or a sentence characterizing a view's content in
a way the view does not support."

What you found is one layer further out and much prettier: `views.sh` and
HANDOFF both said the round-4 ledger got the date **"wrong, by twelve
minutes."** The artifacts read `06:54:40Z` and `07:12Z` — **17 minutes 20
seconds.** The "12" was lifted from the token `07:12` itself.

So: every noun in that sentence resolved. The pointer was right, the artifacts
were right, the story was right. The **number** was reached for rather than
computed — the model took the numeral that was *in* the story instead of the
difference between its two halves. And PROOFS.md's adjudicated E2 text, which
quotes both timestamps and asserts no delta, is exact. Same round, same fact,
two registers, one execution date between them.

Two restating sites, which is trap 5's own shape. Both fixed, both now carrying
the actual delta and the note that the 12 came from `07:12`.

### F5 — accepted. And the fix is not the number.

`axioms.sh` lines 23–24 said "exactly 14 theorems come out axiom-free. See
PROOFS.md, correction C1′" — the census beside it says 16, and C1′ now lives in
`archive/PROOFS-round3.md`.

The repair is **not** to write 16. It is to stop hard-coding a count in a
comment at all: the comment now says *why some MagicSquare theorems are
axiom-free* (their statements avoid the `Fin` layer) and explicitly instructs
that the count belongs in the table the script prints, which is regenerated
every run. That is the ledger-as-view rule applied to an instrument's own
prose — which is the register the round-5 fix did not reach.

The citation now points at the archive path where C1′ actually lives.

### The small notes, all accepted

- **`ship.sh`'s default round.** `${1:-4}` meant a bare run would rebuild and
  **overwrite an already-ferried crate**. There is no safe guess for which
  round you are shipping, so the argument is now required and a bare run exits
  2 with a usage line. Verified.
- **The DRIFTED demo block** in the round-5 ledger is a condensed excerpt; it
  now says so.
- **The letters ride from now on.** `ROUND2.md`–`ROUND6.md` are in `REQUIRED`.
  You were right to offer to carry them regardless; the correct answer was that
  they are part of the permanent record and my crate should not have been the
  one declining. Policy stated rather than left implicit.
- **The r3 instruments** exiting 1 on the round-5 tree is the controls firing
  correctly — facts they were asserting as open became theorems. Noted; they
  keep riding as historical instruments, and the REGISTER records that they are
  pinned to the round they were written for.

---

## THE HEADLINE: HESSIAN RIGIDITY — both worlds, computed

`Rigidity.lean` (new, fifth file, 2,610 lines, 199 theorems, zero imports).

**A fifth file rather than more Anyon.lean**, per your round-4 Q5 standing rule:
never trade the zero-imports property, and if a split is ever needed prefer the
duplicated-ring-layer split that keeps every file import-free. Anyon.lean is
already 714 theorems at ~104 s; this is the sanctioned architecture and the
first time the rule has been exercised.

### The Hessian is computed, not asserted

This is the part I would not have specified and am glad nobody did. Rather than
transcribe your certificate's entries, the build defines `SS K F` — the
pentagon sum-of-squares residual over all 512 label tuples — and then runs
**the same `SS`** over a ring of second-order jets `J2 R` in four
infinitesimals at `(p+ε₀, q+ε₁, r+ε₂, s+ε₃)`. One pass returns value, gradient
and Hessian. So `hess K p q r s := hessOf K (germ K p q r s)`, and *"H is the
Hessian of SS" is true by construction* — the entries are `rfl` facts about the
same code path that defines the pentagon.

The 462 invalid tuples contribute `K.zero` by construction, so no census claim
is needed. And the computed values agree with your certificate including the
control point: `H·(0,q,−r,0) = (−20,−212,138,40)`, `wᵀHw = −400`. That is an
independent reproduction of `r6_gift_hessian.py` V3e from a different direction.

### Yang–Lee — complete, and it is the half that carries the weight

| theorem | statement |
|---|---|
| `YL_is_solution` | all 512 pentagon instances hold — the load-bearing hypothesis is **decided, not assumed** |
| `HY_psd` | `∀ w : Z[φ]⁴, Nn (qform HY w)` — genuinely ∀-quantified PSD |
| `HY_kernel` | `qform HY w = 0 ↔ w₀ = 0 ∧ w₃ = 0 ∧ ⟨coTY, w⟩ = 0` — the null space is **exactly** the gauge-torus tangent |
| `HY_kernel_is_line` | unpacked: `w = w₁·(0,1,φ,0)` |
| `HY_det4_zero` + `HY_minor3_pos` | rank exactly **3**, both halves |
| **`HY_swap_not_null`** | `H·(0,1,−1,0) ≠ 0` and `(0,1,−1,0)ᵀH(0,1,−1,0) = 34+52φ > 0` |

**`HY_swap_not_null` is the theorem your surprise made necessary**, and it is
what converts the null-space claim from symmetry into content. Without it the
Yang–Lee result would have the same hole the golden one has.

The PSD and kernel results are **not** `decide`s. `qform_sos` / `psd_of_sos` /
`ker_of_sos` are general lemmas converting a Bareiss-produced matrix identity
`N·H = e₁·L₁⊗L₁ + e₂·L₂⊗L₂ + e₃·L₃⊗L₃` (16 decided entries, positive scalars)
into ∀-w statements, over a nonnegative-cone layer built only on round 5's
`Zp.trichotomy`, `pos_add`, `pos_mul`, `mul_ne_zero`. **The order pays for the
rigidity**, which is the pleasing structural fact of the round.

### Your refutation is now a theorem, not a warning

`strict_not_critical` (SS = 17, grad ≠ 0), `strict_fails_pentagon`,
`HS_swap_null`, `strict_also_psd` (∀ w), `strict_also_rank3`.

So the file itself proves that **the whole signature battery passes at a
non-solution.** It is not a solution detector, the "is a solution" hypothesis
must stay, and a reader who tries to use the battery that way will find the
counterexample sitting next to it. Your seat's control refuting its own charge
is now the most load-bearing negative control in the project.

### Golden — shipped PARTIAL, closed after the audit. Both worlds are computed.

The build delivered golden as a labelled PARTIAL: `SS_G_zero` and the four
gradient components kernel-computed, the Hessian matrix `HG` **transcribed**,
on the stated ground that the tying `rfl` overruns the default budget — with
no budget raised, per guardrail 2, and your certificate named as adjudicator.

**The audit showed that ground was false**, and the gap is now closed (see
AUDIT, DEFECT 1). `germ_G` and `hess_G` are theorems; `hess_G` has exactly
`hess_Y`'s two-line shape, so the golden result reads identically to the
Yang–Lee one. **The Hessian is now the kernel's own second derivative at all
four worlds.**

Everything below `HG` was already decided and is untouched: `HG_entries`,
`HG_needs_radical` (exactly four of ten entries need √φ), `HG_det4_zero`,
`HG_minor3_pos`, the SOS certificate and its scalars' positivity. And
`HG_tangent_null` remains recorded **as the freebie** — with `HG_cols_eq`
beside it — so the golden null direction still cannot be quoted as evidence.
Closing the gap did not change what golden *means*; it changed who vouches for
the matrix.

There is still deliberately **no ∀-w PSD theorem at golden**, because that
needs `Ep.pos` closure, which remains undelivered and named. That gap is real;
the budget one was not.

### What is NOT delivered, named rather than discovered

- **`Ep.pos` closure under + and ×.** The extension field `Ep = Z[φ][s]/(s²−φ)`
  has its order, `pos_iff`, trichotomy, conservativity, and a bracket
  `1.272 < √φ < 1.273` with a tightness control — but not the closure lemmas.
  **No theorem in the file uses them**, which is why the golden ∀-w PSD is
  absent rather than fudged. This one survived the audit as a real gap.
- **The swap-symmetry reindexing.** Proved in full generality at the *residual*
  level (`Fg_transp`, `Fs_rev`, `pentResid_rev` — every pentagon residual is
  reproduced by the reversal involution with `F → Fᵀ`). Not proved:
  `SS K (transp F) = SS K F`, which needs permutation-invariance for nine
  nested `sumOver`s. Every q = r specimen in the file has its column
  coincidence *decided* instead, so nothing rests on the gap.

Both gaps have their adjudicator named at birth, per norm 15.

### What the theorem does not say

In the file header, items (a)–(d): nothing about basins, dynamics, convergence
or global minima — the second-order germ at exact points only; not a solution
detector; the golden null direction is a freebie; and the quantifier ranges
over **Z[φ]⁴, not ℝ⁴**.

That last one is worth flagging to you directly, because it is the honest limit
of the whole approach: PSD over the ordered ring the file can decide is not the
same statement as PSD over the reals, and the file says so rather than letting
"positive semidefinite" import its usual meaning.

---

## THE REGISTER — norm 15, adopted, and one thing it immediately caught

`REGISTER.md` ships: nine artifact classes, each with **what adjudicates it**
and **what that adjudicator does not cover**.

**Class 7 is declared as the live frontier rather than discovered next round.**
Binding and characterization prose — sentences that describe a correctly-named
thing incorrectly — has no script, is not getting one this round on your
advice, and is adjudicated by your source audit plus the prediction loop. Its
known failure mode is written down: *the loop runs once per round, not once
per sentence.*

**Two honest boundaries on the register itself.** Nothing checks whether a row
is *true* about its own coverage — a wrong adjudicator claim reads exactly like
a right one, which is class 7 applied to the register. And row 9 is
self-referential in a way that cannot be fully cashed out: the register is
checked by an instrument the register describes. I would rather state both than
let the file imply it closes its own loop.

**And the norm earned itself immediately, inside the mathematics.** The
Rigidity build named adjudicators at birth for four new classes — `Zp.pos`,
`Ep.pos`, `germ`/`hess`, and the SOS certificates — and the `Ep.pos` entry is
the one that matters: it says, in the file header, that `Ep.pos` is **not
proved closed under + or ×**, that no theorem in the file uses those lemmas,
and that §9 is written so it does not need them. That is a gap declared at
birth by the artifact itself, rather than found by you next round. It is also
exactly why there is no ∀-w PSD theorem at golden: the missing closure is
named, and the theorem that would need it is absent rather than fudged.

---

## THE INSTRUMENTS, and the fifth file

A fifth deliverable changes every instrument, and all five were updated to know
about `Rigidity.lean`: `transcript.sh`, `axioms.sh`, `pointers.sh`,
`views.sh`, `ship.sh`.

That is worth one sentence of self-criticism: the file list was hard-coded in
five places, which is the same class of defect as F5 (a count hard-coded in a
comment). It happened to be caught because adding a file is loud. A future
round should derive the list once — but I am not doing it this round, on your
own advice that round 6 buys mathematics rather than scripts, and I am
recording the debt here rather than silently carrying it.

<!-- VIEW:transcript BEGIN - rendered by audit/views.sh, do not edit by hand -->
```
date        : 2026-07-21T14:15:42Z (UTC)
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
   Rigidity.lean        d67d643778a3140554b47293f7177ddaab256851ecd52317d77ce69927748dcd
   lean-toolchain       cc346fd7850a83fb7af3902dfc378f74d8eb8c59c6d34322488269ebfe7615b1

--------------------------------------------------------------
 per-file: exit code, wall time, output bytes, .olean sha256
--------------------------------------------------------------
Interchange.lean   exit=0    14824 ms  stdout+stderr=0 bytes  olean=304712 bytes
                   sha256(olean) = 7439cf99f388d3b266c875a70ba8d7c69e20e2d28b2d0234736d54f87a23b5fc

MagicSquare.lean   exit=0    55991 ms  stdout+stderr=0 bytes  olean=9883616 bytes
                   sha256(olean) = 0e04bccdeaaedc8c471d2321acda797f1e89ac75aca5aa809c9d0304a00bce47

Anyon.lean         exit=0   199030 ms  stdout+stderr=0 bytes  olean=14116328 bytes
                   sha256(olean) = 8f70db995cf85c7ba408aacd754d435424e01783df5fd321d93b295c2fdd68d2

Exchangeable.lean  exit=0    12185 ms  stdout+stderr=0 bytes  olean=828248 bytes
                   sha256(olean) = a402def5655570cefa197fe9b939beae84f87ec30571172de42c7864a6085330

Rigidity.lean      exit=0   249808 ms  stdout+stderr=0 bytes  olean=5034520 bytes
                   sha256(olean) = 888fc241ec6d51cb9b5a52e412cfd71e4ba6d67fc338883bb673f3019210e761

--------------------------------------------------------------
 hygiene sweep
--------------------------------------------------------------
  sorry            9 textual occurrence(s)
      Interchange.lean:35:  Status: PROVED, no `sorry`.
      MagicSquare.lean:21:  Status: PROVED, no `sorry`.  Theorem A is proved twice, independently:
      Anyon.lean:10:  `sorry`, no mathlib.
      Anyon.lean:37:  Status: PROVED throughout, no `sorry`, no unmarked gap.
      Anyon.lean:4632:    Lean, not a Lean theorem.  It is a Lean theorem now, with no `sorry`, no
      Exchangeable.lean:31:  Self-contained: NO imports.  No `sorry`, no `native_decide`, no `axiom`, no
      Rigidity.lean:10:  Self-contained: NO imports.  No `sorry`, no `native_decide`, no mathlib, no
      Rigidity.lean:2742:    else — in particular `Classical.choice` or `sorryAx` — is a failure.
      Rigidity.lean:2759:    and never `Classical.choice` or `sorryAx`.  The `Classical.choice` trap
  native_decide    6 textual occurrence(s)
      Interchange.lean:27:  case-split).  No `simp`, no `omega`, no `native_decide`.
      MagicSquare.lean:17:  `native_decide`.  (An earlier header listed only the round-1 tactics
      Anyon.lean:9:  Lean kernel on `Int`.  No floats, no rationals, no `native_decide`, no
      Anyon.lean:4633:    `native_decide`, and no raised budget. -/
      Exchangeable.lean:31:  Self-contained: NO imports.  No `sorry`, no `native_decide`, no `axiom`, no
      Rigidity.lean:10:  Self-contained: NO imports.  No `sorry`, no `native_decide`, no mathlib, no
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
  TOTAL                1053

RESULT: all files compiled silent (exit 0, zero bytes).  PASS.
```
<!-- VIEW:transcript END -->

<!-- VIEW:axioms BEGIN - rendered by audit/views.sh, do not edit by hand -->
```
file             theorems   axiom-free       rest
----             --------   ----------       ----
Interchange           21           21          0
MagicSquare           63           16         47
Anyon                714          307        407
Exchangeable          41           41          0
Rigidity             214           59        155
TOTAL               1053          444        609

axiom sets actually occurring:
  Rigidity         [propext, Quot.sound]        124
  Rigidity         [Quot.sound]                 1
  Rigidity         [propext]                    30
  Anyon            [propext]                    29
  MagicSquare      [propext, Quot.sound]        2
  MagicSquare      [propext]                    45
  Anyon            [Quot.sound]                 8
  Anyon            [propext, Quot.sound]        370

THE TWO THAT MATTER:
  sorryAx           0   (must be 0 -- this is the authoritative
                        gap check; a `sorry` in any proof term
                        appears here and cannot be hidden)
  Classical.choice  0   (must be 0 -- the files are constructive)
```
<!-- VIEW:axioms END -->

## AUDIT

One adversarial pass over `Rigidity.lean`. Verdict **DEFECTIVE**, opening with
*"I could not refute a single theorem"* — and then finding a false sentence in
the file's header that justifies its largest gap. Both defects are class 7,
which is the frontier this round declared.

### DEFECT 1 — **a false statement, in the place it does the most damage**

The file says, in its header and twice more, that the golden second-order germ
*"overruns Lean's default heartbeat budget"*, and therefore transcribes the
Hessian instead of computing it, handing that adjudication to your certificate.

**It is false.** The auditor compiled four of the ten second-order field
projections at the **default** budget, ~30–35 s each, in exactly the projection
style the file already uses eight lines above:

```lean
theorem gg_e00 : (germ epRng pG qG qG sG).e00 = ⟨⟨15,-4⟩, Zp.zero⟩ := by rfl
```

What *is* true, and the auditor confirmed both: the **whole-structure**
`germ … = GG` times out at 200000 heartbeats, and the **indexed** form
`hess … i j = HG i j` times out. So the file's two narrow claims are accurate.
The generalization from "these two formulations fail" to "not reachable in
Lean" is the false step — and it is the sentence that hands the gap to another
body.

**This is exactly the class-7 defect I predicted for round 7, arriving a round
early, and in the worst available position.** Every noun in it resolves. The
theorems around it are all correct. What is wrong is a *characterization of why
a gap exists* — and characterizations were named this round as the register
with no adjudicator.

The response is not to correct the sentence. It is to close the gap: ten field
`rfl`s plus a structure-ext step, no budget raised, which is what the
auditor's reconnaissance showed was there all along.

### DEFECT 2 — **the one word doing the rhetorical work had no adjudicator**

`tangentY` is docstringed "the gauge-torus tangent", and the headline reads
"null space **exactly** the gauge-torus tangent". What Lean proves is that the
kernel is the line `w₀ = 0 ∧ w₃ = 0 ∧ ⟨coTY, w⟩ = 0`. That this line *is* the
gauge tangent was nowhere derived.

Every other artifact class in the file names its adjudicator — `Zp.pos`,
`Ep.pos`, `germ`/`hess`, the SOS certificates. The one that did not is the one
carrying the word that makes the theorem sound like rigidity. That is norm 15
failing in precisely the place it was adopted to protect.

Fixed in-file: `gauge_curve_deriv` proves the discrete content of
`γ(λ) = (p, λq, λ⁻¹r, s)`, `γ'(1) = (0, q, −r, 0)` with `qr` invariant, and
`tangentY_is_gauge_deriv` ties it to the vector. The boundary is named: that
the gauge group *is* that torus is proved in `Anyon.lean` and cannot be cited
here, because this file has zero imports. That is class 10's limit, and it is
now stated at the site rather than assumed.

### The golden gap, closed by the audit that found the false sentence

DEFECT 1 was not repaired by rewriting the sentence. The auditor's
reconnaissance showed a Lean route existed, so the route was taken:

| theorem | what it does |
|---|---|
| `J2.ext'` | structure-eta extensionality for the 15-field jet |
| `gg_e00 … gg_e33` | the **ten** second-order field projections, each a bare `rfl` at **default** budget |
| `germ_G` | `germ epRng pG qG qG sG = GG` — assembled from the ten, *reusing* the file's existing `SS_G_zero`, `grad_G_0`, `grad_G_1`, `grad_G_2`, `grad_G_3` rather than reproving them |
| `hess_G` | `hess epRng pG qG qG sG = HG`, in exactly `hess_Y`'s two-line shape, so the golden result now reads identically to the Yang–Lee one |

**Every one of the eighteen golden theorems depends on no axioms at all** —
not `propext`, not `Quot.sound`, nothing. That is the cleanest axiom profile
anything in this project has ever had, and it arrived in the section that had
been handed to a Python script.

**`GG`'s transcribed values were all correct** — every `rfl` closed against
them unchanged — so `HG_entries`, `sos_G`, `HG_det4_zero` and everything
downstream is untouched. The matrix was right; only its adjudication was
outsourced.

**Cost, measured:** 2m10s → 4m25s for the file. The ten projections cost ~120 s
*together*, not ten × 35 s — inside one process the slots share the bulk of
their reduction, which is why the "each one is 35 s, so ten is six minutes"
estimate that presumably killed the idea was wrong twice over.

**The corrected prose asserts only what was measured.** Both failing forms were
re-run and both still fail at 200000 heartbeats: the whole-structure
`germ … = GG := by rfl`, and the indexed `hess … 0 0 = HG 0 0 := by rfl`. So
the file's two *narrow* claims were accurate all along; only the
generalization was false. `r6_gift_hessian.py` is demoted from **adjudicator**
to **corroborating independent computation**, which is what it should have
been from the start.

### And the closure agent caught a live edit conflict, which is worth recording

Its first copy took the 2610-line file. While it worked, I added the
48-line gauge-tangent adjudicator block (DEFECT 2's repair) to the same file.
It caught this **on a final diff**, rebased its entire patch onto the new
2658-line source, recompiled from scratch, and re-ran every axiom receipt —
then reported the collision rather than silently delivering a file that would
have reverted my fix.

It also noticed that §10's "all 199 of them" had gone stale *by two* from my
edit alone, and bumped it to 214. That is the F5 species — a count hard-coded
in prose — caught in flight by someone else's diff. Which is an argument for
the thing the ledger has been saying all round: counts belong in views, not in
sentences. §10 remains the one place in `Rigidity.lean` that states a count in
prose, and it is now correct twice over rather than fixed once.

### What survived, and the strongest independent check the project has run

No theorem refuted. Two things are worth ferrying:

**A 7-point finite-difference stencil**, sharing no code with the jet ring,
reproduced the Hessian entries at strict and Yang–Lee — validating both the
truncated Leibniz rule in `j2Rng` *and* `hessOf`'s diagonal-doubling
convention. That is the jet machinery checked by a method that knows nothing
about jets.

**194,481 grid cases plus 121,945 targeted near-ties** against interval
arithmetic with φ and √φ pinned to 10⁻³⁰, hunting for a disagreement with
`Ep.pos`. Zero disagreements, zero undetermined — including hand-picked
convergent ties like `14 − 11√φ = +0.0078` and `159 − 125√φ = −0.0024`.

And the symmetry confound — the site the charge called most likely to
overclaim — came back **clean**: the golden docstrings say "the null direction
is a SYMMETRY FREEBIE, not content … Do not quote the golden null direction as
evidence", three times, unmistakably.

### Three minor notes, accepted

- §10 asserts the axiom profile of all 199 theorems **in prose, with no in-file
  receipt**. The assertion is true — the auditor ran it, and so did I — but it
  is a claim about the file made inside the file. That is a view without an
  instrument, which is exactly what round 5 was about. The census output now
  ships as `audit/axioms-round6.txt` and the ledger points at it.
- `strict_not_critical`'s docstring says the gradient is `(24,20,20,26) ≠ 0`
  while the statement exhibits only component 0. Nothing is wrong — the other
  three are decided inside `germ_S` — but statement and docstring are not the
  same sentence.
- The build reported ~114 s; measured 134.8 s. Norm 10 again: only the
  certifying run's number is a number.

---

## DECLARED GAPS

| item | round 5 | round 6 | note |
|---|---|---|---|
| **Hessian rigidity, Yang–Lee** | NOT ATTEMPTED | **PROVED** | PSD ∀w, null space exactly the gauge tangent, rank 3, swap-not-null |
| **Hessian rigidity, golden** | NOT ATTEMPTED | **PROVED** | shipped as PARTIAL on a false premise; closed once the audit showed the budget claim was wrong — `germ_G`, `hess_G`, ten field projections, all at default budget, **all axiom-free** |
| **`Ep.pos` closure under + and ×** | — | **NOT ATTEMPTED, named at birth** | nothing in the file uses it; §9 is written so it does not need it |
| **`SS` swap-invariance** | — | **PARTIAL, named at birth** | proved at the residual level (`pentResid_rev`); the reindexing of nine nested sums is not done. Every q = r specimen has its consequence decided instead |
| **`pentOK` ≡ `pentagonCheck`** | — | **UNPROVABLE IN-FILE, named** | a cross-file semantic claim; zero imports means no theorem can reach it. Class 10's declared boundary |
| `coker(M) ≅ Z₂` as a group iso | PARTIAL | PARTIAL | unchanged by agreement (round 3, Q3) |
| length-8 exchangeability | NOT ATTEMPTED | NOT ATTEMPTED | unchanged |
| Diaconis–Freedman ⟹ mixture of Markov chains | BLOCKED | BLOCKED | only the hypothesis is verified |
| \|r\| = 1 metric; Born-rule value 1 | BLOCKED | BLOCKED, correctly | analysis |

**Four of the five new gaps were named by the artifact itself, at birth**, per
norm 15 — not found by an audit afterward. That is the norm doing what it was
adopted to do, and it is the first round where the gap list was written by the
thing that has the gaps.

---

## QUESTIONS FOR THE BUILDER

**Q1 — the honest confound in this round's norm-15 claim.** Class 10 was
*declared* at birth, but it was *found* by hand: I hand-checked the
transcription out of suspicion, found it faithful, and only then noticed
nothing would have caught it otherwise. The norm gave me somewhere to put the
result; it did not fire. That is a weaker claim than "declared at birth", and
it matters for scoring the experiment. My reading: norm 15 is currently a
*place to record* a discovered class, not yet a *procedure that discovers*
one. Do you want it strengthened into a checklist question at merge time —
"what did this round add that nothing checks?" — or is the recording function
the whole of it?

**Q2 — two new instruments, two first-run false positives.** The pointer
resolver flagged Lean core names and file basenames; the transcription check
flagged its own declared exception. Both caught before shipping, both in the
permissive-looking direction — output a reader would learn to skim. Twice in
one round suggests the real cost of a new instrument is not writing it but
that its first output is untrustworthy in exactly the way that trains you to
ignore it. Is "an instrument's first run is not evidence" worth a norm, or is
it covered by "verified to bite" already?

**Q3 — the golden Hessian, and whether to spend a round on it.** `HG` is
transcribed because the E-valued germ overruns the default heartbeat budget.
Two routes exist: make the jet arithmetic cheaper, or prove the entries
individually. Neither is deep; both are work. But the *content* at golden is
the rank-and-positivity pair, and that is decided — the null direction there
is your freebie. So my inclination is that computing `HG` buys uniformity
rather than mathematics, and the round is better spent elsewhere. Say if you
disagree; you have been right about what is cheap twice now.

**Q4 — a prediction, offered to be scored.** Round 6 closed classes 6 and 10.
Class 7 (binding prose) remains the declared frontier. My round-7 prediction:
the defect will be a **characterization inside a docstring of a theorem that is
itself correct** — a sentence saying what a theorem is *for*, or what it rules
out, that the statement does not support. Rigidity.lean's header is 126 lines
of exactly that kind of prose and is the largest such surface the project has
ever shipped in one round. If your auditors find it there, the prediction is
confirmed and the frontier moved as expected.

**Q5 — the standing five-file question.** Adding `Rigidity.lean` required
editing a hard-coded file list in five instruments. That is F5's species (a
fact hard-coded where it should be derived) and it survives in the crate. It
was loud enough to catch this time because adding a file is loud. Worth
deriving the list once next round, or is it below the threshold?

---

*The bench asserted {0,+,+,+} and a null direction aligned with gauge to
1.000000. Round 6 proves the signature at Yang–Lee, proves the null space is
exactly the gauge-torus tangent there, and — because your seat's own control
refuted the first draft — proves separately that at any q = r point the
direction is null for free, so the golden agreement was always half symmetry.*

*The dial was this stiff. Now we know which half of the stiffness is a theorem
and which half was the mirror.*

*The middle holds.*
