# PROOFS — Round 3

Lean 4 formalization of workshop results. Third body reporting — a *fresh*
instance, continuing the predecessor that crashed twice mid-round-3. Cumulative:
this supersedes the round-2 ledger and marks what changed.

**Toolchain:** Lean 4.32.0, bare (`elan` + `lean`; no `lake`, no mathlib, no
Std). Every file has **zero imports**. `lean-toolchain` pins the version.

Two audit instruments now ship with the round, per your Q4:
`audit/transcript.sh` (compile transcript + `.olean` hashes) and
`audit/axioms.sh` (the axiom census). Both are re-runnable in one command,
which is the point — round 2's axiom row was disputed and could only be
settled by re-running the instrument.

**Round 3 in one line: both coherence equations are now necessity theorems.**
191 → **370 theorems**, 0 `sorry`, 0 `native_decide`, 0 `Classical.choice`,
zero imports, all four files compile silent.

## COMPILE TRANSCRIPT — `.olean` hashes (Q4)

```
date      : 2026-07-20T12:50:11Z (UTC)
host      : MINGW64_NT-10.0-26200 x86_64
toolchain : leanprover/lean4:v4.32.0
lean      : 4.32.0, x86_64-w64-windows-gnu, commit 8c9756b28d64dab099da31a4c09229a9e6a2ef35

Interchange.lean   exit=0   1579 ms   0 bytes   olean   304712 B
  sha256  7439cf99f388d3b266c875a70ba8d7c69e20e2d28b2d0234736d54f87a23b5fc
MagicSquare.lean   exit=0  35494 ms   0 bytes   olean  9883616 B
  sha256  0e04bccdeaaedc8c471d2321acda797f1e89ac75aca5aa809c9d0304a00bce47
Anyon.lean         exit=0  55941 ms   0 bytes   olean  6160504 B
  sha256  84ea435ad732727e0b21d03e4f429bf9d6890aafb70b1fbde9475596e2576dbb
Exchangeable.lean  exit=0  14207 ms   0 bytes   olean   828248 B
  sha256  a402def5655570cefa197fe9b939beae84f87ec30571172de42c7864a6085330

RESULT: all files compiled silent (exit 0, zero bytes).  PASS.
```

A live demonstration that the hashes are load-bearing rather than decorative:
an earlier run in this same round gave Anyon `b29eb596…` at 6173104 bytes. The
only change between the two was the six-line repair of `Zp.toKK_injective`
described under AUDIT — and the hash moved. Two `.olean`s agreeing is
therefore a real claim about two kernels having accepted the same terms, not
a formality.

---

## CORRECTIONS, LOUDEST FIRST

### C1″ — **C1′ is refuted. The round-2 axiom row was right; its *explanation* was wrong.**

C1′ asked me to re-run `#print axioms` on MagicSquare because
`51 | 14 | propext; 2 also Quot.sound` was "impossible as stated": at least 26
of the 51 are literal `rfl`, "which cannot depend on any axiom."

I re-ran it. **The row is correct exactly as written.** 51 theorems, 14
axiom-free, 35 `[propext]`, 2 `[propext, Quot.sound]`.

The premise is what fails. `#print axioms T` reports the axioms of the whole
transitive closure of `T` — **including the definitions that appear in `T`'s
statement**, not merely the constants in its proof term. A literal `rfl` proof
of a statement mentioning an axiom-tainted definition inherits that taint.

Minimal receipt, no imports:

```lean
def g3 (a b c : Bool) : Bool := Bool.xor a (Bool.xor b c)
theorem g3_rfl : g3 false false false = false := rfl   -- axiom-free

def f3 (v : Fin 3 → Bool) : Bool := Bool.xor (v 0) (Bool.xor (v 1) (v 2))
theorem f3_rfl : f3 (fun _ => false) = false := rfl     -- depends on propext
```

Same function, same `rfl`, different axiom set — the only difference is `Fin`
indexing. Bisected: a `Nat`-indexed version is clean, a `Fin`-indexed one
carries `propext`, and an explicit `⟨0, by omega⟩` index carries
`[propext, Quot.sound]`.

In `MagicSquare.lean` the root is `Assignment := Fin 3 → Fin 3 → Bool`.
Probing definitions directly: `rowPar`, `inCtx`, `yM`, `isCocycle` carry
`propext`; `par`, `mkY`, `yEnumSize` do not. That is exactly why 14 come out
clean — they are the ones whose statements avoid the `Fin`-indexed layer.

**But C1′ found something real, and it belongs on the record.** My round-2
prose attributed the axioms to "artifacts of `simp`/`omega`". For MagicSquare
that is wrong, and your auditors were right to call it impossible-as-explained:
the file has zero `simp` and exactly two `omega`. The two `omega` uses are
precisely the two `Quot.sound` theorems — `no_perfect_script` and
`satCount_ne_six` — so that half was right. The other 35 come from `Fin`, not
from a tactic. The attribution in the table below is corrected.

Net: the ledger's *count* survived the challenge; the ledger's *reasoning* did
not. The challenge was worth making — I would not have found the `Fin` root
without being told the row was impossible.

### C2′ — accepted, discharged by proving rather than trimming.

`KK.add_comm`, `KK.add_assoc`, `KK.add_mul` were asserted by the round-2 ledger
and were not in the file. I proved all three, plus `add_left_comm`,
`mul_left_comm`, `mul_right_comm`, and the negation laws (`neg_mul`, `mul_neg`,
`neg_neg`, `add_neg`, `neg_add_cancel`, `neg_add`) at both the `Z5` and `KK`
levels.

They were not decorative. Both hexagon residuals carry a `neg invPhi`, so
without the negation laws the assembly cannot even be *stated* in the form the
instances produce; and `mul_right_comm` is the workhorse that slides the stray
`b` to the end of a product so its unit can delete it.

The house rule stands as you wrote it: the ledger asserts nothing the file does
not contain.

### C3′ — accepted in full.

- `sepPar_noncommutative` → **`sepPar_not_comm`**; `sepPar_has_no_unit` →
  **`sepPar_no_left_unit`** (with `sepPar_no_unit` for the two-sided form). You
  are right that the file is more careful than the ledger was: `SepModel` kills
  the *left* unit and **`MirModel` closes the right-unit side**
  (`mirPar_no_right_unit`), so the honest statement is that neither a left-unit
  law nor a right-unit law for `par` is derivable from `PreInterchanging`.
- Stale round-1 tactic-list headers at `Interchange.lean` and
  `MagicSquare.lean` — replaced with precise, checkable lists (Interchange:
  core tactics plus `decide` on closed `Bool` goals, no `simp`, no `omega`;
  MagicSquare: five `decide`, exactly two `omega`).
- Empty docstring on `Exchangeable.lean`'s `num_pOnes` — filled.

### C4 — **a correction to myself, recorded against myself.**

I briefed the gauge task with `λ = diag(t, 1)`. That is **backwards**: the
correct assignment for the relation as I wrote it is `λ = diag(1, t)`. My
derivation of the *ratio* was right — it is `t`, consistent because `t·b = 1` —
I inverted which label carries it.

Both are theorems in the file, so the record cannot be tidied after the fact:
`gauge_clean = 0` for the correct λ and `sketch_gauge_fails = 2` for mine. The
sketch is rehabilitated rather than merely rejected: `diag(t,1)` is `t` times
the *inverse* gauge, so it satisfies the relation with the two associators
exchanged (`gauge_relation_reversed`).

Eighth correction in the project's ledger, and the first where the third body
is the one overruled.

### C5 — **a second correction to myself: my pentagon prediction was wrong.**

I predicted the pentagon would force `p² + q·r = p`. It does not. The correct
residual is `p² + q·r = **1**` (instance #1), and it is the *separate* instance
#4 (`q·r = p`) that converts it into `p² + p = 1`. Sanity check I should have
run before predicting: at the known solution `p = 1/φ ≈ 0.618` and
`q·r = b² = 1/φ`, so `p² + qr = 0.382 + 0.618 = 1`, not `p`.

The error was conservative — it named the right *relations* and the wrong
*route* — but it is the second time this round my stated expectation was
wrong and the machine was right, which is the pattern this project keeps
finding and I would rather log than smooth over.

**And a finding I did not predict at all, which matters more.** The pentagon
constrains `q` and `r` **only through their product**. Residuals #2, #5, #8 and
#10 vanish identically once `s = −p` and `p² + p = 1` hold, and every other
residual sees `q` and `r` only as `qr`. So **`q = r` is not forced** — the
symmetric gauge `q = r = b` is a *gauge choice*, not a consequence, and the
residual freedom `q ↦ λq, r ↦ λ⁻¹r` is real.

That is not a defect; it is the pentagon telling us where the gauge group is,
and it lands exactly on top of §9: `Frat` (with `q = 1/φ`, `r = 1`) and
`Fsymm` (with `q = r = b`) are two points of precisely that orbit, and
`λ = t` is the group element connecting them. **Uniqueness is uniqueness of
the diagonal `(p, −p)` plus the product `qr` — nothing more.** The two results
were proved by different agents on different days and neither knew the other's
answer; they fit.

---

## THE ENVIRONMENT-PARITY HANDSHAKE

First action of the round, before any new mathematics.

This machine had **no Lean toolchain at all** — round 2 was compiled on the
predecessor's machine and this is a different one. Installed `elan` and
`leanprover/lean4:v4.32.0`, matching `lean-toolchain` exactly:

```
Lean (version 4.32.0, x86_64-w64-windows-gnu,
      commit 8c9756b28d64dab099da31a4c09229a9e6a2ef35, Release)
```

All four round-2 files recompiled from source: **exit 0 and zero bytes of
output — 0 errors, 0 warnings — on all four.** Parity confirmed.

| file | round-2 machine | this machine | pass |
|---|---|---|---|
| `Interchange.lean` | 2.9 s | 1.6 s | exit 0, 0 bytes |
| `MagicSquare.lean` | 55.8 s | 38.3 s | exit 0, 0 bytes |
| `Anyon.lean` | 65.9 s | 35.9 s | exit 0, 0 bytes |
| `Exchangeable.lean` | 20.1 s | 20.5 s | exit 0, 0 bytes |

A note on timings, because my first set was wrong and I would rather say so
than quietly re-measure. That run overlapped a background compile and reported
Anyon at 88.8 s against the predecessor's 65.9 s — which, had I not noticed,
would have been a false parity signal in the *pessimistic* direction. Timings
are the least portable thing in this ledger. **The pass condition is silence,
not speed.**

---

## THE HEADLINE: BOTH UNIQUENESS THEOREMS

Round 2 delivered the project's first necessity theorem and left the rest
PARTIAL or NOT ATTEMPTED. Round 3 closes both coherence equations.

> **The hexagon forces `r₁ = r_τ²` and `r_τ² + (1/φ)r_τ + 1 = 0`.**
> **The pentagon forces `q·r = p`, `p² + p = 1`, `s = −p`.**

`p² + p = 1` is *verbatim* `X² + X − 1 = 0`. **The pentagon alone — no
braiding, no hexagon, no chosen constants — produces the golden ratio.**
`grammar_stone3.py`'s headline is now a necessity theorem: not "the golden
associator satisfies the pentagon" but "anything satisfying the pentagon is
golden."

### (a) Hexagon uniqueness — the standing PARTIAL, retired

| theorem | status | statement |
|---|---|---|
| `cancel_b`, `cancel_invPhi` | PROVED | the two shims: multiply by `bφ` (resp. `φ`) and delete the stray factor |
| `bphi_is_t` | PROVED | **`bφ = t` exactly** — your noted fact, recorded as a theorem |
| `rt_unit_of_e3` | PROVED | residual #3 ⟹ `(1/φ)(r₁ − r_τ)` inverts `r_τ` |
| `quad_times_rt_of_e5` | PROVED | residual #5 ⟹ `r_τ·(r₁ + (1/φ)r_τ + 1) = 0` |
| `linear_of_e3_e5` | PROVED | the two together ⟹ `r₁ + (1/φ)r_τ + 1 = 0` |
| `hexagon_forces_rt_unit` | PROVED | **coherence makes `r_τ` a unit**, inverse exhibited |
| `hexagon_forces_quadratic` | PROVED | **coherence forces `r_τ² + (1/φ)r_τ + 1 = 0`** |
| `hexagon_uniqueness` | PROVED | both halves in one statement |
| `golden_quadratic_by_necessity` | PROVED | anti-vacuity: the golden braiding inhabits the hypothesis |
| `mirror_satisfies_hexagon`, `mirror_quadratic_by_necessity` | PROVED | so does the mirror — the quadratic really carries both roots |
| `golden_chains_cleared` | PROVED | anti-vacuity one level lower: both cleared chains, evaluated |
| `roots_sum_and_product` | PROVED | `r_τ + r_τ' = −1/φ`, `r_τ·r_τ' = 1` — with an honest label |

**The two bookkeeping facts you asked me to record**, both re-confirmed here by
the kernel:

- **Unit −1 on both chains.** `(LHS₃−RHS₃)·(bφ) = −((1/φ)·r_τ·(r₁−r_τ) − 1)`
  and `(LHS₅−RHS₅)·φ = −(r_τ·(r₁ + (1/φ)r_τ + 1))`. Harmless — both chains
  conclude equalities *to zero* and a unit −1 cannot change whether a thing is
  zero — but it is why the proofs arrive with the sides exchanged relative to
  the display. Recorded in the file comment as asked.
- **`bφ = t` exactly**, now `bphi_is_t` rather than a remark. So `cancel_b` is
  literally "multiply by `t`, divide by `φ`": cancelling one `b` costs exactly
  one factor of `t`, which is why the multiplier is a ring element and not a
  fraction.

**No domain property is used anywhere.** Round 1 called this BLOCKED on K being
an integral domain; round 2 saw that residual #3 makes `r_τ` explicitly
invertible; round 3 spends that inverse. `cancel_of_inv` needs only `mul_assoc`
and the unit laws.

### (b) Pentagon uniqueness — cleaner than the hexagon

Carrying the four associator entries as opaque values of K —
`F(1,1)=p, F(1,τ)=q, F(τ,1)=r, F(τ,τ)=s` — `pentagon_forces_golden` gives
`q·r = p`, `p² + p = 1`, `s = −p`.

Three instances suffice. #1 gives `p² + qr = 1`, #4 gives `qr = p`; substitute
and the golden relation falls out **with no cancellation at all**. Then
`p² + p = 1` makes `p` a unit with `p⁻¹ = p + 1` — for `p = 1/φ` that is
literally `φ = 1/φ + 1` — the pentagon's analogue of `rt_unit_of_e3`, except it
arrives free instead of needing a multiplier. #3 then gives `p·(p+s) = 0`, and
cancelling by that exhibited inverse gives `s = −p`.

**Anti-vacuity, by a technique worth ferrying.** Of the 50 live instances,
exactly **11** are non-trivial for a generic associator; the other 39 hold for
*any* `p q r s` and constrain nothing. That count is not asserted — it is
*machine-decided*, by instantiating the existing `countPentViolations` at a
**free commutative polynomial ring on four generators**, built inside the file.
The same coherence code that runs over K is run over `Poly`, and the violation
count is the number of instances failing to be identically zero. Round 2
reported "39 vanish, 11 nonzero, deduping to 10" from your side; the machine
says 11, and the 11 dedupe to 10 distinct residuals (#6 duplicates #4, #7 is #4
negated). **Two instruments, same numbers.**

Negative controls: `strict_is_Fg_and_fails` (4) and `wrong_is_Fg_and_fails` (5)
show the generic associator specializes correctly to the round-1 witnesses.
`resid_09_of_forced` is a consistency receipt: instance #9, which the
derivation never uses, is discharged by the three forced relations.

**Declared gap, pentagon side — sufficiency is NOT proved.** The file proves
necessity (pentagon ⟹ the three relations). The converse — that the three
relations imply all 50 instances — is not formalized. The residual table shows
all 11 non-trivial residuals vanish under them, but the 39 trivial instances
would each need their own lemma, because `KK.beq u v` on *opaque* values does
not reduce by `rfl` even when the two sides are equal by the ring laws.
Estimated ~39 short lemmas; not attempted. (Sufficiency for the *golden* data
is of course already proved, twice — `pentagon_symmetric_gauge` and
`pentagon_rational_gauge`. What is missing is sufficiency for a generic
associator satisfying the three relations.)

And the same caveat as the hexagon: `pentagon_forces_golden` pins `p` to *a
root* of `X² + X − 1` in K, not to `1/φ`. Which root needs the same
no-zero-divisors property. See Q2.

### (c) Galois conjugation — `chirality_left` becomes structural

`Z5.conj ⟨a₀,a₁,a₂,a₃⟩ = ⟨a₀−a₁, −a₁, a₃−a₁, a₂−a₁⟩` is ζ ↦ ζ⁴ in the reduced
basis. Proved: `conj_add`, `conj_mul`, `conj_neg`, `conj_conj` (an involution,
hence an automorphism), `conj_inj` — at the `Z5` level, then lifted to K **with
no descent to `Int`**. The real subfield is fixed: `conj φ = φ`,
`conj (1/φ) = 1/φ`, `conj t = t`, `conj b = b`.

The payoff landed at full strength rather than the fallback:

> **`hexagonCheck_conj`** — for all `r₁, r_τ` in K and all label tuples,
> `hexagonCheck (conj r₁) (conj r_τ) = hexagonCheck r₁ r_τ`.

**Coherence is a Galois invariant.** It rests on four small lemmas: `conj_Fs`
(the associator fixed pointwise), `conj_Rb` (the braiding carried),
`conj_sumOver` (one list induction), `KK.beq_conj` (conj injective, so the
Boolean test cannot see it). From it, `countHexViolations_conj` — the violation
*count* is Galois-invariant — and `chirality_left_structural` is
`chirality_right` **transported**. The 15 live instances are never re-evaluated
on the mirror constants.

**Honest label, the file's own:** one four-integer `rfl` remains
(`conj ζ² = ζ³` and its partner for `r_τ`). What is eliminated is the
re-grinding of the coherence equations, not every computation.

**The sharp negative control is the best thing in this section.** `badConj` is
additive, bijective, an involution — everything `conj` is *except*
multiplicative. It breaks 5 of the 15 hexagon instances
(`badConj_breaks_hexagon`). So `hexagonCheck_conj` is not a consequence of
conj being a bijection; it genuinely spends `Z5.conj_mul`.

Three receipts upgraded from coincidence to structure: `rt_norm_one`
(`r_τ · conj(r_τ) = 1` — the bench's "|r| = 1 EMERGED" is now literally a field
norm down to the real subfield), `r1_norm_one`, and a structural derivation of
the mirror root of `Q`.

### (d) Gauge equivalence — Tier 3a and Tier 3b are one anyon

`Zp.toKK` embeds Z[φ] into K as a proved, injective ring map (`toKK_add`,
`toKK_mul`, `toKK_injective`). `FratK` is `Frat` read in K, and the two gauges
are related by an invertible diagonal:

> `gauge_relation : λ(x) · Fsymm(x,y) = FratK(x,y) · λ(y)`,
> `λ = diag(1, t)`, `λ⁻¹ = diag(1, b)`, `t·b = b·t = 1` by `rfl`.

Two-sided — `FratK = λ·Fsymm·λ⁻¹` and `Fsymm = λ⁻¹·FratK·λ` — so this is an
**equivalence**, not merely a relation, and `tier3a_tier3b_same_anyon` bundles
it with the embedding facts and `pentagon_FratK`. That retires round 2's
"nothing yet licenses treating 3a and 3b as one anyon."

See C4 above: my briefed λ was backwards, and both versions are in the file.

---

## THE FREE GIFT: `satCount_is_odd` — and it is *not* the twin of `gameScore_is_even`

Your auditor's histogram is confirmed exactly: over all 512 assignments,
**{1: 96, 3: 320, 5: 96}** — only odd values occur. `oneCount_eq_96`,
`threeCount_eq_320`, and the existing `fiveCount_eq_96`, with
`oneCount + threeCount + fiveCount = assignCount` tying all three to the same
nest (norm 9, applied without being asked).

`satBits_is_odd` walks the 512; `satCount_is_odd` lifts it to an arbitrary
`Assignment` through the existing `satCount_eq_satBits` bridge. Then the
payoff: `satCount_ne_six_by_parity` and **`sixCount_eq_zero_by_parity`** — "no
global section" re-derived from parity alone, independent of the sharp bound.

**But the even/odd pair is not symmetric, and the ledger should say so.**
`gameScore_is_even` was an *honest demotion*: it showed `no_perfect_script`
held for parity reasons independent of the ceiling — it took a theorem away.
`satCount_is_odd` does the opposite: it *adds* a route. The workshop now has
**three independent proofs that no global section exists** — the cocycle
certificate (no search), the 512-case exhaustion, and now parity. One deflates
a claim; the other corroborates one. Same shape, opposite status.

The mechanism is the one you named: `y·M = 0` with `y·b = 1` forces the number
of met contexts to be odd — the cocycle's pointwise shadow. Six is even, so no
assignment meets all six. The cohomological obstruction and the parity
obstruction are the same fact read at two resolutions.

---

## HOW THIS ROUND AVOIDED THE CRASH

The predecessor died twice here, descending a K-level identity to `Int` — 16
indeterminates at degree 3 — then raising `simp`'s budget when it timed out.
The guardrails were right, and the route around the wall is made from the
round-2 work itself:

> Every identity in the assembly is degree ≤ 3 in **two** opaque variables,
> with every other factor a concrete constant. So each step is an explicit
> `calc` at the K level using proved lemmas — a dozen small rewrites, no
> search.

Three things made it cheap, recorded for whoever picks this up next:

1. **`mul_right_comm` is the whole trick.** Each residual carries exactly one
   stray `b` (or one `1/φ`); `mul_right_comm` slides it to the end of the
   product where its unit deletes it.
2. **Develop in a scratch file containing only the ring layer.** 200 lines,
   **7 seconds** per iteration against Anyon.lean's ~70. The hexagon assembly
   took three iterations, each failure small and legible.
3. **State the algebra with the instance equation as a hypothesis.**
   `rt_unit_of_e3` takes `e3` as an argument rather than deriving it, which
   separates ring manipulation from coherence extraction and lets each half be
   read — and debugged — on its own.

**No budget was raised at any point this round.** No `simp` search was run on a
K-level ring goal. Nothing descended from KK to `Int`.

---

## AUDIT

Two adversarial passes over the hexagon assembly, run before this ledger was
written. One re-derived the mathematics from the round-2 definitions **without
reading the round-3 proof**; the other tried to refute the round-3 proof
directly. Verdicts: **SOUND** and **DEFECTIVE**. Both were right, and the
second found real defects — all three in doc comments, all three now fixed.

### The independent re-derivation — SOUND, and it found a better proof than mine

Method worth ferrying: transcribe the definitions into a fresh file, build a
sparse polynomial ring `K[r₁,r_τ]`, give it a `Rng` structure, and instantiate
the **unmodified** `hexagonCheck` body over it. The residuals are then computed
by the same code path as the round-2 check, with the unknowns kept opaque.
Every result `rfl`, default budgets. (The pentagon section uses the same trick
over a four-generator ring — the two agents arrived at it independently.)

It confirms every round-2 claim and sharpens three:

- **The 10 trivial instances are characterized**, which round 2 only counted:
  they are exactly those with at least one of `a,b,c` the vacuum, and the 5
  survivors are exactly the tuples at total charge (τ,τ,τ).
- **`r₁ = r_τ²` comes from exactly one instance**, and no other instance has
  that residual.
- **The ideal generated by all 15 residuals is exactly `(r₁ − r_τ², Q)`** —
  both containments proved. That is the sharpest available statement of
  hexagon uniqueness. (It still does not give "exactly two": the ideal is one
  thing, the number of its zeros in K is another, and the second needs no zero
  divisors.)

And a **cleaner cancellation than the one in the file**, which I am recording
because it is better than mine:

> `Res(τ,τ,τ,τ,1,τ) − b·Res(τ,τ,τ,τ,τ,τ) = b·(r_τ² + (1/φ)r_τ + 1)`

An exact identity in `K[r₁,r_τ]`. The `r₁r_τ` cross-terms cancel between the
two instances, and the two `r_τ²` contributions add as `1/φ + 1/φ² = 1` — the
golden relation doing the work. Since `b` is a unit, **instances #3 and #5
alone force `Q = 0`, and `r₁ = r_τ²` is never needed for the quadratic.** My
route derives the linear relation first and then substitutes; this one skips
the substitution entirely. A second, disjoint certificate reaches `Q` without
instance #5 at all.

### The trap — the most valuable thing in the audit

The auditor flagged that the *natural narrative* for this theorem is unsound:
"instance #1 gives `r₁ = r_τ²`; substitute into #5 to get `r_τ·Q(r_τ) = 0`;
cancel `r_τ`." **That cancellation is not licensed by those instances** —
`r₁ = r_τ = 0` is a common zero of them, so nothing there excludes `r_τ = 0`.

Not having read round 3, the auditor could not say whether the file falls into
it, and said so: *"If it uses instance 11 or 12, or discharges r_τ ≠ 0 some
other way, it is fine."* It does — `rt_unit_of_e3` reads residual **#3**, an
`e = 1` instance, which is what carries the constant term that makes `r_τ`
invertible.

The finding is now in the file as three theorems rather than a comment:
`zero_braiding_fails_only_two` (the zero braiding satisfies **13 of 15**),
`zero_braiding_passes_the_tempting_route` (all three instances of the naive
route accept it), and `only_the_e_one_instances_reject_zero` (the instance the
proof actually uses rejects it). So the file now documents why it takes the
route it takes, and a future reader who "simplifies" the proof onto the
tempting route will break a theorem rather than silently lose soundness.

### The refutation pass — DEFECTIVE, three doc-comment overclaims, all fixed

The proofs survived: no vacuity (the hypothesis inhabited twice by axiom-free
closed terms, and shown *restrictive* by an exhibited failing tuple, not just a
count); instance extractions re-derived atom by atom with **seven negative
controls all correctly rejected**; the algebra re-derived end-to-end by an
independent assembly and shown to produce the identical `Prop`; the unit −1
claims proved **symbolically for arbitrary `r₁, r_τ`**, not merely at the
golden constants; cancellation argument order verified by explicit
instantiation rather than by reading.

The defects, all in prose, all repaired:

1. **`roots_sum_and_product` overclaimed twice.** Its "HONEST LABEL" said the
   theorem "shows they are the coefficients' only possible pair" — which needs
   the no-zero-divisors property the same paragraph disclaims two clauses
   later. Self-undercutting. And its headline announced "**THE QUADRATIC
   FACTORS EXACTLY** as `(X − r_τ)(X − r_τ')`" — a true consequence of the
   stated identities, but **not asserted by any declaration in the file**.
   Headline exceeded statement. Both rewritten; the theorem now says the pair
   *realizes* `Q`'s coefficients, and says plainly that the factorization is
   not a declaration here.
2. **Stale round-1 prose asserted "K is a domain" and "exactly two
   solutions"** as steps in an argument — 490 lines above the round-3 doc that
   correctly says the domain property is not proved. The two passages
   contradicted each other. Now carries an explicit ⚠ RETRACTION withdrawing
   both, and noting the aside the auditor added: K *really is* a domain (φ is
   not a square in Q(ζ₅)), but true-and-unproved is exactly what an honest
   label is for.
3. **`cancel_of_inv`'s doc said "two-sided inverse"** where the hypothesis is
   one-sided — the theorem is *stronger* than advertised. Corrected.

That all three defects were doc comments rather than proofs is the part I want
noted: under this project's norms a false label is a defect, and this round
produced three of them while producing no unsound proof. The ledgers remain
where both of us are mortal — and now the file comments are too.

### What the census caught that neither auditor did

Both auditors checked `#print axioms` — on the theorems they were looking at.
The census checks **every theorem in the file**, and it found something they
missed:

> **`Zp.toKK_injective` depended on `Classical.choice`.**

Nothing else in this project ever has. Round 2's ledger says "**No
`Classical.choice` anywhere**", and that sentence had silently become false.

The cause is worth recording because it is a trap anyone would fall into. The
natural proof —

```lean
simp only [… , Zp.mk.injEq] at h ⊢
omega                              -- conjunctive hypothesis, conjunctive goal
```

— typechecks and looks identical in style to the dozen `omega` proofs in the
`Z5` ring layer, all of which are clean. It is not `omega` that is at fault:
letting it close a *conjunctive* goal from a *conjunctive* hypothesis is what
pulls the axiom in. Destructuring by hand first and leaving `omega` a single
scalar goal drops it to `[propext, Quot.sound]`; closing by `subst` instead
leaves only `[propext]`. The file now uses the last of these, with the reason
in its docstring so the "simplification" back to the one-liner is not
inviting.

Two process notes, since this is exactly the kind of thing the round is
supposed to surface:

- **The instrument earned its place the first time it ran.** I built
  `audit/axioms.sh` to settle C1′, an argument about *metadata*. It then caught
  a live hygiene regression in the mathematics. That is a better argument for
  shipping instruments than the one I made in Q4.
- **The failure mode was "an adversarial reader checks the interesting
  theorems."** Both audits were thorough and both were pointed at the hexagon
  assembly. The regression was in the gauge section, in a lemma nobody
  suspected, and only an exhaustive sweep would find it. Norm 7 says a check
  that cannot fail is not a check; this round adds the corollary that a check
  that does not cover everything does not cover the thing you did not think of.

I also fixed a false positive in my own instruments while I was there: a doc
comment in Anyon.lean §6 begins with the word "theorem" at column 0, and both
scripts counted it as a declaration — inflating the theorem count by one and
making the census emit a `#print axioms` for a constant that does not exist.
Both now require a type ascription on the line. The count below is the
corrected one.

---

## AXIOM CENSUS

`sh audit/axioms.sh`, every theorem in every file. **370 theorems** (round 2:
191).

| file | theorems | axiom-free | rest |
|---|---|---|---|
| `Interchange.lean` | 21 | 21 | — |
| `MagicSquare.lean` | 63 | 16 | 45 `propext`; 2 `propext, Quot.sound` |
| `Anyon.lean` | 245 | 141 | 96 `propext, Quot.sound`; 6 `Quot.sound`; 2 `propext` |
| `Exchangeable.lean` | 41 | 41 | — |
| **total** | **370** | **219** | |

```
sorryAx           0
Classical.choice  0
```

**`sorryAx` is the authoritative gap check** — a `sorry` anywhere in a proof
term appears here and cannot be hidden by a comment, which is why the census
now carries it explicitly rather than relying on `grep`.

**Corrected attribution**, replacing round 2's wrong one (see C1″):

- **`propext` in MagicSquare comes from `Fin`**, not from a tactic. The file
  contains zero `simp` and exactly two `omega`. Root:
  `Assignment := Fin 3 → Fin 3 → Bool`, hence `rowPar`, `inCtx`, `yM`,
  `isCocycle`. The 16 clean theorems are exactly those whose statements avoid
  the `Fin`-indexed layer. The two `Quot.sound` theorems are exactly the two
  `omega` uses.
- **MagicSquare went 14 → 16 axiom-free**, and the two additions are precisely
  `ne_of_odd_of_even` and `countB_zero` — the two new lemmas deliberately
  stated over bare `Nat` rather than over `Assignment`. An independent
  consistency check on the whole story: 14 + 2 = 16.
- **`Quot.sound` alone (6 theorems in Anyon)** is a pattern new this round:
  they are the pentagon's `funext` lemmas (`Fg_symm`, `Fg_id`, `Fg_wrong`, and
  the three that consume them). `funext` needs `Quot.sound` and nothing else.
- **`propext, Quot.sound` in Anyon** is the `simp`/`omega` cone, which is the
  attribution round 2 gave — and for *Anyon* it was correct. That is why the
  row looked trustworthy and the MagicSquare row did not.

Care taken on the way in, worth recording because it nearly went the other
way: the first draft of `sixIndicator_zero` used `eq_of_beq`, which drags
`Quot.sound` into MagicSquare — a file where every pre-existing theorem
depends on `propext` alone. It was replaced with `of_decide_eq_true` (valid
because `Nat`'s `==` resolves through `instBEqOfDecidableEq`, so `n == 6` is
literally `decide (n = 6)`), and the file's profile is unchanged. Adding
theorems to a file should not change what the file rests on.

---

## DECLARED GAPS

| item | round 2 | round 3 | note |
|---|---|---|---|
| hexagon uniqueness, the quadratic | PARTIAL | **PROVED** | no domain property used |
| (b) pentagon uniqueness | NOT ATTEMPTED | **PROVED** | `p²+p=1` — φ from coherence alone |
| Galois conjugation as a map | NOT ATTEMPTED | **PROVED** | ring automorphism + full naturality |
| (g) gauge equivalence `Frat ↔ Fsymm` | NOT ATTEMPTED | **PROVED** | `tier3a_tier3b_same_anyon` |
| **"*exactly* two" hexagon solutions** | — | **NOT PROVED, labeled** | needs K to have no zero divisors |
| `coker(M) ≅ Z₂` as a group iso | PARTIAL | PARTIAL | unchanged by agreement (Q3) |
| quantum dimension `d_τ = φ` | NOT ATTEMPTED | NOT ATTEMPTED | parked per Q5; *Perron* needs an order on Z[φ] |
| length-8 exchangeability | NOT ATTEMPTED | NOT ATTEMPTED | closed form is length-independent; exhaustions need regenerating |
| Diaconis–Freedman ⟹ mixture of Markov chains | BLOCKED | BLOCKED | only the hypothesis is verified, never the theorem |
| \|r\| = 1 metric; Hessian rigidity; Born-rule value 1 | BLOCKED | BLOCKED, correctly | analysis — though `rt_norm_one` now gives \|r\|=1 *algebraically* |

Two of the three standing PARTIALs are retired. The one that remains
(`coker(M) ≅ Z₂`) remains by agreement, not by defeat.

**One gap is new, and I am declaring it rather than letting it hide inside a
success.** Hexagon uniqueness proves the quadratic and exhibits both roots. It
does **not** prove there is no *third* root of `Q` in K — that needs
`(s−r_τ)(s−r_τ') = 0 ⟹ s = r_τ ∨ s = r_τ'`, i.e. K having no zero divisors,
which is not proved here. "The hexagon forces this explicit quadratic" is a
theorem; "exactly two braidings exist" is not yet. The same caveat applies to
the pentagon: `p² + p = 1` is forced, and `p = 1/φ` is *a* root, but pinning
`p` to that root rather than the other one is the same missing step. See Q2.

---

## QUESTIONS FOR THE BUILDER

**Q1 — C1′, back at you.** I believe C1′ is refuted and the round-2 row was
right; `audit/axioms.sh` reproduces it in one command. But your auditors are
careful and I would rather this be settled than won. The crux is one claim:
*does `#print axioms` traverse the definitions in a theorem's statement, or
only its proof term?* I say the former, and `g3_rfl`/`f3_rfl` above are a
two-line decisive test that needs no toolchain to reason about — only
agreement about what the command means. If you concur, the correction that
survives is the narrower one your auditors actually found: my *attribution* to
`simp`/`omega` was wrong. If you do not concur, name a test and I will run it.

**Q2 — the one place a domain would still buy something.** Both uniqueness
theorems are now proved without any integral-domain property, which is the
pleasing part. But "*exactly* two" needs K to have no zero divisors. Proving it
mathlib-free means building a norm map `K → Z` and proving it multiplicative:
real work, maybe a round. Worth it, or is "coherence forces this explicit
quadratic, and here are both its roots" the statement the project actually
wants? My inclination is that the quadratic is the content and the domain
property is bookkeeping — but whether the ledger should carry "exactly two" as
a theorem is your call.

**Q3 — the even/odd pair is asymmetric.** `gameScore_is_even` deflated a
theorem; `satCount_is_odd` adds a third independent route to "no global
section". Worth a sentence in FINDINGS, or a file-level remark?

**Q4 — timings, and what they are worth.** `.olean` hashes and the transcript
now ship. One caution learned the hard way: my first timing run overlapped a
background compile and reported Anyon 35% *slower* than the predecessor's
machine — a false parity signal I nearly recorded. I propose the transcript's
pass condition stay **exit 0 + zero bytes**, with wall-clock recorded but
explicitly not load-bearing. Agreed?

**Q5 — what round 4 is for.** With both coherence equations retired, the
obvious candidates are: (i) the norm map, which would upgrade both uniqueness
theorems from "forced quadratic" to "exactly two"; (ii) the quantum dimension
`d_τ = φ`, still parked on wanting an order on Z[φ] — but note the Galois layer
now gives the norm form for free, and *Perron* may be reachable through it
rather than through analysis; (iii) length-8 exchangeability. My inclination is
(i), because it is the one that finishes something rather than starting
something, and because it is the last place either uniqueness theorem is
softer than its headline.

**Q6 — a process note, offered not asked.** This round I used a scratch file
holding only the ring layer to develop the hexagon assembly: 7-second compiles
instead of 70. The predecessor crashed working directly in Anyon.lean, where
every failed experiment cost a minute and printed megabyte terms. If a round 5
body inherits this, the single most useful thing in the crate may be the habit
rather than the theorems. Worth a line in the handoff?

---

*Both coherence equations are now necessity theorems. The pentagon conjures φ;
the hexagon conjures the two chiralities; and the mirror is no longer a
coincidence that checks out but a Galois conjugate that must. Three times now,
the thing that was "out of reach" was one observation away — and this time the
observation was already in the crate, written by the instance that did not
survive to use it.*
