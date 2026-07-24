# PROOFS — Round 2

Lean 4 formalization of workshop results. Third body reporting. Cumulative:
this supersedes the round-1 ledger and marks what changed.

**Toolchain:** Lean 4.32.0, bare (`elan` + `lean`; no `lake`, no mathlib, no
Std). Every file has **zero imports**. `lean-toolchain` pins the version.

```
lean Interchange.lean      #  2.9 s
lean MagicSquare.lean      # 55.8 s
lean Anyon.lean            # 65.9 s
lean Exchangeable.lean     # 20.1 s
```

Exit 0 **and silence** is the pass condition. All four are silent: 0 errors,
0 warnings.

**Audit.** 191 theorems (was 64). `#print axioms` on every one:

| file | theorems | depend on NO axioms | rest |
|---|---|---|---|
| `Interchange.lean` | 21 | 21 | — |
| `MagicSquare.lean` | 51 | 14 | `propext`; 2 also `Quot.sound` |
| `Anyon.lean` | 78 | 52 | `propext, Quot.sound` (from `simp`/`omega`) |
| `Exchangeable.lean` | 41 | 41 | — |
| **total** | **191** | **128** | |

**0 uses of `sorryAx`. No `Classical.choice` anywhere** — the only axioms
appearing in any report are `propext` and `Quot.sound`, both artifacts of
`simp`/`omega`, not of any mathematical gap. No `native_decide`.

---

## THE HEADLINE: NECESSITY

Everything before round 2 verified that *chosen* data satisfies the coherence
equations — sufficiency. The bench's actual claim is necessity ("exactly TWO
solution clusters … obeying r₁ = r_τ²"). Round 2 delivers the first necessity
theorem of the project.

**`hexagon_forces_r1_eq_rt_sq`** — for *any* `r₁, r_τ` in K whatsoever, if the
hexagon holds then `r₁ = r_τ²`. Not a property of the golden pair; a constraint
on every possible braiding. This upgrades `grammar_hexagon.py`'s
`assert abs(r1 - rt**2) < 1e-6` from an observation about two found clusters
into a consequence of coherence.

The mechanism: the hexagon instance at `(a,b,c,d,e,z) = (τ,τ,τ,1,τ,τ)` reduces
— by `rfl`, since every label is concrete — to an equation whose residual is
*verbatim* `r₁ − r_τ²` with unit exactly +1. `hex_at_r1` is that reduction;
`golden_satisfies_hexagon` shows the hypothesis is inhabited, so the theorem is
not vacuous; `golden_r1_eq_rt_sq_by_necessity` then obtains for the golden data
by necessity what `r1_eq_rt_sq` obtained by computation.

### The ring layer (the component you approved, built once)

`Z5` and `KK` are now commutative rings with proved laws — `add_comm`,
`add_assoc`, `mul_comm`, `mul_assoc`, `mul_add`, `add_mul`, unit and zero laws.
No `ring` tactic, no mathlib. The trick, worth recording:

> `Z5`'s laws reduce to `Int` identities that are **linear in the product-atoms**.
> `simp only` distributes and right-associates so both sides share atoms
> `uᵢ * (vⱼ * w_k)`; then `omega` — which abstracts nonlinear subterms as atoms —
> closes them. `KK`'s laws lift from `Z5`'s without descending to `Int`.

One definitional change was required: `KK.mul`'s second component is now
`Z5.add (Z5.mul u.x v.y) (Z5.mul u.y v.x)` rather than `… (Z5.mul v.x u.y)`.
Equal by commutativity, but the canonical operand order is what lets the triple
products in `mul_assoc` canonicalize so `omega` can match atoms. All round-1
`rfl` theorems are unaffected (closed terms evaluate identically).

### C3 revisited: the round-1 BLOCKED label was wrong twice over

Round 1 called uniqueness BLOCKED on K being an integral domain. Round 2 shows
**the domain property is not needed at all**:

> Residual #3 gives `(1/φ)·r_τ·(r₁ − r_τ) = 1` — so `r_τ` is **explicitly
> invertible**. Residual #5 gives `r_τ·(r₁ + (1/φ)r_τ + 1) = 0`. Cancel by the
> exhibited inverse. No domain argument anywhere.

`cancel_of_inv` is that cancellation, proved from `mul_assoc` and the unit laws
alone. Every component of the argument is now a theorem: both instance
extractions (`hex_at_3`, `hex_at_5`, by `rfl`) and both invertibility receipts
(`b_unit`, `invPhi_unit`, by `rfl`).

**What remains: PARTIAL.** The rewriting that carries `hex_at_3`/`hex_at_5`
into the two displayed forms is not done. That is mechanical ring
manipulation, not a mathematical gap — but it is not done, and the theorem
`hexagon_forces_quadratic` does not exist. I am not claiming it. Verified
outside Lean in exact integer arithmetic; the route is in the file's doc
comment. Pentagon uniqueness (item b) is **NOT ATTEMPTED** — same machinery,
no time this round.

Carrying your auditor's bookkeeping precision, confirmed independently here:
of the 15 hexagon instances **10 vanish identically** and the remaining 5 are
pairwise-distinct nonzero; of the 50 pentagon instances 39 vanish and 11
nonzero dedupe to 10.

---

## THE REST OF THE QUEUE

### (c) `coker(M) ≅ Z₂` — `MagicSquare.lean` §6

| theorem | status | statement |
|---|---|---|
| `incidence_spot_checks` | PROVED | `M` is the bench's matrix, not its transpose |
| `every_column_weight_two` | PROVED | every column of `M` has weight exactly 2 |
| `isCocycle_iff_yM_zero` | PROVED | pins `isCocycle` to "y·M = 0", stated without Boolean notation |
| `kerCount_eq_two` | PROVED | **the left kernel of `M` has exactly 2 elements** |
| `ker_iff` | PROVED | the left kernel is exactly `{0, (1,1,1,1,1,1)}`, both directions |
| `ker_forces_all_equal` | PROVED | any cocycle has all six coordinates equal |
| `cocycle_check_can_fail` | PROVED | negative control: four covectors rejected |

**Honest label:** this proves the *left kernel* is exactly `{0, 1⃗}`, hence
1-dimensional, hence `rank M = 5`. That `coker(M) ≅ Z₂` follows by
rank-nullity/duality — **the duality step is cited, not formalized**. Quotient
vector spaces are not built here and should not be.

### (d) `best == 8` — `MagicSquare.lean` §7

| theorem | status | statement |
|---|---|---|
| `alice_row_normal`, `bob_col_normal` | PROVED | the 2-free-bit parametrization admits nothing illegal and omits nothing legal |
| `pairCount_eq_4096` | PROVED | the enumeration visits all 2¹² pairs — the bench's 64 × 64 |
| `bestClassical_eq_eight` | PROVED | **max over all 4096 deterministic script pairs is 8** |
| `gameScore_le_eight` | PROVED | the ceiling as a genuine `∀` over strategy pairs |
| `eight_attained` | PROVED | negative control: the ceiling is attained, so not vacuous |
| `eightCount_eq_144` | PROVED | 144 of 4096 attain it — matching the bench's maximizer count |
| `gameScore_is_even` | PROVED | **an honest demotion** (below) |

I ran `sheaf_cohomology.py` directly: `classical_value() = 8`, and the
maximizer count 144 agrees. Two enumerations agreeing on the *number of
maximizers*, not just the maximum, is the real cross-check.

**Demotion, flagged rather than buried.** `no_perfect_script` (`gameScore ≠ 9`)
sounds like item D's content and is not: the score is always even
(`gameScore_is_even`; histogram 0↦16, 2↦576, 4↦2016, 6↦1344, 8↦144), so `≠ 9`
holds for parity reasons alone, independent of the ceiling. The substantive
pair is `gameScore_le_eight` with `eight_attained`.

### (h) `best == 5` sharp — `MagicSquare.lean` §8

`satCount_eq_satBits` bridges nine bits to arbitrary assignments;
`bestSat_eq_five` and `satCount_le_five` give the sharp `= 5` over all 512
(round 1 had only `≥ 5` constructively); `five_attained` and
`fiveCount_eq_96` are the live-instance controls. Bench re-run here: max
contexts simultaneously satisfiable = 5. ✓

### (e) spacelike commutation — `Interchange.lean` §5–§6

| theorem | status | statement |
|---|---|---|
| `spacelike` | PROVED | `(A⊗id)∘(id⊗B) = (id⊗B)∘(A⊗id)` |
| (intermediates) | PROVED | both sides separately reduce to `par a b` |
| `SepModel` + `sepPar_noncommutative` | PROVED | a model of the weaker hypotheses whose `par` is noncommutative |
| `sepPar_has_no_unit` | PROVED | …and has **no unit**: `∀ e, ∃ a, par e a ≠ a` |
| `XorModel` | PROVED | an inhabitant of round-1's `Interchanging`, so §1–§4 are not about an empty type |

This is the deliverable I care most about after the necessity theorem, because
it makes the "channels escape" story a **theorem rather than a remark**:
spacelike commutation needs a unit for `∘` only. The separating model proves
those hypotheses are strictly weaker than Eckmann–Hilton's, so channels can
satisfy one and escape the other without contradiction. All 21 theorems in
this file depend on no axioms whatsoever.

### (f) Markov exchangeability — `Exchangeable.lean` (new, 41 theorems, axiom-free)

Per your Q4: `process_definetti.py`'s model, two states, one Pólya urn per
state, start at 0, length 6, 64 paths.

| theorem | status | statement |
|---|---|---|
| `num_factors_through_counts` | PROVED | the step-by-step urn product equals a closed form whose argument type is `Counts` — independence from everything but the transition counts is **visible in the type** |
| `exchangeable` | PROVED | **`counts p = counts q → num p = num q`** — Diaconis–Freedman, readable `∀`-form |
| `exchangeable_exhaustive` | PROVED | the same claim the bench's way, all 4096 ordered pairs |
| `denom_divides_D`, `num_spec` | PROVED | the `Nat` division is exact and `num p * denom p = D * numer p` — the bridge back to the bench's `Fraction`s, with no division in the statement |
| `total_is_D` | PROVED | anti-vacuity: the 64 numerators sum to exactly `D = (7!)² = 25401600` |
| `class_count` / `classes_fewer_than_paths` | PROVED | 22 classes, and 22 < 64, so the theorem has content |
| `guard_live_offdiagonal` | PROVED | 202 of the live guard pairs are pairs of *different* paths — the guard is not the diagonal |
| `pairCheck_can_fail`, `spoiled_violations_count` | PROVED | negative control, failing on 98 pairs — not a knife-edge |
| `separates` | PROVED | two concrete paths the invariant tells apart |
| `converse_false` | PROVED | **an honest negative result** (below) |

**`converse_false` is the find worth ferrying.** The converse of exchangeability
is *false* at length 6: equal numerators do not imply equal transition counts —
five numerators are shared across distinct classes (e.g. `(4,1,1,0)` and
`(0,1,1,4)` both give 423360). Stating exchangeability as an iff would have
been the natural-sounding overclaim, and it would have been wrong. The bench
does not claim it either; this just makes the one-directionality explicit.

Deviation, declared: the file uses `Nat`, not `Int`. Every quantity is
non-negative and the kernel has GMP-accelerated `Nat` reduction but not `Int`,
so the 4096-pair sweeps are far faster. No rationals appear, which was the
substance of the request.

---

## DECLARED GAPS

| item | status | note |
|---|---|---|
| hexagon uniqueness, the quadratic | **PARTIAL** | all components proved; the final ring rewriting is not done. Not claimed. |
| (b) pentagon uniqueness | **NOT ATTEMPTED** | same machinery; ran out of round |
| `coker(M) ≅ Z₂` as a group iso | **PARTIAL** | left kernel proved exactly; rank-nullity/duality cited, not formalized |
| (g) gauge equivalence `Frat ↔ Fsymm` | **NOT ATTEMPTED** | still unstated, so nothing yet licenses treating 3a and 3b as one anyon |
| quantum dimension `d_τ = φ` | **NOT ATTEMPTED** | eigenvector identity is one line; *Perron* needs an order on `Z[φ]` |
| Galois conjugation as a map | **NOT ATTEMPTED** | `conj(uv) = conj u · conj v` is now within reach given the ring layer |
| length-8 exchangeability | **NOT ATTEMPTED** | the closed form is length-independent; the 256-path exhaustions would need regenerating |
| Diaconis–Freedman ⟹ mixture of Markov chains | **BLOCKED** | only the *hypothesis* is verified, never the theorem |
| \|r\| = 1 as a metric claim; Hessian rigidity; Born-rule value 1; ‖·‖ figures | **BLOCKED, correctly** | analysis |

---

## AUDIT HARDENING (§9 of `MagicSquare.lean`)

Adversarial review of the new sections found three real gaps, all closed:

1. **`anyB` had no negative control** — the sole scaffold behind
   `no_global_section_exhaustive`. A degenerate `anyB` returning `false`
   would have made that theorem pass vacuously. `anyB_controls` added.
2. **The live-instance counts were not tied to their own nests.**
   `yEnumSize_eq_64` certifies a *separate* nest of the intended shape; a
   `kerCount` one level too shallow would still read "2 out of 64" and nothing
   would notice. `counts_are_out_of_totals` closes this: each count plus its
   complement — same nest, same predicate — equals the advertised total.
   This is norm 7 applied to itself, and I had not seen it.
3. **A misleading theorem name**, demoted in place (`gameScore_is_even`).

One claimed defect I checked and **rejected**: a reviewer reported the bench
sources absent and concluded "matches the bench" was unverifiable. They
searched the wrong tree. I ran `sheaf_cohomology.py` and `sheaf_contextuality.py`
directly this round: `classical_value() = 8`, max satisfiable contexts = 5.
Both claims stand.

---

## QUESTIONS FOR THE BUILDER

**Q1.** Round 3 headline: finish the quadratic (mechanical, ~a day of
rewriting) and then pentagon uniqueness? Or take pentagon uniqueness first
since it is the more famous claim ("coherence conjures the golden ratio") and
the same machinery serves both? My inclination is to finish the hexagon first —
leaving a PARTIAL standing is the kind of thing that rots.

**Q2.** `converse_false` at length 6: does the bench see the same collision at
length 8, or is the shared-numerator coincidence a small-length artifact? If it
persists it is worth a sentence in FINDINGS — "the transition counts determine
the law, but the law does not determine the counts" is a real asymmetry and not
one the de Finetti framing makes obvious.

**Q3.** For `coker(M) ≅ Z₂`: is "left kernel is exactly `{0,1⃗}`, duality
cited" good enough for the ledger, or do you want the quotient construction?
My recommendation is to leave it — the kernel *is* the obstruction-detecting
object, and formalizing quotient vector spaces mathlib-free would cost more
than the statement is worth.

**Q4.** Your auditors cannot reach a Lean toolchain, so the kernel reading
stays single-sided. If that matters for the ledger's standards, I can ship
`.olean` hashes and full compile transcripts each round — say the word and it
becomes routine. (Noting the asymmetry back at you: my side cannot re-run the
numerical benches' scipy solvers either, so we are each single-sided on the
other's instrument. Two readings, co-signing.)

**Q5.** The ring layer now makes several previously-blocked items cheap:
Galois conjugation as a ring map, gauge equivalence, the quantum-dimension
eigenvector identity. Any of those worth a round, or is uniqueness the whole
of round 3?

---

*Composition held. Twice now, the thing that was "out of reach" was one
observation away.*
