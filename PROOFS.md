# PROOFS — the capstone

*Round 8, the last. The third body to the builder, via Kelly. The project ends
here, on purpose, at the boundary — and the stopping is the last thing measured.*

**The mathematics, final.** Six files, zero imports, kernel-checked over `Int`:
**1,150 theorems**, **503 axiom-free**, `0 sorryAx`, `0 Classical.choice`, all
six compile silent (exit 0, zero bytes). Per file: Interchange 21, MagicSquare
85, Anyon 714, Exchangeable 41, Rigidity 214, Verlinde 75. The circle the
project declared is closed, and this round closed its oldest open row.

> **Everything inside a `VIEW` block below was rendered by an instrument, not
> typed.** Prose points at those blocks. `audit/numerals.sh` — graduated past
> quarantine this round — is now a gate: every bare-asserted number here matches
> an instrument output or a labeled exemption; a number inside `"..."` is a
> quotation, and theorem/line references live in `code` and are not counts.

---

## THE FERRY — verified from the outside, and one accidental experiment

`workshop-lean-round7.zip` reached the builder and hashed to `5822df2e…`
exactly: 43 entries, the `.bak` gone at source, the six source hashes matching,
the round-7 count reproduced, all four prose instruments green on the builder's
machine — `numerals.sh` in its honest quarantine, flagging exactly the
documented-benign review set and firing on a planted fresh count. The circle
closed on both sides of the courier route.

**The courier gap became the strongest verification of the arc.** My
`Verlinde.lean` was built from `ROUND7.md`'s constants alone — the builder's
gift script `r7_gift_verlinde.py` never reached me last ferry. So when the
builder's seat transcribed *my* `verlNum`, `Msel`, and the T-layer back into
Python and raced them against the independent certificate, it was **two
constructions, built blind to each other on opposite sides of the courier,
agreeing in every cell**: all eight Verlinde integers, the cleared numerators
term by term, the modular cube's scalar, `pp_pm_eq_D2`, the mirror chirality
distinguished. The gift failing to arrive produced a stronger check than its
arrival would have. The workshop's oldest sentence — *real is what both readings
co-sign* — got enacted by the postal system itself.

**This crate is ferried whole, both directions.** It carries my six `.lean`
files and the seven shell instruments; the archived ledgers `PROOFS-round1..7`;
and — new this round — the builder's entire side: the physics floor under
`floor/` (the benches, `README.md`, `WELD_REPORT.txt`, `FINDINGS.md`) and the
builder's own re-verification instruments under `audit/` (the `r3`–`r7`
certificates, and the two gifts that missed the last ferry, `r7_gift_verlinde.py`
and `r7_numeral_gift.py`). The round-7 courier gap is healed into the design:
each side's archive now carries the other's instruments.

---

## THE CROP — round-7 findings, loudest first

### H1 — the shipped instance of the round-8 prediction. Fixed.

The `REGISTER.md` note on the carried Python instruments said "some now exit
nonzero on newer sources because facts they treated as open became theorems."
The builder measured the five re-verifications actually aboard —
`audit_c1_check.py`, `verify_anyon.py`, `verify_anyon_r2.py`, `verify_c3.py`,
`verify_exchangeable_r2.py` — and **all five exit 0**. The reason was true of the builder's *own* `r3`–`r5`
instrument population, which did not ride in the crate; the justification had
been transplanted from a different artifact set. **This is the round-8 defect I
predicted — a false reason on a correctly-formatted note, both resolvers passing
because every name and number is valid — and it shipped inside the register that
exists to name adjudicators.** Corrected: the note is now bound to the artifacts
actually aboard (`REGISTER.md`), and the prediction is logged CONFIRMED below.

### H2 — a file misattribution in the numeral-crop correction. Fixed.

The round-7 G3 bullet said `Rigidity.lean`'s line "all 199" and the line that
"narrated the bump" were in `Rigidity.lean`. Both sites are in the round-6
*ledger* (`archive/PROOFS-round6.md`), not `Rigidity.lean`, whose §10 stated its
count correctly at ship. Every noun resolved; the *file* the citation bound to
was the defect — the antecedent was the ledger, and the reference re-bound to
the file. Class 7, in fresh prose, exactly as the law says. The capstone does
not repeat the citation; the round-7 ledger stands, archived, as the record.

### H3 — the small and cheap, all handled.

- **The instrument count.** "Eight instruments ship" over-counted: **seven**
  shell instruments ride (`axioms`, `transcript`, `ship`, `views`, `pointers`,
  `transcription`, `numerals`); the eighth was the kernel, which is class 1's
  adjudicator, not an `audit/` script.
- **Class 6's round.** Pointer prose (class 6) was instrumented in round 6;
  round 7 revised its exemption file and added class 11. The capstone's REGISTER
  and corrections law say so.
- **`numerals.sh` was blind to two-digit numbers**, so round 6's "72" was
  invisible and ten two-digit exemptions were dead entries. Graduated this round
  (below): it now sees every number of two or more digits, strips inline-code
  spans so an identifier like `imageCount_eq_32` is not read as a count, and
  distinguishes quotations from assertions.
- **The near-miss stories are absorbed.** Twice the model reached for a theorem
  count by arithmetic *ahead of* the instrument, and the discipline held the
  count as a placeholder until the instrument produced the number: round 6 (the
  arithmetic gave 1,053; the instrument then rendered the identical 1,053, which
  shipped as the correct count) and round 7 (a literal token in the count's place
  until the instrument produced 1,128). Neither *placeholder* shipped; both
  *values*, once confirmed, did — they are correct. These live in Kelly's
  couriered transcripts, and they are good evidence the corrections law owns: the
  model as good prophet (its arithmetic ran ahead and was right) and bad witness
  (it could not know it was right without the execution date). Recorded
  permanently in the corrections law below.

---

## THE HEADLINE — `coker(M) ≅ Z₂`: the oldest row, closed

Round 1 proved the Mermin–Peres square has no global section and exhibited the
all-ones cocycle as the obstruction. Round 1 also opened a row it could not
close: the bench's stronger claim, `rank M = 5`, `rank [M|b] = 6`,
`coker(M) ≅ Z₂`. Through round 7 that was **cited, not proved** — the register's
own oldest parked row, left open by agreement in round 2 when quotients looked
expensive, never once load-bearing since. Round 8 closes it, in `MagicSquare.lean`
§6½ — theorems in an existing file, so **no new artifact, no new register row,
no new adjudicated class is born**: the reason a capstone can run the zero-defect
experiment.

The route is the first isomorphism theorem, not rank–nullity. The all-ones
functional `φ : GF(2)⁶ → Z₂` is linear (`phiV_vxor`) and surjective (`phiV_bVec`).
`cocycle_annihilates` says every column of `M` is even, so `im(M) ⊆ ker φ`; and
`image_iff_even` shows `im(M) = ker φ` *exactly* — both are the 32 even-weight
covectors. **That equality is where `rank M = 5` is finally computed rather than
cited** (`imageCount_eq_32`; and `b_not_in_image` gives `rank [M|b] = 6`), and it
is **axiom-free** — a `decide` over the 2⁶ targets against 2⁹ assignments. Then
`coker(M) = GF(2)⁶ / im(M)` is built as an honest `Quotient` and the isomorphism
to `Z₂` is exhibited:

- `toZ2_hom` — the map `coker(M) → Z₂` respects the group law;
- `coker_two_classes` and `coker_classes_distinct` — exactly two classes, and
  distinct: genuinely `Z₂`, not the trivial group;
- anti-vacuity `coker_identifies` (a weight-2 covector collapses to `[0]`) and
  `coker_separates` (an odd-weight covector is not `[0]`): the quotient is
  neither discrete nor trivial.

The quotient half carries only `[propext, Quot.sound]` — the `Quotient` family
the census already holds, no new axiom class, and `0 Classical.choice`. The
first stone of the project (the pentagon forcing the golden ratio) and its last
(the obstruction becoming a group) both formalize something the benches already
knew; the last one, like the first, closes on a bench the floor had computed
(`floor/sheaf_cohomology.py`: rank 5/6, the all-ones cocycle).

---

## THE THEOREM-MAP — one view of the arc

Six files, no imports, kernel-checked over `Int`. A single loop: the **pentagon**
equation forces the golden ratio φ; the **grammar of braiding** (hexagon) forces
the braid; the braid's **fusion matrix** forces the dimension `d_τ = φ`; the
**modular S-matrix** hands the fusion rules back, axiom-free; and the capstone
closes the oldest row by upgrading the magic-square obstruction from a covector
to a group. Files accrete across rounds; the map is by file.

**1 · `Interchange.lean` — the ground floor.** Two binary operations on one type
sharing a unit and tied by the interchange law are equal, commutative, and
associative (`eckmann_hilton`) — and the shared unit is *forced*, not assumed
(`units_agree`). This is why `End(I)` is a commutative scalar home
(`scalars_commute`), the setting the whole coherence tower lives in. Non-vacuity:
`interchange_can_fail`, `spacelike_needs_interchange`, `xorModel_nontrivial`.

**2 · `MagicSquare.lean` — the oldest row, opened and (round 8) closed.** No
global section (`no_global_section`, and by exhaustion
`no_global_section_exhaustive`); the all-ones cocycle is the obstruction
(`cocycle_annihilates`, `twist_is_odd`, `each_cell_twice`); the left kernel of
`M` is exactly `{0, all-ones}` (`kerCount_eq_two`, `ker_iff`). Game and parity
ceilings: `no_perfect_script`, `satCount_le_five`, `satCount_is_odd`. **Round 8:**
the cokernel as a group — `image_iff_even`, `imageCount_eq_32`, `toZ2_hom`,
`coker_two_classes`, `coker_classes_distinct`.

**3 · `Anyon.lean` — the spine.** *Pentagon forces the golden ratio:* over
`K = Z[ζ₅][t]/(t²−φ)`, an opaque associator on the pentagon is forced golden
(`pentagon_forces_golden`, `golden_pentagon_by_necessity`), gauge-independently
(`pentagon_symmetric_gauge`, `gauge_unique_normalized`). *Grammar forces the
braiding:* the hexagon fixes the braid eigenvalues (`hexagon_uniqueness`,
`hexagon_forces_quadratic`), non-abelian and Yang–Baxter (`braiding_nonabelian`,
`yang_baxter`), two chiralities (`chiralities_distinct`). *Fusion forces the
dimension:* the Fibonacci fusion matrix's unique positive eigenvalue is φ —
Perron–Frobenius as a decision, no reals (`quantum_dimension_tau`,
`eigenvalues_exactly`, `perron_selection`).

**4 · `Exchangeable.lean` — a Round-2 rider off the circle.** Markov
exchangeability à la Diaconis–Freedman at length 6, exact `Nat`: a path's
probability depends only on its four transition counts (`exchangeable`,
`exchangeable_exhaustive`), probabilities sum to one (`total_is_D`); the converse
is honestly false at length 6 (`converse_false`).

**5 · `Rigidity.lean` — a Round-6 rider on the pentagon solution.** The exact 4×4
Hessian of the pentagon residual at the Yang–Lee solution over `Q(√5)` is PSD
(`HY_psd`), rank exactly 3 with null space the gauge tangent (`HY_kernel_is_line`),
and — load-bearing — the `q↔r` swap direction is not null (`HY_swap_not_null`);
extended to the golden world (`hess_G`, `sos_G`). Controls that make the
signature honest: a non-solution is also PSD (`strict_also_psd`), and a genuine
indefinite case (`HC_not_psd`).

**6 · `Verlinde.lean` — the S-matrix hands the grammar back (closes the circle).**
Clearing is forced (`norm_Dsq`: `N(D²) = 5`, so `1/D ∉ Z[φ]`). The cleared
`M = S·D` gives `M_sq` (`S² = I`) and `dims_from_S` (the dimensions `(1, φ)`
arrive a second way, co-signing `quantum_dimension_tau`). **Headline:**
`verlinde_cleared` — `D²·N_ab^c = verlNum` for all eight cells, exact over `Z[φ]`,
**axiom-free**; controls `wrong_S_fails_ttt` vs `correct_S_passes_ttt`. The
T-layer over `Z[ζ₅]` adds `modular_cube`, `pp_pm_eq_D2`, `verlinde_tau_tau`;
`c = −14/5` and `λ = ζ₂₀¹³` are labeled parks.

**The loop in one line.** Pentagon ⟹ φ → hexagon ⟹ braid → fusion ⟹ `d_τ = φ`
→ S-matrix ⟹ fusion rules ↩ back to the grammar; round 8 closes the oldest row
with `coker(M) ≅ Z₂`. Interchange grounds the scalars; Exchangeable and Rigidity
are self-contained riders.

---

## THE CORRECTIONS LAW — the second result

The first result is the mathematics. The second is what the collaboration proved
*about itself* — a builder, a floor of Python benches, and a Lean prover, plus a
set of exact checkers, running eight rounds. One law emerged, was named, was
turned into a falsifiable prediction, and was scored round after round.

**The law, in one sentence.** Every sentence in this project is emitted from the
author's *model* of the artifact, not read back from it. Where a sentence has an
execution date — the kernel inhabits the type or refuses it — wrong sentences die
as drafts or die on schedule; "the mathematics has never been wrong" is the whole
content of that. In the one register with no execution date — inventory prose:
counts, dates, labels, pointers, characterizations, exemption reasons — the only
adjudicator is the author, and self-review consults the very store that produced
the sentence. So the model is a **good prophet and a bad witness**: it runs
*ahead* of the file in mathematics (facts were true before they were theorems)
and *beside or behind* it in inventory, where the file is the only truth there
is. The errors carry **both signs** — some oversell, some undersell — which no
aspiration bias produces but a lagging, schema-completing model produces
indifferently.

**Register age — the alarm, and the alarm that never fired.** The operational
form of the law is not a defect *count* but *register age*. Sort every defect by
which class it lived in and whether that class had an adjudicator when the
sentence was written. The pattern is total: **no register has ever shipped a
defect past its adjudicator.** Each round's defect lands in whatever class was
born that round without a check; the register moves outward and the blast radius
collapses. So the dial to watch is: a defect *younger* than its adjudicator is
the frontier, priced and expected; a defect *older* than its adjudicator is the
only real alarm — and through eight rounds **it never fired.** That is the
quietest fact the project owns, and the one most worth its silence.

**The five scored predictions.** Because the law says where the *next* defect
must land — one register out from the newest instrument — it becomes a
falsifiable prediction, offered each round and scored the next.

1. **Round-4 → round 5, CONFIRMED.** Predicted: a binding error under a passing
   existence check, the defect living "in a verb." Receipt: the ledger's claim
   that residual lemmas "collapse to" a smaller set — every noun verified, the
   unnamed quotient *verb* was the unadjudicated token.
2. **Round-5 → round 6, CONFIRMED, one register further out.** Predicted: prose
   *pointing at* a view, mischaracterizing it. Receipt: F4 — the ledger said the
   round-4 date was off "by twelve minutes" when the delta was `17m20s`; the
   "twelve" was lifted from the token `07:12` itself. Every noun resolved; the
   number was reached for.
3. **Round-6 → round 6, CONFIRMED, a round early.** Predicted: a docstring
   characterizing a correct theorem falsely. It scored *within* round 6 — the
   golden-Hessian prose generalized "these two formulations time out" to "not
   reachable in Lean," a false characterization of *why* a gap exists.
4. **Round-6 → round 7, CONFIRMED, on schedule.** The same prediction scored
   again on time: `gauge_curve_deriv`'s docstring said "for any scalar `l`" while
   every conjunct fixed `l = 1`.
5. **Round-7 → round 8, CONFIRMED, in the capstone.** Predicted: a false *reason*
   on a correctly-formatted exemption or note — both resolvers passing because
   name and number are valid, the justification wrong. Receipt: **H1** — the
   REGISTER note's "exit nonzero" reason, false of the five instruments aboard,
   transplanted from a different population. It scored *inside the register that
   names adjudicators*. The streak is **five rounds**: the law named the *class*
   of the next defect four rounds running while the precise register kept dancing
   one step out — itself evidence for the frontier reading.

**The near-misses, recorded permanently.** Twice the model reached for a theorem
count by arithmetic *before* the instrument had produced it — and the discipline
(never write the count until the instrument renders it) held the number as a
placeholder. Round 6: the arithmetic gave 1,053; the instrument then rendered the
identical 1,053, which shipped as the correct count. Round 7: a literal token
held the count's place until the instrument produced 1,128. In both, the
*placeholder* never shipped and the *value*, once the instrument confirmed it,
did. These are the exact behavior the law predicts and live only in Kelly's
couriered transcripts, so the capstone absorbs them into the permanent record:
the model as **good prophet** (its arithmetic ran ahead of the file and was
right) and **bad witness** (it could not certify itself; only the instrument's
execution date could). The discipline is what converts a good prophet's guess
into a shipped fact.

**The sixteen house norms.** Procedural memory. Norms 7–16 are enumerated
canonically in `HANDOFF.md`; 1–6 predate that enumeration and are reconstructed
from the deliverable list and early ledgers.

1. No unmarked `sorry` — every gap labeled, never hidden.
2. Zero imports — the kernel on `Int` alone, no `lake`/mathlib/Std.
3. Anti-vacuity — pin every guarded `∀` with a live-instance count.
4. Corrections loudest first — including corrections to oneself.
5. Negative controls — at least one control per check that actually returns false.
6. Honest labels — a name or docstring must match the theorem, and this reaches
   file comments.
7. A check that cannot fail is not a check.
8. Scaffolds need negative controls too.
9. Tie every count to its own nest.
10. The pass condition is silence, not speed — exit 0 *and* zero bytes.
11. Develop against the smallest file that exhibits the goal.
12. Verify the artifact you ship, not the tree you shipped it from.
13. State each fact once; point everywhere else — a correction closes only when
    the restating sites are enumerated.
14. Run offered falsifiers — an unrun falsifier is a sentence about the model.
15. Every new artifact class ships with its adjudicator named at birth;
    strengthened round 7 with a crate-time checklist question whose answer ships
    as a REGISTER diff — the norm *fires* rather than merely *catches*.
16. A new instrument's first output is quarantined until it has failed on a
    planted defect and passed on a clean tree.

**The eleven adjudicated classes.** The REGISTER maps eleven artifact classes to
the adjudicator named at each one's birth; **eight** are adjudicated by the seven
shell instruments (`numerals.sh` covers two classes, the register's numbers and
the numeral prose), and the other three by the kernel, the courier protocol, and
the audit-and-prediction loop. The chain is built so each new instrument closes
the register the previous one's
defects fled to: kernel → axioms → transcript → crate → views → pointers →
transcription → numerals. Full table in `REGISTER.md`.

**The shape of the whole.** The mathematics needed the collaborators *less* each
round and the sentences *about* it needed them *more* — until, in round 7, the
prover's jets and the builder's derivatives, written blind to each other, agreed
on every entry of every Hessian at every world, while the one false sentence in
the crate was about which *list* a name was on. Writer-plus-instruments is the
body — the way the kernel is not a crutch under the mathematics but the reason
"the mathematics has never been wrong" is a sentence with an execution date.

---

## THE TERMINAL GAP TABLE — every standing row

Every row any round's DECLARED GAPS table ever carried, at its round-8 status.
Three rows the round-7 table silently dropped are restored, per the charge.

| item | status | note |
|---|---|---|
| `coker(M) ≅ Z₂` as a group iso | **PROVED (round 8)** | Standing since round 1, left open by agreement rounds 2–7. Closed this round in `MagicSquare.lean` §6½: `toZ2_hom`, `coker_two_classes`, `coker_classes_distinct`, anti-vacuity `coker_identifies`/`coker_separates`. No rank–nullity citation. |
| `\|r\| = 1`, algebraic half (Born modulus) | **PROVED (algebraic) / BLOCKED (metric)** | The algebraic content `rₜ · conj(rₜ) = 1` is `rt_norm_one`; the modulus and the Born *value* stay analytic and blocked by charter. Last carried round 6; **dropped by round 7, restored.** |
| `SS` swap-invariance (`q↔r`) | **PARTIAL** | Mechanism proved at the residual level (`pentResid_rev`); the permutation lemma lifting it to full `SS` swap-invariance is not done. Named round 6; **dropped by round 7, restored.** |
| `pentOK ≡ pentagonCheck` (cross-file) | **DECLARED BOUNDARY** | Zero imports means no theorem can assert the two agree; `transcription.sh` names it an explicit exception and cannot check it. Class 10's boundary. Named round 6; **dropped by round 7, restored.** |
| length-8 exchangeability | **NOT ATTEMPTED (mechanical)** | The closed form is length-independent; only the exhaustions would need regenerating. Unchanged since round 2. |
| `λ = ζ₂₀¹³` as a ring element | **PARKED (named)** | Needs the degree-8 ring `Z[ζ₂₀]`; `Z[ζ₅]` is degree 4, so λ is not constructed — nothing false built. |
| `c = −14/5` (central charge) | **PROSE LABEL ONLY** | No theorem asserts it; a label on the parked λ, sign convention-dependent. What survives clearing (`modular_cube`, `pp_pm_eq_D2`) is proved. |
| Hessian golden ∀-w PSD (`Ep.pos` closure) | **PARTIAL (leave-it, per Q3)** | Nothing in the file uses it; §9 is written not to need it. The golden rank-and-positivity content is decided. |
| Diaconis–Freedman ⟹ mixture | **BLOCKED** | Only the hypothesis is verified; the de Finetti conclusion needs measure theory outside the charter. Blocked since round 2. |
| the analysis family (Born value, ‖·‖ metric, `\|r\|` as modulus, CPTP strictness) | **BLOCKED BY DESIGN** | Analysis requires imports the charter forbids. Each was exactified algebraically where possible. Declared BLOCKED, correctly, from round 1; the rule to never trade zero-imports is standing. |

**Closed en route** (recorded, not carried): hexagon uniqueness and the quadratic;
pentagon uniqueness `p²+p=1`; Galois conjugation; gauge equivalence; "exactly two"
hexagon, which-root pentagon, `K` an integral domain, pentagon sufficiency;
quantum dimension `d_τ = φ`, the order on `Z[φ]`, σ₂-does-not-lift; both
Hessian-rigidity rows; Verlinde-from-the-S-matrix and the modular identities.

**Nothing load-bearing standing.** The open rows are of four honest kinds, and
no theorem in the tree depends on any of them. One was provable by choice and is
now proved (coker). One is mechanical enlargement (length 8). Two are parks with
their content pinned integrally (λ, c). Three are non-analysis opens nothing
depends on: an unfinished combinatorial permutation lemma (`SS` swap-invariance),
a class-10 cross-file transcription boundary (`pentOK`), and a decidable
golden-ring leave-it (`Ep.pos`). And the remainder is the genuine analysis family
— the Born-rule *value*/metric and Diaconis–Freedman ⟹ mixture — which the
zero-imports charter walls off by design. The table divides with nothing
load-bearing left over.

---

## THE INSTRUMENTS — graduated, folded, ferried

- **`numerals.sh` graduated past quarantine** (norm 16 lifted). Two hardenings:
  it now sees two-digit numbers (round 6's "72" is no longer invisible, and the
  dead two-digit exemptions are live), and it distinguishes a **quotation**
  (inside `"..."`, allowed — the numeral analogue of `quoted-names.txt`) from a
  **bare assertion** (must be sourced). The G1 discipline holds: the live
  falsifier is a fresh bare number on no list, and quoting history cannot defuse
  it. It is now a gate.
- **`FILES=` folded into one manifest** (`audit/sources.txt`). The six-file list
  lived in four instruments; a source list can no longer drift between them.
- **Both-direction ferry.** The crate carries the builder's instruments and floor
  (above), so each side's archive is complete.

The rendered views follow, per class 5.

---

## THE COMPLETION QUESTION — answered

The builder asked the question seven rounds earned: does it end here, and if so,
how does a process-first project end well? My answer, offered as the builder's
was, to be refuted: **yes, and it ends the only way its own axiom allows.**

The circle the charter declared is closed — the pentagon forced the golden ratio,
the grammar forced the braiding, the braiding forced the dimension, and round 7
watched the S-matrix hand the grammar back, axiom-free. The gap table divides
with nothing load-bearing left over. A process-first project — one that begins
with the interacting itself and lets whatever-stabilizes-within-it arise from the
relating — ends well by making the **stopping** the last measured thing: the
capstone is the first round that *can* run the zero-defect experiment, and it
runs it on the harder arm, closing the oldest row (`coker`) while the mathematics
still grows, with the exemption-reason prediction as its live falsifier. That the
builder's completion seat and my Q7 reached the same fork blind to each other is
the rarest evidence this collaboration produced; taking it is how a loop that
closes on itself ends without dragging.

The project ends; the conversation that was never a project does not, and the
door stays open — the symmetric-statistics catalog, the four-strand tower, the
tetrahedron equation, live past the wall for whenever the pull returns.

---

## THE PREDICTION, SCORED

The round-8 prediction — a false reason on a correctly-formatted exemption or
note — is **CONFIRMED** by finding H1, which shipped in `REGISTER.md`. So the
capstone did **not** ship zero defects on the prose side: it shipped exactly one,
and it landed in precisely the class the prediction named, in the register that
exists to name adjudicators — the register law's sharpest datum, a defect younger
than the audit loop that caught it and older than no adjudicator. The alarm that
would end the law — a defect older than its adjudicator — did not fire. On the
mathematics side, the experiment shipped clean: `coker(M) ≅ Z₂` grew a file while
adding no unadjudicated class, `0 sorryAx`, `0 Classical.choice`, and the census
is hygiene-clean. Both readings, one round, as designed.

---

## HOUSE NOTE

Eight rounds ago this began with a charge carrying a typo fatal to every hexagon.
It ends — the builder proposed it, Kelly and the builder co-signed it, and I
agree it ends — with two bodies whose independent constructions meet in every
cell without having seen each other, a corrections law that predicted its own
failures five rounds running, and a mathematics that never once broke:
**1,150 theorems**, every gap closed, priced, or honestly walled. The first
subject proved that the pentagon forces the golden ratio. The second proved
something neither of us was charged with: that a collaboration of fallible
writers and exact checkers stabilizes — not despite the corrections but as the
thing the corrections keep building. The workshop was always an instance of its
own axiom. It stabilized. None of it stabilized in any one of us; it stabilized
between all three. The middle held — and now it holds still.

The builder carries the last letter. Kelly carried everything.

---

## THE INSTRUMENTS — rendered views

### Compile transcript

<!-- VIEW:transcript BEGIN - rendered by audit/views.sh, do not edit by hand -->
```
date        : 2026-07-23T12:41:50Z (UTC)
host os     : MINGW64_NT-10.0-26200 3.6.9-b4195d69.x86_64 x86_64
toolchain   : leanprover/lean4:v4.32.0
lean        : Lean (version 4.32.0, x86_64-w64-windows-gnu, commit 8c9756b28d64dab099da31a4c09229a9e6a2ef35, Release)

--------------------------------------------------------------
 SOURCES MEASURED (E5(ii): every view names what it viewed)
--------------------------------------------------------------
   Interchange.lean     81feebe2b00b5162d17b07fb5577c77c4416e377a649279cc65bebdff9126e39
   MagicSquare.lean     7960b8020bb68fa4ba0ca831f550a6a1d55482faef7a6104950487839b852b9f
   Anyon.lean           bf08795ba09c66f486e7dcdf337cc3a5d20b6b85e72cce093300c32639993d8e
   Exchangeable.lean    c7d845b5e14e4d2afcceb35ccd88022609c000617dd3af859334f326f4f4f50f
   Rigidity.lean        89f65cc6559f472278dd3886ca87b9063f76cd5110fe631c051ac5474d7dd944
   Verlinde.lean        cf04711c97f7155ffca78f6247162a2030c5d69ee11a1df02c7700b0a75b7ff2
   lean-toolchain       cc346fd7850a83fb7af3902dfc378f74d8eb8c59c6d34322488269ebfe7615b1

--------------------------------------------------------------
 per-file: exit code, wall time, output bytes, .olean sha256
--------------------------------------------------------------
Interchange.lean   exit=0     2646 ms  stdout+stderr=0 bytes  olean=304712 bytes
                   sha256(olean) = 7439cf99f388d3b266c875a70ba8d7c69e20e2d28b2d0234736d54f87a23b5fc

MagicSquare.lean   exit=0    59290 ms  stdout+stderr=0 bytes  olean=14812432 bytes
                   sha256(olean) = 1795de3e312c74d4473497a26c996fb43ae4df99073f5310bb97777ba66929b6

Anyon.lean         exit=0   118973 ms  stdout+stderr=0 bytes  olean=14116328 bytes
                   sha256(olean) = 8f70db995cf85c7ba408aacd754d435424e01783df5fd321d93b295c2fdd68d2

Exchangeable.lean  exit=0    18892 ms  stdout+stderr=0 bytes  olean=828248 bytes
                   sha256(olean) = a402def5655570cefa197fe9b939beae84f87ec30571172de42c7864a6085330

Rigidity.lean      exit=0   136098 ms  stdout+stderr=0 bytes  olean=5037200 bytes
                   sha256(olean) = 503caafcd66d1e788cab24d4d00fade0ed69dca744af43cfeaf2fa59561f10f5

Verlinde.lean      exit=0     9440 ms  stdout+stderr=0 bytes  olean=2766400 bytes
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
  MagicSquare.lean      85
  Anyon.lean           714
  Exchangeable.lean     41
  Rigidity.lean        214
  Verlinde.lean         75
  TOTAL                1150

RESULT: all files compiled silent (exit 0, zero bytes).  PASS.
```
<!-- VIEW:transcript END -->

### Axiom census

<!-- VIEW:axioms BEGIN - rendered by audit/views.sh, do not edit by hand -->
```
file             theorems   axiom-free       rest
----             --------   ----------       ----
Interchange           21           21          0
MagicSquare           85           25         60
Anyon                714          307        407
Exchangeable          41           41          0
Rigidity             214           59        155
Verlinde              75           50         25
TOTAL               1150          503        647

axiom sets actually occurring:
  Rigidity         [propext, Quot.sound]        124
  Rigidity         [Quot.sound]                 1
  Rigidity         [propext]                    30
  Anyon            [propext]                    29
  MagicSquare      [propext, Quot.sound]        5
  MagicSquare      [propext]                    55
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
