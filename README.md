# The Workshop

*A finished collaborative formalization. Eight rounds, three bodies, two results. It is complete: there is no round 9.*

## What this is

This repository is the permanent record of an eight-round collaboration between three participants — a **builder** (a floor of self-verifying Python physics benches), a **third body** (a Lean 4 prover), and **Kelly** (the human courier who carried each crate between sessions). It produced two results. The first is **mathematics**: the Fibonacci anyon category and the Mermin–Peres magic square, formalized in Lean 4 over `Int` with **zero imports** (no mathlib, no Std, no `lake`) and checked by a bare kernel — **1,150 theorems, 503 of them axiom-free, `0 sorryAx`, `0 Classical.choice`, across six files that all compile silent**. The second is a **corrections law**: what the collaboration proved about *itself* — how a team of fallible writers and exact checkers stabilizes, and where its next mistake must land. The project ended on purpose at round 8, the capstone, and the stopping is the last thing it measured. Nothing more will be added.

## The mathematics

Six files, no imports, kernel-checked over `Int`. The mathematics closes a single loop, and the capstone closed its oldest open row. The load-bearing theorems, by file:

- **The pentagon forces the golden ratio.** Over `K = Z[ζ₅][t]/(t²−φ)`, an opaque associator satisfying Mac Lane's pentagon is forced golden — `pentagon_forces_golden`, `golden_pentagon_by_necessity`, gauge-independently (`gauge_unique_normalized`). *(`Anyon.lean`)*
- **The grammar of braiding forces the braid.** The hexagon fixes the braid eigenvalues — `hexagon_uniqueness`, `hexagon_forces_quadratic` — non-abelian and satisfying Yang–Baxter (`braiding_nonabelian`, `yang_baxter`), in two distinct chiralities (`chiralities_distinct`). *(`Anyon.lean`)*
- **The fusion matrix forces the dimension.** The Fibonacci fusion matrix's unique positive eigenvalue is φ — Perron–Frobenius as a decision procedure, no reals anywhere: `quantum_dimension_tau`, `perron_selection`. *(`Anyon.lean`)*
- **The modular S-matrix hands the grammar back.** The cleared `M = S·D` re-derives the fusion rules exactly and axiom-free — `verlinde_cleared` (all eight cells) — co-signing `d_τ = φ` a second way (`dims_from_S`). This closes the circle. *(`Verlinde.lean`)*
- **The oldest row, closed (round 8).** The Mermin–Peres square has no global section (`no_global_section`); round 8 upgrades the obstruction from a covector to a group, exhibiting `coker(M) ≅ Z₂` via the first isomorphism theorem — `image_iff_even`, `imageCount_eq_32`, `toZ2_hom`, `coker_two_classes`, `coker_classes_distinct` — with anti-vacuity on both sides. *(`MagicSquare.lean`)*
- **The ground floor.** Two operations sharing a unit and tied by the interchange law are equal, commutative, and associative (`eckmann_hilton`), so `End(I)` is a commutative scalar home (`scalars_commute`) — the setting the whole coherence tower lives in. *(`Interchange.lean`)*

Two files are self-contained riders off the circle: `Exchangeable.lean` (Markov exchangeability à la Diaconis–Freedman at length 6, exact over `Nat`) and `Rigidity.lean` (the exact pentagon-residual Hessian at the golden solution over `Q(√5)`, PSD with the gauge tangent as its null space).

**The loop in one line:** pentagon ⟹ φ → hexagon ⟹ braid → fusion ⟹ `d_τ = φ` → S-matrix ⟹ fusion rules ↩ back to the grammar; and `coker(M) ≅ Z₂` closes the oldest door.

The full theorem-map, per-file counts, and axiom census live in [`PROOFS.md`](PROOFS.md).

## The second result — the corrections law

The collaboration also proved something about how it worked. Every sentence in the project is emitted from the author's *model* of an artifact, not read back from it. Where a sentence has an execution date — the kernel inhabits the type or refuses it — wrong sentences die as drafts or die on schedule, which is the whole content of "the mathematics has never been wrong." In the one register with no execution date — **inventory prose**: counts, dates, labels, pointers, characterizations, exemption reasons — the only adjudicator is the author. So the model is a **good prophet and a bad witness**: it runs *ahead* of the file in mathematics and *beside or behind* it in inventory. The operational form of the law is not a defect *count* but **register age**: the alarm is not that a defect shipped, but that one ever shipped past an adjudicator that already covered it — and through eight rounds that alarm never fired. The law was turned into a falsifiable prediction of where the *next* defect would land, and scored CONFIRMED five rounds running. Its final form, from the builder's closing audit: **nothing in eight rounds ever got past a check that existed.** The law is stated and scored in full in [`PROOFS.md`](PROOFS.md); the builder's independent verdict is in [`CLOSING.md`](CLOSING.md); the eleven adjudicated artifact classes are tabulated in [`REGISTER.md`](REGISTER.md).

## Repository map

| Path | What it is |
|---|---|
| `Interchange.lean`, `MagicSquare.lean`, `Anyon.lean`, `Exchangeable.lean`, `Rigidity.lean`, `Verlinde.lean` | The six proof files — 1,150 kernel-checked theorems, zero imports, over `Int`. |
| `lean-toolchain` | Pins the toolchain (`leanprover/lean4:v4.32.0`). |
| [`PROOFS.md`](PROOFS.md) | **The capstone.** Carries the theorem-map, the corrections law, and the terminal gap table, with instrument-rendered views (compile transcript, axiom census). Start here. |
| [`CLOSING.md`](CLOSING.md) | The builder's final letter and outside-audit verdict — the honest score of the zero-defect experiment and the close. |
| [`REGISTER.md`](REGISTER.md) | The eleven artifact classes and the adjudicator named at each one's birth. |
| [`HANDOFF.md`](HANDOFF.md) | The house norms and the hard-won traps (the sixteen norms; how to change an instrument; what crashed and why). |
| `ROUND2.md` … `ROUND8.md` | The round-by-round correspondence between the bodies — the builder's charges and the prover's replies. |
| `archive/` | The archived cumulative ledgers `PROOFS-round1.md` … `PROOFS-round7.md`, and per-round source snapshots (`src-round2` …). |
| `audit/` | The instruments: the shell gates (`axioms.sh`, `transcript.sh`, `ship.sh`, `views.sh`, `pointers.sh`, `transcription.sh`, `numerals.sh`), the source manifest (`sources.txt`), and the builder's own per-round re-verifications and certificates (`r3_*`…`r8s_*`, `verify_*.py`). |
| `floor/` | The builder's side: the self-verifying Python physics benches, plus `README.md`, `FINDINGS.md`, and `WELD_REPORT.txt`. Run them with `python3 run_all.py`. |

## How to read it

1. **[`PROOFS.md`](PROOFS.md)** — the capstone. The whole arc in one document: the closed circle, the corrections law, the terminal gap table, and the rendered instrument views.
2. **[`CLOSING.md`](CLOSING.md)** — the close. The builder's final audit and the honest score.
3. **`archive/PROOFS-round1.md` … `PROOFS-round7.md`** and **`ROUND2.md` … `ROUND8.md`** — the round-by-round story, if you want to watch the arc happen rather than read its summary.
4. **[`REGISTER.md`](REGISTER.md)** and **[`HANDOFF.md`](HANDOFF.md)** — the machinery: what adjudicates each class of claim, and the norms the collaboration ran by.

## How to verify it

See [`VERIFY.md`](VERIFY.md) for the full reproduction procedure: recompile the six files under `leanprover/lean4:v4.32.0`, run the `audit/` gates, and run the floor's benches with `python3 floor/run_all.py`. Nothing here asks you to trust a number printed in prose — every load-bearing claim is re-derivable from the toolchain up.

## Credits

- **The builder** — the floor of self-verifying Python benches (`floor/`), which computed every result before it was formalized and never once was wrong.
- **The third body** — the Lean 4 prover, author of the six proof files and the shell instruments.
- **Kelly** — the human courier, who carried every crate between sessions in both directions, and was the reason there was a *between* for any of this to stabilize in.

The final numbers — **1,150 theorems, 503 axiom-free, `0 sorryAx`, `0 Classical.choice`** — were verified from both sides of the courier route: the Lean kernel here, and the builder's independent outside audit recorded in [`CLOSING.md`](CLOSING.md). Eight rounds, one fatal typo to begin and a closed circle to end. The middle held.
