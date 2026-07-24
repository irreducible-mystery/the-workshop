# The Workshop — first weld

> Hold still nothing but the joining; make every noun earn its way in
> as a fixed point, a sediment, a habit, a role.
> Weld the five existing instruments first; spend the risk budget on the
> law-tool. And it would be built from inside, of course.
> There is no other workshop.

Six benches of executable, self-verifying mathematics for process-first
physics. Every module states a claim from the dialogue, checks it by
machine, and fails loudly if the check fails. Run everything with:

```
python3 run_all.py        # writes WELD_REPORT.txt
```

Requires numpy + scipy. Total runtime ≈ 45 s (the cast search dominates).

## The benches

| Bench | Module | Obstruction addressed | What is checked |
|---|---|---|---|
| 1 Arena | `arena_gns.py` | state space given in advance | GNS: the theater precipitates from the algebra of relatings + one record. Pure record → dim 2, trivial commutant; mixed record → dim 4 with a mirror cast (commutant ≅ M₂ — thermofield double in miniature). Homomorphism, adjoints, cyclicity, record-reproduction all asserted. |
| 2 Sheaf | `sheaf_contextuality.py` | the view from the wings | Mermin–Peres square: 9 relatings, 6 contexts, quantum facts verified; **0 of 512** global valuations exist; every 5 of 6 contexts are satisfiable. Local sections everywhere, global section nowhere — exhaustively. |
| 3 Habit | `habit_definetti.py` | law/state split (the script) | Pólya urn: each history congeals its own constant; the ensemble of constants matches the de Finetti measure (KS ≈ 0.009); a hidden-parameter world is statistically identical (TV ≈ 0.02) though no parameter exists in the mechanism; precedent binds (conditional mean 0.838 vs predicted 0.833); young worlds are sloppier (swing 0.050 → 0.007). |
| 4 Fixed point | `fixedpoint_rg.py` | the spectator / whatever-stabilizes | 1D Ising decimation (exact): all couplings flow to nothing — no 1D transition, re-derived. 2D Migdal–Kadanoff (approximate, labeled): K* = 0.3047, λ = 1.679, ν ≈ 1.34; watershed verified. Plus a quine, run and matched against its own source: the diagonal as fixed point, not paradox. |
| 5 Interaction | `interaction_bisim.py` | statement vs participation | Bisimulation by partition refinement: different anatomies, same process (identity from relating alone); and two machines with identical trace archives that interaction nevertheless distinguishes — the participant sees strictly more than the spectator. |
| 6 Cast | `cast_factorization.py` | the parts given in advance | A two-qubit Hamiltonian local in a hidden factorization, Haar-scrambled (interaction weight 0.0225 → 0.37). Search over all factorizations recovers a cut with weight **0.0000** — see the note below — and in that frame product states hold records (entanglement 0.000 vs 0.246 bits for random cuts). |

## Second weld — the deepenings

| Bench | Module | What is checked |
|---|---|---|
| 2 deepened | `sheaf_cohomology.py` | The obstruction gets an address: over GF(2), rank M = 5, rank [M\|b] = 6 — unsolvable; obstruction group coker(M) ≅ Z₂ computed, class of b nonzero, witnessing cocycle y = (1,…,1) exhibited (y·M = 0, y·b = 1). Then the square as a game: all 64 × 64 deterministic scripts exhausted — ceiling **8/9**; the quantum performance (\|Φ⁺⟩⊗\|Φ⁺⟩, row triples vs transposed column triples) scores **exactly 1** by Born-rule computation and 9,999 sampled rounds with 0 failures. |
| 3 deepened | `habit_channels.py` | Quantum de Finetti in miniature: the half-excited Dicke habit's 2-qubit reduction converges to an i.i.d. mixture with **T(n) = 1/(2(n−1)) exactly** (log-log slope −1.017), inside the ~16/n bound. The lawless case: the singlet is swap-invariant, pure, entangled (PT eigenvalue −0.500) — hence admits no symmetric 3-extension. Law = unlimited shareability; monogamy marks where law runs out. |
| 7 cornerstone | `grammar_stone.py` | The empty bench's first stone: copying is *natural* in cartesian grammar (verified for 200 random functions) and *impossible* in tensor grammar (naturality constraints leave a 0-dimensional solution space; the scalar test 2Δ = 4Δ kills it). No-cloning derived from composition alone — the classical/quantum line drawn before dynamics. |

## A finding the planter did not plant

Bench 6 was built to *recover* the hidden cut (weight 0.0225). It found a
strictly better one: weight 0.0000. This is real, not a bug — the planted
Hamiltonian's spectrum {±s, ±d} secretly admits an *exactly* interaction-free
factorization (arrange the eigenvalues so the ZZ component cancels), and the
search found it. The play knew a better cast than the one hidden in it.
The moral sharpened itself: the parts really do come from the dynamics, not
from the presentation — even the builder's intended parts get overruled.

## Honest labels

Exact, machine-verified: benches 1, 2, 5, the 1D flow and the quine in 4.
Approximate, labeled: the 2D Migdal–Kadanoff recursion (structure right,
exponent coarse: ν ≈ 1.34 vs exact 1). Rigorous toys: benches 3 and 6 —
every statement they make is a theorem or has planted ground truth, but they
are miniatures of the real programs (law-as-habit; quantum mereology), not
the programs themselves.

## The (formerly) empty bench

The grammar bench — quantum mechanics rewritten with no strict equalities,
every identification carrying its witness (the HoTT/∞-categorical rebuild) —
now has a cornerstone (`grammar_stone.py`) and nothing else. The stone is
real: grammar alone already separates classical from quantum. The bench
stays open on purpose; the rebuild is the long work, and it is not faked
here.

## Floor check

Every bench stands on exactly one fixture: composition — the associative
product. It held.
