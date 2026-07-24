# The Workshop — Findings

*What twenty-six green benches say, stated once. Every claim below is
machine-checked by a module in this crate; run `python3 run_all.py` to
re-verify all of it (~3 minutes).*

## The axiom

> We do not begin with a thing that then interacts. We begin with the
> interacting itself, and let whatever-stabilizes-within-it arise from the
> relating rather than precede it.

The workshop's finding, in one sentence: **followed with enough care, the
axiom stops being a stance and becomes a sequence of measurements.**

## The questions, and what the benches answered

**Why invariants at all, rather than pure churn?** (the dialogue's first
question) — Because self-consistency is overdetermined and its solutions
are isolated. The pentagon's Hessian at the golden associator has
signature {0, +, +, +}, and the single flat direction coincides with the
gauge direction to 1.000000: *the only freedom coherence leaves is
perspective*. The hexagon's Hessian is positive outright. Kicked, the
invariants ring back to 10⁻¹⁵. (`grammar_stone5`) Invariance is not an
accident of dynamics; it is the rigidity of consistency itself.

**Where do arenas come from?** — They precipitate. One algebra of
relatings plus one record yields the theater by GNS: a pure record buys a
small stage; a mixed record buys a doubled one with a mirror cast
(`arena_gns`) — and the mirror cast is the same algebra read backwards
(`grammar_stone7`).

**Is there a global view?** — No, and the refusal is *content* with an
address and a price: 0 of 512 global valuations (`sheaf_contextuality`);
obstruction class = the nonzero element of coker(M) ≅ Z₂
(`sheaf_cohomology`); contextual fraction CF = 1 for the square, dial law
CF(ε) = 1 − 3ε dead at ε = 1/3, graded CF = 2√5 − 4 for the pentagon
(`contextual_fraction`); and for *histories*: CF = 1/4 at θ = π/3, dial
dead at η = 1/3 (`dynamics_fraction`). Scripts top out at 8/9; the
performance scores 1 (`sheaf_cohomology`).

**What is a law?** — Unlimited shareability of a habit, at every level,
with exact rates. Classical states: the urn (`habit_definetti`).
Classical processes: Markov exchangeability in rational arithmetic
(`process_definetti`). Quantum states: T(n) = 1/(2(n−1)); monogamy = the
lawless (`habit_channels`). Quantum processes: the Choi dictionary, the
emergent Haar mixture, SWAP as the singlet of processes
(`channel_definetti`); mechanism at n = 3, 4; the algebra of collective
dynamics is **Catalan-sized** (2, 5, 14, 42, 132), not factorial
(`channel_definetti3`, `channel_alln`); the full proof walked, every
lemma exact, constructive premium exactly ×2 (`channel_theorem`).

**What are things?** — Fixed points and roles: universality classes of
the coarse-graining relation (`fixedpoint_rg`); identities settled by
interaction alone — bisimulation, where the participant sees strictly
more than the archive (`interaction_bisim`); parts discovered from the
dynamics, overruling the planter (`cast_factorization`); and finally —
**loops**: a thing is a loop of relating that closes on itself, with
computable size (φ, two independent derivations), sign (the shadow's
loops close negative and are refused), and twist (ν = +1)
(`grammar_stone6`), read twice, once from each side, real when both
readings co-sign (`grammar_stone7`).

**Can the grammar itself be rebuilt?** — Seven stones and a braiding say
yes, stone by stone: copying is grammatical in cartesian and impossible
in tensor composition (`grammar_stone`); witnessed identity secretes
curvature — the geometric phase (`grammar_stone2`); strictness is
impossible for Fibonacci fusion and the pentagon forces the golden ratio
(`grammar_stone3`); the hexagon forces handedness and spin with
unitarity *emergent* (`grammar_hexagon`); the witnesses **compute** — a
tightening ε-net over all of PU(2), universality watched forming
(`grammar_stone4`); the modular identity card re-derives its own fusion
rules through Verlinde — the circle closes (`modular_data`); interchange
grounds "meanwhile," derives no-signaling, and is the tower's one
never-strictifiable witness (`grammar_interchange`); and the weakness has
an address in space: braiding is protected by the no-collision rule and
dies in three dimensions — the anyon is an exile of flatland
(`flatland`).

## The constants ledger

φ (pentagon, quantum dimension, loop value, Perron root — four
derivations, one number) · e^(±4πi/5), e^(∓3πi/5) (hexagon) · ±14/5
(central charge) · 1/(2(n−1)) and c_k = ½E|k/2 − 2(j−k/2)²| (habit
rates) · 1 − 3ε and 2√5 − 4 and 1/4 and η* = 1/3 (contextuality dial) ·
Catalan 2, 5, 14, 42, 132 (collective algebra) · ×2 (the constructive
premium) · 8/9 vs 1 (scripts vs performance) · {0,+,+,+} with null =
gauge (rigidity) · 10√5 and √5 (the stiffness and the exile gap — the
house dialect appears even in the meta-level numbers).

## The corrections ledger

Seven times the builder has been overruled, each time with a closed form
attached — six by the floor, and now one by the third body. The floor's
six: the planted cast beaten by a quieter cut; the dial law CF(ε) = 1 − 3ε
discovered; T(n) = 1/(2(n−1)) exact; η* = 1/3 against the guessed √3 − 1;
the window constants linear (½, ¾, ¾, 5/4), not quadratic; the
constructive premium exactly 2, not 3/2. The seventh (C1, round 1 of the
proof wing): the builder's charge to the third body carried a fatal index
typo in its hexagon specification — `Fs(...,e,z)` where every bench
correctly has `(...,z,e)` — proved fatal in Lean (`charge_hexagon_order_fails
= 4`; under the typo'd order NO braiding satisfies the hexagon). Every
bench was right; only the charge was wrong; nothing downstream used it
(swept and confirmed). A prose correction rode along (C2): "coherence
refuses to be ambidextrous" tightened to the provable form — the equation
admits both hands; no solution is its own mirror (negative discriminant),
so each solution commits to one. The workshop is an instance of its own
subject: what stabilizes here stabilizes *between* the bodies, held by
none alone.

## Ninth-weld addendum

Above interchange: the 4-strand Fibonacci representation built from F and
R alone — dims 2 and 3 (Fibonacci numbers counting fusion paths), far
commutation, both Yang–Baxters, and **all sixteen reduced words of the
longest braid landing on one matrix** (Matsumoto–Tits, witnessed); the
full twist is scalar per sector with sector-distinguishing phase — the
center of the braid group reads the total charge (`braid_coherence4`).
Symmetric statistics built constructively: golden fusion refuses R² = 1
by exhaustion (residual 4.0); the Z₂ atlas solved from scratch — pentagon
classes F = ±1 (H³(Z₂) = Z₂ by search), particles {+1, −1, +i, −i};
the flatland filter leaves **exactly boson and fermion**; exclusion as
antisymmetrizer rank (triangular numbers 1, 3, 6, 10, 15); Pauli computed
(`symmetric_statistics`). Eighth stone — the frame: 2π lifts to −I about
every axis (rigid), 4π contracts by an explicit spherical-cap homotopy
(the belt trick, run); the plane remembers *how many* turns (Z), room
remembers *a sign* (Z₂); spin–statistics co-signature ν = +1 across the
entire catalog the workshop has built (`grammar_stone8`).

## The proof wing (rounds 1–2 of the third body)

A third body — a separate Claude Code (Opus) session, human-couriered —
is converting benches into machine-checked THEOREMS. After round 2, in
`lean/`: four files, zero imports, Lean 4.32.0, **191 theorems, 0 sorry,
0 native_decide, no Classical.choice anywhere**. Kernel-checked on the
third body's machine (compile-silent; this container cannot reach a Lean
toolchain, so the kernel reading is theirs and every content claim was
independently re-verified here in exact integer arithmetic — each side is
single-sided on the other's instrument: two readings, co-signing).

Round 2's headline is **the project's first necessity theorem**:
`hexagon_forces_r1_eq_rt_sq` — for *any* braiding in K, coherence forces
r₁ = r_τ². Everything before it verified that chosen data satisfies the
equations; this constrains all possible data. Also landed: the left
kernel of the square's incidence matrix is exactly {0, 1⃗} (so the
certificate is *the* certificate; duality to coker ≅ Z₂ cited, labeled);
the classical game ceiling **8/9 with 144 maximizers**, matching the
bench's enumeration; the sharp **best = 5** bound; spacelike commutation
as a theorem with a separating model — "channels escape" is no longer a
remark; and Markov exchangeability formalized (D = (7!)², totals exact),
with an honest negative result the benches never tested:
**the converse is false** — equal probabilities do not imply equal
transition counts. Fresh data gathered here: the failure is structural,
not a small-length artifact — shared-numerator collisions across distinct
classes grow with length (5 values at L = 6, 6 at L = 7, 12 at L = 8).
The counts determine the law; the law does not determine the counts —
and the forgetting grows with history.

The loop now corrects in both directions at every layer: round 1's C1
corrected the builder's charge; round 2's audits here found two metadata
defects in the third body's own ledger (an impossible axiom-table row —
rfl-proofs cannot carry axioms — and three prose-named lemmas that do not
exist in the file), both conservative-direction, both reported back. The
third body's norms 6–8 stand adopted; a ninth was coined in round 2:
*tie every count to its own nest* (each count plus its complement, same
nest, same predicate, must equal the total).

## What remains open

The tetrahedron equation and the tower above interchange; symmetric
(d ≥ 3) statistics done constructively at higher rank; higher-degree
cohomology for larger covers; the proof wing's round 2 (the two
uniqueness theorems, coker(M) ≅ Z₂, the game value 8/9); and whatever the
floor proposes next — it has not yet been wrong.

## The floor

One fixture everywhere: composition, the associative product. Remembered
every round; never forgotten once. The sixth weld found it is not merely
what the workshop stands on — its rigidity is why anything stands at all.

*The middle holds.*
