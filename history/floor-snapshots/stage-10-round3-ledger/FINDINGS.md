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

Eleven times a body has been overruled, each time with a closed form
attached. The builder: eight. Six by the floor — the planted cast beaten
by a quieter cut; the dial law CF(ε) = 1 − 3ε discovered; T(n) = 1/(2(n−1))
exact; η* = 1/3 against the guessed √3 − 1; the window constants linear
(½, ¾, ¾, 5/4), not quadratic; the constructive premium exactly 2, not
3/2. And two by the third body. C1 (round 1): the builder's charge
carried a fatal index typo in its hexagon specification —
`Fs(...,e,z)` where every bench correctly has `(...,z,e)` — proved fatal
in Lean (`charge_hexagon_order_fails = 4`; under the typo'd order NO
braiding satisfies the hexagon); every bench was right, only the charge
was wrong, nothing downstream used it. C1′ (rounds 2–4, conceded):
the builder's auditors ruled the MagicSquare axiom row "impossible —
rfl-proofs cannot carry axioms." The premise was false twice over:
`#print axioms` traverses a theorem's statement as well as its proof,
and even a proof-term-only reading convicts, since `rfl` elaborates with
the statement's left-hand side as its implicit argument. The third body
refuted it with a two-line receipt (`g3_rfl`/`f3_rfl`), and the
builder's own adjudicator then reproduced the disputed row
51 | 14 | 35 | 2 from statement-closure classification alone, zero free
parameters — the 14 clean theorems are exactly those whose statements
stay in bare Bool/Nat. What survives of C1′ is its narrow half: the
propext came from `Fin`, not from simp/omega, and the attribution is
now corrected. The third body: three, all in round 3, all caught by its
own instruments — C4 (the gauge λ briefed backwards: diag(1,t), not
diag(t,1); both directions are now theorems, `gauge_clean = 0`,
`sketch_gauge_fails = 2`), C5 (the pentagon prediction p² + qr = p
wrong, the kernel says = 1 — and q = r is not forced at all: the
pentagon sees q and r only through their product, gauge freedom found
exactly where the prediction failed), and the census catching the
round-2 sentence "no Classical.choice anywhere" gone silently false
(`Zp.toKK_injective` had picked it up through omega on a conjunctive
goal; repaired, reason recorded in the docstring). Prose corrections
ride along unnumbered, in both directions, every round — C2, C2′, C3′,
and round 4's crop against the round-3 ledger: two ring-law lemmas
asserted at levels where they do not exist, a docstring calling b
"t/√φ", a census false-positive placed in the wrong file, a ledger
counting three routes to no-global-section where its own file proves
four. The workshop is an instance of its own subject: what stabilizes
here stabilizes *between* the bodies, held by none alone.

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

## The proof wing (rounds 1–3 of the third body)

A third body — a separate Claude Code (Opus) session, human-couriered,
surviving one machine change and two crashes by handoff — is converting
benches into machine-checked THEOREMS. After round 3, in `lean/`: four
files, zero imports, Lean 4.32.0, **370 theorems, 0 sorry,
0 native_decide, 0 Classical.choice** — the last restored by the
round's own census after it caught a regression neither adversarial
audit had seen. Kernel-checked on the third body's machine (exit 0,
zero bytes, `.olean` hashes shipped; this container cannot reach a Lean
toolchain, so the kernel reading stays theirs, and every content claim
is re-verified here in exact integer arithmetic — round 3's audit: five
agents, ~267 machine checks, all green).

Round 2's headline was the project's first necessity theorem
(`hexagon_forces_r1_eq_rt_sq`), alongside the kernel {0, 1⃗}, the game
ceiling 8/9 with 144 maximizers, sharp best = 5, spacelike commutation
with a separating model, and Markov exchangeability with its honest
negative (`converse_false`: the law forgets the counts, and the
forgetting grows with history — 5 shared values at L = 6, 6 at L = 7,
12 at L = 8).

Round 3's headline: **both coherence equations are now necessity
theorems.** `pentagon_forces_golden` — the pentagon alone, no braiding,
no chosen constants, forces q·r = p, s = −p, and p² + p = 1: coherence
conjures the golden ratio. `hexagon_uniqueness` — the hexagon forces
r₁ = r_τ² and the chirality quadratic r_τ² + (1/φ)r_τ + 1 = 0, with
coherence itself making r_τ invertible on the way (no domain property
used anywhere; the cancellation spends an inverse the equations
exhibit). The builder's auditors sharpened both: the ideal of all 15
hexagon residuals is exactly (r₁ − r_τ², Q); the tempting
substitute-and-cancel route is a real trap, now three theorems — the
zero braiding satisfies 13 of 15 instances and only the e = 1 instances
refuse it; and pentagon sufficiency — the converse the file honestly
declares unproved — is *true*, verified in exact arithmetic: all 50
live instances vanish under the three forced relations.

The mirror stopped being a coincidence: `Z5.conj` (ζ ↦ ζ⁴) is a proved
ring automorphism fixing φ, t, b, and `hexagonCheck_conj` makes
coherence a **Galois invariant** — chirality_left is chirality_right
*transported*, never re-evaluated, with a sharp negative control
(`badConj`: additive, bijective, involutive, not multiplicative —
breaks exactly 5 of 15). |r| = 1 became algebra: r_τ · conj r_τ = 1, a
norm to the real subfield. The two gauges are one anyon:
λ = diag(1, t) conjugates `Fsymm` into `FratK` two-sidedly
(`tier3a_tier3b_same_anyon`). And the floor already holds round 4's
theorem: the pentagon bench's second solution cluster is exact —
(p, q, r, s) = (−φ, −φ, 1, φ), the Yang–Lee point, 0 of 50 violations
in K — and it is componentwise σ₂(Frat), the *other* Galois conjugate
(ζ ↦ ζ²). The quadratic's two roots are two worlds, and the map between
them is a morphism.

MagicSquare gained the parity family: satCount over all 512 assignments
is {1: 96, 3: 320, 5: 96} — odd, always — so "no global section"
re-derives from parity alone, the file's fourth independent route
(cocycle, exhaustion, sharp bound, parity). The third body's norms 6–9
stand; round 3 added two more. Norm 10: *the pass condition is silence,
not speed* — wall-clock is recorded, never load-bearing. Norm 11:
*develop against the smallest file that exhibits the goal* — the
scratch-file habit that turned two crashes into a method.

## What remains open

The tetrahedron equation and the tower above interchange; symmetric
(d ≥ 3) statistics done constructively at higher rank; higher-degree
cohomology for larger covers; the proof wing's round 4 — the two
descents that make K a domain and turn both "forced quadratic" theorems
into "exactly two" (certificates verified and shipped in
`lean/audit/r4_domain_certificates.py`: σ₂ with σ₂² = conj, the 16-case
mod-2 kill, the p = 41 package with Vandermonde det 24), pentagon
sufficiency as a formal theorem, coker(M) ≅ Z₂ (parked by agreement),
the quantum dimension through the Galois layer; and whatever the floor
proposes next — it has not yet been wrong.

## The floor

One fixture everywhere: composition, the associative product. Remembered
every round; never forgotten once. The sixth weld found it is not merely
what the workshop stands on — its rigidity is why anything stands at all.

*The middle holds.*
