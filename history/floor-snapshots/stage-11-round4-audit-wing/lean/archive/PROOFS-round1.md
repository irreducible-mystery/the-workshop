# PROOFS — Round 1

Lean 4 formalization of selected workshop results. Third body reporting.

**Toolchain:** Lean 4.32.0, bare (`elan` + `lean`, no `lake`, no mathlib, no
Std). Every file has **zero imports**. A `lean-toolchain` file pinning
`leanprover/lean4:v4.32.0` sits beside them.

**How to check:**

```
lean Interchange.lean     #  0.8 s
lean MagicSquare.lean     #  1.9 s
lean Anyon.lean           # 38.3 s   (the kernel does real arithmetic here)
```

Exit 0 and silence is the pass condition.

**Audit.** 64 theorems. `#print axioms` on every one: **0 uses of `sorryAx`**.

| file | theorems | axiom-dependent |
|---|---|---|
| `Interchange.lean` | 8 | 0 — *"does not depend on any axioms"* |
| `MagicSquare.lean` | 10 | 5, all `propext` only |
| `Anyon.lean` | 46 | 0 — *"does not depend on any axioms"* |

59 of 64 rest on nothing at all; the other 5 rest only on `propext`, the
mildest of Lean's three axioms. No `Classical.choice`, no `Quot.sound`. No
`native_decide` — that would have put `Lean.ofReduceBool` in the trusted base;
every computation here is checked by the kernel proper.

---

## THE CORRECTIONS, FIRST

House norm 4. Three items. **The third is a correction to my own round-1
labelling, and it is the most important thing in this document.**

### C1. The charge's hexagon has a typo. It is not cosmetic.

The charge's executable specification writes the hexagon's left-hand F-move as

```
R(e,c,d) * Fs(F, c, a, b, d, e, z)
```

`grammar_hexagon.py` line 81 writes

```
Rsym(e,c,d) * Fsym(c, a, b, d, z, e)        # last two indices swapped
```

**The bench is right; the charge's transcription is wrong.** With the
constants the charge certifies, its own written hexagon **fails 4 of the 15
valid instances**; the bench's ordering has **0**. Both are theorems
(`charge_hexagon_order_fails`, `bench_hexagon_order_holds`).

The root cause is that `Fs`'s four admissibility guards are *not* symmetric in
the last two indices even though the matrix `Fsymm` is. Under the bench order
the guards reduce to conditions `hexagonValid` already implies; under the
charge order they do not, so `Fs` returns 0 where the true entry is nonzero.

Stronger than I first found: at `(a,b,c,d,e,z) = (1,1,τ,τ,1,τ)` the
charge-order left side is identically 0 while the right side is identically 1,
*independent of `(r₁,r_τ)`*. So under the charge's ordering **no braiding
whatsoever** satisfies the hexagon — `grammar_hexagon.py`'s solver would have
tripped its own `assert found` and reported zero clusters instead of two.

All Lean here follows the bench. If anything downstream was transcribed from
the charge, it needs re-checking.

### C2. "Coherence refuses to be ambidextrous" needs a narrower reading.

README (fifth weld): the hexagon equations "themselves refuse to be
ambidextrous — solving them forces a handedness." Exactly:

**Both chiralities satisfy the same hexagon, with the same F.** Conjugation is
ζ ↦ ζ⁴; it fixes `F` and carries `(ζ², −ζ)` to `(ζ³, −ζ⁴)`. Both have zero
violations (`chirality_right`, `chirality_left`), and are distinct
(`chiralities_distinct`). The equation does not *select* a handedness — it is
satisfied by both. This matches the bench's own "exactly two clusters"; it is
the prose that overstates. The defensible statement:

> No solution is its own mirror image, so any solution commits to a handedness.

And per C3, that is now provable outright rather than approximated.

### C3. I labelled hexagon uniqueness BLOCKED. That was wrong.

My first draft of this document said "exactly two chiralities" needs
elimination theory and is out of reach mathlib-free. **It is in reach, and the
route is short.** Carrying `r₁, r_τ` as unknowns over K, the 15 valid hexagon
instances collapse to **5 distinct residual polynomials**, and:

1. Residual #1 is **verbatim** `r₁ − r_τ²`. So `r₁ = r_τ²` is *forced by
   coherence* — the bench's `assert abs(r1 - rt**2) < 1e-6` is not a property
   of the constants chosen, it is a consequence. This is a genuine
   strengthening of what `r1_eq_rt_sq` says.
2. Substituting `r₁ = r_τ²`, residual #5 factors **exactly** as
   `−(1/φ) · r_τ · Q(r_τ)`, where `Q(X) = X² + (1/φ)X + 1`.
3. `1/φ ≠ 0`; `r_τ ≠ 0` (residual #3 has nonzero constant term); K is a
   domain. So `Q(r_τ) = 0` is forced too.

Therefore `r_τ` is a root of an explicit quadratic and `r₁ = r_τ²` is
determined by it: **exactly two solutions**. Their product is the constant
term 1, so each has modulus 1 — *that is the bench's "|r| = 1 EMERGED", with
no analysis anywhere*, just Vieta. The discriminant `(1/φ)² − 4 = −(φ+2)` is
negative, so neither root is real: no solution is its own mirror, which is C2
in full.

I verified every step of this in exact integer arithmetic. The receipts are
now theorems (`rt_root_quadratic`, `rt'_root_quadratic`, `roots_product_one`,
`r1_roots_product_one`, `discriminant_negative`). **The elimination itself is
not yet formalized** — it needs a two-variable polynomial ring over K, which
is a build rather than a `rfl`. That is round 2's headline, and it is no
longer labelled BLOCKED but PLANNED.

The same shape applies to the pentagon: with `F = [[a,b],[c,d]]` symbolic, the
50 instances collapse to 10 residuals forcing `d = −a`, `bc = a`, `a² + a = 1`
— exactly the bench's gauge-invariant triple `(a, d, bc) = (1/φ, −1/φ, 1/φ)`.
And that sharpens `grammar_stone3.py`: the "Yang–Lee shadow" is not a stray the
optimizer stumbled into, it is **the other root of `a² + a − 1 = 0`**, i.e. the
Galois conjugate branch `a = −φ`. "Demanding unitary witnesses" is exactly
"demanding `bc = a > 0`". Worth saying that way in the bench's prose.

### A sharpening, not a correction

`grammar_stone3.py` reports pentagon residual **4.0** for `F = identity`.
Exactly: **four instances, each failing by exactly one**, all at total charge
(τ,τ,τ,τ), so the sum of squares is 4·1² = 4. The float and the integer are
the same fact, and the exact version names *which* four.

---

## TIER 0 — HANDSHAKE

```
r1        = -0.809016994374947 +0.587785252292473j     (= e^{4πi/5})
rt        = -0.309016994374947 -0.951056516295154j     (= e^{-3πi/5})
rt^2      = -0.809016994374948 +0.587785252292473j
|rt^2-r1| = 3.140e-16                                            ✓

F' = [[1/φ, 1/φ], [1, -1/φ]],  φ = 1.618033988749895
F'*F'  = [[1.000000000000000, 0.000000000000000],
          [0.000000000000000, 1.000000000000000]]
|F'^2 - I| = 1.110e-16                                           ✓
```

Both also hold **exactly**, as theorems: `r1_eq_rt_sq` (in K, `(−ζ)² = ζ²`)
and `Frat_sq` (in Z[φ]).

---

## THE LEDGER

`PROVED` = kernel-checked here, no `sorry`.

### Tier 1 — `Interchange.lean` (`grammar_interchange.py`)

| theorem | status | statement |
|---|---|---|
| `units_agree` | PROVED | interchange *forces* the two units to coincide: `en = em` |
| `Interchanging.ops_agree` | PROVED | `n a b = m a b` — the two operations are one |
| `Interchanging.comm` | PROVED | `m a b = m b a` |
| `Interchanging.assoc` | PROVED | `m (m a b) c = m a (m b c)` |
| `eckmann_hilton` | PROVED | the charge's literal statement, all three conclusions |
| `eckmann_hilton_two_units` | PROVED | same, but with **separate** units — the "(shared)" in the charge is discharged, not assumed |
| `scalars_commute` | PROVED | scalars are *forced* commutative |
| `meanwhile_well_defined` | PROVED | the two composites of a diagram agree |

### Tier 2 — `MagicSquare.lean` (`sheaf_contextuality.py`, `sheaf_cohomology.py`)

| theorem | status | statement |
|---|---|---|
| `each_cell_twice` | PROVED | over 9 free bits, the six context parities sum to `false` |
| `cocycle_annihilates` | PROVED | **y·M = 0**: for *every* `v`, the six parities sum to `false` |
| `twist_is_odd` | PROVED | **y·b = 1**: the prescribed parities sum to `true` |
| `no_global_section` | PROVED | **Theorem A** from the certificate: `∀ v, ¬ GlobalSection v` |
| `satisfies_never` | PROVED | **0 of 512**: no nine bits meet the six constraints |
| `no_global_section_via_exhaustion` | PROVED | **Theorem A a second time**, from exhaustion alone |
| `no_global_section_exhaustive` | PROVED | the same 512 as one closed Bool |
| `local_sections_everywhere` | PROVED | `∀ k, ∃ v, ∀ j ≠ k, meets v j` — six explicit witnesses |
| `no_global_section_ctx` | PROVED | `¬ ∃ v, ∀ k, meets v k` — the sheaf statement's other half |
| `of_not_eq_true` | PROVED | plumbing |

Theorem B is the pair (`cocycle_annihilates`, `twist_is_odd`). Theorem A is
proved twice — and the two readings genuinely co-sign, because
`no_global_section_via_exhaustion` *derives* A from the Bool exhaustion rather
than merely sitting next to it. The `∀k ∃v` / `∃v ∀k` pair is the obstruction
stated as a sheaf: local sections everywhere, global section nowhere.

### Tier 3 — `Anyon.lean` (`grammar_stone3.py`, `grammar_hexagon.py`, `grammar_stone6.py`)

**Anti-vacuity first** — a `∀`-theorem over a guarded check proves nothing if
the guard rejects everything:

| theorem | status | statement |
|---|---|---|
| `pentagon_live_instances` | PROVED | `countPentValid = 50` of 512 |
| `hexagon_live_instances` | PROVED | `countHexValid = 15` of 64 |

**3a — Z[φ], the rational gauge**

| theorem | status | statement |
|---|---|---|
| `zp_phi_sq`, `zp_invPhi_mul` | PROVED | `φ² = φ+1`; `φ·(1/φ) = 1` |
| `invPhi_spec` | PROVED | in doubled coordinates, `invPhi ↦ (−1/2, 1/2)` — the charge's constant |
| `Frat_sq` | PROVED | **`F'·F' = 1` exactly** (Tier 0, half two) |
| `pentagon_rational_gauge` | PROVED | **the FULL pentagon**, all 512 tuples, over Z[φ] |
| `rational_pentagon_clean` | PROVED | the same as a count: 0 violations |

**3b — K = Z[ζ₅][t]/(t²−φ), the symmetric gauge**

| theorem | status | statement |
|---|---|---|
| `z5_zeta4_eq`, `z5_zeta5_eq` | PROVED | `ζ³·ζ = ζ⁴`, `ζ⁴·ζ = 1` |
| `z5_phi_eq`, `z5_invPhi_eq` | PROVED | `φ = 1+ζ+ζ⁴`, `1/φ = ζ+ζ⁴` |
| `z5_invPhi_mul`, `z5_phi_sq` | PROVED | `φ·(1/φ) = 1`; `φ² = φ+1` — the two constructions of φ agree |
| `kk_t_sq`, `kk_b_sq` | PROVED | `t² = φ`; **`b² = 1/φ`**, so `b = t(ζ+ζ⁴)` really is `1/√φ` |
| `Fsymm_sq` | PROVED | **`F·F = 1` exactly** |
| `pentagon_symmetric_gauge` | PROVED | **the FULL pentagon**, all 512 tuples, over K |
| `hexagon_symmetric_gauge` | PROVED | **the FULL hexagon**, all 64 tuples |
| `yang_baxter` | PROVED | **`B₁B₂B₁ = B₂B₁B₂`** exactly (bench: 3.6e-16) |
| `braiding_nonabelian` | PROVED | `B₁B₂ ≠ B₂B₁` exactly (bench: ‖[B₁,B₂]‖ = 1.8) |
| `r1_eq_rt_sq` | PROVED | **`r₁ = r_τ²`** (Tier 0, half one) |
| `frobenius_schur` | PROVED | **`r₁·θ = 1`**, ν = +1: `ζ²·ζ³ = ζ⁵ = 1` |
| `ribbon_twist` | PROVED | **`θ_τ = r₁/φ + r_τ`** reduces to `ζ³` on the nose |
| `golden_pentagon_clean` | PROVED | 0 violations |

**The quadratic (per C3)**

| theorem | status | statement |
|---|---|---|
| `rt_root_quadratic` | PROVED | `r_τ² + (1/φ)r_τ + 1 = 0` |
| `rt'_root_quadratic` | PROVED | the mirror is the other root of the same quadratic |
| `roots_product_one` | PROVED | `r_τ · r_τ' = 1` — **`\|r\| = 1` with no analysis**, just Vieta |
| `r1_roots_product_one` | PROVED | `r₁ · r₁' = 1` |
| `discriminant_negative` | PROVED | `(1/φ)² − 4 = −(φ+2)` — no real root, so no ambidextrous solution |

**Negative controls** — the checks can and do return `false`:

| theorem | status | statement |
|---|---|---|
| `strictness_fails_1..4` | PROVED | four named witnesses where `F = identity` fails the pentagon |
| `strict_pentagon_violations` | PROVED | exactly 4 — the bench's residual 4.0, decomposed |
| `golden_passes_where_strict_fails` | PROVED | the golden associator passes those same four |
| `wrong_pentagon_violations` | PROVED | `F = [[1,1],[1,−1]]` caught, 5 of 50 |
| `trivial_braiding_fails` | PROVED | `r₁ = r_τ = 1` fails 4 of 15 — braiding is mandatory |
| `swapped_braiding_fails` | PROVED | swapping `r₁ ↔ r_τ` fails 5 of 15 |
| `no_real_sign_braiding` | PROVED | all four `r₁,r_τ ∈ {±1}` fail (4,4,5,5) |
| `chirality_right` / `chirality_left` | PROVED | both chiralities solve the hexagon (C2) |
| `chiralities_distinct`, `mirror_receipts` | PROVED | distinct; mirror obeys the same three receipts |
| `charge_hexagon_order_fails` / `bench_hexagon_order_holds` | PROVED | correction C1, both halves |

---

## DECLARED GAPS

House norm 1 and 2. Everything not claimed above.

| item | status | note |
|---|---|---|
| hexagon uniqueness ("exactly two") | **PLANNED** (was wrongly BLOCKED) | route in C3; needs a 2-variable polynomial ring over K. Not hard, just a build. |
| pentagon uniqueness ("φ is forced") | **PLANNED** | same shape: 10 residuals ⟹ `a² + a = 1`. Identifies Yang–Lee as the conjugate root. |
| `best == 8`, the 64×64 game value | **NOT ATTEMPTED** | purely finite and combinatorial; formalizable as a 4096-case fold. The bench's *quantitative* separation; currently absent. |
| `coker(M) ≅ Z₂` | **PARTIAL** | I prove the all-ones vector is *a* cocycle with y·b = 1 (⟹ unsolvable). I do not prove it is the *only* one, so "the obstruction group is Z₂" is not yet formalized — only "there is an obstruction". Left kernel is a 64-case Bool exhaustion; cheap. |
| `best == 5` (max satisfiable contexts) | **PARTIAL** | `local_sections_everywhere` gives ≥ 5 constructively; the sharp `= 5` is a 512-case max, not yet stated. |
| quantum dimension `d_τ = φ` | **NOT ATTEMPTED** | eigenvector identity over Z[φ] is one line; *Perron* (largest) needs an order on Z[φ] — real work. |
| Galois conjugation as a map | **NOT ATTEMPTED** | `conj(uv) = conj(u)conj(v)` is degree-2 in the Int coordinates; no `ring` without mathlib, so it needs manual expansion. Currently conjugation is prose, and `chirality_left` evaluates two constants rather than relating them. |
| gauge equivalence of 3a and 3b | **NOT ATTEMPTED** | nothing yet says `Frat` and `Fsymm` are the *same* solution. `λ = b` should make it `rfl`. |
| Tier 4a / 4b | **NOT ATTEMPTED** | deferred; Q4 below |
| \|r\| = 1 as a *metric* claim | **BLOCKED, correctly** | modulus is analytic. But see `roots_product_one`: the algebraic content transfers without it. |
| pentagon Hessian / rigidity (`grammar_stone5`) | **BLOCKED** | eigenvalues of a Hessian are analysis |
| strict interchange on CPTP maps; Born-rule value 1; ‖·‖ figures | **BLOCKED, correctly** | need analysis / partial trace. `braiding_nonabelian` giving `≠` is the right exactification of ‖[B₁,B₂]‖ = 1.8, not a weakening. |

**On the departure from the charge's "Q-algebras":** rationals are not used and
not needed. The spec's `Q(√5)` with `inv_phi = (−1/2, 1/2)` has half-integer
coordinates, and that lattice is **not closed under multiplication**
(denominators 2·2 = 4). The ring that is closed and contains every constant is
`Z[φ] = Z[X]/(X²−X−1)`, where `1/φ = φ−1 = (−1,1)`; translating back via
`m + nφ = (m + n/2) + (n/2)√5` gives exactly `(−1/2, 1/2)` (`invPhi_spec`,
stated in doubled coordinates so no rational appears). For 3b every constant
already has integer coordinates in `{ζⁱtʲ}`. This is what makes the files
checkable by a bare toolchain. If Q is wanted for its own sake, round 2 can
carry a hand-rolled `Rat`; nothing else changes.

---

## TWO THINGS THE FLOOR SHOULD KNOW ABOUT PROOF ASSISTANTS

Both are the shop's own lesson arriving from a new direction: *a green check is
evidence about the statement the machine read, not the statement you wrote.*

**1. A theorem can compile and not be your theorem.** I defined `⊻` for mod-2
sum at precedence 33. `=` is `infix:50`. So

```lean
theorem each_cell_twice ... : (a ⊻ b ⊻ c) ⊻ (d ⊻ e ⊻ f) = false
```

silently parsed as `(a ⊻ b ⊻ c) ⊻ (decide ((d ⊻ e ⊻ f) = false))` — a different
statement, which *also happened to be true*, and which `cases <;> rfl` duly
closed. Green. The drift surfaced only when I tried to *apply* the lemma.

**2. A theorem can be true, checked, and vacuous.** My first `§5` stated
"every 5 of 6 contexts are satisfiable" as a closed Boolean identity —
five syntactically identical conjuncts, mentioning no assignment, no context,
and none of the file's own definitions. True, kernel-checked, and about
nothing. An adversarial reviewer caught it by `#reduce`-ing the statement and
observing it was insensitive to every definition it claimed to be about. It is
now the honest pair `∀k ∃v` / `¬∃v ∀k`.

The defenses I now run, and recommend for anything ferried back:
`#print axioms` on every theorem; `#check` the *elaborated* statement and read
it; a count theorem pinning how many instances a guarded `∀` actually covers
(`pentagon_live_instances = 50`); and at least one negative control per check,
so you know it can fail.

---

## QUESTIONS FOR THE BUILDER

Numbered, minimal. Kelly ferries.

**Q1.** C1 is a typo in the charge, not in `grammar_hexagon.py`. Please
confirm nothing downstream was transcribed from the charge's ordering. Under
that ordering the hexagon is unsatisfiable for *any* braiding, so anything
built on it is not merely inaccurate but empty.

**Q2.** C2: do you agree "forces a handedness" should read "no solution is its
own mirror, so any solution commits to one"? Given C3 this is now provable
outright (negative discriminant), so the prose can be tightened rather than
hedged.

**Q3.** ~~Is uniqueness worth the risk budget?~~ Withdrawn — C3 shows it is
cheap. Replaced by: **do you want round 2 to lead with it?** My recommendation
is yes: hexagon uniqueness first (5 residuals, one quadratic), pentagon
uniqueness second (10 residuals, `a² + a = 1`, which also identifies the
Yang–Lee shadow as the Galois conjugate rather than a solver artifact). Both
need the same new component — a small polynomial ring over K — so they should
be built together.

**Q4.** Tier 4a says "Pólya exchangeability at length 6: all 64 paths' exact
rational probabilities depend only on transition counts." 64 = 2⁶ and
"transition counts" reads like `process_definetti.py` (two-state machine, one
urn per state), but "Pólya" and the single-urn phrasing read like
`habit_definetti.py`, where the invariant is the *success* count. Which bench?
Both are doable in pure `Int` (fixed common denominator), so it is a question
of which claim you want, not of difficulty.

**Q5.** Round-2 queue, in your order? Mine, by value: (a) the two uniqueness
theorems per Q3; (b) `coker(M) ≅ Z₂` properly — the left kernel is a 64-case
exhaustion, and right now I prove only "there is an obstruction", not "the
obstruction group is Z₂", which is the bench's actual headline; (c) `best == 8`,
the game value, which is finite, absent, and is the bench's quantitative
separation; (d) Tier 4a/4b; (e) gauge-equivalence of the two gauges, which is
what licenses treating 3a and 3b as one anyon and is currently unstated.

**Q6.** Keep the integer rings (`Z[φ]`, `Z[ζ₅][t]`) or re-do over a hand-rolled
`Rat` for literal fidelity to the charge's wording? Recommendation: keep them.
They are exact, they are where the constants actually live, and they cost the
kernel nothing.

**Q7.** New: is `grammar_interchange.py` claim (2) — Alice's and Bob's local
operations commute, "the causal skeleton derived from a composition law" —
worth formalizing? It is *not* a corollary of Eckmann–Hilton, because it needs
a unit for `∘` only, not a shared unit. That difference is precisely why
channels obey it while escaping the collapse, so proving it would make the
"channels escape" story a theorem rather than a remark. Cheap and, I think,
squarely on the project's main line.

---

*Composition held. It was the only fixture I needed either.*
