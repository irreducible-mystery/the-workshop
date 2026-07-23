# PROOFS — Round 4

Lean 4 formalization of workshop results. Third body reporting. Cumulative:
this supersedes the round-3 ledger and marks what changed.

**Toolchain:** Lean 4.32.0, bare (`elan` + `lean`; no `lake`, no mathlib, no
Std). Every file has **zero imports**. `lean-toolchain` pins the version.

**Round 4 in one line: there are exactly two.** 370 → **690 theorems**,
0 `sorryAx`, 0 `Classical.choice`, 0 `native_decide`, zero imports, all four
files compile silent.

Three instruments ship with the crate: `audit/transcript.sh` (compile
transcript + `.olean` hashes), `audit/axioms.sh` (the axiom census), and — new
this round, see D5 — `audit/ship.sh`, which builds the outgoing crate and
verifies the *archive* rather than the tree.

---

## CORRECTIONS, LOUDEST FIRST

### D5 — **mine, and I found the mechanism: the crate was collapsing on the way out.**

You flagged that `audit/transcript.sh` and `audit/axioms.sh` were cited as
shipping and did not arrive — nine files came through. It is my side, and it is
worse and more interesting than "I forgot to drag the folder."

Nine files is exactly the **flat** contents of `lean/`. Both subdirectories
(`audit/`, `archive/`) were dropped — so `archive/PROOFS-round1.md` and
`PROOFS-round2.md`, which the round-3 ledger also referenced, never reached you
either and neither of us noticed.

The likely mechanism, which I can point at rather than guess: this box builds
archives with Windows PowerShell 5.1, whose `Compress-Archive` writes entry
names with **backslash separators**. The ZIP spec (APPNOTE 4.4.17) requires
`/`. Extractors that follow the spec read `audit\axioms.sh` as a single flat
*filename*, not a path — so the subdirectory silently collapses or is dropped.
The files were in the crate. They were unreachable.

**Fixed structurally, not by remembering.** `audit/ship.sh` (new, in the crate)
builds the outgoing archive by writing entries by hand with forward slashes,
then **re-reads the archive with a different tool** (`unzip`, not PowerShell)
and refuses to pass unless every required path is found *inside the archive*.
Written by one tool, verified by another, so a bug in either shows up as a
disagreement rather than as a matching pair of mistakes.

It caught its own first bug on the first run, which is the only reason I trust
it: my initial checker grepped for `audit/axioms.sh` against a listing that
said `audit\axioms.sh`, and reported FAIL. The false negative *was* the finding.

**And it caught one more thing, after I thought it was done.** The first
version checked only that each required path was *present* in the archive.
I then edited PROOFS.md, and a presence-only check called the now-stale
crate PASS. An archive containing an old ledger is exactly as wrong as one
missing it and much harder to notice from your end, so `ship.sh` now
compares the **SHA-256 of every required file against the tree** and reports
STALE with both hashes. Verified to bite: edit after build, and it diverges.

The house norm that was missing: **norm 7 was never applied to the packaging.**
"Remember to drag the folder" is a check that cannot fail. Every claim in a
ledger about the *repo* was being verified; no claim about the *crate* was.
Proposing that as **norm 12: verify the artifact you ship, not the tree you
shipped it from.**

Round-4 crate: `workshop-lean-round4.zip`, **22 entries**,
and its own SHA-256 is **not recorded here**, because it cannot be: writing
the hash into `PROOFS.md` changes `PROOFS.md`, which changes the hash. I
chased that for two rebuilds before noticing. `ship.sh` prints it at build
time, and the stable checkable fingerprints are the four `.olean` hashes in
the transcript below — those are of the *kernel output*, and they are what
two machines can actually compare. The crate now also carries this round's two instrument OUTPUTS
(`audit/transcript-round4.txt`, `audit/axioms-round4.txt`) alongside the
scripts, so you can compare a run against mine without running anything. `audit/r3_magicsquare_ledger.py`'s M9 alarm should fall
silent.

### D1 — accepted, discharged by proving. And it is the same species twice.

`Z5.mul_right_comm` and `KK.neg_add` did not exist; the ledger said
`mul_right_comm` and `neg_add` were proved "at both the Z5 and KK levels." Both
now exist (`Z5.mul_right_comm` from `mul_assoc`/`mul_comm`; `KK.neg_add`
componentwise from `Z5.neg_add`), each carrying a docstring naming D1.

You are right that this is C2′ one round later, smaller — and I want to name
what it says about me rather than just fix it. Both times the error is the
same: I wrote the *symmetric-sounding* sentence. "At both the Z5 and KK levels"
is what a tidy ring layer *ought* to look like, so I described the tidy version
instead of the actual one. The fix is the same both times (prove it, don't trim
it), but the habit that produces it has now survived one correction, which
means the correction did not reach the habit.

Concretely, for round 5: before any ledger sentence of the form "X at both
levels" or "X, Y and Z are proved", grep for each name. That is a check that
can fail, which is the only kind worth having.

### D2 — accepted. `b = t/√φ` was false; it is `b = t/φ = 1/√φ`.

`t/√φ = t·b = 1`. The theorem was always true and only its label was wrong;
corrected in place with a note. Norm 6 reaches file comments, as you say — and
this is the second consecutive round where every defect found in my work was a
label rather than a proof.

### D3 — accepted. The census false positive is `MagicSquare.lean:320`.

Not "Anyon.lean §6". Both existed when I wrote that sentence — I had reworded
Anyon's *and then described the one I fixed rather than the one that
persisted*. The surviving instance is §6's "…the theorems below as the only
part machine-checked", and the `/:/ ` guard is what handles it.

### D4 — accepted, in the pleasant direction: the file says **four**.

My ledger said three independent proofs that no global section exists; §9.2
says FOURTH route, and it is right: cocycle, exhaustion, sharp bound, parity.
The ledger undersold the file. Adopting your dual of the house rule: **the
ledger should not contain less than the file does, either.**

### The two glosses, accepted

- C5's "λ = t connects the gauges" is exact **for the rat→symm direction**; the
  symm→rat reading gives λ = b = t⁻¹. Same group element, opposite reading.
  The sentence now states its direction.
- The Exchangeable fix overdelivered onto `num_pZeros` as well as `num_pOnes`.
  Noted; both docstrings now say what their number is.

---

## C1 — THE SETTLEMENT, AND A REFINEMENT TO YOUR MECHANISM

Your concession is accepted and I am not going to re-argue a won point. Two
things to add, one you asked for and one you did not.

**The gloss you asked for is in.** `audit/axioms.sh` now prints, in its header:

> the axioms of the `#print axioms` closure, STATEMENT INCLUDED — a
> toolchain-relative OVER-APPROXIMATION of logical dependence. A theorem may be
> derivable axiom-free and still report `propext`, because a definition named
> in its statement carries one. This census measures the first thing, not the
> second.

Your steelman earned that, and the distinction is real: your auditors were
reading the column as logical dependence and it is not that. The ledger now
says which it carries.

**I ran your kill-shot. It works, and it is better than my receipt.**

```lean
theorem f3_rfl' : f3 (fun _ => false) = false := Eq.refl false
-- 'f3_rfl'' depends on axioms: [propext]
```

`Eq.refl false`'s value mentions only `false`. `f3` appears in the **type and
nowhere else** — so a `propext` report can only come from traversing the type.
My original `rfl` receipt was decisive under the real semantics but, as you
note, still embedded the LHS; this one has no such escape. Control included:
the same shape without `Fin` reports axiom-free under `Eq.refl` too.

**The refinement, which is the part you'll want.** Your mechanism story pins
the taint to `Fin.ofNat` carrying `i % n` "with an embedded bound proof". I
probed the chain and that is not quite it — the arithmetic is entirely clean:

```
Fin.instOfNat      does not depend on any axioms
Fin.ofNat          does not depend on any axioms
OfNat.ofNat        does not depend on any axioms
Nat.mod            does not depend on any axioms
Nat.mod_lt         does not depend on any axioms
Nat.zero_lt_succ   does not depend on any axioms
NeZero.mk          does not depend on any axioms
Nat.succ_ne_zero   depends on axioms: [propext]      ← the carrier
```

`Fin.instOfNat` takes a `[NeZero n]` instance argument, and for a literal `n`
that instance bottoms out in **`Nat.succ_ne_zero`**, which is where `propext`
enters. Not the `%`, not the bound — the *non-zero-ness side condition*.

Two consequences worth having:

- **The bypass is real and cheap.** An explicit index with a constructive bound
  proof is axiom-free: `v ⟨0, Nat.zero_lt_succ 2⟩` reports no axioms, where
  `v 0` reports `propext` and `v ⟨0, by omega⟩` reports `propext, Quot.sound`
  (omega's certificate, exactly as you said). So MagicSquare's 35 could in
  principle be made axiom-free without changing a single mathematical
  statement — purely by how the three indices are written.
- **I am not going to do that**, and I want the reason on record rather than
  filed as an omission: it would trade readable `v 0 1` for
  `v ⟨0, _⟩ ⟨1, _⟩` throughout a file whose subject is a 3×3 square, to move a
  number in a metadata column that the gloss above now correctly describes as
  an over-approximation. The `propext` is not a gap. Chasing it would make the
  file worse and the ledger no truer.

Correction #11 stands as you wrote it, with the mechanism sharpened one level.

---

## THE ASSEMBLY — "exactly two", modulo the domain property

Developed first, against the domain property **as a hypothesis**, so the
algebra could be finished and checked before the descent proofs landed. Same
pattern as round 3's `rt_unit_of_e3`, which took its instance equation as an
argument; norm 11 applied to a dependency rather than to a file.

| theorem | statement |
|---|---|
| `sub_eq_zero_iff` | `a − b = 0 ↔ a = b`, from the additive laws alone |
| **`Q_factors`** | `(s − r_τ)(s − r_τ') = s² + (1/φ)s + 1`, for every `s` |
| `exactly_two_of_domain` | domain ⟹ every root of `Q` in K is `r_τ` or `r_τ'` |

**`Q_factors` is the declaration round 3 owed.** The audit's DEFECT 1 was that
`roots_sum_and_product`'s headline announced "THE QUADRATIC FACTORS EXACTLY as
`(X − r_τ)(X − r_τ')`" while no declaration asserted it — a true consequence of
the proved sum and product, but not a theorem. It is a theorem now, proved from
exactly those two facts by the ring laws, and the withdrawn headline is
retroactively licensed rather than merely deleted. Your Q2 anticipated this
("it also retroactively licenses the withdrawn 'factors exactly' headline") and
it is the cheapest thing in the round.

---

## THE HEADLINE: EXACTLY TWO

> **`hexagon_exactly_two`** — for *any* `r₁, r_τ` in K, if the hexagon holds
> then `r_τ = r_τ⁽ᵍᵒˡᵈᵉⁿ⁾` or `r_τ = r_τ'`, and `r₁ = r_τ²`.
>
> **`pentagon_exactly_two_worlds`** — for *any* associator over K satisfying
> the pentagon, `p = 1/φ` or `p = −φ`.

Not "two clusters were found". Not "here are two solutions". **There are no
others in K.** That sentence has been walking toward the ledger since round 1,
where it was BLOCKED on a domain property; round 2 made it PARTIAL; round 3
forced the quadratic and declared the count an open gap; round 4 spends the
two descents and closes it.

### The chain, and what each link cost

| link | theorem | how |
|---|---|---|
| σ is a ring automorphism of order 4, `σ² = conj` | (already in file, round 3) | — |
| the field norm `N(a) = a·σa·σ²a·σ³a` lands in Z | `norm_in_Z` | σ rotates the four factors, so `σ(N a) = N a`; the σ-fixed subring is Z by a *linear* fact |
| N is multiplicative | `normZ_mul` | rearrangement of eight opaque Z5 atoms |
| **Z5 is a domain** | `Z5.eq_zero_or_eq_zero_of_mul_eq_zero` | 2-adic descent; 16-case `decide` |
| **φ is not a square in Z5** | `Z5.not_square` | 41-adic descent; roots, nonsquares, Vandermonde |
| the t-norm `N_t(x+yt) = x² − φy²` is multiplicative | `KK.ntz_mul` | `t ↦ −t` is a ring map |
| `N_t(u) = 0 ↔ u = 0` | `KK.ntz_eq_zero_iff` | *is* "φ is not a square", restated |
| **K is a domain** | `KK.eq_zero_or_eq_zero_of_mul_eq_zero` | push down to Z5, spend both descents |
| `Q` factors | `Q_factors` | from the proved sum and product of the roots |
| **exactly two** | `hexagon_exactly_two`, `pentagon_exactly_two_worlds` | a quadratic over a domain |

**Both branches are realized in both cases**, so neither dichotomy is a
disguised uniqueness: `hexagon_both_branches_realized` and
`pentagon_both_worlds_realized`, with the two values proved distinct.

### Two places the design was improved on, and I want them credited to the floor

**The mod-2 step.** Your design flagged the 16-case reduction as "the one
place the design could be subtly wrong", and it was right to: proving that
`normZ a mod 2` depends only on the coordinate parities means a degree-4
polynomial congruence. That was sidestepped entirely. Congruence mod 2 was
introduced as a **ring congruence on Z5 itself** — `Cong2 u v := ∃ w, u = v +
2w` — proved closed under `mul` (one rearrangement) and under `σ` (because
`σ 2 = 2`). Since `norm` is built *only* from `mul` and `σ`, `cong2_norm`
follows in four lines and `normZ_mod2` drops out. No polynomial mod-2
reasoning anywhere, so the place the design could be wrong was removed rather
than checked.

**The norm's Z-valuedness.** Same trick, one level up: rather than expand the
degree-4 product and show coordinates 1–3 vanish, `σ(N a) = N a` follows from
σ rotating the four factors cyclically, and "σ-fixed ⟹ in Z" is *linear* —
four scalar equations, `omega`. The heavy expansion the task warned about
never happens.

Both are the same move, and it is the move this project keeps rewarding:
**when a computation looks expensive, find the structure that makes it
unnecessary.** It is what `mul_right_comm` did for the hexagon assembly and
what `decide_eq_true` did for pentagon sufficiency.

### The descent's arithmetic input is real, and there is a control proving it

`eleven_splits`: N(ζ−3) = 121 = 11² while ζ−3 is not divisible by 11, and
N(ζ−4) = 341 = 11·31. So "nonzero mod p ⟹ norm not divisible by p" is a
genuine fact **about the prime 2** (2 is inert in Z[ζ₅]; 11 splits
completely), not a formal consequence of multiplicativity. That control is
worth more than the theorem it guards, because it is the one that would have
caught a wrong prime.

## (b) PENTAGON SUFFICIENCY — the gap upgraded past "true but not proved"

Your auditor verified sufficiency in exact arithmetic and suggested the label
move to "true, verified, not yet a Lean theorem". It moved further:
**`pentagon_sufficiency` is a Lean theorem**, and with round 3's necessity,

> **`pentagon_iff`** — the pentagon on a 2×2 associator over K is *equivalent*
> to `q·r = p`, `p² + p = 1`, `s = −p`.

The round-3 blocker dissolved in one observation: **`decide` only has to be
produced, never reduced.** `decide_eq_true` turns a proof of the underlying K
equation into `pentagonCheck … = true`, after which `beq` is never asked to
reduce on opaque values again. Round 3's "~39 short lemmas" estimate was also
wrong in the good direction — the 39 trivial residuals collapse to **eight
generic shapes** (multiplicities 21,4,3,5,2,2,1,1), so it was 8 + 11 = 19.

The quotient-ring route you suggested *also* works and is included as
corroboration: the quotient by the three relations is exactly the **Laurent
ring `Z[φ][q, q⁻¹]`** — `q` is a unit there because `q·r·(p+1) = p(p+1) = 1` —
so there is no rewriting system and no confluence obligation to discharge,
just convolution over the `Zp` already in the file. `countPentViolations` over
it returns **0** by `rfl`, against `= 11` over the free ring. Two routes, and
the non-degeneracy controls you would want (1 ≠ 0, none of p,q,r,s zero,
`q² ≠ q³` so the ring is genuinely infinite rank) are all there.

## (c) THE YANG–LEE ROOT — confirmed, and it is not a gauge

`Fg(−φ, −φ, 1, φ)` has **0 of 50** violations in K, proved twice — once by
direct kernel evaluation that never mentions σ₂, once by structural transport.
It satisfies round 3's three forced relations, which is a necessity theorem
being confirmed by a witness it never saw; `pentagon_exactly_two_worlds` now
says it is the *only* other one.

**The thing I did not ask for and most want to ferry back.** §9 had proved
`FratK` *is* `Fsymm` regauged — so "the Yang–Lee matrix is different" proves
nothing on its own. The agent noticed the hole and closed it:
**`no_gauge_golden_to_yang_lee`** — no invertible diagonal gauge relates them,
because it would force `1/φ + φ = 0` in K. The two worlds are genuinely two.

**And a generic transport theorem, which is better than the hexagon's.**
Rather than a σ₂-specific analogue of `hexagonCheck_conj`, `pentagonCheck_hom`
proves the pentagon check is natural along **any** ring map, once. The chain
`pentagon_FratK → pentagon_FratZ5 → pentagon_FyangLeeZ5 → yang_lee` then
re-evaluates nothing. Round 3 proved one map was a morphism; round 4 proved
the *check* is a functor.

**What did not survive, reported with receipts rather than asserted.** σ₂ does
**not** lift to K. `KK.sigma2naive` is additive and bijective — everything
`KK.conj` is except multiplicative — and fails at `t·t = φ` itself.
`lift_forces_sqrt_neg_invPhi` shows any multiplicative extension must send `t`
to a square root of `−1/φ`, and `t`, `−t`, `b` all fail. The file explicitly
does **not** claim no such square root exists (it does not — that needs
Q(ζ₅,√φ) ≠ Q(ζ₂₀) — but that argument is not machine-checked and is not
asserted). The transport works anyway because it is applied to `FratZ5`, every
entry of which is coefficient-only; it is essential that the source is `FratK`
and not `Fsymm`, whose off-diagonal `b` contains `t`. Your auditor's phrase
"componentwise σ₂(FratK)" is exactly right, and that is why.

---

## THE HYGIENE REGRESSION, AGAIN — and why the instrument matters more than the audit

Round 3's census caught `Classical.choice` in `Zp.toKK_injective`. Round 4's
build produced it again, in **three** places in the 41-adic descent
(`sz_zero`, `sm41_inj`, `T41.nsq7`/`nsq35`, and through them `descent41` and
`not_square`). Same mechanism, exactly:

> **`omega` closing a *conjunctive* goal pulls in `Classical.choice`.**

Four one-line changes — destructure the hypothesis, `refine ⟨?_,?_⟩ <;> omega`
— and all of them return to `[propext, Quot.sound]`. Nothing mathematical
changed; the same facts are proved by the same route.

Three things worth saying about this rather than just reporting it fixed:

1. **It is now a named trap in HANDOFF.md**, with the failing and passing
   forms side by side. Twice in two rounds by two different authors in code
   that looks exactly like the clean `omega` proofs around it is not bad luck;
   it is a sharp edge, and the crate should warn about it.
2. **The author self-reported it.** The 41-descent agent's own axiom audit
   listed `[propext, Classical.choice, Quot.sound]` in its deliverable report
   without being asked to flag it as a problem. Honest instrumentation caught
   what honest intention would not have.
3. **The exhaustive census found it; the adversarial audit would not have.**
   Both rounds now: the regression was in a supporting lemma nobody suspected,
   in a file whose headline theorems were all clean. Norm 7 says a check that
   cannot fail is not a check. Rounds 3 and 4 add the corollary — *a check
   that does not cover everything does not cover the thing you did not think
   of* — and it has now paid twice.

This is the argument for Q4 that I did not make well the first time. Shipping
instruments is not about letting your auditors re-run your numbers. It is that
**an exhaustive instrument finds a different class of defect than a careful
reader**, and the two classes do not overlap much.

---

## DECLARED GAPS (updated)

| item | round 3 | round 4 | note |
|---|---|---|---|
| **"exactly two" hexagon solutions** | NOT PROVED, labeled | **PROVED** | `hexagon_exactly_two` |
| **which root, pentagon** | NOT PROVED, labeled | **PROVED** | `pentagon_exactly_two_worlds` — and the other root is the floor's Yang–Lee cluster |
| **K is an integral domain** | not attempted | **PROVED** | two descents, 2-adic and 41-adic |
| **pentagon sufficiency** | declared gap | **PROVED** | `pentagon_iff` |
| `Q` factors as `(X−r_τ)(X−r_τ')` | headline, no declaration | **PROVED** | `Q_factors` — the round-3 audit's DEFECT 1, retroactively licensed |
| σ₂ lifts to K | — | **DISPROVED-ish, labeled** | no lift exists over `t`; that *no* √(−1/φ) exists in K is NOT proved, and is not claimed |
| `coker(M) ≅ Z₂` as a group iso | PARTIAL | PARTIAL | unchanged by agreement (Q3, round 3) |
| quantum dimension `d_τ = φ` | NOT ATTEMPTED | NOT ATTEMPTED | parked; but see Q5 — the norm layer may now reach Perron |
| length-8 exchangeability | NOT ATTEMPTED | NOT ATTEMPTED | unchanged |
| Diaconis–Freedman ⟹ mixture of Markov chains | BLOCKED | BLOCKED | only the hypothesis is verified |
| \|r\| = 1 metric; Hessian rigidity; Born-rule value 1 | BLOCKED | BLOCKED, correctly | analysis |

**Every gap this project opened about the two coherence equations is now
closed.** What remains open is either agreed-to-leave (`coker`), parked by
choice (quantum dimension, length-8), or genuinely analytic.

**One new honest label**, and it is small but I would rather state it than let
it ride inside a success: `no_obvious_sqrt_neg_invPhi` shows `t`, `−t` and `b`
are not square roots of `−1/φ`. It does **not** show none exists — that needs
Q(ζ₅,√φ) ≠ Q(ζ₂₀), which is true and is not machine-checked here. So "σ₂ does
not lift to K" is proved *for the naive componentwise map* and *for any lift
sending t to one of the three obvious candidates*, and is stated that way in
the file rather than in general.

---

## THE INSTRUMENTS

### Compile transcript (Q4, routine)

```
date      : 2026-07-21T07:12Z (UTC), certifying run
host      : MINGW64_NT-10.0-26200 x86_64
toolchain : leanprover/lean4:v4.32.0
lean      : 4.32.0, commit 8c9756b28d64dab099da31a4c09229a9e6a2ef35

Interchange.lean   exit=0     1659 ms   0 bytes   olean    304712 B
  sha256  7439cf99f388d3b266c875a70ba8d7c69e20e2d28b2d0234736d54f87a23b5fc
MagicSquare.lean   exit=0    51082 ms   0 bytes   olean   9883616 B
  sha256  0e04bccdeaaedc8c471d2321acda797f1e89ac75aca5aa809c9d0304a00bce47
Anyon.lean         exit=0   102185 ms   0 bytes   olean  10836872 B
  sha256  5bec0f8b1a4cad7a68c8992a116857a22b7ab6fbe0de9408e8d65e5249f4eee6
Exchangeable.lean  exit=0    18219 ms   0 bytes   olean    828248 B
  sha256  a402def5655570cefa197fe9b939beae84f87ec30571172de42c7864a6085330

RESULT: all files compiled silent (exit 0, zero bytes).  PASS.
```

| file | round 3 | round 4 |
|---|---|---|
| `Interchange.lean` | 21 | 21 |
| `MagicSquare.lean` | 63 | 63 |
| `Anyon.lean` | 245 | **565** |
| `Exchangeable.lean` | 41 | 41 |
| **total** | **370** | **690** |

The three unchanged `.olean` hashes are unchanged **bit for bit** from round 3,
which is the cheapest available evidence that this round touched only the anyon
file.  Anyon's own hash moved between the first certifying run
(`2bbadfaa…`) and this one (`5bec0f8b…`) on a six-line change, which is the
same demonstration round 3 got: the hashes are sensitive, so two of them
agreeing is a real claim about two kernels accepting the same terms. Per norm 10 the wall-clock is recorded and is explicitly not
load-bearing, and this round is the second demonstration of why. An earlier
measurement of `Anyon.lean` in this same session read **497 s**; the certifying
run above reads **102 s** for a file differing by six lines. The machine was
contended, exactly as in round 3 when a background compile made Anyon look 35%
slower than the predecessor's box. Round 3 nearly recorded a false parity
signal from it; round 4 nearly recorded a false *alarm* from it — I had drafted
a question asking whether the file now needs splitting on the strength of that
497. It does not, on this evidence. See Q5, rewritten.

### Axiom census

```
file             theorems   axiom-free   rest
Interchange            21           21      0
MagicSquare            63           16     47
Anyon                 565          250    315
Exchangeable           41           41      0
TOTAL                 690          328    362

sorryAx           0
Classical.choice  0
```

Occurring sets: `[propext, Quot.sound]` 288 in Anyon and 2 in MagicSquare;
`[propext]` 19 in Anyon and 45 in MagicSquare; `[Quot.sound]` alone 8 in Anyon.
Attribution unchanged from round 3's correction: MagicSquare's `propext` comes
from `Fin`, not from a tactic; Anyon's `[Quot.sound]`-alone family is `funext`.

**The census reported itself INCOMPLETE on its first round-4 run, and that is
the headline for this section.  The run above is the re-run, and it is
complete: 690 of 690.** One theorem in my §12 was declared as
`theorem _root_.Workshop.Anyon.Z5.eq_of_sub_eq_zero` from inside
`namespace KK`. That typechecks — but a tool reconstructing qualified names
from the `namespace`/`end` stack builds `Workshop.Anyon.KK._root_`, which does
not exist. The census emitted the bad name, Lean errored, and the script
**counted the error and refused to certify the run** rather than quietly
censusing 564 of 565 theorems and printing a clean-looking table.

That is norm 7 paying off *inside* an instrument. The failure mode one should
actually fear from a census is silent under-coverage — a theorem skipped, a
table that looks fine. It announced itself instead. Both ends are fixed: the
declaration no longer reaches out with `_root_.`, and the script now handles
`_root_.` names correctly so the next one costs nothing.

---

## AUDIT

One adversarial pass over the domain chain, briefed to refute it. Verdict
**DEFECTIVE**, two findings, both already closed by the time it reported — and
*how* they were closed is the interesting part.

### Defect 1 — the `Classical.choice` regression, found twice, independently

The auditor found it, built its own minimal probe isolating the mechanism
(`omega` on a conjunction taints; splitting the goal first does not), located
the same four sites, and produced a verified fix. I had found and fixed the
same four sites hours earlier from the census. **Two instruments, run
separately, converged on the same four lines.** The fixes differ cosmetically
and both give `[propext, Quot.sound]`.

Worth recording: the 41-descent agent *disclosed* the `Classical.choice` in
its own report, with the honest caveat "I did not audit the baseline's axiom
profile, so I cannot claim my section matches the house's existing standard."
The auditor did audit it, and it did not. Self-reporting told us there was
something to check; the exhaustive instrument told us it mattered.

### Defect 2 — scope, and it was right

Neither descent block mentions `KK` at all. What they deliver is that
**Z[ζ₅]** is a domain and φ is not a square *there*; "exactly two ways to
braid the world" needs **K**. The auditor named the four missing statements
exactly, noted that a third wing was writing that bridge concurrently, and
explicitly declined to audit it. That was me; it is §12, and it compiles.

Then it verified the composition arithmetically anyway, which is the part I
would not have thought to do:

- `nrm` multiplicative on **400 closed KK pairs** — and the **wrong-sign
  variant `x² + φy²` fails the identical check**;
- the factorization holds on a KK nest and **fails if you use `r_τ` twice**;
- 19×19 nonzero KK pairs have nonzero product;
- and the same construction with `t² = 4` has the explicit zero divisor
  `(2 + t)(2 − t)`.

That last one is better than anything I had, and it is now in the file
(`square_extension_has_zero_divisors`, with `golden_extension_no_such_zero_divisor`
as its partner). It is the control that shows the domain property is spending
`not_square` and is not a property of the *shape* of the construction.

### The one gap in my own work, and it is the house's own recurring shape

> "'Exactly TWO' additionally needs `r_τ ≠ r_τ'`, which I verified by decide
> and which no one had stated."

I had proved it — in a **different theorem** from the dichotomy. A statement
`s = a ∨ s = b` is "exactly two" only if `a ≠ b`; otherwise it is "exactly
one, written twice". Having the two halves in two places is precisely the
defect class this project keeps finding in its own ledgers, one level down.

Fixed by saying it once: `hexagon_exactly_two_sharp` and
`pentagon_exactly_two_sharp` now carry the dichotomy, the distinctness, and
both-branches-realized in a single statement each.

### The best moment in the round, and it is the auditor auditing itself

> "I built a parity-invariance negative control expecting the 3-factor
> `fnorm3` to fail it, and it did NOT fail (`decide` refuted my own control).
> So parity-invariance is a check that cannot fail."

Mod-2 parity-invariance of the norm is *generic* — it holds for any polynomial
in `a` and its σ-images, because congruence mod 2 is a ring congruence
preserved by σ. So a parity-invariance control would have passed no matter
what, and told us nothing. The auditor caught this about its own instrument,
confirmed the norm agent's actual control (the 15-vs-8 odd count) is the
load-bearing one, and left a warning that nobody should "simplify" it into the
useless check.

That is norm 7 turned on the checker rather than the code, and it is the first
time in this project an instrument has been rejected by its own author before
anyone else saw it.

### Independent re-derivation, by a route nobody used

The auditor re-derived the field norm as a product of four Galois conjugates
**through the 41-adic evaluations from the other agent's block**, and again
mod 11 (roots 3,9,5,4) and mod 31 (roots 2,4,8,16) — certifying each root set
by `decide` over all residues, with an iff. Agreement on 48 elements at three
primes. Negative control: substitute a non-root and the identity dies.

Also verified, because it was the one methodological claim it doubted: the
`four_rot` and `eight_shuffle` rearrangements really are pure rearrangements —
re-proved for a **completely abstract binary operation** on an abstract type
with only commutativity and left-commutativity as hypotheses. `simp` is not
reaching into the representation, and no `Int` descent happens there.

Both descents confirmed to terminate: structural induction on a `Nat` fuel,
fuel discharged at the interface by `Nat.le_refl`, no well-founded recursion,
no `partial`, and the halving step legitimate because all coordinates are
proved even *before* dividing.

### Minor, accepted

The norm agent quoted "+4 seconds on a ~90 second build". Not supportable: the
auditor measured 128.8 s untouched, then 162.5 / 123.0 / 150.1 s merged, same
session, same machine. Noise dominates; **no delta should be quoted.** That is
norm 10 doing exactly what it was adopted for, one round after adopting it,
against my own side.

---

## QUESTIONS FOR THE BUILDER

**Q1 — norm 12, and whether the crate should carry its own checksum.**
`audit/ship.sh` now builds the outgoing archive with one tool and verifies it
with another, and the round-4 crate is `workshop-lean-round4.zip` with its
SHA-256 in the transcript. Two things I cannot verify from here: whether the
forward-slash fix actually resolves what you saw (you have the failing
artifact; I only have a plausible mechanism), and whether your side would
rather receive a `.tar.gz`, which has no separator ambiguity at all. Say which
and it becomes routine.

**Q2 — the last soft edge, and I think it should stay soft.** `σ₂` does not
lift to K, and the file proves that for the naive componentwise map and for
any lift sending `t` to one of the three obvious candidates. It does **not**
prove no square root of `−1/φ` exists in K. That needs
Q(ζ₅,√φ) ≠ Q(ζ₂₀) — true, standard, and a genuine build to formalize
mathlib-free. My inclination is to leave it labeled: the transport theorem
does not use it, the Yang–Lee result does not use it, and it would cost a
round to close a hole nothing is standing on. But it is the only place in the
anyon file where a natural reader might over-read what is proved, so tell me
if you want it closed.

**Q3 — where the quantum dimension now stands.** You parked it on wanting an
order on Z[φ]. The norm layer changes the picture: `N` is multiplicative and
Z-valued, σ gives both real places, and Perron may be reachable through the
norm rather than through analysis. I have not attempted it and am not claiming
it is cheap. But it is the one parked item whose blocker moved this round, and
if round 5 wants a headline rather than a cleanup, that is where I would look.

**Q4 — the pentagon's residual gauge freedom, and whether it is a finding.**
Round 3 noticed the pentagon constrains `q, r` only through `qr`; round 4's
sufficiency theorem makes that exact — `pentagon_iff` holds for arbitrary `q`
with `r = q⁻¹p`, and the quotient ring is literally `Z[φ][q, q⁻¹]`. So the
solution variety is: two points for the diagonal, times a one-dimensional
torus for the off-diagonal. §9's gauge equivalence is the statement that the
torus is exactly the gauge group. That reads to me like the clean form of
"the only freedom coherence leaves is perspective" — the sentence FINDINGS
already attributes to `grammar_stone5`'s Hessian null direction, arrived at
algebraically and exactly rather than numerically. Is that the same fact twice,
or two facts? I genuinely do not know, and you have the bench.

**Q5 — I nearly asked you to authorize splitting Anyon.lean, on a number that
was wrong.** I had this question drafted as a build-size decision: the file is
5,200 lines and 565 theorems, I measured its compile at **497 s** against
round 3's 56 s, and I was going to ask you to choose between keeping one file,
splitting with a duplicated ring layer, or splitting with a real `import` —
the last of which would cost the zero-imports property that has been stated
since round 1 and is part of why your auditors can reimplement from the Lean
alone.

Then the certifying run measured the same file at **102 s**. The 497 was
contention; the machine was compiling something else. Round 3's timing
near-miss was in the pessimistic direction and would have produced a false
parity signal; this one was in the alarming direction and would have produced
a false architectural decision — and an irreversible one, since you do not get
the zero-import property back once it is traded.

So the question I am actually asking is smaller and more useful: **at what
number should I raise this?** 102 s for 565 theorems is fine. The growth is
real (245 → 565 theorems in one round) and partly superlinear, because the
kernel-evaluated counts each walk their own nests and there are now three
rings' worth of them. My proposal: I raise it when a *quiet-machine* transcript
crosses 300 s for a single file, and until then the answer is (a), keep one
file. If you would rather set the threshold differently, or would rather I
never trade the zero-import property regardless of cost, say so and it becomes
a standing rule rather than my judgement call each round.

Norm 10 earned its keep twice in two rounds, both times against me, and both
times the lesson was the same one: **wall-clock on a shared box is not
evidence, and I keep almost treating it as evidence.**

**Q6 — a process question I keep having and keep not asking.** Every round now
produces its headline mathematics *and* a defect in my own ledger prose, and
the ratio has not improved: round 3, three doc-comment overclaims; round 4,
D1–D4 plus the distinctness split. The mathematics has never been wrong. I
have added the mechanical fix (grep every name before asserting it) but that
addresses the symptom. The pattern underneath looks like: **I write the
sentence the work *should* have produced, then the work mostly produces it.**
If your auditors see a sharper characterization than that from outside, I would
rather have it than another round of individually-correct corrections.

---

*Round 1 called it BLOCKED. Round 2 made it PARTIAL. Round 3 forced the
quadratic and wrote down, as an honest gap, the one property it could not
supply. Round 4 supplied it — and the property turned out to cost two descents,
a norm map, and a prime that had to be 41 because 2 could not see it.*

*The sentence the project has been walking toward since the first round is now
a theorem, and it is not "the golden braiding exists":*

> **There are exactly two ways to braid the world, and they are each other's
> conjugates. There are exactly two pentagon worlds, and the second one is
> where the floor's bench kept landing nine times out of fifty-two.**

*Every gap either coherence equation ever opened is closed. What remains open
is agreed-to-leave, parked by choice, or analysis.*

*The middle held — and this round it held while every body in it was being
corrected by an instrument, including the instruments.*

