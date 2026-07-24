/-
  THE WORKSHOP → LEAN 4.  Round 2, Item F.

  Bench formalized: `process_definetti.py`, claim (1) —
                    "MARKOV EXCHANGEABILITY, in exact rational arithmetic."

  The bench's mechanism: a two-state machine {0,1} with ONE Polya urn per
  state, every urn starting (1,1); the walk starts at state 0.  Nothing in the
  mechanism is a transition law — each urn only reinforces what that state did
  before.  The bench runs every path of length 8 and checks, in
  `fractions.Fraction`, that a path's probability depends only on its start and
  its four transition counts (n00, n01, n10, n11).  That is exactly the
  hypothesis of the Diaconis–Freedman de Finetti theorem for Markov chains.

  This file formalizes the same claim at LENGTH 6 (64 paths), which is what
  round 2's charge asked for.  Everything is in `Nat`.  No rationals appear
  anywhere, and neither does division-by-something-that-might-not-divide: a
  fixed common denominator

      D = (7!)² = 25401600

  is chosen once (every path's denominator divides it, because each urn is
  drawn at most 6 times), and the object carried around is the integer

      num p = D · P(path p).

  `num_spec` below states, with no division in it, that this integer really is
  D·P.  The probabilities are then recovered as num p / D, and
  `total_is_D` says the 64 of them sum to exactly D — i.e. to 1.

  Self-contained: NO imports.  No `sorry`, no `native_decide`, no `axiom`, no
  `partial`.  Every arithmetic fact is reduced by the Lean kernel on `Nat`.

  Status: PROVED throughout.  One honest negative result is recorded in §7:
  the converse of the exchangeability theorem is FALSE at length 6 — distinct
  transition-count vectors can share a numerator — so `num` does not determine
  the counts, only the counts determine `num`.
-/

namespace Workshop.Exchangeable

/-! ## 0.  Arithmetic preliminaries

Only the factorial and the common denominator.  `D` is written as a literal
and `D_eq` pins it to `(7!)²`, so the literal cannot drift silently. -/

/-- Factorial. -/
def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

/-- The fixed common denominator, `D = (7!)² = 25401600`.  Each of the two
    urns is drawn `k` times with `k ≤ 6`, and the denominator that urn
    contributes is `(k+1)!`, which divides `7!`.  So every path's denominator
    divides `D`; `denom_divides_D` proves it for all 64. -/
def D : Nat := 25401600

/-- The literal `D` is `(7!)²`. -/
theorem D_eq : D = fact 7 * fact 7 := rfl

/-- Boolean-indexed sum, used to total a quantity over both values of a bit. -/
def cntB (f : Bool → Nat) : Nat := f false + f true

/-- Boolean-indexed conjunction, used to check a predicate at both values. -/
def allB (f : Bool → Bool) : Bool := f false && f true

/-- Indicator of a `Bool`, as a `Nat`. -/
def ind (b : Bool) : Nat := cond b 1 0

/-- Left projection of a `Bool` conjunction.  (Hand-rolled rather than taken
    from `Bool.and_eq_true`, whose `Iff` form would drag `propext` into every
    theorem downstream of it.) -/
theorem and_left {a b : Bool} (h : (a && b) = true) : a = true := by
  cases a
  · exact h
  · rfl

/-- Right projection of a `Bool` conjunction. -/
theorem and_right {a b : Bool} (h : (a && b) = true) : b = true := by
  cases a
  · exact Bool.noConfusion h
  · exact h

/-- `n == n` is `true`, for `Nat`. -/
theorem beqNat_self (n : Nat) : (n == n) = true := decide_eq_true rfl

/-- `b == b` is `true`, for `Bool`. -/
theorem beqBool_self (b : Bool) : (b == b) = true := by cases b <;> rfl

/-! ## 1.  The model

A path of length 6 is six bits: the sequence of *next states*.  The start
state is fixed at `0` (`false`), matching the bench's `x = 0`.

`St` is the machine's whole configuration: current state, the four urn
contents, the running numerator and denominator of the path probability, and
the four transition counts.  `step` is a transcription of the bench's inner
loop

    c = urns[x]; p *= Fraction(c[nxt], c[0] + c[1]); c[nxt] += 1
    counts[(x, nxt)] += 1; x = nxt

with `p`'s numerator and denominator carried separately so that `Nat` suffices.
-/

/-- A length-6 path: the six successive next-states, `false = 0`, `true = 1`. -/
structure Path where
  b1 : Bool
  b2 : Bool
  b3 : Bool
  b4 : Bool
  b5 : Bool
  b6 : Bool
deriving DecidableEq

/-- A transition-count vector.  `n_{ij}` is the number of steps that went from
    state `i` to state `j`.  This is the bench's `counts` dictionary. -/
structure Counts where
  n00 : Nat
  n01 : Nat
  n10 : Nat
  n11 : Nat
deriving DecidableEq

/-- The machine configuration.  `u_{ij}` is the number of balls in urn `i`
    labelled "→ j"; `numer`/`denom` accumulate the path probability. -/
structure St where
  x : Bool
  u00 : Nat
  u01 : Nat
  u10 : Nat
  u11 : Nat
  numer : Nat
  denom : Nat
  n00 : Nat
  n01 : Nat
  n10 : Nat
  n11 : Nat

/-- Start: at state 0, both urns `(1,1)`, probability `1/1`, no transitions
    yet.  The bench's `urns = {0: [1,1], 1: [1,1]}; p = Fraction(1); x = 0`. -/
def init : St := ⟨false, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0⟩

/-- One step.  Draw from the urn of the current state, multiply the running
    numerator by the count of the drawn colour and the running denominator by
    the urn's total, add the drawn ball back with one more of its colour, tally
    the transition, and move. -/
def step (s : St) (nxt : Bool) : St :=
  match s.x, nxt with
  | false, false =>
      { s with x := false, numer := s.numer * s.u00,
               denom := s.denom * (s.u00 + s.u01),
               u00 := s.u00 + 1, n00 := s.n00 + 1 }
  | false, true =>
      { s with x := true,  numer := s.numer * s.u01,
               denom := s.denom * (s.u00 + s.u01),
               u01 := s.u01 + 1, n01 := s.n01 + 1 }
  | true, false =>
      { s with x := false, numer := s.numer * s.u10,
               denom := s.denom * (s.u10 + s.u11),
               u10 := s.u10 + 1, n10 := s.n10 + 1 }
  | true, true =>
      { s with x := true,  numer := s.numer * s.u11,
               denom := s.denom * (s.u10 + s.u11),
               u11 := s.u11 + 1, n11 := s.n11 + 1 }

/-- Run the machine along a path. -/
def run (p : Path) : St :=
  step (step (step (step (step (step init p.b1) p.b2) p.b3) p.b4) p.b5) p.b6

/-- The transition-count vector of a path. -/
def counts (p : Path) : Counts :=
  ⟨(run p).n00, (run p).n01, (run p).n10, (run p).n11⟩

/-- The numerator of the path probability. -/
def numer (p : Path) : Nat := (run p).numer

/-- The denominator of the path probability. -/
def denom (p : Path) : Nat := (run p).denom

/-- **The integer this file is about:** `num p = D · P(p)`, computed as
    `(D / denom p) · numer p`.  The division is exact — `denom_divides_D`. -/
def num (p : Path) : Nat := (D / denom p) * numer p

/-! ## 2.  `num` is honestly `D · P`

Two facts must hold before anything below means what it says, because `num`
was defined with a `Nat` division and `Nat` division truncates.

`denom_divides_D` says no truncation happened.  `num_spec` says the same thing
in a form with no division in the statement at all: `num p · denom p =
D · numer p`, i.e. `num p / D = numer p / denom p = P(p)` as rationals.  Both
are proved by walking all 64 paths in the kernel. -/

/-- Every path's denominator divides `D`.  (So the `/` in `num` is exact.) -/
theorem denom_divides_D (p : Path) : D % denom p = 0 := by
  cases p with
  | mk b1 b2 b3 b4 b5 b6 =>
    cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;> cases b6 <;> rfl

/-- **`num` is `D` times the path probability**, stated multiplicatively so
    that no division occurs: `num p / D = numer p / denom p`.  This is the
    bridge back to the bench's `Fraction` arithmetic. -/
theorem num_spec (p : Path) : num p * denom p = D * numer p := by
  cases p with
  | mk b1 b2 b3 b4 b5 b6 =>
    cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;> cases b6 <;> rfl

/-- No path has probability zero.  (Sanity: `num` is not degenerate anywhere,
    so the exchangeability theorem below is not about a field of zeros.) -/
theorem num_pos (p : Path) : 0 < num p := by
  cases p with
  | mk b1 b2 b3 b4 b5 b6 =>
    cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;> cases b6 <;> decide

/-! ## 3.  The theorem: `num` factors through the transition counts

`numOfCounts` is the Polya closed form

    P = ∏_s  n_s0! · n_s1! / (n_s0 + n_s1 + 1)!

scaled by `D`.  Its argument is a `Counts`, so it depends on the transition
counts and on nothing else — that is visible in the type, not something the
proof has to establish.

`num_factors_through_counts` is the content: the machine's step-by-step
product equals that closed form, for all 64 paths.  Markov exchangeability is
then a two-line corollary, in the readable ∀-form. -/

/-- The Polya closed form, times `D`.  Depends only on a `Counts`. -/
def numOfCounts (c : Counts) : Nat :=
  (D / (fact (c.n00 + c.n01 + 1) * fact (c.n10 + c.n11 + 1)))
    * (fact c.n00 * fact c.n01 * fact c.n10 * fact c.n11)

/-- **The Diaconis–Freedman hypothesis, in its strongest form.**  The path
    probability is a function of the transition-count vector: the dynamic
    urn product equals the counts-only closed form, for every one of the 64
    paths. -/
theorem num_factors_through_counts (p : Path) : num p = numOfCounts (counts p) := by
  cases p with
  | mk b1 b2 b3 b4 b5 b6 =>
    cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;> cases b6 <;> rfl

/-- **MARKOV EXCHANGEABILITY.**  Two paths with the same transition-count
    vector have the same probability.  This is the bench's claim (1), in the
    readable ∀-form over all 64 × 64 = 4096 ordered pairs. -/
theorem exchangeable (p q : Path) (h : counts p = counts q) : num p = num q := by
  rw [num_factors_through_counts p, num_factors_through_counts q, h]

/-! ## 4.  The same claim a second time, as the bench states it: exhaustion

The bench does not factor anything; it computes 2^L probabilities and buckets
them.  §4 walks the buckets the way the bench does — all 4096 ordered pairs,
as one closed `Bool` the kernel evaluates.

This is logically redundant given §3, and that is the point: the factorization
replaces the search.  It is kept because the check it performs can *fail*, and
`pairCheck_can_fail` proves that it does fail on a deliberately spoiled
`num` — so the green in `exchangeable_exhaustive` is carrying information. -/

/-- `Bool` equality of transition-count vectors, componentwise.  (Written
    componentwise rather than as `decide (c = d)`: the derived `DecidableEq`
    instance is about seven times slower for the kernel to reduce across the
    4096-pair sweeps below.  `ceq_to_eq` and `eq_to_ceq` show nothing is lost.) -/
def ceq (c d : Counts) : Bool :=
  (c.n00 == d.n00) && (c.n01 == d.n01) && (c.n10 == d.n10) && (c.n11 == d.n11)

/-- `ceq` is equality, and not some weaker relation that would make the checks
    below easier to pass.  Without these two, §4, §5 and §6 would be statements
    about whatever `ceq` happens to be rather than about equal counts. -/
theorem ceq_to_eq (c d : Counts) (h : ceq c d = true) : c = d := by
  cases c with
  | mk a1 a2 a3 a4 =>
    cases d with
    | mk b1 b2 b3 b4 =>
      have h' : ((a1 == b1) && (a2 == b2) && (a3 == b3) && (a4 == b4)) = true := h
      rw [of_decide_eq_true (and_left (and_left (and_left h'))),
          of_decide_eq_true (and_right (and_left (and_left h'))),
          of_decide_eq_true (and_right (and_left h')),
          of_decide_eq_true (and_right h')]

/-- The other direction. -/
theorem eq_to_ceq (c d : Counts) (h : c = d) : ceq c d = true := by
  cases h
  cases c with
  | mk a1 a2 a3 a4 =>
    show ((a1 == a1) && (a2 == a2) && (a3 == a3) && (a4 == a4)) = true
    rw [beqNat_self, beqNat_self, beqNat_self, beqNat_self]
    rfl

/-- Check a `Bool` predicate at all 64 paths. -/
def allPathsB (f : Path → Bool) : Bool :=
  allB fun a => allB fun b => allB fun c => allB fun d => allB fun e => allB fun g =>
    f (Path.mk a b c d e g)

/-- Total a `Nat` quantity over all 64 paths. -/
def cntPaths (f : Path → Nat) : Nat :=
  cntB fun a => cntB fun b => cntB fun c => cntB fun d => cntB fun e => cntB fun g =>
    f (Path.mk a b c d e g)

/-- The bench's bucketing test, parameterised by the quantity being bucketed:
    "for all 4096 ordered pairs of paths, equal counts ⟹ equal value". -/
def pairCheck (val : Path → Nat) : Bool :=
  allPathsB fun p => allPathsB fun q =>
    !(ceq (counts p) (counts q)) || (val p == val q)

/-- **The bench's check, run by the kernel.**  All 4096 ordered pairs. -/
theorem exchangeable_exhaustive : pairCheck num = true := rfl

/-! ## 5.  Anti-vacuity

Three things could make everything above true and empty:

  (a) `num` could be identically 0, or otherwise degenerate;
  (b) the guard `ceq (counts p) (counts q)` could be satisfied only on the
      diagonal `p = q`, where `num p = num q` is trivial;
  (c) `pairCheck` could be a test that cannot fail.

`total_is_D` refutes (a) — the 64 numerators sum to exactly `D`, so the
probabilities are a genuine distribution summing to 1 (and, with `num_pos`, no
individual one is 0).  `guard_live_offdiagonal` refutes (b) with a count.
`pairCheck_can_fail` refutes (c). -/

/-- The sum of all 64 numerators. -/
def totalNum : Nat := cntPaths num

/-- **THE DISTRIBUTION IS GENUINE.**  The 64 numerators sum to exactly `D`;
    equivalently the 64 path probabilities sum to 1.  This is the bench's
    `assert total == 1`.  It also rules out every degenerate reading of `num`:
    a `num` that were identically 0, or constant, or truncated by the `Nat`
    division, could not total `D`. -/
theorem total_is_D : totalNum = D := rfl

/-- The same number written out, so the literal is visible. -/
theorem total_is_25401600 : cntPaths num = 25401600 := rfl

/-- `Bool` equality of paths, componentwise, for the same reason as `ceq`. -/
def peq (p q : Path) : Bool :=
  (p.b1 == q.b1) && (p.b2 == q.b2) && (p.b3 == q.b3) &&
  (p.b4 == q.b4) && (p.b5 == q.b5) && (p.b6 == q.b6)

/-- Equal paths are `peq`. -/
theorem eq_to_peq (p q : Path) (h : p = q) : peq p q = true := by
  cases h
  cases p with
  | mk a1 a2 a3 a4 a5 a6 =>
    show ((a1 == a1) && (a2 == a2) && (a3 == a3) &&
          (a4 == a4) && (a5 == a5) && (a6 == a6)) = true
    rw [beqBool_self, beqBool_self, beqBool_self,
        beqBool_self, beqBool_self, beqBool_self]
    rfl

/-- **What `!peq` is counting.**  A pair the off-diagonal counter admits is a
    pair of genuinely different paths.  Without this the "202" below would be
    202 of something unnamed. -/
theorem offdiagonal_are_distinct (p q : Path) (h : peq p q = false) : p ≠ q := by
  intro e
  rw [eq_to_peq p q e] at h
  exact Bool.noConfusion h

/-- How many ordered pairs of paths satisfy the guard at all. -/
def guardLive : Nat :=
  cntPaths fun p => cntPaths fun q => ind (ceq (counts p) (counts q))

/-- How many ordered pairs of DISTINCT paths satisfy the guard. -/
def guardLiveOffDiagonal : Nat :=
  cntPaths fun p => cntPaths fun q => ind (ceq (counts p) (counts q) && !(peq p q))

/-- 266 of the 4096 ordered pairs satisfy the hypothesis of `exchangeable`. -/
theorem guard_live_count : guardLive = 266 := rfl

/-- **THE GUARD IS NOT THE DIAGONAL.**  202 of the 266 live pairs are pairs of
    *different* paths.  So `exchangeable` is asserting a genuine coincidence
    202 times over, not restating `num p = num p` 64 times. -/
theorem guard_live_offdiagonal : guardLiveOffDiagonal = 202 := rfl

/-- 202 > 0, said as an inequality. -/
theorem guard_has_offdiagonal_instances : 0 < guardLiveOffDiagonal := by decide

/-- A deliberately spoiled numerator: `num`, bumped by 1 on paths whose first
    step is `1`.  Its value is not a function of the transition counts. -/
def numSpoiled (p : Path) : Nat := num p + ind p.b1

/-- **NEGATIVE CONTROL.**  `pairCheck` returns `false` on the spoiled
    numerator.  The test in §4 can fail, so its passing on `num` is a fact
    about `num` and not about `pairCheck`. -/
theorem pairCheck_can_fail : pairCheck numSpoiled = false := rfl

/-- How many pairs the spoiled numerator actually breaks — 98 of the 266 live
    pairs.  (A single counterexample would suffice; the count is here so the
    failure is not a knife-edge.) -/
def spoiledViolations : Nat :=
  cntPaths fun p => cntPaths fun q =>
    ind (ceq (counts p) (counts q) && !(numSpoiled p == numSpoiled q))

/-- The spoiled numerator violates exchangeability on 98 ordered pairs. -/
theorem spoiled_violations_count : spoiledViolations = 98 := rfl

/-- And `num` itself violates it on none.  (The same counter, run on the real
    thing: `exchangeable_exhaustive` again, as a number rather than a Bool.) -/
theorem num_violations_count :
    (cntPaths fun p => cntPaths fun q =>
      ind (ceq (counts p) (counts q) && !(num p == num q))) = 0 := rfl

/-! ## 6.  How many classes there are

If every path were its own transition-count class, `exchangeable` would be
true and empty.  The bench reports the class count for L = 8; here is the
count for L = 6.

`isRep p` holds when `p` has the least index among the paths sharing its count
vector.  Counting representatives counts classes provided each class has
exactly one — which is not assumed here but proved, by
`exactly_one_rep_per_class`.  (`ceq` is equality by §4, so "class" means what
it should; `idx_injective` says the indices really do order the paths.) -/

/-- The index of a path, `b1` the most significant bit: `0 ≤ idx p < 64`. -/
def idx (p : Path) : Nat :=
  cond p.b1 32 0 + cond p.b2 16 0 + cond p.b3 8 0 +
  cond p.b4 4 0 + cond p.b5 2 0 + cond p.b6 1 0

/-- Distinct paths get distinct indices. -/
def idxInjective : Bool :=
  allPathsB fun p => allPathsB fun q => !(idx p == idx q) || peq p q

/-- `idx` is injective on the 64 paths, so "least index in its class" picks out
    at most one path per class. -/
theorem idx_injective : idxInjective = true := rfl

/-- Is `p` the least-indexed path of its transition-count class? -/
def isRep (p : Path) : Bool :=
  allPathsB fun q => !(ceq (counts p) (counts q)) || Nat.ble (idx p) (idx q)

/-- For each path, how many members of its class are representatives. -/
def repsPerClass : Bool :=
  allPathsB fun p => (cntPaths fun q => ind (ceq (counts p) (counts q) && isRep q)) == 1

/-- **EXACTLY ONE REPRESENTATIVE PER CLASS.**  For every one of the 64 paths,
    its class contains exactly one representative.  This is what licenses
    reading `numClasses` as a number of classes rather than as the size of
    some incidental subset. -/
theorem exactly_one_rep_per_class : repsPerClass = true := rfl

/-- The number of distinct transition-count classes among the 64 paths. -/
def numClasses : Nat := cntPaths fun p => ind (isRep p)

/-- There are 64 paths. -/
theorem path_count : cntPaths (fun _ => 1) = 64 := rfl

/-- **22 CLASSES.**  The 64 paths of length 6 fall into 22 transition-count
    classes.  (The bench prints the analogous number for length 8.) -/
theorem class_count : numClasses = 22 := rfl

/-- **THE THEOREM HAS CONTENT.**  22 < 64: the classes are strictly coarser
    than the paths, so `exchangeable` is identifying paths that the machine
    could have told apart. -/
theorem classes_fewer_than_paths : numClasses < cntPaths (fun _ => 1) := by decide

/-! ## 7.  Negative controls, and one honest failure

Norm: a test that cannot separate is not a test.  §7.1 exhibits two concrete
paths that the invariant separates, and two that it identifies.

§7.2 records something the bench does not claim and this file will not either:
the converse is FALSE.  `num` does not determine the count vector — at length
6 there are distinct classes sharing a numerator.  So the honest statement is
one-directional: the counts determine the probability, not conversely. -/

/-- The all-0 path `000000`. -/
def pZeros : Path := ⟨false, false, false, false, false, false⟩

/-- The all-1 path `111111`. -/
def pOnes : Path := ⟨true, true, true, true, true, true⟩

/-- `000000`: six `0 → 0` steps.  Probability `3628800/D = 1/7`. -/
theorem counts_pZeros : counts pZeros = ⟨6, 0, 0, 0⟩ := rfl

/-- `111111`: one `0 → 1` step then five `1 → 1`.  Probability
    `2116800/D = 1/12`. -/
theorem counts_pOnes : counts pOnes = ⟨0, 1, 0, 5⟩ := rfl

/-- **NEGATIVE CONTROL — the invariant separates.**  Two paths with different
    count vectors and different numerators.  Without this, `exchangeable`
    could be true merely because `num` is constant. -/
theorem separates : counts pZeros ≠ counts pOnes ∧ num pZeros ≠ num pOnes := by
  constructor
  · decide
  · decide

/-- The two numerators, written out. -/
theorem num_pZeros : num pZeros = 3628800 := rfl

/-- -/
theorem num_pOnes : num pOnes = 2116800 := rfl

/-- `000010`. -/
def pA : Path := ⟨false, false, false, false, true, false⟩

/-- `000100`.  A different path from `pA` — they differ in step 4. -/
def pB : Path := ⟨false, false, false, true, false, false⟩

/-- The two are genuinely different paths — they differ at step 4. -/
theorem pA_ne_pB : pA ≠ pB := by decide

/-- **POSITIVE CONTROL — the invariant identifies.**  `pA` and `pB` are
    different paths with the same count vector `(4,1,1,0)`, and `exchangeable`
    forces their probabilities equal.  Here the equality is also checked
    directly: both are `423360/D = 1/60`. -/
theorem pA_pB_same_counts : counts pA = counts pB := rfl

/-- The conclusion `exchangeable` draws from `pA_pB_same_counts`, checked
    independently by computation. -/
theorem pA_pB_same_num : num pA = num pB := rfl

/-- Derived from the general theorem rather than computed, so that the general
    theorem is exercised on a live instance. -/
theorem pA_pB_same_num_via_theorem : num pA = num pB :=
  exchangeable pA pB pA_pB_same_counts

/-! ### 7.2  The converse is false

`11111 0`: one `0 → 1`, four `1 → 1`, one `1 → 0`. -/

/-- `111110`. -/
def pC : Path := ⟨true, true, true, true, true, false⟩

/-- `pC` has count vector `(0,1,1,4)`, different from `pA`'s `(4,1,1,0)` … -/
theorem counts_pC : counts pC = ⟨0, 1, 1, 4⟩ := rfl

/-- … so the two count vectors differ … -/
theorem pA_pC_different_counts : counts pA ≠ counts pC := by decide

/-- … and yet the numerators agree. -/
theorem pA_pC_same_num : num pA = num pC := rfl

/-- **THE CONVERSE FAILS.**  Equal numerators do not imply equal transition
    counts.  `num` is a function of the counts (§3); it is not an injective
    one.  Stated here so that no reader takes `exchangeable` for an
    equivalence.  (Five numerators are shared between distinct classes at
    length 6; this is one of those collisions.) -/
theorem converse_false :
    ∃ p q : Path, num p = num q ∧ counts p ≠ counts q :=
  ⟨pA, pC, pA_pC_same_num, pA_pC_different_counts⟩

end Workshop.Exchangeable
