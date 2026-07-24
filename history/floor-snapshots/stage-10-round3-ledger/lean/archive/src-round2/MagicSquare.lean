/-
  THE WORKSHOP → LEAN 4.  Round 1, Tier 2.

  Bench formalized: `sheaf_contextuality.py` / `sheaf_cohomology.py`
                    (second weld — "the obstruction gets an address")
  Claims made theorem:
    A.  No global section: 0 of 512 assignments satisfy all six contexts.
    B.  The cohomological certificate: the all-ones cocycle y = (1,1,1,1,1,1)
        satisfies y·M = 0 and y·b = 1, so no assignment can exist — and this
        is a *proof*, not a search.

  Self-contained: NO imports.  Core tactics only (`cases`, `rw`, `exact`,
  `intro`, `rfl`).  No `decide` over function types, no Fintype, no mathlib.

  Status: PROVED, no `sorry`.  Theorem A is proved twice, independently:
  once by the cocycle (B ⟹ A, no search), once by kernel-exhausting all 512.

  ROUND 2 ADDENDUM (§§6-8).  Three further bench claims:
    C.  The obstruction *group*: the left kernel of the incidence matrix M is
        exactly {0, (1,1,1,1,1,1)} — computed by exhausting all 64 covectors.
        The last step to "coker(M) ≅ Z_2" is rank-nullity and duality, which
        are CITED, NOT PROVED here; see the §6 header for the exact boundary.
    D.  The classical ceiling: over all 4096 deterministic script pairs for the
        cooperation game, the best score is exactly 8 of 9, attained.
    H.  The sharp local bound: over all 512 assignments, the largest number of
        simultaneously satisfiable contexts is exactly 5 of 6.  Round 1 proved
        only ≥ 5, constructively; §8 adds the matching ≤ 5.
-/

namespace Workshop.MagicSquare

/-! ## 0. Mod-2 arithmetic, hand-rolled

`par a b` is the mod-2 sum.  The dictionary with the bench's ±1 convention:
`false` ↔ outcome +1, `true` ↔ outcome −1; multiplying signs is adding
parities.  Defined here rather than imported so the file depends on nothing.
(Note: core Lean's `⊕` is `Sum`, the type former — hence `⊻` here.) -/

/-- Mod-2 sum (xor) on `Bool`. -/
def par : Bool → Bool → Bool
  | true,  b => !b
  | false, b => b

-- Precedence 65 (that of `+`), NOT below 50: `=` is `infix:50`, so a looser
-- `⊻` would make `A ⊻ B = false` parse as `A ⊻ (decide (B = false))` — which
-- typechecks, and is even true, but is not the statement intended.  Caught
-- only when the lemma was applied.  Recorded here because a theorem that
-- compiles is not yet a theorem that says what you meant.
@[inherit_doc] local infixl:65 " ⊻ " => par

/-! ## 1. The square

Nine cells indexed `(r, c) : Fin 3 × Fin 3`.  Six contexts: three rows, three
columns.  The bench's `COL_SIGNS = [+1, +1, -1]` becomes: rows and columns 0,1
have parity `false`, column 2 has parity `true`.  That single sign flip is the
whole obstruction. -/

/-- An assignment of a definite ±1 value to every cell — a candidate
    "view from the wings". -/
abbrev Assignment := Fin 3 → Fin 3 → Bool

/-- The parity a row context reports. -/
def rowPar (v : Assignment) (r : Fin 3) : Bool := v r 0 ⊻ v r 1 ⊻ v r 2

/-- The parity a column context reports. -/
def colPar (v : Assignment) (c : Fin 3) : Bool := v 0 c ⊻ v 1 c ⊻ v 2 c

/-- The six constraints of the Mermin–Peres square. -/
def GlobalSection (v : Assignment) : Prop :=
  rowPar v 0 = false ∧ rowPar v 1 = false ∧ rowPar v 2 = false ∧
  colPar v 0 = false ∧ colPar v 1 = false ∧ colPar v 2 = true

/-! ## 2. Theorem B — the certificate

The bench computes: rank M = 5, rank [M|b] = 6, coker(M) ≅ Z₂, and exhibits
the witnessing cocycle y = (1,1,1,1,1,1) with y·M = 0 and y·b = 1.

Here those two facts become two theorems.  `cocycle_annihilates` is y·M = 0:
summing all six context parities, every cell appears exactly twice — once in
its row, once in its column — so the total is forced to `false` *whatever the
assignment is*.  `twist_is_odd` is y·b = 1: the prescribed parities sum to
`true`.  Together: `false = true`. -/

/-- The combinatorial heart, over nine free bits: each cell occurs in exactly
    one row and exactly one column, hence exactly twice in the total, hence
    cancels.  Proved by exhausting all 2⁹ bit patterns in the kernel. -/
theorem each_cell_twice (a b c d e f g h i : Bool) :
    ((a ⊻ b ⊻ c) ⊻ (d ⊻ e ⊻ f) ⊻ (g ⊻ h ⊻ i)) ⊻
    ((a ⊻ d ⊻ g) ⊻ (b ⊻ e ⊻ h) ⊻ (c ⊻ f ⊻ i)) = false := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;>
    cases g <;> cases h <;> cases i <;> rfl

/-- **y · M = 0.**  For *every* assignment, the six context parities sum to
    zero.  This is the fundamental cycle of the cover; no coboundary reaches
    it, and no assignment escapes it. -/
theorem cocycle_annihilates (v : Assignment) :
    ((rowPar v 0 ⊻ rowPar v 1 ⊻ rowPar v 2) ⊻
     (colPar v 0 ⊻ colPar v 1 ⊻ colPar v 2)) = false :=
  each_cell_twice (v 0 0) (v 0 1) (v 0 2)
                  (v 1 0) (v 1 1) (v 1 2)
                  (v 2 0) (v 2 1) (v 2 2)

/-- **y · b = 1.**  The parities the square *prescribes* sum to one.  The lone
    `true` is column 2 — the bench's `COL_SIGNS = [+1, +1, −1]`. -/
theorem twist_is_odd :
    ((false ⊻ false ⊻ false) ⊻ (false ⊻ false ⊻ true)) = true := rfl

/-! ## 3. Theorem A — no global section, from the certificate -/

/-- **THE OBSTRUCTION.**  No assignment satisfies all six contexts.
    Proof: the cocycle evaluates the left side to `false` and the right side
    to `true`.  Local sections everywhere, global section nowhere. -/
theorem no_global_section (v : Assignment) : ¬ GlobalSection v := by
  intro hs
  have hr0 : rowPar v 0 = false := hs.1
  have hr1 : rowPar v 1 = false := hs.2.1
  have hr2 : rowPar v 2 = false := hs.2.2.1
  have hc0 : colPar v 0 = false := hs.2.2.2.1
  have hc1 : colPar v 1 = false := hs.2.2.2.2.1
  have hc2 : colPar v 2 = true  := hs.2.2.2.2.2
  have key := cocycle_annihilates v
  rw [hr0, hr1, hr2, hc0, hc1, hc2] at key
  -- `key` now reads `((false ⊻ false ⊻ false) ⊻ (false ⊻ false ⊻ true)) = false`.
  -- Its left side is `true` by `twist_is_odd`, so: `true = false`.
  have bad : true = false := twist_is_odd.symm.trans key
  exact Bool.noConfusion bad

/-! ## 4. Theorem A again, the way the bench got it: exhaustion

`sheaf_contextuality.py` reports **0 of 512**.  Here the same 512 are walked by
the kernel.  This is logically redundant given §3 — and that is the point: the
certificate replaces the search.  Kept because the workshop's habit is to check
a thing twice, from two directions, and believe it when both co-sign.

For the two readings to genuinely co-sign, the Bool enumeration must be *tied*
to `GlobalSection` — otherwise it is a true statement about a different object
and "proved twice" is a bluff.  `no_global_section_via_exhaustion` is the tie:
it derives Theorem A from `satisfies_never` alone, never invoking §3. -/

/-- The six constraints, as a single decidable test on nine bits. -/
def satisfies (a b c d e f g h i : Bool) : Bool :=
  !(a ⊻ b ⊻ c) && !(d ⊻ e ⊻ f) && !(g ⊻ h ⊻ i) &&
  !(a ⊻ d ⊻ g) && !(b ⊻ e ⊻ h) &&  (c ⊻ f ⊻ i)

/-- **0 of 512.**  No bit pattern whatsoever satisfies the six constraints —
    the bench's exhaustive search, walked by the kernel. -/
theorem satisfies_never (a b c d e f g h i : Bool) :
    satisfies a b c d e f g h i = false := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;>
    cases g <;> cases h <;> cases i <;> rfl

/-- **THEOREM A, PROVED A SECOND TIME** — from the exhaustion, independently of
    the cocycle argument in §3.  The nine cells of any assignment are nine
    bits; `satisfies_never` says no nine bits work. -/
theorem no_global_section_via_exhaustion (v : Assignment) : ¬ GlobalSection v := by
  intro hs
  have hr0 : v 0 0 ⊻ v 0 1 ⊻ v 0 2 = false := hs.1
  have hr1 : v 1 0 ⊻ v 1 1 ⊻ v 1 2 = false := hs.2.1
  have hr2 : v 2 0 ⊻ v 2 1 ⊻ v 2 2 = false := hs.2.2.1
  have hc0 : v 0 0 ⊻ v 1 0 ⊻ v 2 0 = false := hs.2.2.2.1
  have hc1 : v 0 1 ⊻ v 1 1 ⊻ v 2 1 = false := hs.2.2.2.2.1
  have hc2 : v 0 2 ⊻ v 1 2 ⊻ v 2 2 = true  := hs.2.2.2.2.2
  have hsat : satisfies (v 0 0) (v 0 1) (v 0 2) (v 1 0) (v 1 1) (v 1 2)
                        (v 2 0) (v 2 1) (v 2 2) = true := by
    show (!(v 0 0 ⊻ v 0 1 ⊻ v 0 2) && !(v 1 0 ⊻ v 1 1 ⊻ v 1 2) &&
          !(v 2 0 ⊻ v 2 1 ⊻ v 2 2) && !(v 0 0 ⊻ v 1 0 ⊻ v 2 0) &&
          !(v 0 1 ⊻ v 1 1 ⊻ v 2 1) &&  (v 0 2 ⊻ v 1 2 ⊻ v 2 2)) = true
    rw [hr0, hr1, hr2, hc0, hc1, hc2]
    rfl
  rw [satisfies_never (v 0 0) (v 0 1) (v 0 2) (v 1 0) (v 1 1) (v 1 2)
                      (v 2 0) (v 2 1) (v 2 2)] at hsat
  exact Bool.noConfusion hsat

/-- Existential quantifier over one bit. -/
def anyB (p : Bool → Bool) : Bool := p true || p false

/-- "Does some assignment satisfy all six contexts?", as one closed Bool. -/
def existsGlobal : Bool :=
  anyB fun a => anyB fun b => anyB fun c =>
  anyB fun d => anyB fun e => anyB fun f =>
  anyB fun g => anyB fun h => anyB fun i =>
    satisfies a b c d e f g h i

/-- The same **0 of 512**, packaged as a single Bool the kernel evaluates.
    (Presentation only — `satisfies_never` is the load-bearing statement, and
    `no_global_section_via_exhaustion` is what makes the second reading a
    proof of Theorem A rather than a parallel fact.) -/
theorem no_global_section_exhaustive : existsGlobal = false := rfl

/-! ## 5. Local sections everywhere, global section nowhere

`sheaf_contextuality.py`: "every context is internally consistent … every five
contexts are jointly satisfiable — and all six are not."  That is the sheaf
statement, and it is a *pair* of quantified claims, one existential and one
universal.  Both are below.

(An earlier draft stated the "five" half as a closed Boolean identity with no
assignment in it — five syntactically identical conjuncts, provably insensitive
to every definition in this file.  It was true and it was vacuous.  It said
nothing about the square.  Replaced with the statement it was pretending to
be.) -/

/-- The six contexts, named. -/
inductive Ctx where
  | r0 | r1 | r2 | c0 | c1 | c2

/-- Does `v` meet context `k`?  Rows and columns 0,1 want parity `false`;
    column 2 — the twisted one — wants `true`. -/
def meets (v : Assignment) : Ctx → Bool
  | .r0 => !rowPar v 0
  | .r1 => !rowPar v 1
  | .r2 => !rowPar v 2
  | .c0 => !colPar v 0
  | .c1 => !colPar v 1
  | .c2 =>  colPar v 2

/-- Build an assignment from nine bits, row-major. -/
def mk (a00 a01 a02 a10 a11 a12 a20 a21 a22 : Bool) : Assignment :=
  fun i j =>
    if i = 0 then (if j = 0 then a00 else if j = 1 then a01 else a02)
    else if i = 1 then (if j = 0 then a10 else if j = 1 then a11 else a12)
    else (if j = 0 then a20 else if j = 1 then a21 else a22)

/-- `!b = true → b = false`.  (`b` explicit: left implicit, the elaborator
    unifies it against a coerced `decide (… = true)` and the application
    fails.) -/
theorem of_not_eq_true (b : Bool) (h : (!b) = true) : b = false := by
  cases b
  · rfl
  · exact Bool.noConfusion h

/-- **LOCAL SECTIONS EVERYWHERE.**  For *every* context `k` there is an
    assignment meeting all five others.  Six explicit witnesses; no context is
    individually to blame. -/
theorem local_sections_everywhere (k : Ctx) :
    ∃ v : Assignment, ∀ j : Ctx, j ≠ k → meets v j = true := by
  cases k
  · exact ⟨mk false false true  false false false false false false,
      by intro j hj; cases j <;> first | rfl | exact absurd rfl hj⟩
  · exact ⟨mk false false false false false true  false false false,
      by intro j hj; cases j <;> first | rfl | exact absurd rfl hj⟩
  · exact ⟨mk false false false false false false false false true,
      by intro j hj; cases j <;> first | rfl | exact absurd rfl hj⟩
  · exact ⟨mk false false false false false false true  false true,
      by intro j hj; cases j <;> first | rfl | exact absurd rfl hj⟩
  · exact ⟨mk false false false false false false false true  true,
      by intro j hj; cases j <;> first | rfl | exact absurd rfl hj⟩
  · exact ⟨mk false false false false false false false false false,
      by intro j hj; cases j <;> first | rfl | exact absurd rfl hj⟩

/-- **GLOBAL SECTION NOWHERE.**  No assignment meets all six.  Same content as
    `no_global_section`, phrased against `meets` so it pairs exactly with the
    theorem above: `∀k ∃v` holds, `∃v ∀k` fails.  That gap is the obstruction. -/
theorem no_global_section_ctx :
    ¬ ∃ v : Assignment, ∀ k : Ctx, meets v k = true := by
  intro hex
  apply Exists.elim hex
  intro v h
  have e0 : rowPar v 0 = false := of_not_eq_true (rowPar v 0) (h .r0)
  have e1 : rowPar v 1 = false := of_not_eq_true (rowPar v 1) (h .r1)
  have e2 : rowPar v 2 = false := of_not_eq_true (rowPar v 2) (h .r2)
  have f0 : colPar v 0 = false := of_not_eq_true (colPar v 0) (h .c0)
  have f1 : colPar v 1 = false := of_not_eq_true (colPar v 1) (h .c1)
  have f2 : colPar v 2 = true  := h .c2
  exact no_global_section v ⟨e0, e1, e2, f0, f1, f2⟩

/-! ## 6. Item C — the obstruction *group*, not just an obstruction

Round 1 proved that the all-ones vector `y = (1,1,1,1,1,1)` is a cocycle
(`cocycle_annihilates`) pairing nontrivially with the twist (`twist_is_odd`).
That establishes *there is an obstruction*.  It does not establish the bench's
stronger claim, which is about the size of the obstruction group:

    rank M = 5,  rank [M|b] = 6,  coker(M) ≅ Z_2.

This section closes the first half of that gap by computing the **left kernel**
of `M` exactly.

`M` is the 6×9 incidence matrix over GF(2): rows are the six contexts (three
rows of the square, then three columns), columns are the nine cells, and
`M[k][cell] = 1` when `cell` lies in context `k`.  A covector `y : GF(2)^6`
satisfies `y·M = 0` when every one of the nine entries of the row vector `y·M`
vanishes; since cell `(i,j)` lies in exactly the two contexts `row i` and
`col j`, that entry is `y_i + y_{3+j}`.

What is proved below, by exhausting all 2^6 = 64 covectors:

  * `kerCount_eq_two`    — the left kernel has **exactly 2** elements;
  * `ker_iff`            — a covector is in the left kernel **iff** it is the
                           zero vector or the all-ones vector;
  * `ker_forces_all_equal` — every kernel element has all six coordinates equal.

So the left kernel of `M` is exactly `{0, (1,1,1,1,1,1)}`, a 1-dimensional
subspace of GF(2)^6, and the all-ones cocycle of §2 is its unique nonzero
element — not merely *a* certificate but *the* certificate, up to nothing.

WHAT IS **NOT** PROVED HERE, STATED PLAINLY.  The step

    dim (left kernel of M) = 1   ⟹   rank M = 6 − 1 = 5   ⟹   dim coker(M) = 1

is rank–nullity applied to the map `y ↦ y·M` together with the duality
`coker(M) ≅ (left kernel of M)^*` over a field.  Both are standard and both are
**cited, not proved**: quotient vector spaces and dimension theory are not
formalized in this file, and formalizing them was judged out of scope.  The
Lean content is the exhaustive kernel computation.  Read "coker(M) ≅ Z_2" as a
one-line consequence of the theorems below plus a textbook fact, and read the
theorems below as the only part machine-checked. -/

/-- The incidence matrix `M`, as a predicate: is cell `(i,j)` in context `k`?
    Contexts `r0,r1,r2` are the three rows, `c0,c1,c2` the three columns —
    the same order as the bench's `M[r, cell] = 1` / `M[3 + c, cell] = 1`. -/
def inCtx : Ctx → Fin 3 → Fin 3 → Bool
  | .r0, i, _ => i == 0
  | .r1, i, _ => i == 1
  | .r2, i, _ => i == 2
  | .c0, _, j => j == 0
  | .c1, _, j => j == 1
  | .c2, _, j => j == 2

/-- Spot checks that `inCtx` is the bench's matrix and not its transpose or a
    permutation: cell (1,2) lies in row 1 and column 2 and in nothing else. -/
theorem incidence_spot_checks :
    inCtx .r1 1 2 = true ∧ inCtx .c2 1 2 = true ∧
    inCtx .r0 1 2 = false ∧ inCtx .r2 1 2 = false ∧
    inCtx .c0 1 2 = false ∧ inCtx .c1 1 2 = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- How many of the six contexts contain cell `(i,j)` — the weight of that
    column of `M`. -/
def colWeight (i j : Fin 3) : Nat :=
  cond (inCtx .r0 i j) 1 0 + cond (inCtx .r1 i j) 1 0 + cond (inCtx .r2 i j) 1 0 +
  cond (inCtx .c0 i j) 1 0 + cond (inCtx .c1 i j) 1 0 + cond (inCtx .c2 i j) 1 0

/-- **Every column of `M` has weight exactly 2.**  Each cell sits in one row
    context and one column context.  This is the matrix-level restatement of
    `each_cell_twice`, and it is what makes the all-ones vector a cocycle. -/
theorem every_column_weight_two :
    colWeight 0 0 = 2 ∧ colWeight 0 1 = 2 ∧ colWeight 0 2 = 2 ∧
    colWeight 1 0 = 2 ∧ colWeight 1 1 = 2 ∧ colWeight 1 2 = 2 ∧
    colWeight 2 0 = 2 ∧ colWeight 2 1 = 2 ∧ colWeight 2 2 = 2 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The `(i,j)` entry of the row vector `y · M`, over GF(2). -/
def yM (y : Ctx → Bool) (i j : Fin 3) : Bool :=
  ((y .r0 && inCtx .r0 i j) ⊻ (y .r1 && inCtx .r1 i j) ⊻ (y .r2 && inCtx .r2 i j)) ⊻
  ((y .c0 && inCtx .c0 i j) ⊻ (y .c1 && inCtx .c1 i j) ⊻ (y .c2 && inCtx .c2 i j))

/-- Build a covector from six bits, in the bench's context order. -/
def mkY (y0 y1 y2 y3 y4 y5 : Bool) : Ctx → Bool
  | .r0 => y0
  | .r1 => y1
  | .r2 => y2
  | .c0 => y3
  | .c1 => y4
  | .c2 => y5

/-- `y · M = 0`: all nine entries of the row vector vanish. -/
def isCocycle (y : Ctx → Bool) : Bool :=
  !(yM y 0 0) && !(yM y 0 1) && !(yM y 0 2) &&
  !(yM y 1 0) && !(yM y 1 1) && !(yM y 1 2) &&
  !(yM y 2 0) && !(yM y 2 1) && !(yM y 2 2)

-- A note on `!`, in the spirit of the `⊻` precedence trap recorded at the top
-- of this file.  `!` binds tighter than `&&` and than `⊻`, so `isCocycle` above
-- is the nine-fold conjunction it looks like.  But Lean's *pretty printer*
-- omits the parentheses it needs around `!`'s argument: `#check` displays
-- `not (b4 ⊻ b5)` as `!b4 ⊻ b5`, which if re-read as source would mean
-- `(!b4) ⊻ b5`.  So `#check` output involving `!` cannot be read at face value.
-- Rather than rely on reading a notation correctly, `isCocycle_iff_yM_zero`
-- below pins `isCocycle` to a statement containing no `!` at all.

/-- Nine negations conjoined are true exactly when all nine bits are false.
    Spelled with `not` applied as a function, never as the `!` notation, so
    that the lemma cannot be matched to `isCocycle` by a shared misreading. -/
theorem and9_not_iff (p0 p1 p2 p3 p4 p5 p6 p7 p8 : Bool) :
    (not p0 && not p1 && not p2 && not p3 && not p4 &&
     not p5 && not p6 && not p7 && not p8) = true ↔
      (p0 = false ∧ p1 = false ∧ p2 = false ∧ p3 = false ∧ p4 = false ∧
       p5 = false ∧ p6 = false ∧ p7 = false ∧ p8 = false) := by
  cases p0 <;> cases p1 <;> cases p2 <;> cases p3 <;> cases p4 <;>
    cases p5 <;> cases p6 <;> cases p7 <;> cases p8 <;> decide

/-- **`isCocycle y` says exactly `y · M = 0`.**  The right-hand side names the
    nine entries of the row vector `y · M` individually and uses no Boolean
    notation beyond `=`, so it is immune to any precedence misreading.  That
    this typechecks at all is the check: it forces `isCocycle` to have parsed
    as the nine-fold conjunction, since no other parse is definitionally equal
    to `and9_not_iff`'s left-hand side. -/
theorem isCocycle_iff_yM_zero (y : Ctx → Bool) :
    isCocycle y = true ↔
      (yM y 0 0 = false ∧ yM y 0 1 = false ∧ yM y 0 2 = false ∧
       yM y 1 0 = false ∧ yM y 1 1 = false ∧ yM y 1 2 = false ∧
       yM y 2 0 = false ∧ yM y 2 1 = false ∧ yM y 2 2 = false) :=
  and9_not_iff (yM y 0 0) (yM y 0 1) (yM y 0 2)
               (yM y 1 0) (yM y 1 1) (yM y 1 2)
               (yM y 2 0) (yM y 2 1) (yM y 2 2)

/-- Sum a `Nat`-valued function over one bit. -/
def countB (p : Bool → Nat) : Nat := p true + p false

/-- The number of covectors the enumeration below actually visits.  Stated so
    that `kerCount_eq_two` is a count *out of a known total* rather than a
    number produced by a scaffold that might be visiting fewer leaves than
    advertised. -/
def yEnumSize : Nat :=
  countB fun _ => countB fun _ => countB fun _ =>
  countB fun _ => countB fun _ => countB fun _ => 1

/-- The enumeration visits all 2^6 = 64 covectors. -/
theorem yEnumSize_eq_64 : yEnumSize = 64 := rfl

/-- How many of the 64 covectors lie in the left kernel of `M`. -/
def kerCount : Nat :=
  countB fun y0 => countB fun y1 => countB fun y2 =>
  countB fun y3 => countB fun y4 => countB fun y5 =>
    cond (isCocycle (mkY y0 y1 y2 y3 y4 y5)) 1 0

/-- **The left kernel of `M` has exactly 2 elements.**  Exhaustive over all 64
    covectors.  With `yEnumSize_eq_64`, this is 2 live out of 64 examined. -/
theorem kerCount_eq_two : kerCount = 2 := rfl

/-- **The left kernel is exactly `{0, (1,1,1,1,1,1)}`.**  Both directions, all
    64 covectors.  This is the statement that pins the kernel down to a
    1-dimensional subspace; `kerCount_eq_two` is the same fact as a number. -/
theorem ker_iff (y0 y1 y2 y3 y4 y5 : Bool) :
    isCocycle (mkY y0 y1 y2 y3 y4 y5) = true ↔
      ((y0 = false ∧ y1 = false ∧ y2 = false ∧
        y3 = false ∧ y4 = false ∧ y5 = false) ∨
       (y0 = true ∧ y1 = true ∧ y2 = true ∧
        y3 = true ∧ y4 = true ∧ y5 = true)) := by
  cases y0 <;> cases y1 <;> cases y2 <;> cases y3 <;> cases y4 <;> cases y5 <;> decide

/-- Every kernel element has all six coordinates equal — the coordinate-wise
    form of "the kernel is spanned by the all-ones vector". -/
theorem ker_forces_all_equal (y0 y1 y2 y3 y4 y5 : Bool) :
    isCocycle (mkY y0 y1 y2 y3 y4 y5) = true →
      (y0 = y1 ∧ y1 = y2 ∧ y2 = y3 ∧ y3 = y4 ∧ y4 = y5) := by
  cases y0 <;> cases y1 <;> cases y2 <;> cases y3 <;> cases y4 <;> cases y5 <;> decide

/-- The zero covector is in the kernel (it always is; recorded so the count of
    2 has both of its members named). -/
theorem zero_is_cocycle : isCocycle (mkY false false false false false false) = true := rfl

/-- The all-ones covector of §2 is in the kernel.  By `ker_iff` it is the
    *only* nonzero one. -/
theorem allOnes_is_cocycle : isCocycle (mkY true true true true true true) = true := rfl

/-- NEGATIVE CONTROL for `isCocycle`.  A test that cannot fail is not a test:
    here are covectors the check rejects.  The first is a single basis vector,
    the second the sum of two — both plausible candidates, both caught. -/
theorem cocycle_check_can_fail :
    isCocycle (mkY true false false false false false) = false ∧
    isCocycle (mkY false false false false false true) = false ∧
    isCocycle (mkY true true false false false false) = false ∧
    isCocycle (mkY true false false true false false) = false :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ## 7. Item D — the classical ceiling is 8/9, exactly

`sheaf_cohomology.py`'s `classical_value()` exhausts all deterministic scripts
for the cooperation game — Alice is handed a row and fills all three of its
cells, Bob is handed a column and fills all three of its cells, and they win a
cell when their two entries there agree — and asserts `best == 8` out of 9.

The bench enumerates 64 × 64 = 4096 strategy pairs: Alice picks, for each of
the three rows, one of the four triples whose product is +1; Bob picks, for
each of the three columns `c`, one of the four triples whose product is
`COL_SIGNS[c]`.  Four triples is two free bits, so 3 × 2 = 6 bits for Alice and
6 for Bob: 12 bits, 4096 pairs.  That is the parametrization used here.

The parametrization is *proved* to be the right one, not asserted:

  * `alice_row_normal` / `bob_col_normal` — a triple has a prescribed parity
    **iff** its third entry is determined by the first two.  So writing the
    third entry as a function of the first two loses no strategy and admits no
    illegal one: the 12 bits are in bijection with the bench's 4096 pairs.
  * `alice_rows_untwisted` / `bob_cols_twisted` — the tables built from those
    12 bits really do satisfy the game's parity rules, stated with the *same*
    `rowPar` and `colPar` used everywhere else in this file.

Cross-check against the bench, run separately: the bench's `classical_value()`
enumerates 4096 pairs, reports `best = 8`, and 144 pairs attain 8.  The
enumeration here reports the same three numbers (`pairCount_eq_4096`,
`bestClassical_eq_eight`, `eightCount_eq_144`).  Agreeing on the count of
maximizers, not just on the maximum, is what makes this a correspondence
between the two enumerations rather than a coincidence of one integer. -/

/-- A legal row triple for Alice — parity `false`, the bench's product +1 — is
    exactly one whose third entry is the sum of the first two.  Left-to-right:
    the parametrization admits nothing illegal.  Right-to-left: it omits
    nothing legal. -/
theorem alice_row_normal (x y z : Bool) : (x ⊻ y ⊻ z) = false ↔ z = (x ⊻ y) := by
  cases x <;> cases y <;> cases z <;> decide

/-- The same for Bob, with the prescribed parity `s` left free — `false` for
    columns 0 and 1, `true` for column 2. -/
theorem bob_col_normal (x y z s : Bool) : (x ⊻ y ⊻ z) = s ↔ z = (x ⊻ y ⊻ s) := by
  cases x <;> cases y <;> cases z <;> cases s <;> decide

/-- Alice's script from 6 bits: two free bits per row, third entry forced. -/
def aliceTable (a0 a1 a2 a3 a4 a5 : Bool) : Assignment :=
  mk a0 a1 (a0 ⊻ a1)
     a2 a3 (a2 ⊻ a3)
     a4 a5 (a4 ⊻ a5)

/-- Bob's script from 6 bits, written row-major so it can be compared with
    Alice's cell by cell.  Column 0 is `(b0, b1, b0+b1)` read downwards,
    column 1 is `(b2, b3, b2+b3)`, column 2 is `(b4, b5, ¬(b4+b5))` — the lone
    flipped parity, the bench's `COL_SIGNS = [+1, +1, −1]`. -/
def bobTable (b0 b1 b2 b3 b4 b5 : Bool) : Assignment :=
  mk b0 b2 b4
     b1 b3 b5
     (b0 ⊻ b1) (b2 ⊻ b3) (!(b4 ⊻ b5))

/-- Alice's three rows all have parity `false`, whatever her 6 bits. -/
theorem alice_rows_untwisted (a0 a1 a2 a3 a4 a5 : Bool) :
    rowPar (aliceTable a0 a1 a2 a3 a4 a5) 0 = false ∧
    rowPar (aliceTable a0 a1 a2 a3 a4 a5) 1 = false ∧
    rowPar (aliceTable a0 a1 a2 a3 a4 a5) 2 = false := by
  cases a0 <;> cases a1 <;> cases a2 <;> cases a3 <;> cases a4 <;> cases a5 <;>
    exact ⟨rfl, rfl, rfl⟩

/-- Bob's three columns have parities `false, false, true`, whatever his
    6 bits.  This is the constraint set of the magic square, and it is stated
    with the file's own `colPar`. -/
theorem bob_cols_twisted (b0 b1 b2 b3 b4 b5 : Bool) :
    colPar (bobTable b0 b1 b2 b3 b4 b5) 0 = false ∧
    colPar (bobTable b0 b1 b2 b3 b4 b5) 1 = false ∧
    colPar (bobTable b0 b1 b2 b3 b4 b5) 2 = true := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;>
    exact ⟨rfl, rfl, rfl⟩

/-- Cell-level spot checks that the two tables are laid out as described and
    not transposed.  Alice's free bits `a2, a3` are row 1; Bob's free bits
    `b2, b3` are column 1; Bob's forced cell `(2,2)` is the negated sum, the one
    place the twist lives. -/
theorem table_layout_spot_checks (a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5 : Bool) :
    aliceTable a0 a1 a2 a3 a4 a5 1 0 = a2 ∧
    aliceTable a0 a1 a2 a3 a4 a5 1 1 = a3 ∧
    aliceTable a0 a1 a2 a3 a4 a5 2 2 = (a4 ⊻ a5) ∧
    bobTable b0 b1 b2 b3 b4 b5 0 1 = b2 ∧
    bobTable b0 b1 b2 b3 b4 b5 1 1 = b3 ∧
    bobTable b0 b1 b2 b3 b4 b5 2 1 = (b2 ⊻ b3) ∧
    (bobTable b0 b1 b2 b3 b4 b5 2 2 ⊻ (b4 ⊻ b5)) = true := by
  cases b4 <;> cases b5 <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- 1 when Alice and Bob write the same value in cell `(i,j)`, else 0.  Two
    `Bool`s are equal exactly when their mod-2 sum is `false`. -/
def agree (v w : Assignment) (i j : Fin 3) : Nat := cond (v i j ⊻ w i j) 0 1

/-- The number of the nine cells on which the two scripts agree, out of 9. -/
def gameScore (a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5 : Bool) : Nat :=
  agree (aliceTable a0 a1 a2 a3 a4 a5) (bobTable b0 b1 b2 b3 b4 b5) 0 0 +
  agree (aliceTable a0 a1 a2 a3 a4 a5) (bobTable b0 b1 b2 b3 b4 b5) 0 1 +
  agree (aliceTable a0 a1 a2 a3 a4 a5) (bobTable b0 b1 b2 b3 b4 b5) 0 2 +
  agree (aliceTable a0 a1 a2 a3 a4 a5) (bobTable b0 b1 b2 b3 b4 b5) 1 0 +
  agree (aliceTable a0 a1 a2 a3 a4 a5) (bobTable b0 b1 b2 b3 b4 b5) 1 1 +
  agree (aliceTable a0 a1 a2 a3 a4 a5) (bobTable b0 b1 b2 b3 b4 b5) 1 2 +
  agree (aliceTable a0 a1 a2 a3 a4 a5) (bobTable b0 b1 b2 b3 b4 b5) 2 0 +
  agree (aliceTable a0 a1 a2 a3 a4 a5) (bobTable b0 b1 b2 b3 b4 b5) 2 1 +
  agree (aliceTable a0 a1 a2 a3 a4 a5) (bobTable b0 b1 b2 b3 b4 b5) 2 2

/-- Maximum of a `Nat`-valued function over one bit. -/
def maxB (p : Bool → Nat) : Nat := cond (Nat.ble (p true) (p false)) (p false) (p true)

/-- Universal quantifier over one bit, as a `Bool`. -/
def allB (p : Bool → Bool) : Bool := p true && p false

/-- CONTROLS ON THE SEARCH SCAFFOLD ITSELF.  Every "max over N cases" result
    below is only as good as `maxB`, and every count only as good as `countB`.
    A `maxB` that silently returned `p true` would still make
    `bestClassical = 8` come out — and would be reporting one strategy pair,
    not 4096.  So: `maxB` picks the larger branch from either side, `countB`
    adds both branches, and `allB` can return `false`. -/
theorem scaffold_controls :
    maxB (fun b => cond b 3 7) = 7 ∧
    maxB (fun b => cond b 7 3) = 7 ∧
    countB (fun b => cond b 1 0) = 1 ∧
    countB (fun _ => 1) = 2 ∧
    allB (fun b => b) = false ∧
    allB (fun _ => true) = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Eliminator turning one exhausted bit into a genuine `∀`.  Used twelve deep
    below so that the 4096-case bound is a real quantified statement about
    every strategy pair, not a closed `Bool` that merely evaluated to `true`. -/
theorem allB_elim {p : Bool → Bool} (h : allB p = true) (x : Bool) : p x = true := by
  have h' : (p true && p false) = true := h
  cases x
  · cases hy : p false
    · rw [hy, Bool.and_false] at h'; exact Bool.noConfusion h'
    · rfl
  · cases hx : p true
    · rw [hx, Bool.false_and] at h'; exact Bool.noConfusion h'
    · rfl

/-- The number of strategy pairs the enumeration visits. -/
def pairCount : Nat :=
  countB fun _ => countB fun _ => countB fun _ => countB fun _ =>
  countB fun _ => countB fun _ => countB fun _ => countB fun _ =>
  countB fun _ => countB fun _ => countB fun _ => countB fun _ => 1

/-- The enumeration visits all 2^12 = 4096 strategy pairs — the bench's
    64 × 64. -/
theorem pairCount_eq_4096 : pairCount = 4096 := rfl

/-- The best score any deterministic script pair achieves. -/
def bestClassical : Nat :=
  maxB fun a0 => maxB fun a1 => maxB fun a2 =>
  maxB fun a3 => maxB fun a4 => maxB fun a5 =>
  maxB fun b0 => maxB fun b1 => maxB fun b2 =>
  maxB fun b3 => maxB fun b4 => maxB fun b5 =>
    gameScore a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5

/-- **best = 8.**  The maximum over all 4096 deterministic script pairs, walked
    by the kernel.  The bench's `assert best == 8`. -/
theorem bestClassical_eq_eight : bestClassical = 8 := rfl

/-- The same 4096 walked as a `Bool`: every pair scores at most 8. -/
def scoreLe8 : Bool :=
  allB fun a0 => allB fun a1 => allB fun a2 =>
  allB fun a3 => allB fun a4 => allB fun a5 =>
  allB fun b0 => allB fun b1 => allB fun b2 =>
  allB fun b3 => allB fun b4 => allB fun b5 =>
    Nat.ble (gameScore a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5) 8

theorem scoreLe8_true : scoreLe8 = true := rfl

/-- **THE CEILING, QUANTIFIED.**  For *every* pair of deterministic scripts the
    score is at most 8.  Derived from `scoreLe8_true` by twelve applications of
    `allB_elim`, so the bound is a `∀` over strategy pairs rather than a closed
    Boolean that happens to evaluate to `true`. -/
theorem gameScore_le_eight (a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5 : Bool) :
    gameScore a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5 ≤ 8 :=
  Nat.le_of_ble_eq_true
    (allB_elim (allB_elim (allB_elim (allB_elim (allB_elim (allB_elim
    (allB_elim (allB_elim (allB_elim (allB_elim (allB_elim (allB_elim
      scoreLe8_true a0) a1) a2) a3) a4) a5) b0) b1) b2) b3) b4) b5)

/-- **NO SCRIPT IS PERFECT.**  No pair of deterministic scripts wins all nine
    cells — the ninth cell is exactly the missing global section. -/
theorem no_perfect_script (a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5 : Bool) :
    gameScore a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5 ≠ 9 := by
  have h := gameScore_le_eight a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5
  omega

/-- **THE CEILING IS ATTAINED.**  A concrete pair scoring exactly 8: both
    parties write all-`false` in their two free slots.  Without this the bound
    "≤ 8" would be consistent with a maximum of 0, and the search could have
    been empty. -/
theorem eight_attained :
    gameScore false false false false false false false false false false false false = 8 :=
  rfl

/-- NEGATIVE CONTROL for `gameScore`: it is not the constant 8.  Here is a pair
    scoring 4 and a pair scoring 6, so the maximum in `bestClassical_eq_eight`
    is a maximum over a genuinely varying quantity. -/
theorem gameScore_varies :
    gameScore true false false false false false false false false false false false = 6 ∧
    gameScore true false true false true false false false false false false false = 4 := by
  exact ⟨rfl, rfl⟩

/-- How many of the 4096 pairs attain 8. -/
def eightCount : Nat :=
  countB fun a0 => countB fun a1 => countB fun a2 =>
  countB fun a3 => countB fun a4 => countB fun a5 =>
  countB fun b0 => countB fun b1 => countB fun b2 =>
  countB fun b3 => countB fun b4 => countB fun b5 =>
    cond (gameScore a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5 == 8) 1 0

/-- 144 of the 4096 pairs attain 8 — the bench's enumeration reports the same
    144.  Two enumerations agreeing on the number of maximizers, and not only
    on the maximum, is the cross-check. -/
theorem eightCount_eq_144 : eightCount = 144 := rfl

/-- How many of the 4096 pairs attain 9. -/
def nineCount : Nat :=
  countB fun a0 => countB fun a1 => countB fun a2 =>
  countB fun a3 => countB fun a4 => countB fun a5 =>
  countB fun b0 => countB fun b1 => countB fun b2 =>
  countB fun b3 => countB fun b4 => countB fun b5 =>
    cond (gameScore a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5 == 9) 1 0

/-- None. -/
theorem nineCount_eq_zero : nineCount = 0 := rfl

/-! ## 8. Item H — five contexts, and not six: the sharp bound

`sheaf_contextuality.py` computes `best = 5` over all 512 assignments and
asserts it.  §5 above proved the `≥ 5` half constructively, with six explicit
witnesses (`local_sections_everywhere`).  What was missing is the `≤ 5` half:
that no assignment does better.

`satCount v` counts how many of the six contexts `v` meets, using the same
`meets` — hence the same `rowPar`, `colPar`, `par` — as everywhere else.  The
bound is *not* restated as a fresh closed Boolean identity; it is a statement
about `satCount` of an arbitrary `Assignment`.

  * `satCount_le_five` — for **every** assignment, at most 5 of 6 contexts;
  * `five_attained`    — an assignment meeting exactly 5, so the bound is tight;
  * `satCount_ne_six`  — the `0 of 512` of §4, recovered from the sharp bound.

Together: the maximum is exactly 5. -/

/-- How many of the six contexts the assignment `v` meets. -/
def satCount (v : Assignment) : Nat :=
  cond (meets v .r0) 1 0 + cond (meets v .r1) 1 0 + cond (meets v .r2) 1 0 +
  cond (meets v .c0) 1 0 + cond (meets v .c1) 1 0 + cond (meets v .c2) 1 0

/-- The same count, read off nine explicit bits. -/
def satBits (a b c d e f g h i : Bool) : Nat := satCount (mk a b c d e f g h i)

/-- `satCount` reads only the nine cell values, so the nine-bit form and the
    assignment form agree for every assignment.  This is the bridge that makes
    the exhaustion below a statement about all assignments. -/
theorem satCount_eq_satBits (v : Assignment) :
    satCount v = satBits (v 0 0) (v 0 1) (v 0 2)
                         (v 1 0) (v 1 1) (v 1 2)
                         (v 2 0) (v 2 1) (v 2 2) := rfl

/-- The number of assignments the enumeration visits. -/
def assignCount : Nat :=
  countB fun _ => countB fun _ => countB fun _ =>
  countB fun _ => countB fun _ => countB fun _ =>
  countB fun _ => countB fun _ => countB fun _ => 1

/-- All 2^9 = 512 of them — the bench's 512. -/
theorem assignCount_eq_512 : assignCount = 512 := rfl

/-- The largest number of contexts any assignment meets. -/
def bestSat : Nat :=
  maxB fun a => maxB fun b => maxB fun c =>
  maxB fun d => maxB fun e => maxB fun f =>
  maxB fun g => maxB fun h => maxB fun i => satBits a b c d e f g h i

/-- **best = 5.**  The maximum over all 512 assignments.  The bench's
    `assert best == 5`. -/
theorem bestSat_eq_five : bestSat = 5 := rfl

/-- The same 512 walked as a `Bool`. -/
def satLe5 : Bool :=
  allB fun a => allB fun b => allB fun c =>
  allB fun d => allB fun e => allB fun f =>
  allB fun g => allB fun h => allB fun i =>
    Nat.ble (satBits a b c d e f g h i) 5

theorem satLe5_true : satLe5 = true := rfl

/-- The bound on nine bits, quantified. -/
theorem satBits_le_five (a b c d e f g h i : Bool) : satBits a b c d e f g h i ≤ 5 :=
  Nat.le_of_ble_eq_true
    (allB_elim (allB_elim (allB_elim (allB_elim (allB_elim (allB_elim
    (allB_elim (allB_elim (allB_elim satLe5_true a) b) c) d) e) f) g) h) i)

/-- **AT MOST FIVE, FOR EVERY ASSIGNMENT.**  The `≤ 5` half of the bench's
    sharp `best = 5`.  Stated about an arbitrary `Assignment` and about
    `meets`, so it is the same object §5 constructed witnesses for. -/
theorem satCount_le_five (v : Assignment) : satCount v ≤ 5 := by
  rw [satCount_eq_satBits v]
  exact satBits_le_five (v 0 0) (v 0 1) (v 0 2)
                        (v 1 0) (v 1 1) (v 1 2)
                        (v 2 0) (v 2 1) (v 2 2)

/-- **FIVE IS ATTAINED.**  The witness §5 used for "every context but `r0`"
    meets exactly five.  With `satCount_le_five` the maximum is exactly 5. -/
theorem five_attained :
    satCount (mk false false true false false false false false false) = 5 := rfl

/-- **GLOBAL SECTION NOWHERE, ONE MORE TIME** — now as a corollary of the sharp
    bound rather than of the cocycle or of the 512-case kernel walk. -/
theorem satCount_ne_six (v : Assignment) : satCount v ≠ 6 := by
  have h := satCount_le_five v
  omega

/-- NEGATIVE CONTROL for `satCount`: it is not the constant 5.  Assignments
    meeting 3 and meeting 1 of the six contexts.  A counter that always
    returned 5 would satisfy `satCount_le_five` and `five_attained` while
    measuring nothing. -/
theorem satCount_varies :
    satCount (mk true false false false false false false false false) = 3 ∧
    satCount (mk false false false false false true true true true) = 1 :=
  ⟨rfl, rfl⟩

/-- How many of the 512 assignments attain 5. -/
def fiveCount : Nat :=
  countB fun a => countB fun b => countB fun c =>
  countB fun d => countB fun e => countB fun f =>
  countB fun g => countB fun h => countB fun i =>
    cond (satBits a b c d e f g h i == 5) 1 0

/-- 96 of the 512 assignments meet five contexts.  A live-instance count for
    the guarded claim above: the `≤ 5` bound is not vacuous, and "five" is
    reached from 96 different directions. -/
theorem fiveCount_eq_96 : fiveCount = 96 := rfl

/-- How many of the 512 assignments attain 6. -/
def sixCount : Nat :=
  countB fun a => countB fun b => countB fun c =>
  countB fun d => countB fun e => countB fun f =>
  countB fun g => countB fun h => countB fun i =>
    cond (satBits a b c d e f g h i == 6) 1 0

/-- None — the bench's `0 of 512`, counted this time through `meets` rather
    than through `satisfies`. -/
theorem sixCount_eq_zero : sixCount = 0 := rfl

/-! ## 9. Audit hardening

Three gaps found by adversarial review of §6–§8, closed here.

The first is a missing negative control.  The second is subtler and worth
stating plainly: a count like `kerCount = 2` is only meaningful "out of 64" if
the nest computing it has the same depth as the nest computing 64 — and
`yEnumSize_eq_64` certifies a *separate* nest of the intended shape, not that
`kerCount`'s nest has that shape.  A `kerCount` one level too shallow would
still be "2", and nothing would notice.  The complements below close that: they
share each count's own nest and predicate, so `count + complement = total` can
only hold if the nest really has the advertised depth. -/

/-- NORM 8, the one scaffold `scaffold_controls` omitted: `anyB` can return
    either value.  Without this, a degenerate `anyB` returning `false`
    unconditionally would make `no_global_section_exhaustive` pass vacuously. -/
theorem anyB_controls :
    anyB (fun b => b) = true ∧ anyB (fun _ => false) = false := ⟨rfl, rfl⟩

/-- The covectors NOT in the left kernel, counted by `kerCount`'s own nest. -/
def kerCountC : Nat :=
  countB fun y0 => countB fun y1 => countB fun y2 =>
  countB fun y3 => countB fun y4 => countB fun y5 =>
    cond (isCocycle (mkY y0 y1 y2 y3 y4 y5)) 0 1

/-- The strategy pairs NOT attaining 8, by `eightCount`'s own nest. -/
def eightCountC : Nat :=
  countB fun a0 => countB fun a1 => countB fun a2 =>
  countB fun a3 => countB fun a4 => countB fun a5 =>
  countB fun b0 => countB fun b1 => countB fun b2 =>
  countB fun b3 => countB fun b4 => countB fun b5 =>
    cond (gameScore a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5 == 8) 0 1

/-- The assignments NOT attaining 5, by `fiveCount`'s own nest. -/
def fiveCountC : Nat :=
  countB fun a => countB fun b => countB fun c =>
  countB fun d => countB fun e => countB fun f =>
  countB fun g => countB fun h => countB fun i =>
    cond (satBits a b c d e f g h i == 5) 0 1

/-- **THE COUNTS ARE GENUINELY "OUT OF" THEIR TOTALS.**  Each count plus its
    complement — computed by the *same* nest over the *same* predicate — equals
    the advertised total.  This is what makes 2/64, 144/4096 and 96/512 counts
    rather than numbers. -/
theorem counts_are_out_of_totals :
    kerCountC = 62 ∧ kerCount + kerCountC = yEnumSize ∧
    eightCountC = 3952 ∧ eightCount + eightCountC = pairCount ∧
    fiveCountC = 416 ∧ fiveCount + fiveCountC = assignCount :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **AN HONEST DEMOTION.**  `no_perfect_script` (`gameScore ≠ 9`) sounds like
    the content of item D, and is not: the score is always even, so `≠ 9` holds
    for parity reasons alone, independently of the ceiling.  The substantive
    pair is `gameScore_le_eight` together with `eight_attained`.  Recorded so
    the name cannot mislead a later reader.  (Score histogram over all 4096
    pairs: 0↦16, 2↦576, 4↦2016, 6↦1344, 8↦144 — all even.) -/
theorem gameScore_is_even (a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5 : Bool) :
    gameScore a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5 % 2 = 0 := by
  cases a0 <;> cases a1 <;> cases a2 <;> cases a3 <;> cases a4 <;> cases a5 <;>
    cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;>
    rfl

end Workshop.MagicSquare
