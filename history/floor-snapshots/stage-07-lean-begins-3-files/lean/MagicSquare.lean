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

end Workshop.MagicSquare
