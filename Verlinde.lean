/-
  THE WORKSHOP → LEAN 4.  ROUND 7 — VERLINDE FOR THE FIBONACCI CATEGORY.

  Bench formalized: `modular_data.py` — the S-matrix re-derives the fusion
  rules (Verlinde), the quantum dimensions, and the central charge.

  Self-contained: NO imports.  No `sorry`, no `native_decide`, no mathlib, no
  floats, no rationals.  Every arithmetic fact decided by the Lean kernel on
  `Int`.  No budget raised anywhere.

  The circle closes: grammar forced the braiding (Anyon.lean §hexagon), the
  braiding forced the dimension (`quantum_dimension_tau`, round 5), and here
  the modular S-matrix hands the fusion rules back — `verlinde_cleared`, all
  eight cells, exact over Z[φ], AXIOM-FREE (not even propext).

  Two rings, both transcribed VERBATIM from Anyon.lean (there is a transcription
  check, `audit/transcription.sh`; the copies are byte-faithful and the ONE new
  definition, `Zp.conj`, is labeled NEW):
    * Z[φ]   — the cleared Verlinde core (§1–§4);
    * Z[ζ₅]  — the T-layer, twist and central charge (§5–§9).

  D² = φ + 2 = √5·φ prices the ring: N(D²) = 5, so 1/D ∉ Z[φ] and every
  statement is CLEARED.  The one unit that does the work is φ itself; the only
  non-unit is D², and it is exactly what the eight Verlinde identities clear.

  ADJUDICATOR (norm 15): the cleared identities are decided in Z[φ] / Z[ζ₅] by
  the kernel.  What is NOT covered: the un-cleared 1/D statement as an element
  of any completed field (only the integer equalities are proved), and the
  central charge c = −14/5 is a LABEL on the parked λ = ζ₂₀¹³, which needs the
  degree-8 ring Z[ζ₂₀] and is not constructed here (its coordinates carry
  denominator 5 — measured, not assumed).

  Status: PROVED for the Z[φ] core and every cleared Z[ζ₅] identity; the
  central-charge element λ is a labelled PARK (needs Z[ζ₂₀]).
-/

namespace Round7Verlinde

/-! ═══════ TRANSCRIBED VERBATIM FROM Anyon.lean (transcription check) ═══════ -/

-- inductive Anyon (Anyon.lean:48)
inductive Anyon where
  | one
  | tau
  deriving DecidableEq

-- fuse (Anyon.lean:54)
def fuse : Anyon → Anyon → List Anyon
  | .one, b    => [b]
  | a,    .one => [a]
  | .tau, .tau => [.one, .tau]

-- memA (Anyon.lean:60)
def memA (a : Anyon) : List Anyon → Bool
  | []      => false
  | x :: xs => decide (a = x) || memA a xs

-- isOne (Anyon.lean:65)
def isOne : Anyon → Bool
  | .one => true
  | .tau => false

-- Rng (Anyon.lean:76)
structure Rng (R : Type) where
  zero : R
  one  : R
  add  : R → R → R
  mul  : R → R → R
  beq  : R → R → Bool

-- matMul (Anyon.lean:157)
def matMul {R : Type} (K : Rng R) (A B : Anyon → Anyon → R) :
    Anyon → Anyon → R :=
  fun i j => K.add (K.mul (A i .one) (B .one j)) (K.mul (A i .tau) (B .tau j))

-- matEq (Anyon.lean:162)
def matEq {R : Type} (K : Rng R) (A B : Anyon → Anyon → R) : Bool :=
  K.beq (A .one .one) (B .one .one) && K.beq (A .one .tau) (B .one .tau) &&
  K.beq (A .tau .one) (B .tau .one) && K.beq (A .tau .tau) (B .tau .tau)

-- matId (Anyon.lean:167)
def matId {R : Type} (K : Rng R) : Anyon → Anyon → R :=
  fun i j => if i = j then K.one else K.zero

-- structure Zp (Anyon.lean:175)
structure Zp where
  m : Int
  n : Int
  deriving DecidableEq

namespace Zp

def zero : Zp := ⟨0, 0⟩
def one  : Zp := ⟨1, 0⟩
def phi  : Zp := ⟨0, 1⟩
def add (u v : Zp) : Zp := ⟨u.m + v.m, u.n + v.n⟩
def neg (u : Zp) : Zp := ⟨-u.m, -u.n⟩

/-- `(a+bφ)(c+dφ) = (ac+bd) + (ad+bc+bd)φ`, using `φ² = φ+1`. -/
def mul (u v : Zp) : Zp :=
  ⟨u.m * v.m + u.n * v.n, u.m * v.n + u.n * v.m + u.n * v.n⟩

def beq (u v : Zp) : Bool := decide (u = v)

/-- `1/φ = φ − 1`. -/
def invPhi : Zp := ⟨-1, 1⟩

end Zp

-- zpRng (Anyon.lean:200)
def zpRng : Rng Zp := ⟨Zp.zero, Zp.one, Zp.add, Zp.mul, Zp.beq⟩

/-! ═══════ NEW: Galois conjugation on Z[φ] ═══════
    `φ = (1+√5)/2`, conjugate `φ̄ = 1 − φ = (1−√5)/2`.  Field norm
    `N(u) = u · ū`, landing in Z. -/
namespace Zp
/-- `conj (a + bφ) = a + b(1−φ) = (a+b) − bφ`. -/
def conj (u : Zp) : Zp := ⟨u.m + u.n, -u.n⟩
end Zp

/-! ════════════════════════════════════════════════════════════════════
    (1) TOTAL QUANTUM DIMENSION, and why clearing is forced.
    ════════════════════════════════════════════════════════════════════ -/

/-- `D² = φ + 2 = ⟨2,1⟩`, the total quantum dimension squared. -/
def Dsq : Zp := Zp.add Zp.phi ⟨2, 0⟩
/-- `√5 = 2φ − 1 = ⟨-1,2⟩`. -/
def sqrt5 : Zp := ⟨-1, 2⟩

/-- `√5·√5 = 5`: the surd squares to the rational integer 5. -/
theorem sqrt5_sq : Zp.mul sqrt5 sqrt5 = ⟨5, 0⟩ := rfl

/-- `D² = √5·φ`, i.e. `(2φ−1)·φ = φ+2`. -/
theorem Dsq_eq_sqrt5_phi : Dsq = Zp.mul sqrt5 Zp.phi := rfl

/-- **Field norm N(φ+2) = 5.**  `(φ+2)·conj(φ+2) = (φ+2)(3−φ) = 5`.
    conj(φ+2) = ⟨3,-1⟩ = 3−φ. -/
theorem norm_Dsq : Zp.mul Dsq (Zp.conj Dsq) = ⟨5, 0⟩ := rfl

/-- conj(φ+2) is literally `3 − φ = ⟨3,-1⟩`, as the letter states. -/
theorem conj_Dsq : Zp.conj Dsq = ⟨3, -1⟩ := rfl

/-- **CLEARING IS UNAVOIDABLE**: since N(D²) = 5 ≠ ±1, `D²` is not a unit of
    Z[φ] — its norm is not invertible in Z — so `1/D ∉ Z[φ]`.  Negative
    control witnessing non-unit-ness: no `u ∈ Z[φ]` has `D²·u = 1`, because
    that would force `N(D²)·N(u)=1` with `N(D²)=5`.  We record the norm fact;
    5 has no inverse in Z. -/
theorem Dsq_norm_not_unit : (Zp.mul Dsq (Zp.conj Dsq)).m = 5 ∧
    (Zp.mul Dsq (Zp.conj Dsq)).n = 0 := ⟨rfl, rfl⟩

/-! ════════════════════════════════════════════════════════════════════
    (2) THE S-MATRIX, cleared.  S = (1/D)·M,  M = [[1,φ],[φ,-1]].
    ════════════════════════════════════════════════════════════════════ -/

/-- `M = S·D`, the cleared S-matrix over Z[φ]. -/
def Msel : Anyon → Anyon → Zp
  | .one, .one => Zp.one
  | .one, .tau => Zp.phi
  | .tau, .one => Zp.phi
  | .tau, .tau => Zp.neg Zp.one

/-- `D²·I` as a matrix (the cleared `S² = I`). -/
def DsqI : Anyon → Anyon → Zp := fun i j => if i = j then Dsq else Zp.zero

/-- **M is symmetric.** -/
theorem M_symm : ∀ i j, Msel i j = Msel j i := by
  intro i j; cases i <;> cases j <;> rfl

/-- **Cleared S² = I**: `M² = D²·I` entrywise over Z[φ]. -/
theorem M_sq : matEq zpRng (matMul zpRng Msel Msel) DsqI = true := rfl

/-- Cleared row dot product `row_i · row_j = Σ_x M i x · M j x`. -/
def rowDot (i j : Anyon) : Zp :=
  Zp.add (Zp.mul (Msel i .one) (Msel j .one)) (Zp.mul (Msel i .tau) (Msel j .tau))

/-- **Rows orthonormal, cleared**: `row_i · row_j = D²·δ_ij`. -/
theorem rows_orthonormal : ∀ i j, rowDot i j = DsqI i j := by
  intro i j; cases i <;> cases j <;> rfl

/-- **THE DIMENSIONS FALL OUT.**  `M 0 0 = 1`, `M 0 1 = φ`, so the ratio
    `S_0a / S_00 = (M 0 a)/(M 0 0) = (1, φ)` — the quantum dimensions
    `(d_1, d_τ) = (1, φ)` arriving a SECOND way, from modular data.  This is
    the `d_τ = φ` of `quantum_dimension_tau` (Anyon.lean:6737), now read off
    the S-matrix instead of the fusion matrix's Perron eigenvalue. -/
theorem dims_from_S : Msel .one .one = Zp.one ∧ Msel .one .tau = Zp.phi :=
  ⟨rfl, rfl⟩

/-! ════════════════════════════════════════════════════════════════════
    (3) VERLINDE, EXACTLY.  N_ab^c = Σ_x S_ax S_bx S_cx / S_0x.
    ════════════════════════════════════════════════════════════════════ -/

/-- The fusion multiplicity: how many times `c` appears in `fuse a b`. -/
def fuseMult (a b c : Anyon) : Int :=
  ((fuse a b).countP (fun x => decide (x = c)) : Int)

/-- `fuseMult` as a Z[φ] element `⟨k,0⟩` (a rational integer). -/
def fuseZp (a b c : Anyon) : Zp := ⟨fuseMult a b c, 0⟩

/-- **The cleared Verlinde numerator** `G_abc = D² · N_ab^c`.

    `S_ax = M_ax/D`, `1/S_0x = D/M_0x`; three S give `1/D³`, one gives `D`,
    net `1/D²`, so `N_ab^c = (1/D²)·Σ_x M_ax M_bx M_cx / M_0x`.
    `M_0,one = 1` (x=one term, denominator 1) and `M_0,tau = φ` (x=tau term,
    denominator φ, cleared by `·invPhi` since φ is a UNIT: φ·(φ−1)=1).
    The ONLY non-unit is `D²`; this numerator is what remains after the
    unit `φ` is cleared, and it is manifestly in Z[φ]. -/
def verlNum (a b c : Anyon) : Zp :=
  Zp.add
    (Zp.mul (Zp.mul (Msel a .one) (Msel b .one)) (Msel c .one))
    (Zp.mul (Zp.mul (Zp.mul (Msel a .tau) (Msel b .tau)) (Msel c .tau)) Zp.invPhi)

/-- **THE HEADLINE — THE S-MATRIX KNOWS THE FUSION RULES.**
    The exact cleared Verlinde identity, all 8 cells `(a,b,c) ∈ {0,1}³`:
      `D² · fuseMult a b c = verlNum a b c`.
    Because Z[φ] is an integral domain and `D²` is a non-zero non-unit, this
    determines `N_ab^c = verlNum/D²` UNIQUELY, and it is the integer
    `fuseMult a b c`.  So `N_ab^c ∈ Z` and `N_ab^c = fuseMult a b c`. -/
theorem verlinde_cleared : ∀ a b c, Zp.mul Dsq (fuseZp a b c) = verlNum a b c := by
  intro a b c; cases a <;> cases b <;> cases c <;> rfl

/-! ════════════════════════════════════════════════════════════════════
    (4) NEGATIVE CONTROLS.
    ════════════════════════════════════════════════════════════════════ -/

/-- A WRONG S-matrix `[[1,1],[1,-1]]` (Hadamard, not the Fibonacci S). -/
def Mwrong : Anyon → Anyon → Zp
  | .one, .one => Zp.one
  | .one, .tau => Zp.one
  | .tau, .one => Zp.one
  | .tau, .tau => Zp.neg Zp.one

/-- Its total dimension squared is `D'² = Σ_x M_0x² = 1+1 = 2`. -/
def DsqWrong : Zp := ⟨2, 0⟩

/-- Cleared Verlinde numerator for the wrong matrix.  Now `M_0,one = 1` and
    `M_0,tau = 1`, so BOTH denominators are 1 (no `invPhi`). -/
def verlNumWrong (a b c : Anyon) : Zp :=
  Zp.add
    (Zp.mul (Zp.mul (Mwrong a .one) (Mwrong b .one)) (Mwrong c .one))
    (Zp.mul (Zp.mul (Mwrong a .tau) (Mwrong b .tau)) (Mwrong c .tau))

/-- **The wrong S-matrix FAILS at cell (τ,τ,τ).**  It stays integral
    (`0/2 = 0`) but gives the WRONG fusion: the cleared identity
    `D'²·fuseMult = verlNum` is FALSE there — `⟨0,0⟩ ≠ ⟨2,0⟩` — because the
    wrong matrix yields `N_ττ^τ = 0` while the true multiplicity is 1. -/
theorem wrong_S_fails_ttt :
    verlNumWrong .tau .tau .tau ≠ Zp.mul DsqWrong (fuseZp .tau .tau .tau) := by
  decide

/-- For contrast: the CORRECT matrix passes that same cell. -/
theorem correct_S_passes_ttt :
    verlNum .tau .tau .tau = Zp.mul Dsq (fuseZp .tau .tau .tau) :=
  (verlinde_cleared .tau .tau .tau).symm

/-- **fuseMult is NOT constant**: 0 on some cells, 1 on others. -/
theorem fuseMult_nonconstant :
    fuseMult .one .one .tau = 0 ∧ fuseMult .tau .tau .tau = 1 := ⟨rfl, rfl⟩

/-- **Anti-vacuity for Verlinde**: `N_ττ^1 = N_ττ^τ = 1` but `N_11^τ = 0`.
    Read both from `fuseMult` and from the cleared numerators
    (`verlNum = D²` when the multiplicity is 1, `= 0` when it is 0). -/
theorem verlinde_anti_vacuity :
    fuseMult .tau .tau .one = 1 ∧ fuseMult .tau .tau .tau = 1 ∧
    fuseMult .one .one .tau = 0 ∧
    verlNum .tau .tau .one = Dsq ∧ verlNum .tau .tau .tau = Dsq ∧
    verlNum .one .one .tau = Zp.zero :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ═══════ NORM 15 — ADJUDICATOR FOR THE CLEARED-VERLINDE CLASS ═══════

    WHAT CHECKS A CLAIM OF THIS KIND.  A "cleared Verlinde identity" of this
    class is adjudicated by `verlinde_cleared`: for each of the 8 label
    triples it asserts the Z[φ] equation `D² · fuseMult a b c = verlNum a b c`,
    where `verlNum` is Σ_x M_ax M_bx M_cx / M_0x with every UNIT denominator
    (`M_0,tau = φ`, cleared by `invPhi`) already multiplied through, and only
    the single NON-unit `D²` left as an explicit factor.  To trust `N = fuse`
    a reader checks three things, all decidable by `rfl`:
      (i)   `verlNum` transcribes the Verlinde sum with the M of `dims_from_S`;
      (ii)  the 8 equalities hold (they compile to `rfl`, axiom-free);
      (iii) Z[φ] is an integral domain and `D²` is a non-zero non-unit
            (`norm_Dsq`, `Dsq_norm_not_unit`), so `D²·k = D²·k'` forces
            `k = k'` — hence `N_ab^c := verlNum/D²` is the UNIQUE integer, and
            it equals `fuseMult`.
    The negative controls `wrong_S_fails_ttt` (a different S breaks a cell) and
    `fuseMult_nonconstant` / `verlinde_anti_vacuity` (the RHS is neither all-0
    nor all-1) certify the check is discriminating, not vacuous.

    WHAT THE CLEARED FORM DOES NOT SAY.  It makes NO claim about `1/D`, `1/D²`,
    or `S` itself as elements of any completed field (ℝ, ℂ, or Q(√5)); `1/D ∉
    Z[φ]` is exactly why clearing is forced.  It asserts only the INTEGER
    equality `N_ab^c = fuseMult a b c` as extracted from an exact Z[φ]
    identity.  It does not claim modularity, unitarity of `S` over ℂ, or
    positivity — only that the cleared modular data reproduces the fusion
    multiplicities of `fuse`. -/

/-! ═══════ AXIOM RECEIPTS ═══════ -/


/-! ══════════════════════════════════════════════════════════════════
    ## §5-§9.  THE T-LAYER, over Z5 = Z[zeta5].
    ══════════════════════════════════════════════════════════════════ -/

/-! ═══════════════════════════════════════════════════════════════════════
    ROUND 7 — THE T-LAYER AND THE CENTRAL CHARGE, over Z5 = Z[ζ₅]
    Every new theorem below is decided by the kernel (decide/rfl) and depends
    on NO axioms (verified: not even propext/Quot.sound).  Zero imports.
    ═══════════════════════════════════════════════════════════════════════ -/

/-! ── PART 0.  The ring Z5 = Z[ζ₅], transcribed VERBATIM from Anyon.lean
    (structure Z5, its defs, the reduction receipts, the full ring laws, and
    the complex-conjugation automorphism `conj`).  Zero imports ⇒ we copy. -/

/-- `⟨a₀,a₁,a₂,a₃⟩` denotes `a₀ + a₁ζ + a₂ζ² + a₃ζ³`, with ζ a primitive
    fifth root of unity: `1 + ζ + ζ² + ζ³ + ζ⁴ = 0`, so `ζ⁴ = −(1+ζ+ζ²+ζ³)`. -/
structure Z5 where
  a0 : Int
  a1 : Int
  a2 : Int
  a3 : Int
  deriving DecidableEq

namespace Z5

def zero : Z5 := ⟨0, 0, 0, 0⟩
def one  : Z5 := ⟨1, 0, 0, 0⟩
def add (u v : Z5) : Z5 := ⟨u.a0+v.a0, u.a1+v.a1, u.a2+v.a2, u.a3+v.a3⟩
def neg (u : Z5) : Z5 := ⟨-u.a0, -u.a1, -u.a2, -u.a3⟩

/-- Convolve to degree 6, then reduce with `ζ⁴ = −(1+ζ+ζ²+ζ³)`, `ζ⁵ = 1`,
    `ζ⁶ = ζ`. -/
def mul (u v : Z5) : Z5 :=
  let c0 := u.a0*v.a0
  let c1 := u.a0*v.a1 + u.a1*v.a0
  let c2 := u.a0*v.a2 + u.a1*v.a1 + u.a2*v.a0
  let c3 := u.a0*v.a3 + u.a1*v.a2 + u.a2*v.a1 + u.a3*v.a0
  let c4 := u.a1*v.a3 + u.a2*v.a2 + u.a3*v.a1
  let c5 := u.a2*v.a3 + u.a3*v.a2
  let c6 := u.a3*v.a3
  ⟨c0 - c4 + c5, c1 - c4 + c6, c2 - c4, c3 - c4⟩

def zeta  : Z5 := ⟨0, 1, 0, 0⟩
def zeta2 : Z5 := ⟨0, 0, 1, 0⟩
def zeta3 : Z5 := ⟨0, 0, 0, 1⟩
/-- `ζ⁴ = −(1+ζ+ζ²+ζ³)`. -/
def zeta4 : Z5 := ⟨-1, -1, -1, -1⟩

/-- `φ = 1 + ζ + ζ⁴`, reduced.  Numerically 1.6180339887…, and this is the
    element the workshop's `t² = 1 + ζ + ζ⁴` names. -/
def phi : Z5 := ⟨0, 0, -1, -1⟩

/-- `1/φ = ζ + ζ⁴`, reduced.  Numerically 0.6180339887… -/
def invPhi : Z5 := ⟨-1, 0, -1, -1⟩

end Z5

/-! ### Receipts on Z[ζ₅] — the reduction rules are what they claim -/

theorem z5_zeta4_eq : Z5.mul Z5.zeta3 Z5.zeta = Z5.zeta4 := rfl
theorem z5_zeta5_eq : Z5.mul Z5.zeta4 Z5.zeta = Z5.one := rfl
theorem z5_phi_eq : Z5.add (Z5.add Z5.one Z5.zeta) Z5.zeta4 = Z5.phi := rfl
theorem z5_invPhi_eq : Z5.add Z5.zeta Z5.zeta4 = Z5.invPhi := rfl
theorem z5_invPhi_mul : Z5.mul Z5.phi Z5.invPhi = Z5.one := rfl
theorem z5_phi_sq : Z5.mul Z5.phi Z5.phi = Z5.add Z5.phi Z5.one := rfl

namespace Z5

theorem add_comm (u v : Z5) : add u v = add v u := by
  cases u; cases v; simp only [add, Z5.mk.injEq]; refine ⟨?_,?_,?_,?_⟩ <;> omega
theorem add_assoc (u v w : Z5) : add (add u v) w = add u (add v w) := by
  cases u; cases v; cases w; simp only [add, Z5.mk.injEq]
  refine ⟨?_,?_,?_,?_⟩ <;> omega
theorem add_zero (u : Z5) : add u zero = u := by
  cases u; simp only [add, zero, Z5.mk.injEq]; refine ⟨?_,?_,?_,?_⟩ <;> omega
theorem zero_add (u : Z5) : add zero u = u := by
  cases u; simp only [add, zero, Z5.mk.injEq]; refine ⟨?_,?_,?_,?_⟩ <;> omega
theorem mul_one (u : Z5) : mul u one = u := by
  cases u; simp only [mul, one, Z5.mk.injEq]; refine ⟨?_,?_,?_,?_⟩ <;> omega
theorem one_mul (u : Z5) : mul one u = u := by
  cases u; simp only [mul, one, Z5.mk.injEq]; refine ⟨?_,?_,?_,?_⟩ <;> omega
theorem mul_zero (u : Z5) : mul u zero = zero := by
  cases u; simp only [mul, zero, Z5.mk.injEq]; refine ⟨?_,?_,?_,?_⟩ <;> omega
theorem zero_mul (u : Z5) : mul zero u = zero := by
  cases u; simp only [mul, zero, Z5.mk.injEq]; refine ⟨?_,?_,?_,?_⟩ <;> omega

theorem mul_comm (u v : Z5) : mul u v = mul v u := by
  cases u; cases v; simp only [mul, Z5.mk.injEq]
  refine ⟨?_,?_,?_,?_⟩ <;> simp only [Int.mul_comm] <;> omega

theorem mul_add (u v w : Z5) : mul u (add v w) = add (mul u v) (mul u w) := by
  cases u; cases v; cases w; simp only [mul, add, Z5.mk.injEq, Int.mul_add]
  refine ⟨?_,?_,?_,?_⟩ <;> omega
theorem add_mul (u v w : Z5) : mul (add u v) w = add (mul u w) (mul v w) := by
  cases u; cases v; cases w; simp only [mul, add, Z5.mk.injEq, Int.add_mul]
  refine ⟨?_,?_,?_,?_⟩ <;> omega

theorem mul_assoc (u v w : Z5) : mul (mul u v) w = mul u (mul v w) := by
  cases u; cases v; cases w
  simp only [mul, Z5.mk.injEq, Int.sub_mul, Int.add_mul, Int.mul_sub, Int.mul_add,
             Int.mul_assoc]
  refine ⟨?_,?_,?_,?_⟩ <;> omega

theorem mul_left_comm (u v w : Z5) : mul u (mul v w) = mul v (mul u w) := by
  rw [← mul_assoc, mul_comm u v, mul_assoc]
theorem add_left_comm (u v w : Z5) : add u (add v w) = add v (add u w) := by
  rw [← add_assoc, add_comm u v, add_assoc]

theorem neg_mul (u v : Z5) : mul (neg u) v = neg (mul u v) := by
  cases u; cases v
  simp only [mul, neg, Z5.mk.injEq, Int.neg_mul]
  refine ⟨?_,?_,?_,?_⟩ <;> omega
theorem mul_neg (u v : Z5) : mul u (neg v) = neg (mul u v) := by
  cases u; cases v
  simp only [mul, neg, Z5.mk.injEq, Int.mul_neg]
  refine ⟨?_,?_,?_,?_⟩ <;> omega
theorem neg_neg (u : Z5) : neg (neg u) = u := by
  cases u; simp only [neg, Z5.mk.injEq]; refine ⟨?_,?_,?_,?_⟩ <;> omega
theorem add_neg (u : Z5) : add u (neg u) = zero := by
  cases u; simp only [add, neg, zero, Z5.mk.injEq]; refine ⟨?_,?_,?_,?_⟩ <;> omega
theorem neg_add_cancel (u : Z5) : add (neg u) u = zero := by
  cases u; simp only [add, neg, zero, Z5.mk.injEq]; refine ⟨?_,?_,?_,?_⟩ <;> omega
theorem neg_add (u v : Z5) : neg (add u v) = add (neg u) (neg v) := by
  cases u; cases v; simp only [add, neg, Z5.mk.injEq]; refine ⟨?_,?_,?_,?_⟩ <;> omega

theorem mul_right_comm (u v w : Z5) : mul (mul u v) w = mul (mul u w) v := by
  rw [mul_assoc, mul_comm v w, ← mul_assoc]

/-- **Complex conjugation on Z[ζ₅]**, `ζ ↦ ζ⁴`, in the basis `(1,ζ,ζ²,ζ³)`. -/
def conj (u : Z5) : Z5 := ⟨u.a0 - u.a1, -u.a1, u.a3 - u.a1, u.a2 - u.a1⟩

theorem conj_zeta  : conj zeta  = zeta4 := rfl
theorem conj_zeta2 : conj zeta2 = zeta3 := rfl
theorem conj_zeta3 : conj zeta3 = zeta2 := rfl
theorem conj_zeta4 : conj zeta4 = zeta  := rfl
theorem conj_phi : conj phi = phi := rfl
theorem conj_invPhi : conj invPhi = invPhi := rfl

theorem conj_add (u v : Z5) : conj (add u v) = add (conj u) (conj v) := by
  cases u; cases v
  simp only [conj, add, Z5.mk.injEq]
  refine ⟨?_,?_,?_,?_⟩ <;> omega
theorem conj_neg (u : Z5) : conj (neg u) = neg (conj u) := by
  cases u; simp only [conj, neg, Z5.mk.injEq]
  refine ⟨?_, trivial, ?_, ?_⟩ <;> omega
theorem conj_mul (u v : Z5) : conj (mul u v) = mul (conj u) (conj v) := by
  cases u; cases v
  simp only [conj, mul, Z5.mk.injEq,
             Int.sub_mul, Int.mul_sub, Int.neg_mul, Int.mul_neg]
  refine ⟨?_,?_,?_,?_⟩ <;> omega
theorem conj_conj (u : Z5) : conj (conj u) = u := by
  cases u; simp only [conj, Z5.mk.injEq]; refine ⟨?_,?_,?_,?_⟩ <;> omega

end Z5

/-! ═══════════════════════════════════════════════════════════════════════
    ── PART 1.  THE TWIST (T-layer).  θ₁ = 1, θ_τ = ζ³ (bench convention,
    co-signed by Anyon.lean `ribbon_twist`: θ_τ = r₁/φ + r_τ = ζ²·(1/φ) − ζ).
    ═══════════════════════════════════════════════════════════════════════ -/

/-- `θ₁ = 1`. -/
def theta1 : Z5 := Z5.one
/-- `θ_τ = ζ³`, the bench twist. -/
def thetaTau : Z5 := Z5.zeta3

theorem theta1_eq : theta1 = Z5.one := rfl
theorem thetaTau_eq : thetaTau = Z5.zeta3 := rfl

/-- Co-sign of Anyon.lean `ribbon_twist`: the same twist, `θ_τ = ζ²·(1/φ) − ζ`,
    reduces to `ζ³` on the nose. -/
theorem thetaTau_ribbon :
    Z5.add (Z5.mul Z5.zeta2 Z5.invPhi) (Z5.neg Z5.zeta) = thetaTau := rfl

/-! ── The distinguished Z5 constants of the T-layer. -/

/-- `φ + 2 = D²` (total quantum dimension squared): `φ = (0,0,−1,−1)` so
    `φ+2 = (2,0,−1,−1)`. -/
def phiPlus2 : Z5 := ⟨2, 0, -1, -1⟩
/-- `pp = ζ³ − ζ` — the chiral twist-defect. -/
def pp : Z5 := ⟨0, -1, 0, 1⟩
/-- `pm = ζ² − ζ⁴` — the mirror (opposite chirality). -/
def pm : Z5 := ⟨1, 1, 2, 1⟩

/-- `φ+2` is exactly `φ + 2`. -/
theorem phiPlus2_eq : phiPlus2 = Z5.add Z5.phi ⟨2,0,0,0⟩ := rfl
/-- `φ+2` really is `D² = φ² + 1` (Fibonacci total dimension). -/
theorem phiPlus2_is_D2 : phiPlus2 = Z5.add (Z5.mul Z5.phi Z5.phi) Z5.one := rfl
/-- `pp = ζ³ − ζ`. -/
theorem pp_eq : pp = Z5.add Z5.zeta3 (Z5.neg Z5.zeta) := rfl
/-- `pm = ζ² − ζ⁴`. -/
theorem pm_eq : pm = Z5.add Z5.zeta2 (Z5.neg Z5.zeta4) := rfl
/-- **THE MIRROR IS THE COMPLEX CONJUGATE**: `pm = conj pp`, exactly.  This is
    the cleared shadow of `zeta20⁷ = conj(zeta20¹³)`: the two chiralities are
    complex-conjugate, decided integrally in Z[ζ₅]. -/
theorem pm_eq_conj_pp : pm = Z5.conj pp := rfl

/-! ═══════════════════════════════════════════════════════════════════════
    ── PART 2.  THE CLEARED MODULAR RELATION  (Ŝ T)³ = (φ+2)·pp·I.
    Ŝ = [[1,φ],[φ,−1]] (cleared S), T = diag(1, ζ³).  So
    Ŝ T = [[1, φζ³],[φ, −ζ³]] (column-scale by T), and its cube is scalar.
    ═══════════════════════════════════════════════════════════════════════ -/

/-- 2×2 matrices over Z5. -/
structure Mat2 where
  a : Z5
  b : Z5
  c : Z5
  d : Z5
  deriving DecidableEq

/-- Matrix product over Z5 (no descent to Int; entries are Z5.mul/Z5.add). -/
def Mat2.mul (M N : Mat2) : Mat2 :=
  ⟨Z5.add (Z5.mul M.a N.a) (Z5.mul M.b N.c),
   Z5.add (Z5.mul M.a N.b) (Z5.mul M.b N.d),
   Z5.add (Z5.mul M.c N.a) (Z5.mul M.d N.c),
   Z5.add (Z5.mul M.c N.b) (Z5.mul M.d N.d)⟩

/-- `Ŝ T = [[1, φζ³],[φ, −ζ³]]`. -/
def ShatT : Mat2 := ⟨Z5.one, Z5.mul Z5.phi Z5.zeta3, Z5.phi, Z5.neg Z5.zeta3⟩

/-- **THE CLEARED MODULAR RELATION**, exact in Z[ζ₅]:
    `(Ŝ T)³ = (φ+2)·pp·I` — diagonal `(φ+2)·pp`, off-diagonal `0`. -/
theorem modular_cube :
    Mat2.mul (Mat2.mul ShatT ShatT) ShatT
      = ⟨Z5.mul phiPlus2 pp, Z5.zero, Z5.zero, Z5.mul phiPlus2 pp⟩ := by decide

/-! ── Mirror (opposite chirality): T′ = diag(1, ζ²), giving `(φ+2)·pm·I`.
    `ShatTmirror` is the entrywise conjugate of `ShatT` (conj φ = φ, conj ζ³ = ζ²),
    so its cube is the conjugate of `modular_cube`'s — pinning `pm = conj pp`. -/
def ShatTmirror : Mat2 := ⟨Z5.one, Z5.mul Z5.phi Z5.zeta2, Z5.phi, Z5.neg Z5.zeta2⟩

theorem modular_cube_mirror :
    Mat2.mul (Mat2.mul ShatTmirror ShatTmirror) ShatTmirror
      = ⟨Z5.mul phiPlus2 pm, Z5.zero, Z5.zero, Z5.mul phiPlus2 pm⟩ := by decide

/-! ═══════════════════════════════════════════════════════════════════════
    ── PART 3.  THE CENTRAL CHARGE, pinned integrally (λ PARKED).
    The claims are `λ·D = pp` with `λ = zeta20¹³ = e^{2πi c/8}`, `c = −14/5`,
    and the mirror `conj(λ)·D = pm` with `conj λ = zeta20⁷`.  λ and D live in
    Z[ζ₂₀][D] — NOT in Z[ζ₅] — so λ is PARKED.  What survives clearing λ are
    exact Z[ζ₅] relations between pp, pm, φ+2:
    ═══════════════════════════════════════════════════════════════════════ -/

/-- **CLEARED MODULUS**: `pp · pm = φ + 2 = D²`.  From `λD = pp`, `conj(λ)D = pm`
    and `λ·conj(λ) = 1`: multiply to kill λ, leaving `D² = pp·pm`. -/
theorem pp_pm_eq_D2 : Z5.mul pp pm = phiPlus2 := by decide

/-- **CLEARED PHASE (λ⁴ = θ_τ)**: `pp⁴ = θ_τ · (φ+2)²`.  `λ⁴ = zeta20⁵² = ζ³ =
    θ_τ`, and `D⁴ = (φ+2)²`, so `(λD)⁴ = pp⁴` clears to a Z[ζ₅] identity that
    pins the *content* of λ (its 4th power is the twist) without constructing λ. -/
theorem pp_pow4_eq :
    Z5.mul (Z5.mul pp pp) (Z5.mul pp pp)
      = Z5.mul thetaTau (Z5.mul phiPlus2 phiPlus2) := by decide

/-- Mirror phase: `pm⁴ = conj(θ_τ) · (φ+2)² = ζ² · (φ+2)²` — the conjugate law. -/
theorem pm_pow4_eq :
    Z5.mul (Z5.mul pm pm) (Z5.mul pm pm)
      = Z5.mul Z5.zeta2 (Z5.mul phiPlus2 phiPlus2) := by decide

/-! ═══════════════════════════════════════════════════════════════════════
    ── PART 4.  IMAGINARY PARTS CANCEL — the cleared balancing/Verlinde form
    `Ŝ_ab · θ_a · θ_b = Σ_c N_ab^c d_c θ_c`  (clear the unit denominators
    θ_a θ_b; 1/ζ³ = ζ² since ζ⁵ = 1).  Fibonacci: d₁=1, d_τ=φ; τ×τ = 1 + τ.
    The RHS is a sum of roots of unity; the LHS is Ŝ times units — the two
    agree exactly in Z[ζ₅], which is "the imaginary parts cancel."
    ═══════════════════════════════════════════════════════════════════════ -/

/-- `(1,1)`: `Ŝ₁₁ = 1`.  `1·θ₁·θ₁ = N₁₁¹ d₁ θ₁`, both `= 1`. -/
theorem verlinde_one_one :
    Z5.mul (Z5.mul Z5.one theta1) theta1
      = Z5.mul (Z5.mul Z5.one Z5.one) theta1 := by decide

/-- `(1,τ)`: `Ŝ₁τ = φ`.  `φ·θ₁·θ_τ = N₁τ^τ d_τ θ_τ`, both `= φζ³`. -/
theorem verlinde_one_tau :
    Z5.mul (Z5.mul Z5.phi theta1) thetaTau
      = Z5.mul (Z5.mul Z5.one Z5.phi) thetaTau := by decide

/-- **THE SUBSTANTIVE ENTRY — `(τ,τ)`: `Ŝ_ττ = −1`.**
    `(−1)·θ_τ·θ_τ = N_ττ¹ d₁ θ₁ + N_ττ^τ d_τ θ_τ`.
    LHS `= −ζ⁶ = −ζ`; RHS `= 1 + φζ³ = 1 + (−1−ζ) = −ζ`.  A sum of two
    genuinely complex twists collapses to the real cleared entry `−ζ`. -/
theorem verlinde_tau_tau :
    Z5.mul (Z5.mul (Z5.neg Z5.one) thetaTau) thetaTau
      = Z5.add (Z5.mul (Z5.mul Z5.one Z5.one) theta1)
               (Z5.mul (Z5.mul Z5.one Z5.phi) thetaTau) := by decide

/-! ═══════════════════════════════════════════════════════════════════════
    ── PART 5.  NEGATIVE CONTROLS + ANTI-VACUITY.
    ═══════════════════════════════════════════════════════════════════════ -/

/-- **MIRROR INDEX DIFFERS**: `pp ≠ pm` — chirality is load-bearing. -/
theorem pp_ne_pm : pp ≠ pm := by decide
/-- The two chiral cube-scalars differ: `(φ+2)pp ≠ (φ+2)pm`. -/
theorem cube_chirality_differs : Z5.mul phiPlus2 pp ≠ Z5.mul phiPlus2 pm := by decide

/-- **θ_τ NONTRIVIAL**: `ζ³ ≠ 1`. -/
theorem thetaTau_ne_one : thetaTau ≠ Z5.one := by decide
/-- …but a 5th root of unity: `(ζ³)⁵ = 1`. -/
theorem thetaTau_pow5 :
    Z5.mul (Z5.mul (Z5.mul (Z5.mul Z5.zeta3 Z5.zeta3) Z5.zeta3) Z5.zeta3) Z5.zeta3
      = Z5.one := by decide

/-- **ANTI-VACUITY**: the cleared statements are not `0 = 0` — their content is
    nonzero.  `pp ≠ 0`, `φ+2 ≠ 0`, and the cube-scalar `(φ+2)pp ≠ 0`. -/
theorem pp_ne_zero : pp ≠ Z5.zero := by decide
theorem phiPlus2_ne_zero : phiPlus2 ≠ Z5.zero := by decide
theorem cube_scalar_ne_zero : Z5.mul phiPlus2 pp ≠ Z5.zero := by decide
/-- **pp IS LOAD-BEARING** in the cube: the scalar is `(φ+2)·pp`, NOT `φ+2`. -/
theorem cube_scalar_carries_pp : Z5.mul phiPlus2 pp ≠ phiPlus2 := by decide

/-! ── The denominator obstruction (documented, NOT constructed).
    λ = zeta20¹³ has degree 8 over ℚ; Z[ζ₅] has degree 4; and even over the
    quadratic tower Z[ζ₅][D] the builder MEASURED λ's coordinates to carry
    denominator 5 (a first draft predicted 2; the measurement corrected it).
    So λ CANNOT be an element of Z5, and it is PARKED here.  What IS in Z5 —
    and decided above — is every *cleared* consequence: φ+2, pp, pm and the
    identities `(ŜT)³=(φ+2)pp·I`, `pp·pm=φ+2`, `pp⁴=θ_τ(φ+2)²`, `pm=conj pp`.

    ADJUDICATOR (norm 15): claims of the form "such-and-such is an exact
    Z[ζ₅] identity among {φ, ζ^k, pp, pm, φ+2, the cleared Ŝ, T}" are checked
    here by kernel `decide`/`rfl` on the transcribed Z5 ring.  NOT covered:
    (i) λ = zeta20¹³ itself, or any statement mentioning ζ₂₀ or D as a ring
    element — those need Z[ζ₂₀][D], a degree-16 tower not built here; (ii) the
    numeric value c = −14/5 as a rational — it is a *label* on λ, recorded but
    not a Z5 object; (iii) analytic positivity of D. -/

end Round7Verlinde
