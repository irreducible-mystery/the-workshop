/-
  THE WORKSHOP → LEAN 4.  ROUND 6 — HESSIAN RIGIDITY AS A KERNEL-CHECKED
  THEOREM.

  Bench formalized: `grammar_stone5.py`'s numerically-asserted signature
  {0,+,+,+} of the 4×4 Hessian of the pentagon sum-of-squares residual, at the
  pentagon solutions.  Builder's certification: `audit/r6_gift_hessian.py`
  (40/40 PASS).  Round-5 order technology reused verbatim: `Ord5`, `Zp.pos`.

  Self-contained: NO imports.  No `sorry`, no `native_decide`, no mathlib, no
  floats, no rationals, no reals.  Every arithmetic fact is decided by the
  Lean kernel on `Int`.  No budget (`maxHeartbeats`, `maxRecDepth`, simp
  budget) is raised anywhere.

  ══════════════════════════════════════════════════════════════════════════
  WHAT THIS FILE'S HEADLINE THEOREM SAYS

  Let `SS(p,q,r,s)` be the pentagon sum-of-squares residual: sum over all 512
  label tuples of `(LHS − RHS)²` of `pentagonCheck` for the generic associator
  `Fg p q r s = [[p,q],[r,s]]`.  Let `H` be its exact 4×4 Hessian at a point,
  computed by second-order jets (`J2`) — i.e. `H` is the kernel's own second
  derivative of `SS`, not an assertion about one.  That holds as stated at
  ALL FOUR worlds, golden included.  (At the golden world the route is
  slightly longer: the whole-structure `rfl` `germ epRng … = GG` and the
  indexed form `hess epRng … i j = HG i j` DO overrun the default heartbeat
  budget, but the fifteen FIELD PROJECTIONS `(germ epRng …).eIJ = …` each
  close by `rfl` at the default budget, and `J2.ext'` glues them back into
  the whole-structure equation.  No budget is raised.  See §9 and the
  docstring on `HG`.)

  At the YANG–LEE solution `(p,q,r,s) = (−φ, 1, −φ, φ)` — a genuine pentagon
  solution, all 512 instances of `pentagonCheck` true — the exact Hessian `H`
  over the ordered field `Q(√5)` is

    * POSITIVE SEMIDEFINITE:  `wᵀHw ≥ 0` for every `w : Z[φ]⁴`;
    * with NULL SPACE EXACTLY the gauge-torus tangent:  `wᵀHw = 0` iff
      `w₀ = 0`, `w₃ = 0`, `w₁·r + w₂·q = 0` — i.e. `w ∈ span(0,q,−r,0)`;
    * of RANK EXACTLY 3:  `det H = 0` and a 3×3 principal minor is `> 0`;
    * and — this is the part that carries the weight — the `q↔r` SWAP
      direction `(0,1,−1,0)` is NOT null there:  `H·(0,1,−1,0) ≠ 0` and
      `(0,1,−1,0)ᵀ H (0,1,−1,0) > 0`.

  ══════════════════════════════════════════════════════════════════════════
  WHAT IT DOES **NOT** SAY — read this before quoting the theorem

  (a) It says NOTHING about basins, gradient dynamics, convergence of any
      search, global minimality, or behaviour anywhere off the two solution
      points.  It is the SECOND-ORDER GERM at two exact points, only.

  (b) It is NOT a solution-detector, and the hypothesis "the point is a
      pentagon solution" is LOAD-BEARING.  The builder's planned negative
      control REFUTED the first draft of the charge: at the strict associator
      `(1,1,1,1)` — a NON-solution, `SS = 17 ≠ 0`, gradient ≠ 0 — the Hessian
      is ALSO positive semidefinite with null space exactly `span(0,1,−1,0)`.
      That specimen is in this file (`HS`, `strict_also_psd`,
      `strict_also_rank3`), stated as a theorem, precisely so that nobody can
      read the signature as detecting solutionhood.

  (c) At the GOLDEN world `q = r`, the null direction is a SYMMETRY FREEBIE,
      not content.  `SS` is `q↔r` swap-invariant (mechanism proved in §6 at
      the residual level, `pentResid_rev`; the last step to `SS` itself is a
      named gap there), so at any `q = r` point columns `q` and `r` of `H`
      coincide — decided here for every such specimen — and `(0,1,−1,0)` is
      null for free, by `swapDir_null_of_cols_eq`.  The
      CONTENT at golden is the pair (rank exactly 3) + (positivity on a
      complement).  The null-space-equals-gauge-tangent claim carries its full
      weight EXACTLY AT YANG–LEE, where `q ≠ r` and the swap direction is
      provably not null.  Do not quote the golden null direction as evidence.

  (d) The positive-semidefiniteness quantifier ranges over `Z[φ]⁴`
      (equivalently `Q(√5)⁴`, by clearing denominators — every statement here
      is homogeneous of degree 2 in `w`).  It is not a statement about `ℝ⁴`;
      no real number appears in this file.

  ══════════════════════════════════════════════════════════════════════════
  ADJUDICATORS (house norm 15 — every new artifact class names, at birth,
  what checks sentences of its kind and what that check does not cover).

  * `Zp` = `Z[φ]`, and its order `Zp.pos`.  ADJUDICATOR: `Ord5.posUN_iff`
    plus `Zp.trichotomy` — a claim `Zp.pos a = true` is settled by integer
    arithmetic (`a = (u + n√5)/2`, compare `u²` against `5n²`), and
    `Zp.phi_bracket` pins the semantics to `1.618 < φ < 1.619` so the order is
    the real one and not some other total order.  This does NOT certify any
    claim about elements outside `Z[φ]`, and says nothing about `Q(√5)(√φ)`.

  * `Ep` = `Z[φ][s]/(s² − φ)`, and its order `Ep.pos`.  ADJUDICATOR:
    `Ep.pos_iff` + `Ep.trichotomy`, which reduce the sign of `x + y·s` to two
    `Zp.pos` calls plus, in the mixed case, the sign of `x² − φy²` — legitimate
    exactly because `Ep.no_sqrtPhi` proves `x² = φy² ⟹ x = y = 0`.  The
    semantics is pinned to the real `√φ` by `Ep.rad_bracket` and its negative
    control `Ep.rad_bracket_tight`, and `Ep.wrong_radicand_miscalls` shows the
    radicand `φ` is load-bearing.  What this does NOT cover: `Ep.pos` is NOT
    proved closed under addition or under multiplication — the analogues of
    `Ord5.posP_add_*` and `Ord5.posP_mul_*` one level up are NOT ATTEMPTED
    here.  No theorem in this file uses them, and §9 is written so that it
    does not need them; see §9's header.

  * `germ` / `hess` — the second-order jet germ of `SS` at a point.
    ADJUDICATOR: `rfl` in the Lean kernel.  `germ` is a computation, so
    `germ_Y`-style theorems are decided, not asserted; `hess` is *defined* as
    the germ's second-order coefficients, so "H is the Hessian" is true by
    construction and there is nothing analytic left to trust.  This now holds
    at the golden world too (`germ_G`, `hess_G`), reached slot-by-slot
    through `J2.ext'` rather than in one `rfl`.  What this does NOT cover:
    the germ is a formal second derivative of a POLYNOMIAL; it carries no
    analytic content (no Taylor remainder, no neighbourhood).

  * The SOS certificates `sos_Y`, `sos_S`, `sos_G` — matrix identities
    `N·H = e₁·L₁⊗L₁ + e₂·L₂⊗L₂ + e₃·L₃⊗L₃` with `N, eᵢ > 0`.  ADJUDICATOR:
    `decide` on the ring entries, plus `Zp.pos` / `Ep.pos` on the four
    scalars.  Over `Z[φ]` the certificate is then CONSUMED by `psd_of_sos`
    and `ker_of_sos` (§4), which is where it becomes a `∀ w` theorem; over
    `E` it stands alone, because those two lemmas need order closure that §8
    does not deliver.  What this does NOT cover: a failure of the certificate
    is not a proof that the matrix is indefinite — the control point `HC`
    shows the certificate genuinely failing (`det H ≠ 0`), and indefiniteness
    there is proved separately by exhibiting `w` with `wᵀHw < 0`.

  Status: PROVED throughout — the Yang–Lee world, the two negative controls,
  the ordered-field extension, AND the golden world.  The golden Hessian is
  no longer transcribed: `germ_G` and `hess_G` (§9) derive `HG` from the
  kernel's own `E`-valued germ, at the DEFAULT heartbeat budget, exactly as
  `germ_Y` / `hess_Y` do over `Z[φ]`.

  What is true about the budget there, stated precisely because an earlier
  revision of this header overstated it: TWO specific forms do overrun the
  default budget over `E` — the whole-structure `germ epRng pG qG qG sG = GG
  := by rfl`, and the indexed entry form `hess epRng pG qG qG sG i j = HG i j
  := by rfl`.  Both were re-checked and both do fail; neither is needed.  The
  FIFTEEN field projections `(germ epRng pG qG qG sG).v/.d0…/.e00…e33 = …`
  each close by `rfl` well inside the default budget (~30–35 s of kernel
  reduction apiece when forced in isolation), because a projection out of
  `SS`'s jet result forces only the sub-fields that slot depends on.
  `J2.ext'` (§3) glues the fifteen back into the whole-structure equation by
  structure eta, and `hess_G` then rewrites `hessOf` along it — the same
  two-line shape as `hess_Y`, `hess_S`, `hess_C`.  No budget is raised
  anywhere in this file.

  COST, measured (Lean 4.32.0, headless `lean Rigidity.lean`, one core, two
  runs each): the whole file compiles in 3 min 49 s – 4 min 24 s, against
  2 min 10 s – 2 min 20 s for the revision that transcribed `GG`.  The ten
  second-order projections are therefore worth roughly 100–130 s in a full
  run — far less than ten times their isolated cost, because the slots share
  the bulk of their reduction.  Still comfortably a single-file compile.

  Two further gaps, both named where they occur: `Ep.pos` is not proved
  closed under `+` or `×` (§8; nothing here uses it), and the step from
  `pentResid_rev` to full `q↔r` invariance of `SS` needs a permutation lemma
  for nine nested sums that this file does not contain (§6; every `q = r`
  specimen here has its consequence decided instead).
-/

/-- The two labels of the Fibonacci fusion category. -/
inductive Anyon where
  | one
  | tau
  deriving DecidableEq

namespace Workshop.R6

/-! ══════════════════════════════════════════════════════════════════════
    ## §0.  TRANSCRIPTION — the pentagon machinery, verbatim from
    `Anyon.lean` (`fuse`, `memA`, `isOne`, `Rng`, `sumOver`, `Fs`,
    `pentagonValid`, `pentagonCheck`, `Fg`, `Zp`).

    Nothing here is new.  It is copied so this file can be checked with zero
    imports; the canonical statements live in `Anyon.lean` and this file
    points at them rather than re-deriving them.
    ══════════════════════════════════════════════════════════════════════ -/

/-- Fusion: `τ × τ = 1 + τ`, the vacuum is the unit. -/
def fuse : Anyon → Anyon → List Anyon
  | .one, b    => [b]
  | a,    .one => [a]
  | .tau, .tau => [.one, .tau]

def memA (a : Anyon) : List Anyon → Bool
  | []      => false
  | x :: xs => decide (a = x) || memA a xs

def isOne : Anyon → Bool
  | .one => true
  | .tau => false

/-- A commutative ring's operations, as data.  `Anyon.lean`'s `Rng` carries
    `beq` where this one carries `neg`; the residual `LHS − RHS` needs a
    negation and nothing below needs a Boolean equality, so this is the one
    deliberate deviation from the transcription.  Flagged here, not hidden. -/
structure Rng (R : Type) where
  zero : R
  one  : R
  add  : R → R → R
  neg  : R → R
  mul  : R → R → R

def sumOver {R : Type} (K : Rng R) (f : Anyon → R) : List Anyon → R
  | []      => K.zero
  | u :: us => K.add (f u) (sumOver K f us)

/-- **The F-move**, transcribed from the workshop's executable specification. -/
def Fs {R : Type} (K : Rng R) (F : Anyon → Anyon → R)
    (a b c d x y : Anyon) : R :=
  if memA x (fuse a b) && memA d (fuse x c) &&
     memA y (fuse b c) && memA d (fuse a y) then
    if isOne a || isOne b || isOne c then K.one
    else if isOne d then (if !isOne x && !isOne y then K.one else K.zero)
    else F x y
  else K.zero

/-- The pentagon's index guard.  50 of the 512 tuples pass. -/
def pentagonValid (a b c dd x y t w v : Anyon) : Bool :=
  memA x (fuse a b) && memA y (fuse x c) && memA t (fuse y dd) &&
  memA w (fuse c dd) && memA v (fuse b w) && memA t (fuse a v)

/-- The generic associator `[[p,q],[r,s]]`. -/
def Fg {R : Type} (p q r sp : R) : Anyon → Anyon → R
  | .one, .one => p
  | .one, .tau => q
  | .tau, .one => r
  | .tau, .tau => sp

/-- **The pentagon residual**, `LHS − RHS`, in the convention of
    `pentagonCheck`:
    `Σ_u F(a,b,c,y,x,u)·F(a,u,d,t,y,v)·F(b,c,d,v,u,w) − F(x,c,d,t,y,w)·F(a,b,w,t,x,v)`. -/
def pentResid {R : Type} (K : Rng R) (F : Anyon → Anyon → R)
    (a b c dd x y t w v : Anyon) : R :=
  K.add
    (sumOver K (fun u => K.mul (K.mul (Fs K F a b c y x u)
                                      (Fs K F a u dd t y v))
                               (Fs K F b c dd v u w)) (fuse b c))
    (K.neg (K.mul (Fs K F x c dd t y w) (Fs K F a b w t x v)))

/-- The residual squared on the valid set, zero off it — so a single sum over
    all 512 tuples is exactly "sum of squares over the live instances". -/
def sqResid {R : Type} (K : Rng R) (F : Anyon → Anyon → R)
    (a b c dd x y t w v : Anyon) : R :=
  if pentagonValid a b c dd x y t w v then
    K.mul (pentResid K F a b c dd x y t w v) (pentResid K F a b c dd x y t w v)
  else K.zero

def allA : List Anyon := [.one, .tau]

/-- **THE OBJECT.**  `SS K F` is the pentagon sum-of-squares residual: the sum
    over ALL 512 label tuples of the squared residual, which is the sum over
    the 50 live instances (the other 462 contribute `0` by construction, not
    by a census claim).  This is the scalar `grammar_stone5.py` measures. -/
def SS {R : Type} (K : Rng R) (F : Anyon → Anyon → R) : R :=
  sumOver K (fun a => sumOver K (fun b => sumOver K (fun c => sumOver K (fun dd =>
  sumOver K (fun x => sumOver K (fun y => sumOver K (fun t => sumOver K (fun w =>
  sumOver K (fun v => sqResid K F a b c dd x y t w v) allA) allA) allA) allA)
  allA) allA) allA) allA) allA

/-- `⟨m, n⟩` denotes `m + n·φ`, `φ² = φ + 1`.  Verbatim from `Anyon.lean`. -/
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
def sub (u v : Zp) : Zp := ⟨u.m - v.m, u.n - v.n⟩

/-- `(a+bφ)(c+dφ) = (ac+bd) + (ad+bc+bd)φ`, using `φ² = φ+1`. -/
def mul (u v : Zp) : Zp :=
  ⟨u.m * v.m + u.n * v.n, u.m * v.n + u.n * v.m + u.n * v.n⟩

def invPhi : Zp := ⟨-1, 1⟩

end Zp

/-- `Z[φ]` as a ring record. -/
def zpRng : Rng Zp := ⟨Zp.zero, Zp.one, Zp.add, Zp.neg, Zp.mul⟩

theorem zp_phi_sq : Zp.mul Zp.phi Zp.phi = Zp.add Zp.phi Zp.one := rfl
theorem zp_invPhi_mul : Zp.mul Zp.phi Zp.invPhi = Zp.one := rfl

/-! ══════════════════════════════════════════════════════════════════════
    ## §1.  TRANSCRIPTION — `Ord5`, the round-5 integer order toolkit.

    Verbatim from `Anyon.lean` lines 5690–6257.  The canonical statements are
    there; this copy exists only because the file takes no imports.  Nothing
    below descends a ring-level polynomial goal to `Int` components: every
    `omega` here is on a scalar `Int` goal.
    ══════════════════════════════════════════════════════════════════════ -/
namespace Ord5

theorem sq_le_of_le (a b : Int) (ha : 0 ≤ a) (h : a ≤ b) : a * a ≤ b * b := by
  have hb : 0 ≤ b := by omega
  exact Int.mul_le_mul h h ha hb

theorem sq_lt_of_lt (a b : Int) (ha : 0 ≤ a) (h : a < b) : a * a < b * b := by
  have h1 : 0 < b - a := by omega
  have h2 : 0 < b + a := by omega
  have h3 : 0 < (b - a) * (b + a) := Int.mul_pos h1 h2
  have hc : a * b = b * a := Int.mul_comm a b
  have h4 : (b - a) * (b + a) = b * b - a * a := by
    simp only [Int.sub_mul, Int.mul_add]; omega
  omega

theorem lt_of_sq_lt (z w : Int) (hw : 0 < w) (h : z * z < w * w) : z < w := by
  have hcase : z < w ∨ w ≤ z := by omega
  rcases hcase with hc | hc
  · exact hc
  · exfalso
    have h0 : 0 ≤ w := by omega
    have := sq_le_of_le w z h0 hc
    omega

theorem neg_sq (a : Int) : (-a) * (-a) = a * a := by
  simp only [Int.neg_mul, Int.mul_neg, Int.neg_neg]

theorem sq_nonneg (a : Int) : 0 ≤ a * a := by
  have hcase : 0 ≤ a ∨ a < 0 := by omega
  rcases hcase with hc | hc
  · exact Int.mul_nonneg hc hc
  · have h := neg_sq a
    have : 0 ≤ (-a) * (-a) := Int.mul_nonneg (by omega) (by omega)
    omega

theorem neg_lt_of_sq_lt (z w : Int) (hw : 0 < w) (h : z * z < w * w) : -w < z := by
  have hz := neg_sq z
  have := lt_of_sq_lt (-z) w hw (by omega)
  omega

theorem mul_lt_mul_nn (x X y Y : Int) (hx : 0 ≤ x) (hX : x < X) (hy : 0 ≤ y)
    (hY : y < Y) : x * y < X * Y := by
  have hY0 : (0 : Int) < Y := by omega
  have h1 : x * y ≤ x * Y := Int.mul_le_mul_of_nonneg_left (by omega) hx
  have h2 : x * Y < X * Y := Int.mul_lt_mul_of_pos_right hX hY0
  omega

theorem lt_of_mul_lt_mul_right (x y k : Int) (hk : 0 < k) (h : x * k < y * k) :
    x < y := by
  have hcase : x < y ∨ y ≤ x := by omega
  rcases hcase with hc | hc
  · exact hc
  · exfalso
    have : y * k ≤ x * k := Int.mul_le_mul_of_nonneg_right hc (by omega)
    omega

theorem sq_add (a b : Int) : (a + b) * (a + b) = a * a + (a * b + a * b) + b * b := by
  have hc : b * a = a * b := Int.mul_comm b a
  simp only [Int.add_mul, Int.mul_add]; omega

theorem sq_prod (a b : Int) : (a * b) * (a * b) = (a * a) * (b * b) := by
  simp only [Int.mul_comm, Int.mul_left_comm]

theorem mul4 (a b c d : Int) : (a * b) * (c * d) = (a * c) * (b * d) := by
  simp only [Int.mul_comm, Int.mul_left_comm]

theorem sq5_prod (a b : Int) :
    (5 * (a * b)) * (5 * (a * b)) = (5 * (a * a)) * (5 * (b * b)) := by
  simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]

/-- multiply two inequalities, then cancel `p*q`: the workhorse of the mixed
    sign cases.  `s p < 5 t q` and `s q < t p` give `s² < 5 t²`. -/
theorem sq5_lt_of (s t p q : Int) (hp : 0 < p) (hq : 0 < q) (hs : 0 ≤ s)
    (h1 : s * p < 5 * (t * q)) (h2 : s * q < t * p) : s * s < 5 * (t * t) := by
  have hsp : 0 ≤ s * p := Int.mul_nonneg hs (by omega)
  have hsq : 0 ≤ s * q := Int.mul_nonneg hs (by omega)
  have hmul := mul_lt_mul_nn (s * p) (5 * (t * q)) (s * q) (t * p) hsp h1 hsq h2
  have e1 : (s * p) * (s * q) = (s * s) * (p * q) := by
    simp only [Int.mul_comm, Int.mul_left_comm]
  have e2 : (5 * (t * q)) * (t * p) = (5 * (t * t)) * (p * q) := by
    simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  have hpq : 0 < p * q := Int.mul_pos hp hq
  exact lt_of_mul_lt_mul_right (s * s) (5 * (t * t)) (p * q) hpq (by omega)

theorem sq5_gt_of (s t p q : Int) (hp : 0 < p) (hq : 0 < q) (ht : 0 ≤ t)
    (h1 : 5 * (t * q) < s * p) (h2 : t * p < s * q) : 5 * (t * t) < s * s := by
  have h5tq : 0 ≤ 5 * (t * q) := by
    have := Int.mul_nonneg ht (by omega : (0:Int) ≤ q); omega
  have htp : 0 ≤ t * p := Int.mul_nonneg ht (by omega)
  have hmul := mul_lt_mul_nn (5 * (t * q)) (s * p) (t * p) (s * q) h5tq h1 htp h2
  have e1 : (s * p) * (s * q) = (s * s) * (p * q) := by
    simp only [Int.mul_comm, Int.mul_left_comm]
  have e2 : (5 * (t * q)) * (t * p) = (5 * (t * t)) * (p * q) := by
    simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  have hpq : 0 < p * q := Int.mul_pos hp hq
  exact lt_of_mul_lt_mul_right (5 * (t * t)) (s * s) (p * q) hpq (by omega)

/-! ### the mod-5 step, and the descent that proves `√5 ∉ Q` -/

theorem five_dvd_aux (q r n : Int) (h0 : 0 ≤ r) (h1 : r < 5)
    (h : (5 * q + r) * (5 * q + r) = 5 * (n * n)) : r = 0 := by
  have hexp : (5 * q + r) * (5 * q + r)
      = 5 * (5 * (q * q)) + (5 * (q * r) + 5 * (q * r)) + r * r := by
    simp only [Int.mul_add, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    omega
  have hr : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 := by omega
  rcases hr with hr | hr | hr | hr | hr
  · exact hr
  · exfalso; rw [hr] at hexp h; omega
  · exfalso; rw [hr] at hexp h; omega
  · exfalso; rw [hr] at hexp h; omega
  · exfalso; rw [hr] at hexp h; omega

theorem five_dvd_of_sq (u n : Int) (h : u * u = 5 * (n * n)) : u % 5 = 0 := by
  have hdm : u = 5 * (u / 5) + u % 5 := by omega
  have h0 : 0 ≤ u % 5 := by omega
  have h1 : u % 5 < 5 := by omega
  have h' : (5 * (u / 5) + u % 5) * (5 * (u / 5) + u % 5) = 5 * (n * n) := by
    rw [← hdm]; exact h
  exact five_dvd_aux (u / 5) (u % 5) n h0 h1 h'

theorem no_sqrt5_fuel : ∀ (f : Nat) (u n : Int), u.natAbs + n.natAbs ≤ f →
    u * u = 5 * (n * n) → u = 0 ∧ n = 0 := by
  intro f
  induction f with
  | zero => intro u n hm _; refine ⟨?_, ?_⟩ <;> omega
  | succ f ih =>
    intro u n hm h
    have hcase : u = 0 ∨ 1 ≤ u.natAbs := by omega
    rcases hcase with hu | hu
    · subst hu
      have hn : n * n = 0 := by omega
      have hnn := Int.mul_eq_zero.mp hn
      refine ⟨rfl, ?_⟩
      rcases hnn with h1 | h1 <;> exact h1
    · exfalso
      have h5 := five_dvd_of_sq u n h
      have hk : u = 5 * (u / 5) := by omega
      have hexp : (5 * (u / 5)) * (5 * (u / 5))
          = 5 * (5 * ((u / 5) * (u / 5))) := by
        simp only [Int.mul_comm, Int.mul_left_comm]
      have h2 : 5 * (5 * ((u / 5) * (u / 5))) = 5 * (n * n) := by
        rw [← hexp, ← hk]; exact h
      have hnn : n * n = 5 * ((u / 5) * (u / 5)) := by omega
      have hmeas : n.natAbs + (u / 5).natAbs ≤ f := by omega
      have hz := ih n (u / 5) hmeas hnn
      have e1 : u / 5 = 0 := hz.2
      omega

theorem no_sqrt5 (u n : Int) (h : u * u = 5 * (n * n)) : u = 0 ∧ n = 0 :=
  no_sqrt5_fuel (u.natAbs + n.natAbs) u n (Nat.le_refl _) h

theorem norm5_mul (a b c d : Int) :
    (a * c + 5 * (b * d)) * (a * c + 5 * (b * d))
      - 5 * ((a * d + c * b) * (a * d + c * b))
    = (a * a - 5 * (b * b)) * (c * c - 5 * (d * d)) := by
  simp only [Int.add_mul, Int.mul_add, Int.mul_sub, Int.mul_assoc,
             Int.mul_comm, Int.mul_left_comm]
  omega

/-! ═══════════════════════════════════════════════════════════════════
    ## THE ORDER, at the level of raw integer coordinates

    `PosP u y` says the real number `u + y√5` is `> 0`.  The two disjuncts
    are exactly "totally positive" (`u + y√5 > 0` and its conjugate
    `u − y√5 > 0`) and "mixed" (`u + y√5 > 0 > u − y√5`).
    ═══════════════════════════════════════════════════════════════════ -/

def PosP (u y : Int) : Prop :=
  (0 < u ∧ 5 * (y * y) < u * u) ∨ (0 < y ∧ u * u < 5 * (y * y))

/-- Non-negative coordinates, not both zero, is positive. -/
theorem posP_of_nonneg (u y : Int) (hu : 0 ≤ u) (hy : 0 ≤ y)
    (hne : ¬ (u = 0 ∧ y = 0)) : PosP u y := by
  have hyy : 0 ≤ y * y := sq_nonneg y
  have huu : 0 ≤ u * u := sq_nonneg u
  have hc : 5 * (y * y) < u * u ∨ u * u < 5 * (y * y) ∨ u * u = 5 * (y * y) := by
    omega
  rcases hc with h | h | h
  · refine Or.inl ⟨?_, h⟩
    have h0 : u = 0 ∨ 0 < u := by omega
    rcases h0 with h0 | h0
    · exfalso; rw [h0] at h; omega
    · exact h0
  · refine Or.inr ⟨?_, h⟩
    have h0 : y = 0 ∨ 0 < y := by omega
    rcases h0 with h0 | h0
    · exfalso; rw [h0] at h; omega
    · exact h0
  · exfalso
    have hz := no_sqrt5 u y h
    exact hne ⟨hz.1, hz.2⟩

/-- Non-positive coordinates is never positive. -/
theorem not_posP_of_nonpos (u y : Int) (hu : u ≤ 0) (hy : y ≤ 0) :
    ¬ PosP u y := by
  intro h
  rcases h with ⟨h1, _⟩ | ⟨h1, _⟩ <;> omega

/-! ### trichotomy -/

theorem posP_trichotomy (u y : Int) :
    (PosP u y ∧ ¬ PosP (-u) (-y) ∧ ¬ (u = 0 ∧ y = 0)) ∨
    (¬ PosP u y ∧ ¬ PosP (-u) (-y) ∧ (u = 0 ∧ y = 0)) ∨
    (¬ PosP u y ∧ PosP (-u) (-y) ∧ ¬ (u = 0 ∧ y = 0)) := by
  have eu := neg_sq u
  have ey := neg_sq y
  have hyy : 0 ≤ y * y := sq_nonneg y
  have huu : 0 ≤ u * u := sq_nonneg u
  have hc : 5 * (y * y) < u * u ∨ u * u < 5 * (y * y) ∨ u * u = 5 * (y * y) := by
    omega
  rcases hc with h | h | h
  · have hune : ¬ u = 0 := by intro h0; rw [h0] at h; omega
    have hcs : 0 < u ∨ u < 0 := by omega
    rcases hcs with hs | hs
    · refine Or.inl ⟨Or.inl ⟨hs, h⟩, ?_, ?_⟩
      · intro hp
        rcases hp with ⟨k1, _⟩ | ⟨_, k2⟩
        · omega
        · rw [eu, ey] at k2; omega
      · intro hz; exact hune hz.1
    · refine Or.inr (Or.inr ⟨?_, Or.inl ⟨by omega, by rw [eu, ey]; exact h⟩, ?_⟩)
      · intro hp
        rcases hp with ⟨k1, _⟩ | ⟨_, k2⟩ <;> omega
      · intro hz; exact hune hz.1
  · have hyne : ¬ y = 0 := by intro h0; rw [h0] at h; omega
    have hcs : 0 < y ∨ y < 0 := by omega
    rcases hcs with hs | hs
    · refine Or.inl ⟨Or.inr ⟨hs, h⟩, ?_, ?_⟩
      · intro hp
        rcases hp with ⟨_, k1⟩ | ⟨k2, _⟩
        · rw [eu, ey] at k1; omega
        · omega
      · intro hz; exact hyne hz.2
    · refine Or.inr (Or.inr ⟨?_, Or.inr ⟨by omega, by rw [eu, ey]; exact h⟩, ?_⟩)
      · intro hp
        rcases hp with ⟨_, k1⟩ | ⟨k2, _⟩ <;> omega
      · intro hz; exact hyne hz.2
  · have hz := no_sqrt5 u y h
    refine Or.inr (Or.inl ⟨?_, ?_, hz.1, hz.2⟩)
    · intro hp
      rcases hp with ⟨k, _⟩ | ⟨k, _⟩ <;> omega
    · intro hp
      rcases hp with ⟨k, _⟩ | ⟨k, _⟩ <;> omega

/-! ### algebraic expansions used by the closure proofs -/

theorem diff_prod (a b : Int) : (a - b) * (a + b) = a * a - b * b := by
  have hc : b * a = a * b := Int.mul_comm b a
  simp only [Int.sub_mul, Int.mul_add]; omega

theorem sq_sub_comm (a b : Int) : (a - b) * (a - b) = (b - a) * (b - a) := by
  have hc : b * a = a * b := Int.mul_comm b a
  simp only [Int.sub_mul, Int.mul_sub]; omega

theorem cross_prod (a b c d : Int) :
    (a - b) * (c + d) = a * c + a * d - b * c - b * d := by
  simp only [Int.sub_mul, Int.mul_add]; omega

/-! ### closure under addition -/

/-- totally positive + totally positive. -/
theorem posP_add_tt (x1 y1 x2 y2 : Int) (hx1 : 0 < x1) (k1 : 5 * (y1 * y1) < x1 * x1)
    (hx2 : 0 < x2) (k2 : 5 * (y2 * y2) < x2 * x2) : PosP (x1 + x2) (y1 + y2) := by
  have hcross : 5 * (y1 * y2) < x1 * x2 := by
    have hA : 0 ≤ 5 * (y1 * y1) := by have := sq_nonneg y1; omega
    have hC : 0 ≤ 5 * (y2 * y2) := by have := sq_nonneg y2; omega
    have hm := mul_lt_mul_nn (5 * (y1 * y1)) (x1 * x1) (5 * (y2 * y2)) (x2 * x2)
                 hA k1 hC k2
    have e1 := sq5_prod y1 y2
    have e2 := sq_prod x1 x2
    exact lt_of_sq_lt (5 * (y1 * y2)) (x1 * x2) (Int.mul_pos hx1 hx2) (by omega)
  refine Or.inl ⟨by omega, ?_⟩
  have ea := sq_add x1 x2
  have eb := sq_add y1 y2
  omega

/-- mixed + mixed. -/
theorem posP_add_mm (x1 y1 x2 y2 : Int) (hy1 : 0 < y1) (k1 : x1 * x1 < 5 * (y1 * y1))
    (hy2 : 0 < y2) (k2 : x2 * x2 < 5 * (y2 * y2)) : PosP (x1 + x2) (y1 + y2) := by
  have hcross : x1 * x2 < 5 * (y1 * y2) := by
    have hA : 0 ≤ x1 * x1 := sq_nonneg x1
    have hC : 0 ≤ x2 * x2 := sq_nonneg x2
    have hm := mul_lt_mul_nn (x1 * x1) (5 * (y1 * y1)) (x2 * x2) (5 * (y2 * y2))
                 hA k1 hC k2
    have e1 := sq5_prod y1 y2
    have e2 := sq_prod x1 x2
    have hpos : 0 < 5 * (y1 * y2) := by have := Int.mul_pos hy1 hy2; omega
    exact lt_of_sq_lt (x1 * x2) (5 * (y1 * y2)) hpos (by omega)
  refine Or.inr ⟨by omega, ?_⟩
  have ea := sq_add x1 x2
  have eb := sq_add y1 y2
  omega

/-- **The hard mixed case, in positive coordinates.**  `a − g√5 > 0`
    (`a,g > 0`, `a² > 5g²`) plus `−b + d√5 > 0` (`b,d > 0`, `b² < 5d²`).
    Both certificates are produced by multiplying two integer inequalities
    and cancelling the positive factor `p·q`. -/
theorem posP_add_hard (a g b d : Int) (ha : 0 < a) (hg : 0 < g) (hb : 0 < b)
    (hd : 0 < d) (k1 : 5 * (g * g) < a * a) (k2 : b * b < 5 * (d * d)) :
    PosP (a - b) (d - g) := by
  have hcross : b * g < a * d := by
    have hA : 0 ≤ b * b := sq_nonneg b
    have hC : 0 ≤ 5 * (g * g) := by have := sq_nonneg g; omega
    have hm := mul_lt_mul_nn (b * b) (5 * (d * d)) (5 * (g * g)) (a * a) hA k2 hC k1
    have f1 : (b * b) * (5 * (g * g)) = 5 * ((b * b) * (g * g)) := by
      simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    have f2 : (5 * (d * d)) * (a * a) = 5 * ((a * a) * (d * d)) := by
      simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    have e1 := sq_prod b g
    have e2 := sq_prod a d
    exact lt_of_sq_lt (b * g) (a * d) (Int.mul_pos ha hd) (by omega)
  have hcaseX : a - b < 0 ∨ a - b = 0 ∨ 0 < a - b := by omega
  rcases hcaseX with hX | hX | hX
  · have hsq : a * a < b * b := sq_lt_of_lt a b (by omega) (by omega)
    have hgd : g < d := lt_of_sq_lt g d hd (by omega)
    refine Or.inr ⟨by omega, ?_⟩
    have p1 := diff_prod b a
    have p2 := diff_prod d g
    have q1 := cross_prod b a d g
    have q2 := cross_prod d g b a
    have c1 : d * b = b * d := Int.mul_comm d b
    have c2 : d * a = a * d := Int.mul_comm d a
    have c3 : g * b = b * g := Int.mul_comm g b
    have c4 : g * a = a * g := Int.mul_comm g a
    have hres := sq5_lt_of (b - a) (d - g) (b + a) (d + g) (by omega) (by omega)
                   (by omega) (by omega) (by omega)
    have hcm := sq_sub_comm a b
    omega
  · have hsq : a * a = b * b := by
      have : a = b := by omega
      rw [this]
    have hgd : g < d := lt_of_sq_lt g d hd (by omega)
    refine Or.inr ⟨by omega, ?_⟩
    have hp : 0 < (d - g) * (d - g) := Int.mul_pos (by omega) (by omega)
    rw [hX]
    omega
  · have hcaseY : 0 ≤ d - g ∨ d - g < 0 := by omega
    rcases hcaseY with hY | hY
    · exact posP_of_nonneg _ _ (by omega) hY (by intro hz; omega)
    · refine Or.inl ⟨by omega, ?_⟩
      have p1 := diff_prod a b
      have p2 := diff_prod g d
      have q1 := cross_prod a b g d
      have q2 := cross_prod g d a b
      have c1 : g * a = a * g := Int.mul_comm g a
      have c2 : g * b = b * g := Int.mul_comm g b
      have c3 : d * a = a * d := Int.mul_comm d a
      have c4 : d * b = b * d := Int.mul_comm d b
      have hres := sq5_gt_of (a - b) (g - d) (a + b) (g + d) (by omega) (by omega)
                     (by omega) (by omega) (by omega)
      have hcm := sq_sub_comm d g
      omega

/-- totally positive + mixed. -/
theorem posP_add_tm (x1 y1 x2 y2 : Int) (hx1 : 0 < x1) (k1 : 5 * (y1 * y1) < x1 * x1)
    (hy2 : 0 < y2) (k2 : x2 * x2 < 5 * (y2 * y2)) : PosP (x1 + x2) (y1 + y2) := by
  have hcase1 : 0 ≤ y1 ∨ y1 < 0 := by omega
  rcases hcase1 with hy1 | hy1
  · have hcX : 0 ≤ x1 + x2 ∨ x1 + x2 < 0 := by omega
    rcases hcX with hX | hX
    · exact posP_of_nonneg _ _ hX (by omega) (by intro hz; omega)
    · refine Or.inr ⟨by omega, ?_⟩
      have hs := sq_le_of_le (-(x1 + x2)) (-x2) (by omega) (by omega)
      have e1 := neg_sq (x1 + x2)
      have e2 := neg_sq x2
      have hy := sq_le_of_le y2 (y1 + y2) (by omega) (by omega)
      omega
  · have hcx2 : 0 ≤ x2 ∨ x2 < 0 := by omega
    rcases hcx2 with hx2 | hx2
    · have hcY : 0 ≤ y1 + y2 ∨ y1 + y2 < 0 := by omega
      rcases hcY with hY | hY
      · exact posP_of_nonneg _ _ (by omega) hY (by intro hz; omega)
      · refine Or.inl ⟨by omega, ?_⟩
        have hs := sq_le_of_le (-(y1 + y2)) (-y1) (by omega) (by omega)
        have e1 := neg_sq (y1 + y2)
        have e2 := neg_sq y1
        have hx := sq_le_of_le x1 (x1 + x2) (by omega) (by omega)
        omega
    · have g1 := neg_sq y1
      have g2 := neg_sq x2
      have h := posP_add_hard x1 (-y1) (-x2) y2 hx1 (by omega) (by omega) hy2
                  (by omega) (by omega)
      have e1 : x1 - -x2 = x1 + x2 := by omega
      have e2 : y2 - -y1 = y1 + y2 := by omega
      rw [e1, e2] at h
      exact h

/-- **CLOSURE UNDER ADDITION.** -/
theorem posP_add (x1 y1 x2 y2 : Int) (h1 : PosP x1 y1) (h2 : PosP x2 y2) :
    PosP (x1 + x2) (y1 + y2) := by
  rcases h1 with ⟨hx1, k1⟩ | ⟨hy1, k1⟩ <;> rcases h2 with ⟨hx2, k2⟩ | ⟨hy2, k2⟩
  · exact posP_add_tt x1 y1 x2 y2 hx1 k1 hx2 k2
  · exact posP_add_tm x1 y1 x2 y2 hx1 k1 hy2 k2
  · have h := posP_add_tm x2 y2 x1 y1 hx2 k2 hy1 k1
    have e1 : x2 + x1 = x1 + x2 := by omega
    have e2 : y2 + y1 = y1 + y2 := by omega
    rw [e1, e2] at h
    exact h
  · exact posP_add_mm x1 y1 x2 y2 hy1 k1 hy2 k2

/-! ### closure under multiplication

    Here `φ² = φ + 1` enters, in the guise of the `5` in `norm5_mul`:
    `(u + y√5)(u' + y'√5) = (uu' + 5yy') + (uy' + u'y)√5`. -/

theorem posP_mul_tt (x1 y1 x2 y2 : Int) (hx1 : 0 < x1) (k1 : 5 * (y1 * y1) < x1 * x1)
    (hx2 : 0 < x2) (k2 : 5 * (y2 * y2) < x2 * x2) :
    PosP (x1 * x2 + 5 * (y1 * y2)) (x1 * y2 + x2 * y1) := by
  have hX : 0 < x1 * x2 + 5 * (y1 * y2) := by
    have hA : 0 ≤ 5 * (y1 * y1) := by have := sq_nonneg y1; omega
    have hC : 0 ≤ 5 * (y2 * y2) := by have := sq_nonneg y2; omega
    have hm := mul_lt_mul_nn (5 * (y1 * y1)) (x1 * x1) (5 * (y2 * y2)) (x2 * x2)
                 hA k1 hC k2
    have e1 := sq5_prod y1 y2
    have e2 := sq_prod x1 x2
    have hb := neg_lt_of_sq_lt (5 * (y1 * y2)) (x1 * x2) (Int.mul_pos hx1 hx2)
                 (by omega)
    omega
  refine Or.inl ⟨hX, ?_⟩
  have hn := norm5_mul x1 y1 x2 y2
  have hp : 0 < (x1 * x1 - 5 * (y1 * y1)) * (x2 * x2 - 5 * (y2 * y2)) :=
    Int.mul_pos (by omega) (by omega)
  omega

theorem posP_mul_mm (x1 y1 x2 y2 : Int) (hy1 : 0 < y1) (k1 : x1 * x1 < 5 * (y1 * y1))
    (hy2 : 0 < y2) (k2 : x2 * x2 < 5 * (y2 * y2)) :
    PosP (x1 * x2 + 5 * (y1 * y2)) (x1 * y2 + x2 * y1) := by
  have hX : 0 < x1 * x2 + 5 * (y1 * y2) := by
    have hm := mul_lt_mul_nn (x1 * x1) (5 * (y1 * y1)) (x2 * x2) (5 * (y2 * y2))
                 (sq_nonneg x1) k1 (sq_nonneg x2) k2
    have e1 := sq5_prod y1 y2
    have e2 := sq_prod x1 x2
    have hpos : 0 < 5 * (y1 * y2) := by have := Int.mul_pos hy1 hy2; omega
    have hb := neg_lt_of_sq_lt (x1 * x2) (5 * (y1 * y2)) hpos (by omega)
    omega
  refine Or.inl ⟨hX, ?_⟩
  have hn := norm5_mul x1 y1 x2 y2
  have hp : 0 < (x1 * x1 - 5 * (y1 * y1)) * (x2 * x2 - 5 * (y2 * y2)) := by
    have h := Int.mul_pos (show (0:Int) < 5 * (y1 * y1) - x1 * x1 by omega)
                          (show (0:Int) < 5 * (y2 * y2) - x2 * x2 by omega)
    have e : (5 * (y1 * y1) - x1 * x1) * (5 * (y2 * y2) - x2 * x2)
           = (x1 * x1 - 5 * (y1 * y1)) * (x2 * x2 - 5 * (y2 * y2)) := by
      simp only [Int.sub_mul, Int.mul_sub]; omega
    omega
  omega

theorem posP_mul_tm (x1 y1 x2 y2 : Int) (hx1 : 0 < x1) (k1 : 5 * (y1 * y1) < x1 * x1)
    (hy2 : 0 < y2) (k2 : x2 * x2 < 5 * (y2 * y2)) :
    PosP (x1 * x2 + 5 * (y1 * y2)) (x1 * y2 + x2 * y1) := by
  have hY : 0 < x1 * y2 + x2 * y1 := by
    have hC : 0 ≤ 5 * (y1 * y1) := by have := sq_nonneg y1; omega
    have hm := mul_lt_mul_nn (x2 * x2) (5 * (y2 * y2)) (5 * (y1 * y1)) (x1 * x1)
                 (sq_nonneg x2) k2 hC k1
    have f1 : (x2 * x2) * (5 * (y1 * y1)) = 5 * ((x2 * y1) * (x2 * y1)) := by
      simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    have f2 : (5 * (y2 * y2)) * (x1 * x1) = 5 * ((x1 * y2) * (x1 * y2)) := by
      simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    have hb := neg_lt_of_sq_lt (x2 * y1) (x1 * y2) (Int.mul_pos hx1 hy2) (by omega)
    omega
  refine Or.inr ⟨hY, ?_⟩
  have hn := norm5_mul x1 y1 x2 y2
  have hp : (x1 * x1 - 5 * (y1 * y1)) * (x2 * x2 - 5 * (y2 * y2)) < 0 := by
    have h := Int.mul_pos (show (0:Int) < x1 * x1 - 5 * (y1 * y1) by omega)
                          (show (0:Int) < 5 * (y2 * y2) - x2 * x2 by omega)
    have e1 : (x1 * x1 - 5 * (y1 * y1)) * (5 * (y2 * y2) - x2 * x2)
            = (x1 * x1 - 5 * (y1 * y1)) * (5 * (y2 * y2))
              - (x1 * x1 - 5 * (y1 * y1)) * (x2 * x2) := Int.mul_sub _ _ _
    have e2 : (x1 * x1 - 5 * (y1 * y1)) * (x2 * x2 - 5 * (y2 * y2))
            = (x1 * x1 - 5 * (y1 * y1)) * (x2 * x2)
              - (x1 * x1 - 5 * (y1 * y1)) * (5 * (y2 * y2)) := Int.mul_sub _ _ _
    omega
  omega

/-- **CLOSURE UNDER MULTIPLICATION.** -/
theorem posP_mul (x1 y1 x2 y2 : Int) (h1 : PosP x1 y1) (h2 : PosP x2 y2) :
    PosP (x1 * x2 + 5 * (y1 * y2)) (x1 * y2 + x2 * y1) := by
  rcases h1 with ⟨hx1, k1⟩ | ⟨hy1, k1⟩ <;> rcases h2 with ⟨hx2, k2⟩ | ⟨hy2, k2⟩
  · exact posP_mul_tt x1 y1 x2 y2 hx1 k1 hx2 k2
  · exact posP_mul_tm x1 y1 x2 y2 hx1 k1 hy2 k2
  · have h := posP_mul_tm x2 y2 x1 y1 hx2 k2 hy1 k1
    have a1 : x2 * x1 = x1 * x2 := Int.mul_comm x2 x1
    have a2 : y2 * y1 = y1 * y2 := Int.mul_comm y2 y1
    have e1 : x2 * x1 + 5 * (y2 * y1) = x1 * x2 + 5 * (y1 * y2) := by omega
    have e2 : x2 * y1 + x1 * y2 = x1 * y2 + x2 * y1 := by omega
    rw [e1, e2] at h
    exact h
  · exact posP_mul_mm x1 y1 x2 y2 hy1 k1 hy2 k2

/-- Positivity is invariant under doubling — needed because the `Zp` product
    coordinates satisfy `2·U = uu' + 5yy'`, `2·Y = uy' + u'y`. -/
theorem posP_two (u y : Int) : PosP (2 * u) (2 * y) ↔ PosP u y := by
  have e1 := sq_prod 2 u
  have e2 := sq_prod 2 y
  constructor
  · intro h
    rcases h with ⟨a1, a2⟩ | ⟨a1, a2⟩
    · exact Or.inl ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
  · intro h
    rcases h with ⟨a1, a2⟩ | ⟨a1, a2⟩
    · exact Or.inl ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩

/-! ### the decidable test, exactly as the builder's certificate branches -/

/-- `posUN u y` decides `u + y√5 > 0` by integer arithmetic only. -/
def posUN (u y : Int) : Bool :=
  if 0 ≤ y then
    (if 0 ≤ u then decide (0 < u ∨ 0 < y)
     else decide (u * u < 5 * (y * y)))
  else
    (if 0 ≤ u then decide (5 * (y * y) < u * u) else false)

theorem posUN_iff (u y : Int) : posUN u y = true ↔ PosP u y := by
  unfold posUN
  split
  · rename_i hy
    split
    · rename_i hu
      simp only [decide_eq_true_eq]
      constructor
      · intro h
        refine posP_of_nonneg u y hu hy ?_
        intro hz
        rcases h with h | h
        · have e := hz.1; omega
        · have e := hz.2; omega
      · intro h
        rcases h with ⟨a1, _⟩ | ⟨a1, _⟩
        · exact Or.inl a1
        · exact Or.inr a1
    · rename_i hu
      simp only [decide_eq_true_eq]
      constructor
      · intro h
        refine Or.inr ⟨?_, h⟩
        have hcy : y = 0 ∨ 0 < y := by omega
        rcases hcy with h0 | h0
        · exfalso; rw [h0] at h; have := sq_nonneg u; omega
        · exact h0
      · intro h
        rcases h with ⟨a1, _⟩ | ⟨_, a2⟩
        · exact absurd a1 (by omega)
        · exact a2
  · rename_i hy
    split
    · rename_i hu
      simp only [decide_eq_true_eq]
      constructor
      · intro h
        refine Or.inl ⟨?_, h⟩
        have hcu : u = 0 ∨ 0 < u := by omega
        rcases hcu with h0 | h0
        · exfalso; rw [h0] at h; have := sq_nonneg y; omega
        · exact h0
      · intro h
        rcases h with ⟨_, a2⟩ | ⟨a1, _⟩
        · exact a2
        · exact absurd a1 (by omega)
    · rename_i hu
      constructor
      · intro h; exact Bool.noConfusion h
      · intro h
        exfalso
        rcases h with ⟨a1, _⟩ | ⟨a1, _⟩ <;> omega

end Ord5

namespace Zp

/-! ### THE ORDER -/

/-- **`pos a` decides `a > 0` in `Z[φ]`.**  With `u = 2m + n` the element
    `m + nφ` is `(u + n√5)/2`, and the sign of `u + n√5` is decided by
    integer arithmetic alone. -/
def pos (a : Zp) : Bool := Ord5.posUN (2 * a.m + a.n) a.n

theorem pos_iff (a : Zp) : pos a = true ↔ Ord5.PosP (2 * a.m + a.n) a.n :=
  Ord5.posUN_iff _ _

theorem pos_eq_false_iff (a : Zp) :
    pos a = false ↔ ¬ Ord5.PosP (2 * a.m + a.n) a.n := by
  rw [← pos_iff]
  cases h : pos a
  · simp
  · simp

theorem eq_zero_iff (a : Zp) : a = zero ↔ (2 * a.m + a.n = 0 ∧ a.n = 0) := by
  rcases a with ⟨m, n⟩
  simp only [zero, Zp.mk.injEq]
  constructor
  · intro h; refine ⟨?_, ?_⟩ <;> omega
  · intro h; have e1 := h.1; have e2 := h.2; refine ⟨?_, ?_⟩ <;> omega

theorem pos_neg_iff (a : Zp) :
    pos (neg a) = true ↔ Ord5.PosP (-(2 * a.m + a.n)) (-a.n) := by
  have h := pos_iff (neg a)
  have e1 : 2 * (neg a).m + (neg a).n = -(2 * a.m + a.n) := by
    simp only [neg]; omega
  have e2 : (neg a).n = -a.n := by simp only [neg]
  rw [e1, e2] at h
  exact h

theorem pos_neg_eq_false_iff (a : Zp) :
    pos (neg a) = false ↔ ¬ Ord5.PosP (-(2 * a.m + a.n)) (-a.n) := by
  rw [← pos_neg_iff]
  cases h : pos (neg a)
  · simp
  · simp

/-! ### TRICHOTOMY -/

/-- **TRICHOTOMY.**  For every `a : Z[φ]` exactly one of `a > 0`, `a = 0`,
    `−a > 0` holds.  The `5n² = u² ⟹ u = n = 0` step is the one mod-5
    descent (`Ord5.no_sqrt5`), run on an explicit `Nat` fuel. -/
theorem trichotomy (a : Zp) :
    (pos a = true ∧ a ≠ zero ∧ pos (neg a) = false) ∨
    (pos a = false ∧ a = zero ∧ pos (neg a) = false) ∨
    (pos a = false ∧ a ≠ zero ∧ pos (neg a) = true) := by
  rcases Ord5.posP_trichotomy (2 * a.m + a.n) a.n with
      ⟨p1, p2, p3⟩ | ⟨p1, p2, p3⟩ | ⟨p1, p2, p3⟩
  · exact Or.inl ⟨(pos_iff a).mpr p1, fun hz => p3 ((eq_zero_iff a).mp hz),
                  (pos_neg_eq_false_iff a).mpr p2⟩
  · exact Or.inr (Or.inl ⟨(pos_eq_false_iff a).mpr p1, (eq_zero_iff a).mpr p3,
                          (pos_neg_eq_false_iff a).mpr p2⟩)
  · exact Or.inr (Or.inr ⟨(pos_eq_false_iff a).mpr p1,
                          fun hz => p3 ((eq_zero_iff a).mp hz),
                          (pos_neg_iff a).mpr p2⟩)

/-- The certificate's own phrasing: the three flags sum to exactly one. -/
def triCount (a : Zp) : Nat :=
  (if pos a = true then 1 else 0) + (if a = zero then 1 else 0)
    + (if pos (neg a) = true then 1 else 0)

theorem tri_count_eq_one (a : Zp) : triCount a = 1 := by
  unfold triCount
  rcases trichotomy a with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · rw [h1, h3, if_neg h2]; rfl
  · rw [h1, h3, if_pos h2]; rfl
  · rw [h1, h3, if_neg h2]; rfl

/-! ### CLOSURE -/

theorem pos_add (a b : Zp) (ha : pos a = true) (hb : pos b = true) :
    pos (add a b) = true := by
  have h1 := (pos_iff a).mp ha
  have h2 := (pos_iff b).mp hb
  have hm := Ord5.posP_add _ _ _ _ h1 h2
  refine (pos_iff (add a b)).mpr ?_
  have e1 : 2 * (add a b).m + (add a b).n
          = (2 * a.m + a.n) + (2 * b.m + b.n) := by simp only [add]; omega
  have e2 : (add a b).n = a.n + b.n := by simp only [add]
  rw [e1, e2]
  exact hm

theorem pos_mul (a b : Zp) (ha : pos a = true) (hb : pos b = true) :
    pos (mul a b) = true := by
  have h1 := (pos_iff a).mp ha
  have h2 := (pos_iff b).mp hb
  have hm := Ord5.posP_mul (2 * a.m + a.n) a.n (2 * b.m + b.n) b.n h1 h2
  refine (pos_iff (mul a b)).mpr ?_
  refine (Ord5.posP_two _ _).mp ?_
  have b1 := Ord5.mul4 2 a.m 2 b.m
  have c1 : 2 * a.m * b.n = 2 * (a.m * b.n) := Int.mul_assoc 2 a.m b.n
  have c2 : a.n * (2 * b.m) = 2 * (a.n * b.m) := Int.mul_left_comm a.n 2 b.m
  have c3 : 2 * b.m * a.n = 2 * (b.m * a.n) := Int.mul_assoc 2 b.m a.n
  have c4 : b.m * a.n = a.n * b.m := Int.mul_comm b.m a.n
  have c5 : b.n * a.n = a.n * b.n := Int.mul_comm b.n a.n
  have e1 : 2 * (2 * (mul a b).m + (mul a b).n)
          = (2 * a.m + a.n) * (2 * b.m + b.n) + 5 * (a.n * b.n) := by
    simp only [mul, Int.add_mul, Int.mul_add]
    omega
  have e2 : 2 * (mul a b).n = (2 * a.m + a.n) * b.n + (2 * b.m + b.n) * a.n := by
    simp only [mul, Int.add_mul, Int.mul_add]
    omega
  rw [e1, e2]
  exact hm

/-! ### ring laws needed downstream -/

theorem mul_zero (u : Zp) : mul u zero = zero := by
  cases u; simp only [mul, zero, Zp.mk.injEq]; refine ⟨?_, ?_⟩ <;> omega
theorem one_mul (u : Zp) : mul one u = u := by
  cases u; simp only [mul, one, Zp.mk.injEq]; refine ⟨?_, ?_⟩ <;> omega
theorem mul_assoc (u v w : Zp) : mul (mul u v) w = mul u (mul v w) := by
  cases u; cases v; cases w
  simp only [mul, Zp.mk.injEq, Int.add_mul, Int.mul_add, Int.mul_assoc]
  refine ⟨?_, ?_⟩ <;> omega
theorem add_mul (u v w : Zp) : mul (add u v) w = add (mul u w) (mul v w) := by
  cases u; cases v; cases w
  simp only [mul, add, Zp.mk.injEq, Int.add_mul]
  refine ⟨?_, ?_⟩ <;> omega
theorem sub_mul (u v w : Zp) : mul (sub u v) w = sub (mul u w) (mul v w) := by
  cases u; cases v; cases w
  simp only [mul, sub, Zp.mk.injEq, Int.sub_mul]
  refine ⟨?_, ?_⟩ <;> omega
theorem neg_mul (u v : Zp) : mul (neg u) v = neg (mul u v) := by
  cases u; cases v
  simp only [mul, neg, Zp.mk.injEq, Int.neg_mul]
  refine ⟨?_, ?_⟩ <;> omega
theorem mul_neg (u v : Zp) : mul u (neg v) = neg (mul u v) := by
  cases u; cases v
  simp only [mul, neg, Zp.mk.injEq, Int.mul_neg]
  refine ⟨?_, ?_⟩ <;> omega
theorem neg_neg (u : Zp) : neg (neg u) = u := by
  cases u; simp only [neg, Zp.mk.injEq]; refine ⟨?_, ?_⟩ <;> omega
theorem neg_zero : neg zero = zero := rfl
theorem sub_eq_zero (u v : Zp) (h : sub u v = zero) : u = v := by
  cases u; cases v
  simp only [sub, zero, Zp.mk.injEq] at h
  have e1 := h.1; have e2 := h.2
  simp only [Zp.mk.injEq]; refine ⟨?_, ?_⟩ <;> omega

/-! ### THE DOMAIN PROPERTY, FROM THE ORDER -/

/-- **`Z[φ]` is an integral domain — proved from the order alone.**  Nonzero
    `a`, `b` have `±a`, `±b` positive; multiplicative closure makes `±(ab)`
    `a`, `b` have `±a`, `±b` positive; multiplicative closure makes `±(ab)`
    positive; and `pos zero = false`. -/
theorem mul_ne_zero (a b : Zp) (ha : a ≠ zero) (hb : b ≠ zero) :
    mul a b ≠ zero := by
  have pa : pos a = true ∨ pos (neg a) = true := by
    rcases trichotomy a with ⟨h, _, _⟩ | ⟨_, h, _⟩ | ⟨_, _, h⟩
    · exact Or.inl h
    · exact absurd h ha
    · exact Or.inr h
  have pb : pos b = true ∨ pos (neg b) = true := by
    rcases trichotomy b with ⟨h, _, _⟩ | ⟨_, h, _⟩ | ⟨_, _, h⟩
    · exact Or.inl h
    · exact absurd h hb
    · exact Or.inr h
  have key : pos (mul a b) = true ∨ pos (neg (mul a b)) = true := by
    rcases pa with p1 | p1 <;> rcases pb with p2 | p2
    · exact Or.inl (pos_mul a b p1 p2)
    · have h := pos_mul a (neg b) p1 p2
      rw [mul_neg] at h; exact Or.inr h
    · have h := pos_mul (neg a) b p1 p2
      rw [neg_mul] at h; exact Or.inr h
    · have h := pos_mul (neg a) (neg b) p1 p2
      rw [neg_mul, mul_neg, neg_neg] at h; exact Or.inl h
  intro hz
  rcases key with k | k
  · rw [hz] at k; exact absurd k (by decide)
  · rw [hz, neg_zero] at k; exact absurd k (by decide)

/-! ### §2b.  The remaining commutative-ring laws of `Z[φ]`

    `Anyon.lean` proves the subset round 5 needed; the quadratic-form algebra
    below needs the rest.  Same recipe: `simp only` distributes and
    canonicalises the product atoms, then each component is linear in those
    atoms and `omega` closes it.  These are `Zp`-level laws with `Zp`-level
    variables — no polynomial goal is descended anywhere. -/

theorem add_comm (u v : Zp) : add u v = add v u := by
  cases u; cases v; simp only [add, Zp.mk.injEq]; refine ⟨?_, ?_⟩ <;> omega
theorem add_assoc (u v w : Zp) : add (add u v) w = add u (add v w) := by
  cases u; cases v; cases w; simp only [add, Zp.mk.injEq]
  refine ⟨?_, ?_⟩ <;> omega
theorem add_zero (u : Zp) : add u zero = u := by
  cases u; simp only [add, zero, Zp.mk.injEq]; refine ⟨?_, ?_⟩ <;> omega
theorem zero_add (u : Zp) : add zero u = u := by
  cases u; simp only [add, zero, Zp.mk.injEq]; refine ⟨?_, ?_⟩ <;> omega
theorem add_left_comm (u v w : Zp) : add u (add v w) = add v (add u w) := by
  rw [← add_assoc, add_comm u v, add_assoc]
theorem mul_one (u : Zp) : mul u one = u := by
  cases u; simp only [mul, one, Zp.mk.injEq]; refine ⟨?_, ?_⟩ <;> omega
theorem zero_mul (u : Zp) : mul zero u = zero := by
  cases u; simp only [mul, zero, Zp.mk.injEq]; refine ⟨?_, ?_⟩ <;> omega
theorem mul_comm (u v : Zp) : mul u v = mul v u := by
  cases u; cases v; simp only [mul, Zp.mk.injEq]
  refine ⟨?_, ?_⟩ <;> simp only [Int.mul_comm] <;> omega
theorem mul_add (u v w : Zp) : mul u (add v w) = add (mul u v) (mul u w) := by
  cases u; cases v; cases w
  simp only [mul, add, Zp.mk.injEq, Int.mul_add]
  refine ⟨?_, ?_⟩ <;> omega
theorem mul_left_comm (u v w : Zp) : mul u (mul v w) = mul v (mul u w) := by
  rw [← mul_assoc, mul_comm u v, mul_assoc]
theorem add_neg (u : Zp) : add u (neg u) = zero := by
  cases u; simp only [add, neg, zero, Zp.mk.injEq]; refine ⟨?_, ?_⟩ <;> omega
theorem eq_zero_of_add_neg (u v : Zp) (h : add u (neg v) = zero) : u = v := by
  cases u; cases v
  simp only [add, neg, zero, Zp.mk.injEq] at h
  have e1 := h.1; have e2 := h.2
  simp only [Zp.mk.injEq]; refine ⟨?_, ?_⟩ <;> omega
theorem add_neg_of_eq (u v : Zp) (h : u = v) : add u (neg v) = zero := by
  rw [h]; exact add_neg v

/-! ### §2c.  The nonnegative cone of `Z[φ]`

    `Nn a` reads `a ≥ 0`.  Everything here follows from round 5's
    `trichotomy`, `pos_add`, `pos_mul` and `mul_ne_zero`; no new order
    reasoning is introduced.  ADJUDICATOR: `Zp.trichotomy` — `Nn a` is
    decided by `pos a` together with `a = zero`, both decidable.  It does NOT
    say anything about `Q(√5)(√φ)`; see `Ep.TPos` for that. -/

/-- `a ≥ 0` in `Z[φ]`. -/
def Nn (a : Zp) : Prop := a = zero ∨ pos a = true

theorem nn_zero : Nn zero := Or.inl rfl

theorem pos_ne_zero (a : Zp) (h : pos a = true) : a ≠ zero := by
  intro hz; rw [hz] at h; exact absurd h (by decide)

theorem not_nn (a : Zp) (h : pos (neg a) = true) : ¬ Nn a := by
  intro hn
  rcases trichotomy a with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · rw [h] at h3; exact Bool.noConfusion h3
  · rw [h2, neg] at h
    exact absurd h (by decide)
  · rcases hn with hn | hn
    · exact h2 hn
    · rw [hn] at h1; exact Bool.noConfusion h1

theorem nn_add (a b : Zp) (ha : Nn a) (hb : Nn b) : Nn (add a b) := by
  rcases ha with ha | ha
  · rcases hb with hb | hb
    · exact Or.inl (by rw [ha, hb]; rfl)
    · exact Or.inr (by rw [ha, zero_add]; exact hb)
  · rcases hb with hb | hb
    · exact Or.inr (by rw [hb, add_zero]; exact ha)
    · exact Or.inr (pos_add a b ha hb)

theorem nn_mul (a b : Zp) (ha : Nn a) (hb : Nn b) : Nn (mul a b) := by
  rcases ha with ha | ha
  · exact Or.inl (by rw [ha, zero_mul])
  · rcases hb with hb | hb
    · exact Or.inl (by rw [hb, mul_zero])
    · exact Or.inr (pos_mul a b ha hb)

/-- Squares are nonnegative. -/
theorem nn_sq (a : Zp) : Nn (mul a a) := by
  rcases trichotomy a with ⟨h1, _, _⟩ | ⟨_, h2, _⟩ | ⟨_, _, h3⟩
  · exact Or.inr (pos_mul a a h1 h1)
  · exact Or.inl (by rw [h2, zero_mul])
  · have h := pos_mul (neg a) (neg a) h3 h3
    rw [neg_mul, mul_neg, neg_neg] at h
    exact Or.inr h

/-- A sum of two nonnegatives vanishes only if both do. -/
theorem nn_split (a b : Zp) (ha : Nn a) (hb : Nn b) (h : add a b = zero) :
    a = zero ∧ b = zero := by
  rcases ha with ha | ha
  · refine ⟨ha, ?_⟩
    rw [ha, zero_add] at h; exact h
  · rcases hb with hb | hb
    · refine ⟨?_, hb⟩
      rw [hb, add_zero] at h; exact h
    · exfalso
      have hp := pos_add a b ha hb
      rw [h] at hp
      exact absurd hp (by decide)

/-- A positive factor can be cancelled out of a nonnegativity claim. -/
theorem nn_of_mul_pos (c a : Zp) (hc : pos c = true) (h : Nn (mul c a)) : Nn a := by
  rcases trichotomy a with ⟨h1, _, _⟩ | ⟨_, h2, _⟩ | ⟨_, _, h3⟩
  · exact Or.inr h1
  · exact Or.inl h2
  · exfalso
    have hp := pos_mul c (neg a) hc h3
    rw [mul_neg] at hp
    exact not_nn (mul c a) hp h

/-- A positive factor can be cancelled out of a vanishing product. -/
theorem eq_zero_of_mul_pos (c a : Zp) (hc : pos c = true) (h : mul c a = zero) :
    a = zero := by
  by_cases hz : a = zero
  · exact hz
  · exact absurd h (mul_ne_zero c a (pos_ne_zero c hc) hz)

/-- ...and out of a vanishing square. -/
theorem eq_zero_of_mul_ne (c a : Zp) (hc : c ≠ zero) (h : mul c a = zero) : a = zero := by
  by_cases hz : a = zero
  · exact hz
  · exact absurd h (mul_ne_zero c a hc hz)

/-- ...and out of a vanishing square. -/
theorem eq_zero_of_sq (a : Zp) (h : mul a a = zero) : a = zero := by
  by_cases hz : a = zero
  · exact hz
  · exact absurd h (mul_ne_zero a a hz hz)

end Zp

/-! ══════════════════════════════════════════════════════════════════════
    ## §3.  THE SECOND-ORDER GERM — how `H` is *computed*, not asserted

    `J2 R` is the ring of second-order jets in four infinitesimals
    `ε₀ … ε₃` (all triple products zero): a value, four first-order slots,
    and the ten independent second-order slots.  Running `SS` — the very
    same `SS`, over `J2 R` instead of `R` — at the point
    `(p + ε₀, q + ε₁, r + ε₂, s + ε₃)` returns, in one pass, `SS` itself
    (`.v`), its gradient (`.d₀ … .d₃`), and its Hessian (`.e₀₀ … .e₃₃`, with
    `∂²/∂xᵢ² = 2·eᵢᵢ` and `∂²/∂xᵢ∂xⱼ = eᵢⱼ` for `i ≠ j`).

    So `hess` is not a matrix somebody typed in and claimed is the Hessian:
    it is the kernel's own second derivative of `SS`.  ADJUDICATOR: `rfl`.
    ══════════════════════════════════════════════════════════════════════ -/

/-- Second-order jets in four infinitesimals. -/
structure J2 (R : Type) where
  v : R
  d0 : R
  d1 : R
  d2 : R
  d3 : R
  e00 : R
  e01 : R
  e02 : R
  e03 : R
  e11 : R
  e12 : R
  e13 : R
  e22 : R
  e23 : R
  e33 : R
  deriving DecidableEq

/-- **STRUCTURE EXTENSIONALITY FOR `J2`** — fifteen field equations give one
    germ equation, by structure eta.  Pure plumbing: no arithmetic happens
    here, so it costs nothing.

    This is what makes the golden world (§9) reachable at the DEFAULT
    heartbeat budget.  Over `E = Z[φ][√φ]` a single `rfl` on the WHOLE germ
    overruns that budget, but each individual field projection does not — a
    projection out of `SS`'s jet result forces only the sub-fields that one
    slot depends on.  So §9 discharges the fifteen slots one at a time and
    reassembles them here, instead of transcribing the matrix. -/
theorem J2.ext' {R : Type} {g h : J2 R}
    (hv : g.v = h.v) (hd0 : g.d0 = h.d0) (hd1 : g.d1 = h.d1)
    (hd2 : g.d2 = h.d2) (hd3 : g.d3 = h.d3)
    (a00 : g.e00 = h.e00) (a01 : g.e01 = h.e01) (a02 : g.e02 = h.e02)
    (a03 : g.e03 = h.e03) (a11 : g.e11 = h.e11) (a12 : g.e12 = h.e12)
    (a13 : g.e13 = h.e13) (a22 : g.e22 = h.e22) (a23 : g.e23 = h.e23)
    (a33 : g.e33 = h.e33) : g = h := by
  show (⟨g.v, g.d0, g.d1, g.d2, g.d3, g.e00, g.e01, g.e02, g.e03,
         g.e11, g.e12, g.e13, g.e22, g.e23, g.e33⟩ : J2 R) =
       ⟨h.v, h.d0, h.d1, h.d2, h.d3, h.e00, h.e01, h.e02, h.e03,
        h.e11, h.e12, h.e13, h.e22, h.e23, h.e33⟩
  rw [hv, hd0, hd1, hd2, hd3, a00, a01, a02, a03, a11, a12, a13, a22, a23,
      a33]

/-- The jet ring.  Multiplication is the truncated Leibniz rule. -/
def j2Rng {R : Type} (K : Rng R) : Rng (J2 R) :=
  { zero := ⟨K.zero,K.zero,K.zero,K.zero,K.zero,K.zero,K.zero,K.zero,K.zero,
             K.zero,K.zero,K.zero,K.zero,K.zero,K.zero⟩
    one  := ⟨K.one,K.zero,K.zero,K.zero,K.zero,K.zero,K.zero,K.zero,K.zero,
             K.zero,K.zero,K.zero,K.zero,K.zero,K.zero⟩
    add  := fun u w => ⟨K.add u.v w.v, K.add u.d0 w.d0, K.add u.d1 w.d1,
      K.add u.d2 w.d2, K.add u.d3 w.d3, K.add u.e00 w.e00, K.add u.e01 w.e01,
      K.add u.e02 w.e02, K.add u.e03 w.e03, K.add u.e11 w.e11, K.add u.e12 w.e12,
      K.add u.e13 w.e13, K.add u.e22 w.e22, K.add u.e23 w.e23, K.add u.e33 w.e33⟩
    neg  := fun u => ⟨K.neg u.v, K.neg u.d0, K.neg u.d1, K.neg u.d2, K.neg u.d3,
      K.neg u.e00, K.neg u.e01, K.neg u.e02, K.neg u.e03, K.neg u.e11,
      K.neg u.e12, K.neg u.e13, K.neg u.e22, K.neg u.e23, K.neg u.e33⟩
    mul  := fun u w =>
      ⟨K.mul u.v w.v,
       K.add (K.mul u.v w.d0) (K.mul u.d0 w.v),
       K.add (K.mul u.v w.d1) (K.mul u.d1 w.v),
       K.add (K.mul u.v w.d2) (K.mul u.d2 w.v),
       K.add (K.mul u.v w.d3) (K.mul u.d3 w.v),
       K.add (K.add (K.mul u.v w.e00) (K.mul u.e00 w.v)) (K.mul u.d0 w.d0),
       K.add (K.add (K.mul u.v w.e01) (K.mul u.e01 w.v))
             (K.add (K.mul u.d0 w.d1) (K.mul u.d1 w.d0)),
       K.add (K.add (K.mul u.v w.e02) (K.mul u.e02 w.v))
             (K.add (K.mul u.d0 w.d2) (K.mul u.d2 w.d0)),
       K.add (K.add (K.mul u.v w.e03) (K.mul u.e03 w.v))
             (K.add (K.mul u.d0 w.d3) (K.mul u.d3 w.d0)),
       K.add (K.add (K.mul u.v w.e11) (K.mul u.e11 w.v)) (K.mul u.d1 w.d1),
       K.add (K.add (K.mul u.v w.e12) (K.mul u.e12 w.v))
             (K.add (K.mul u.d1 w.d2) (K.mul u.d2 w.d1)),
       K.add (K.add (K.mul u.v w.e13) (K.mul u.e13 w.v))
             (K.add (K.mul u.d1 w.d3) (K.mul u.d3 w.d1)),
       K.add (K.add (K.mul u.v w.e22) (K.mul u.e22 w.v)) (K.mul u.d2 w.d2),
       K.add (K.add (K.mul u.v w.e23) (K.mul u.e23 w.v))
             (K.add (K.mul u.d2 w.d3) (K.mul u.d3 w.d2)),
       K.add (K.add (K.mul u.v w.e33) (K.mul u.e33 w.v)) (K.mul u.d3 w.d3)⟩ }

/-- The `k`-th coordinate of the point, carrying its own infinitesimal. -/
def jp {R : Type} (K : Rng R) (a : R) (k : Nat) : J2 R :=
  ⟨a, (if k == 0 then K.one else K.zero), (if k == 1 then K.one else K.zero),
      (if k == 2 then K.one else K.zero), (if k == 3 then K.one else K.zero),
   K.zero,K.zero,K.zero,K.zero,K.zero,K.zero,K.zero,K.zero,K.zero,K.zero⟩

/-- **THE GERM.**  `SS` evaluated over the jet ring at the given point. -/
def germ {R : Type} (K : Rng R) (p q r sp : R) : J2 R :=
  SS (j2Rng K) (Fg (jp K p 0) (jp K q 1) (jp K r 2) (jp K sp 3))

/-- The Hessian read off a germ.  Diagonal entries are doubled because the
    `εᵢ²` coefficient of a function is `½·∂²f/∂xᵢ²`. -/
def hessOf {R : Type} (K : Rng R) (g : J2 R) : Fin 4 → Fin 4 → R := fun a b =>
  match a.val, b.val with
  | 0, 0 => K.add g.e00 g.e00
  | 0, 1 => g.e01
  | 0, 2 => g.e02
  | 0, 3 => g.e03
  | 1, 0 => g.e01
  | 1, 1 => K.add g.e11 g.e11
  | 1, 2 => g.e12
  | 1, 3 => g.e13
  | 2, 0 => g.e02
  | 2, 1 => g.e12
  | 2, 2 => K.add g.e22 g.e22
  | 2, 3 => g.e23
  | 3, 0 => g.e03
  | 3, 1 => g.e13
  | 3, 2 => g.e23
  | _, _ => K.add g.e33 g.e33

/-- **THE HESSIAN** of the pentagon sum-of-squares residual at `(p,q,r,s)`. -/
def hess {R : Type} (K : Rng R) (p q r sp : R) : Fin 4 → Fin 4 → R :=
  hessOf K (germ K p q r sp)

/-- The gradient, read off the same germ. -/
def gradOf {R : Type} (g : J2 R) : Fin 4 → R := fun a =>
  match a.val with
  | 0 => g.d0
  | 1 => g.d1
  | 2 => g.d2
  | _ => g.d3

/-- The Boolean pentagon check, so "is a solution" is a hypothesis we can
    state and decide.  `Anyon.lean`'s `pentagonCheck` carries `Rng.beq`; this
    file's `Rng` carries `neg` instead, so the check is phrased through
    `DecidableEq Zp` on the residual.  Same content, same convention: `true`
    vacuously off the valid set. -/
def pentOK (F : Anyon → Anyon → Zp) (a b c dd x y t w v : Anyon) : Bool :=
  if pentagonValid a b c dd x y t w v then
    decide (pentResid zpRng F a b c dd x y t w v = Zp.zero)
  else true

/-! ══════════════════════════════════════════════════════════════════════
    ## §4.  QUADRATIC FORMS OVER `Z[φ]`, AND SOS CERTIFICATES
    ══════════════════════════════════════════════════════════════════════ -/

abbrev V4 := Fin 4 → Zp
abbrev M4 := Fin 4 → Fin 4 → Zp

def mkV (a b c d : Zp) : V4 := fun i =>
  match i.val with
  | 0 => a
  | 1 => b
  | 2 => c
  | _ => d

def dot (u w : V4) : Zp :=
  Zp.add (Zp.add (Zp.mul (u 0) (w 0)) (Zp.mul (u 1) (w 1)))
         (Zp.add (Zp.mul (u 2) (w 2)) (Zp.mul (u 3) (w 3)))

def mvec (A : M4) (w : V4) : V4 := fun a => dot (fun b => A a b) w

/-- `wᵀAw`. -/
def qform (A : M4) (w : V4) : Zp := dot w (mvec A w)

def outer (u : V4) : M4 := fun a b => Zp.mul (u a) (u b)
def smulM (c : Zp) (A : M4) : M4 := fun a b => Zp.mul c (A a b)
def addM (A B : M4) : M4 := fun a b => Zp.add (A a b) (B a b)

theorem dot_mk (a b c d : Zp) (w : V4) :
    dot (mkV a b c d) w =
      Zp.add (Zp.add (Zp.mul a (w 0)) (Zp.mul b (w 1)))
             (Zp.add (Zp.mul c (w 2)) (Zp.mul d (w 3))) := rfl

theorem dot_congr (u u' w : V4) (h : ∀ k, u k = u' k) : dot u w = dot u' w := by
  have e : u = u' := funext h
  rw [e]

theorem dot_left_smul (c : Zp) (u w : V4) :
    dot (fun k => Zp.mul c (u k)) w = Zp.mul c (dot u w) := by
  show Zp.add (Zp.add (Zp.mul (Zp.mul c (u 0)) (w 0))
                      (Zp.mul (Zp.mul c (u 1)) (w 1)))
              (Zp.add (Zp.mul (Zp.mul c (u 2)) (w 2))
                      (Zp.mul (Zp.mul c (u 3)) (w 3)))
     = Zp.mul c (Zp.add (Zp.add (Zp.mul (u 0) (w 0)) (Zp.mul (u 1) (w 1)))
                        (Zp.add (Zp.mul (u 2) (w 2)) (Zp.mul (u 3) (w 3))))
  rw [Zp.mul_assoc c (u 0) (w 0), Zp.mul_assoc c (u 1) (w 1),
      Zp.mul_assoc c (u 2) (w 2), Zp.mul_assoc c (u 3) (w 3),
      Zp.mul_add, Zp.mul_add, Zp.mul_add]

theorem dot_right_smul (c : Zp) (u v : V4) :
    dot u (fun k => Zp.mul c (v k)) = Zp.mul c (dot u v) := by
  show Zp.add (Zp.add (Zp.mul (u 0) (Zp.mul c (v 0)))
                      (Zp.mul (u 1) (Zp.mul c (v 1))))
              (Zp.add (Zp.mul (u 2) (Zp.mul c (v 2)))
                      (Zp.mul (u 3) (Zp.mul c (v 3))))
     = Zp.mul c (Zp.add (Zp.add (Zp.mul (u 0) (v 0)) (Zp.mul (u 1) (v 1)))
                        (Zp.add (Zp.mul (u 2) (v 2)) (Zp.mul (u 3) (v 3))))
  rw [Zp.mul_left_comm (u 0) c (v 0), Zp.mul_left_comm (u 1) c (v 1),
      Zp.mul_left_comm (u 2) c (v 2), Zp.mul_left_comm (u 3) c (v 3),
      Zp.mul_add, Zp.mul_add, Zp.mul_add]

theorem dot_left_add (u v w : V4) :
    dot (fun k => Zp.add (u k) (v k)) w = Zp.add (dot u w) (dot v w) := by
  simp only [dot, Zp.add_mul]
  simp only [Zp.add_assoc, Zp.add_left_comm]

theorem dot_right_add (u v w : V4) :
    dot u (fun k => Zp.add (v k) (w k)) = Zp.add (dot u v) (dot u w) := by
  simp only [dot, Zp.mul_add]
  simp only [Zp.add_assoc, Zp.add_left_comm]

theorem dot_comm (u w : V4) : dot u w = dot w u := by
  simp only [dot]
  rw [Zp.mul_comm (u 0) (w 0), Zp.mul_comm (u 1) (w 1),
      Zp.mul_comm (u 2) (w 2), Zp.mul_comm (u 3) (w 3)]

theorem qform_congr (A B : M4) (w : V4) (h : ∀ a b, A a b = B a b) :
    qform A w = qform B w := by
  have e : A = B := funext (fun a => funext (fun b => h a b))
  rw [e]

theorem qform_add (A B : M4) (w : V4) :
    qform (addM A B) w = Zp.add (qform A w) (qform B w) := by
  have e : mvec (addM A B) w = fun a => Zp.add (mvec A w a) (mvec B w a) :=
    funext (fun a => dot_left_add (fun b => A a b) (fun b => B a b) w)
  show dot w (mvec (addM A B) w) = _
  rw [e, dot_right_add]
  rfl

theorem qform_smul (c : Zp) (A : M4) (w : V4) :
    qform (smulM c A) w = Zp.mul c (qform A w) := by
  have e : mvec (smulM c A) w = fun a => Zp.mul c (mvec A w a) :=
    funext (fun a => dot_left_smul c (fun b => A a b) w)
  show dot w (mvec (smulM c A) w) = _
  rw [e, dot_right_smul]
  rfl

theorem qform_outer (u w : V4) :
    qform (outer u) w = Zp.mul (dot u w) (dot u w) := by
  have e : mvec (outer u) w = fun a => Zp.mul (dot u w) (u a) := by
    refine funext (fun a => ?_)
    show dot (fun b => Zp.mul (u a) (u b)) w = _
    rw [dot_left_smul (u a) u w]
    exact Zp.mul_comm _ _
  show dot w (mvec (outer u) w) = _
  rw [e, dot_right_smul, dot_comm]

/-- **THE SUM-OF-SQUARES TRANSFER.**  A matrix identity
    `N·A = e₁·L₁⊗L₁ + e₂·L₂⊗L₂ + e₃·L₃⊗L₃` becomes, for every `w`, the scalar
    identity `N·(wᵀAw) = e₁(L₁·w)² + e₂(L₂·w)² + e₃(L₃·w)²`. -/
theorem qform_sos (N e1 e2 e3 : Zp) (A : M4) (L1 L2 L3 : V4)
    (h : ∀ a b, Zp.mul N (A a b) =
      Zp.add (Zp.add (Zp.mul e1 (Zp.mul (L1 a) (L1 b)))
                     (Zp.mul e2 (Zp.mul (L2 a) (L2 b))))
             (Zp.mul e3 (Zp.mul (L3 a) (L3 b))))
    (w : V4) :
    Zp.mul N (qform A w) =
      Zp.add (Zp.add (Zp.mul e1 (Zp.mul (dot L1 w) (dot L1 w)))
                     (Zp.mul e2 (Zp.mul (dot L2 w) (dot L2 w))))
             (Zp.mul e3 (Zp.mul (dot L3 w) (dot L3 w))) := by
  have hcong : qform (smulM N A) w =
      qform (addM (addM (smulM e1 (outer L1)) (smulM e2 (outer L2)))
                  (smulM e3 (outer L3))) w :=
    qform_congr _ _ w (fun a b => h a b)
  rw [qform_smul] at hcong
  rw [hcong, qform_add, qform_add, qform_smul, qform_smul, qform_smul,
      qform_outer, qform_outer, qform_outer]

/-- **POSITIVE SEMIDEFINITENESS FROM A SOS CERTIFICATE.** -/
theorem psd_of_sos (N e1 e2 e3 : Zp) (A : M4) (L1 L2 L3 : V4)
    (h : ∀ a b, Zp.mul N (A a b) =
      Zp.add (Zp.add (Zp.mul e1 (Zp.mul (L1 a) (L1 b)))
                     (Zp.mul e2 (Zp.mul (L2 a) (L2 b))))
             (Zp.mul e3 (Zp.mul (L3 a) (L3 b))))
    (hN : Zp.pos N = true) (h1 : Zp.pos e1 = true) (h2 : Zp.pos e2 = true)
    (h3 : Zp.pos e3 = true) (w : V4) : Zp.Nn (qform A w) := by
  refine Zp.nn_of_mul_pos N (qform A w) hN ?_
  rw [qform_sos N e1 e2 e3 A L1 L2 L3 h w]
  exact Zp.nn_add _ _
    (Zp.nn_add _ _ (Zp.nn_mul _ _ (Or.inr h1) (Zp.nn_sq _))
                   (Zp.nn_mul _ _ (Or.inr h2) (Zp.nn_sq _)))
    (Zp.nn_mul _ _ (Or.inr h3) (Zp.nn_sq _))

/-- **THE NULL SPACE FROM A SOS CERTIFICATE.**  `wᵀAw = 0` exactly when `w` is
    annihilated by all three linear forms of the certificate. -/
theorem ker_of_sos (N e1 e2 e3 : Zp) (A : M4) (L1 L2 L3 : V4)
    (h : ∀ a b, Zp.mul N (A a b) =
      Zp.add (Zp.add (Zp.mul e1 (Zp.mul (L1 a) (L1 b)))
                     (Zp.mul e2 (Zp.mul (L2 a) (L2 b))))
             (Zp.mul e3 (Zp.mul (L3 a) (L3 b))))
    (hN : Zp.pos N = true) (h1 : Zp.pos e1 = true) (h2 : Zp.pos e2 = true)
    (h3 : Zp.pos e3 = true) (w : V4) :
    qform A w = Zp.zero ↔
      (dot L1 w = Zp.zero ∧ dot L2 w = Zp.zero ∧ dot L3 w = Zp.zero) := by
  have key := qform_sos N e1 e2 e3 A L1 L2 L3 h w
  constructor
  · intro hz
    rw [hz, Zp.mul_zero] at key
    have hs := (Zp.nn_split _ _
      (Zp.nn_add _ _ (Zp.nn_mul _ _ (Or.inr h1) (Zp.nn_sq _))
                     (Zp.nn_mul _ _ (Or.inr h2) (Zp.nn_sq _)))
      (Zp.nn_mul _ _ (Or.inr h3) (Zp.nn_sq _)) key.symm)
    have hs2 := Zp.nn_split _ _
      (Zp.nn_mul _ _ (Or.inr h1) (Zp.nn_sq _))
      (Zp.nn_mul _ _ (Or.inr h2) (Zp.nn_sq _)) hs.1
    exact ⟨Zp.eq_zero_of_sq _ (Zp.eq_zero_of_mul_pos _ _ h1 hs2.1),
           Zp.eq_zero_of_sq _ (Zp.eq_zero_of_mul_pos _ _ h2 hs2.2),
           Zp.eq_zero_of_sq _ (Zp.eq_zero_of_mul_pos _ _ h3 hs.2)⟩
  · intro hk
    rw [hk.1, hk.2.1, hk.2.2] at key
    simp only [Zp.mul_zero, Zp.add_zero] at key
    exact Zp.eq_zero_of_mul_pos N (qform A w) hN key

/-! ### determinants, for the rank statement -/

def det2 (a b c d : Zp) : Zp := Zp.sub (Zp.mul a d) (Zp.mul b c)

def det3 (A : M4) (r0 r1 r2 c0 c1 c2 : Fin 4) : Zp :=
  Zp.add (Zp.sub (Zp.mul (A r0 c0) (det2 (A r1 c1) (A r1 c2) (A r2 c1) (A r2 c2)))
                 (Zp.mul (A r0 c1) (det2 (A r1 c0) (A r1 c2) (A r2 c0) (A r2 c2))))
         (Zp.mul (A r0 c2) (det2 (A r1 c0) (A r1 c1) (A r2 c0) (A r2 c1)))

def det4 (A : M4) : Zp :=
  Zp.add (Zp.sub (Zp.mul (A 0 0) (det3 A 1 2 3 1 2 3))
                 (Zp.mul (A 0 1) (det3 A 1 2 3 0 2 3)))
         (Zp.sub (Zp.mul (A 0 2) (det3 A 1 2 3 0 1 3))
                 (Zp.mul (A 0 3) (det3 A 1 2 3 0 1 2)))

/-! ### the standard covectors -/

def E0 : V4 := mkV Zp.one Zp.zero Zp.zero Zp.zero
def E3 : V4 := mkV Zp.zero Zp.zero Zp.zero Zp.one

theorem dot_E0 (w : V4) : dot E0 w = w 0 := by
  show Zp.add (Zp.add (Zp.mul Zp.one (w 0)) (Zp.mul Zp.zero (w 1)))
              (Zp.add (Zp.mul Zp.zero (w 2)) (Zp.mul Zp.zero (w 3))) = w 0
  simp only [Zp.zero_mul, Zp.one_mul, Zp.add_zero]

theorem dot_E3 (w : V4) : dot E3 w = w 3 := by
  show Zp.add (Zp.add (Zp.mul Zp.zero (w 0)) (Zp.mul Zp.zero (w 1)))
              (Zp.add (Zp.mul Zp.zero (w 2)) (Zp.mul Zp.one (w 3))) = w 3
  simp only [Zp.zero_mul, Zp.one_mul, Zp.zero_add, Zp.add_zero]

/-! ══════════════════════════════════════════════════════════════════════
    ## §5.  THE YANG–LEE WORLD  `(p,q,r,s) = (−φ, 1, −φ, φ)`

    This is the half that carries the weight.  Here `q ≠ r`, so the `q↔r`
    swap symmetry gives nothing away, and "the flat direction is the GAUGE
    tangent" is a statement with content rather than a freebie.  Everything
    in this section lives in `Z[φ] = Q(√5)`'s ring of integers — no `√φ`
    anywhere, so the whole section runs on round-5 technology unchanged.
    ══════════════════════════════════════════════════════════════════════ -/

def pY : Zp := Zp.neg Zp.phi
def qY : Zp := Zp.one
def rY : Zp := Zp.neg Zp.phi
def sY : Zp := Zp.phi

/-- The Yang–Lee point sits on the variety `pentagon_iff` describes:
    `q·r = p` and `s = −p`. -/
theorem YL_on_variety : Zp.mul qY rY = pY ∧ sY = Zp.neg pY := by decide

/-- **THE HYPOTHESIS, DECIDED.**  Yang–Lee IS a pentagon solution: all 512
    label tuples pass, the 462 invalid ones vacuously and the 50 live ones as
    genuine identities in `Z[φ]`.  This hypothesis is load-bearing — see the
    strict-associator section. -/
theorem YL_is_solution :
    ∀ a b c dd x y t w v, pentOK (Fg pY qY rY sY) a b c dd x y t w v = true := by
  intro a b c dd x y t w v
  cases a <;> cases b <;> cases c <;> cases dd <;> cases x <;> cases y <;>
    cases t <;> cases w <;> cases v <;> rfl

/-- ANTI-VACUITY for the check: it is not constant-`true` on the live set —
    the strict associator fails instance #1. -/
theorem pentOK_not_constant :
    pentOK (Fg Zp.one Zp.one Zp.one Zp.one) .tau .tau .tau .tau .one .tau .one .one .tau
      = false := by decide

/-- The second-order germ of `SS` at Yang–Lee, computed by the kernel. -/
def GY : J2 Zp :=
  ⟨Zp.zero, Zp.zero, Zp.zero, Zp.zero, Zp.zero,
   ⟨15,10⟩, ⟨8,18⟩, ⟨-10,-8⟩, ⟨12,18⟩,
   ⟨8,9⟩, ⟨-2,-16⟩, ⟨-4,-8⟩,
   ⟨7,1⟩, ⟨4,4⟩,
   ⟨29,29⟩⟩

/-- **THE GERM, DECIDED.**  One `rfl`; every downstream fact reads off `GY`. -/
theorem germ_Y : germ zpRng pY qY rY sY = GY := by rfl

/-- `SS` vanishes at Yang–Lee — the residual sum is exactly zero, and this is
    the germ's own value slot, not a separate computation. -/
theorem SS_Y_zero : (germ zpRng pY qY rY sY).v = Zp.zero := by rw [germ_Y]; rfl

/-- ...and Yang–Lee is a critical point: the gradient of `SS` vanishes. -/
theorem grad_Y_zero : ∀ i, gradOf (germ zpRng pY qY rY sY) i = Zp.zero := by
  rw [germ_Y]; decide

/-- **THE HESSIAN AT YANG–LEE**, entries exact in `Z[φ]`:
    `⟨30,20⟩ ⟨8,18⟩ ⟨−10,−8⟩ ⟨12,18⟩ / ⟨16,18⟩ ⟨−2,−16⟩ ⟨−4,−8⟩ /
     ⟨14,2⟩ ⟨4,4⟩ / ⟨58,58⟩` in the basis `m + nφ`. -/
def HY : M4 := hessOf zpRng GY

theorem hess_Y : hess zpRng pY qY rY sY = HY := by
  show hessOf zpRng (germ zpRng pY qY rY sY) = hessOf zpRng GY
  rw [germ_Y]

theorem HY_symm : ∀ a b, HY a b = HY b a := by decide

theorem HY_entries :
    HY 0 0 = ⟨30,20⟩ ∧ HY 0 1 = ⟨8,18⟩ ∧ HY 0 2 = ⟨-10,-8⟩ ∧ HY 0 3 = ⟨12,18⟩ ∧
    HY 1 1 = ⟨16,18⟩ ∧ HY 1 2 = ⟨-2,-16⟩ ∧ HY 1 3 = ⟨-4,-8⟩ ∧
    HY 2 2 = ⟨14,2⟩ ∧ HY 2 3 = ⟨4,4⟩ ∧ HY 3 3 = ⟨58,58⟩ := by decide

/-! ### The gauge-torus tangent, and the certificate's covectors -/

/-- The gauge-torus tangent `(0, q, −r, 0)` — at Yang–Lee, `(0, 1, φ, 0)`.

    ADJUDICATOR (norm 15; added round 6 after an audit found this the one
    artifact class in the file whose name did the rhetorical work without one).

    WHY THIS VECTOR IS *THE GAUGE TANGENT*, and where that is settled.
    `Anyon.lean`'s pentagon uniqueness leaves exactly one residual freedom in a
    solution: `q ↦ λq`, `r ↦ λ⁻¹r`, with `p` and `s` fixed — the diagonal is
    pinned by `pentagon_exactly_two_worlds` and the off-diagonal only through
    the product `qr`.  So the gauge orbit through `(p, q, r, s)` is the curve
    `γ(λ) = (p, λq, λ⁻¹r, s)`, and

        γ'(1) = (0, q, −r, 0)

    by differentiating each coordinate at `λ = 1`.  `gauge_curve_deriv` below
    proves the discrete content of that one-line computation *inside this
    file*: the curve stays on the orbit (`qr` is invariant) and the difference
    quotient at `λ = 1` is exactly this vector.

    WHAT THIS DOES NOT COVER.  That the residual freedom IS `q ↦ λq, r ↦ λ⁻¹r`
    — i.e. that the gauge group is that torus and nothing larger — is proved in
    `Anyon.lean` (`pentagon_iff` plus `tier3a_tier3b_same_anyon`), not here,
    and this file has zero imports so it cannot cite those theorems as terms.
    That is class 10's boundary: a cross-file semantic claim, adjudicated by
    the builder's source audit.  What *is* settled here is the differentiation
    step, which is the part that was previously only a word. -/
def tangentY : V4 := mkV Zp.zero qY (Zp.neg rY) Zp.zero

/-- **THE GAUGE CURVE, AND ITS DERIVATIVE.**  For **any** scalar `l` with an
    inverse `li` (`l·li = 1`), the reparametrisation `(p, l·q, li·r, s)` leaves
    the product `qr` fixed **exactly** — not merely to first order — so it stays
    inside the solution set that `pentagon_iff` cuts out; and the first-order
    cross-term of that product, `q·(−r) + q·r`, vanishes, which is the reason
    differentiating the curve at `l = 1` gives a tangent with no `p`- or
    `s`-component and `q`, `−r` in the middle two.

    (Round-7 correction G5: the earlier statement fixed `l = 1` in every
    conjunct while the docstring said "for any scalar `l`", and it omitted the
    cross-term fact the tangent argument actually turns on.  Both are repaired:
    the invariance is now genuinely `∀ l li`, and the cross-term conjunct is
    present.  That the resulting tangent is `(0, q, −r, 0)` and equals
    `tangentY` at Yang–Lee is `tangentY_is_gauge_deriv` just below.) -/
theorem gauge_curve_deriv (l li q r : Zp) (hli : Zp.mul l li = Zp.one) :
    Zp.mul (Zp.mul l q) (Zp.mul li r) = Zp.mul q r ∧
    Zp.add (Zp.mul q (Zp.neg r)) (Zp.mul q r) = Zp.zero := by
  refine ⟨?_, ?_⟩
  · calc Zp.mul (Zp.mul l q) (Zp.mul li r)
        = Zp.mul l (Zp.mul q (Zp.mul li r)) := Zp.mul_assoc _ _ _
      _ = Zp.mul l (Zp.mul li (Zp.mul q r)) := by rw [Zp.mul_left_comm q li r]
      _ = Zp.mul (Zp.mul l li) (Zp.mul q r) := (Zp.mul_assoc _ _ _).symm
      _ = Zp.mul Zp.one (Zp.mul q r) := by rw [hli]
      _ = Zp.mul q r := Zp.one_mul _
  · rw [Zp.mul_neg, Zp.add_comm]; exact Zp.add_neg _

/-- ...and at Yang–Lee that tangent vector is literally `tangentY`. -/
theorem tangentY_is_gauge_deriv :
    tangentY 0 = Zp.zero ∧ tangentY 1 = qY ∧
    tangentY 2 = Zp.neg rY ∧ tangentY 3 = Zp.zero :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Its annihilating covector `(0, r, q, 0)`: `dot coTY w = 0` says exactly
    `w₁·r + w₂·q = 0`, the certificate's `in_span_tangent` test. -/
def coTY : V4 := mkV Zp.zero rY qY Zp.zero

/-- The `q↔r` SWAP direction `(0, 1, −1, 0)`.  Not the same vector as the
    gauge tangent unless `q = r`. -/
def swapDir : V4 := mkV Zp.zero Zp.one (Zp.neg Zp.one) Zp.zero

theorem tangentY_ne_swapDir : ¬ (∀ k, tangentY k = swapDir k) := by decide

/-- **`H·(0,q,−r,0) = 0`** — the gauge tangent is null, exactly. -/
theorem HY_tangent_null : ∀ a, mvec HY tangentY a = Zp.zero := by decide

/-- **THE SWAP DIRECTION IS NOT NULL AT YANG–LEE.**  This is what makes the
    null-space claim content rather than symmetry: `H·(0,1,−1,0) ≠ 0`, and
    the quadratic form on it is strictly positive. -/
theorem HY_swap_not_null :
    mvec HY swapDir 0 ≠ Zp.zero ∧ qform HY swapDir = ⟨34,52⟩ ∧
    Zp.pos (qform HY swapDir) = true := by
  refine ⟨by decide, by decide, by decide⟩

/-! ### rank exactly three -/

/-- `det H = 0`: the rank is at most 3. -/
theorem HY_det4_zero : det4 HY = Zp.zero := by decide

/-- ...and the principal `(p,q,s)` minor is strictly positive, so the rank is
    at least 3.  Together: rank exactly 3. -/
theorem HY_minor3_pos :
    det3 HY 0 1 3 0 1 3 = ⟨21120,31480⟩ ∧ Zp.pos (det3 HY 0 1 3 0 1 3) = true := by
  refine ⟨by decide, by decide⟩

/-! ### the sum-of-squares certificate

    Produced by fraction-free (Bareiss) symmetric elimination on the pivot
    order `(p, q, s)` with `r` free; `N`, `e₁`, `e₂` are the successive
    pivots' products and are positive by `Zp.pos`. -/

def NY  : Zp := ⟨111227520000, 179906032000⟩
def eY1 : Zp := ⟨1784777600, 2884209600⟩
def eY2 : Zp := ⟨1263200, 1996400⟩
def eY3 : Zp := Zp.one

def LY1 : V4 := mkV ⟨30,20⟩ ⟨8,18⟩ ⟨-10,-8⟩ ⟨12,18⟩
def LY2 : V4 := mkV Zp.zero ⟨452,608⟩ ⟨-156,-452⟩ ⟨-700,-1164⟩
def LY3 : V4 := mkV Zp.zero Zp.zero Zp.zero ⟨1263200,1996400⟩

/-- **THE CERTIFICATE.**  `N·H = e₁·L₁⊗L₁ + e₂·L₂⊗L₂ + e₃·L₃⊗L₃`, sixteen
    exact identities in `Z[φ]`. -/
theorem sos_Y : ∀ a b, Zp.mul NY (HY a b) =
    Zp.add (Zp.add (Zp.mul eY1 (Zp.mul (LY1 a) (LY1 b)))
                   (Zp.mul eY2 (Zp.mul (LY2 a) (LY2 b))))
           (Zp.mul eY3 (Zp.mul (LY3 a) (LY3 b))) := by decide

theorem sos_Y_pos :
    Zp.pos NY = true ∧ Zp.pos eY1 = true ∧ Zp.pos eY2 = true ∧
    Zp.pos eY3 = true := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- **POSITIVE SEMIDEFINITE.**  `wᵀHw ≥ 0` for every `w : Z[φ]⁴`. -/
theorem HY_psd (w : V4) : Zp.Nn (qform HY w) :=
  psd_of_sos NY eY1 eY2 eY3 HY LY1 LY2 LY3 sos_Y
    (by decide) (by decide) (by decide) (by decide) w

/-! ### the null space, exactly -/

def cY3  : Zp := ⟨1263200,1996400⟩
def lamY : Zp := ⟨-156,-452⟩
def aY3  : Zp := ⟨-700,-1164⟩
def bY0  : Zp := ⟨30,20⟩
def bY2  : Zp := ⟨-10,-8⟩
def bY3  : Zp := ⟨12,18⟩

theorem dotLY3 (w : V4) : dot LY3 w = Zp.mul cY3 (dot E3 w) := by
  have h : ∀ k, LY3 k = Zp.mul cY3 (E3 k) := by decide
  calc dot LY3 w = dot (fun k => Zp.mul cY3 (E3 k)) w := dot_congr _ _ w h
    _ = Zp.mul cY3 (dot E3 w) := dot_left_smul cY3 E3 w

theorem dotLY2 (w : V4) :
    dot LY2 w = Zp.add (Zp.mul lamY (dot coTY w)) (Zp.mul aY3 (dot E3 w)) := by
  have h : ∀ k, LY2 k = Zp.add (Zp.mul lamY (coTY k)) (Zp.mul aY3 (E3 k)) := by decide
  calc dot LY2 w
      = dot (fun k => Zp.add (Zp.mul lamY (coTY k)) (Zp.mul aY3 (E3 k))) w :=
        dot_congr _ _ w h
    _ = Zp.add (dot (fun k => Zp.mul lamY (coTY k)) w)
               (dot (fun k => Zp.mul aY3 (E3 k)) w) := dot_left_add _ _ w
    _ = Zp.add (Zp.mul lamY (dot coTY w)) (Zp.mul aY3 (dot E3 w)) := by
        rw [dot_left_smul, dot_left_smul]

theorem dotLY1 (w : V4) :
    dot LY1 w = Zp.add (Zp.add (Zp.mul bY0 (dot E0 w)) (Zp.mul bY2 (dot coTY w)))
                       (Zp.mul bY3 (dot E3 w)) := by
  have h : ∀ k, LY1 k =
      Zp.add (Zp.add (Zp.mul bY0 (E0 k)) (Zp.mul bY2 (coTY k))) (Zp.mul bY3 (E3 k)) := by
    decide
  calc dot LY1 w
      = dot (fun k => Zp.add (Zp.add (Zp.mul bY0 (E0 k)) (Zp.mul bY2 (coTY k)))
                             (Zp.mul bY3 (E3 k))) w := dot_congr _ _ w h
    _ = Zp.add (dot (fun k => Zp.add (Zp.mul bY0 (E0 k)) (Zp.mul bY2 (coTY k))) w)
               (dot (fun k => Zp.mul bY3 (E3 k)) w) := dot_left_add _ _ w
    _ = Zp.add (Zp.add (dot (fun k => Zp.mul bY0 (E0 k)) w)
                       (dot (fun k => Zp.mul bY2 (coTY k)) w))
               (dot (fun k => Zp.mul bY3 (E3 k)) w) := by rw [dot_left_add]
    _ = Zp.add (Zp.add (Zp.mul bY0 (dot E0 w)) (Zp.mul bY2 (dot coTY w)))
               (Zp.mul bY3 (dot E3 w)) := by
        rw [dot_left_smul, dot_left_smul, dot_left_smul]

/-- **THE NULL SPACE IS EXACTLY THE GAUGE-TORUS TANGENT.**
    `wᵀHw = 0` iff `w₀ = 0`, `w₃ = 0` and `w₁·r + w₂·q = 0` — i.e. iff `w`
    lies on the line spanned by `(0, q, −r, 0)`. -/
theorem HY_kernel (w : V4) :
    qform HY w = Zp.zero ↔
      (w 0 = Zp.zero ∧ w 3 = Zp.zero ∧ dot coTY w = Zp.zero) := by
  rw [ker_of_sos NY eY1 eY2 eY3 HY LY1 LY2 LY3 sos_Y
        (by decide) (by decide) (by decide) (by decide) w]
  constructor
  · rintro ⟨k1, k2, k3⟩
    rw [dotLY3] at k3
    have e3 : dot E3 w = Zp.zero := Zp.eq_zero_of_mul_pos cY3 _ (by decide) k3
    rw [dotLY2, e3, Zp.mul_zero, Zp.add_zero] at k2
    have ec : dot coTY w = Zp.zero := Zp.eq_zero_of_mul_ne lamY _ (by decide) k2
    rw [dotLY1, e3, ec, Zp.mul_zero, Zp.mul_zero, Zp.add_zero, Zp.add_zero] at k1
    have e0 : dot E0 w = Zp.zero := Zp.eq_zero_of_mul_pos bY0 _ (by decide) k1
    rw [dot_E0] at e0
    rw [dot_E3] at e3
    exact ⟨e0, e3, ec⟩
  · rintro ⟨h0, h3, hc⟩
    have e0 : dot E0 w = Zp.zero := by rw [dot_E0]; exact h0
    have e3 : dot E3 w = Zp.zero := by rw [dot_E3]; exact h3
    refine ⟨?_, ?_, ?_⟩
    · rw [dotLY1, e0, hc, e3, Zp.mul_zero, Zp.mul_zero, Zp.mul_zero]; decide
    · rw [dotLY2, hc, e3, Zp.mul_zero, Zp.mul_zero]; decide
    · rw [dotLY3, e3, Zp.mul_zero]

/-- The tangent itself is in the kernel, so the theorem above is not about an
    empty set. -/
theorem HY_tangent_in_kernel : qform HY tangentY = Zp.zero := by decide

/-- The kernel condition, unpacked: a null `w` is exactly `w₁·(0,1,φ,0)`. -/
theorem HY_kernel_is_line (w : V4) (h : qform HY w = Zp.zero) :
    w 0 = Zp.zero ∧ w 3 = Zp.zero ∧ w 2 = Zp.mul Zp.phi (w 1) := by
  obtain ⟨h0, h3, hc⟩ := (HY_kernel w).mp h
  refine ⟨h0, h3, ?_⟩
  have hcc : Zp.add (Zp.neg (Zp.mul Zp.phi (w 1))) (w 2) = Zp.zero := by
    have e : dot coTY w = Zp.add (Zp.neg (Zp.mul Zp.phi (w 1))) (w 2) := by
      show Zp.add (Zp.add (Zp.mul Zp.zero (w 0)) (Zp.mul rY (w 1)))
                  (Zp.add (Zp.mul qY (w 2)) (Zp.mul Zp.zero (w 3))) = _
      simp only [rY, qY, Zp.zero_mul, Zp.one_mul, Zp.neg_mul, Zp.zero_add,
                 Zp.add_zero]
    rw [e] at hc; exact hc
  exact (Zp.eq_zero_of_add_neg (w 2) (Zp.mul Zp.phi (w 1))
          (by rw [Zp.add_comm]; exact hcc))

/-- ANTI-VACUITY: the null line is a line, not the whole space — the swap
    direction is a `w` with `wᵀHw ≠ 0`. -/
theorem HY_kernel_proper : qform HY swapDir ≠ Zp.zero := by decide

/-! ══════════════════════════════════════════════════════════════════════
    ## §6.  THE `q↔r` SWAP SYMMETRY — why the golden null direction is a
    freebie

    `SS` is invariant under transposing the associator matrix, `F ↦ Fᵀ`,
    i.e. under `q ↔ r`.  The residual-level mechanism is proved here in full
    generality (`Fs_rev`, `pentResid_rev`): reversing the object string
    `(a,b,c,d) ↦ (d,c,b,a)` and transposing `F` reproduces every pentagon
    residual on the nose.  Consequently, at ANY point with `q = r`, columns
    `q` and `r` of `H` coincide and `(0,1,−1,0)` is null FOR FREE — no
    solutionhood, no rigidity, nothing but the symmetry.

    NOT PROVED HERE, and named as such: the step from `pentResid_rev` to
    `SS K (transp F) = SS K F` is a reindexing of the 512-fold nested sum by
    the involution `(a,b,c,d,x,y,t,w,v) ↦ (d,c,b,a,w,v,t,x,y)`, which needs a
    permutation-invariance lemma for nine nested `sumOver`s that this file
    does not contain.  ADJUDICATOR for that missing step: the builder's
    certificate `r6_gift_hessian.py`, check `V3e.swap_symmetry`, which
    verifies `swapqr_poly(RSUM) == RSUM` symbolically in `Z[p,q,r,s]`.  Every
    `q = r` specimen in THIS file has its column-coincidence decided by the
    kernel instead (`HS_cols_eq` below), so nothing here rests on the gap. -/

theorem fuse_comm (a b : Anyon) : fuse a b = fuse b a := by
  cases a <;> cases b <;> rfl

/-- Transpose of an associator matrix.  `transp (Fg p q r s) = Fg p r q s`. -/
def transp {R : Type} (F : Anyon → Anyon → R) : Anyon → Anyon → R := fun i j => F j i

theorem Fg_transp {R : Type} (p q r sp : R) : transp (Fg p q r sp) = Fg p r q sp := by
  funext i j; cases i <;> cases j <;> rfl

/-- **THE F-MOVE UNDER STRING REVERSAL.**  Reversing `(a,b,c) ↦ (c,b,a)` and
    swapping `(x,y) ↦ (y,x)` on a transposed `F` gives back the original
    F-symbol — because `fuse` is commutative and the special cases are
    symmetric in `a,b,c` and in `x,y`. -/
theorem Fs_rev {R : Type} (K : Rng R) (F : Anyon → Anyon → R) (a b c d x y : Anyon) :
    Fs K (transp F) c b a d y x = Fs K F a b c d x y := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases x <;> cases y <;> rfl

theorem mul3_rev (a b c : Zp) : Zp.mul (Zp.mul c b) a = Zp.mul (Zp.mul a b) c := by
  rw [Zp.mul_comm (Zp.mul c b) a, Zp.mul_comm c b, ← Zp.mul_assoc]

/-- **THE PENTAGON RESIDUAL UNDER STRING REVERSAL.**  Each of the 50 live
    residuals is carried to another live residual by
    `(a,b,c,d,x,y,t,w,v) ↦ (d,c,b,a,w,v,t,x,y)` together with `F ↦ Fᵀ`. -/
theorem pentResid_rev (F : Anyon → Anyon → Zp) (a b c dd x y t w v : Anyon) :
    pentResid zpRng (transp F) dd c b a w v t x y
      = pentResid zpRng F a b c dd x y t w v := by
  have hf : (fun u => Zp.mul (Zp.mul (Fs zpRng (transp F) dd c b v w u)
                                     (Fs zpRng (transp F) dd u a t v y))
                             (Fs zpRng (transp F) c b a y u x))
          = (fun u => Zp.mul (Zp.mul (Fs zpRng F a b c y x u)
                                     (Fs zpRng F a u dd t y v))
                             (Fs zpRng F b c dd v u w)) := by
    funext u
    rw [Fs_rev zpRng F b c dd v u w, Fs_rev zpRng F a u dd t y v,
        Fs_rev zpRng F a b c y x u]
    exact mul3_rev _ _ _
  show Zp.add (sumOver zpRng (fun u => Zp.mul (Zp.mul (Fs zpRng (transp F) dd c b v w u)
                                                     (Fs zpRng (transp F) dd u a t v y))
                                             (Fs zpRng (transp F) c b a y u x)) (fuse c b))
              (Zp.neg (Zp.mul (Fs zpRng (transp F) w b a t v x)
                              (Fs zpRng (transp F) dd c x t w y)))
     = Zp.add (sumOver zpRng (fun u => Zp.mul (Zp.mul (Fs zpRng F a b c y x u)
                                                     (Fs zpRng F a u dd t y v))
                                             (Fs zpRng F b c dd v u w)) (fuse b c))
              (Zp.neg (Zp.mul (Fs zpRng F x c dd t y w) (Fs zpRng F a b w t x v)))
  rw [fuse_comm c b, hf, Fs_rev zpRng F a b w t x v, Fs_rev zpRng F x c dd t y w,
      Zp.mul_comm (Fs zpRng F a b w t x v) (Fs zpRng F x c dd t y w)]

/-- **THE FREEBIE, AS A THEOREM.**  If columns `q` and `r` of a symmetric
    matrix agree, the swap direction `(0,1,−1,0)` is null.  No solutionhood is
    involved; this is why a `q = r` point cannot be used as evidence of
    rigidity. -/
theorem swapDir_null_of_cols_eq (A : M4) (h : ∀ a, A a 1 = A a 2) (a : Fin 4) :
    mvec A swapDir a = Zp.zero := by
  show Zp.add (Zp.add (Zp.mul (A a 0) Zp.zero) (Zp.mul (A a 1) Zp.one))
              (Zp.add (Zp.mul (A a 2) (Zp.neg Zp.one)) (Zp.mul (A a 3) Zp.zero))
     = Zp.zero
  rw [h a]
  simp only [Zp.mul_zero, Zp.mul_one, Zp.mul_neg, Zp.zero_add, Zp.add_zero]
  exact Zp.add_neg _

/-- Yang–Lee is NOT a `q = r` point, and its columns genuinely differ — which
    is exactly why §5's null-space theorem is not the freebie. -/
theorem YL_cols_differ : qY ≠ rY ∧ HY 1 1 ≠ HY 1 2 := by
  refine ⟨by decide, by decide⟩

/-! ══════════════════════════════════════════════════════════════════════
    ## §7.  NEGATIVE CONTROLS
    ══════════════════════════════════════════════════════════════════════ -/

/-! ### §7a.  THE STRICT ASSOCIATOR `(1,1,1,1)` — the specimen that refuted
    the first draft of the charge.

    It is a NON-solution: `SS = 17 ≠ 0`, gradient `≠ 0`, eight of the eleven
    live residuals alive.  And YET its Hessian is positive semidefinite with
    null space exactly `span(0,1,−1,0)` — every certificate the charge
    expected to fail here PASSES.  Reason: `q = r`, so §6's freebie applies.
    MORAL, and it is the point of this section: the signature `{0,+,+,+}` does
    NOT detect solutionhood.  The "point is a pentagon solution" hypothesis in
    §5 is load-bearing and must stay in the statement. -/

def pS : Zp := Zp.one

def GS : J2 Zp :=
  ⟨⟨17,0⟩, ⟨24,0⟩, ⟨20,0⟩, ⟨20,0⟩, ⟨26,0⟩,
   ⟨21,0⟩, ⟨14,0⟩, ⟨14,0⟩, ⟨16,0⟩,
   ⟨12,0⟩, ⟨24,0⟩, ⟨28,0⟩,
   ⟨12,0⟩, ⟨28,0⟩,
   ⟨26,0⟩⟩

theorem germ_S : germ zpRng pS pS pS pS = GS := by rfl

def HS : M4 := hessOf zpRng GS

theorem hess_S : hess zpRng pS pS pS pS = HS := by
  show hessOf zpRng (germ zpRng pS pS pS pS) = hessOf zpRng GS
  rw [germ_S]

/-- **NOT A SOLUTION.**  `SS = 17`, and the gradient is `(24,20,20,26) ≠ 0`. -/
theorem strict_not_critical :
    (germ zpRng pS pS pS pS).v = ⟨17,0⟩ ∧
    gradOf (germ zpRng pS pS pS pS) 0 = ⟨24,0⟩ ∧
    gradOf (germ zpRng pS pS pS pS) 0 ≠ Zp.zero := by
  rw [germ_S]; refine ⟨by decide, by decide, by decide⟩

/-- ...and the pentagon genuinely fails there. -/
theorem strict_fails_pentagon :
    pentOK (Fg pS pS pS pS) .tau .tau .tau .tau .one .tau .one .one .tau = false := by
  decide

/-- The columns coincide because `q = r`: §6's freebie, decided. -/
theorem HS_cols_eq : ∀ a, HS a 1 = HS a 2 := by decide

/-- **THE REFUTATION, PART ONE.**  The swap direction is null at the strict
    associator — for free, by `swapDir_null_of_cols_eq`, not by rigidity. -/
theorem HS_swap_null (a : Fin 4) : mvec HS swapDir a = Zp.zero :=
  swapDir_null_of_cols_eq HS HS_cols_eq a

/-- **THE REFUTATION, PART TWO.**  The strict associator also passes the rank
    and positivity battery: `det H = 0`, a positive `3×3` minor, and a
    sum-of-squares certificate with positive coefficients.  So the battery is
    not a solution-detector. -/
def NS  : Zp := ⟨22482448128, 0⟩
def eS1 : Zp := ⟨535296384, 0⟩
def eS2 : Zp := ⟨659232, 0⟩
def LS1 : V4 := mkV ⟨42,0⟩ ⟨14,0⟩ ⟨14,0⟩ ⟨16,0⟩
def LS2 : V4 := mkV Zp.zero ⟨812,0⟩ ⟨812,0⟩ ⟨952,0⟩
def LS3 : V4 := mkV Zp.zero Zp.zero Zp.zero ⟨659232,0⟩

theorem sos_S : ∀ a b, Zp.mul NS (HS a b) =
    Zp.add (Zp.add (Zp.mul eS1 (Zp.mul (LS1 a) (LS1 b)))
                   (Zp.mul eS2 (Zp.mul (LS2 a) (LS2 b))))
           (Zp.mul Zp.one (Zp.mul (LS3 a) (LS3 b))) := by decide

theorem strict_also_psd (w : V4) : Zp.Nn (qform HS w) :=
  psd_of_sos NS eS1 eS2 Zp.one HS LS1 LS2 LS3 sos_S
    (by decide) (by decide) (by decide) (by decide) w

theorem strict_also_rank3 :
    det4 HS = Zp.zero ∧ Zp.pos (det3 HS 0 1 3 0 1 3) = true := by
  refine ⟨by decide, by decide⟩

/-! ### §7b.  THE WORKING NEGATIVE CONTROL `(1,2,3,−1)`

    An all-integer point with `q ≠ r`, off the variety.  Here the symmetry
    crutch is gone and the whole construction fails, exactly as it should:
    the gauge tangent is NOT null, the rank is 4, and the form takes strictly
    negative values.  This is the control the builder's certificate isolates
    as the one that actually discriminates (`V3e.negctrl_working`). -/

def pC : Zp := ⟨1,0⟩
def qC : Zp := ⟨2,0⟩
def rC : Zp := ⟨3,0⟩
def sC : Zp := ⟨-1,0⟩

def GC : J2 Zp :=
  ⟨⟨201,0⟩, Zp.zero, ⟨220,0⟩, ⟨150,0⟩, ⟨-96,0⟩,
   ⟨39,0⟩, ⟨-10,0⟩, Zp.zero, ⟨-2,0⟩,
   ⟨64,0⟩, ⟨156,0⟩, ⟨-64,0⟩,
   ⟨29,0⟩, ⟨-56,0⟩,
   ⟨136,0⟩⟩

theorem germ_C : germ zpRng pC qC rC sC = GC := by rfl

def HC : M4 := hessOf zpRng GC

theorem hess_C : hess zpRng pC qC rC sC = HC := by
  show hessOf zpRng (germ zpRng pC qC rC sC) = hessOf zpRng GC
  rw [germ_C]

def tangentC : V4 := mkV Zp.zero qC (Zp.neg rC) Zp.zero
def wNegC : V4 := mkV ⟨-3,0⟩ ⟨-3,0⟩ ⟨3,0⟩ ⟨-1,0⟩

/-- **`H·(0,q,−r,0) ≠ 0`** at the control point: the four components are
    `(−20, −212, 138, 40)`, matching the builder's certificate exactly. -/
theorem HC_tangent_not_null :
    mvec HC tangentC 0 = ⟨-20,0⟩ ∧ mvec HC tangentC 1 = ⟨-212,0⟩ ∧
    mvec HC tangentC 2 = ⟨138,0⟩ ∧ mvec HC tangentC 3 = ⟨40,0⟩ ∧
    mvec HC tangentC 0 ≠ Zp.zero := by
  refine ⟨by decide, by decide, by decide, by decide, by decide⟩

/-- **NOT POSITIVE SEMIDEFINITE**: `wᵀHw = −400 < 0` at `w = (−3,−3,3,−1)`. -/
theorem HC_not_psd :
    qform HC wNegC = ⟨-400,0⟩ ∧ Zp.pos (Zp.neg (qform HC wNegC)) = true ∧
    ¬ Zp.Nn (qform HC wNegC) := by
  refine ⟨by decide, by decide, Zp.not_nn _ (by decide)⟩

/-- ...and the rank is 4, so no SOS certificate of the §4 shape can exist. -/
theorem HC_rank4 : det4 HC = ⟨-322420288,0⟩ ∧ det4 HC ≠ Zp.zero := by
  refine ⟨by decide, by decide⟩

/-! ══════════════════════════════════════════════════════════════════════
    ## §8.  THE ORDERED-FIELD EXTENSION  `E = Z[φ][s]/(s² − φ)`

    One more square root on top of round 5.  An element is `x + y·s` with
    `x, y ∈ Z[φ]` and `s = √φ > 0`.  The sign of `x + y·s` is decided by two
    `Zp.pos` calls and, in the mixed case, by the sign of the NORM
    `nrm(x + y·s) = x² − φy²` — which is legitimate exactly because
    `no_sqrtPhi` below proves the norm never vanishes on a nonzero element.

    ADJUDICATOR (house norm 15).  A claim `Ep.pos u = true` is settled by
    `Ep.pos_iff` (it means `PosE u`, the same two-disjunct shape as
    `Ord5.PosP` with `5 ↦ φ`) together with `Ep.trichotomy` (exactly one of
    `u > 0`, `u = 0`, `−u > 0`), and the semantics is pinned to the real
    number `√φ = 1.272…` by `Ep.rad_bracket` (with `Ep.rad_bracket_tight` as
    its negative control).  The Galois conjugation `Zp.conj` (`√5 ↦ −√5`,
    i.e. `φ ↦ 1 − φ`) is what makes `no_sqrtPhi` go through, and
    `Zp.conj_mul` is its receipt.

    WHAT THIS ADJUDICATOR DOES NOT COVER, stated plainly: `Ep.pos` is NOT
    proved here to be closed under addition or multiplication.  Those closure
    proofs are the analogues of `Ord5.posP_add_*` / `Ord5.posP_mul_*` one
    level up, and they need an order toolkit over `Z[φ]` (`a < b`, products
    of inequalities, `a² < b² → a < b`) that this file does not build.  NOT
    ATTEMPTED, deliberately: no theorem in this file uses them.  See §9's
    header for exactly what the golden world does and does not claim as a
    consequence.
    ══════════════════════════════════════════════════════════════════════ -/

namespace Zp

/-- The Galois conjugation of `Q(√5)`: `√5 ↦ −√5`, i.e. `φ ↦ 1 − φ`.
    In the basis `m + nφ`: `⟨m,n⟩ ↦ ⟨m+n, −n⟩`. -/
def conj (u : Zp) : Zp := ⟨u.m + u.n, -u.n⟩

theorem conj_phi : conj phi = ⟨1,-1⟩ := rfl
theorem conj_zero : conj zero = zero := rfl

theorem conj_conj (u : Zp) : conj (conj u) = u := by
  cases u
  simp only [conj, Zp.mk.injEq]
  refine ⟨?_, ?_⟩ <;> omega

/-- `conj` is a ring map — the receipt for using it in `Ep.no_sqrtPhi`. -/
theorem conj_mul (u v : Zp) : conj (mul u v) = mul (conj u) (conj v) := by
  cases u; cases v
  simp only [conj, mul, Zp.mk.injEq, Int.add_mul, Int.mul_add, Int.neg_mul,
             Int.mul_neg]
  refine ⟨?_, ?_⟩ <;> omega

theorem conj_eq_zero (u : Zp) (h : conj u = zero) : u = zero := by
  cases u
  simp only [conj, zero, Zp.mk.injEq] at h
  have e1 := h.1
  have e2 := h.2
  simp only [zero, Zp.mk.injEq]
  refine ⟨?_, ?_⟩ <;> omega

theorem zero_sub (a : Zp) : sub zero a = neg a := by
  cases a; simp only [sub, zero, neg, Zp.mk.injEq]; refine ⟨?_, ?_⟩ <;> omega

theorem sub_zero (a : Zp) : sub a zero = a := by
  cases a; simp only [sub, zero, Zp.mk.injEq]; refine ⟨?_, ?_⟩ <;> omega

/-- A nonzero square is strictly positive. -/
theorem pos_sq (a : Zp) (h : a ≠ zero) : pos (mul a a) = true := by
  rcases nn_sq a with hn | hn
  · exact absurd (eq_zero_of_sq a hn) h
  · exact hn

/-- `a` and `−a` are never both positive. -/
theorem not_both_pos (a : Zp) (h1 : pos a = true) (h2 : pos (neg a) = true) :
    False := by
  rcases trichotomy a with ⟨_, _, k3⟩ | ⟨k1, _, _⟩ | ⟨k1, _, _⟩
  · rw [h2] at k3; exact Bool.noConfusion k3
  · rw [h1] at k1; exact Bool.noConfusion k1
  · rw [h1] at k1; exact Bool.noConfusion k1

/-- A nonzero element is positive or its negation is. -/
theorem pos_or_pos_neg (a : Zp) (h : a ≠ zero) :
    pos a = true ∨ pos (neg a) = true := by
  rcases trichotomy a with ⟨k1, _, _⟩ | ⟨_, k2, _⟩ | ⟨_, _, k3⟩
  · exact Or.inl k1
  · exact absurd k2 h
  · exact Or.inr k3

/-- `1 − φ < 0` — the fact that powers `Ep.no_sqrtPhi`. -/
theorem conj_phi_neg : pos (neg (conj phi)) = true := by decide

end Zp

/-- `⟨x, y⟩` denotes `x + y·s`, `s = √φ`. -/
structure Ep where
  x : Zp
  y : Zp
  deriving DecidableEq

namespace Ep

def zero : Ep := ⟨Zp.zero, Zp.zero⟩
def one  : Ep := ⟨Zp.one, Zp.zero⟩
/-- `s = √φ`. -/
def rad  : Ep := ⟨Zp.zero, Zp.one⟩
def ofZ (a : Zp) : Ep := ⟨a, Zp.zero⟩
def add (u v : Ep) : Ep := ⟨Zp.add u.x v.x, Zp.add u.y v.y⟩
def neg (u : Ep) : Ep := ⟨Zp.neg u.x, Zp.neg u.y⟩
def sub (u v : Ep) : Ep := ⟨Zp.sub u.x v.x, Zp.sub u.y v.y⟩
def mul (u v : Ep) : Ep :=
  ⟨Zp.add (Zp.mul u.x v.x) (Zp.mul Zp.phi (Zp.mul u.y v.y)),
   Zp.add (Zp.mul u.x v.y) (Zp.mul u.y v.x)⟩

/-- The norm to `Z[φ]`: `nrm (x + y·s) = x² − φy² = (x + y·s)(x − y·s)`. -/
def nrm (u : Ep) : Zp :=
  Zp.sub (Zp.mul u.x u.x) (Zp.mul Zp.phi (Zp.mul u.y u.y))

theorem rad_sq : mul rad rad = ofZ Zp.phi := rfl

theorem nrm_neg (u : Ep) : nrm (neg u) = nrm u := by
  cases u
  simp only [nrm, neg, Zp.neg_mul, Zp.mul_neg, Zp.neg_neg]

theorem neg_eq_zero (u : Ep) (h : neg u = zero) : u = zero := by
  cases u with
  | mk x y =>
    cases x; cases y
    simp only [neg, zero, Zp.neg, Zp.zero, Ep.mk.injEq, Zp.mk.injEq] at h
    simp only [zero, Ep.mk.injEq, Zp.zero, Zp.mk.injEq]
    have a1 := h.1.1
    have a2 := h.1.2
    have a3 := h.2.1
    have a4 := h.2.2
    exact ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩

end Ep

/-- `E` as a ring record. -/
def epRng : Rng Ep := ⟨Ep.zero, Ep.one, Ep.add, Ep.neg, Ep.mul⟩

namespace Ep

/-- **`√φ ∉ Q(√5)`.**  If `x² = φ·y²` in `Z[φ]` then `x = y = 0`.  Proof: the
    Galois conjugate of `φ` is `1 − φ < 0`, so conjugating turns a square into
    a negative multiple of a square, which forces both to vanish.  This is the
    exact analogue of round 5's `Ord5.no_sqrt5`, one level up — and it is what
    licenses the mixed branch of `Ep.pos`. -/
theorem no_sqrtPhi (x y : Zp) (h : Zp.mul x x = Zp.mul Zp.phi (Zp.mul y y)) :
    x = Zp.zero ∧ y = Zp.zero := by
  have hc : Zp.mul (Zp.conj x) (Zp.conj x)
          = Zp.mul (Zp.conj Zp.phi) (Zp.mul (Zp.conj y) (Zp.conj y)) := by
    rw [← Zp.conj_mul, ← Zp.conj_mul, ← Zp.conj_mul, h]
  have hy : Zp.conj y = Zp.zero := by
    by_cases hne : Zp.conj y = Zp.zero
    · exact hne
    exfalso
    have hsq : Zp.pos (Zp.mul (Zp.conj y) (Zp.conj y)) = true := Zp.pos_sq _ hne
    have hprod := Zp.pos_mul (Zp.neg (Zp.conj Zp.phi))
      (Zp.mul (Zp.conj y) (Zp.conj y)) Zp.conj_phi_neg hsq
    rw [Zp.neg_mul, ← hc] at hprod
    exact Zp.not_nn _ hprod (Zp.nn_sq (Zp.conj x))
  have hy0 : y = Zp.zero := Zp.conj_eq_zero y hy
  refine ⟨?_, hy0⟩
  refine Zp.eq_zero_of_sq x ?_
  rw [h, hy0, Zp.zero_mul, Zp.mul_zero]

/-- The norm vanishes only on `0`. -/
theorem nrm_eq_zero (u : Ep) (h : nrm u = Zp.zero) : u = zero := by
  have he : Zp.mul u.x u.x = Zp.mul Zp.phi (Zp.mul u.y u.y) :=
    Zp.sub_eq_zero _ _ h
  obtain ⟨h1, h2⟩ := no_sqrtPhi u.x u.y he
  cases u
  simp only [zero, Ep.mk.injEq]
  exact ⟨h1, h2⟩

theorem nrm_ne_zero (u : Ep) (h : u ≠ zero) : nrm u ≠ Zp.zero := by
  intro hz; exact h (nrm_eq_zero u hz)

theorem x_zero_nrm (u : Ep) (hx : u.x = Zp.zero) :
    nrm u = Zp.neg (Zp.mul Zp.phi (Zp.mul u.y u.y)) := by
  show Zp.sub (Zp.mul u.x u.x) (Zp.mul Zp.phi (Zp.mul u.y u.y)) = _
  rw [hx, Zp.zero_mul, Zp.zero_sub]

theorem y_zero_nrm (u : Ep) (hy : u.y = Zp.zero) : nrm u = Zp.mul u.x u.x := by
  show Zp.sub (Zp.mul u.x u.x) (Zp.mul Zp.phi (Zp.mul u.y u.y)) = _
  rw [hy, Zp.zero_mul, Zp.mul_zero, Zp.sub_zero]

/-- If the norm is positive then the `Z[φ]` part is nonzero. -/
theorem x_ne_zero_of_nrm_pos (u : Ep) (h : Zp.pos (nrm u) = true) :
    u.x ≠ Zp.zero := by
  intro hx
  rw [x_zero_nrm u hx] at h
  exact Zp.not_nn _ h
    (Zp.nn_mul _ _ (Or.inr (by decide)) (Zp.nn_sq u.y))

/-- If the norm is negative then the `√φ` part is nonzero. -/
theorem y_ne_zero_of_nrm_neg (u : Ep) (h : Zp.pos (Zp.neg (nrm u)) = true) :
    u.y ≠ Zp.zero := by
  intro hy
  rw [y_zero_nrm u hy] at h
  exact Zp.not_nn _ h (Zp.nn_sq u.x)

/-! ### the decision procedure, and what it means -/

/-- **`Ep.pos u` decides `u > 0` in `Z[φ][√φ]`.**  Four `Zp.pos` calls at
    worst: the signs of `x` and `y`, and in the mixed case the sign of the
    norm `x² − φy²`. -/
def pos (u : Ep) : Bool :=
  if Zp.pos u.x then
    (if Zp.pos (Zp.neg u.y) then Zp.pos (nrm u) else true)
  else if Zp.pos (Zp.neg u.x) then
    (if Zp.pos u.y then Zp.pos (Zp.neg (nrm u)) else false)
  else Zp.pos u.y

/-- The semantic predicate, in the same two-disjunct shape as `Ord5.PosP`
    with `5 ↦ φ`: totally positive, or mixed. -/
def PosE (u : Ep) : Prop :=
  (Zp.pos u.x = true ∧ Zp.pos (nrm u) = true) ∨
  (Zp.pos u.y = true ∧ Zp.pos (Zp.neg (nrm u)) = true)

theorem nrm_sign_cases (u : Ep) (h : u ≠ zero) :
    Zp.pos (nrm u) = true ∨ Zp.pos (Zp.neg (nrm u)) = true :=
  Zp.pos_or_pos_neg (nrm u) (nrm_ne_zero u h)

/-- **THE DECISION PROCEDURE IS CORRECT.** -/
theorem pos_iff (u : Ep) : pos u = true ↔ PosE u := by
  unfold pos
  by_cases hx : Zp.pos u.x = true
  · rw [if_pos hx]
    by_cases hy : Zp.pos (Zp.neg u.y) = true
    · rw [if_pos hy]
      constructor
      · intro h; exact Or.inl ⟨hx, h⟩
      · intro h
        rcases h with ⟨_, h2⟩ | ⟨h1, _⟩
        · exact h2
        · exact absurd (Zp.not_both_pos u.y h1 hy) (fun k => k)
    · rw [if_neg hy]
      constructor
      · intro _
        by_cases hz : u = zero
        · exfalso
          rw [hz] at hx
          exact absurd hx (by decide)
        · rcases nrm_sign_cases u hz with k | k
          · exact Or.inl ⟨hx, k⟩
          · refine Or.inr ⟨?_, k⟩
            have hyne : u.y ≠ Zp.zero := y_ne_zero_of_nrm_neg u k
            rcases Zp.pos_or_pos_neg u.y hyne with m | m
            · exact m
            · exact absurd m hy
      · intro _; rfl
  · rw [if_neg hx]
    by_cases hxn : Zp.pos (Zp.neg u.x) = true
    · rw [if_pos hxn]
      by_cases hy : Zp.pos u.y = true
      · rw [if_pos hy]
        constructor
        · intro h; exact Or.inr ⟨hy, h⟩
        · intro h
          rcases h with ⟨h1, _⟩ | ⟨_, h2⟩
          · exact absurd h1 hx
          · exact h2
      · rw [if_neg hy]
        constructor
        · intro h; exact Bool.noConfusion h
        · intro h
          exfalso
          rcases h with ⟨h1, _⟩ | ⟨h1, _⟩
          · exact hx h1
          · exact hy h1
    · rw [if_neg hxn]
      have hx0 : u.x = Zp.zero := by
        by_cases hne : u.x = Zp.zero
        · exact hne
        · exact absurd (Zp.pos_or_pos_neg u.x hne)
            (fun k => Or.elim k (fun m => hx m) (fun m => hxn m))
      constructor
      · intro h
        refine Or.inr ⟨h, ?_⟩
        have hyne : u.y ≠ Zp.zero := by
          intro hz; rw [hz] at h; exact absurd h (by decide)
        rw [x_zero_nrm u hx0, Zp.neg_neg]
        exact Zp.pos_mul _ _ (by decide) (Zp.pos_sq u.y hyne)
      · intro h
        rcases h with ⟨h1, _⟩ | ⟨h1, _⟩
        · rw [hx0] at h1; exact absurd h1 (by decide)
        · exact h1

theorem pos_zero_false : pos zero = false := by decide

theorem pos_ne_zero (u : Ep) (h : pos u = true) : u ≠ zero := by
  intro hz; rw [hz] at h; exact absurd h (by decide)

/-- `u` and `−u` are never both positive. -/
theorem not_both_pos (u : Ep) (h1 : pos u = true) (h2 : pos (neg u) = true) :
    False := by
  have p1 := (pos_iff u).mp h1
  have p2 := (pos_iff (neg u)).mp h2
  have hnx : (neg u).x = Zp.neg u.x := rfl
  have hny : (neg u).y = Zp.neg u.y := rfl
  have hnn : nrm (neg u) = nrm u := nrm_neg u
  rcases p1 with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> rcases p2 with ⟨b1, b2⟩ | ⟨b1, b2⟩
  · rw [hnx] at b1; exact Zp.not_both_pos u.x a1 b1
  · rw [hnn] at b2; exact Zp.not_both_pos (nrm u) a2 b2
  · rw [hnn] at b2; exact Zp.not_both_pos (nrm u) b2 a2
  · rw [hny] at b1; exact Zp.not_both_pos u.y a1 b1

/-- A nonzero element is positive or its negation is. -/
theorem pos_or_pos_neg (u : Ep) (h : u ≠ zero) :
    pos u = true ∨ pos (neg u) = true := by
  have hnx : (neg u).x = Zp.neg u.x := rfl
  have hny : (neg u).y = Zp.neg u.y := rfl
  rcases nrm_sign_cases u h with hk | hk
  · rcases Zp.pos_or_pos_neg u.x (x_ne_zero_of_nrm_pos u hk) with m | m
    · exact Or.inl ((pos_iff u).mpr (Or.inl ⟨m, hk⟩))
    · refine Or.inr ((pos_iff (neg u)).mpr (Or.inl ⟨?_, ?_⟩))
      · rw [hnx]; exact m
      · rw [nrm_neg u]; exact hk
  · rcases Zp.pos_or_pos_neg u.y (y_ne_zero_of_nrm_neg u hk) with m | m
    · exact Or.inl ((pos_iff u).mpr (Or.inr ⟨m, hk⟩))
    · refine Or.inr ((pos_iff (neg u)).mpr (Or.inr ⟨?_, ?_⟩))
      · rw [hny]; exact m
      · rw [nrm_neg u]; exact hk

/-- **TRICHOTOMY.**  For every `u : E` exactly one of `u > 0`, `u = 0`,
    `−u > 0` holds.  The `x² = φy² ⟹ x = y = 0` step is `no_sqrtPhi`, run
    through the Galois conjugation of `Q(√5)`. -/
theorem trichotomy (u : Ep) :
    (pos u = true ∧ u ≠ zero ∧ pos (neg u) = false) ∨
    (pos u = false ∧ u = zero ∧ pos (neg u) = false) ∨
    (pos u = false ∧ u ≠ zero ∧ pos (neg u) = true) := by
  by_cases hz : u = zero
  · refine Or.inr (Or.inl ⟨?_, hz, ?_⟩)
    · rw [hz]; rfl
    · rw [hz]; rfl
  · rcases pos_or_pos_neg u hz with hp | hp
    · refine Or.inl ⟨hp, hz, ?_⟩
      cases hq : pos (neg u) with
      | false => rfl
      | true => exact absurd (not_both_pos u hp hq) (fun k => k)
    · refine Or.inr (Or.inr ⟨?_, hz, hp⟩)
      cases hq : pos u with
      | false => rfl
      | true => exact absurd (not_both_pos u hq hp) (fun k => k)

/-- The certificate's phrasing: the three flags sum to exactly one. -/
def triCount (u : Ep) : Nat :=
  (if pos u = true then 1 else 0) + (if u = zero then 1 else 0)
    + (if pos (neg u) = true then 1 else 0)

theorem tri_count_eq_one (u : Ep) : triCount u = 1 := by
  unfold triCount
  rcases trichotomy u with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · rw [h1, h3, if_neg h2]; rfl
  · rw [h1, h3, if_pos h2]; rfl
  · rw [h1, h3, if_neg h2]; rfl

/-! ### sanity, brackets and negative controls -/

theorem pos_one : pos one = true := by decide
theorem pos_rad : pos rad = true := by decide
theorem pos_neg_one : pos (neg one) = false := by decide

/-- **THE ORDER AGREES WITH `1.272 < √φ < 1.273`.**  This pins the semantics
    of `Ep.pos` to the real square root without ever mentioning a real
    number, and it is a check that can fail. -/
theorem rad_bracket :
    pos (sub (mul (ofZ ⟨1000,0⟩) rad) (ofZ ⟨1272,0⟩)) = true ∧
    pos (sub (ofZ ⟨1273,0⟩) (mul (ofZ ⟨1000,0⟩) rad)) = true := by
  refine ⟨by decide, by decide⟩

/-- NEGATIVE CONTROL for the bracket: it is tight on both sides. -/
theorem rad_bracket_tight :
    pos (sub (mul (ofZ ⟨1000,0⟩) rad) (ofZ ⟨1273,0⟩)) = false ∧
    pos (sub (ofZ ⟨1272,0⟩) (mul (ofZ ⟨1000,0⟩) rad)) = false := by
  refine ⟨by decide, by decide⟩

/-- The wrong radicand: comparing `x²` against `(φ−1)y²` instead of `φy²`. -/
def nrmW (u : Ep) : Zp :=
  Zp.sub (Zp.mul u.x u.x) (Zp.mul Zp.invPhi (Zp.mul u.y u.y))

def posW (u : Ep) : Bool :=
  if Zp.pos u.x then
    (if Zp.pos (Zp.neg u.y) then Zp.pos (nrmW u) else true)
  else if Zp.pos (Zp.neg u.x) then
    (if Zp.pos u.y then Zp.pos (Zp.neg (nrmW u)) else false)
  else Zp.pos u.y

/-- **NEGATIVE CONTROL: the radicand `φ` is load-bearing.**  `4√φ − 5 ≈ 0.088`
    is positive; the procedure with `φ − 1` in place of `φ` calls it negative.
    So `Ep.pos` is not merely "some" total order — it is the one in which
    `s² = φ`. -/
theorem wrong_radicand_miscalls :
    pos ⟨⟨-5,0⟩, ⟨4,0⟩⟩ = true ∧ posW ⟨⟨-5,0⟩, ⟨4,0⟩⟩ = false := by
  refine ⟨by decide, by decide⟩

/-- ANTI-VACUITY: each trichotomy branch is inhabited, and `pos` is neither
    constant-`true` nor constant-`false`. -/
theorem tri_inhabited :
    (pos rad = true ∧ rad ≠ zero) ∧ (zero = zero ∧ pos zero = false) ∧
    (pos (neg rad) = false ∧ pos (neg (neg rad)) = true) := by
  refine ⟨⟨by decide, by decide⟩, ⟨rfl, by decide⟩, ⟨by decide, by decide⟩⟩

/-- The extension is conservative: on `Z[φ] ⊂ E` the new order is the old. -/
theorem pos_ofZ (a : Zp) : pos (ofZ a) = Zp.pos a := by
  show (if Zp.pos a = true then
          (if Zp.pos (Zp.neg Zp.zero) = true then Zp.pos (nrm (ofZ a)) else true)
        else if Zp.pos (Zp.neg a) = true then
          (if Zp.pos Zp.zero = true then Zp.pos (Zp.neg (nrm (ofZ a))) else false)
        else Zp.pos Zp.zero) = Zp.pos a
  by_cases hA : Zp.pos a = true
  · rw [if_pos hA, if_neg (by decide : ¬ (Zp.pos (Zp.neg Zp.zero) = true)), hA]
  · rw [if_neg hA, Bool.not_eq_true] at *
    by_cases hB : Zp.pos (Zp.neg a) = true
    · rw [if_pos hB, if_neg (by decide : ¬ (Zp.pos Zp.zero = true)), hA]
    · rw [if_neg hB, hA]; rfl

end Ep

/-! ══════════════════════════════════════════════════════════════════════
    ## §9.  THE GOLDEN WORLD  `(p,q,r,s) = (1/φ, 1/√φ, 1/√φ, −1/φ)`

    Here `q = r`, and that changes what is worth saying.  Read §6 first.

    WHAT IS CLAIMED HERE, and it is the pair the charge identifies as the
    content at this world:
      * the exact Hessian entries in `E = Z[φ][√φ]` — four of the ten
        genuinely need `√φ`, which is why §8 exists.  These are COMPUTED, not
        transcribed: `germ_G` decides the whole `E`-valued second-order germ
        (fifteen field projections, each its own `rfl`, glued by `J2.ext'`),
        and `hess_G` reads `HG` off it exactly as `hess_Y` reads `HY` off
        `germ_Y`.  Default heartbeat budget throughout — see the note on
        `germ_G` for which forms do NOT fit and why it does not matter;
      * RANK EXACTLY 3: `det H = 0` together with a strictly positive `3×3`
        principal minor, positivity decided by `Ep.pos`;
      * a sum-of-squares certificate `N·H = Σ eᵢ·Lᵢ⊗Lᵢ` whose four scalars
        are strictly positive by `Ep.pos` — the positivity half of the
        signature, as an exact matrix identity.

    WHAT IS **NOT** CLAIMED HERE, and must not be quoted as if it were:
      * The null direction at this world is a SYMMETRY FREEBIE.  `q = r`, so
        §6's `swapDir_null_of_cols_eq` applies and `(0,1,−1,0)` is null for
        free; `HG_cols_eq` records this.  Nothing about rigidity follows from
        it.  The null-space-is-the-gauge-tangent claim carries its weight at
        YANG–LEE (§5), where `q ≠ r`, and only there.
      * There is NO `∀ w : E⁴` positive-semidefiniteness theorem in this
        section.  §5's `psd_of_sos` runs on `Zp.nn_add` / `Zp.nn_mul`, i.e.
        on the closure of `Zp.pos` under `+` and `×` (round 5).  The
        corresponding closure lemmas for `Ep.pos` are NOT ATTEMPTED (see §8's
        header), so the golden PSD statement is delivered here only as the
        certificate — the matrix identity plus the positivity of its four
        scalars — and NOT as a quantified theorem.  Adjudicator for the
        quantified reading: `r6_gift_hessian.py`, checks `V3d.sylvester_golden`,
        `V3d.ldl_golden`, `V3d.psd_kernel_statement_golden`.
    ══════════════════════════════════════════════════════════════════════ -/

/-! ### linear algebra over `E`

    The same formulas as §4, over `Ep` instead of `Zp`.  §4's lemmas need
    `Z[φ]`'s ring laws, which is why the definitions are repeated rather than
    shared; no FACT is stated twice — everything proved about these is a
    `decide` about explicit elements, and every general lemma about quadratic
    forms lives once, in §4. -/

abbrev V4E := Fin 4 → Ep
abbrev M4E := Fin 4 → Fin 4 → Ep

def mkVE (a b c d : Ep) : V4E := fun i =>
  match i.val with
  | 0 => a
  | 1 => b
  | 2 => c
  | _ => d

def dotE (u w : V4E) : Ep :=
  Ep.add (Ep.add (Ep.mul (u 0) (w 0)) (Ep.mul (u 1) (w 1)))
         (Ep.add (Ep.mul (u 2) (w 2)) (Ep.mul (u 3) (w 3)))

def mvecE (A : M4E) (w : V4E) : V4E := fun a => dotE (fun b => A a b) w

def det2E (a b c d : Ep) : Ep := Ep.sub (Ep.mul a d) (Ep.mul b c)

def det3E (A : M4E) (r0 r1 r2 c0 c1 c2 : Fin 4) : Ep :=
  Ep.add (Ep.sub (Ep.mul (A r0 c0) (det2E (A r1 c1) (A r1 c2) (A r2 c1) (A r2 c2)))
                 (Ep.mul (A r0 c1) (det2E (A r1 c0) (A r1 c2) (A r2 c0) (A r2 c2))))
         (Ep.mul (A r0 c2) (det2E (A r1 c0) (A r1 c1) (A r2 c0) (A r2 c1)))

def det4E (A : M4E) : Ep :=
  Ep.add (Ep.sub (Ep.mul (A 0 0) (det3E A 1 2 3 1 2 3))
                 (Ep.mul (A 0 1) (det3E A 1 2 3 0 2 3)))
         (Ep.sub (Ep.mul (A 0 2) (det3E A 1 2 3 0 1 3))
                 (Ep.mul (A 0 3) (det3E A 1 2 3 0 1 2)))

/-! ### the point -/

/-- `p = 1/φ = φ − 1`. -/
def pG : Ep := ⟨⟨-1,1⟩, Zp.zero⟩
/-- `q = r = 1/√φ = (φ−1)·√φ`. -/
def qG : Ep := ⟨Zp.zero, ⟨-1,1⟩⟩
/-- `s = −1/φ`. -/
def sG : Ep := ⟨⟨1,-1⟩, Zp.zero⟩

/-- `q = 1/s` exactly: `q·√φ = 1`, and `q² = 1/φ = p`. -/
theorem qG_inv_rad : Ep.mul qG Ep.rad = Ep.one ∧ Ep.mul qG qG = pG := by
  refine ⟨by decide, by decide⟩

/-- The golden point sits on the variety `pentagon_iff` describes:
    `q·r = p` and `s = −p`. -/
theorem G_on_variety : Ep.mul qG qG = pG ∧ sG = Ep.neg pG := by
  refine ⟨by decide, by decide⟩

/-- The second-order germ of `SS` at the golden point, computed by the
    kernel over `E`. -/
def GG : J2 Ep :=
  ⟨Ep.zero, Ep.zero, Ep.zero, Ep.zero, Ep.zero,
   ⟨⟨15,-4⟩, Zp.zero⟩, ⟨Zp.zero, ⟨26,-18⟩⟩, ⟨Zp.zero, ⟨26,-18⟩⟩, ⟨⟨-12,8⟩, Zp.zero⟩,
   ⟨⟨-9,8⟩, Zp.zero⟩, ⟨⟨-18,16⟩, Zp.zero⟩, ⟨Zp.zero, ⟨-12,8⟩⟩,
   ⟨⟨-9,8⟩, Zp.zero⟩, ⟨Zp.zero, ⟨-12,8⟩⟩,
   ⟨⟨1,6⟩, Zp.zero⟩⟩

/-- `SS` vanishes at the golden point.  Stated field by field: a single
    `rfl` on the whole germ over `E` exceeds the default heartbeat budget,
    and this file raises no budget, so each projection is discharged on its
    own — the kernel then only reduces the fields that projection needs.
    `germ_G`, below, puts the fifteen projections back together. -/
theorem SS_G_zero : (germ epRng pG qG qG sG).v = Ep.zero := by rfl

/-- ...and it is a critical point: all four first-order slots vanish. -/
theorem grad_G_0 : (germ epRng pG qG qG sG).d0 = Ep.zero := by rfl
theorem grad_G_1 : (germ epRng pG qG qG sG).d1 = Ep.zero := by rfl
theorem grad_G_2 : (germ epRng pG qG qG sG).d2 = Ep.zero := by rfl
theorem grad_G_3 : (germ epRng pG qG qG sG).d3 = Ep.zero := by rfl

/-! ### the ten second-order slots, one `rfl` each

    Same projection style as `SS_G_zero` and `grad_G_0 … grad_G_3` above, and
    for the same reason.  Each of these is the kernel's own computation of
    one second-order coefficient of `SS` over `E = Z[φ][√φ]`, at the DEFAULT
    heartbeat budget.  Nothing here is asserted. -/

theorem gg_e00 : (germ epRng pG qG qG sG).e00 = ⟨⟨15,-4⟩, Zp.zero⟩ := by rfl
theorem gg_e01 : (germ epRng pG qG qG sG).e01 = ⟨Zp.zero, ⟨26,-18⟩⟩ := by rfl
theorem gg_e02 : (germ epRng pG qG qG sG).e02 = ⟨Zp.zero, ⟨26,-18⟩⟩ := by rfl
theorem gg_e03 : (germ epRng pG qG qG sG).e03 = ⟨⟨-12,8⟩, Zp.zero⟩ := by rfl
theorem gg_e11 : (germ epRng pG qG qG sG).e11 = ⟨⟨-9,8⟩, Zp.zero⟩ := by rfl
theorem gg_e12 : (germ epRng pG qG qG sG).e12 = ⟨⟨-18,16⟩, Zp.zero⟩ := by rfl
theorem gg_e13 : (germ epRng pG qG qG sG).e13 = ⟨Zp.zero, ⟨-12,8⟩⟩ := by rfl
theorem gg_e22 : (germ epRng pG qG qG sG).e22 = ⟨⟨-9,8⟩, Zp.zero⟩ := by rfl
theorem gg_e23 : (germ epRng pG qG qG sG).e23 = ⟨Zp.zero, ⟨-12,8⟩⟩ := by rfl
theorem gg_e33 : (germ epRng pG qG qG sG).e33 = ⟨⟨1,6⟩, Zp.zero⟩ := by rfl

/-- **THE GOLDEN GERM, DECIDED** — the golden-world analogue of `germ_Y`.

    A NOTE ON THE BUDGET, because an earlier revision of this file claimed
    the second-order germ was out of reach and transcribed `GG` instead.
    That claim was too strong.  What genuinely does NOT close at the default
    heartbeat budget over `E` is exactly two forms:

      * the whole structure in one go, `germ epRng pG qG qG sG = GG := by
        rfl`; and
      * the indexed entry form, `hess epRng pG qG qG sG i j = HG i j := by
        rfl`,

    both because they force the kernel to reduce every slot inside a single
    `rfl`, with `E`-valued jet arithmetic roughly four times the `Z[φ]` cost.
    Both were re-checked against Lean 4.32.0 at the default 200000
    heartbeats; both do fail, and neither is needed.  A FIELD PROJECTION is a
    different problem: it forces only the sub-fields that one slot depends
    on, and every one of the fifteen closes by `rfl` well inside the default
    budget.  `J2.ext'` (§3) is then pure structure eta — no arithmetic — so
    this theorem costs nothing beyond the fifteen projections it cites.  No
    budget is raised. -/
theorem germ_G : germ epRng pG qG qG sG = GG :=
  J2.ext' SS_G_zero grad_G_0 grad_G_1 grad_G_2 grad_G_3
    gg_e00 gg_e01 gg_e02 gg_e03 gg_e11 gg_e12 gg_e13 gg_e22 gg_e23 gg_e33

/-- **THE HESSIAN AT THE GOLDEN POINT**, exact in `E = Z[φ][√φ]`, and — this
    is the point — COMPUTED here, not transcribed.  Read this, because an
    earlier revision of this file said the opposite.

    `GG` is the germ's value, and every one of its fifteen slots is
    kernel-checked against `germ epRng pG qG qG sG`: `SS_G_zero` for `.v`,
    `grad_G_0 … grad_G_3` for the first-order slots, `gg_e00 … gg_e33` for
    the ten second-order slots, each a `rfl` at the DEFAULT heartbeat budget.
    `germ_G` glues them by structure eta (`J2.ext'`), and `hess_G` below
    reads `HG` off the germ — the same two lines as `hess_Y`, `hess_S`,
    `hess_C`.  So `HG` is the kernel's own second derivative of `SS` at the
    golden point, on exactly the same footing as `HY`, and there is nothing
    analytic left to trust.  No budget is raised anywhere.

    THE BUDGET CLAIM, CORRECTED.  What was true, and is still true, is that
    two SPECIFIC FORMS overrun the default budget over `E`: the
    whole-structure `germ epRng pG qG qG sG = GG := by rfl`, and the indexed
    entry form `hess epRng pG qG qG sG i j = HG i j := by rfl`.  Both force
    the kernel through every slot inside one `rfl`.  What was FALSE is the
    generalisation that the second-order germ is therefore out of reach: the
    field projections `(germ epRng pG qG qG sG).eIJ = …` are each reachable,
    at ~30–35 s of kernel reduction apiece, because a projection forces only
    the sub-fields that slot needs.  That is the route taken above.

    ADJUDICATOR for `HG` being the Hessian: `rfl` in the Lean kernel, via
    `germ_G` and `hess_G`.  `r6_gift_hessian.py` (checks
    `V2.hessian_is_2JtJ_golden`, `V3a.entry_fields_golden`) is now a
    CORROBORATING independent computation, not the adjudicator — the two
    agree entrywise.  What this still does NOT cover is unchanged from the
    other worlds: the germ is a formal second derivative of a POLYNOMIAL,
    with no analytic content (no Taylor remainder, no neighbourhood). -/
def HG : M4E := hessOf epRng GG

/-- **THE HESSIAN, READ OFF THE COMPUTED GERM** — golden-world analogue of
    `hess_Y` / `hess_S` / `hess_C`, and identical in shape to them. -/
theorem hess_G : hess epRng pG qG qG sG = HG := by
  show hessOf epRng (germ epRng pG qG qG sG) = hessOf epRng GG
  rw [germ_G]

theorem HG_symm : ∀ a b, HG a b = HG b a := by decide

/-- **THE EXACT ENTRIES.**  Six live in `Z[φ]`; the four in the `(p,s)×(q,r)`
    cross block genuinely need `√φ` — this is the whole reason §8 exists.
    `H[p,q] = H[p,r] = (26−18φ)·√φ` and `H[q,s] = H[r,s] = (−12+8φ)·√φ`. -/
theorem HG_entries :
    HG 0 0 = ⟨⟨30,-8⟩, Zp.zero⟩ ∧ HG 0 1 = ⟨Zp.zero, ⟨26,-18⟩⟩ ∧
    HG 0 2 = ⟨Zp.zero, ⟨26,-18⟩⟩ ∧ HG 0 3 = ⟨⟨-12,8⟩, Zp.zero⟩ ∧
    HG 1 1 = ⟨⟨-18,16⟩, Zp.zero⟩ ∧ HG 1 2 = ⟨⟨-18,16⟩, Zp.zero⟩ ∧
    HG 1 3 = ⟨Zp.zero, ⟨-12,8⟩⟩ ∧ HG 2 2 = ⟨⟨-18,16⟩, Zp.zero⟩ ∧
    HG 2 3 = ⟨Zp.zero, ⟨-12,8⟩⟩ ∧ HG 3 3 = ⟨⟨2,12⟩, Zp.zero⟩ := by decide

/-- Exactly four of the ten distinct entries need the radical. -/
theorem HG_needs_radical :
    (HG 0 1).y ≠ Zp.zero ∧ (HG 0 2).y ≠ Zp.zero ∧
    (HG 1 3).y ≠ Zp.zero ∧ (HG 2 3).y ≠ Zp.zero ∧
    (HG 0 0).y = Zp.zero ∧ (HG 1 1).y = Zp.zero ∧
    (HG 2 2).y = Zp.zero ∧ (HG 3 3).y = Zp.zero ∧ (HG 0 3).y = Zp.zero ∧
    (HG 1 2).y = Zp.zero := by decide

/-! ### the freebie, recorded as such -/

/-- The gauge-torus tangent at the golden point, `(0, q, −r, 0)` with
    `q = r`. -/
def tangentG : V4E := mkVE Ep.zero qG (Ep.neg qG) Ep.zero
/-- The `q↔r` swap direction. -/
def swapDirE : V4E := mkVE Ep.zero Ep.one (Ep.neg Ep.one) Ep.zero

/-- **THE FREEBIE AT WORK.**  `q = r` here, so columns `q` and `r` of `H`
    coincide.  §6's `swapDir_null_of_cols_eq` is the general statement; this
    is the specimen. -/
theorem HG_cols_eq : ∀ a, HG a 1 = HG a 2 := by decide

/-- The gauge tangent is null — but at THIS world that is the freebie, not
    the content.  It is also, here, a scalar multiple of the swap direction
    (`q = r`), which is exactly why it proves nothing about rigidity. -/
theorem HG_tangent_null :
    (∀ a, mvecE HG tangentG a = Ep.zero) ∧
    (∀ a, mvecE HG swapDirE a = Ep.zero) ∧
    (∀ k, tangentG k = Ep.mul qG (swapDirE k)) := by
  refine ⟨by decide, by decide, by decide⟩

/-! ### rank exactly three — this IS content -/

theorem HG_det4_zero : det4E HG = Ep.zero := by decide

theorem HG_minor3_pos :
    det3E HG 0 1 3 0 1 3 = ⟨⟨1920,360⟩, Zp.zero⟩ ∧
    Ep.pos (det3E HG 0 1 3 0 1 3) = true := by
  refine ⟨by decide, by decide⟩

/-! ### the sum-of-squares certificate — the positivity half -/

def NG  : Ep := Ep.ofZ ⟨-160218240, 152446080⟩
def eG1 : Ep := Ep.ofZ ⟨-3867840, 5522880⟩
def eG2 : Ep := Ep.ofZ ⟨54720, -7440⟩

def LG1 : V4E := mkVE ⟨⟨30,-8⟩, Zp.zero⟩ ⟨Zp.zero, ⟨26,-18⟩⟩
                      ⟨Zp.zero, ⟨26,-18⟩⟩ ⟨⟨-12,8⟩, Zp.zero⟩
def LG2 : V4E := mkVE Ep.zero ⟨⟨-56,108⟩, Zp.zero⟩
                      ⟨⟨-56,108⟩, Zp.zero⟩ ⟨Zp.zero, ⟨32,-8⟩⟩
def LG3 : V4E := mkVE Ep.zero Ep.zero Ep.zero ⟨⟨54720,-7440⟩, Zp.zero⟩

/-- One entry of the golden certificate. -/
abbrev sosGat (a b : Fin 4) : Prop :=
  Ep.mul NG (HG a b) =
    Ep.add (Ep.add (Ep.mul eG1 (Ep.mul (LG1 a) (LG1 b)))
                   (Ep.mul eG2 (Ep.mul (LG2 a) (LG2 b))))
           (Ep.mul Ep.one (Ep.mul (LG3 a) (LG3 b)))

/-- **THE CERTIFICATE AT THE GOLDEN POINT.**
    `N·H = e₁·L₁⊗L₁ + e₂·L₂⊗L₂ + 1·L₃⊗L₃`, on the upper triangle; the lower
    triangle follows from `HG_symm` and the symmetry of `Lᵢ⊗Lᵢ`.

    Each entry is decided separately, which keeps every `decide` well inside the
    default budget.  (Round-7 correction G5: an earlier docstring justified the
    per-entry split by asserting that a single sixteen-cell `decide` "exceeds
    the default heartbeat budget" — that overrun was **never measured**, and
    after DEFECT 1 an unmeasured budget claim is exactly the sentence this
    project has learned not to write.  The per-entry split was chosen to keep
    each `decide` small and to avoid the question, not because the question was
    answered; no budget is raised either way.) -/
theorem sos_G :
    sosGat 0 0 ∧ sosGat 0 1 ∧ sosGat 0 2 ∧ sosGat 0 3 ∧
    sosGat 1 1 ∧ sosGat 1 2 ∧ sosGat 1 3 ∧
    sosGat 2 2 ∧ sosGat 2 3 ∧ sosGat 3 3 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide,
          by decide, by decide, by decide, by decide⟩

theorem sos_G_lower :
    sosGat 1 0 ∧ sosGat 2 0 ∧ sosGat 2 1 ∧
    sosGat 3 0 ∧ sosGat 3 1 ∧ sosGat 3 2 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- ...and all four scalars are strictly positive in the order of §8. -/
theorem sos_G_pos :
    Ep.pos NG = true ∧ Ep.pos eG1 = true ∧ Ep.pos eG2 = true ∧
    Ep.pos Ep.one = true := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- The certificate's three covectors annihilate the gauge tangent — the
    matrix identity therefore locates the flat direction exactly where §5
    locates it at Yang–Lee, even though the ∀-quantified reading is not
    proved at this world (see the section header). -/
theorem LG_kill_tangent :
    dotE LG1 tangentG = Ep.zero ∧ dotE LG2 tangentG = Ep.zero ∧
    dotE LG3 tangentG = Ep.zero := by
  refine ⟨by decide, by decide, by decide⟩

/-- ANTI-VACUITY: the covectors are not the zero covector, so the certificate
    is not degenerate. -/
theorem LG_nontrivial :
    LG1 0 ≠ Ep.zero ∧ LG2 1 ≠ Ep.zero ∧ LG3 3 ≠ Ep.zero := by
  refine ⟨by decide, by decide, by decide⟩

/-! ══════════════════════════════════════════════════════════════════════
    ## §10.  AXIOM RECEIPTS

    Every theorem above is checked below.  The permitted profiles are
    `[propext]`, `[Quot.sound]`, `[propext, Quot.sound]`, or none.  Anything
    else — in particular `Classical.choice` or `sorryAx` — is a failure.
    (`omega` on a CONJUNCTIVE goal silently pulls in `Classical.choice`; every
    `omega` in this file runs on a scalar `Int` goal after an explicit
    `refine ⟨?_, ?_⟩` split, exactly for that reason.)
    ══════════════════════════════════════════════════════════════════════ -/

/-! The audit is run OUTSIDE the file, so the file itself compiles silently
    (project convention: `Anyon.lean` contains no `#print axioms` either).
    Append

        #print axioms <name>

    for each theorem, or run the whole list at once; the result for every
    theorem in this file (the count is in the census output, not hard-coded
    here -- round-7 correction G3) is one of

        [propext]      [Quot.sound]      [propext, Quot.sound]      (none)

    and never `Classical.choice` or `sorryAx`.  The `Classical.choice` trap
    the project has hit twice is `omega` on a CONJUNCTIVE goal; every `omega`
    below runs on a scalar `Int` goal reached through an explicit
    `refine ⟨?_, ?_⟩` split, and `by_contra` (which routes through
    `Classical.byContradiction`) appears nowhere — `by_cases` on decidable
    propositions is used instead. -/

end Workshop.R6
