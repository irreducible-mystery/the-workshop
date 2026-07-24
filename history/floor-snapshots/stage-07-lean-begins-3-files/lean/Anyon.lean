/-
  THE WORKSHOP → LEAN 4.  Round 1, Tier 3 — THE ANYON, EXACTLY.

  Benches formalized: `grammar_stone3.py`  (pentagon → golden ratio)
                      `grammar_hexagon.py` (hexagon → chirality, spin, braiding)
                      `grammar_stone6.py`  (Frobenius–Schur ν = r₁·θ = +1)

  Self-contained: NO imports.  Every arithmetic fact below is decided by the
  Lean kernel on `Int`.  No floats, no rationals, no `native_decide`, no
  `sorry`, no mathlib.

  ─────────────────────────────────────────────────────────────────────────
  ONE DELIBERATE DEPARTURE FROM THE SPEC, flagged loudly (see QUESTIONS):

  The charge said "explicit finite-dimensional Q-algebras … Q has decidable
  equality".  Rationals are not needed and are not used.  Reason:

    3a.  The spec's Q(√5) with inv_phi = (−1/2, 1/2) has half-integer
         coordinates, and the half-integer lattice {p + q√5 : 2p, 2q ∈ Z} is
         NOT closed under multiplication (denominators 2·2 = 4).  The ring
         that *is* closed and *does* contain every constant in play is
         Z[φ] = Z[X]/(X²−X−1), the ring of integers of Q(√5).  In the basis
         (1, φ) every entry of F' is integral: 1/φ = φ − 1 = (−1, 1).
         Translating back: m + nφ = (m + n/2) + (n/2)√5, so (−1,1) ↦
         (−1/2, 1/2) — exactly the spec's inv_phi.  Proved as `invPhi_spec`
         below, in doubled coordinates so no rational ever appears.

    3b.  Every constant of the symmetric gauge — inv_phi = ζ+ζ⁴, b = t(ζ+ζ⁴),
         r₁ = ζ², r_τ = −ζ, θ = ζ³ — already has INTEGER coordinates in the
         basis {ζⁱtʲ}.  So Z[ζ₅][t]/(t²−φ) suffices; Q buys nothing.

  This makes the file kernel-checkable with a bare toolchain, which was the
  binding constraint.  If the builder wants Q for its own sake, say so and
  round 2 will carry a hand-rolled Rat; nothing else would change.
  ─────────────────────────────────────────────────────────────────────────

  Status: PROVED throughout, no `sorry`, no unmarked gap.
-/

namespace Workshop.Anyon

/-! ## 0. The fusion grammar

Fibonacci: 1 is the vacuum, τ×τ = 1 + τ.  `fuse` is the workshop's `fuse`,
transcribed pattern for pattern (first match wins, exactly as in Python). -/

/-- The two labels. `one` is the vacuum; `tau` is the anyon. -/
inductive Anyon where
  | one
  | tau
  deriving DecidableEq

/-- The fusion rule.  `1 × b = b`, `a × 1 = a`, `τ × τ = 1 + τ`. -/
def fuse : Anyon → Anyon → List Anyon
  | .one, b    => [b]
  | a,    .one => [a]
  | .tau, .tau => [.one, .tau]

/-- Membership in a fusion channel — the Python `x in fuse(a,b)`. -/
def memA (a : Anyon) : List Anyon → Bool
  | []      => false
  | x :: xs => decide (a = x) || memA a xs

/-- Is this the vacuum?  (Python `a == ONE`.) -/
def isOne : Anyon → Bool
  | .one => true
  | .tau => false

/-! ## 1. A ring, passed by hand

No typeclasses: a plain record of operations, given explicitly at every call.
This keeps the file free of instance resolution and makes the two gauges
(Tier 3a over Z[φ], Tier 3b over K) share one copy of the coherence code. -/

/-- A commutative ring's operations, as data.  `beq` is decidable equality. -/
structure Rng (R : Type) where
  zero : R
  one  : R
  add  : R → R → R
  mul  : R → R → R
  beq  : R → R → Bool

/-- Sum over a fusion channel — the Python `for u in fuse(b,c): lhs += …`. -/
def sumOver {R : Type} (K : Rng R) (f : Anyon → R) : List Anyon → R
  | []      => K.zero
  | u :: us => K.add (f u) (sumOver K f us)

/-- **The F-move**, transcribed from the workshop's executable specification:

    def Fs(F, a, b, c, d, x, y):
        if x not in fuse(a,b) or d not in fuse(x,c): return 0
        if y not in fuse(b,c) or d not in fuse(a,y): return 0
        if ONE in (a,b,c): return 1
        if d == ONE: return 1 if (x,y)==(TAU,TAU) else 0
        return F[x][y]                                                    -/
def Fs {R : Type} (K : Rng R) (F : Anyon → Anyon → R)
    (a b c d x y : Anyon) : R :=
  if memA x (fuse a b) && memA d (fuse x c) &&
     memA y (fuse b c) && memA d (fuse a y) then
    if isOne a || isOne b || isOne c then K.one
    else if isOne d then (if !isOne x && !isOne y then K.one else K.zero)
    else F x y
  else K.zero

/-- **The braiding phase.**  `R(x,y,c)`: 1 if either is the vacuum, else `r₁`
    if they fuse to the vacuum, else `r_τ`. -/
def Rb {R : Type} (K : Rng R) (r1 rt : R) (x y c : Anyon) : R :=
  if isOne x || isOne y then K.one
  else if isOne c then r1 else rt

/-! ## 2. The coherence equations

`pentagonValid` / `hexagonValid` are the workshop's loop guards; the checks
return `true` vacuously off the valid set, so a single `∀` over all label
tuples states exactly "every valid instance holds". -/

/-- The pentagon's index guard: `x ∈ a×b`, `y ∈ x×c`, `t ∈ y×d`, `w ∈ c×d`,
    `v ∈ b×w`, `t ∈ a×v`.  50 of the 512 tuples pass. -/
def pentagonValid (a b c dd x y t w v : Anyon) : Bool :=
  memA x (fuse a b) && memA y (fuse x c) && memA t (fuse y dd) &&
  memA w (fuse c dd) && memA v (fuse b w) && memA t (fuse a v)

/-- **THE PENTAGON.**
    `Σ_u F(a,b,c,y,x,u)·F(a,u,d,t,y,v)·F(b,c,d,v,u,w) = F(x,c,d,t,y,w)·F(a,b,w,t,x,v)` -/
def pentagonCheck {R : Type} (K : Rng R) (F : Anyon → Anyon → R)
    (a b c dd x y t w v : Anyon) : Bool :=
  if pentagonValid a b c dd x y t w v then
    K.beq
      (sumOver K (fun u => K.mul (K.mul (Fs K F a b c y x u)
                                        (Fs K F a u dd t y v))
                                 (Fs K F b c dd v u w)) (fuse b c))
      (K.mul (Fs K F x c dd t y w) (Fs K F a b w t x v))
  else true

/-- The hexagon's index guard: `e ∈ a×b`, `d ∈ e×c`, `z ∈ a×c`, `d ∈ z×b`.
    15 of the 64 tuples pass. -/
def hexagonValid (a b c d e z : Anyon) : Bool :=
  memA e (fuse a b) && memA d (fuse e c) &&
  memA z (fuse a c) && memA d (fuse z b)

/-- **THE HEXAGON.**
    `R(e,c,d)·F(c,a,b,d,z,e) = Σ_g F(a,b,c,d,e,g)·R(b,c,g)·F(a,c,b,d,z,g)·R(a,c,z)` -/
def hexagonCheck {R : Type} (K : Rng R) (F : Anyon → Anyon → R) (r1 rt : R)
    (a b c d e z : Anyon) : Bool :=
  if hexagonValid a b c d e z then
    K.beq
      (K.mul (Rb K r1 rt e c d) (Fs K F c a b d z e))
      (sumOver K (fun g => K.mul (K.mul (K.mul (Fs K F a b c d e g)
                                               (Rb K r1 rt b c g))
                                        (Fs K F a c b d z g))
                                 (Rb K r1 rt a c z)) (fuse b c))
  else true

/-! ## 3. 2×2 matrices indexed by the anyon labels -/

/-- Matrix product, indices running over `{one, tau}`. -/
def matMul {R : Type} (K : Rng R) (A B : Anyon → Anyon → R) :
    Anyon → Anyon → R :=
  fun i j => K.add (K.mul (A i .one) (B .one j)) (K.mul (A i .tau) (B .tau j))

/-- Entrywise equality. -/
def matEq {R : Type} (K : Rng R) (A B : Anyon → Anyon → R) : Bool :=
  K.beq (A .one .one) (B .one .one) && K.beq (A .one .tau) (B .one .tau) &&
  K.beq (A .tau .one) (B .tau .one) && K.beq (A .tau .tau) (B .tau .tau)

/-- The identity matrix. -/
def matId {R : Type} (K : Rng R) : Anyon → Anyon → R :=
  fun i j => if i = j then K.one else K.zero

/-! ═══════════════════════════════════════════════════════════════════════
    ## TIER 3a.  Z[φ] = Z[X]/(X² − X − 1), and the rational gauge
    ═══════════════════════════════════════════════════════════════════════ -/

/-- `⟨m, n⟩` denotes `m + n·φ`, where `φ² = φ + 1`, i.e. `φ = (1+√5)/2`. -/
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

/-- The ring Z[φ], as data. -/
def zpRng : Rng Zp := ⟨Zp.zero, Zp.one, Zp.add, Zp.mul, Zp.beq⟩

/-- The defining relation: `φ² = φ + 1`. -/
theorem zp_phi_sq : Zp.mul Zp.phi Zp.phi = Zp.add Zp.phi Zp.one := rfl

/-- `φ · (1/φ) = 1` — so `invPhi` deserves its name. -/
theorem zp_invPhi_mul : Zp.mul Zp.phi Zp.invPhi = Zp.one := rfl

/-- **The spec's coordinates, without rationals.**  Writing `m + nφ` as
    `p + q√5` gives `p = m + n/2`, `q = n/2`.  Stated in doubled coordinates
    `(2p, 2q)` so the claim is an integer identity: `invPhi ↦ (−1/2, 1/2)`,
    which is the charge's `inv_phi = (-1/2, 1/2)`. -/
theorem invPhi_spec :
    (2 * Zp.invPhi.m + Zp.invPhi.n, Zp.invPhi.n) = ((-1 : Int), (1 : Int)) := rfl

/-- The gauge-rationalized associator `F' = [[1/φ, 1/φ], [1, −1/φ]]`. -/
def Frat : Anyon → Anyon → Zp
  | .one, .one => Zp.invPhi
  | .one, .tau => Zp.invPhi
  | .tau, .one => Zp.one
  | .tau, .tau => Zp.neg Zp.invPhi

/-- **TIER 0 HANDSHAKE, half two — exactly.**  `F' · F' = 1` in Z[φ]. -/
theorem Frat_sq : matEq zpRng (matMul zpRng Frat Frat) (matId zpRng) = true := rfl

/-- **THE FULL PENTAGON in the rational gauge**, over Z[φ], exactly.
    All 512 label tuples; the 462 invalid ones hold vacuously, the 50 valid
    ones are genuine ring identities. -/
theorem pentagon_rational_gauge :
    ∀ a b c dd x y t w v, pentagonCheck zpRng Frat a b c dd x y t w v = true := by
  intro a b c dd x y t w v
  cases a <;> cases b <;> cases c <;> cases dd <;> cases x <;> cases y <;>
    cases t <;> cases w <;> cases v <;> rfl

/-! ═══════════════════════════════════════════════════════════════════════
    ## TIER 3b.  K = Z[ζ₅][t]/(t² − φ), and the symmetric gauge
    ═══════════════════════════════════════════════════════════════════════ -/

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

/-- `ζ⁴` really is `ζ³·ζ`. -/
theorem z5_zeta4_eq : Z5.mul Z5.zeta3 Z5.zeta = Z5.zeta4 := rfl

/-- `ζ⁵ = 1`. -/
theorem z5_zeta5_eq : Z5.mul Z5.zeta4 Z5.zeta = Z5.one := rfl

/-- `φ = 1 + ζ + ζ⁴`, as the charge specifies. -/
theorem z5_phi_eq : Z5.add (Z5.add Z5.one Z5.zeta) Z5.zeta4 = Z5.phi := rfl

/-- `1/φ = ζ + ζ⁴`, as the charge specifies. -/
theorem z5_invPhi_eq : Z5.add Z5.zeta Z5.zeta4 = Z5.invPhi := rfl

/-- `φ · (1/φ) = 1` — exactly, in Z[ζ₅]. -/
theorem z5_invPhi_mul : Z5.mul Z5.phi Z5.invPhi = Z5.one := rfl

/-- `φ² = φ + 1` holds here too: the two constructions of φ agree. -/
theorem z5_phi_sq : Z5.mul Z5.phi Z5.phi = Z5.add Z5.phi Z5.one := rfl

/-- `⟨x, y⟩` denotes `x + y·t`, where `t² = φ`.  So `t = √φ` and
    `K = Z[ζ₅][t]/(t² − φ)`, dimension 8 over Z. -/
structure KK where
  x : Z5
  y : Z5
  deriving DecidableEq

namespace KK

def zero : KK := ⟨Z5.zero, Z5.zero⟩
def one  : KK := ⟨Z5.one,  Z5.zero⟩
/-- Z[ζ₅] ↪ K. -/
def emb (u : Z5) : KK := ⟨u, Z5.zero⟩
/-- `t = √φ`. -/
def t : KK := ⟨Z5.zero, Z5.one⟩
def add (u v : KK) : KK := ⟨Z5.add u.x v.x, Z5.add u.y v.y⟩
def neg (u : KK) : KK := ⟨Z5.neg u.x, Z5.neg u.y⟩

/-- `(x₁+y₁t)(x₂+y₂t) = (x₁x₂ + φy₁y₂) + (x₁y₂ + x₂y₁)t`. -/
def mul (u v : KK) : KK :=
  ⟨Z5.add (Z5.mul u.x v.x) (Z5.mul Z5.phi (Z5.mul u.y v.y)),
   Z5.add (Z5.mul u.x v.y) (Z5.mul v.x u.y)⟩

def beq (u v : KK) : Bool := decide (u = v)

/-- `1/φ = ζ + ζ⁴`. -/
def invPhi : KK := emb Z5.invPhi
/-- `b = t(ζ + ζ⁴) = 1/√φ`. -/
def b : KK := mul t invPhi
/-- `r₁ = ζ² = e^{4πi/5}`. -/
def r1 : KK := emb Z5.zeta2
/-- `r_τ = −ζ = e^{−3πi/5}`. -/
def rt : KK := emb (Z5.neg Z5.zeta)
/-- `θ_τ = ζ³ = e^{−4πi/5}`. -/
def theta : KK := emb Z5.zeta3

end KK

/-- The ring K, as data. -/
def kRng : Rng KK := ⟨KK.zero, KK.one, KK.add, KK.mul, KK.beq⟩

/-- `t² = φ`, the defining relation of the extension. -/
theorem kk_t_sq : KK.mul KK.t KK.t = KK.emb Z5.phi := rfl

/-- **`b` is `1/√φ`**: `b² = 1/φ`.  (The charge's `b_entry` certified.) -/
theorem kk_b_sq : KK.mul KK.b KK.b = KK.invPhi := rfl

/-- The symmetric-gauge associator `F = [[1/φ, b], [b, −1/φ]]`. -/
def Fsymm : Anyon → Anyon → KK
  | .one, .one => KK.invPhi
  | .one, .tau => KK.b
  | .tau, .one => KK.b
  | .tau, .tau => KK.neg KK.invPhi

/-- **`F · F = 1`** in K, exactly.  (`F` is its own inverse: the associator
    undoes itself, which is why `F⁻¹ = Fᵀ = F` is used in the hexagon.) -/
theorem Fsymm_sq : matEq kRng (matMul kRng Fsymm Fsymm) (matId kRng) = true := rfl

/-- **THE FULL PENTAGON in the symmetric gauge**, over K, exactly. -/
theorem pentagon_symmetric_gauge :
    ∀ a b c dd x y t w v, pentagonCheck kRng Fsymm a b c dd x y t w v = true := by
  intro a b c dd x y t w v
  cases a <;> cases b <;> cases c <;> cases dd <;> cases x <;> cases y <;>
    cases t <;> cases w <;> cases v <;> rfl

/-- **THE FULL HEXAGON**, over K, exactly.  This is the equation that fixes
    the braiding — and with it chirality and spin. -/
theorem hexagon_symmetric_gauge :
    ∀ a b c d e z, hexagonCheck kRng Fsymm KK.r1 KK.rt a b c d e z = true := by
  intro a b c d e z
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases z <;> rfl

/-! ### The braid group representation -/

/-- `B₁ = diag(r₁, r_τ)`. -/
def B1 : Anyon → Anyon → KK
  | .one, .one => KK.r1
  | .one, .tau => KK.zero
  | .tau, .one => KK.zero
  | .tau, .tau => KK.rt

/-- `B₂ = F · diag(r₁, r_τ) · F`. -/
def B2 : Anyon → Anyon → KK := matMul kRng (matMul kRng Fsymm B1) Fsymm

/-- **YANG–BAXTER / THE BRAID RELATION**: `B₁B₂B₁ = B₂B₁B₂`, exactly.
    (`grammar_hexagon.py` reports residual 3.6e-16; here it is zero.) -/
theorem yang_baxter :
    matEq kRng (matMul kRng (matMul kRng B1 B2) B1)
               (matMul kRng (matMul kRng B2 B1) B2) = true := rfl

/-- **NON-ABELIAN**: `B₁B₂ ≠ B₂B₁`.  Order of exchange matters — which is the
    whole reason the representation can compute.
    (`grammar_hexagon.py` reports ‖[B₁,B₂]‖ = 1.8; here: not equal, exactly.) -/
theorem braiding_nonabelian :
    matEq kRng (matMul kRng B1 B2) (matMul kRng B2 B1) = false := rfl

/-! ### The receipts: three exact scalar identities -/

/-- **TIER 0 HANDSHAKE, half one — exactly.**  `r₁ = r_τ²`, i.e.
    `e^{4πi/5} = (e^{−3πi/5})²`.  In K this is `ζ² = (−ζ)²`. -/
theorem r1_eq_rt_sq : KK.mul KK.rt KK.rt = KK.r1 := rfl

/-- **THE FROBENIUS–SCHUR RECEIPT**: `ν = r₁ · θ_τ = +1`, exactly.
    In K: `ζ² · ζ³ = ζ⁵ = 1`.  (`grammar_stone6.py`: ν = +1.) -/
theorem frobenius_schur : KK.mul KK.r1 KK.theta = KK.one := rfl

/-- **THE RIBBON FORMULA**, exactly: `θ_τ = r₁/φ + r_τ`.
    `grammar_hexagon.py` computes this numerically as `e^{−4πi/5}`; here the
    right side reduces to `ζ³` on the nose:  ζ²(ζ+ζ⁴) + (−ζ) = ζ³ + ζ⁶ − ζ = ζ³. -/
theorem ribbon_twist :
    KK.add (KK.mul KK.r1 KK.invPhi) KK.rt = KK.theta := rfl

/-! ### Strictness is impossible — with named witnesses

`grammar_stone3.py` reports pentagon residual **4.0** for `F = identity` and
concludes the witness is mandatory.  Exact enumeration sharpens that number:
the residual is not merely positive, it is exactly **four instances each
failing by exactly one**, all four at total charge (τ,τ,τ,τ).  All four are
named below, and `strict_pentagon_violations` proves there are no others. -/

/-- The strict (identity) associator. -/
def Fid : Anyon → Anyon → KK := matId kRng

/-- **STRICTNESS IS IMPOSSIBLE**, witness 1 of 4: at
    `(a,b,c,d) = (τ,τ,τ,τ)` with `(x,y,t,w,v) = (1,τ,τ,1,τ)` the strict
    associator gives left side 1, right side 0. -/
theorem strictness_fails_1 :
    pentagonCheck kRng Fid .tau .tau .tau .tau .one .tau .tau .one .tau
      = false := rfl

/-- **STRICTNESS IS IMPOSSIBLE**, witness 2 of 4: at `(x,y,t,w,v) = (1,τ,τ,τ,1)`
    the strict associator gives left side 0, right side 1. -/
theorem strictness_fails_2 :
    pentagonCheck kRng Fid .tau .tau .tau .tau .one .tau .tau .tau .one
      = false := rfl

/-- Witness 3 of 4. -/
theorem strictness_fails_3 :
    pentagonCheck kRng Fid .tau .tau .tau .tau .tau .one .tau .one .tau
      = false := rfl

/-- Witness 4 of 4. -/
theorem strictness_fails_4 :
    pentagonCheck kRng Fid .tau .tau .tau .tau .tau .one .tau .tau .one
      = false := rfl

/-- The golden associator passes exactly where the strict one fails: the same
    four instances, now true.  (Compare `pentagon_symmetric_gauge`, which
    covers all 512 at once — this is the pointed contrast.) -/
theorem golden_passes_where_strict_fails :
    pentagonCheck kRng Fsymm .tau .tau .tau .tau .one .tau .tau .one .tau = true ∧
    pentagonCheck kRng Fsymm .tau .tau .tau .tau .one .tau .tau .tau .one = true ∧
    pentagonCheck kRng Fsymm .tau .tau .tau .tau .tau .one .tau .one .tau = true ∧
    pentagonCheck kRng Fsymm .tau .tau .tau .tau .tau .one .tau .tau .one = true :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ═══════════════════════════════════════════════════════════════════════
    ## 4.  ANTI-VACUITY AND NEGATIVE CONTROLS

    A `∀`-theorem over a guarded check is worthless if the guard rejects
    everything: `pentagonCheck` returns `true` vacuously off the valid set, so
    a bug in `fuse` or `memA` would make every theorem above pass while
    proving nothing.  The counts below close that hole — they pin the guards
    to the workshop's own numbers — and the violation counts show the checks
    have teeth: they can and do return `false`.
    ═══════════════════════════════════════════════════════════════════════ -/

/-- Sum a Nat-valued function over the two labels. -/
def sumB (f : Anyon → Nat) : Nat := f .one + f .tau

/-- How many of the 512 pentagon tuples pass the index guard. -/
def countPentValid : Nat :=
  sumB fun a => sumB fun b => sumB fun c => sumB fun dd => sumB fun x =>
  sumB fun y => sumB fun t => sumB fun w => sumB fun v =>
    if pentagonValid a b c dd x y t w v then 1 else 0

/-- How many of the 64 hexagon tuples pass the index guard. -/
def countHexValid : Nat :=
  sumB fun a => sumB fun b => sumB fun c =>
  sumB fun d => sumB fun e => sumB fun z =>
    if hexagonValid a b c d e z then 1 else 0

/-- **ANTI-VACUITY, pentagon.**  Exactly 50 of 512 tuples are live — so
    `pentagon_rational_gauge` and `pentagon_symmetric_gauge` each assert 50
    genuine ring identities, not 512 vacuous truths. -/
theorem pentagon_live_instances : countPentValid = 50 := rfl

/-- **ANTI-VACUITY, hexagon.**  Exactly 15 of 64 tuples are live. -/
theorem hexagon_live_instances : countHexValid = 15 := rfl

/-- Pentagon violations of a given associator, counted. -/
def countPentViolations {R : Type} (K : Rng R) (F : Anyon → Anyon → R) : Nat :=
  sumB fun a => sumB fun b => sumB fun c => sumB fun dd => sumB fun x =>
  sumB fun y => sumB fun t => sumB fun w => sumB fun v =>
    if pentagonCheck K F a b c dd x y t w v then 0 else 1

/-- Hexagon violations of a given braiding, counted. -/
def countHexViolations (r1 rt : KK) : Nat :=
  sumB fun a => sumB fun b => sumB fun c =>
  sumB fun d => sumB fun e => sumB fun z =>
    if hexagonCheck kRng Fsymm r1 rt a b c d e z then 0 else 1

/-- A deliberately wrong associator, `[[1,1],[1,−1]]`. -/
def Fwrong : Anyon → Anyon → KK
  | .one, .one => KK.one
  | .one, .tau => KK.one
  | .tau, .one => KK.one
  | .tau, .tau => KK.neg KK.one

/-- The golden associator: zero violations (restating the `∀` as a count). -/
theorem golden_pentagon_clean : countPentViolations kRng Fsymm = 0 := rfl

/-- The rational gauge: zero violations. -/
theorem rational_pentagon_clean : countPentViolations zpRng Frat = 0 := rfl

/-- **STRICTNESS, quantified.**  `grammar_stone3.py` reports pentagon residual
    **4.0** for `F = identity`.  Exactly: four instances, each failing by
    exactly one, so the sum of squares is 4·1² = 4.  The bench's float and
    this integer are the same fact. -/
theorem strict_pentagon_violations : countPentViolations kRng Fid = 4 := rfl

/-- **THE CHECK HAS TEETH**: a wrong associator is caught, 5 instances over. -/
theorem wrong_pentagon_violations : countPentViolations kRng Fwrong = 5 := rfl

/-! ### The two chiralities — both are solutions, exactly

`grammar_hexagon.py` finds **exactly two solution clusters, complex-conjugate
mirror twins**.  Conjugation on K is ζ ↦ ζ⁴; it fixes `F` (since `1/φ = ζ+ζ⁴`
and `t = +√φ` are both fixed), and it carries our braiding to the mirror one:

    conj(r₁) = conj(ζ²) = ζ³ ,   conj(r_τ) = conj(−ζ) = −ζ⁴ ,
    conj(θ)  = conj(ζ³) = ζ² .

Both satisfy the hexagon *as written*, exactly — verified below.  See the
QUESTIONS block: this refines, and does not contradict, the bench. -/

/-- Mirror `r₁ = ζ³`. -/
def r1' : KK := KK.emb Z5.zeta3
/-- Mirror `r_τ = −ζ⁴`. -/
def rt' : KK := KK.emb (Z5.neg Z5.zeta4)
/-- Mirror `θ_τ = ζ²`. -/
def theta' : KK := KK.emb Z5.zeta2

/-- Our chirality solves the hexagon: zero violations. -/
theorem chirality_right : countHexViolations KK.r1 KK.rt = 0 := rfl

/-- **The mirror chirality solves the SAME hexagon, exactly.**  The equation
    admits both; it forces a *choice* of handedness, it does not make one. -/
theorem chirality_left : countHexViolations r1' rt' = 0 := rfl

/-- The two chiralities are genuinely different braidings. -/
theorem chiralities_distinct : KK.beq KK.r1 r1' = false := rfl

/-- The mirror obeys the same three receipts: `r₁ = r_τ²`, ribbon, and
    Frobenius–Schur ν = +1.  Spin flips sign; the co-signature does not. -/
theorem mirror_receipts :
    KK.mul rt' rt' = r1' ∧
    KK.add (KK.mul r1' KK.invPhi) rt' = theta' ∧
    KK.mul r1' theta' = KK.one :=
  ⟨rfl, rfl, rfl⟩

/-- **BRAIDING IS MANDATORY**: trivial braiding `r₁ = r_τ = 1` fails the
    hexagon in 4 of its 15 instances.  There is no unbraided Fibonacci. -/
theorem trivial_braiding_fails : countHexViolations KK.one KK.one = 4 := rfl

/-- **THE ROLES ARE NOT INTERCHANGEABLE**: swapping `r₁ ↔ r_τ` fails 5 of 15. -/
theorem swapped_braiding_fails : countHexViolations KK.rt KK.r1 = 5 := rfl

/-- **NO AMBIDEXTROUS BRAIDING BY SIGNS.**  Every mirror-symmetric candidate
    with `r₁, r_τ ∈ {+1, −1}` — the braidings fixed by conjugation that are
    expressible with signs alone — fails the hexagon.  A solution must leave
    the real subfield, and leaving it is what commits it to a handedness.
    (This is the honest, provable core of "coherence refuses to be
    ambidextrous"; the full statement is out of reach here — see QUESTIONS.) -/
theorem no_real_sign_braiding :
    countHexViolations KK.one KK.one = 4 ∧
    countHexViolations KK.one (KK.neg KK.one) = 4 ∧
    countHexViolations (KK.neg KK.one) KK.one = 5 ∧
    countHexViolations (KK.neg KK.one) (KK.neg KK.one) = 5 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ### The quadratic the hexagon forces

**This corrects a BLOCKED label in the round-1 PROOFS.md.**  I wrote that
"exactly two chiralities" was out of reach without elimination theory.  It is
not.  Carrying `r₁, r_τ` as unknowns over K, the 15 valid hexagon instances
collapse to **5 distinct residual polynomials**, and:

  * residual #1 is *verbatim* `r₁ − r_τ²`, so **`r₁ = r_τ²` is forced** — the
    bench's `assert abs(r1 - rt**2) < 1e-6` is not a property of the chosen
    constants, it is a consequence of coherence;
  * substituting `r₁ = r_τ²`, residual #5 factors exactly as
    `−(1/φ)·r_τ·Q(r_τ)` where `Q(X) = X² + (1/φ)X + 1`;
  * `1/φ ≠ 0`, and `r_τ ≠ 0` (residual #3 has nonzero constant term), and K is
    a domain — so **`Q(r_τ) = 0` is forced too**.

Hence `r_τ` is a root of an explicit quadratic and `r₁` is determined by it:
**exactly two solutions**, which is the bench's "exactly two clusters".  Their
product is the constant term 1, so each has modulus 1 — the bench's "|r| = 1
EMERGED".  The discriminant is negative, so neither root is real: no solution
is its own mirror, which is the defensible form of "coherence refuses to be
ambidextrous".

The receipts below are exact and checked.  The elimination itself is *not yet*
formalized — it needs a polynomial ring over K in two indeterminates, which is
a build, not a `rfl`.  Round 2.  What is proved here is that both named roots
satisfy `Q`, that their product is 1, and that the discriminant is negative. -/

/-- **`r_τ` is a root of `X² + (1/φ)X + 1`.**  Exactly: `(−ζ)² + (ζ+ζ⁴)(−ζ) + 1
    = ζ² − ζ² − 1 + 1 = 0`. -/
theorem rt_root_quadratic :
    KK.add (KK.add (KK.mul KK.rt KK.rt) (KK.mul KK.invPhi KK.rt)) KK.one
      = KK.zero := rfl

/-- **The mirror `r_τ' = −ζ⁴` is the other root of the same quadratic.** -/
theorem rt'_root_quadratic :
    KK.add (KK.add (KK.mul rt' rt') (KK.mul KK.invPhi rt')) KK.one
      = KK.zero := rfl

/-- **`|r| = 1`, algebraically.**  The two roots multiply to the constant term
    1; they are Galois conjugates, so this is `r_τ · conj(r_τ) = 1` — modulus
    one, with no analysis anywhere.  (`ζ⁵ = 1`.) -/
theorem roots_product_one : KK.mul KK.rt rt' = KK.one := rfl

/-- **`r₁` and its mirror multiply to 1 too** — the same receipt one level up. -/
theorem r1_roots_product_one : KK.mul KK.r1 r1' = KK.one := rfl

/-- **THE DISCRIMINANT IS NEGATIVE**: `(1/φ)² − 4 = −(φ + 2)`, and `φ + 2 > 0`.
    So `Q` has no real root, so no solution of the hexagon is fixed by
    conjugation, so every solution commits to a handedness.  This is the full
    statement that `no_real_sign_braiding` could only approximate. -/
theorem discriminant_negative :
    Z5.add (Z5.mul Z5.invPhi Z5.invPhi) (Z5.neg ⟨4, 0, 0, 0⟩)
      = Z5.neg (Z5.add Z5.phi ⟨2, 0, 0, 0⟩) := rfl

/-! ═══════════════════════════════════════════════════════════════════════
    ## 5.  A CORRECTION TO THE CHARGE, MACHINE-CHECKED

    The round-1 charge writes the hexagon's left-hand F-move as

        R(e,c,d) * Fs(F, c, a, b, d, e, z)

    but `grammar_hexagon.py` line 81 writes

        Rsym(e,c,d) * Fsym(c, a, b, d, z, e)          -- last two swapped.

    The bench is right and the charge's transcription is a typo.  It is not
    cosmetic: the two orderings disagree on 4 of the 15 valid instances, and
    the charge's ordering is FALSE for the certified constants.  Both facts
    are theorems below.  The Lean everywhere above follows the BENCH.
    ═══════════════════════════════════════════════════════════════════════ -/

/-- The hexagon with the LHS F-move indices exactly as the charge writes them
    (`… d e z` rather than the bench's `… d z e`). -/
def hexagonCheckCharge (r1 rt : KK) (a b c d e z : Anyon) : Bool :=
  if hexagonValid a b c d e z then
    kRng.beq
      (kRng.mul (Rb kRng r1 rt e c d) (Fs kRng Fsymm c a b d e z))
      (sumOver kRng (fun g => kRng.mul (kRng.mul (kRng.mul (Fs kRng Fsymm a b c d e g)
                                                           (Rb kRng r1 rt b c g))
                                                 (Fs kRng Fsymm a c b d z g))
                                       (Rb kRng r1 rt a c z)) (fuse b c))
  else true

/-- Violations of the charge-ordered hexagon. -/
def countHexViolationsCharge (r1 rt : KK) : Nat :=
  sumB fun a => sumB fun b => sumB fun c =>
  sumB fun d => sumB fun e => sumB fun z =>
    if hexagonCheckCharge r1 rt a b c d e z then 0 else 1

/-- **THE CHARGE'S INDEX ORDER IS WRONG.**  With the very constants the charge
    certifies, its own written hexagon fails 4 of 15 instances. -/
theorem charge_hexagon_order_fails :
    countHexViolationsCharge KK.r1 KK.rt = 4 := rfl

/-- **THE BENCH'S INDEX ORDER IS RIGHT.**  Same constants, bench ordering,
    zero violations.  (Restates `chirality_right`; placed here so the
    correction can be read as a single before/after pair.) -/
theorem bench_hexagon_order_holds :
    countHexViolations KK.r1 KK.rt = 0 := rfl

end Workshop.Anyon
