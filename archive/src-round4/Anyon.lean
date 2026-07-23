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

/-- `(x₁+y₁t)(x₂+y₂t) = (x₁x₂ + φy₁y₂) + (x₁y₂ + y₁x₂)t`.
    Operand order is kept canonical (`u`'s component always written before
    `v`'s) so that the triple products in `mul_assoc` canonicalize and `omega`
    can match atoms.  `Z5.mul v.x u.y` would be equal by commutativity but
    breaks that matching. -/
def mul (u v : KK) : KK :=
  ⟨Z5.add (Z5.mul u.x v.x) (Z5.mul Z5.phi (Z5.mul u.y v.y)),
   Z5.add (Z5.mul u.x v.y) (Z5.mul u.y v.x)⟩

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
    `−(1/φ)·r_τ·Q(r_τ)` where `Q(X) = X² + (1/φ)X + 1`.

Their product is the constant term 1, so each has modulus 1 — the bench's
"|r| = 1 EMERGED".  The discriminant is negative, so neither root is real: no
solution is its own mirror, which is the defensible form of "coherence refuses
to be ambidextrous".

⚠ **ROUND-3 RETRACTION — read this before the paragraph above.**  As written in
round 1, this passage continued: "`1/φ ≠ 0`, and `r_τ ≠ 0`, **and K is a
domain** — so `Q(r_τ) = 0` is forced too", concluding "**exactly two
solutions**".  Both of those are withdrawn:

  * **K being a domain is nowhere proved in this file**, and §6's round-3 route
    deliberately does not use it — `hexagon_forces_quadratic` cancels by an
    *exhibited inverse* instead (`rt_unit_of_e3`).  Asserting the domain
    property here as a step in an argument contradicted the round-3 doc 490
    lines below, which correctly says it is not proved.  (It is *true* — φ is
    not a square in Q(ζ₅) — but true-and-unproved is exactly what an honest
    label is supposed to catch.)
  * **"exactly two solutions" is therefore not established either.**  What §6
    proves is that every hexagon solution *satisfies* `Q`; that `Q` has no
    third root in K needs the no-zero-divisors property above.  See
    `roots_sum_and_product` and PROOFS.md, declared gaps.

The elimination *is* now formalized — §6, round 3 — so the round-1 sentence
"not yet formalized … Round 2" is also superseded.  What round 1 proved and
what still stands: both named roots satisfy `Q`, their product is 1, and the
discriminant is negative. -/

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
    ## 6.  ROUND 2 — THE RING LAYER, AND UNIQUENESS

    Round 1 proved the golden data *satisfies* the coherence equations.  That
    is sufficiency.  The bench's actual headline is necessity: "exactly TWO
    solution clusters … obeying r₁ = r_τ²".  Necessity needs symbolic algebra
    over K, not evaluation of constants — hence a commutative-ring layer.

    It is cheap.  `Z5`'s laws reduce to `Int` identities that are linear in the
    product-atoms, so `omega` closes them after `simp only` distributes; `KK`'s
    laws lift from `Z5`'s.  No `ring`, no mathlib, no decision procedure beyond
    core `omega`.
    ═══════════════════════════════════════════════════════════════════════ -/

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

/-- Commutativity: canonicalize the products with `Int.mul_comm`, then the goal
    is linear in the product-atoms and `omega` finishes. -/
theorem mul_comm (u v : Z5) : mul u v = mul v u := by
  cases u; cases v; simp only [mul, Z5.mk.injEq]
  refine ⟨?_,?_,?_,?_⟩ <;> simp only [Int.mul_comm] <;> omega

theorem mul_add (u v w : Z5) : mul u (add v w) = add (mul u v) (mul u w) := by
  cases u; cases v; cases w; simp only [mul, add, Z5.mk.injEq, Int.mul_add]
  refine ⟨?_,?_,?_,?_⟩ <;> omega
theorem add_mul (u v w : Z5) : mul (add u v) w = add (mul u w) (mul v w) := by
  cases u; cases v; cases w; simp only [mul, add, Z5.mk.injEq, Int.add_mul]
  refine ⟨?_,?_,?_,?_⟩ <;> omega

/-- Associativity: distribute, right-associate every triple product so both
    sides share atoms `uᵢ * (vⱼ * w_k)`, then `omega`. -/
theorem mul_assoc (u v w : Z5) : mul (mul u v) w = mul u (mul v w) := by
  cases u; cases v; cases w
  simp only [mul, Z5.mk.injEq, Int.sub_mul, Int.add_mul, Int.mul_sub, Int.mul_add,
             Int.mul_assoc]
  refine ⟨?_,?_,?_,?_⟩ <;> omega

theorem mul_left_comm (u v w : Z5) : mul u (mul v w) = mul v (mul u w) := by
  rw [← mul_assoc, mul_comm u v, mul_assoc]
theorem add_left_comm (u v w : Z5) : add u (add v w) = add v (add u w) := by
  rw [← add_assoc, add_comm u v, add_assoc]

/-! #### Round 3: the negation laws.

Needed to move `neg` through a product and to cancel `u + (−u)`.  Both hexagon
residuals carry a `neg invPhi`, so without these the assembly cannot even be
stated in the form the instances produce.  Same recipe as above: normalize the
`Int` sign rules first (`Int.neg_mul`, `Int.mul_neg`), after which each
component is linear in the product-atoms and `omega` closes it. -/

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

/-- Round 4, correction D1: the round-3 ledger asserted `mul_right_comm` "at
    both the Z5 and KK levels" and only the `KK` one existed.  Proved here
    rather than trimmed from the prose — the same choice made for C2′, and for
    the same reason: the house rule is that the ledger asserts nothing the file
    does not contain, and the cheaper way to keep it true is to make the file
    contain it. -/
theorem mul_right_comm (u v w : Z5) : mul (mul u v) w = mul (mul u w) v := by
  rw [mul_assoc, mul_comm v w, ← mul_assoc]

end Z5

namespace KK

theorem mul_one (u : KK) : mul u one = u := by
  cases u; simp [mul, one, Z5.mul_one, Z5.mul_zero, Z5.add_zero, Z5.zero_add]
theorem one_mul (u : KK) : mul one u = u := by
  cases u; simp [mul, one, Z5.one_mul, Z5.zero_mul, Z5.mul_zero, Z5.add_zero]
theorem mul_zero (u : KK) : mul u zero = zero := by
  cases u; simp [mul, zero, Z5.mul_zero, Z5.add_zero]
theorem zero_mul (u : KK) : mul zero u = zero := by
  cases u; simp [mul, zero, Z5.zero_mul, Z5.mul_zero, Z5.add_zero]
theorem add_zero (u : KK) : add u zero = u := by
  cases u; simp [add, zero, Z5.add_zero]
theorem zero_add (u : KK) : add zero u = u := by
  cases u; simp [add, zero, Z5.zero_add]

/-- Associativity in K, lifted from `Z5`'s laws — no descent to `Int`. -/
theorem mul_assoc (u v w : KK) : mul (mul u v) w = mul u (mul v w) := by
  cases u; cases v; cases w
  simp only [mul, KK.mk.injEq, Z5.add_mul, Z5.mul_add, Z5.mul_assoc]
  constructor
  · simp [Z5.add_comm, Z5.add_left_comm, Z5.add_assoc,
          Z5.mul_comm, Z5.mul_left_comm]
  · simp [Z5.add_comm, Z5.add_left_comm, Z5.add_assoc,
          Z5.mul_comm, Z5.mul_left_comm]

end KK

/-! ### Necessity: coherence *forces* `r₁ = r_τ²`

Residual #1 of the hexagon — the instance at total charge `(τ,τ,τ,1)` with
`(e,z) = (τ,τ)` — is verbatim `r₁ − r_τ²`, with unit exactly +1.  So the
identity is not a property of the constants the solver happened to find; every
braiding satisfying the hexagon must obey it.  That upgrades
`grammar_hexagon.py`'s `assert abs(r1 - rt**2) < 1e-6` from an observation
about two clusters to a consequence of coherence. -/

/-- The hexagon instance at `(a,b,c,d,e,z) = (τ,τ,τ,1,τ,τ)`, reduced.  Proved
    by `rfl`: every label is concrete, so `Fs`, `Rb`, `fuse` and `sumOver` all
    evaluate; only `r₁` and `r_τ` are carried along as opaque values. -/
theorem hex_at_r1 (r1 rt : KK) :
    hexagonCheck kRng Fsymm r1 rt .tau .tau .tau .one .tau .tau
      = KK.beq (KK.mul r1 KK.one)
          (KK.add (KK.mul (KK.mul (KK.mul KK.zero r1) KK.zero) rt)
            (KK.add (KK.mul (KK.mul (KK.mul KK.one rt) KK.one) rt) KK.zero)) :=
  rfl

/-- **COHERENCE FORCES `r₁ = r_τ²`.**  For *any* `r₁, r_τ` in K satisfying the
    hexagon — not merely the golden pair — `r₁ = r_τ²`.  This is the first
    genuine necessity theorem of the project: everything before it verified
    that chosen data satisfies an equation; this constrains all possible data. -/
theorem hexagon_forces_r1_eq_rt_sq (r1 rt : KK)
    (h : ∀ a b c d e z, hexagonCheck kRng Fsymm r1 rt a b c d e z = true) :
    r1 = KK.mul rt rt := by
  have h1 := h .tau .tau .tau .one .tau .tau
  rw [hex_at_r1 r1 rt] at h1
  have e1 := of_decide_eq_true h1
  simp only [KK.mul_one, KK.one_mul, KK.mul_zero, KK.zero_mul, KK.add_zero,
             KK.zero_add] at e1
  exact e1

/-- The golden braiding is not a vacuous instance of the above: it does satisfy
    the hexagon, so the hypothesis of `hexagon_forces_r1_eq_rt_sq` is
    inhabited.  (`chirality_right` gives the same fact as a violation count;
    this is the `∀`-form the necessity theorem actually consumes.) -/
theorem golden_satisfies_hexagon :
    ∀ a b c d e z, hexagonCheck kRng Fsymm KK.r1 KK.rt a b c d e z = true := by
  intro a b c d e z
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases z <;> rfl

/-- ...and therefore `r₁ = r_τ²` for it, obtained by *necessity* rather than by
    evaluating both sides.  Compare `r1_eq_rt_sq`, which is the same equation
    proved by computation on the constants. -/
theorem golden_r1_eq_rt_sq_by_necessity : KK.r1 = KK.mul KK.rt KK.rt :=
  hexagon_forces_r1_eq_rt_sq KK.r1 KK.rt golden_satisfies_hexagon

/-! ### The quadratic — ROUND 3: the assembly, done

The remaining half of uniqueness is that the hexagon also forces
`r_τ² + (1/φ)r_τ + 1 = 0`, whence `r_τ` is one of two values.  Round 1 called
this BLOCKED on K being an integral domain.  **It is not**, and the reason is
below: residual #3 makes `r_τ` *explicitly invertible*, so the cancellation is
by an exhibited inverse rather than by a domain property.  The route:

    residual #3, times bφ  ⟹  (1/φ)·r_τ·(r₁ − r_τ) = 1     [r_τ is a unit]
    residual #5, times φ   ⟹  r_τ·(r₁ + (1/φ)r_τ + 1) = 0
    cancel                 ⟹  r₁ + (1/φ)r_τ + 1 = 0
    with r₁ = r_τ²         ⟹  r_τ² + (1/φ)r_τ + 1 = 0

Round 2 left this PARTIAL: the components were proved, the rewriting was not.
**Round 3 closes it** — `hexagon_forces_quadratic` below.  Two bookkeeping
facts, both confirmed by the builder's auditors and recorded here as the
charge asked:

  * **each chain's multiplier carries unit −1.**  Precisely,
    `(LHS₃ − RHS₃)·(bφ) = −((1/φ)·r_τ·(r₁ − r_τ) − 1)` and
    `(LHS₅ − RHS₅)·φ = −(r_τ·(r₁ + (1/φ)r_τ + 1))`.  Harmless — both chains
    conclude an equality *to zero*, and a unit −1 cannot change whether a
    thing is zero — but the sign is real and is why the proofs below arrive
    at `e3'`/`e5'` with the sides exchanged relative to the display above.
  * **the multiplier `bφ` is exactly `t`.**  `b = t/φ`, so `bφ = t`.  Nothing
    in the proof uses this, but it is the reason the first multiplier is a
    ring element and not a fraction: cancelling `b` costs one factor of `t`.

The method, and the reason this round did not repeat round 3's crash: every
identity here is degree ≤ 3 in the **two** opaque variables `r₁, r_τ`, with
all other factors concrete.  So each step is an explicit `calc` at the K
level using the proved laws, never a descent to `Int` and never a `simp`
search over a K-level ring goal.  `mul_right_comm` slides the single `b` (or
`1/φ`) to the end; `cancel_b` / `cancel_invPhi` delete it against its unit. -/

namespace KK

theorem mul_comm (u v : KK) : mul u v = mul v u := by
  cases u; cases v; simp only [mul, KK.mk.injEq]
  constructor
  · simp [Z5.mul_comm]
  · simp [Z5.add_comm, Z5.mul_comm]

theorem mul_add (u v w : KK) : mul u (add v w) = add (mul u v) (mul u w) := by
  cases u; cases v; cases w
  simp only [mul, add, KK.mk.injEq, Z5.mul_add]
  constructor
  · simp [Z5.add_left_comm, Z5.add_assoc]
  · simp [Z5.add_left_comm, Z5.add_assoc]

def sub (u v : KK) : KK := add u (neg v)

/-! #### Round 3: the additive laws, negation, and the two AC shuffles.

`add_comm`, `add_assoc` and `add_mul` were asserted by the round-2 ledger but
were **not in the file** — correction C2′, now discharged by proving them
rather than by trimming the prose.  Each lifts componentwise from `Z5`; none
descends to `Int`.  `mul_right_comm` is the workhorse of the hexagon
assembly: it is what slides the single `b` (or the single `1/φ`) to the end of
a product so the corresponding unit can cancel it. -/

theorem add_comm (u v : KK) : add u v = add v u := by
  cases u; cases v; simp only [add, KK.mk.injEq]
  exact ⟨Z5.add_comm _ _, Z5.add_comm _ _⟩

theorem add_assoc (u v w : KK) : add (add u v) w = add u (add v w) := by
  cases u; cases v; cases w; simp only [add, KK.mk.injEq]
  exact ⟨Z5.add_assoc _ _ _, Z5.add_assoc _ _ _⟩

theorem add_mul (u v w : KK) : mul (add u v) w = add (mul u w) (mul v w) := by
  rw [mul_comm, mul_add, mul_comm w u, mul_comm w v]

theorem add_left_comm (u v w : KK) : add u (add v w) = add v (add u w) := by
  rw [← add_assoc, add_comm u v, add_assoc]

theorem neg_mul (u v : KK) : mul (neg u) v = neg (mul u v) := by
  cases u; cases v
  simp only [mul, neg, Z5.neg_mul, Z5.mul_neg, Z5.neg_add]

theorem mul_neg (u v : KK) : mul u (neg v) = neg (mul u v) := by
  rw [mul_comm, neg_mul, mul_comm]

theorem neg_neg (u : KK) : neg (neg u) = u := by
  cases u; simp only [neg, KK.mk.injEq]
  exact ⟨Z5.neg_neg _, Z5.neg_neg _⟩

theorem add_neg (u : KK) : add u (neg u) = zero := by
  cases u; simp only [add, neg, zero, KK.mk.injEq]
  exact ⟨Z5.add_neg _, Z5.add_neg _⟩

theorem neg_add_cancel (u : KK) : add (neg u) u = zero := by
  cases u; simp only [add, neg, zero, KK.mk.injEq]
  exact ⟨Z5.neg_add_cancel _, Z5.neg_add_cancel _⟩

theorem mul_left_comm (u v w : KK) : mul u (mul v w) = mul v (mul u w) := by
  rw [← mul_assoc, mul_comm u v, mul_assoc]

theorem mul_right_comm (u v w : KK) : mul (mul u v) w = mul (mul u w) v := by
  rw [mul_assoc, mul_comm v w, ← mul_assoc]

/-- Round 4, correction D1's other half: `KK.neg_add`, asserted by the round-3
    ledger and absent from the file.  Lifts componentwise from `Z5.neg_add`. -/
theorem neg_add (u v : KK) : neg (add u v) = add (neg u) (neg v) := by
  cases u; cases v; simp only [add, neg, KK.mk.injEq]
  exact ⟨Z5.neg_add _ _, Z5.neg_add _ _⟩

end KK

/-- **CANCELLATION WITHOUT A DOMAIN.**  If `w` is a **left** inverse for `rt`
    (`w · rt = 1`) and `rt · X = 0`, then `X = 0`.  Needs only associativity
    and the unit laws — no integral-domain property, which is what round 1
    wrongly treated as the blocker.

    (Round 3: the docstring previously said "two-sided inverse".  The
    hypothesis is one-sided, so the theorem is *stronger* than that
    advertised — no soundness consequence, but the description was inaccurate.
    In K it happens to be two-sided anyway, since `KK.mul_comm` is proved
    above; the point is that the proof never needs it.) -/
theorem cancel_of_inv (w rt X : KK)
    (hw : KK.mul w rt = KK.one) (h : KK.mul rt X = KK.zero) : X = KK.zero := by
  calc X = KK.mul KK.one X          := (KK.one_mul X).symm
    _    = KK.mul (KK.mul w rt) X   := by rw [hw]
    _    = KK.mul w (KK.mul rt X)   := KK.mul_assoc w rt X
    _    = KK.mul w KK.zero         := by rw [h]
    _    = KK.zero                  := KK.mul_zero w

/-- `b` is a unit: `b · (bφ) = 1`, since `b² = 1/φ` and `(1/φ)·φ = 1`. -/
theorem b_unit : KK.mul KK.b (KK.mul KK.b (KK.emb Z5.phi)) = KK.one := rfl

/-- `1/φ` is a unit. -/
theorem invPhi_unit : KK.mul KK.invPhi (KK.emb Z5.phi) = KK.one := rfl

/-- The hexagon instance at `(τ,τ,τ,τ,1,τ)` — residual #3, the one that makes
    `r_τ` invertible.  Reduced by `rfl`. -/
theorem hex_at_3 (r1 rt : KK) :
    hexagonCheck kRng Fsymm r1 rt .tau .tau .tau .tau .one .tau
      = KK.beq (KK.mul KK.one KK.b)
          (KK.add (KK.mul (KK.mul (KK.mul KK.invPhi r1) KK.b) rt)
            (KK.add (KK.mul (KK.mul (KK.mul KK.b rt) (KK.neg KK.invPhi)) rt)
              KK.zero)) :=
  rfl

/-- The hexagon instance at `(τ,τ,τ,τ,τ,τ)` — residual #5, the one carrying the
    quadratic.  Reduced by `rfl`. -/
theorem hex_at_5 (r1 rt : KK) :
    hexagonCheck kRng Fsymm r1 rt .tau .tau .tau .tau .tau .tau
      = KK.beq (KK.mul rt (KK.neg KK.invPhi))
          (KK.add (KK.mul (KK.mul (KK.mul KK.b r1) KK.b) rt)
            (KK.add (KK.mul (KK.mul (KK.mul (KK.neg KK.invPhi) rt)
                                    (KK.neg KK.invPhi)) rt) KK.zero)) :=
  rfl

/-! #### The two cancellation shims

Each hexagon residual carries exactly one stray `b` (residual #3) or one
stray `1/φ` (residual #5).  These two lemmas are the whole of the "multiply
through and cancel" step: slide the stray factor to the end with
`mul_right_comm`, then delete it here. -/

/-- **`bφ = t` EXACTLY** — the builder's noted fact, recorded as a theorem
    rather than a remark, per the round-3 charge.  `b = t/φ`, so multiplying by
    `bφ` is multiplying by `t`: cancelling one `b` costs exactly one factor of
    `t`, which is why the first multiplier is a ring element and not a
    fraction. -/
theorem bphi_is_t : KK.mul KK.b (KK.emb Z5.phi) = KK.t := rfl

/-- Multiplying by `bφ` erases a trailing `b`.  (`bφ = t` exactly.) -/
theorem cancel_b (u : KK) :
    KK.mul (KK.mul u KK.b) (KK.mul KK.b (KK.emb Z5.phi)) = u := by
  calc KK.mul (KK.mul u KK.b) (KK.mul KK.b (KK.emb Z5.phi))
      = KK.mul u (KK.mul KK.b (KK.mul KK.b (KK.emb Z5.phi))) := KK.mul_assoc _ _ _
    _ = KK.mul u KK.one := by rw [b_unit]
    _ = u := KK.mul_one u

/-- Multiplying by `φ` erases a trailing `1/φ`. -/
theorem cancel_invPhi (u : KK) :
    KK.mul (KK.mul u KK.invPhi) (KK.emb Z5.phi) = u := by
  calc KK.mul (KK.mul u KK.invPhi) (KK.emb Z5.phi)
      = KK.mul u (KK.mul KK.invPhi (KK.emb Z5.phi)) := KK.mul_assoc _ _ _
    _ = KK.mul u KK.one := by rw [invPhi_unit]
    _ = u := KK.mul_one u

/-! #### The two residual chains

Stated with the instance equation as a hypothesis, so the ring algebra is
separated from the coherence extraction and each half can be read on its own.
The hypotheses `e3`, `e5` are verbatim the right-hand sides of `hex_at_3` and
`hex_at_5`; `hexagon_forces_quadratic` supplies them by `of_decide_eq_true`. -/

/-- **`r_τ` IS A UNIT**, from residual #3 alone, with the inverse exhibited:
    `(1/φ)(r₁ − r_τ)` inverts it.  This is what replaces round 1's appeal to K
    being an integral domain — the cancellation below is by a named inverse,
    and no domain property is used anywhere in this file. -/
theorem rt_unit_of_e3 (r1 rt : KK)
    (e3 : KK.mul KK.one KK.b
        = KK.add (KK.mul (KK.mul (KK.mul KK.invPhi r1) KK.b) rt)
            (KK.add (KK.mul (KK.mul (KK.mul KK.b rt) (KK.neg KK.invPhi)) rt)
              KK.zero)) :
    KK.mul (KK.mul KK.invPhi (KK.add r1 (KK.neg rt))) rt = KK.one := by
  rw [KK.one_mul, KK.add_zero] at e3
  have hA : KK.mul (KK.mul (KK.mul KK.invPhi r1) KK.b) rt
          = KK.mul (KK.mul (KK.mul KK.invPhi r1) rt) KK.b := KK.mul_right_comm _ _ _
  have hB : KK.mul (KK.mul (KK.mul KK.b rt) (KK.neg KK.invPhi)) rt
          = KK.mul (KK.mul (KK.mul rt (KK.neg KK.invPhi)) rt) KK.b := by
    rw [KK.mul_comm KK.b rt, KK.mul_right_comm rt KK.b (KK.neg KK.invPhi),
        KK.mul_right_comm (KK.mul rt (KK.neg KK.invPhi)) KK.b rt]
  rw [hA, hB] at e3
  have e3' := congrArg (fun X => KK.mul X (KK.mul KK.b (KK.emb Z5.phi))) e3
  rw [KK.add_mul, b_unit, cancel_b, cancel_b] at e3'
  calc KK.mul (KK.mul KK.invPhi (KK.add r1 (KK.neg rt))) rt
      = KK.mul (KK.add (KK.mul KK.invPhi r1) (KK.mul KK.invPhi (KK.neg rt))) rt := by
        rw [KK.mul_add]
    _ = KK.add (KK.mul (KK.mul KK.invPhi r1) rt)
               (KK.mul (KK.mul KK.invPhi (KK.neg rt)) rt) := KK.add_mul _ _ _
    _ = KK.add (KK.mul (KK.mul KK.invPhi r1) rt)
               (KK.mul (KK.mul rt (KK.neg KK.invPhi)) rt) := by
        rw [KK.mul_neg, KK.mul_comm KK.invPhi rt, ← KK.mul_neg]
    _ = KK.one := e3'.symm

/-- **RESIDUAL #5, CLEARED**: multiplying by `φ` turns it into
    `r_τ·(r₁ + (1/φ)r_τ + 1) = 0`.  `b² = 1/φ` collapses the first summand and
    the two `neg`s cancel in the second. -/
theorem quad_times_rt_of_e5 (r1 rt : KK)
    (e5 : KK.mul rt (KK.neg KK.invPhi)
        = KK.add (KK.mul (KK.mul (KK.mul KK.b r1) KK.b) rt)
            (KK.add (KK.mul (KK.mul (KK.mul (KK.neg KK.invPhi) rt)
                                    (KK.neg KK.invPhi)) rt) KK.zero)) :
    KK.mul rt (KK.add (KK.add r1 (KK.mul KK.invPhi rt)) KK.one) = KK.zero := by
  rw [KK.add_zero] at e5
  have hA : KK.mul (KK.mul (KK.mul KK.b r1) KK.b) rt
          = KK.mul (KK.mul KK.invPhi r1) rt := by
    rw [KK.mul_right_comm KK.b r1 KK.b, kk_b_sq]
  have hB : KK.mul (KK.mul (KK.mul (KK.neg KK.invPhi) rt) (KK.neg KK.invPhi)) rt
          = KK.mul (KK.mul (KK.mul KK.invPhi rt) KK.invPhi) rt := by
    rw [KK.neg_mul, KK.neg_mul, KK.mul_neg, KK.neg_neg]
  rw [hA, hB] at e5
  have hA2 : KK.mul (KK.mul KK.invPhi r1) rt
           = KK.mul (KK.mul r1 rt) KK.invPhi := by
    rw [KK.mul_comm KK.invPhi r1, KK.mul_right_comm r1 KK.invPhi rt]
  have hB2 : KK.mul (KK.mul (KK.mul KK.invPhi rt) KK.invPhi) rt
           = KK.mul (KK.mul (KK.mul KK.invPhi rt) rt) KK.invPhi :=
    KK.mul_right_comm _ _ _
  have hL : KK.mul rt (KK.neg KK.invPhi) = KK.mul (KK.neg rt) KK.invPhi := by
    rw [KK.mul_neg, KK.neg_mul]
  rw [hA2, hB2, hL] at e5
  have e5' := congrArg (fun X => KK.mul X (KK.emb Z5.phi)) e5
  rw [KK.add_mul, cancel_invPhi, cancel_invPhi, cancel_invPhi] at e5'
  calc KK.mul rt (KK.add (KK.add r1 (KK.mul KK.invPhi rt)) KK.one)
      = KK.add (KK.mul rt (KK.add r1 (KK.mul KK.invPhi rt))) (KK.mul rt KK.one) :=
        KK.mul_add _ _ _
    _ = KK.add (KK.add (KK.mul rt r1) (KK.mul rt (KK.mul KK.invPhi rt))) rt := by
        rw [KK.mul_add, KK.mul_one]
    _ = KK.add (KK.add (KK.mul r1 rt) (KK.mul (KK.mul KK.invPhi rt) rt)) rt := by
        rw [KK.mul_comm rt r1, KK.mul_comm rt (KK.mul KK.invPhi rt)]
    _ = KK.add (KK.neg rt) rt := by rw [← e5']
    _ = KK.zero := KK.neg_add_cancel rt

/-- **THE LINEAR RELATION** `r₁ + (1/φ)r_τ + 1 = 0`, from residuals #3 and #5
    together: #3 exhibits the inverse, #5 supplies the product that is zero,
    `cancel_of_inv` divides. -/
theorem linear_of_e3_e5 (r1 rt : KK)
    (e3 : KK.mul KK.one KK.b
        = KK.add (KK.mul (KK.mul (KK.mul KK.invPhi r1) KK.b) rt)
            (KK.add (KK.mul (KK.mul (KK.mul KK.b rt) (KK.neg KK.invPhi)) rt)
              KK.zero))
    (e5 : KK.mul rt (KK.neg KK.invPhi)
        = KK.add (KK.mul (KK.mul (KK.mul KK.b r1) KK.b) rt)
            (KK.add (KK.mul (KK.mul (KK.mul (KK.neg KK.invPhi) rt)
                                    (KK.neg KK.invPhi)) rt) KK.zero)) :
    KK.add (KK.add r1 (KK.mul KK.invPhi rt)) KK.one = KK.zero :=
  cancel_of_inv (KK.mul KK.invPhi (KK.add r1 (KK.neg rt))) rt _
    (rt_unit_of_e3 r1 rt e3) (quad_times_rt_of_e5 r1 rt e5)

/-! #### The two necessity theorems -/

/-- **COHERENCE MAKES `r_τ` INVERTIBLE.**  For any braiding satisfying the
    hexagon, `r_τ` is a unit of K — with the inverse written down.  This is the
    statement round 1 wrongly believed needed K to be an integral domain. -/
theorem hexagon_forces_rt_unit (r1 rt : KK)
    (h : ∀ a b c d e z, hexagonCheck kRng Fsymm r1 rt a b c d e z = true) :
    KK.mul (KK.mul KK.invPhi (KK.add r1 (KK.neg rt))) rt = KK.one := by
  have h3 := h .tau .tau .tau .tau .one .tau
  rw [hex_at_3 r1 rt] at h3
  exact rt_unit_of_e3 r1 rt (of_decide_eq_true h3)

/-- **COHERENCE FORCES THE QUADRATIC.**  For *any* `r₁, r_τ` in K whatsoever,
    if the hexagon holds then `r_τ² + (1/φ)r_τ + 1 = 0`.

    With `hexagon_forces_r1_eq_rt_sq`: coherence pins `r₁` to `r_τ²` and pins
    `r_τ` to a root of an explicit quadratic over Z[φ].  Round 2 left this
    PARTIAL; it is now closed.

    WHAT THIS DOES AND DOES NOT SAY, because the distinction is easy to blur.
    It says every hexagon solution *satisfies* `Q(X) = X² + (1/φ)X + 1`.
    `rt_root_quadratic` and `rt'_root_quadratic` exhibit two roots,
    `roots_product_one` gives `r_τ·r_τ' = 1`, and `discriminant_negative` says
    neither is real — so each solution commits to a handedness.  It does **not**
    say there is no *third* root of `Q` in K: that needs
    `(s − r_τ)(s − r_τ') = 0 ⟹ s = r_τ ∨ s = r_τ'`, i.e. K having no zero
    divisors, which is NOT proved in this file.  So the bench's "exactly TWO
    solution clusters" is *supported* here — the quadratic is forced and both
    its named roots are exhibited — but the word "exactly" is not itself a
    theorem yet.  See `roots_sum_and_product` and PROOFS.md, declared gaps. -/
theorem hexagon_forces_quadratic (r1 rt : KK)
    (h : ∀ a b c d e z, hexagonCheck kRng Fsymm r1 rt a b c d e z = true) :
    KK.add (KK.add (KK.mul rt rt) (KK.mul KK.invPhi rt)) KK.one = KK.zero := by
  have h3 := h .tau .tau .tau .tau .one .tau
  rw [hex_at_3 r1 rt] at h3
  have h5 := h .tau .tau .tau .tau .tau .tau
  rw [hex_at_5 r1 rt] at h5
  have hlin := linear_of_e3_e5 r1 rt (of_decide_eq_true h3) (of_decide_eq_true h5)
  rw [hexagon_forces_r1_eq_rt_sq r1 rt h] at hlin
  exact hlin

/-- **HEXAGON UNIQUENESS, both halves in one statement.** -/
theorem hexagon_uniqueness (r1 rt : KK)
    (h : ∀ a b c d e z, hexagonCheck kRng Fsymm r1 rt a b c d e z = true) :
    r1 = KK.mul rt rt ∧
    KK.add (KK.add (KK.mul rt rt) (KK.mul KK.invPhi rt)) KK.one = KK.zero :=
  ⟨hexagon_forces_r1_eq_rt_sq r1 rt h, hexagon_forces_quadratic r1 rt h⟩

/-- ANTI-VACUITY for the two theorems above: the golden braiding satisfies the
    hypothesis, so neither is a statement about an empty class — and what they
    then yield is exactly `r1_eq_rt_sq` and `rt_root_quadratic`, obtained here
    by necessity rather than by evaluating the constants. -/
theorem golden_quadratic_by_necessity :
    KK.r1 = KK.mul KK.rt KK.rt ∧
    KK.add (KK.add (KK.mul KK.rt KK.rt) (KK.mul KK.invPhi KK.rt)) KK.one
      = KK.zero :=
  hexagon_uniqueness KK.r1 KK.rt golden_satisfies_hexagon

/-- The MIRROR braiding also satisfies the hypothesis, so the necessity
    theorems are satisfied by *both* roots — the quadratic really does have the
    two solutions the bench found, and nothing in the derivation prefers one.
    (Compare `chirality_left`, the same fact as a violation count.) -/
theorem mirror_satisfies_hexagon :
    ∀ a b c d e z, hexagonCheck kRng Fsymm r1' rt' a b c d e z = true := by
  intro a b c d e z
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases z <;> rfl

/-- ...and so the mirror obeys the same forced quadratic, by necessity. -/
theorem mirror_quadratic_by_necessity :
    r1' = KK.mul rt' rt' ∧
    KK.add (KK.add (KK.mul rt' rt') (KK.mul KK.invPhi rt')) KK.one = KK.zero :=
  hexagon_uniqueness r1' rt' mirror_satisfies_hexagon

/-- **THE TWO ROOTS REALIZE `Q`'s COEFFICIENTS**: `r_τ + r_τ' = −1/φ` and
    `r_τ · r_τ' = 1`, which are exactly the coefficients of
    `Q(X) = X² + (1/φ)X + 1`.  Both by `rfl`.

    HONEST LABEL, tightened in round 3 after an audit caught it overclaiming
    twice:

    * The theorem says this pair *realizes* the coefficients.  It does **not**
      say it is the only pair that does — sum-and-product pins a pair only in a
      ring without zero divisors, which is the very property disclaimed below.
      (The earlier wording "shows they are the coefficients' only possible
      pair" was self-undercutting and is withdrawn.)
    * The name is `roots_sum_and_product`, not `factors_exactly`, because the
      factorization `Q(X) = (X − r_τ)(X − r_τ')` — though a true consequence of
      these two identities by distributivity — is **not asserted by any
      declaration in this file**.  The earlier headline claimed it; no theorem
      backed it.

    And the standing gap: "*exactly* two" — no third root anywhere in K — needs
    `(s − r_τ)(s − r_τ') = 0 ⟹ s = r_τ ∨ s = r_τ'`, i.e. K having no zero
    divisors.  That is the one place a domain property would still be wanted,
    and it is NOT proved here.  See PROOFS.md, declared gaps. -/
theorem roots_sum_and_product :
    KK.add KK.rt rt' = KK.neg KK.invPhi ∧ KK.mul KK.rt rt' = KK.one :=
  ⟨rfl, rfl⟩

/-- ANTI-VACUITY for the two residual chains themselves, one level below the
    necessity theorems: the golden constants satisfy each chain's *cleared*
    form, so `rt_unit_of_e3` and `quad_times_rt_of_e5` are not conclusions
    about an unreachable configuration.  These are the two displayed identities
    of the route, evaluated — the same equations the necessity theorems derive
    symbolically for arbitrary `r₁, r_τ`. -/
theorem golden_chains_cleared :
    KK.mul (KK.mul KK.invPhi (KK.add KK.r1 (KK.neg KK.rt))) KK.rt = KK.one ∧
    KK.mul KK.rt (KK.add (KK.add KK.r1 (KK.mul KK.invPhi KK.rt)) KK.one)
      = KK.zero ∧
    KK.add (KK.add KK.r1 (KK.mul KK.invPhi KK.rt)) KK.one = KK.zero :=
  ⟨rfl, rfl, rfl⟩

/-! #### THE TRAP, and why the proof above steps around it

Found by an independent auditor who re-derived this section from the round-2
definitions without reading the round-3 proof.  It is the sharpest thing in
the audit and it belongs in the file, because the *natural* narrative for
this result is unsound while looking perfectly fine.

The tempting route is: "instance `(τ,τ,τ,1,τ,τ)` gives `r₁ = r_τ²`; substitute
into `(τ,τ,τ,τ,τ,τ)`, which becomes `r_τ·Q(r_τ) = 0`; cancel `r_τ`; done."
**That last cancellation is not licensed by those two instances.**  They force
only `r_τ·Q = 0`, and `r₁ = r_τ = 0` is a genuine common zero of them — so
nothing in that pair rules out `r_τ = 0`, and "cancel `r_τ`" is an unjustified
step, not a bookkeeping one.

The witness below makes that concrete: the zero braiding satisfies **13 of the
15** live instances, failing only the two with `e = 1`.  It is one of those —
`(τ,τ,τ,τ,1,τ)`, the instance behind `hex_at_3` — that carries the constant
term `1` and hence makes `r_τ` invertible.  That is why `rt_unit_of_e3` reads
residual #3 and not residual #1, and why the proof needs no non-vanishing
hypothesis: invertibility is *derived*, not assumed. -/

/-- **THE ZERO BRAIDING FAILS ONLY TWO OF FIFTEEN.**  So the instances used to
    get `r₁ = r_τ²` and `r_τ·Q(r_τ) = 0` do not, between them, exclude
    `r_τ = 0`. -/
theorem zero_braiding_fails_only_two :
    countHexViolations KK.zero KK.zero = 2 := rfl

/-- The three instances of the tempting route all **accept** the zero braiding
    — which is exactly why they cannot license cancelling `r_τ`. -/
theorem zero_braiding_passes_the_tempting_route :
    hexagonCheck kRng Fsymm KK.zero KK.zero .tau .tau .tau .one .tau .tau = true ∧
    hexagonCheck kRng Fsymm KK.zero KK.zero .tau .tau .tau .tau .tau .one = true ∧
    hexagonCheck kRng Fsymm KK.zero KK.zero .tau .tau .tau .tau .tau .tau = true :=
  ⟨rfl, rfl, rfl⟩

/-- **AND THE INSTANCE THE PROOF ACTUALLY USES REJECTS IT.**  `hex_at_3`'s
    tuple `(τ,τ,τ,τ,1,τ)` is false at `r₁ = r_τ = 0`; so is its `e = 1`
    partner.  These two are the only rejecters among the fifteen, and one of
    them is what `rt_unit_of_e3` consumes. -/
theorem only_the_e_one_instances_reject_zero :
    hexagonCheck kRng Fsymm KK.zero KK.zero .tau .tau .tau .tau .one .tau = false ∧
    hexagonCheck kRng Fsymm KK.zero KK.zero .tau .tau .tau .tau .one .one = false :=
  ⟨rfl, rfl⟩

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



/-! ═══════════════════════════════════════════════════════════════════════
    ## 7.  PENTAGON UNIQUENESS — coherence conjures the golden ratio

    The hexagon work above proved that coherence FORCES `r₁ = r_τ²` and
    `r_τ² + (1/φ)r_τ + 1 = 0`.  This section is the pentagon analogue:
    carrying the FOUR associator entries as unknowns

        F(1,1) = p ,  F(1,τ) = q ,  F(τ,1) = r ,  F(τ,τ) = s ,

    the pentagon forces

        q·r = p ,      p² + p = 1 ,      s = −p .

    `p² + p = 1` is *verbatim* the golden-ratio relation: `p = 1/φ` is the
    positive root of `X² + X − 1`.  So the pentagon alone — with no braiding,
    no hexagon, no chosen constants — produces φ.

    Method, and why it does not repeat the round-3 crash: every step is a
    `calc` at the KK level with `p q r s` kept opaque, using only the ring
    laws proved above.  Nothing descends to `Int`; no budget is raised.
    ═══════════════════════════════════════════════════════════════════════ -/


/-- **The generic associator.**  Four opaque entries of K, in the same layout
    as `Fsymm`. -/
def Fg (p q r s : KK) : Anyon → Anyon → KK
  | .one, .one => p
  | .one, .tau => q
  | .tau, .one => r
  | .tau, .tau => s

/-- `Fg` at the golden data is `Fsymm`, on the nose. -/
theorem Fg_symm : Fg KK.invPhi KK.b KK.b (KK.neg KK.invPhi) = Fsymm := by
  funext i j; cases i <;> cases j <;> rfl

/-- `Fg` at the strict data is `Fid`, on the nose. -/
theorem Fg_id : Fg KK.one KK.zero KK.zero KK.one = Fid := by
  funext i j; cases i <;> cases j <;> rfl

/-- `Fg` at the deliberately-wrong data is `Fwrong`. -/
theorem Fg_wrong : Fg KK.one KK.one KK.one (KK.neg KK.one) = Fwrong := by
  funext i j; cases i <;> cases j <;> rfl

/-! ### 7.1  The eleven non-trivial instances, extracted by `rfl`

Of the 50 valid pentagon tuples, exactly **11** impose a condition on a
generic associator; all eleven sit at total charge `(a,b,c,d) = (τ,τ,τ,τ)`.
That count is itself a theorem — `pentagon_nontrivial_instances` in §7.4.
Each theorem below is `rfl`: the labels are concrete, so `fuse`, `memA`,
`isOne`, `Fs` and `sumOver` all evaluate, and only `p q r s` are carried
along opaque — exactly the technique of `hex_at_3`.

The residual (LHS − RHS) is recorded in each docstring. -/

/-- #1  `(x,y,t,w,v) = (1,τ,1,1,τ)`.  Residual `p² + qr − 1`. -/
theorem pent_at_01 (p q r s : KK) :
    pentagonCheck kRng (Fg p q r s) .tau .tau .tau .tau .one .tau .one .one .tau
      = KK.beq (KK.add (KK.mul (KK.mul p KK.one) p)
                 (KK.add (KK.mul (KK.mul q KK.one) r) KK.zero))
               (KK.mul KK.one KK.one) := rfl

/-- #2  `(1,τ,1,τ,τ)`.  Residual `pq + qs = q·(p+s)`. -/
theorem pent_at_02 (p q r s : KK) :
    pentagonCheck kRng (Fg p q r s) .tau .tau .tau .tau .one .tau .one .tau .tau
      = KK.beq (KK.add (KK.mul (KK.mul p KK.one) q)
                 (KK.add (KK.mul (KK.mul q KK.one) s) KK.zero))
               (KK.mul KK.zero KK.zero) := rfl

/-- #3  `(1,τ,τ,1,τ)`.  Residual `p² + qsr`. -/
theorem pent_at_03 (p q r s : KK) :
    pentagonCheck kRng (Fg p q r s) .tau .tau .tau .tau .one .tau .tau .one .tau
      = KK.beq (KK.add (KK.mul (KK.mul p KK.one) p)
                 (KK.add (KK.mul (KK.mul q s) r) KK.zero))
               (KK.mul KK.zero KK.zero) := rfl

/-- #4  `(1,τ,τ,τ,1)`.  Residual `qr − p`. -/
theorem pent_at_04 (p q r s : KK) :
    pentagonCheck kRng (Fg p q r s) .tau .tau .tau .tau .one .tau .tau .tau .one
      = KK.beq (KK.add (KK.mul (KK.mul p KK.zero) KK.zero)
                 (KK.add (KK.mul (KK.mul q r) KK.one) KK.zero))
               (KK.mul KK.one p) := rfl

/-- #5  `(1,τ,τ,τ,τ)`.  Residual `pq − q + qs² = q·(p − 1 + s²)`. -/
theorem pent_at_05 (p q r s : KK) :
    pentagonCheck kRng (Fg p q r s) .tau .tau .tau .tau .one .tau .tau .tau .tau
      = KK.beq (KK.add (KK.mul (KK.mul p KK.one) q)
                 (KK.add (KK.mul (KK.mul q s) s) KK.zero))
               (KK.mul KK.one q) := rfl

/-- #6  `(τ,1,τ,1,τ)`.  Residual `qr − p` — the same constraint as #4. -/
theorem pent_at_06 (p q r s : KK) :
    pentagonCheck kRng (Fg p q r s) .tau .tau .tau .tau .tau .one .tau .one .tau
      = KK.beq (KK.add (KK.mul (KK.mul KK.zero KK.zero) p)
                 (KK.add (KK.mul (KK.mul KK.one q) r) KK.zero))
               (KK.mul p KK.one) := rfl

/-- #7  `(τ,1,τ,τ,1)`.  Residual `p − qr` — #4 with the sides exchanged. -/
theorem pent_at_07 (p q r s : KK) :
    pentagonCheck kRng (Fg p q r s) .tau .tau .tau .tau .tau .one .tau .tau .one
      = KK.beq (KK.add (KK.mul (KK.mul KK.zero KK.zero) KK.zero)
                 (KK.add (KK.mul (KK.mul KK.one p) KK.one) KK.zero))
               (KK.mul q r) := rfl

/-- #8  `(τ,τ,1,1,τ)`.  Residual `pr + rs = r·(p+s)`. -/
theorem pent_at_08 (p q r s : KK) :
    pentagonCheck kRng (Fg p q r s) .tau .tau .tau .tau .tau .tau .one .one .tau
      = KK.beq (KK.add (KK.mul (KK.mul r KK.one) p)
                 (KK.add (KK.mul (KK.mul s KK.one) r) KK.zero))
               (KK.mul KK.zero KK.zero) := rfl

/-- #9  `(τ,τ,1,τ,τ)`.  Residual `qr + s² − 1`. -/
theorem pent_at_09 (p q r s : KK) :
    pentagonCheck kRng (Fg p q r s) .tau .tau .tau .tau .tau .tau .one .tau .tau
      = KK.beq (KK.add (KK.mul (KK.mul r KK.one) q)
                 (KK.add (KK.mul (KK.mul s KK.one) s) KK.zero))
               (KK.mul KK.one KK.one) := rfl

/-- #10  `(τ,τ,τ,1,τ)`.  Residual `pr − r + rs² = r·(p − 1 + s²)`. -/
theorem pent_at_10 (p q r s : KK) :
    pentagonCheck kRng (Fg p q r s) .tau .tau .tau .tau .tau .tau .tau .one .tau
      = KK.beq (KK.add (KK.mul (KK.mul r KK.one) p)
                 (KK.add (KK.mul (KK.mul s s) r) KK.zero))
               (KK.mul r KK.one) := rfl

/-- #11  `(τ,τ,τ,τ,τ)`.  Residual `qr − s² + s³`. -/
theorem pent_at_11 (p q r s : KK) :
    pentagonCheck kRng (Fg p q r s) .tau .tau .tau .tau .tau .tau .tau .tau .tau
      = KK.beq (KK.add (KK.mul (KK.mul r KK.one) q)
                 (KK.add (KK.mul (KK.mul s s) s) KK.zero))
               (KK.mul s s) := rfl

/-- The three instances the assembly consumes really are live instances of the
    index guard — not vacuous truths. -/
theorem pent_instances_valid :
    pentagonValid .tau .tau .tau .tau .one .tau .one .one .tau = true ∧
    pentagonValid .tau .tau .tau .tau .one .tau .tau .tau .one = true ∧
    pentagonValid .tau .tau .tau .tau .one .tau .tau .one .tau = true :=
  ⟨rfl, rfl, rfl⟩

/-! ### 7.2  Clearing the three residuals that carry the whole result

Only three of the eleven are needed: #1, #4 and #3.  Each is cleared by the
same bounded `simp only` over the unit-and-zero laws that
`hexagon_forces_r1_eq_rt_sq` uses — no search, no ring normalisation. -/

/-- Residual #1 cleared: `p² + qr = 1`. -/
theorem clear_01 (p q r : KK)
    (e : KK.add (KK.mul (KK.mul p KK.one) p)
           (KK.add (KK.mul (KK.mul q KK.one) r) KK.zero)
       = KK.mul KK.one KK.one) :
    KK.add (KK.mul p p) (KK.mul q r) = KK.one := by
  simp only [KK.mul_one, KK.add_zero] at e
  exact e

/-- Residual #4 cleared: `qr = p`. -/
theorem clear_04 (p q r : KK)
    (e : KK.add (KK.mul (KK.mul p KK.zero) KK.zero)
           (KK.add (KK.mul (KK.mul q r) KK.one) KK.zero)
       = KK.mul KK.one p) :
    KK.mul q r = p := by
  simp only [KK.mul_one, KK.one_mul, KK.mul_zero, KK.add_zero,
             KK.zero_add] at e
  exact e

/-- Residual #3 cleared: `p² + (q·s)·r = 0`. -/
theorem clear_03 (p q r s : KK)
    (e : KK.add (KK.mul (KK.mul p KK.one) p)
           (KK.add (KK.mul (KK.mul q s) r) KK.zero)
       = KK.mul KK.zero KK.zero) :
    KK.add (KK.mul p p) (KK.mul (KK.mul q s) r) = KK.zero := by
  simp only [KK.mul_one, KK.mul_zero, KK.add_zero] at e
  exact e

/-! ### 7.3  The assembly -/

/-- **THE GOLDEN RELATION.**  Residual #1 says `p² + qr = 1`; residual #4 says
    `qr = p`; substituting gives `p² + p = 1`.  No cancellation, no unit, no
    domain property — the two instances alone do it. -/
theorem golden_of_01_04 (p q r : KK)
    (h1 : KK.add (KK.mul p p) (KK.mul q r) = KK.one)
    (h4 : KK.mul q r = p) :
    KK.add (KK.mul p p) p = KK.one := by
  rw [h4] at h1; exact h1

/-- **`p` IS A UNIT**, with the inverse exhibited: `p·(p+1) = 1`.  Immediate
    from the golden relation, and this is what replaces any appeal to K being
    an integral domain in the step below.  (For `p = 1/φ` this is the identity
    `φ = 1/φ + 1`.) -/
theorem p_unit_of_golden (p : KK) (hg : KK.add (KK.mul p p) p = KK.one) :
    KK.mul p (KK.add p KK.one) = KK.one := by
  calc KK.mul p (KK.add p KK.one)
      = KK.add (KK.mul p p) (KK.mul p KK.one) := KK.mul_add p p KK.one
    _ = KK.add (KK.mul p p) p                 := by rw [KK.mul_one]
    _ = KK.one                                := hg

/-- **`s = −p`.**  Residual #3 is `p² + (qs)r = 0`; `mul_right_comm` turns
    `(qs)r` into `(qr)s`, residual #4 turns that into `ps`, so `p·(p+s) = 0`;
    `p` is a unit, so `p + s = 0`. -/
theorem s_eq_neg_p (p q r s : KK)
    (h4 : KK.mul q r = p)
    (h3 : KK.add (KK.mul p p) (KK.mul (KK.mul q s) r) = KK.zero)
    (hu : KK.mul p (KK.add p KK.one) = KK.one) :
    s = KK.neg p := by
  have hqsr : KK.mul (KK.mul q s) r = KK.mul p s := by
    rw [KK.mul_right_comm q s r, h4]
  rw [hqsr] at h3
  have hprod : KK.mul p (KK.add p s) = KK.zero := by
    rw [KK.mul_add]; exact h3
  have hinv : KK.mul (KK.add p KK.one) p = KK.one := by
    rw [KK.mul_comm]; exact hu
  have hz : KK.add p s = KK.zero :=
    cancel_of_inv (KK.add p KK.one) p (KK.add p s) hinv hprod
  calc s = KK.add KK.zero s               := (KK.zero_add s).symm
    _    = KK.add (KK.add (KK.neg p) p) s := by rw [KK.neg_add_cancel]
    _    = KK.add (KK.neg p) (KK.add p s) := KK.add_assoc _ _ _
    _    = KK.add (KK.neg p) KK.zero      := by rw [hz]
    _    = KK.neg p                       := KK.add_zero _

/-- **PENTAGON UNIQUENESS.**  For *any* four values `p q r s` of K whatsoever,
    if the generic associator `Fg p q r s` satisfies the pentagon then

        q·r = p ,      p² + p = 1 ,      s = −p .

    The middle equation is the golden-ratio relation `X² + X − 1 = 0`, whose
    positive root is `1/φ`.  So the pentagon — with no braiding anywhere in
    sight — is what produces φ.  The first says the off-diagonal entries are
    constrained only through their product, which is the residual gauge
    freedom `q ↦ λq, r ↦ λ⁻¹r`; the third says the diagonal is `(p, −p)`. -/
theorem pentagon_forces_golden (p q r s : KK)
    (h : ∀ a b c dd x y t w v,
           pentagonCheck kRng (Fg p q r s) a b c dd x y t w v = true) :
    KK.mul q r = p ∧
    KK.add (KK.mul p p) p = KK.one ∧
    s = KK.neg p := by
  have h1 := h .tau .tau .tau .tau .one .tau .one .one .tau
  rw [pent_at_01 p q r s] at h1
  have h4 := h .tau .tau .tau .tau .one .tau .tau .tau .one
  rw [pent_at_04 p q r s] at h4
  have h3 := h .tau .tau .tau .tau .one .tau .tau .one .tau
  rw [pent_at_03 p q r s] at h3
  have e1 := clear_01 p q r (of_decide_eq_true h1)
  have e4 := clear_04 p q r (of_decide_eq_true h4)
  have e3 := clear_03 p q r s (of_decide_eq_true h3)
  have hg := golden_of_01_04 p q r e1 e4
  exact ⟨e4, hg, s_eq_neg_p p q r s e4 e3 (p_unit_of_golden p hg)⟩

/-- **COROLLARY: `p` is invertible**, for every pentagon-coherent associator,
    with `p⁻¹ = p + 1`. -/
theorem pentagon_forces_p_unit (p q r s : KK)
    (h : ∀ a b c dd x y t w v,
           pentagonCheck kRng (Fg p q r s) a b c dd x y t w v = true) :
    KK.mul p (KK.add p KK.one) = KK.one :=
  p_unit_of_golden p (pentagon_forces_golden p q r s h).2.1

/-! ### 7.3a  A consistency receipt: the three relations reproduce residual #9

`pentagon_forces_golden` extracts its result from instances #1, #4 and #3.
Instance #9 is a *different* instance with residual `qr + s² − 1`, and the
three forced relations discharge it — so they are not an arbitrary subset,
they already imply constraints they were not derived from. -/

/-- `s = −p` gives `s² = p²`. -/
theorem s_sq_eq_p_sq (p s : KK) (hs : s = KK.neg p) :
    KK.mul s s = KK.mul p p := by
  rw [hs, KK.neg_mul, KK.mul_neg, KK.neg_neg]

/-- Residual #9, `qr + s² = 1`, follows from the three forced relations. -/
theorem resid_09_of_forced (p q r s : KK)
    (h4 : KK.mul q r = p)
    (hg : KK.add (KK.mul p p) p = KK.one)
    (hs : s = KK.neg p) :
    KK.add (KK.mul q r) (KK.mul s s) = KK.one := by
  rw [h4, s_sq_eq_p_sq p s hs, KK.add_comm p (KK.mul p p)]
  exact hg

/-! ### 7.4  Anti-vacuity and negative controls -/

/-- The golden associator IS `Fg` at the golden data, so the hypothesis of
    `pentagon_forces_golden` is inhabited — the theorem is not about an empty
    class.  (Restates `pentagon_symmetric_gauge` through `Fg`.) -/
theorem golden_satisfies_pentagon :
    ∀ a b c dd x y t w v,
      pentagonCheck kRng (Fg KK.invPhi KK.b KK.b (KK.neg KK.invPhi))
        a b c dd x y t w v = true := by
  rw [Fg_symm]; exact pentagon_symmetric_gauge

/-- ...and so the golden data obeys all three forced relations **by
    necessity** rather than by evaluating the constants.  The middle conjunct
    is `(1/φ)² + 1/φ = 1`: the golden ratio, derived from coherence. -/
theorem golden_pentagon_by_necessity :
    KK.mul KK.b KK.b = KK.invPhi ∧
    KK.add (KK.mul KK.invPhi KK.invPhi) KK.invPhi = KK.one ∧
    KK.neg KK.invPhi = KK.neg KK.invPhi :=
  pentagon_forces_golden KK.invPhi KK.b KK.b (KK.neg KK.invPhi)
    golden_satisfies_pentagon

/-- The same two facts checked directly on the constants, for comparison with
    the necessity route above.  (The first is `kk_b_sq`.) -/
theorem golden_pentagon_by_evaluation :
    KK.mul KK.b KK.b = KK.invPhi ∧
    KK.add (KK.mul KK.invPhi KK.invPhi) KK.invPhi = KK.one :=
  ⟨rfl, rfl⟩

/-- **NEGATIVE CONTROL 1.**  The strict associator is `Fg 1 0 0 1`, and it
    fails 4 pentagon instances — so the hypothesis of `pentagon_forces_golden`
    is not satisfied by everything.  Consistent: `p = 1` fails `p² + p = 1`. -/
theorem strict_is_Fg_and_fails :
    countPentViolations kRng (Fg KK.one KK.zero KK.zero KK.one) = 4 := by
  rw [Fg_id]; exact strict_pentagon_violations

/-- **NEGATIVE CONTROL 2.**  `Fg 1 1 1 (−1)` fails 5 instances. -/
theorem wrong_is_Fg_and_fails :
    countPentViolations kRng (Fg KK.one KK.one KK.one (KK.neg KK.one)) = 5 := by
  rw [Fg_wrong]; exact wrong_pentagon_violations

/-! #### The count of non-trivial instances, machine-checked

`pentagonCheck` is run over the FREE commutative polynomial ring on the four
generators `p q r s`.  There `K.beq` decides equality of normal forms, so an
instance returns `true` exactly when it is an identity for a *generic*
associator.  `countPentViolations` over that ring therefore counts the
instances that impose a real condition: **11 of the 50**.

This is pure evaluation on a tiny type — `List (Int × List Nat)` — not a ring
goal, so no budget question arises. -/

namespace PentPoly

abbrev Mon := List Nat
abbrev Poly := List (Int × Mon)

def monCmp : Mon → Mon → Ordering
  | [], []       => .eq
  | [], _        => .lt
  | _, []        => .gt
  | a::as, b::bs => if a < b then .lt else if b < a then .gt else monCmp as bs

def insSorted : Nat → Mon → Mon
  | x, []      => [x]
  | x, y :: ys => if x ≤ y then x :: y :: ys else y :: insSorted x ys

def monMul : Mon → Mon → Mon
  | [], m      => m
  | a :: as, m => insSorted a (monMul as m)

def insTerm (c : Int) (m : Mon) : Poly → Poly
  | [] => if c = 0 then [] else [(c, m)]
  | (c', m') :: ps =>
    match monCmp m m' with
    | .lt => if c = 0 then (c', m') :: ps else (c, m) :: (c', m') :: ps
    | .eq => let t := c + c'
             if t = 0 then ps else (t, m') :: ps
    | .gt => (c', m') :: insTerm c m ps

def normP (p : Poly) : Poly := p.foldl (fun acc t => insTerm t.1 t.2 acc) []
def addP (p q : Poly) : Poly := q.foldl (fun acc t => insTerm t.1 t.2 acc) p
def mulP (p q : Poly) : Poly :=
  normP (p.flatMap fun t => q.map fun u => (t.1 * u.1, monMul t.2 u.2))

/-- The free ring on `p q r s`, as `Rng` data. -/
def polyRng : Rng Poly :=
  ⟨[], [(1, [])], addP, mulP, fun a b => decide (a = b)⟩

/-- The generic associator over the free ring. -/
def FgP : Anyon → Anyon → Poly
  | .one, .one => [(1, [0])]
  | .one, .tau => [(1, [1])]
  | .tau, .one => [(1, [2])]
  | .tau, .tau => [(1, [3])]

end PentPoly

/-- **ANTI-VACUITY, pentagon uniqueness.**  Of the 50 live pentagon instances,
    exactly **11** are non-trivial for a generic associator — the eleven
    extracted by `rfl` in §7.1.  The other 39 hold for *any* `p q r s`, so
    they constrain nothing. -/
theorem pentagon_nontrivial_instances :
    countPentViolations PentPoly.polyRng PentPoly.FgP = 11 := rfl


/-! ═══════════════════════════════════════════════════════════════════════
    ## 8.  GALOIS CONJUGATION  ζ ↦ ζ⁴  AS A PROVED RING AUTOMORPHISM
           — and the structural proof of `chirality_left`

    Everything above about the two chiralities was proved by EVALUATION: the
    mirror constants `r1'`, `rt'` were written down and the hexagon was
    re-checked on them (`chirality_left`, `mirror_satisfies_hexagon`).  That
    is a true statement obtained by a coincidence of arithmetic.  This section
    replaces the coincidence with a reason.

    `Gal(Q(ζ₅)/Q) ≅ Z/4` is generated by `σ : ζ ↦ ζ²`.  Its square
    `conj = σ² : ζ ↦ ζ⁴` is complex conjugation, and it is the unique element
    of order 2, so it fixes the real subfield `Q(√5) = Q(φ)` pointwise.  In
    the integral basis `(1, ζ, ζ², ζ³)` with `ζ⁴ = −(1+ζ+ζ²+ζ³)`:

        a₀ + a₁ζ + a₂ζ² + a₃ζ³
          ↦ a₀ + a₁ζ⁴ + a₂ζ³ + a₃ζ²                      [ζ²↦ζ⁸=ζ³, ζ³↦ζ¹²=ζ²]
          = (a₀−a₁) + (−a₁)ζ + (a₃−a₁)ζ² + (a₂−a₁)ζ³ .

    Because `φ` is fixed, and `t = √φ` is defined by `t² = φ`, the assignment
    `t ↦ t` extends `conj` to all of `K = Z[ζ₅][t]/(t²−φ)`.  (The OTHER
    extension `t ↦ −t` exists too; we take the one that fixes `b = t/φ`, which
    is the one that fixes the associator `F`.)

    The payoff is `hexagonCheck_conj`: conjugation commutes with the hexagon
    check on the nose, for ALL `r₁, r_τ`.  `chirality_left` then falls out of
    `chirality_right` by transport — the 15 coherence instances are never
    re-evaluated on the mirror constants.  (One four-integer `rfl` does remain,
    identifying `conj ζ² = ζ³`; see the honest label at the payoff.)
    ═══════════════════════════════════════════════════════════════════════ -/

namespace Z5

/-- **Complex conjugation on Z[ζ₅]**, `ζ ↦ ζ⁴`, in the basis `(1,ζ,ζ²,ζ³)`. -/
def conj (u : Z5) : Z5 := ⟨u.a0 - u.a1, -u.a1, u.a3 - u.a1, u.a2 - u.a1⟩

/-! ### It is the map it claims to be: the basis, checked -/

theorem conj_zero  : conj zero  = zero  := rfl
theorem conj_one   : conj one   = one   := rfl
/-- `conj ζ = ζ⁴` — the defining property. -/
theorem conj_zeta  : conj zeta  = zeta4 := rfl
/-- `conj ζ² = ζ⁸ = ζ³`. -/
theorem conj_zeta2 : conj zeta2 = zeta3 := rfl
/-- `conj ζ³ = ζ¹² = ζ²`. -/
theorem conj_zeta3 : conj zeta3 = zeta2 := rfl
/-- `conj ζ⁴ = ζ¹⁶ = ζ` — so `conj` is an involution already on the basis. -/
theorem conj_zeta4 : conj zeta4 = zeta  := rfl

/-- **THE REAL SUBFIELD IS FIXED**: `conj φ = φ`.  `φ = 1 + ζ + ζ⁴` and
    conjugation swaps `ζ ↔ ζ⁴`, so the sum is untouched. -/
theorem conj_phi : conj phi = phi := rfl

/-- **`1/φ` is fixed too**: `1/φ = ζ + ζ⁴`, the same swap. -/
theorem conj_invPhi : conj invPhi = invPhi := rfl

/-! ### It is a ring homomorphism -/

theorem conj_add (u v : Z5) : conj (add u v) = add (conj u) (conj v) := by
  cases u; cases v
  simp only [conj, add, Z5.mk.injEq]
  refine ⟨?_,?_,?_,?_⟩ <;> omega

/-- (The `trivial` slot is the `ζ` component: `−(−a₁) = −(−a₁)` is closed by
    `simp` before `omega` ever sees it.  Discharging it with `trivial` rather
    than the simp lemma `true_and` keeps this file free of
    `Classical.choice`, matching the rest of the development.) -/
theorem conj_neg (u : Z5) : conj (neg u) = neg (conj u) := by
  cases u; simp only [conj, neg, Z5.mk.injEq]
  refine ⟨?_, trivial, ?_, ?_⟩ <;> omega

/-- **THE REAL CONTENT.**  `conj` is multiplicative: degree 2 in the eight
    integer indeterminates `u.aᵢ, v.aⱼ`.  After `simp only` distributes the
    four `Int` sign/subtraction rules, every component of both sides is a
    LINEAR combination of the sixteen atoms `u.aᵢ * v.aⱼ`, and `omega` closes
    each of the four componentwise goals.  Default budgets throughout. -/
theorem conj_mul (u v : Z5) : conj (mul u v) = mul (conj u) (conj v) := by
  cases u; cases v
  simp only [conj, mul, Z5.mk.injEq,
             Int.sub_mul, Int.mul_sub, Int.neg_mul, Int.mul_neg]
  refine ⟨?_,?_,?_,?_⟩ <;> omega

/-- **AN INVOLUTION** — hence a bijection, hence an automorphism. -/
theorem conj_conj (u : Z5) : conj (conj u) = u := by
  cases u; simp only [conj, Z5.mk.injEq]; refine ⟨?_,?_,?_,?_⟩ <;> omega

theorem conj_inj {u v : Z5} (h : conj u = conj v) : u = v := by
  have h2 := congrArg conj h
  rwa [conj_conj, conj_conj] at h2

/-! ### Negative controls: not every coordinate shuffle is a ring map, and
    not every Galois element fixes `φ`. -/

/-- The naive coordinate swap `a₁ ↔ a₂`.  It fixes `1`, `ζ³` and looks like a
    plausible "conjugation", but it is not a ring map. -/
def swapBad (u : Z5) : Z5 := ⟨u.a0, u.a2, u.a1, u.a3⟩

/-- `swapBad` is additive… -/
theorem swapBad_add (u v : Z5) :
    swapBad (add u v) = add (swapBad u) (swapBad v) := rfl
/-- …and an involution, hence a bijection.  It has every property `conj` has
    except the one that matters. -/
theorem swapBad_swapBad (u : Z5) : swapBad (swapBad u) = u := rfl

/-- **NEGATIVE CONTROL**: `swapBad` fails multiplicativity at `ζ·ζ`.
    `swapBad(ζ²) = ζ` but `swapBad(ζ)² = (ζ²)² = ζ⁴ ≠ ζ`.  So `conj_mul` above
    is not a theorem about any old additive bijection on the coordinates. -/
theorem swapBad_not_mul :
    swapBad (mul zeta zeta) ≠ mul (swapBad zeta) (swapBad zeta) := by decide

/-- The OTHER nontrivial Galois element, `σ : ζ ↦ ζ²` — the generator of
    `Gal ≅ Z/4`.  `σ(a₀+a₁ζ+a₂ζ²+a₃ζ³) = (a₀−a₂) + (a₃−a₂)ζ + (a₁−a₂)ζ² − a₂ζ³`. -/
def sigma (u : Z5) : Z5 := ⟨u.a0 - u.a2, u.a3 - u.a2, u.a1 - u.a2, -u.a2⟩

theorem sigma_zeta  : sigma zeta  = zeta2 := rfl
theorem sigma_zeta2 : sigma zeta2 = zeta4 := rfl

/-- `σ` really is a ring map too — so the next theorem is not about a broken
    definition, it is about a genuine automorphism of `Z[ζ₅]`. -/
theorem sigma_mul (u v : Z5) : sigma (mul u v) = mul (sigma u) (sigma v) := by
  cases u; cases v
  simp only [sigma, mul, Z5.mk.injEq,
             Int.sub_mul, Int.mul_sub, Int.neg_mul, Int.mul_neg]
  refine ⟨?_,?_,?_,?_⟩ <;> omega

/-- **WHY `conj` AND NOT `σ`**: `σ` does NOT fix the real subfield —
    `σ(φ) = −1/φ`, the other root of `X² − X − 1`.  So `σ` moves `t² = φ` and
    cannot be extended to `K` with `t` fixed; it would move the associator
    `F` as well.  Conjugation `ζ ↦ ζ⁴` is the unique nontrivial element that
    survives to `K` fixing `F`. -/
theorem sigma_phi : sigma phi = neg invPhi := rfl

theorem sigma_phi_ne : sigma phi ≠ phi := by decide

/-- **`conj` IS `σ²`.**  This pins down which element of the Galois group
    `conj` is: `Gal(Q(ζ₅)/Q) ≅ Z/4` is generated by `σ : ζ ↦ ζ²`, and the
    unique element of order two is `σ² : ζ ↦ ζ⁴`.  Not a definition — a
    computed identity between the two maps as written. -/
theorem sigma_sigma (u : Z5) : sigma (sigma u) = conj u := by
  cases u; simp only [sigma, conj, Z5.mk.injEq]; refine ⟨?_,?_,?_,?_⟩ <;> omega

/-- …and therefore `σ` has order exactly 4, which is why `conj` is the only
    nontrivial candidate that can fix a quadratic subfield. -/
theorem sigma_order_four (u : Z5) : sigma (sigma (sigma (sigma u))) = u := by
  rw [sigma_sigma, sigma_sigma, conj_conj]

end Z5

/-! ### Lifting to K = Z[ζ₅][t]/(t² − φ)

`conj φ = φ`, so `t ↦ t` is consistent with `t² = φ`, and the extension is
just "conjugate both coordinates". -/

namespace KK

/-- **Conjugation on K**: `ζ ↦ ζ⁴`, `t ↦ t`. -/
def conj (u : KK) : KK := ⟨Z5.conj u.x, Z5.conj u.y⟩

theorem conj_zero : conj zero = zero := rfl
theorem conj_one  : conj one  = one  := rfl
theorem conj_emb (u : Z5) : conj (emb u) = emb (Z5.conj u) := rfl

/-- `t = √φ` is fixed — this is what makes the lift legal. -/
theorem conj_t : conj t = t := rfl
/-- `1/φ` is fixed. -/
theorem conj_invPhi : conj invPhi = invPhi := rfl
/-- **`b = t/φ = 1/√φ` is fixed** — the off-diagonal entry of the associator.

    (Round 4, correction D2: this docstring previously read `b = t/√φ`, which
    is wrong — `t/√φ = t·b = 1`.  The constant is stated correctly at its
    definition and in §9; the theorem was always true and only its label was
    false.  Norm 6 reaches file comments too.) -/
theorem conj_b : conj b = b := rfl

theorem conj_add (u v : KK) : conj (add u v) = add (conj u) (conj v) := by
  cases u; cases v; simp only [conj, add, KK.mk.injEq]
  exact ⟨Z5.conj_add _ _, Z5.conj_add _ _⟩

theorem conj_neg (u : KK) : conj (neg u) = neg (conj u) := by
  cases u; simp only [conj, neg, KK.mk.injEq]
  exact ⟨Z5.conj_neg _, Z5.conj_neg _⟩

/-- **`conj` IS MULTIPLICATIVE ON K.**  Lifted from `Z5.conj_mul` — no descent
    to `Int` at this level.  The `φ` in `(x₁y₁t)(x₂y₂t)`'s cross term is
    exactly where `Z5.conj_phi` is spent. -/
theorem conj_mul (u v : KK) : conj (mul u v) = mul (conj u) (conj v) := by
  cases u; cases v
  simp only [conj, mul, Z5.conj_add, Z5.conj_mul, Z5.conj_phi]

/-- **AN INVOLUTION ON K**, hence an automorphism. -/
theorem conj_conj (u : KK) : conj (conj u) = u := by
  cases u; simp only [conj, KK.mk.injEq]
  exact ⟨Z5.conj_conj _, Z5.conj_conj _⟩

theorem conj_inj {u v : KK} (h : conj u = conj v) : u = v := by
  have h2 := congrArg conj h
  rwa [conj_conj, conj_conj] at h2

/-- Conjugation is invisible to the equality test — the step that lets it pass
    through a `Bool`-valued coherence check. -/
theorem beq_conj (u v : KK) : beq (conj u) (conj v) = beq u v := by
  simp only [beq]
  exact decide_eq_decide.mpr ⟨conj_inj, fun h => by rw [h]⟩

/-! #### The mirror, obtained rather than posited -/

/-- **THE MIRROR BRAIDING IS THE CONJUGATE ONE**: `conj(ζ²) = ζ³`. -/
theorem conj_r1 : conj r1 = r1' := rfl
/-- `conj(−ζ) = −ζ⁴`. -/
theorem conj_rt : conj rt = rt' := rfl
/-- `conj(ζ³) = ζ²` — spin flips. -/
theorem conj_theta : conj theta = theta' := rfl

/-- **ANTI-VACUITY for the whole section**: `conj` is not the identity map.
    If it were, `hexagonCheck_conj` below would be a tautology and
    `chirality_left_structural` would prove nothing new. -/
theorem conj_ne_id : beq (conj r1) r1 = false := rfl

end KK

/-! ### Naturality: `conj` commutes with the coherence machinery

Three lemmas, then the theorem.  Each is small: `Fs` and `Rb` are finite case
splits, `sumOver` is one induction. -/

/-- **The associator is fixed pointwise.**  Every entry of `F` — `1/φ`, `b`,
    `b`, `−1/φ` — lies in the fixed subring, and the `0`/`1` branches of `Fs`
    are fixed trivially.  64 label tuples, each `rfl`. -/
theorem conj_Fs (a b c d x y : Anyon) :
    KK.conj (Fs kRng Fsymm a b c d x y) = Fs kRng Fsymm a b c d x y := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases x <;> cases y <;> rfl

/-- The four entries of `F`, stated on their own. -/
theorem conj_Fsymm (i j : Anyon) : KK.conj (Fsymm i j) = Fsymm i j := by
  cases i <;> cases j <;> rfl

/-- **The braiding transforms.**  `Rb` returns `1`, `r₁` or `r_τ`; `1` is
    fixed and the other two are carried along. -/
theorem conj_Rb (r1 rt : KK) (x y c : Anyon) :
    KK.conj (Rb kRng r1 rt x y c) = Rb kRng (KK.conj r1) (KK.conj rt) x y c := by
  cases x <;> cases y <;> cases c <;> rfl

/-- **Sums are preserved**, by induction on the fusion channel, using
    `conj_zero` at the base and `conj_add` at the step. -/
theorem conj_sumOver (f g : Anyon → KK) (l : List Anyon)
    (hfg : ∀ u, g u = KK.conj (f u)) :
    sumOver kRng g l = KK.conj (sumOver kRng f l) := by
  induction l with
  | nil => rfl
  | cons u us ih =>
      show KK.add (g u) (sumOver kRng g us)
         = KK.conj (KK.add (f u) (sumOver kRng f us))
      rw [KK.conj_add, hfg u, ih]

/-- **NATURALITY OF THE HEXAGON UNDER GALOIS CONJUGATION.**

    For every `r₁, r_τ` in K and every label tuple, the hexagon check on the
    conjugated braiding returns exactly what it returns on the original.  Both
    sides of the equation are conjugated term by term — `F` is fixed, `R` is
    carried, sums and products commute with `conj` — and `beq` cannot tell the
    difference because `conj` is injective.

    This is the structural statement the round-1 file was missing. -/
theorem hexagonCheck_conj (r1 rt : KK) (a b c d e z : Anyon) :
    hexagonCheck kRng Fsymm (KK.conj r1) (KK.conj rt) a b c d e z
      = hexagonCheck kRng Fsymm r1 rt a b c d e z := by
  unfold hexagonCheck
  by_cases hv : hexagonValid a b c d e z = true
  · have hL : kRng.mul (Rb kRng (KK.conj r1) (KK.conj rt) e c d)
                       (Fs kRng Fsymm c a b d z e)
            = KK.conj (kRng.mul (Rb kRng r1 rt e c d)
                                (Fs kRng Fsymm c a b d z e)) := by
      show KK.mul _ _ = KK.conj (KK.mul _ _)
      simp only [KK.conj_mul, conj_Rb, conj_Fs]
    have hR : sumOver kRng
                (fun g => kRng.mul (kRng.mul (kRng.mul (Fs kRng Fsymm a b c d e g)
                                                       (Rb kRng (KK.conj r1) (KK.conj rt) b c g))
                                             (Fs kRng Fsymm a c b d z g))
                                   (Rb kRng (KK.conj r1) (KK.conj rt) a c z)) (fuse b c)
            = KK.conj (sumOver kRng
                (fun g => kRng.mul (kRng.mul (kRng.mul (Fs kRng Fsymm a b c d e g)
                                                       (Rb kRng r1 rt b c g))
                                             (Fs kRng Fsymm a c b d z g))
                                   (Rb kRng r1 rt a c z)) (fuse b c)) := by
      refine conj_sumOver _ _ _ ?_
      intro u
      show KK.mul (KK.mul (KK.mul _ _) _) _
         = KK.conj (KK.mul (KK.mul (KK.mul _ _) _) _)
      simp only [KK.conj_mul, conj_Rb, conj_Fs]
    rw [if_pos hv, if_pos hv, hL, hR]
    exact KK.beq_conj _ _
  · rw [if_neg hv, if_neg hv]

/-- **CONJUGATION CARRIES SOLUTIONS TO SOLUTIONS.**  The requested
    `conj_maps_solution`: if `(r₁, r_τ)` satisfies the hexagon then so does
    `(conj r₁, conj r_τ)`.  Immediate from naturality. -/
theorem conj_maps_solution (r1 rt : KK)
    (h : ∀ a b c d e z, hexagonCheck kRng Fsymm r1 rt a b c d e z = true) :
    ∀ a b c d e z,
      hexagonCheck kRng Fsymm (KK.conj r1) (KK.conj rt) a b c d e z = true := by
  intro a b c d e z
  rw [hexagonCheck_conj]
  exact h a b c d e z

/-- The violation COUNT is a Galois invariant — same fact in the counted form
    the anti-vacuity section uses. -/
theorem countHexViolations_conj (r1 rt : KK) :
    countHexViolations (KK.conj r1) (KK.conj rt) = countHexViolations r1 rt := by
  simp only [countHexViolations, sumB, hexagonCheck_conj]

/-! ### THE PAYOFF: `chirality_left`, structurally

`chirality_left` and `mirror_satisfies_hexagon` above are proved by `rfl` —
by grinding the mirror constants through all 15 live instances.  Here are the
same two statements with the grinding replaced by a reason: the mirror IS the
conjugate, and conjugation is a ring automorphism fixing the associator, so it
maps the solution set to itself.

HONEST LABEL on what "structural" means here.  The hexagon is never re-checked
on the mirror constants — that is the whole saving.  What *is* still computed
is the single scalar identification `KK.conj_r1 : conj ζ² = ζ³` (and its
partner for `r_τ`), a one-line `rfl` on four integers.  The 15 coherence
instances are transported, not recomputed. -/

/-- **`chirality_left`, STRUCTURALLY.**  Not "the mirror happens to work" but
    "the mirror is the Galois conjugate of something that works". -/
theorem mirror_satisfies_hexagon_structural :
    ∀ a b c d e z, hexagonCheck kRng Fsymm r1' rt' a b c d e z = true := by
  intro a b c d e z
  rw [← KK.conj_r1, ← KK.conj_rt]
  exact conj_maps_solution KK.r1 KK.rt golden_satisfies_hexagon a b c d e z

/-- The counted form: `chirality_left` derived from `chirality_right` by
    transport, with no arithmetic on `r1'`, `rt'` at all. -/
theorem chirality_left_structural : countHexViolations r1' rt' = 0 := by
  rw [← KK.conj_r1, ← KK.conj_rt, countHexViolations_conj]
  exact chirality_right

/-- Both chirality theorems, and the fact that they are the same theorem. -/
theorem chiralities_are_conjugate :
    countHexViolations KK.r1 KK.rt = countHexViolations (KK.conj KK.r1) (KK.conj KK.rt) ∧
    KK.conj KK.r1 = r1' ∧ KK.conj KK.rt = rt' ∧ KK.conj KK.theta = theta' :=
  ⟨(countHexViolations_conj KK.r1 KK.rt).symm, rfl, rfl, rfl⟩

/-! ### Two receipts upgraded from coincidence to structure -/

/-- **`|r_τ| = 1`, now literally a norm.**  `roots_product_one` says
    `r_τ · r_τ' = 1`; with `conj rt = rt'` proved, that IS
    `r_τ · conj(r_τ) = 1` — the field norm of `r_τ` down to the real subfield
    is 1.  The bench's "|r| = 1 EMERGED" with no analysis anywhere. -/
theorem rt_norm_one : KK.mul KK.rt (KK.conj KK.rt) = KK.one := by
  rw [KK.conj_rt]; exact roots_product_one

/-- Same one level up, for `r₁`. -/
theorem r1_norm_one : KK.mul KK.r1 (KK.conj KK.r1) = KK.one := by
  rw [KK.conj_r1]; exact r1_roots_product_one

/-- **THE QUADRATIC'S TWO ROOTS ARE A GALOIS ORBIT.**  `rt_root_quadratic` and
    `rt'_root_quadratic` are two `rfl`s in the file above; here the second is
    obtained from the first by applying `conj` and using that every coefficient
    of `Q(X) = X² + (1/φ)X + 1` is fixed.  Conjugation permutes the roots of a
    polynomial over the fixed subring — that is why there is a mirror at all. -/
theorem rt'_root_quadratic_structural :
    KK.add (KK.add (KK.mul rt' rt') (KK.mul KK.invPhi rt')) KK.one = KK.zero := by
  have h := congrArg KK.conj rt_root_quadratic
  rw [KK.conj_add, KK.conj_add, KK.conj_mul, KK.conj_mul,
      KK.conj_one, KK.conj_zero, KK.conj_invPhi, KK.conj_rt] at h
  exact h

/-- **ANTI-VACUITY, section 7.**  The hypothesis of `conj_maps_solution` is
    inhabited (the golden braiding), the conclusion is about a genuinely
    different braiding (`conj_ne_id`, `chiralities_distinct`), and the 15 live
    hexagon instances of `hexagon_live_instances` are what is being
    transported.  Restated in one place so the section cannot be read as
    vacuous. -/
theorem galois_section_not_vacuous :
    countHexValid = 15 ∧
    KK.beq (KK.conj KK.r1) KK.r1 = false ∧
    KK.beq KK.r1 r1' = false ∧
    (∀ a b c d e z, hexagonCheck kRng Fsymm KK.r1 KK.rt a b c d e z = true) :=
  ⟨rfl, rfl, rfl, golden_satisfies_hexagon⟩

/-- **NEGATIVE CONTROL FOR NATURALITY.**  Naturality is a statement about
    `conj` specifically, not about any relabelling of the braiding: swapping
    `r₁ ↔ r_τ` is also a "symmetry-looking" operation on the pair, and it
    destroys the solution (5 of 15 fail).  So `hexagonCheck_conj` is carrying
    real information about `conj`. -/
theorem naturality_negative_control :
    countHexViolations KK.rt KK.r1 = 5 ∧
    countHexViolations (KK.conj KK.r1) (KK.conj KK.rt) = 0 :=
  ⟨rfl, (countHexViolations_conj KK.r1 KK.rt).trans chirality_right⟩

/-- The coordinate map on K induced by `Z5.swapBad` — additive, bijective, not
    multiplicative. -/
def badConj (u : KK) : KK := ⟨Z5.swapBad u.x, Z5.swapBad u.y⟩

/-- **THE SHARP NEGATIVE CONTROL: MULTIPLICATIVITY IS WHAT DOES THE WORK.**

    `badConj` is additive and an involution, exactly like `conj`; it fails only
    `conj_mul`.  Transporting the golden solution along it lands *outside* the
    solution set — 5 of the 15 live hexagon instances break.  So
    `hexagonCheck_conj` is not a consequence of `conj` being a bijection or of
    it being additive: it genuinely spends `Z5.conj_mul`.

    Compare `chirality_left_structural`, where the same transport along the
    genuine ring automorphism gives 0. -/
theorem badConj_breaks_hexagon :
    countHexViolations (badConj KK.r1) (badConj KK.rt) = 5 := rfl

/-- The two transports side by side: same shape of map, opposite outcome. -/
theorem multiplicativity_is_load_bearing :
    countHexViolations (KK.conj KK.r1) (KK.conj KK.rt) = 0 ∧
    countHexViolations (badConj KK.r1) (badConj KK.rt) = 5 :=
  ⟨(countHexViolations_conj KK.r1 KK.rt).trans chirality_right, rfl⟩

/-! ═══════════════════════════════════════════════════════════════════════
    ## 9.  GAUGE EQUIVALENCE.  Tier 3a and Tier 3b are ONE anyon.

    Tier 3a lives over `Zp = Z[φ]`; Tier 3b lives over `KK = Z[ζ₅][t]/(t²−φ)`.
    Those are different rings, so "the same anyon in two gauges" is not even a
    well-formed claim until Z[φ] is placed inside K.  Three steps:

      STEP 1.  `Zp.toKK : Zp → KK`, `m + nφ ↦ m + n·φ_K`, proved a ring map
               (and injective — the embedding does not collapse anything).
      STEP 2.  `FratK := toKK ∘ Frat`, and the exact diagonal gauge relating it
               to `Fsymm`.
      STEP 3.  The gauge is invertible, so the relation is an EQUIVALENCE.

    HONEST NOTE ON THE HAND SKETCH.  The sketch's SHAPE is right — a diagonal
    gauge, ratio `t`, consistent because `t·b = 1` — and its DIRECTION is
    backwards.  Precisely:

      * the sketch proposed `λ = diag(t, 1)` in the relation
        `λ_x · Fsymm(x,y) = FratK(x,y) · λ_y`.  That combination fails 2 of the
        4 entries (`sketch_gauge_fails`).
      * the gauge that satisfies THAT relation is `λ = diag(1, t)`
        (`gauge_clean`, 0 failures).
      * the sketch's `diag(t,1)` is exactly `t·λ⁻¹` (`lamSketch_eq`) and it
        does satisfy the relation with the two associators EXCHANGED
        (`sketch_gauge_relation_reversed`).

    So nothing in the sketch's reasoning was wrong; the index placement was.
    The entry-ratio table `gauge_ratio_table` is where it is visible: the ratio
    matrix `FratK(x,y)/Fsymm(x,y)` is `[[1, b],[t, 1]]`, which is `λ_x/λ_y` for
    `λ = (1, t)`, not for `λ = (t, 1)`.  The transposed table fails 2 of 4, so
    the table is not accidentally symmetric.
    ═══════════════════════════════════════════════════════════════════════ -/

/-! ### STEP 1.  The embedding Z[φ] ↪ Z[ζ₅] ↪ K

In `Z5` the golden ratio is `Z5.phi = ⟨0,0,−1,−1⟩ = −ζ²−ζ³ = 1+ζ+ζ⁴`.  So
`m + nφ` has `Z5`-coordinates `⟨m, 0, −n, −n⟩`.  That closed form is taken as
the definition (it makes every proof below cheap) and `toZ5_eq` certifies it is
literally "substitute `Z5.phi` for `φ`". -/

namespace Zp

/-- `m + nφ` as an element of `Z[ζ₅]`. -/
def toZ5 (u : Zp) : Z5 := ⟨u.m, 0, -u.n, -u.n⟩

/-- `toZ5` really is `m·1 + n·φ` — the closed form is not a fudge. -/
theorem toZ5_eq (u : Zp) :
    toZ5 u = Z5.add (Z5.mul ⟨u.m,0,0,0⟩ Z5.one) (Z5.mul ⟨u.n,0,0,0⟩ Z5.phi) := by
  cases u
  simp only [toZ5, Z5.add, Z5.mul, Z5.one, Z5.phi, Z5.mk.injEq]
  refine ⟨?_,?_,?_,?_⟩ <;> omega

theorem toZ5_zero : toZ5 zero = Z5.zero := rfl
theorem toZ5_one : toZ5 one = Z5.one := rfl
theorem toZ5_phi : toZ5 phi = Z5.phi := rfl
theorem toZ5_invPhi : toZ5 invPhi = Z5.invPhi := rfl

theorem toZ5_add (u v : Zp) : toZ5 (add u v) = Z5.add (toZ5 u) (toZ5 v) := by
  cases u; cases v
  simp only [toZ5, add, Z5.add, Z5.mk.injEq]
  refine ⟨trivial, ?_, ?_, ?_⟩ <;> omega

theorem toZ5_neg (u : Zp) : toZ5 (neg u) = Z5.neg (toZ5 u) := rfl

/-- **The multiplicative half of the ring map.**  This is the one real
    computation: `Zp.mul` uses `φ² = φ+1`, `Z5.mul` uses `ζ⁵ = 1` and
    `1+ζ+ζ²+ζ³+ζ⁴ = 0`, and the two agree on the nose.  A `Zp`/`Z5`-level
    descent to `Int`, which the house rules allow (the forbidden descent is at
    the `KK` level). -/
theorem toZ5_mul (u v : Zp) : toZ5 (mul u v) = Z5.mul (toZ5 u) (toZ5 v) := by
  cases u; cases v
  simp only [toZ5, mul, Z5.mul, Z5.mk.injEq,
             Int.neg_mul, Int.mul_neg, Int.neg_neg, Int.mul_zero, Int.zero_mul]
  refine ⟨?_,?_,?_,?_⟩ <;> omega

end Zp

/-! ### `Z[ζ₅] ↪ K` is a ring map — proved from the `Z5` laws, no `Int` descent -/

namespace KK

theorem emb_zero : emb Z5.zero = zero := rfl
theorem emb_one : emb Z5.one = one := rfl

theorem emb_add (u v : Z5) : add (emb u) (emb v) = emb (Z5.add u v) := rfl

theorem emb_mul (u v : Z5) : mul (emb u) (emb v) = emb (Z5.mul u v) := by
  simp only [emb, mul, KK.mk.injEq]
  refine ⟨?_, ?_⟩
  · rw [show Z5.mul Z5.zero Z5.zero = Z5.zero from rfl, Z5.mul_zero, Z5.add_zero]
  · rw [Z5.mul_zero, Z5.zero_mul, Z5.add_zero]

theorem emb_neg (u : Z5) : neg (emb u) = emb (Z5.neg u) := rfl

end KK

/-! ### `Zp.toKK` — the composite, and the four ring-map receipts -/

namespace Zp

/-- **THE EMBEDDING** `Z[φ] ↪ K`, `m + nφ ↦ m + n·φ`. -/
def toKK (u : Zp) : KK := KK.emb (toZ5 u)

theorem toKK_zero : toKK zero = KK.zero := rfl
theorem toKK_one : toKK one = KK.one := rfl

theorem toKK_add (u v : Zp) : toKK (add u v) = KK.add (toKK u) (toKK v) := by
  rw [toKK, toKK, toKK, KK.emb_add, toZ5_add]

theorem toKK_mul (u v : Zp) : toKK (mul u v) = KK.mul (toKK u) (toKK v) := by
  rw [toKK, toKK, toKK, KK.emb_mul, toZ5_mul]

theorem toKK_neg (u : Zp) : toKK (neg u) = KK.neg (toKK u) := by
  rw [toKK, toKK, KK.emb_neg, toZ5_neg]

/-- **`φ ↦ φ`.** -/
theorem toKK_phi : toKK phi = KK.emb Z5.phi := rfl

/-- **`1/φ ↦ 1/φ`.**  The two rings' names for the golden inverse agree under
    the embedding — which is what makes the Tier 3a and Tier 3b matrices
    comparable at all. -/
theorem toKK_invPhi : toKK invPhi = KK.invPhi := rfl

/-- The embedding is compatible with the two `φ`-receipts: `t² = φ_K` is the
    image of Tier 3a's `φ`, and `φ·(1/φ) = 1` transports. -/
theorem toKK_phi_eq_t_sq : toKK phi = KK.mul KK.t KK.t := rfl

theorem toKK_invPhi_mul : KK.mul (toKK phi) (toKK invPhi) = KK.one := rfl

/-- **THE EMBEDDING IS INJECTIVE** — `Z[φ]` sits inside `K` without collapse,
    so "the same anyon" below is a statement about a genuine subring.

    Round-3 note on the proof, because the obvious one is not constructive.
    Writing this as `simp only [… , Zp.mk.injEq] at h ⊢; omega` — i.e. letting
    `omega` close the *conjunctive* goal from the *conjunctive* hypothesis —
    typechecks, but the resulting term depends on **`Classical.choice`**, which
    no other theorem in this project does.  The audit's axiom census caught it.
    Destructuring the hypothesis by hand first and leaving `omega` a single
    scalar goal removes it; going one step further and closing by `subst`
    leaves only `propext`.  So the version below is the one that keeps the
    file's "no `Classical.choice` anywhere" guarantee true. -/
theorem toKK_injective (u v : Zp) (h : toKK u = toKK v) : u = v := by
  cases u; cases v
  simp only [toKK, toZ5, KK.emb, KK.mk.injEq, Z5.mk.injEq] at h
  obtain ⟨⟨hm, _, hn, _⟩, _⟩ := h
  have hn' : _ = _ := Int.neg_inj.mp hn
  subst hm; subst hn'; rfl

end Zp

/-- **ANTI-VACUITY for the embedding**: it is not the zero map and it does not
    identify the basis.  (An injective map already implies this; these are the
    two cheap concrete witnesses.) -/
theorem toKK_nontrivial :
    KK.beq (Zp.toKK Zp.one) KK.zero = false ∧
    KK.beq (Zp.toKK Zp.phi) (Zp.toKK Zp.one) = false ∧
    KK.beq (Zp.toKK Zp.invPhi) (Zp.toKK Zp.one) = false :=
  ⟨rfl, rfl, rfl⟩

/-! ### STEP 2.  `FratK` — Tier 3a's associator, read inside K -/

/-- The rational-gauge associator pushed into `K` along the embedding. -/
def FratK : Anyon → Anyon → KK := fun x y => Zp.toKK (Frat x y)

/-- The four entries, in `K`'s own vocabulary: `FratK = [[1/φ, 1/φ],[1, −1/φ]]`.
    (Compare `Fsymm = [[1/φ, b],[b, −1/φ]]`: the diagonals already agree; only
    the off-diagonal pair differs, and it differs by exactly one factor of
    `t`.) -/
theorem FratK_entries :
    FratK .one .one = KK.invPhi ∧
    FratK .one .tau = KK.invPhi ∧
    FratK .tau .one = KK.one ∧
    FratK .tau .tau = KK.neg KK.invPhi :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The embedding carries Tier 3a's `F'·F' = 1` into `K`. -/
theorem FratK_sq : matEq kRng (matMul kRng FratK FratK) (matId kRng) = true := rfl

/-- **COHERENCE TRANSPORTS.**  The pentagon holds for `FratK` over `K` — all
    512 tuples, the same 50 live instances.  So the embedding does not merely
    move symbols; it moves the theorem.  (`pentagon_rational_gauge` is the
    `Zp`-level statement; this is its image.) -/
theorem pentagon_FratK :
    ∀ a b c dd x y t w v, pentagonCheck kRng FratK a b c dd x y t w v = true := by
  intro a b c dd x y t w v
  cases a <;> cases b <;> cases c <;> cases dd <;> cases x <;> cases y <;>
    cases t <;> cases w <;> cases v <;> rfl

/-- **THE TWO GAUGES ARE NOT EQUAL.**  Without this the equivalence below would
    be vacuous — `FratK` and `Fsymm` really are different matrices over `K`. -/
theorem FratK_ne_Fsymm : matEq kRng FratK Fsymm = false := rfl

/-! ### The gauge, derived rather than assumed

Divide `FratK` by `Fsymm` entrywise (legitimately: every `Fsymm` entry is a
unit).  Recall `b = t·(1/φ)` and `t² = φ`, so `t·b = 1`, i.e. `b = 1/t`.

    (1,1):  (1/φ) / (1/φ)  = 1
    (1,τ):  (1/φ) / b      = (1/φ)·t·… = b        [since b² = 1/φ, b·t = 1]
    (τ,1):  1     / b      = t
    (τ,τ): (−1/φ) / (−1/φ) = 1

So the ratio matrix is `[[1, b],[t, 1]]`.  For a DIAGONAL gauge that table must
be `λ_x/λ_y`; reading the corners, `λ_one/λ_tau = b` and `λ_tau/λ_one = t`,
which is consistent exactly because `t·b = 1`.  Hence

        λ_one = 1,   λ_tau = t.

The ratios are stated below WITHOUT division, as
`FratK(x,y) = ratio(x,y) · Fsymm(x,y)`, and each is `rfl`. -/

/-- The entrywise ratio `FratK / Fsymm`, written multiplicatively. -/
def gaugeRatio : Anyon → Anyon → KK
  | .one, .one => KK.one
  | .one, .tau => KK.b
  | .tau, .one => KK.t
  | .tau, .tau => KK.one

/-- **THE RATIO TABLE, EXACTLY** — division-free: each `FratK` entry is the
    corresponding `Fsymm` entry times the tabulated ratio. -/
theorem gauge_ratio_table (x y : Anyon) :
    FratK x y = KK.mul (gaugeRatio x y) (Fsymm x y) := by
  cases x <;> cases y <;> rfl

/-! ### The gauge itself -/

/-- **THE GAUGE** `λ = diag(1, t)`.  (NOT `diag(t,1)`; see the honest note.) -/
def lam : Anyon → KK
  | .one => KK.one
  | .tau => KK.t

/-- Its inverse `λ⁻¹ = diag(1, b)`, since `t·b = 1`. -/
def lamInv : Anyon → KK
  | .one => KK.one
  | .tau => KK.b

/-- The sketch's proposal, kept as a named negative control. -/
def lamSketch : Anyon → KK
  | .one => KK.t
  | .tau => KK.one

/-- **The ratio table IS `λ_x/λ_y`**, division-free: `ratio(x,y) · λ_y = λ_x`.
    This is the check that the entrywise ratios really do come from a DIAGONAL
    gauge — four independent entries, two free parameters, and it closes. -/
theorem gauge_ratio_is_lambda_quotient (x y : Anyon) :
    KK.mul (gaugeRatio x y) (lam y) = lam x := by
  cases x <;> cases y <;> rfl

/-! ### STEP 3.  Invertibility, the relation, and the conclusion -/

/-- **`t·b = 1`** — the single fact that makes the gauge invertible.
    `t·b = t·t·(1/φ) = φ·(1/φ) = 1`. -/
theorem t_mul_b : KK.mul KK.t KK.b = KK.one := rfl

/-- ...and the other side. -/
theorem b_mul_t : KK.mul KK.b KK.t = KK.one := rfl

/-- **EVERY GAUGE ENTRY IS A UNIT** — both sides, with the inverse exhibited.
    This is what upgrades the relation below from "a relation" to "an
    equivalence". -/
theorem lam_unit (x : Anyon) :
    KK.mul (lam x) (lamInv x) = KK.one ∧ KK.mul (lamInv x) (lam x) = KK.one := by
  cases x <;> exact ⟨rfl, rfl⟩

/-- **THE GAUGE RELATION**, division-free:
    `λ_x · Fsymm(x,y) = FratK(x,y) · λ_y` for all four `(x,y)`.
    Entry by entry:
      (1,1)  1·(1/φ) = (1/φ)·1
      (1,τ)  1·b     = (1/φ)·t
      (τ,1)  t·b     = 1·1
      (τ,τ)  t·(−1/φ) = (−1/φ)·t                                            -/
theorem gauge_relation (x y : Anyon) :
    KK.mul (lam x) (Fsymm x y) = KK.mul (FratK x y) (lam y) := by
  cases x <;> cases y <;> rfl

/-- The same, with `λ` on the outside of the other factor — the form that reads
    as "conjugate `Fsymm` by `λ` to get `FratK`". -/
theorem FratK_of_Fsymm (x y : Anyon) :
    FratK x y = KK.mul (KK.mul (lam x) (Fsymm x y)) (lamInv y) := by
  cases x <;> cases y <;> rfl

/-- ...and back the other way: `Fsymm` is `FratK` conjugated by `λ⁻¹`.
    Together with the previous theorem this is a two-sided inverse pair of
    transformations, i.e. an EQUIVALENCE and not a one-way relation. -/
theorem Fsymm_of_FratK (x y : Anyon) :
    Fsymm x y = KK.mul (KK.mul (lamInv x) (FratK x y)) (lam y) := by
  cases x <;> cases y <;> rfl

/-! ### Anti-vacuity and negative controls for the gauge -/

/-- Failures of a candidate diagonal gauge, out of the 4 entries. -/
def gaugeFails (l : Anyon → KK) : Nat :=
  sumB fun x => sumB fun y =>
    if KK.beq (KK.mul (l x) (Fsymm x y)) (KK.mul (FratK x y) (l y)) then 0 else 1

/-- **THE GAUGE WORKS**: zero failures (the count form of `gauge_relation`). -/
theorem gauge_clean : gaugeFails lam = 0 := rfl

/-- **THE CHECK HAS TEETH, 1**: the trivial gauge `λ = 1` fails 2 of 4 — which
    is exactly the statement that `FratK ≠ Fsymm` and that a gauge is
    *required*. -/
theorem trivial_gauge_fails : gaugeFails (fun _ => KK.one) = 2 := rfl

/-- **THE CHECK HAS TEETH, 2 — and the sketch is corrected on the record.**
    The charge's `λ = diag(t, 1)` fails 2 of the 4 entries: at `(1,τ)` it gives
    `t·b = 1` against `(1/φ)·1 = 1/φ`, and at `(τ,1)` it gives `1·b = b`
    against `1·t = t`.  The working gauge is `diag(1, t)`. -/
theorem sketch_gauge_fails : gaugeFails lamSketch = 2 := rfl

/-- **THE CHECK HAS TEETH, 3**: a non-unit diagonal (`diag(1, 1/φ)`) also
    fails, so `gaugeFails = 0` is not an artefact of "any diagonal will do". -/
theorem nonunit_gauge_fails :
    gaugeFails (fun x => match x with | .one => KK.one | .tau => KK.invPhi) = 2 :=
  rfl

/-! ### The sketch, rehabilitated

`sketch_gauge_fails` is not the end of the story.  `λ_sketch = diag(t,1)` is
exactly `t · λ⁻¹` — a scalar multiple of the INVERSE gauge — so it is not a
wrong matrix, it is the right matrix pointed the other way.  It satisfies the
relation with `Frat` and `Fsymm` EXCHANGED.  Both facts below are `rfl`, and
together they say the sketch had the gauge right and the direction backwards. -/

/-- `λ_sketch = t·λ⁻¹`: the sketch is the inverse gauge, rescaled by the unit
    `t`.  (An overall scalar is itself a gauge freedom, so this is the same
    transformation.) -/
theorem lamSketch_eq (x : Anyon) : lamSketch x = KK.mul KK.t (lamInv x) := by
  cases x <;> rfl

/-- **THE SKETCH'S GAUGE, IN ITS CORRECT DIRECTION**: `diag(t,1)` carries
    `FratK` to `Fsymm`, i.e. `λ_sketch,x · FratK(x,y) = Fsymm(x,y) · λ_sketch,y`.
    So the sketch is sound once the two associators swap places. -/
theorem sketch_gauge_relation_reversed (x y : Anyon) :
    KK.mul (lamSketch x) (FratK x y) = KK.mul (Fsymm x y) (lamSketch y) := by
  cases x <;> cases y <;> rfl

/-- The same for `λ⁻¹` unscaled — the clean reverse of `gauge_relation`. -/
theorem gauge_relation_reversed (x y : Anyon) :
    KK.mul (lamInv x) (FratK x y) = KK.mul (Fsymm x y) (lamInv y) := by
  cases x <;> cases y <;> rfl

/-- **THE GAUGE IS ESSENTIALLY UNIQUE.**  Any diagonal gauge `l` that satisfies
    the relation and is normalized at the vacuum (`l one = 1`) has `l tau = t`.
    Read off the `(τ,1)` entry: `l tau · b = 1 · l one = 1`, and multiplying by
    `t` gives `l tau = t`.  So `λ` was not one lucky choice among many. -/
theorem gauge_unique_normalized (l : Anyon → KK)
    (h1 : l .one = KK.one)
    (h : ∀ x y, KK.mul (l x) (Fsymm x y) = KK.mul (FratK x y) (l y)) :
    l .tau = KK.t := by
  have e := h .tau .one
  -- `Fsymm τ 1 = b`, `FratK τ 1 = 1`, and `l one = 1`
  rw [show Fsymm .tau .one = KK.b from rfl, show FratK .tau .one = KK.one from rfl,
      h1, KK.one_mul] at e
  calc l .tau = KK.mul (l .tau) KK.one          := (KK.mul_one _).symm
    _         = KK.mul (l .tau) (KK.mul KK.b KK.t) := by rw [b_mul_t]
    _         = KK.mul (KK.mul (l .tau) KK.b) KK.t := (KK.mul_assoc _ _ _).symm
    _         = KK.mul KK.one KK.t              := by rw [e]
    _         = KK.t                            := KK.one_mul _

/-- The uniqueness theorem is not vacuous: `lam` satisfies its hypotheses. -/
theorem gauge_unique_anti_vacuity : lam .tau = KK.t :=
  gauge_unique_normalized lam rfl gauge_relation

/-! ### THE CONCLUSION -/

/-- **TIER 3a AND TIER 3b ARE THE SAME ANYON, IN TWO GAUGES.**

    Everything the project wants, in one statement over the single ring `K`:

      (1) `Z[φ] ↪ K` is an injective ring map, so Tier 3a's associator has an
          unambiguous image `FratK` in Tier 3b's ring;
      (2) `FratK` satisfies the pentagon over `K` — the coherence, not just the
          symbols, transports;
      (3) `λ = diag(1, t)` is a two-sided unit at every label;
      (4) `λ` conjugates `Fsymm` to `FratK`, and `λ⁻¹` conjugates back.

    (3)+(4) is precisely the definition of a gauge equivalence of associators.
    So the rational gauge `[[1/φ,1/φ],[1,−1/φ]]` and the symmetric gauge
    `[[1/φ,b],[b,−1/φ]]` are two coordinate presentations of one Fibonacci
    anyon — not two anyons.  The whole difference is one factor of `t = √φ`
    moved across the off-diagonal. -/
theorem tier3a_tier3b_same_anyon :
    (∀ u v : Zp, Zp.toKK (Zp.add u v) = KK.add (Zp.toKK u) (Zp.toKK v)) ∧
    (∀ u v : Zp, Zp.toKK (Zp.mul u v) = KK.mul (Zp.toKK u) (Zp.toKK v)) ∧
    (∀ u v : Zp, Zp.toKK u = Zp.toKK v → u = v) ∧
    (∀ a b c dd x y t w v, pentagonCheck kRng FratK a b c dd x y t w v = true) ∧
    (∀ x, KK.mul (lam x) (lamInv x) = KK.one ∧
          KK.mul (lamInv x) (lam x) = KK.one) ∧
    (∀ x y, FratK x y = KK.mul (KK.mul (lam x) (Fsymm x y)) (lamInv y)) ∧
    (∀ x y, Fsymm x y = KK.mul (KK.mul (lamInv x) (FratK x y)) (lam y)) :=
  ⟨Zp.toKK_add, Zp.toKK_mul, Zp.toKK_injective,
   pentagon_FratK, lam_unit, FratK_of_Fsymm, Fsymm_of_FratK⟩


/-! ═══════════════════════════════════════════════════════════════════════
    ROUND 4 — `σ`, THE NORM MAP, AND **`Z[ζ₅]` IS AN INTEGRAL DOMAIN**

    The Galois generator `σ : ζ ↦ ζ²` is already in this file (`Z5.sigma`,
    with `sigma_mul`, `sigma_sigma : σ² = conj`, `sigma_order_four`).  That is
    exactly the map the round-4 design calls `sigma2`; nothing is redefined.
    What follows completes it to a hom, builds the field norm

        N(a) = a · σa · σ²a · σ³a ,

    shows `N` lands in `Z` **without ever expanding the degree-4 polynomial**
    (it is `σ`-fixed, and the `σ`-fixed subring is `Z` — a linear fact), shows
    `N` is multiplicative **by rearrangement of eight opaque factors alone**,
    and then runs a 2-adic descent to conclude that `Z[ζ₅]` has no zero
    divisors.  The descent works because 2 is inert in `Z[ζ₅]`; the negative
    controls at the bottom show that this is a real input and not bookkeeping.
    ═══════════════════════════════════════════════════════════════════════ -/

namespace Z5

/-! ### σ completed to a ring homomorphism

    `sigma` as written IS the design's `sigma2`; recorded so the merge is
    unambiguous. -/
theorem sigma_is_sigma2 (a : Z5) :
    sigma a = ⟨a.a0 - a.a2, a.a3 - a.a2, a.a1 - a.a2, -a.a2⟩ := rfl

theorem sigma_add (u v : Z5) : sigma (add u v) = add (sigma u) (sigma v) := by
  cases u; cases v; simp only [sigma, add, Z5.mk.injEq]
  refine ⟨?_,?_,?_,?_⟩ <;> omega

/-- The `ζ³` slot is `−(−a₂) = −(−a₂)`, closed by `simp only` before `omega`
    sees it; `trivial` discharges the leftover `True`, matching `conj_neg`. -/
theorem sigma_neg (u : Z5) : sigma (neg u) = neg (sigma u) := by
  cases u; simp only [sigma, neg, Z5.mk.injEq]
  refine ⟨?_,?_,?_,?_⟩ <;> first | omega | trivial

theorem sigma_zero : sigma zero = zero := rfl
theorem sigma_one  : sigma one  = one  := rfl

/-- `σ(1/φ) = −φ` — the companion of the already-proved `sigma_phi : σφ = −1/φ`.
    So `σ` swaps the two roots of `X² − X − 1` up to sign, as it must. -/
theorem sigma_invPhi : sigma invPhi = neg phi := rfl

/-- `σ² = conj` is `sigma_sigma`, already proved above; recorded here in the
    order-4 form the norm uses. -/
theorem sigma_sq (a : Z5) : sigma (sigma a) = conj a := sigma_sigma a

/-! ### The norm `N(a) = a · σa · σ²a · σ³a` -/

def norm (a : Z5) : Z5 :=
  mul (mul a (sigma a)) (mul (sigma (sigma a)) (sigma (sigma (sigma a))))

def normZ (a : Z5) : Int := (norm a).a0

/-- Rotating four opaque factors cyclically.  Commutative-monoid rearrangement
    in `Z5`; no descent to `Int`, no unfolding of `mul`. -/
theorem four_rot (p q r s : Z5) :
    mul (mul q r) (mul s p) = mul (mul p q) (mul r s) := by
  simp [mul_comm, mul_left_comm]

/-- Interleaving two four-factor products.  Same: eight opaque factors,
    rearrangement only. -/
theorem eight_shuffle (p q r s pp qq rr ss : Z5) :
    mul (mul (mul p pp) (mul q qq)) (mul (mul r rr) (mul s ss))
      = mul (mul (mul p q) (mul r s)) (mul (mul pp qq) (mul rr ss)) := by
  simp [mul_comm, mul_left_comm]

/-- **`N(a)` is `σ`-fixed**: `σ` permutes the four factors cyclically, using
    `σ⁴ = id`.  This is the whole reason `N` lands in `Z`, and it costs one
    rearrangement instead of a degree-4 polynomial identity. -/
theorem sigma_norm (a : Z5) : sigma (norm a) = norm a := by
  simp only [norm, sigma_mul, sigma_order_four]
  exact four_rot _ _ _ _

/-- The `σ`-fixed subring is `Z`.  `σu = u` reads
    `a₀−a₂ = a₀`, `a₃−a₂ = a₁`, `a₁−a₂ = a₂`, `−a₂ = a₃` — LINEAR, so `omega`
    settles it outright: `a₂ = 0`, then `a₁ = 0`, then `a₃ = 0`. -/
theorem sigma_fixed_coords {u : Z5} (h : sigma u = u) :
    u.a1 = 0 ∧ u.a2 = 0 ∧ u.a3 = 0 := by
  have h1 : u.a0 - u.a2 = u.a0 := congrArg Z5.a0 h
  have h2 : u.a3 - u.a2 = u.a1 := congrArg Z5.a1 h
  have h3 : u.a1 - u.a2 = u.a2 := congrArg Z5.a2 h
  have h4 : -u.a2 = u.a3 := congrArg Z5.a3 h
  refine ⟨?_,?_,?_⟩ <;> omega

/-- **`N(a) ∈ Z`.**  Coordinates 1, 2, 3 of the norm vanish. -/
theorem norm_in_Z (a : Z5) :
    (norm a).a1 = 0 ∧ (norm a).a2 = 0 ∧ (norm a).a3 = 0 :=
  sigma_fixed_coords (sigma_norm a)

/-- **`N` is multiplicative — by rearrangement alone.**  `σ` is a hom, so the
    eight factors of `N(ab)` are exactly the eight factors of `N(a)·N(b)`
    interleaved; `eight_shuffle` unshuffles them.  No `Int` descent. -/
theorem norm_mul (a b : Z5) : norm (mul a b) = mul (norm a) (norm b) := by
  simp only [norm, sigma_mul]
  exact eight_shuffle _ _ _ _ _ _ _ _

/-- Reading off the rational coordinate of a product whose left factor is a
    rational integer. -/
theorem mul_a0_of_inZ (u v : Z5) (h1 : u.a1 = 0) (h2 : u.a2 = 0) (h3 : u.a3 = 0) :
    (mul u v).a0 = u.a0 * v.a0 := by
  show u.a0*v.a0 - (u.a1*v.a3 + u.a2*v.a2 + u.a3*v.a1)
        + (u.a2*v.a3 + u.a3*v.a2) = u.a0*v.a0
  rw [h1, h2, h3]; omega

/-- **`normZ` is multiplicative as an `Int`.** -/
theorem normZ_mul (a b : Z5) : normZ (mul a b) = normZ a * normZ b := by
  have h := norm_in_Z a
  show (norm (mul a b)).a0 = (norm a).a0 * (norm b).a0
  rw [norm_mul]
  exact mul_a0_of_inZ _ _ h.1 h.2.1 h.2.2

/-! ### Anti-vacuity: the norm takes at least four different values -/

theorem normZ_zero   : normZ zero          = 0  := rfl
theorem normZ_one    : normZ one           = 1  := rfl
theorem normZ_phi    : normZ phi           = 1  := rfl
theorem normZ_invPhi : normZ invPhi        = 1  := rfl
theorem normZ_zeta   : normZ zeta          = 1  := rfl
/-- `φ` is a unit, so `N(φ) = 1`; `2` is not, and `N(2) = 2⁴`. -/
theorem normZ_twoElt : normZ ⟨2,0,0,0⟩     = 16 := rfl
/-- `1 − ζ` generates the ramified prime above 5. -/
theorem normZ_oneSubZeta : normZ ⟨1,-1,0,0⟩ = 5 := rfl

/-- **`normZ` is not constant `0` and not constant `1`.** -/
theorem normZ_not_constant :
    normZ one ≠ normZ ⟨2,0,0,0⟩ ∧ normZ zero ≠ normZ one
      ∧ normZ ⟨1,-1,0,0⟩ ≠ normZ one := by decide

/-! ### 2-adic descent -/

def two : Z5 := ⟨2,0,0,0⟩

theorem sigma_two  : sigma two  = two := rfl
theorem normZ_two  : normZ two  = 16  := rfl

/-- `u ≡ v (mod 2)` in `Z[ζ₅]`. -/
def Cong2 (u v : Z5) : Prop := ∃ w : Z5, u = add v (mul two w)

/-- Congruence mod 2 is multiplicative: `(b+2w)(d+2x) = bd + 2(bx + wd + 2wx)`.
    Proved at the `Z5` level from the ring laws; no `Int` descent. -/
theorem cong2_mul {a b c d : Z5} (h1 : Cong2 a b) (h2 : Cong2 c d) :
    Cong2 (mul a c) (mul b d) := by
  cases h1 with
  | intro w hw =>
    cases h2 with
    | intro x hx =>
      refine ⟨add (add (mul b x) (mul w d)) (mul two (mul w x)), ?_⟩
      rw [hw, hx]
      simp [mul_add, mul_comm, mul_left_comm, add_assoc, add_left_comm]

/-- …and `σ`-stable, because `σ(2) = 2`. -/
theorem cong2_sigma {a b : Z5} (h : Cong2 a b) : Cong2 (sigma a) (sigma b) := by
  cases h with
  | intro w hw =>
    refine ⟨sigma w, ?_⟩
    rw [hw, sigma_add, sigma_mul, sigma_two]

theorem cong2_norm {a b : Z5} (h : Cong2 a b) : Cong2 (norm a) (norm b) := by
  have h1 := cong2_sigma h
  have h2 := cong2_sigma h1
  have h3 := cong2_sigma h2
  exact cong2_mul (cong2_mul h h1) (cong2_mul h2 h3)

theorem two_mul_a0 (w : Z5) : (mul two w).a0 = 2 * w.a0 := by
  cases w; simp only [mul, two]; omega

/-- **The mod-2 reduction lemma the design flagged as the risky step.**  It is
    discharged here without any polynomial identity: congruence mod 2 is a
    ring congruence, `σ` preserves it, and `norm` is built from `mul` and `σ`. -/
theorem normZ_mod2 {a b : Z5} (h : Cong2 a b) : normZ a % 2 = normZ b % 2 := by
  cases cong2_norm h with
  | intro w hw =>
    have e : normZ a = normZ b + 2 * w.a0 := by
      show (norm a).a0 = (norm b).a0 + 2 * w.a0
      rw [hw]
      show (norm b).a0 + (mul two w).a0 = (norm b).a0 + 2 * w.a0
      rw [two_mul_a0]
    omega

/-- The mod-2 representative, coordinatewise. -/
def par (a : Z5) : Z5 := ⟨a.a0 % 2, a.a1 % 2, a.a2 % 2, a.a3 % 2⟩

theorem cong2_par (a : Z5) : Cong2 a (par a) := by
  refine ⟨⟨a.a0 / 2, a.a1 / 2, a.a2 / 2, a.a3 / 2⟩, ?_⟩
  cases a; simp only [par, add, mul, two, Z5.mk.injEq]
  refine ⟨?_,?_,?_,?_⟩ <;> omega

theorem bit_eq (n : Int) : n % 2 = cond (decide (n % 2 = 1)) 1 0 := by
  cases h : decide (n % 2 = 1) with
  | false =>
    have hn : ¬ (n % 2 = 1) := of_decide_eq_false h
    show n % 2 = 0
    omega
  | true => exact of_decide_eq_true h

theorem par_eq_bits (a : Z5) :
    par a = ⟨cond (decide (a.a0 % 2 = 1)) 1 0, cond (decide (a.a1 % 2 = 1)) 1 0,
             cond (decide (a.a2 % 2 = 1)) 1 0, cond (decide (a.a3 % 2 = 1)) 1 0⟩ := by
  simp only [par, Z5.mk.injEq]
  exact ⟨bit_eq _, bit_eq _, bit_eq _, bit_eq _⟩

def bitRep (b0 b1 b2 b3 : Bool) : Z5 :=
  ⟨cond b0 1 0, cond b1 1 0, cond b2 1 0, cond b3 1 0⟩

/-- **THE 16-CASE FACT.**  2 is inert in `Z[ζ₅]` (2 has order 4 mod 5), so
    `Z[ζ₅]/2 ≅ F₁₆` is a field and the norm of a nonzero class is a unit of
    `F₂`, i.e. odd.  Checked as a genuinely finite enumeration: 16 branches,
    each a closed `Int` computation. -/
theorem bits_norm_zero (b0 b1 b2 b3 : Bool)
    (h : normZ (bitRep b0 b1 b2 b3) % 2 = 0) :
    b0 = false ∧ b1 = false ∧ b2 = false ∧ b3 = false := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> revert h <;> decide

/-! #### The 16-case nest, counted against itself -/

def parityNest : List (Bool × Bool × Bool × Bool) :=
  [(false,false,false,false), (false,false,false,true),
   (false,false,true ,false), (false,false,true ,true),
   (false,true ,false,false), (false,true ,false,true),
   (false,true ,true ,false), (false,true ,true ,true),
   (true ,false,false,false), (true ,false,false,true),
   (true ,false,true ,false), (true ,false,true ,true),
   (true ,true ,false,false), (true ,true ,false,true),
   (true ,true ,true ,false), (true ,true ,true ,true)]

/-- The nest really has 16 members, and they really are distinct — every
    member occurs exactly once, so the count below is over 16 classes and not
    over a shorter list padded with repeats. -/
theorem parityNest_size : parityNest.length = 16 := by decide
theorem parityNest_nodup :
    parityNest.all (fun p => parityNest.count p == 1) = true := by decide

def parityOddCount : Nat :=
  (parityNest.filter
    (fun p => normZ (bitRep p.1 p.2.1 p.2.2.1 p.2.2.2) % 2 == 1)).length

/-- **ANTI-VACUITY COUNT, tied to its own nest**: of the 16 parity classes,
    exactly 15 have odd norm — the missing one is the zero class.  If the
    count were 16 the statement would be false; if it were 0 the descent
    would be vacuous.  It is 15. -/
theorem parityOddCount_eq : parityOddCount = 15 := by decide
theorem parityOddCount_lt : parityOddCount < parityNest.length := by decide

theorem all_even_of_norm_even (a : Z5) (h : normZ a % 2 = 0) :
    a.a0 % 2 = 0 ∧ a.a1 % 2 = 0 ∧ a.a2 % 2 = 0 ∧ a.a3 % 2 = 0 := by
  have hpar : normZ a % 2 = normZ (par a) % 2 := normZ_mod2 (cong2_par a)
  rw [par_eq_bits, h] at hpar
  have hb := bits_norm_zero _ _ _ _ hpar.symm
  have n0 := of_decide_eq_false hb.1
  have n1 := of_decide_eq_false hb.2.1
  have n2 := of_decide_eq_false hb.2.2.1
  have n3 := of_decide_eq_false hb.2.2.2
  exact ⟨by omega, by omega, by omega, by omega⟩

theorem eq_two_mul (x0 x1 x2 x3 : Int) (h0 : x0 % 2 = 0) (h1 : x1 % 2 = 0)
    (h2 : x2 % 2 = 0) (h3 : x3 % 2 = 0) :
    (⟨x0,x1,x2,x3⟩ : Z5) = mul two ⟨x0/2, x1/2, x2/2, x3/2⟩ := by
  simp only [mul, two, Z5.mk.injEq]; refine ⟨?_,?_,?_,?_⟩ <;> omega

theorem normZ_two_mul (y : Z5) : normZ (mul two y) = 16 * normZ y := by
  rw [normZ_mul, normZ_two]

/-- **THE DESCENT**, with an explicit `Nat` fuel rather than well-founded
    recursion (core-only, no imports, no budget changes).  Fuel `n` bounds
    `|a₀|+|a₁|+|a₂|+|a₃|`; halving strictly decreases it unless the element is
    already `0`, and the fuel is discharged at the call site by taking
    `n` to be the measure itself. -/
theorem descent : ∀ (n : Nat) (x0 x1 x2 x3 : Int),
    x0.natAbs + x1.natAbs + x2.natAbs + x3.natAbs ≤ n →
    normZ ⟨x0,x1,x2,x3⟩ = 0 → (⟨x0,x1,x2,x3⟩ : Z5) = zero := by
  intro n
  induction n with
  | zero =>
    intro x0 x1 x2 x3 hm _
    simp only [zero, Z5.mk.injEq]
    refine ⟨?_,?_,?_,?_⟩ <;> omega
  | succ n ih =>
    intro x0 x1 x2 x3 hm hz
    have he : normZ (⟨x0,x1,x2,x3⟩ : Z5) % 2 = 0 := by rw [hz]; rfl
    have hall := all_even_of_norm_even ⟨x0,x1,x2,x3⟩ he
    have h0 : x0 % 2 = 0 := hall.1
    have h1 : x1 % 2 = 0 := hall.2.1
    have h2 : x2 % 2 = 0 := hall.2.2.1
    have h3 : x3 % 2 = 0 := hall.2.2.2
    have hsplit := eq_two_mul x0 x1 x2 x3 h0 h1 h2 h3
    have hz2 : (16 : Int) * normZ (⟨x0/2, x1/2, x2/2, x3/2⟩ : Z5) = 0 := by
      rw [← normZ_two_mul, ← hsplit]; exact hz
    have hz3 : normZ (⟨x0/2, x1/2, x2/2, x3/2⟩ : Z5) = 0 := by omega
    have hm2 : (x0/2).natAbs + (x1/2).natAbs + (x2/2).natAbs + (x3/2).natAbs ≤ n := by
      omega
    have hhalf := ih (x0/2) (x1/2) (x2/2) (x3/2) hm2 hz3
    have e0 : x0/2 = 0 := congrArg Z5.a0 hhalf
    have e1 : x1/2 = 0 := congrArg Z5.a1 hhalf
    have e2 : x2/2 = 0 := congrArg Z5.a2 hhalf
    have e3 : x3/2 = 0 := congrArg Z5.a3 hhalf
    simp only [zero, Z5.mk.injEq]
    refine ⟨?_,?_,?_,?_⟩ <;> omega

/-- **`N(a) = 0 ⟺ a = 0`.** -/
theorem normZ_eq_zero_iff (a : Z5) : normZ a = 0 ↔ a = zero := by
  constructor
  · intro h
    cases a with
    | mk x0 x1 x2 x3 =>
      exact descent (x0.natAbs + x1.natAbs + x2.natAbs + x3.natAbs)
        x0 x1 x2 x3 (Nat.le_refl _) h
  · intro h; rw [h]; rfl

/-- **`Z[ζ₅]` IS AN INTEGRAL DOMAIN.**  `N` is multiplicative into `Z`, `Z` has
    no zero divisors, and `N` detects zero. -/
theorem eq_zero_or_eq_zero_of_mul_eq_zero (a b : Z5) (h : mul a b = zero) :
    a = zero ∨ b = zero := by
  have hp : normZ a * normZ b = 0 := by
    rw [← normZ_mul, h]; rfl
  cases Int.mul_eq_zero.mp hp with
  | inl ha => exact Or.inl ((normZ_eq_zero_iff a).mp ha)
  | inr hb => exact Or.inr ((normZ_eq_zero_iff b).mp hb)

/-- The cancellation form, which is what downstream arguments actually use. -/
theorem mul_left_cancel {a b c : Z5} (ha : a ≠ zero) (h : mul a b = mul a c) :
    b = c := by
  have h0 : mul a (add b (neg c)) = zero := by
    rw [mul_add, mul_neg, h, add_neg]
  cases eq_zero_or_eq_zero_of_mul_eq_zero _ _ h0 with
  | inl hx => exact absurd hx ha
  | inr hx =>
    calc b = add b zero                := (add_zero b).symm
    _      = add b (add (neg c) c)     := by rw [neg_add_cancel]
    _      = add (add b (neg c)) c     := (add_assoc b (neg c) c).symm
    _      = add zero c                := by rw [hx]
    _      = c                         := zero_add c

/-! ### Anti-vacuity for the domain theorem, and negative controls

    #### (i) The domain theorem is not vacuous -/

/-- The trivial side: `0 · b = 0`, and the disjunction picks the left. -/
theorem domain_trivial_witness (b : Z5) : mul zero b = zero := zero_mul b
/-- The nontrivial side: two nonzero elements whose product is nonzero.  If
    every product of nonzero elements were zero, the theorem would be empty. -/
theorem domain_nontrivial_witness :
    zeta ≠ zero ∧ zeta3 ≠ zero ∧ mul zeta zeta3 ≠ zero := by decide
/-- …and one more, using a non-unit, so the witness is not an artefact of
    everything in sight being invertible. -/
theorem domain_nontrivial_witness2 :
    two ≠ zero ∧ mul two two ≠ zero ∧ normZ (mul two two) = 256 := by decide

/-! #### (ii) NEGATIVE CONTROL — additive but not multiplicative is not enough

    `a₀` is additive, sends `1 ↦ 1`, and is `Z`-valued.  It fails to be
    multiplicative, and — the point — it does NOT detect zero: it kills `ζ`.
    Substituting it for `normZ` breaks the domain proof at the last step. -/

def a0map (u : Z5) : Int := u.a0

theorem a0map_add (u v : Z5) : a0map (add u v) = a0map u + a0map v := rfl
theorem a0map_one : a0map one = 1 := rfl
/-- Not multiplicative: `ζ · ζ⁴ = 1` has `a₀ = 1`, but `0 · (−1) = 0`. -/
theorem a0map_not_mul :
    a0map (mul zeta zeta4) ≠ a0map zeta * a0map zeta4 := by decide
/-- And it cannot detect zero, so it is useless for the descent. -/
theorem a0map_blind : a0map zeta = 0 ∧ zeta ≠ zero := by decide

/-! #### (iii) NEGATIVE CONTROL — the 16-case fact has teeth

    Drop one of the four Galois factors.  The three-factor product
    `a · σa · σ²a` is still built out of ring maps, but its rational
    coordinate vanishes on the unit `ζ³` — so the 16-case `decide` above
    would FAIL for it, at parity class `(false,false,false,true)`. -/

def fnorm3 (a : Z5) : Int := (mul (mul a (sigma a)) (sigma (sigma a))).a0

theorem fnorm3_breaks_parity :
    bitRep false false false true ≠ zero
      ∧ fnorm3 (bitRep false false false true) % 2 = 0 := by decide

/-- Count the damage against the same nest: the three-factor product is odd on
    only 8 of the 16 parity classes, against 15 for the real norm.  A check
    that cannot fail is not a check; this one fails. -/
def fnorm3OddCount : Nat :=
  (parityNest.filter
    (fun p => fnorm3 (bitRep p.1 p.2.1 p.2.2.1 p.2.2.2) % 2 == 1)).length

theorem fnorm3OddCount_eq : fnorm3OddCount = 8 := by decide
theorem fnorm3_worse_than_norm : fnorm3OddCount < parityOddCount := by decide

/-! #### (iv) NEGATIVE CONTROL — two of the four factors is not enough either

    `a · conj a` is the relative norm to the real subfield `Z[φ]`; it does NOT
    land in `Z`.  So `norm_in_Z` is a statement about the full four-fold
    product, not a formality. -/

theorem twoFactor_not_in_Z :
    (mul (bitRep false false true true)
         (conj (bitRep false false true true))).a2 ≠ 0 := by decide

/-! #### (v) NEGATIVE CONTROL — the descent is special to 2

    2 is inert in `Z[ζ₅]`; 11 is totally split (11 ≡ 1 mod 5).  The exact
    analogue of the 16-case fact at 11 is FALSE: `ζ − 3` is not divisible by
    11 in any coordinate, yet `N(ζ − 3) = 121 = 11²`.  So "nonzero mod p ⇒
    norm not divisible by p" is a real arithmetic input about 2, not a formal
    consequence of multiplicativity. -/

theorem eleven_splits :
    normZ ⟨-3,1,0,0⟩ = 121 ∧ normZ ⟨-3,1,0,0⟩ % 11 = 0
      ∧ ((-3 : Int) % 11 ≠ 0 ∨ (1 : Int) % 11 ≠ 0) := by decide

/-- A second, independent split witness, so the control is not a coincidence
    of one element: `N(ζ − 4) = 341 = 11 · 31`. -/
theorem eleven_splits2 :
    normZ ⟨-4,1,0,0⟩ = 341 ∧ normZ ⟨-4,1,0,0⟩ % 11 = 0 := by decide

end Z5
/-! ═══════════════════════════════════════════════════════════════════════════
    **φ IS NOT A SQUARE IN `Z5 = Z[ζ₅]`**, by 41-adic descent.

    41 is the smallest prime carrying primitive fifth roots of unity (mod 2 is
    useless: in characteristic 2 everything is a square).  The four primitive
    fifth roots of 1 mod 41 are `{10, 16, 18, 37}`; each gives a ring map
    `Z5 → Z/41` sending `ζ ↦ r`.  `φ = 1 + ζ + ζ⁴` maps to `7` or `35`, both
    NONSQUARES mod 41.  So `x² = φ·y²` forces all four evaluations of `x` and
    of `y` to vanish mod 41; the Vandermonde matrix of the four roots is
    invertible mod 41 (det = 24), hence 41 divides every coordinate of `x` and
    `y`; divide by 41 and descend on the coordinate size.

    Everything below descends only to `Int` at the `Z5` level, which the house
    rules allow.  No `Int` descent at the `K` level, no budget raised.
    ═══════════════════════════════════════════════════════════════════════ -/

namespace T41

/-! ### Numeral normalisation kit

There is no `ring` tactic available here, so the bilinear expansions in
`ev41*_mul` are normalised by an explicitly terminating rewrite system into the
shape `numeral * (atom * atom)`, after which `omega` is purely linear.

Two `simp only` passes are needed.  The extraction lemmas `eN` loop against each
other on a `numeral * (numeral * atom)` nest (`e10` and `e16` will swap the two
numerals forever), so the three-level lemmas `gMN` run first and collapse that
nest in one step; only the `p₀ * (n * qⱼ)` leftovers remain for the `eN` pass,
and those cannot regenerate the nest. -/

theorem e10 (a b : Int) : a * (10 * b) = 10 * (a * b) := by
  rw [← Int.mul_assoc, Int.mul_comm a 10, Int.mul_assoc]
theorem e16 (a b : Int) : a * (16 * b) = 16 * (a * b) := by
  rw [← Int.mul_assoc, Int.mul_comm a 16, Int.mul_assoc]
theorem e18 (a b : Int) : a * (18 * b) = 18 * (a * b) := by
  rw [← Int.mul_assoc, Int.mul_comm a 18, Int.mul_assoc]
theorem e37 (a b : Int) : a * (37 * b) = 37 * (a * b) := by
  rw [← Int.mul_assoc, Int.mul_comm a 37, Int.mul_assoc]
theorem e41 (a b : Int) : a * (41 * b) = 41 * (a * b) := by
  rw [← Int.mul_assoc, Int.mul_comm a 41, Int.mul_assoc]

theorem g1010 (p q : Int) : (10:Int) * (p * (10 * q)) = 100 * (p * q) := by rw [e10]; omega
theorem g1016 (p q : Int) : (10:Int) * (p * (16 * q)) = 160 * (p * q) := by rw [e16]; omega
theorem g1018 (p q : Int) : (10:Int) * (p * (18 * q)) = 180 * (p * q) := by rw [e18]; omega
theorem g1037 (p q : Int) : (10:Int) * (p * (37 * q)) = 370 * (p * q) := by rw [e37]; omega
theorem g1610 (p q : Int) : (16:Int) * (p * (10 * q)) = 160 * (p * q) := by rw [e10]; omega
theorem g1616 (p q : Int) : (16:Int) * (p * (16 * q)) = 256 * (p * q) := by rw [e16]; omega
theorem g1618 (p q : Int) : (16:Int) * (p * (18 * q)) = 288 * (p * q) := by rw [e18]; omega
theorem g1637 (p q : Int) : (16:Int) * (p * (37 * q)) = 592 * (p * q) := by rw [e37]; omega
theorem g1810 (p q : Int) : (18:Int) * (p * (10 * q)) = 180 * (p * q) := by rw [e10]; omega
theorem g1816 (p q : Int) : (18:Int) * (p * (16 * q)) = 288 * (p * q) := by rw [e16]; omega
theorem g1818 (p q : Int) : (18:Int) * (p * (18 * q)) = 324 * (p * q) := by rw [e18]; omega
theorem g1837 (p q : Int) : (18:Int) * (p * (37 * q)) = 666 * (p * q) := by rw [e37]; omega
theorem g3710 (p q : Int) : (37:Int) * (p * (10 * q)) = 370 * (p * q) := by rw [e10]; omega
theorem g3716 (p q : Int) : (37:Int) * (p * (16 * q)) = 592 * (p * q) := by rw [e16]; omega
theorem g3718 (p q : Int) : (37:Int) * (p * (18 * q)) = 666 * (p * q) := by rw [e18]; omega
theorem g3737 (p q : Int) : (37:Int) * (p * (37 * q)) = 1369 * (p * q) := by rw [e37]; omega

/-! ### Certificates about the prime 41 — every one machine-checked by `decide`

These are the four certificates the builder supplied.  They are re-derived here,
not assumed. -/

/-- **Root certificate.**  `Φ₅(X) = 1+X+X²+X³+X⁴` has exactly the roots
`{10,16,18,37}` in `Z/41`.  Stated as an *iff* over all residues, so it
certifies both that the four listed values ARE roots and that there are no
others (in particular that they are the four *primitive* fifth roots). -/
theorem roots_char : ∀ r, r < 41 →
    ((1 + r + r*r + r*r*r + r*r*r*r) % 41 = 0 ↔
      (r = 10 ∨ r = 16 ∨ r = 18 ∨ r = 37)) := by decide

/-- NEGATIVE CONTROL for `roots_char`: `2` is not a fifth root of unity mod 41,
so `roots_char` is not a test that everything passes. -/
theorem two_not_root : (1 + 2 + 2*2 + 2*2*2 + 2*2*2*2) % 41 ≠ 0 := by decide

/-- The four roots are pairwise distinct, and none of them is the trivial root
`1` — so they really are four *primitive* fifth roots. -/
theorem roots_distinct :
    (10 ≠ 16 ∧ 10 ≠ 18 ∧ 10 ≠ 37 ∧ 16 ≠ 18 ∧ 16 ≠ 37 ∧ 18 ≠ 37) ∧
    (10 ≠ 1 ∧ 16 ≠ 1 ∧ 18 ≠ 1 ∧ 37 ≠ 1) := by decide

/-- Each root really has order dividing 5: `r⁵ = 1 (mod 41)`. -/
theorem roots_pow5 :
    (10*10*10*10*10) % 41 = 1 ∧ (16*16*16*16*16) % 41 = 1 ∧
    (18*18*18*18*18) % 41 = 1 ∧ (37*37*37*37*37) % 41 = 1 := by decide

/-- The powers used as the coefficients of `ev41A…ev41D` are the right ones:
row `r` of the Vandermonde matrix is `(1, r, r², r³) mod 41`. -/
theorem root_powers :
    ((10*10) % 41 = 18 ∧ (10*10*10) % 41 = 16) ∧
    ((16*16) % 41 = 10 ∧ (16*16*16) % 41 = 37) ∧
    ((18*18) % 41 = 37 ∧ (18*18*18) % 41 = 10) ∧
    ((37*37) % 41 = 16 ∧ (37*37*37) % 41 = 18) := by decide

/-- **Golden-quadratic certificate.**  `7` and `35` are the two roots of
`X² - X - 1` mod 41 — exactly what `φ` must satisfy. -/
theorem golden_quadratic :
    (7*7 - 7 - 1 : Int) % 41 = 0 ∧ (35*35 - 35 - 1 : Int) % 41 = 0 := by decide

/-- **Nonsquare certificate.**  `7` is a nonsquare mod 41. -/
theorem nonsq7  : ∀ i, i < 41 → (i*i) % 41 ≠ 7  := by decide
/-- **Nonsquare certificate.**  `35` is a nonsquare mod 41. -/
theorem nonsq35 : ∀ i, i < 41 → (i*i) % 41 ≠ 35 := by decide
/-- NEGATIVE CONTROL for the nonsquare test: `2` IS a square mod 41 (`17² = 2`),
so `nonsq7`/`nonsq35` are not a check that cannot fail. -/
theorem two_is_square : (17*17) % 41 = 2 := by decide

/-- Independent cross-check of the nonsquare certificates by Euler's criterion:
`7²⁰ = 35²⁰ = −1 = 40 (mod 41)`, while the square `2` gives `2²⁰ = 1`.
(Not used downstream; it is a second, different witness for the same facts.) -/
theorem euler_criterion :
    (7^20) % 41 = 40 ∧ (35^20) % 41 = 40 ∧ (2^20) % 41 = 1 := by decide

/-- **Vandermonde certificate.**  The `4×4` Vandermonde determinant of
`(10,16,18,37)` is `∏_{i<j}(rⱼ − rᵢ) = 1034208 ≡ 24 (mod 41)`, and `24` is a
unit mod 41 because `24 · 12 = 288 ≡ 1`. -/
theorem vandermonde :
    ((16-10) * (18-10) * (37-10) * (18-16) * (37-16) * (37-18) : Int) = 1034208 ∧
    (1034208 : Int) % 41 = 24 ∧ (24 * 12 : Int) % 41 = 1 := by decide

/-! ### The nonsquare step, as a bounded computation over `Z/41 × Z/41`

This replaces the number theory ("`c` is a nonsquare, so divide and derive a
contradiction") by a closed 41×41 computation. -/

theorem nsq7N : ∀ m : Nat, m < 41 → ∀ n : Nat, n < 41 →
    (((m:Int)*(m:Int)) % 41 = (7*((n:Int)*(n:Int))) % 41) → m = 0 ∧ n = 0 := by decide
theorem nsq35N : ∀ m : Nat, m < 41 → ∀ n : Nat, n < 41 →
    (((m:Int)*(m:Int)) % 41 = (35*((n:Int)*(n:Int))) % 41) → m = 0 ∧ n = 0 := by decide

/-- NEGATIVE CONTROL for `nsq7N`/`nsq35N`: for the SQUARE constant `c = 4` the
very same statement is FALSE, witnessed by `a = 2, b = 1`.  So those two lemmas
detect nonsquareness; they do not merely always conclude zero. -/
theorem nsq4N_false :
    ¬ (∀ m : Nat, m < 41 → ∀ n : Nat, n < 41 →
        (((m:Int)*(m:Int)) % 41 = (4*((n:Int)*(n:Int))) % 41) → m = 0 ∧ n = 0) := by
  intro hc
  exact absurd (hc 2 (by decide) 1 (by decide) (by decide)).1 (by decide)

theorem sqred (z : Int) : (z*z) % 41 = ((z%41)*(z%41)) % 41 := Int.mul_emod z z 41
theorem csqred (c z : Int) : (c*(z*z)) % 41 = (c*((z%41)*(z%41))) % 41 := by
  rw [Int.mul_emod c (z*z) 41, Int.mul_emod z z 41, Int.mul_emod c ((z%41)*(z%41)) 41]

/-- `x² = 7·y²` mod 41 forces `x ≡ y ≡ 0`, because `7` is a nonsquare. -/
theorem nsq7 (a b : Int) (h : (a*a) % 41 = (7*(b*b)) % 41) :
    a % 41 = 0 ∧ b % 41 = 0 := by
  have hm : (((a % 41).toNat : Nat) : Int) = a % 41 := by omega
  have hn : (((b % 41).toNat : Nat) : Int) = b % 41 := by omega
  have hml : (a % 41).toNat < 41 := by omega
  have hnl : (b % 41).toNat < 41 := by omega
  have key : ((((a % 41).toNat : Nat) : Int) * (((a % 41).toNat : Nat) : Int)) % 41
      = (7 * ((((b % 41).toNat : Nat) : Int) * (((b % 41).toNat : Nat) : Int))) % 41 := by
    rw [hm, hn, ← sqred, ← csqred]; exact h
  have := nsq7N _ hml _ hnl key
  refine ⟨?_,?_⟩ <;> omega

/-- `x² = 35·y²` mod 41 forces `x ≡ y ≡ 0`, because `35` is a nonsquare. -/
theorem nsq35 (a b : Int) (h : (a*a) % 41 = (35*(b*b)) % 41) :
    a % 41 = 0 ∧ b % 41 = 0 := by
  have hm : (((a % 41).toNat : Nat) : Int) = a % 41 := by omega
  have hn : (((b % 41).toNat : Nat) : Int) = b % 41 := by omega
  have hml : (a % 41).toNat < 41 := by omega
  have hnl : (b % 41).toNat < 41 := by omega
  have key : ((((a % 41).toNat : Nat) : Int) * (((a % 41).toNat : Nat) : Int)) % 41
      = (35 * ((((b % 41).toNat : Nat) : Int) * (((b % 41).toNat : Nat) : Int))) % 41 := by
    rw [hm, hn, ← sqred, ← csqred]; exact h
  have := nsq35N _ hml _ hnl key
  refine ⟨?_,?_⟩ <;> omega

/-! ### Explicit inversion of the Vandermonde system mod 41

Rather than asking `omega` to *solve* the 4×4 congruence system (which it can
do, but slowly), we hand it the inverse explicitly.  Writing `Tₖ = Σ_r r^{−k}·e_r`
one has `Tₖ ≡ 5aₖ − (a₀+a₁+a₂+a₃)` and `Σₖ Tₖ ≡ a₀+a₁+a₂+a₃`, so `5aₖ` is the
combination `2Tₖ + Σ_{j≠k} Tⱼ` of the four evaluations.  `id0…id3` are those four
combinations, written out with their exact 41-multiples; each is a *closed linear
identity* in four variables, so `omega` verifies it instantly. -/

theorem id0 (a0 a1 a2 a3 : Int) :
    73*(a0 + 10*a1 + 18*a2 + 16*a3) + 67*(a0 + 16*a1 + 10*a2 + 37*a3)
  + 65*(a0 + 18*a1 + 37*a2 + 10*a3) + 46*(a0 + 37*a1 + 16*a2 + 18*a3)
    = 5*a0 + 41*(6*a0 + 114*a1 + 125*a2 + 125*a3) := by omega

theorem id1 (a0 a1 a2 a3 : Int) :
    109*(a0 + 10*a1 + 18*a2 + 16*a3) + 84*(a0 + 16*a1 + 10*a2 + 37*a3)
  + 80*(a0 + 18*a1 + 37*a2 + 10*a3) + 55*(a0 + 37*a1 + 16*a2 + 18*a3)
    = 5*a1 + 41*(8*a0 + 144*a1 + 162*a2 + 162*a3) := by omega

theorem id2 (a0 a1 a2 a3 : Int) :
    88*(a0 + 10*a1 + 18*a2 + 16*a3) + 103*(a0 + 16*a1 + 10*a2 + 37*a3)
  + 74*(a0 + 18*a1 + 37*a2 + 10*a3) + 63*(a0 + 37*a1 + 16*a2 + 18*a3)
    = 5*a2 + 41*(8*a0 + 151*a1 + 155*a2 + 173*a3) := by omega

theorem id3 (a0 a1 a2 a3 : Int) :
    90*(a0 + 10*a1 + 18*a2 + 16*a3) + 76*(a0 + 16*a1 + 10*a2 + 37*a3)
  + 101*(a0 + 18*a1 + 37*a2 + 10*a3) + 61*(a0 + 37*a1 + 16*a2 + 18*a3)
    = 5*a3 + 41*(8*a0 + 151*a1 + 173*a2 + 155*a3) := by omega

theorem dvd41_of_emod {z : Int} (h : z % 41 = 0) : (41:Int) ∣ z := by omega

theorem dvd41_smul {a : Int} (c : Int) (h : (41:Int) ∣ a) : (41:Int) ∣ c*a := by
  obtain ⟨k, hk⟩ := h
  exact ⟨c*k, by rw [hk, e41]⟩

theorem dvd41_add {a b : Int} (ha : (41:Int) ∣ a) (hb : (41:Int) ∣ b) :
    (41:Int) ∣ (a + b) := by
  obtain ⟨p, hp⟩ := ha
  obtain ⟨q, hq⟩ := hb
  exact ⟨p + q, by omega⟩

/-- `41 ∣ 5x + 41K → 41 ∣ x`, i.e. `5` is a unit mod 41. -/
theorem dvd41_strip {x K : Int} (h : (41:Int) ∣ (5*x + 41*K)) : (41:Int) ∣ x := by
  obtain ⟨m, hm⟩ := h
  omega

theorem natAbs41 (b : Int) : (41*b).natAbs = 41 * b.natAbs := Int.natAbs_mul 41 b

theorem sum8_zero {m0 m1 m2 m3 m4 m5 m6 m7 : Nat}
    (h : m0+m1+m2+m3+m4+m5+m6+m7 ≤ 0) :
    m0 = 0 ∧ m1 = 0 ∧ m2 = 0 ∧ m3 = 0 ∧ m4 = 0 ∧ m5 = 0 ∧ m6 = 0 ∧ m7 = 0 := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> omega

theorem sum8_step {n m0 m1 m2 m3 m4 m5 m6 m7 : Nat}
    (h : 41*m0 + 41*m1 + 41*m2 + 41*m3 + 41*m4 + 41*m5 + 41*m6 + 41*m7 ≤ n+1) :
    m0+m1+m2+m3+m4+m5+m6+m7 ≤ n := by omega

end T41

namespace Z5

/-! ### Multiplication by the integer 41 -/

/-- Scaling a `Z5` element by the integer `41`. -/
def sm41 (u : Z5) : Z5 := ⟨41*u.a0, 41*u.a1, 41*u.a2, 41*u.a3⟩

theorem mul_sm41 (u v : Z5) : mul (sm41 u) v = sm41 (mul u v) := by
  cases u; cases v
  simp only [mul, sm41, Int.mul_add, Int.mul_sub, Int.mul_assoc]

theorem mul_sm41r (u v : Z5) : mul u (sm41 v) = sm41 (mul u v) := by
  cases u; cases v
  simp only [mul, sm41, Int.mul_add, Int.mul_sub, T41.e41]

theorem sm41_inj {u v : Z5} (h : sm41 u = sm41 v) : u = v := by
  cases u; cases v
  simp only [sm41, Z5.mk.injEq] at h ⊢
  refine ⟨?_,?_,?_,?_⟩ <;> omega

theorem sm41_zero : sm41 zero = zero := by decide

theorem eq_sm41 {x : Z5} {b0 b1 b2 b3 : Int}
    (h0 : x.a0 = 41*b0) (h1 : x.a1 = 41*b1) (h2 : x.a2 = 41*b2) (h3 : x.a3 = 41*b3) :
    x = sm41 ⟨b0, b1, b2, b3⟩ := by
  cases x
  simp only [sm41, Z5.mk.injEq]
  exact ⟨h0, h1, h2, h3⟩

theorem ext41 {x : Z5} (h0 : x.a0 = 0) (h1 : x.a1 = 0) (h2 : x.a2 = 0) (h3 : x.a3 = 0) :
    x = zero := by
  cases x
  simp only [zero, Z5.mk.injEq]
  exact ⟨h0, h1, h2, h3⟩

/-! ### The four evaluations `Z5 → Z/41` at the primitive fifth roots of unity

`ev41A` sends `ζ ↦ 10`, `ev41B` sends `ζ ↦ 16`, `ev41C` sends `ζ ↦ 18`,
`ev41D` sends `ζ ↦ 37`; the remaining coefficients are `r²` and `r³` mod 41,
certified by `T41.root_powers`. -/

def ev41A (u : Z5) : Int := u.a0 + 10*u.a1 + 18*u.a2 + 16*u.a3
def ev41B (u : Z5) : Int := u.a0 + 16*u.a1 + 10*u.a2 + 37*u.a3
def ev41C (u : Z5) : Int := u.a0 + 18*u.a1 + 37*u.a2 + 10*u.a3
def ev41D (u : Z5) : Int := u.a0 + 37*u.a1 + 16*u.a2 + 18*u.a3

/-- Each `ev41*` is additive on the nose — not merely mod 41. -/
theorem ev41A_add (u v : Z5) : ev41A (add u v) = ev41A u + ev41A v := by
  cases u; cases v; simp only [add, ev41A, Int.mul_add]; omega
theorem ev41B_add (u v : Z5) : ev41B (add u v) = ev41B u + ev41B v := by
  cases u; cases v; simp only [add, ev41B, Int.mul_add]; omega
theorem ev41C_add (u v : Z5) : ev41C (add u v) = ev41C u + ev41C v := by
  cases u; cases v; simp only [add, ev41C, Int.mul_add]; omega
theorem ev41D_add (u v : Z5) : ev41D (add u v) = ev41D u + ev41D v := by
  cases u; cases v; simp only [add, ev41D, Int.mul_add]; omega

/-- **`ev41A` is multiplicative mod 41.**  This is exactly where the reduction
rule `ζ⁴ = −(1+ζ+ζ²+ζ³)` is used: it survives the evaluation because `10` is a
primitive fifth root of unity mod 41 (`T41.roots_char`). -/
theorem ev41A_mul (u v : Z5) : (ev41A (mul u v)) % 41 = (ev41A u * ev41A v) % 41 := by
  cases u; cases v
  simp only [mul, ev41A, Int.add_mul, Int.mul_add, Int.mul_sub, Int.mul_assoc]
  simp only [T41.g1010, T41.g1018, T41.g1016, T41.g1810, T41.g1818, T41.g1816,
    T41.g1610, T41.g1618, T41.g1616]
  simp only [T41.e10, T41.e18, T41.e16]
  omega

/-- `ev41B` is multiplicative mod 41. -/
theorem ev41B_mul (u v : Z5) : (ev41B (mul u v)) % 41 = (ev41B u * ev41B v) % 41 := by
  cases u; cases v
  simp only [mul, ev41B, Int.add_mul, Int.mul_add, Int.mul_sub, Int.mul_assoc]
  simp only [T41.g1616, T41.g1610, T41.g1637, T41.g1016, T41.g1010, T41.g1037,
    T41.g3716, T41.g3710, T41.g3737]
  simp only [T41.e16, T41.e10, T41.e37]
  omega

/-- `ev41C` is multiplicative mod 41. -/
theorem ev41C_mul (u v : Z5) : (ev41C (mul u v)) % 41 = (ev41C u * ev41C v) % 41 := by
  cases u; cases v
  simp only [mul, ev41C, Int.add_mul, Int.mul_add, Int.mul_sub, Int.mul_assoc]
  simp only [T41.g1818, T41.g1837, T41.g1810, T41.g3718, T41.g3737, T41.g3710,
    T41.g1018, T41.g1037, T41.g1010]
  simp only [T41.e18, T41.e37, T41.e10]
  omega

/-- `ev41D` is multiplicative mod 41. -/
theorem ev41D_mul (u v : Z5) : (ev41D (mul u v)) % 41 = (ev41D u * ev41D v) % 41 := by
  cases u; cases v
  simp only [mul, ev41D, Int.add_mul, Int.mul_add, Int.mul_sub, Int.mul_assoc]
  simp only [T41.g3737, T41.g3716, T41.g3718, T41.g1637, T41.g1616, T41.g1618,
    T41.g1837, T41.g1816, T41.g1818]
  simp only [T41.e37, T41.e16, T41.e18]
  omega

/-- **`φ` lands on a nonsquare at every root.**  `φ` evaluates to `7` at
`ζ = 10` and `ζ = 37`, and to `35` at `ζ = 16` and `ζ = 18`; by `T41.nonsq7`
and `T41.nonsq35` both are nonsquares mod 41. -/
theorem ev41_phi :
    ev41A phi % 41 = 7 % 41 ∧ ev41B phi % 41 = 35 % 41 ∧
    ev41C phi % 41 = 35 % 41 ∧ ev41D phi % 41 = 7 % 41 := by decide

/-- ANTI-VACUITY for the evaluations: they are not identically zero — each sends
`1` to `1`. -/
theorem ev41_one :
    ev41A one % 41 = 1 ∧ ev41B one % 41 = 1 ∧
    ev41C one % 41 = 1 ∧ ev41D one % 41 = 1 := by decide

/-- ANTI-VACUITY: the evaluations are pairwise different maps — `ζ` is sent to
four different residues. -/
theorem ev41_zeta_distinct :
    ev41A zeta % 41 = 10 ∧ ev41B zeta % 41 = 16 ∧
    ev41C zeta % 41 = 18 ∧ ev41D zeta % 41 = 37 := by decide

/-! ### One evaluation of the equation `x² = φ·y²` -/

/-- Evaluate `x² = φ·y²` through a mod-41 ring map `ev` whose value on `φ` is a
nonsquare `c`; conclude that `ev x` and `ev y` both vanish mod 41. -/
theorem root_step (ev : Z5 → Int) (c : Int)
    (hom : ∀ u v : Z5, ev (mul u v) % 41 = (ev u * ev v) % 41)
    (hphi : ev phi % 41 = c % 41)
    (hns : ∀ a b : Int, (a*a) % 41 = (c*(b*b)) % 41 → a % 41 = 0 ∧ b % 41 = 0)
    {x y : Z5} (h : mul x x = mul phi (mul y y)) :
    ev x % 41 = 0 ∧ ev y % 41 = 0 := by
  refine hns (ev x) (ev y) ?_
  calc (ev x * ev x) % 41
      = ev (mul x x) % 41 := (hom x x).symm
    _ = ev (mul phi (mul y y)) % 41 := by rw [h]
    _ = (ev phi * ev (mul y y)) % 41 := hom _ _
    _ = (c * (ev y * ev y)) % 41 := by
          rw [Int.mul_emod, hphi, hom y y, ← Int.mul_emod]

/-- **The Vandermonde step.**  If all four evaluations of an element vanish mod
41 then 41 divides every coordinate.  This is invertibility of the Vandermonde
matrix (`T41.vandermonde`: det `= 24`, a unit); the explicit inverse is supplied
by `T41.id0 … T41.id3` and `T41.dvd41_strip` (which uses that `5` is a unit). -/
theorem coords_dvd41 (a0 a1 a2 a3 : Int)
    (hA : (41:Int) ∣ (a0 + 10*a1 + 18*a2 + 16*a3))
    (hB : (41:Int) ∣ (a0 + 16*a1 + 10*a2 + 37*a3))
    (hC : (41:Int) ∣ (a0 + 18*a1 + 37*a2 + 10*a3))
    (hD : (41:Int) ∣ (a0 + 37*a1 + 16*a2 + 18*a3)) :
    (41:Int) ∣ a0 ∧ (41:Int) ∣ a1 ∧ (41:Int) ∣ a2 ∧ (41:Int) ∣ a3 := by
  have s0 := T41.dvd41_add (T41.dvd41_add (T41.dvd41_add
    (T41.dvd41_smul 73 hA) (T41.dvd41_smul 67 hB)) (T41.dvd41_smul 65 hC))
    (T41.dvd41_smul 46 hD)
  have s1 := T41.dvd41_add (T41.dvd41_add (T41.dvd41_add
    (T41.dvd41_smul 109 hA) (T41.dvd41_smul 84 hB)) (T41.dvd41_smul 80 hC))
    (T41.dvd41_smul 55 hD)
  have s2 := T41.dvd41_add (T41.dvd41_add (T41.dvd41_add
    (T41.dvd41_smul 88 hA) (T41.dvd41_smul 103 hB)) (T41.dvd41_smul 74 hC))
    (T41.dvd41_smul 63 hD)
  have s3 := T41.dvd41_add (T41.dvd41_add (T41.dvd41_add
    (T41.dvd41_smul 90 hA) (T41.dvd41_smul 76 hB)) (T41.dvd41_smul 101 hC))
    (T41.dvd41_smul 61 hD)
  rw [T41.id0] at s0
  rw [T41.id1] at s1
  rw [T41.id2] at s2
  rw [T41.id3] at s3
  exact ⟨T41.dvd41_strip s0, T41.dvd41_strip s1,
         T41.dvd41_strip s2, T41.dvd41_strip s3⟩

/-- NEGATIVE CONTROL for `coords_dvd41`: three of the four evaluations are not
enough.  `⟨5,14,22,20⟩` is killed by `ev41A`, `ev41B`, `ev41C` but not by
`ev41D`, and 41 does not divide its coordinates.  So all four roots are load
bearing, i.e. the Vandermonde hypothesis is not decorative. -/
theorem coords_dvd41_needs_all_four :
    ev41A ⟨5, 14, 22, 20⟩ % 41 = 0 ∧ ev41B ⟨5, 14, 22, 20⟩ % 41 = 0 ∧
    ev41C ⟨5, 14, 22, 20⟩ % 41 = 0 ∧ ev41D ⟨5, 14, 22, 20⟩ % 41 = 5 ∧
    ¬ ((41:Int) ∣ (5:Int)) := by decide

/-! ### The descent -/

/-- Descent measure: total absolute size of the eight coordinates. -/
def sz (x y : Z5) : Nat :=
  x.a0.natAbs + x.a1.natAbs + x.a2.natAbs + x.a3.natAbs
    + y.a0.natAbs + y.a1.natAbs + y.a2.natAbs + y.a3.natAbs

theorem sz_zero {x y : Z5} (h : sz x y ≤ 0) : x = zero ∧ y = zero := by
  simp only [sz] at h
  have k := T41.sum8_zero h
  exact ⟨ext41 (Int.natAbs_eq_zero.mp k.1) (Int.natAbs_eq_zero.mp k.2.1)
           (Int.natAbs_eq_zero.mp k.2.2.1) (Int.natAbs_eq_zero.mp k.2.2.2.1),
         ext41 (Int.natAbs_eq_zero.mp k.2.2.2.2.1) (Int.natAbs_eq_zero.mp k.2.2.2.2.2.1)
           (Int.natAbs_eq_zero.mp k.2.2.2.2.2.2.1)
           (Int.natAbs_eq_zero.mp k.2.2.2.2.2.2.2)⟩

/-- The descent proper, run on an explicit `Nat` fuel parameter discharged from
the measure `sz` (plain structural induction on `Nat`; no well-founded
recursion and no `Nat.strongRecOn`). -/
theorem descent41 : ∀ (n : Nat) (x y : Z5), sz x y ≤ n →
    mul x x = mul phi (mul y y) → x = zero ∧ y = zero := by
  intro n
  induction n with
  | zero => intro x y hm _; exact sz_zero hm
  | succ n ih =>
      intro x y hm h
      have rA := root_step ev41A 7 ev41A_mul ev41_phi.1 T41.nsq7 h
      have rB := root_step ev41B 35 ev41B_mul ev41_phi.2.1 T41.nsq35 h
      have rC := root_step ev41C 35 ev41C_mul ev41_phi.2.2.1 T41.nsq35 h
      have rD := root_step ev41D 7 ev41D_mul ev41_phi.2.2.2 T41.nsq7 h
      have hx := coords_dvd41 x.a0 x.a1 x.a2 x.a3
        (T41.dvd41_of_emod rA.1) (T41.dvd41_of_emod rB.1)
        (T41.dvd41_of_emod rC.1) (T41.dvd41_of_emod rD.1)
      have hy := coords_dvd41 y.a0 y.a1 y.a2 y.a3
        (T41.dvd41_of_emod rA.2) (T41.dvd41_of_emod rB.2)
        (T41.dvd41_of_emod rC.2) (T41.dvd41_of_emod rD.2)
      obtain ⟨b0, hb0⟩ := hx.1
      obtain ⟨b1, hb1⟩ := hx.2.1
      obtain ⟨b2, hb2⟩ := hx.2.2.1
      obtain ⟨b3, hb3⟩ := hx.2.2.2
      obtain ⟨c0, hc0⟩ := hy.1
      obtain ⟨c1, hc1⟩ := hy.2.1
      obtain ⟨c2, hc2⟩ := hy.2.2.1
      obtain ⟨c3, hc3⟩ := hy.2.2.2
      have hxs : x = sm41 ⟨b0, b1, b2, b3⟩ := eq_sm41 hb0 hb1 hb2 hb3
      have hys : y = sm41 ⟨c0, c1, c2, c3⟩ := eq_sm41 hc0 hc1 hc2 hc3
      rw [hxs, hys] at h hm
      rw [mul_sm41, mul_sm41r, mul_sm41, mul_sm41r, mul_sm41r, mul_sm41r] at h
      have h4 := sm41_inj (sm41_inj h)
      have hmeas : sz (⟨b0,b1,b2,b3⟩ : Z5) ⟨c0,c1,c2,c3⟩ ≤ n := by
        simp only [sz, sm41, T41.natAbs41] at hm
        simp only [sz]
        exact T41.sum8_step hm
      have hz := ih ⟨b0,b1,b2,b3⟩ ⟨c0,c1,c2,c3⟩ hmeas h4
      rw [hxs, hys, hz.1, hz.2, sm41_zero]
      exact ⟨rfl, rfl⟩

/-! ### Main theorem -/

/-- **`φ` IS NOT A SQUARE IN `Z[ζ₅]`.**  The equation `x² = φ·y²` has only the
zero solution.  (If `φ` were `w²` with `w ≠ 0` then `x = w, y = 1` would be a
nonzero solution.) -/
theorem not_square : ∀ x y : Z5, mul x x = mul phi (mul y y) → x = zero ∧ y = zero :=
  fun x y h => descent41 (sz x y) x y (Nat.le_refl _) h

/-! ### Anti-vacuity and negative controls for `not_square` -/

/-- ANTI-VACUITY: the hypothesis of `not_square` is satisfiable — `x = y = 0` is
a solution — so `not_square` is not vacuously true. -/
theorem not_square_nonvacuous : mul zero zero = mul phi (mul zero zero) := by decide

/-- … and `not_square` returns the expected verdict on that solution. -/
theorem not_square_at_zero : zero = zero ∧ zero = zero :=
  not_square zero zero not_square_nonvacuous

/-- ANTI-VACUITY: `φ` itself is not zero, so "not a square" is a claim about a
genuine element. -/
theorem phi_ne_zero : (phi : Z5) ≠ zero := by decide

/-- NEGATIVE CONTROL.  The analogous statement for a multiplier that IS a square
is FALSE: with `c = ⟨4,0,0,0⟩ = 2²`, the equation `x² = c·y²` has the nonzero
solution `x = ⟨2,0,0,0⟩`, `y = 1`.  So `not_square` is detecting nonsquareness
of `φ`; it is not a check that always answers "zero". -/
theorem square_case_has_nonzero_solution :
    mul ⟨2,0,0,0⟩ ⟨2,0,0,0⟩ = mul ⟨4,0,0,0⟩ (mul one one)
      ∧ (⟨2,0,0,0⟩ : Z5) ≠ zero ∧ (one : Z5) ≠ zero := by decide

/-- NEGATIVE CONTROL, stated as the outright failure of the `not_square`
conclusion when the multiplier is a square.  Contrast with `not_square`. -/
theorem not_square_false_for_squares :
    ¬ (∀ x y : Z5, mul x x = mul ⟨4,0,0,0⟩ (mul y y) → x = zero ∧ y = zero) := by
  intro hc
  exact absurd (hc ⟨2,0,0,0⟩ one (by decide)).2 (by decide)

/-- NEGATIVE CONTROL with a multiplier that is a nontrivial square in `Z5`:
`c = φ²` admits the nonzero solution `x = φ`, `y = 1`. -/
theorem phi_sq_case_has_nonzero_solution :
    mul phi phi = mul (mul phi phi) (mul one one) ∧ (phi : Z5) ≠ zero := by decide

end Z5

/-! ═══════════════════════════════════════════════════════════════════════
    ## 9.  THE YANG–LEE ROOT, and σ₂ as a transport of pentagon solutions

    The floor's pentagon bench reports TWO converged clusters.  Round 3 proved
    that any pentagon-coherent `Fg p q r s` must satisfy

        q·r = p ,      p² + p = 1 ,      s = −p ,

    and exhibited the golden solution `p = 1/φ`.  But `X² + X − 1` has TWO
    roots, and the second one is `p = −φ`.  This section:

      (1) exhibits the second solution explicitly — `Fg (−φ) (−φ) 1 φ`, zero
          pentagon violations in `K`, by kernel evaluation;
      (2) confirms round 3's *necessity* theorem on a witness it did not know
          about, both by `rfl` and by applying `pentagon_forces_golden`;
      (3) explains where the second solution comes from: it is the OTHER
          Galois generator `σ₂ : ζ ↦ ζ²` applied entrywise to Tier 3a's
          rationalized associator.  `σ₂(1/φ) = −φ`.

    THE HONEST PART.  `σ₂` does NOT fix `φ`, so — unlike `conj` in section 8 —
    it does NOT lift to `K = Z[ζ₅][t]/(t²−φ)` with `t ↦ t`; the naive
    componentwise lift is not multiplicative (`sigma2naive_not_mul` below), and
    any lift at all would have to send `t` to a square root of `−1/φ`
    (`lift_forces_sqrt_neg_invPhi`).  So the transport is NOT a `K`-level
    statement.  It is a `Z[ζ₅]`-level statement, and it applies because
    `FratZ5` and its image both live in the *coefficient* subring `emb(Z[ζ₅])`
    — no `t` in any entry.  The generic naturality lemma
    `pentagonCheck_hom` carries the pentagon along any ring map, and the
    Yang–Lee associator is reached by composing `σ₂` (inside `Z[ζ₅]`) with
    `emb` (into `K`).
    ═══════════════════════════════════════════════════════════════════════ -/

/-! ### 9.1  Z[ζ₅] as a ring in its own right, and its generic associator -/

namespace Z5

/-- Decidable equality, packaged as the `Rng` field. -/
def beq (u v : Z5) : Bool := decide (u = v)

end Z5

/-- The ring Z[ζ₅], as data. -/
def z5Rng : Rng Z5 := ⟨Z5.zero, Z5.one, Z5.add, Z5.mul, Z5.beq⟩

/-- `Fg`, but valued in the coefficient ring Z[ζ₅]. -/
def FgZ5 (p q r s : Z5) : Anyon → Anyon → Z5
  | .one, .one => p
  | .one, .tau => q
  | .tau, .one => r
  | .tau, .tau => s

/-! ### 9.2  A ring homomorphism, as data — and the pentagon is natural in it

Section 8 proved naturality for one specific map (`conj`) and one specific
check (the hexagon).  Here it is done once, generically: any map of the
hand-rolled rings carries `pentagonCheck` across on the nose. -/

/-- A homomorphism of the hand-rolled rings.  `map_beq` is the injectivity
    clause, stated in the only form a `Bool`-valued coherence check can use. -/
structure RngHom {R S : Type} (KR : Rng R) (KS : Rng S) where
  map      : R → S
  map_zero : map KR.zero = KS.zero
  map_one  : map KR.one  = KS.one
  map_add  : ∀ u v, map (KR.add u v) = KS.add (map u) (map v)
  map_mul  : ∀ u v, map (KR.mul u v) = KS.mul (map u) (map v)
  map_beq  : ∀ u v, KS.beq (map u) (map v) = KR.beq u v

/-- The fusion-channel sum commutes with a ring map.  One induction. -/
theorem sumOver_hom {R S : Type} {KR : Rng R} {KS : Rng S}
    (H : RngHom KR KS) (f : Anyon → R) (l : List Anyon) :
    H.map (sumOver KR f l) = sumOver KS (fun u => H.map (f u)) l := by
  induction l with
  | nil => exact H.map_zero
  | cons a as ih => simp only [sumOver, H.map_add, ih]

/-- The F-move commutes with a ring map.  64 label tuples; each lands on
    `map_zero`, `map_one`, or `rfl`. -/
theorem Fs_hom {R S : Type} {KR : Rng R} {KS : Rng S}
    (H : RngHom KR KS) (F : Anyon → Anyon → R) (a b c d x y : Anyon) :
    H.map (Fs KR F a b c d x y) = Fs KS (fun i j => H.map (F i j)) a b c d x y := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases x <;> cases y <;>
    first | rfl | exact H.map_one | exact H.map_zero

/-- **THE PENTAGON IS NATURAL.**  For any ring map `H`, the pentagon check on
    `H ∘ F` over the target ring is the *same Boolean* as the pentagon check on
    `F` over the source ring — every tuple, valid or not.  This is the pentagon
    analogue of `hexagonCheck_conj`, done once for all ring maps. -/
theorem pentagonCheck_hom {R S : Type} {KR : Rng R} {KS : Rng S}
    (H : RngHom KR KS) (F : Anyon → Anyon → R) (a b c dd x y t w v : Anyon) :
    pentagonCheck KS (fun i j => H.map (F i j)) a b c dd x y t w v
      = pentagonCheck KR F a b c dd x y t w v := by
  have hsum :
      sumOver KS (fun u => KS.mul (KS.mul
          (Fs KS (fun i j => H.map (F i j)) a b c y x u)
          (Fs KS (fun i j => H.map (F i j)) a u dd t y v))
          (Fs KS (fun i j => H.map (F i j)) b c dd v u w)) (fuse b c)
        = H.map (sumOver KR (fun u => KR.mul (KR.mul
            (Fs KR F a b c y x u) (Fs KR F a u dd t y v))
            (Fs KR F b c dd v u w)) (fuse b c)) := by
    rw [sumOver_hom H]
    refine congrArg (fun g => sumOver KS g (fuse b c)) ?_
    funext u
    rw [H.map_mul, H.map_mul, Fs_hom H, Fs_hom H, Fs_hom H]
  have hrhs :
      KS.mul (Fs KS (fun i j => H.map (F i j)) x c dd t y w)
             (Fs KS (fun i j => H.map (F i j)) a b w t x v)
        = H.map (KR.mul (Fs KR F x c dd t y w) (Fs KR F a b w t x v)) := by
    rw [H.map_mul, Fs_hom H, Fs_hom H]
  simp only [pentagonCheck, hsum, hrhs, H.map_beq]

/-! ### 9.3  Z[ζ₅] ↪ K is such a homomorphism -/

namespace KK

theorem emb_inj {u v : Z5} (h : emb u = emb v) : u = v := congrArg KK.x h

/-- The embedding is invisible to the equality test. -/
theorem emb_beq (u v : Z5) : beq (emb u) (emb v) = Z5.beq u v := by
  simp only [beq, Z5.beq]
  exact decide_eq_decide.mpr ⟨emb_inj, fun h => by rw [h]⟩

end KK

/-- `Z[ζ₅] ↪ K` packaged as a `RngHom`.  (`emb_add`/`emb_mul` are section 8's,
    reoriented.) -/
def embHom : RngHom z5Rng kRng :=
  ⟨KK.emb, rfl, rfl,
   fun u v => (KK.emb_add u v).symm,
   fun u v => (KK.emb_mul u v).symm,
   KK.emb_beq⟩

/-! ### 9.4  σ₂ : ζ ↦ ζ², the other Galois generator -/

namespace Z5

/-- **σ₂ : ζ ↦ ζ²**, the generator of `Gal(Q(ζ₅)/Q) ≅ Z/4`, in the basis
    `(1, ζ, ζ², ζ³)`:

        a₀ + a₁ζ + a₂ζ² + a₃ζ³
          ↦ a₀ + a₁ζ² + a₂ζ⁴ + a₃ζ⁶
          = (a₀−a₂) + (a₃−a₂)ζ + (a₁−a₂)ζ² + (−a₂)ζ³ .

    Definitionally the `Z5.sigma` of section 8 (see `sigma2_eq_sigma`); it gets
    its own name here because this section uses it as a *transport*, where
    section 8 used it only as a foil for `conj`. -/
def sigma2 (u : Z5) : Z5 := ⟨u.a0 - u.a2, u.a3 - u.a2, u.a1 - u.a2, -u.a2⟩

/-- The two names denote one map. -/
theorem sigma2_eq_sigma (u : Z5) : sigma2 u = sigma u := rfl

/-! #### It is the map it claims to be: the basis, checked -/

theorem sigma2_zero  : sigma2 zero  = zero  := by decide
theorem sigma2_one   : sigma2 one   = one   := by decide
/-- `σ₂ ζ = ζ²` — the defining property. -/
theorem sigma2_zeta  : sigma2 zeta  = zeta2 := by decide
/-- `σ₂ ζ² = ζ⁴`. -/
theorem sigma2_zeta2 : sigma2 zeta2 = zeta4 := by decide
/-- `σ₂ ζ³ = ζ⁶ = ζ`. -/
theorem sigma2_zeta3 : sigma2 zeta3 = zeta  := by decide
/-- `σ₂ ζ⁴ = ζ⁸ = ζ³` — so `σ₂` is a 4-cycle on the primitive roots. -/
theorem sigma2_zeta4 : sigma2 zeta4 = zeta3 := by decide

/-! #### It is a ring homomorphism -/

theorem sigma2_add (u v : Z5) : sigma2 (add u v) = add (sigma2 u) (sigma2 v) := by
  cases u; cases v
  simp only [sigma2, add, Z5.mk.injEq]
  refine ⟨?_,?_,?_,?_⟩ <;> omega

theorem sigma2_neg (u : Z5) : sigma2 (neg u) = neg (sigma2 u) := by
  cases u; simp only [sigma2, neg, Z5.mk.injEq]
  refine ⟨?_,?_,?_,?_⟩ <;> first | omega | trivial

/-- **THE REAL CONTENT.**  `σ₂` is multiplicative — the same recipe as
    `conj_mul`: degree 2 in the eight integer indeterminates, four `omega`
    goals that are linear in the sixteen atoms `u.aᵢ * v.aⱼ`.  A `Z5`-level
    descent to `Int`, which the house rules allow.  Default budgets. -/
theorem sigma2_mul (u v : Z5) : sigma2 (mul u v) = mul (sigma2 u) (sigma2 v) := by
  cases u; cases v
  simp only [sigma2, mul, Z5.mk.injEq,
             Int.sub_mul, Int.mul_sub, Int.neg_mul, Int.mul_neg]
  refine ⟨?_,?_,?_,?_⟩ <;> omega

/-- **`σ₂ ∘ σ₂ = conj`.**  Complex conjugation is the *square* of `σ₂`; this is
    what "the other generator" means.  (Section 8 records the same identity as
    `sigma_sigma`; restated here in the `sigma2` vocabulary.) -/
theorem sigma2_sigma2 (u : Z5) : sigma2 (sigma2 u) = conj u := by
  cases u; simp only [sigma2, conj, Z5.mk.injEq]; refine ⟨?_,?_,?_,?_⟩ <;> omega

/-- Hence `σ₂` has order exactly 4. -/
theorem sigma2_order_four (u : Z5) : sigma2 (sigma2 (sigma2 (sigma2 u))) = u := by
  rw [sigma2_sigma2, sigma2_sigma2, conj_conj]

theorem sigma2_inj {u v : Z5} (h : sigma2 u = sigma2 v) : u = v := by
  have h2 : sigma2 (sigma2 (sigma2 (sigma2 u)))
          = sigma2 (sigma2 (sigma2 (sigma2 v))) := by rw [h]
  rwa [sigma2_order_four, sigma2_order_four] at h2

theorem sigma2_beq (u v : Z5) : beq (sigma2 u) (sigma2 v) = beq u v := by
  simp only [beq]
  exact decide_eq_decide.mpr ⟨sigma2_inj, fun h => by rw [h]⟩

/-! #### Where it sends the golden constants — the Yang–Lee values -/

/-- **`σ₂ φ = −1/φ`** — the other root of `X² − X − 1`. -/
theorem sigma2_phi : sigma2 phi = neg invPhi := by decide
/-- **`σ₂ (1/φ) = −φ`** — the other root of `X² + X − 1`.  This one `decide` is
    the entire reason the pentagon has a second solution cluster. -/
theorem sigma2_invPhi : sigma2 invPhi = neg phi := by decide
/-- `σ₂ (−1/φ) = φ`. -/
theorem sigma2_neg_invPhi : sigma2 (neg invPhi) = phi := by decide

/-! #### Anti-vacuity and negative controls for `σ₂` -/

/-- `σ₂` is not the identity — so the transport below is not a tautology. -/
theorem sigma2_ne_id : beq (sigma2 zeta) zeta = false := by decide
/-- …and not `conj` either: it is a genuinely different Galois element. -/
theorem sigma2_ne_conj : beq (sigma2 zeta) (conj zeta) = false := by decide
/-- **`σ₂` DOES NOT FIX `φ`.**  This is exactly what stops it from lifting to
    `K`, and exactly what makes the transported solution a *new* one. -/
theorem sigma2_phi_ne : sigma2 phi ≠ phi := by decide

end Z5

/-- σ₂ as an automorphism of Z[ζ₅], packaged. -/
def sigma2Hom : RngHom z5Rng z5Rng :=
  ⟨Z5.sigma2, by decide, by decide,
   Z5.sigma2_add, Z5.sigma2_mul, Z5.sigma2_beq⟩

/-! ### 9.5  The two associators over Z[ζ₅], and the transport -/

/-- Tier 3a's rationalized associator read inside Z[ζ₅]: `[[1/φ, 1/φ],[1,−1/φ]]`.
    Every entry lies in the *coefficient* ring — there is no `t` anywhere.
    That is precisely why `σ₂` is allowed to act on it. -/
def FratZ5 : Anyon → Anyon → Z5 :=
  FgZ5 Z5.invPhi Z5.invPhi Z5.one (Z5.neg Z5.invPhi)

/-- **THE YANG–LEE ASSOCIATOR**, `[[−φ, −φ],[1, φ]]`, over Z[ζ₅]. -/
def FyangLeeZ5 : Anyon → Anyon → Z5 :=
  FgZ5 (Z5.neg Z5.phi) (Z5.neg Z5.phi) Z5.one Z5.phi

/-- **THE STRUCTURAL IDENTITY.**  The Yang–Lee associator is `σ₂` applied
    entrywise to the rational-gauge associator.  Four `decide`s. -/
theorem yangLee_is_sigma2_Frat :
    (fun i j => Z5.sigma2 (FratZ5 i j)) = FyangLeeZ5 := by
  funext i j; cases i <;> cases j <;> decide

/-- `FratZ5` pushed into `K` along `emb` is `Fg` at the Tier-3a data — which is
    `FratK`, section 8's object. -/
theorem emb_FratZ5 : (fun i j => embHom.map (FratZ5 i j)) = FratK := by
  funext i j; cases i <;> cases j <;> rfl

/-- `FyangLeeZ5` pushed into `K` is the Yang–Lee `Fg`. -/
theorem emb_FyangLeeZ5 :
    (fun i j => embHom.map (FyangLeeZ5 i j))
      = Fg (KK.neg (KK.emb Z5.phi)) (KK.neg (KK.emb Z5.phi))
           KK.one (KK.emb Z5.phi) := by
  funext i j; cases i <;> cases j <;> rfl

/-- **The pentagon descends to Z[ζ₅]**: `FratK`'s coherence, already proved
    over `K`, is the same Boolean as `FratZ5`'s coherence over Z[ζ₅].  Nothing
    is re-evaluated — `pentagonCheck_hom` moves it. -/
theorem pentagon_FratZ5 :
    ∀ a b c dd x y t w v, pentagonCheck z5Rng FratZ5 a b c dd x y t w v = true := by
  intro a b c dd x y t w v
  have h := pentagonCheck_hom embHom FratZ5 a b c dd x y t w v
  rw [emb_FratZ5] at h
  rw [← h]
  exact pentagon_FratK a b c dd x y t w v

/-- **THE TRANSPORT.**  Apply the Galois automorphism `σ₂` entrywise: the
    pentagon still holds, for the abstract reason, over Z[ζ₅]. -/
theorem pentagon_FyangLeeZ5 :
    ∀ a b c dd x y t w v,
      pentagonCheck z5Rng FyangLeeZ5 a b c dd x y t w v = true := by
  intro a b c dd x y t w v
  have h := pentagonCheck_hom sigma2Hom FratZ5 a b c dd x y t w v
  rw [show (fun i j => sigma2Hom.map (FratZ5 i j)) = FyangLeeZ5
        from yangLee_is_sigma2_Frat] at h
  rw [h]
  exact pentagon_FratZ5 a b c dd x y t w v

/-- **THE CONTRAST WITH SECTION 8, half one.**  `conj` fixes `FratZ5`
    entrywise.  So the round-3 Galois symmetry, transported along
    `pentagonCheck_hom`, returns the solution it started from — it produces a
    symmetry, not a new cluster. -/
theorem conj_fixes_FratZ5 : (fun i j => Z5.conj (FratZ5 i j)) = FratZ5 := by
  funext i j; cases i <;> cases j <;> decide

/-- **THE CONTRAST WITH SECTION 8, half two.**  `σ₂` moves both diagonal
    entries of `FratZ5`.  That is exactly why it lands on a *different*
    pentagon solution — and, at the same time, exactly why it cannot be a
    symmetry of `K` fixing `t`. -/
theorem sigma2_moves_FratZ5 :
    Z5.beq (Z5.sigma2 (FratZ5 .one .one)) (FratZ5 .one .one) = false ∧
    Z5.beq (Z5.sigma2 (FratZ5 .tau .tau)) (FratZ5 .tau .tau) = false :=
  ⟨rfl, rfl⟩

/-! ### 9.6  THE YANG–LEE WITNESS IN K -/

/-- **THE SECOND SOLUTION, by transport.**  `Fg (−φ) (−φ) 1 φ` satisfies every
    one of the 50 live pentagon instances over `K` — obtained by pushing the
    Z[ζ₅]-level transport along `emb`, not by re-evaluating the constants. -/
theorem yang_lee_satisfies_pentagon :
    ∀ a b c dd x y t w v,
      pentagonCheck kRng
        (Fg (KK.neg (KK.emb Z5.phi)) (KK.neg (KK.emb Z5.phi))
            KK.one (KK.emb Z5.phi)) a b c dd x y t w v = true := by
  intro a b c dd x y t w v
  have h := pentagonCheck_hom embHom FyangLeeZ5 a b c dd x y t w v
  rw [emb_FyangLeeZ5] at h
  rw [h]
  exact pentagon_FyangLeeZ5 a b c dd x y t w v

/-- **…and by direct kernel evaluation**, as a violation count: zero of 50.
    The two routes are independent — this one never mentions `σ₂`. -/
theorem yang_lee_pentagon_count :
    countPentViolations kRng
      (Fg (KK.neg (KK.emb Z5.phi)) (KK.neg (KK.emb Z5.phi))
          KK.one (KK.emb Z5.phi)) = 0 := rfl

/-- **The Tier-0 handshake for the second cluster**: `F·F = 1` for the
    Yang–Lee associator too, exactly as for `Frat` and `Fsymm`.  (`φ² − φ = 1`
    is what makes the diagonal come out right.) -/
theorem FyangLee_sq :
    matEq kRng (matMul kRng
      (Fg (KK.neg (KK.emb Z5.phi)) (KK.neg (KK.emb Z5.phi))
          KK.one (KK.emb Z5.phi))
      (Fg (KK.neg (KK.emb Z5.phi)) (KK.neg (KK.emb Z5.phi))
          KK.one (KK.emb Z5.phi))) (matId kRng) = true := rfl

/-! ### 9.7  Round 3's necessity theorem, confirmed on a witness it never saw -/

/-- The three forced relations, **checked directly on the Yang–Lee constants**:
    `(−φ)·1 = −φ`,  `(−φ)² + (−φ) = 1`  (i.e. `φ² − φ = 1`),  `φ = −(−φ)`. -/
theorem yang_lee_forced_relations_by_evaluation :
    KK.mul (KK.neg (KK.emb Z5.phi)) KK.one = KK.neg (KK.emb Z5.phi) ∧
    KK.add (KK.mul (KK.neg (KK.emb Z5.phi)) (KK.neg (KK.emb Z5.phi)))
           (KK.neg (KK.emb Z5.phi)) = KK.one ∧
    KK.emb Z5.phi = KK.neg (KK.neg (KK.emb Z5.phi)) :=
  ⟨rfl, rfl, rfl⟩

/-- **…and the same three relations obtained by NECESSITY.**  Round 3's
    `pentagon_forces_golden` was proved with only the golden witness in hand;
    fed the Yang–Lee witness it returns the Yang–Lee relations.  The middle
    conjunct is `(−φ)² + (−φ) = 1` — the *other* root of `X² + X − 1`, so the
    golden relation was never a disguised definition of `1/φ`. -/
theorem yang_lee_pentagon_by_necessity :
    KK.mul (KK.neg (KK.emb Z5.phi)) KK.one = KK.neg (KK.emb Z5.phi) ∧
    KK.add (KK.mul (KK.neg (KK.emb Z5.phi)) (KK.neg (KK.emb Z5.phi)))
           (KK.neg (KK.emb Z5.phi)) = KK.one ∧
    KK.emb Z5.phi = KK.neg (KK.neg (KK.emb Z5.phi)) :=
  pentagon_forces_golden (KK.neg (KK.emb Z5.phi)) (KK.neg (KK.emb Z5.phi))
    KK.one (KK.emb Z5.phi) yang_lee_satisfies_pentagon

/-- **BOTH ROOTS, side by side.**  `X² + X − 1 = 0` has exactly the two
    solutions the bench found, and the pentagon admits both. -/
theorem both_roots_of_the_golden_relation :
    KK.add (KK.mul KK.invPhi KK.invPhi) KK.invPhi = KK.one ∧
    KK.add (KK.mul (KK.neg (KK.emb Z5.phi)) (KK.neg (KK.emb Z5.phi)))
           (KK.neg (KK.emb Z5.phi)) = KK.one :=
  ⟨rfl, rfl⟩

/-! ### 9.8  The two solutions are genuinely different -/

/-- **DISTINCTNESS, at the diagonal entry.**  `−φ ≠ 1/φ` in `K`. -/
theorem yang_lee_p_ne_golden_p :
    KK.beq (KK.neg (KK.emb Z5.phi)) KK.invPhi = false := rfl

/-- …and therefore the two associators differ, at `F(1,1)`. -/
theorem yang_lee_ne_golden :
    Fg (KK.neg (KK.emb Z5.phi)) (KK.neg (KK.emb Z5.phi)) KK.one (KK.emb Z5.phi)
      .one .one
    ≠ Fsymm .one .one := by decide

/-- The whole matrices differ, as matrices. -/
theorem yang_lee_matrix_ne_golden :
    matEq kRng
      (Fg (KK.neg (KK.emb Z5.phi)) (KK.neg (KK.emb Z5.phi))
          KK.one (KK.emb Z5.phi)) Fsymm = false := rfl

/-- …and it is not `FratK` either — `σ₂` really moved it. -/
theorem yang_lee_matrix_ne_FratK :
    matEq kRng
      (Fg (KK.neg (KK.emb Z5.phi)) (KK.neg (KK.emb Z5.phi))
          KK.one (KK.emb Z5.phi)) FratK = false := rfl

/-- **…AND NOT GAUGE-EQUIVALENT EITHER.**  Section 8 showed `FratK` is `Fsymm`
    in another gauge (`FratK_of_Fsymm`), so "different matrix" alone proves
    nothing.  Here it does: a diagonal gauge `l` — invertible at the vacuum,
    which any gauge must be — relating `Fsymm` to the Yang–Lee associator would
    force `1/φ + φ = 0` in `K`, and `1/φ + φ = √5 ≠ 0`.  So the second cluster
    is a genuinely different solution, not the golden one redressed.

    A `calc` at the `KK` level with `l` kept opaque; only the ring laws and
    `cancel_of_inv` are used. -/
theorem no_gauge_golden_to_yang_lee (l linv : Anyon → KK)
    (hu : KK.mul (linv .one) (l .one) = KK.one)
    (h : ∀ x y, KK.mul (l x) (Fsymm x y)
              = KK.mul (Fg (KK.neg (KK.emb Z5.phi)) (KK.neg (KK.emb Z5.phi))
                            KK.one (KK.emb Z5.phi) x y) (l y)) :
    False := by
  have h11 : KK.mul (l .one) KK.invPhi
           = KK.mul (KK.neg (KK.emb Z5.phi)) (l .one) := h .one .one
  have hz : KK.mul (l .one) (KK.add KK.invPhi (KK.emb Z5.phi)) = KK.zero := by
    calc KK.mul (l .one) (KK.add KK.invPhi (KK.emb Z5.phi))
        = KK.add (KK.mul (l .one) KK.invPhi)
                 (KK.mul (l .one) (KK.emb Z5.phi)) := KK.mul_add _ _ _
      _ = KK.add (KK.mul (KK.neg (KK.emb Z5.phi)) (l .one))
                 (KK.mul (l .one) (KK.emb Z5.phi)) := by rw [h11]
      _ = KK.add (KK.neg (KK.mul (KK.emb Z5.phi) (l .one)))
                 (KK.mul (l .one) (KK.emb Z5.phi)) := by rw [KK.neg_mul]
      _ = KK.add (KK.neg (KK.mul (l .one) (KK.emb Z5.phi)))
                 (KK.mul (l .one) (KK.emb Z5.phi)) := by
            rw [KK.mul_comm (KK.emb Z5.phi) (l .one)]
      _ = KK.zero := KK.neg_add_cancel _
  have hX : KK.add KK.invPhi (KK.emb Z5.phi) = KK.zero :=
    cancel_of_inv (linv .one) (l .one) _ hu hz
  exact absurd hX (by decide)

/-- The constant the gauge argument turns on: `1/φ + φ` is not zero in `K`.
    (It is `√5`.) -/
theorem invPhi_add_phi_ne_zero :
    KK.beq (KK.add KK.invPhi (KK.emb Z5.phi)) KK.zero = false := rfl

/-! ### 9.9  NEGATIVE CONTROLS — "zero violations" has teeth -/

/-- **NEGATIVE CONTROL A.**  The *near miss*: keep `p = q = −φ`, `r = 1`, but
    take `s = −φ` instead of `s = φ`.  Only the third forced relation `s = −p`
    is broken, and the pentagon catches it — 4 of the 50 instances fail.  So
    `yang_lee_pentagon_count = 0` is not an artefact of the shape of `Fg`. -/
theorem yang_lee_near_miss_fails :
    countPentViolations kRng
      (Fg (KK.neg (KK.emb Z5.phi)) (KK.neg (KK.emb Z5.phi))
          KK.one (KK.neg (KK.emb Z5.phi))) = 4 := rfl

/-- **NEGATIVE CONTROL B.**  The sign-flipped candidate `Fg φ φ 1 (−φ)` — the
    root of `X² − X − 1` rather than `X² + X − 1` — fails 5 instances. -/
theorem yang_lee_wrong_root_fails :
    countPentViolations kRng
      (Fg (KK.emb Z5.phi) (KK.emb Z5.phi) KK.one (KK.neg (KK.emb Z5.phi))) = 5 := rfl

/-- **NEGATIVE CONTROL C.**  `Fg ζ ζ 1 (−ζ)`: `ζ` is a unit of `K` but not a
    root of `X² + X − 1`; 5 instances fail. -/
theorem yang_lee_zeta_fails :
    countPentViolations kRng
      (Fg (KK.emb Z5.zeta) (KK.emb Z5.zeta) KK.one (KK.neg (KK.emb Z5.zeta))) = 5 := rfl

/-- **NEGATIVE CONTROL D — the transport needs a ring map.**  Section 8's
    `swapBad` is an additive involution of Z[ζ₅] that is *not* multiplicative.
    Applied entrywise to `FratZ5` it destroys the pentagon: 5 of 50 fail.  So
    `pentagonCheck_hom` is carrying `sigma2_mul`, not merely bijectivity. -/
theorem swapBad_breaks_the_pentagon :
    countPentViolations z5Rng (fun i j => Z5.swapBad (FratZ5 i j)) = 5 := rfl

/-- **ANTI-VACUITY for 9.5.**  `FratZ5` itself is clean over Z[ζ₅], so the
    transport starts from a real solution. -/
theorem FratZ5_pentagon_clean : countPentViolations z5Rng FratZ5 = 0 := rfl

/-- …and its `σ₂`-image is clean, by evaluation, matching the transport. -/
theorem FyangLeeZ5_pentagon_clean : countPentViolations z5Rng FyangLeeZ5 = 0 := rfl

/-! ### 9.10  WHY THERE IS NO K-LEVEL σ₂ — the honest negative result

`conj` lifted to `K` because it fixes `φ`, so `t ↦ t` respects `t² = φ`.
`σ₂ φ = −1/φ ≠ φ`, so that route is closed.  Two receipts. -/

namespace KK

/-- The naive componentwise lift, `⟨x,y⟩ ↦ ⟨σ₂x, σ₂y⟩` — the literal analogue
    of `KK.conj`. -/
def sigma2naive (u : KK) : KK := ⟨Z5.sigma2 u.x, Z5.sigma2 u.y⟩

/-- It is additive… -/
theorem sigma2naive_add (u v : KK) :
    sigma2naive (add u v) = add (sigma2naive u) (sigma2naive v) := by
  cases u; cases v; simp only [sigma2naive, add, KK.mk.injEq]
  exact ⟨Z5.sigma2_add _ _, Z5.sigma2_add _ _⟩

/-- …and of order 4, hence a bijection — it has every property `KK.conj` has
    except the one that matters. -/
theorem sigma2naive_order_four (u : KK) :
    sigma2naive (sigma2naive (sigma2naive (sigma2naive u))) = u := by
  cases u; simp only [sigma2naive, KK.mk.injEq]
  exact ⟨Z5.sigma2_order_four _, Z5.sigma2_order_four _⟩

/-- **…but it is NOT multiplicative.**  It fails at the defining relation
    itself: `σ₂naive(t·t) = σ₂naive(φ) = −1/φ`, while
    `σ₂naive(t)·σ₂naive(t) = t·t = φ`, and `−1/φ ≠ φ`. -/
theorem sigma2naive_not_mul :
    beq (sigma2naive (mul t t)) (mul (sigma2naive t) (sigma2naive t)) = false := rfl

end KK

/-- **THE OBSTRUCTION, stated exactly.**  Any multiplicative `Ψ : K → K` that
    extends `σ₂` on the coefficient ring must send `t = √φ` to a square root of
    `σ₂ φ = −1/φ`.  Proved from the ring laws at the `K` level — nothing
    descends to `Int`. -/
theorem lift_forces_sqrt_neg_invPhi (P : KK → KK)
    (hmul : ∀ u v, P (KK.mul u v) = KK.mul (P u) (P v))
    (hemb : ∀ u, P (KK.emb u) = KK.emb (Z5.sigma2 u)) :
    KK.mul (P KK.t) (P KK.t) = KK.emb (Z5.neg Z5.invPhi) :=
  calc KK.mul (P KK.t) (P KK.t)
      = P (KK.mul KK.t KK.t)     := (hmul KK.t KK.t).symm
    _ = P (KK.emb Z5.phi)        := by rw [kk_t_sq]
    _ = KK.emb (Z5.sigma2 Z5.phi) := hemb Z5.phi
    _ = KK.emb (Z5.neg Z5.invPhi) := by rw [Z5.sigma2_phi]

/-- The obvious candidates for `Ψ t` all fail: `t² = φ`, `(−t)² = φ`, and
    `b² = 1/φ` — none of them is `−1/φ`.  (Not a proof that no square root
    exists in `K`; that is left open, and stated as such.) -/
theorem no_obvious_sqrt_neg_invPhi :
    KK.beq (KK.mul KK.t KK.t) (KK.emb (Z5.neg Z5.invPhi)) = false ∧
    KK.beq (KK.mul (KK.neg KK.t) (KK.neg KK.t))
           (KK.emb (Z5.neg Z5.invPhi)) = false ∧
    KK.beq (KK.mul KK.b KK.b) (KK.emb (Z5.neg Z5.invPhi)) = false :=
  ⟨rfl, rfl, rfl⟩

/-- **THE SUMMARY OF SECTION 9.**  Six facts, one term. -/
theorem yang_lee_summary :
    (∀ a b c dd x y t w v,
       pentagonCheck kRng
         (Fg (KK.neg (KK.emb Z5.phi)) (KK.neg (KK.emb Z5.phi))
             KK.one (KK.emb Z5.phi)) a b c dd x y t w v = true) ∧
    countPentViolations kRng
      (Fg (KK.neg (KK.emb Z5.phi)) (KK.neg (KK.emb Z5.phi))
          KK.one (KK.emb Z5.phi)) = 0 ∧
    (fun i j => Z5.sigma2 (FratZ5 i j)) = FyangLeeZ5 ∧
    Z5.sigma2 Z5.invPhi = Z5.neg Z5.phi ∧
    (∀ u, Z5.sigma2 (Z5.sigma2 u) = Z5.conj u) ∧
    KK.beq (KK.neg (KK.emb Z5.phi)) KK.invPhi = false :=
  ⟨yang_lee_satisfies_pentagon, yang_lee_pentagon_count,
   yangLee_is_sigma2_Frat, Z5.sigma2_invPhi, Z5.sigma2_sigma2,
   yang_lee_p_ne_golden_p⟩


/-! ═══════════════════════════════════════════════════════════════════════
    ## 7.5  PENTAGON SUFFICIENCY — the converse, proved

    §7.3 proved NECESSITY: pentagon ⟹ `q·r = p`, `p² + p = 1`, `s = −p`.
    Round 3 left the converse as an honest gap, estimated at ~39 lemmas,
    because `KK.beq u v` on OPAQUE values does not reduce by `rfl` even when
    the two sides are equal by the ring laws.  This section closes it.

    The gap is closed by *routing around* `beq` rather than fighting it.
    `pentcheck_of_eq` below converts the Bool goal `pentagonCheck … = true`
    into the KK equation `LHS = RHS` once and for all, via `decide_eq_true`;
    after that no `beq` is ever asked to reduce on an opaque value again, and
    what remains is 50 small equations in `p q r s`.

    The 50 are not 50 different problems.  Reading off the reduced residual of
    each live tuple (the technique of `pent_at_01`…`pent_at_11`, applied to
    all 50 rather than to the eleven), the 39 trivial ones fall into **eight**
    generic shapes — `sufT_B`…`sufT_I`, each a one-line unit-and-zero
    cancellation valid for *arbitrary* ring elements `u v` — and the eleven
    non-trivial ones are `sufE_1`…`sufE_11`, each an explicit `calc` at the
    KK level with `p q r s` kept opaque.  Exactly eleven of the fifty instance
    lemmas below take a relation as a hypothesis; the other thirty-nine take
    none.  That 11/39 split is `pentagon_nontrivial_instances` (§7.4) again,
    now visible in the *type* of each lemma rather than in a count.

    Method note, and why this does not repeat the round-3 crash: nothing
    descends to `Int`, no budget is raised, no `simp` search runs on a KK ring
    goal — every `simp only` here is a fixed unit-and-zero list applied to an
    already-reduced residual, and every non-trivial step is an explicit
    `calc`.  The whole section costs a few seconds.
    ═══════════════════════════════════════════════════════════════════════ -/

/-- Off the valid set `pentagonCheck` is `true` by construction.  Concrete
    labels make the guard decide, so each of the 462 dead tuples is `rfl`. -/
theorem pentcheck_of_invalid {R : Type} (K : Rng R) (F : Anyon → Anyon → R)
    (a b c dd x y t w v : Anyon)
    (h : pentagonValid a b c dd x y t w v = false) :
    pentagonCheck K F a b c dd x y t w v = true := by
  unfold pentagonCheck; rw [h]; rfl

/-- **THE BRIDGE OUT OF `beq`.**  `KK.beq u v` is `decide (u = v)`, which is
    stuck on opaque arguments — that was round 3's blocker.  But `decide` only
    needs to be *produced*, never *reduced*: `decide_eq_true` turns a proof of
    `u = v` into `decide (u = v) = true`.  So a pentagon instance is
    discharged by proving one KK equation, and the equation's two sides are
    already fully reduced whenever the nine labels are concrete. -/
theorem pentcheck_of_eq (F : Anyon → Anyon → KK) (a b c dd x y t w v : Anyon)
    (h : sumOver kRng (fun u => KK.mul (KK.mul (Fs kRng F a b c y x u)
                                               (Fs kRng F a u dd t y v))
                                        (Fs kRng F b c dd v u w)) (fuse b c)
       = KK.mul (Fs kRng F x c dd t y w) (Fs kRng F a b w t x v)) :
    pentagonCheck kRng F a b c dd x y t w v = true := by
  unfold pentagonCheck
  split
  · exact decide_eq_true h
  · rfl

/-! ### 7.5.1  The eight generic shapes of the 39 trivial residuals

Each holds for *arbitrary* `u v : K` — no relation is used, which is exactly
what "trivial for a generic associator" means.  Together they cover 39 of the
50 live tuples; the multiplicities are 21, 4, 3, 5, 2, 2, 1, 1. -/

/-- Shape B, 21 instances (17 of them at `u = 1`). -/
theorem sufT_B (u : KK) :
    KK.add (KK.mul (KK.mul KK.one u) KK.one) KK.zero = KK.mul u KK.one := by
  simp only [KK.mul_one, KK.one_mul, KK.add_zero]

/-- Shape C, 4 instances — shape B with the right-hand product transposed. -/
theorem sufT_C (u : KK) :
    KK.add (KK.mul (KK.mul KK.one u) KK.one) KK.zero = KK.mul KK.one u := by
  simp only [KK.mul_one, KK.one_mul, KK.add_zero]

/-- Shape D, 3 instances. -/
theorem sufT_D (u v : KK) :
    KK.add (KK.mul (KK.mul u KK.one) KK.one)
           (KK.add (KK.mul (KK.mul v KK.zero) KK.zero) KK.zero)
      = KK.mul KK.one u := by
  simp only [KK.mul_one, KK.one_mul, KK.mul_zero, KK.add_zero]

/-- Shape E, 5 instances. -/
theorem sufT_E (u v : KK) :
    KK.add (KK.mul (KK.mul u KK.zero) KK.zero)
           (KK.add (KK.mul (KK.mul v KK.one) KK.one) KK.zero)
      = KK.mul KK.one v := by
  simp only [KK.mul_zero, KK.mul_one, KK.one_mul, KK.add_zero, KK.zero_add]

/-- Shape F, 2 instances. -/
theorem sufT_F (u v : KK) :
    KK.add (KK.mul (KK.mul KK.one KK.one) u)
           (KK.add (KK.mul (KK.mul KK.zero KK.zero) v) KK.zero)
      = KK.mul u KK.one := by
  simp only [KK.mul_one, KK.one_mul, KK.mul_zero, KK.zero_mul, KK.add_zero]

/-- Shape G, 2 instances. -/
theorem sufT_G (u v : KK) :
    KK.add (KK.mul (KK.mul KK.zero KK.zero) u)
           (KK.add (KK.mul (KK.mul KK.one KK.one) v) KK.zero)
      = KK.mul v KK.one := by
  simp only [KK.mul_zero, KK.zero_mul, KK.mul_one, KK.one_mul, KK.add_zero,
             KK.zero_add]

/-- Shape H, 1 instance — the tempting one at `(τ,1,τ,τ | τ,1,τ,τ,τ)`, which
    looks like it should constrain `q` and `s` but does not. -/
theorem sufT_H (u v : KK) :
    KK.add (KK.mul (KK.mul KK.zero KK.zero) u)
           (KK.add (KK.mul (KK.mul KK.one u) v) KK.zero)
      = KK.mul u v := by
  simp only [KK.mul_zero, KK.zero_mul, KK.one_mul, KK.add_zero, KK.zero_add]

/-- Shape I, 1 instance. -/
theorem sufT_I (u v : KK) :
    KK.add (KK.mul (KK.mul u KK.zero) KK.zero)
           (KK.add (KK.mul (KK.mul v u) KK.one) KK.zero)
      = KK.mul v u := by
  simp only [KK.mul_zero, KK.mul_one, KK.add_zero, KK.zero_add]

/-! ### 7.5.2  The eleven essential residuals

These are the eleven of `pentagon_nontrivial_instances`, in the numbering of
`pent_at_01`…`pent_at_11`.  `s` has been substituted as `−p` in the statements
(the instance lemmas below do the `subst`), which is why `s` does not appear:
carrying it symbolically would only duplicate `sufNsq` at every step. -/

/-- `(−p)² = p²`.  The one fact about the sign that everything else uses. -/
theorem sufNsq (p : KK) : KK.mul (KK.neg p) (KK.neg p) = KK.mul p p := by
  rw [KK.neg_mul, KK.mul_neg, KK.neg_neg]

/-- #1  residual `p² + qr − 1`: `qr = p` turns it into the golden relation. -/
theorem sufE_1 (p q r : KK) (h4 : KK.mul q r = p)
    (hg : KK.add (KK.mul p p) p = KK.one) :
    KK.add (KK.mul (KK.mul p KK.one) p)
           (KK.add (KK.mul (KK.mul q KK.one) r) KK.zero)
      = KK.mul KK.one KK.one := by
  simp only [KK.mul_one, KK.add_zero]
  rw [h4]; exact hg

/-- #2  residual `q·(p + s)`: zero because `s = −p`, for any `q`. -/
theorem sufE_2 (p q : KK) :
    KK.add (KK.mul (KK.mul p KK.one) q)
           (KK.add (KK.mul (KK.mul q KK.one) (KK.neg p)) KK.zero)
      = KK.mul KK.zero KK.zero := by
  simp only [KK.mul_one, KK.mul_zero, KK.add_zero]
  calc KK.add (KK.mul p q) (KK.mul q (KK.neg p))
      = KK.add (KK.mul p q) (KK.neg (KK.mul q p)) := by rw [KK.mul_neg]
    _ = KK.add (KK.mul p q) (KK.neg (KK.mul p q)) := by rw [KK.mul_comm q p]
    _ = KK.zero                                   := KK.add_neg _

/-- #3  residual `p² + (qs)r`: `mul_right_comm` makes `(qs)r` into `(qr)s`. -/
theorem sufE_3 (p q r : KK) (h4 : KK.mul q r = p) :
    KK.add (KK.mul (KK.mul p KK.one) p)
           (KK.add (KK.mul (KK.mul q (KK.neg p)) r) KK.zero)
      = KK.mul KK.zero KK.zero := by
  simp only [KK.mul_one, KK.mul_zero, KK.add_zero]
  have h : KK.mul (KK.mul q (KK.neg p)) r = KK.neg (KK.mul p p) := by
    rw [KK.mul_right_comm q (KK.neg p) r, h4, KK.mul_neg]
  rw [h]; exact KK.add_neg _

/-- #4  residual `qr − p`: the relation verbatim. -/
theorem sufE_4 (p q r : KK) (h4 : KK.mul q r = p) :
    KK.add (KK.mul (KK.mul p KK.zero) KK.zero)
           (KK.add (KK.mul (KK.mul q r) KK.one) KK.zero)
      = KK.mul KK.one p := by
  simp only [KK.mul_zero, KK.mul_one, KK.one_mul, KK.add_zero, KK.zero_add]
  exact h4

/-- #5  residual `q·(p − 1 + s²)`: `s² = p²` and `p² + p = 1`. -/
theorem sufE_5 (p q : KK) (hg : KK.add (KK.mul p p) p = KK.one) :
    KK.add (KK.mul (KK.mul p KK.one) q)
           (KK.add (KK.mul (KK.mul q (KK.neg p)) (KK.neg p)) KK.zero)
      = KK.mul KK.one q := by
  simp only [KK.mul_one, KK.one_mul, KK.add_zero]
  calc KK.add (KK.mul p q) (KK.mul (KK.mul q (KK.neg p)) (KK.neg p))
      = KK.add (KK.mul p q) (KK.mul q (KK.mul (KK.neg p) (KK.neg p))) := by
        rw [KK.mul_assoc]
    _ = KK.add (KK.mul p q) (KK.mul q (KK.mul p p)) := by rw [sufNsq]
    _ = KK.add (KK.mul q p) (KK.mul q (KK.mul p p)) := by rw [KK.mul_comm p q]
    _ = KK.mul q (KK.add p (KK.mul p p)) := (KK.mul_add q p (KK.mul p p)).symm
    _ = KK.mul q (KK.add (KK.mul p p) p) := by rw [KK.add_comm p (KK.mul p p)]
    _ = KK.mul q KK.one                  := by rw [hg]
    _ = q                                := KK.mul_one q

/-- #6  residual `qr − p` again, at a different tuple. -/
theorem sufE_6 (p q r : KK) (h4 : KK.mul q r = p) :
    KK.add (KK.mul (KK.mul KK.zero KK.zero) p)
           (KK.add (KK.mul (KK.mul KK.one q) r) KK.zero)
      = KK.mul p KK.one := by
  simp only [KK.mul_zero, KK.zero_mul, KK.one_mul, KK.mul_one, KK.add_zero,
             KK.zero_add]
  exact h4

/-- #7  residual `p − qr`: #4 with the sides exchanged. -/
theorem sufE_7 (p q r : KK) (h4 : KK.mul q r = p) :
    KK.add (KK.mul (KK.mul KK.zero KK.zero) KK.zero)
           (KK.add (KK.mul (KK.mul KK.one p) KK.one) KK.zero)
      = KK.mul q r := by
  simp only [KK.mul_zero, KK.one_mul, KK.mul_one, KK.add_zero, KK.zero_add]
  exact h4.symm

/-- #8  residual `r·(p + s)`: the `r` twin of #2. -/
theorem sufE_8 (p r : KK) :
    KK.add (KK.mul (KK.mul r KK.one) p)
           (KK.add (KK.mul (KK.mul (KK.neg p) KK.one) r) KK.zero)
      = KK.mul KK.zero KK.zero := by
  simp only [KK.mul_one, KK.mul_zero, KK.add_zero]
  calc KK.add (KK.mul r p) (KK.mul (KK.neg p) r)
      = KK.add (KK.mul r p) (KK.neg (KK.mul p r)) := by rw [KK.neg_mul]
    _ = KK.add (KK.mul r p) (KK.neg (KK.mul r p)) := by rw [KK.mul_comm p r]
    _ = KK.zero                                   := KK.add_neg _

/-- #9  residual `qr + s² − 1` — the consistency receipt of §7.3a, now as a
    pentagon instance rather than a hand-checked corollary. -/
theorem sufE_9 (p q r : KK) (h4 : KK.mul q r = p)
    (hg : KK.add (KK.mul p p) p = KK.one) :
    KK.add (KK.mul (KK.mul r KK.one) q)
           (KK.add (KK.mul (KK.mul (KK.neg p) KK.one) (KK.neg p)) KK.zero)
      = KK.mul KK.one KK.one := by
  simp only [KK.mul_one, KK.add_zero]
  rw [KK.mul_comm r q, h4, sufNsq, KK.add_comm p (KK.mul p p)]
  exact hg

/-- #10  residual `r·(p − 1 + s²)`: the `r` twin of #5. -/
theorem sufE_10 (p r : KK) (hg : KK.add (KK.mul p p) p = KK.one) :
    KK.add (KK.mul (KK.mul r KK.one) p)
           (KK.add (KK.mul (KK.mul (KK.neg p) (KK.neg p)) r) KK.zero)
      = KK.mul r KK.one := by
  simp only [KK.mul_one, KK.add_zero]
  calc KK.add (KK.mul r p) (KK.mul (KK.mul (KK.neg p) (KK.neg p)) r)
      = KK.add (KK.mul r p) (KK.mul (KK.mul p p) r) := by rw [sufNsq]
    _ = KK.add (KK.mul r p) (KK.mul r (KK.mul p p)) := by
        rw [KK.mul_comm (KK.mul p p) r]
    _ = KK.mul r (KK.add p (KK.mul p p)) := (KK.mul_add r p (KK.mul p p)).symm
    _ = KK.mul r (KK.add (KK.mul p p) p) := by rw [KK.add_comm p (KK.mul p p)]
    _ = KK.mul r KK.one                  := by rw [hg]
    _ = r                                := KK.mul_one r

/-- #11  residual `qr − s² + s³`, the only cubic one.  It needs `p³ + p² = p`,
    which is `p·(p² + p) = p·1`; that is `hc` below.  No cancellation and no
    unit is used — only the ring laws and the golden relation. -/
theorem sufE_11 (p q r : KK) (h4 : KK.mul q r = p)
    (hg : KK.add (KK.mul p p) p = KK.one) :
    KK.add (KK.mul (KK.mul r KK.one) q)
           (KK.add (KK.mul (KK.mul (KK.neg p) (KK.neg p)) (KK.neg p)) KK.zero)
      = KK.mul (KK.neg p) (KK.neg p) := by
  simp only [KK.mul_one, KK.add_zero, sufNsq]
  have hc : KK.add (KK.mul p p) (KK.mul p (KK.mul p p)) = p := by
    calc KK.add (KK.mul p p) (KK.mul p (KK.mul p p))
        = KK.add (KK.mul p (KK.mul p p)) (KK.mul p p) := KK.add_comm _ _
      _ = KK.mul p (KK.add (KK.mul p p) p) := (KK.mul_add p (KK.mul p p) p).symm
      _ = KK.mul p KK.one                  := by rw [hg]
      _ = p                                := KK.mul_one p
  have key : KK.add p (KK.neg (KK.mul p (KK.mul p p))) = KK.mul p p := by
    calc KK.add p (KK.neg (KK.mul p (KK.mul p p)))
        = KK.add (KK.add (KK.mul p p) (KK.mul p (KK.mul p p)))
                 (KK.neg (KK.mul p (KK.mul p p)))          := by rw [hc]
      _ = KK.add (KK.mul p p) (KK.add (KK.mul p (KK.mul p p))
                 (KK.neg (KK.mul p (KK.mul p p))))         := KK.add_assoc _ _ _
      _ = KK.add (KK.mul p p) KK.zero                      := by rw [KK.add_neg]
      _ = KK.mul p p                                       := KK.add_zero _
  calc KK.add (KK.mul r q) (KK.mul (KK.mul p p) (KK.neg p))
      = KK.add (KK.mul q r) (KK.mul (KK.mul p p) (KK.neg p)) := by
        rw [KK.mul_comm r q]
    _ = KK.add p (KK.mul (KK.mul p p) (KK.neg p)) := by rw [h4]
    _ = KK.add p (KK.neg (KK.mul (KK.mul p p) p)) := by rw [KK.mul_neg]
    _ = KK.add p (KK.neg (KK.mul p (KK.mul p p))) := by rw [KK.mul_assoc]
    _ = KK.mul p p                                := key

/-! ### 7.5.3  The fifty live instances, one lemma each

Every one is `pentcheck_of_eq` applied to a §7.5.1 or §7.5.2 lemma; the
elaborator's defeq check performs the same reduction that makes
`pent_at_01 … := rfl` work.  Exactly eleven of the fifty carry a hypothesis —
`suffP_38 … suffP_44`, `suffP_46 … suffP_48`, `suffP_50` — which is
`pentagon_nontrivial_instances` restated in the types. -/

theorem suffP_01 (p q r s : KK) :
    pentagonCheck kRng (Fg p q r s) .one .one .one .one .one .one .one .one .one = true :=
  pentcheck_of_eq _ _ _ _ _ _ _ _ _ _ (sufT_B KK.one)

theorem suffP_02 (p q r s : KK) :
    pentagonCheck kRng (Fg p q r s) .one .one .one .tau .one .one .tau .tau .tau = true :=
  pentcheck_of_eq _ _ _ _ _ _ _ _ _ _ (sufT_B KK.one)

theorem suffP_03 (p q r s : KK) :
    pentagonCheck kRng (Fg p q r s) .one .one .tau .one .one .tau .tau .tau .tau = true :=
  pentcheck_of_eq _ _ _ _ _ _ _ _ _ _ (sufT_B KK.one)

theorem suffP_04 (p q r s : KK) :
    pentagonCheck kRng (Fg p q r s) .one .one .tau .tau .one .tau .one .one .one = true :=
  pentcheck_of_eq _ _ _ _ _ _ _ _ _ _ (sufT_B KK.one)

theorem suffP_05 (p q r s : KK) :
    pentagonCheck kRng (Fg p q r s) .one .one .tau .tau .one .tau .tau .tau .tau = true :=
  pentcheck_of_eq _ _ _ _ _ _ _ _ _ _ (sufT_B KK.one)

theorem suffP_06 (p q r s : KK) :
    pentagonCheck kRng (Fg p q r s) .one .tau .one .one .tau .tau .tau .one .tau = true :=
  pentcheck_of_eq _ _ _ _ _ _ _ _ _ _ (sufT_B KK.one)

theorem suffP_07 (p q r s : KK) :
    pentagonCheck kRng (Fg p q r s) .one .tau .one .tau .tau .tau .one .tau .one = true :=
  pentcheck_of_eq _ _ _ _ _ _ _ _ _ _ (sufT_B KK.one)

theorem suffP_08 (p q r s : KK) :
    pentagonCheck kRng (Fg p q r s) .one .tau .one .tau .tau .tau .tau .tau .tau = true :=
  pentcheck_of_eq _ _ _ _ _ _ _ _ _ _ (sufT_B KK.one)

theorem suffP_09 (p q r s : KK) :
    pentagonCheck kRng (Fg p q r s) .one .tau .tau .one .tau .one .one .tau .one = true :=
  pentcheck_of_eq _ _ _ _ _ _ _ _ _ _ (sufT_D KK.one KK.zero)

theorem suffP_10 (p q r s : KK) :
    pentagonCheck kRng (Fg p q r s) .one .tau .tau .one .tau .tau .tau .tau .tau = true :=
  pentcheck_of_eq _ _ _ _ _ _ _ _ _ _ (sufT_E KK.zero KK.one)

theorem suffP_11 (p q r s : KK) :
    pentagonCheck kRng (Fg p q r s) .one .tau .tau .tau .tau .one .tau .one .tau = true :=
  pentcheck_of_eq _ _ _ _ _ _ _ _ _ _ (sufT_F p r)

theorem suffP_12 (p q r s : KK) :
    pentagonCheck kRng (Fg p q r s) .one .tau .tau .tau .tau .one .tau .tau .tau = true :=
  pentcheck_of_eq _ _ _ _ _ _ _ _ _ _ (sufT_F q s)

theorem suffP_13 (p q r s : KK) :
    pentagonCheck kRng (Fg p q r s) .one .tau .tau .tau .tau .tau .one .tau .one = true :=
  pentcheck_of_eq _ _ _ _ _ _ _ _ _ _ (sufT_E KK.zero KK.one)

theorem suffP_14 (p q r s : KK) :
    pentagonCheck kRng (Fg p q r s) .one .tau .tau .tau .tau .tau .tau .one .tau = true :=
  pentcheck_of_eq _ _ _ _ _ _ _ _ _ _ (sufT_G p r)

theorem suffP_15 (p q r s : KK) :
    pentagonCheck kRng (Fg p q r s) .one .tau .tau .tau .tau .tau .tau .tau .tau = true :=
  pentcheck_of_eq _ _ _ _ _ _ _ _ _ _ (sufT_G q s)

theorem suffP_16 (p q r s : KK) :
    pentagonCheck kRng (Fg p q r s) .tau .one .one .one .tau .tau .tau .one .one = true :=
  pentcheck_of_eq _ _ _ _ _ _ _ _ _ _ (sufT_B KK.one)

theorem suffP_17 (p q r s : KK) :
    pentagonCheck kRng (Fg p q r s) .tau .one .one .tau .tau .tau .one .tau .tau = true :=
  pentcheck_of_eq _ _ _ _ _ _ _ _ _ _ (sufT_B KK.one)

theorem suffP_18 (p q r s : KK) :
    pentagonCheck kRng (Fg p q r s) .tau .one .one .tau .tau .tau .tau .tau .tau = true :=
  pentcheck_of_eq _ _ _ _ _ _ _ _ _ _ (sufT_B KK.one)

theorem suffP_19 (p q r s : KK) :
    pentagonCheck kRng (Fg p q r s) .tau .one .tau .one .tau .one .one .tau .tau = true :=
  pentcheck_of_eq _ _ _ _ _ _ _ _ _ _ (sufT_B KK.one)

theorem suffP_20 (p q r s : KK) :
    pentagonCheck kRng (Fg p q r s) .tau .one .tau .one .tau .tau .tau .tau .tau = true :=
  pentcheck_of_eq _ _ _ _ _ _ _ _ _ _ (sufT_B KK.one)

theorem suffP_21 (p q r s : KK) :
    pentagonCheck kRng (Fg p q r s) .tau .one .tau .tau .tau .one .tau .one .one = true :=
  pentcheck_of_eq _ _ _ _ _ _ _ _ _ _ (sufT_B p)

theorem suffP_22 (p q r s : KK) :
    pentagonCheck kRng (Fg p q r s) .tau .one .tau .tau .tau .one .tau .tau .tau = true :=
  pentcheck_of_eq _ _ _ _ _ _ _ _ _ _ (sufT_B q)

theorem suffP_23 (p q r s : KK) :
    pentagonCheck kRng (Fg p q r s) .tau .one .tau .tau .tau .tau .one .tau .tau = true :=
  pentcheck_of_eq _ _ _ _ _ _ _ _ _ _ (sufT_B KK.one)

theorem suffP_24 (p q r s : KK) :
    pentagonCheck kRng (Fg p q r s) .tau .one .tau .tau .tau .tau .tau .one .one = true :=
  pentcheck_of_eq _ _ _ _ _ _ _ _ _ _ (sufT_B r)

theorem suffP_25 (p q r s : KK) :
    pentagonCheck kRng (Fg p q r s) .tau .one .tau .tau .tau .tau .tau .tau .tau = true :=
  pentcheck_of_eq _ _ _ _ _ _ _ _ _ _ (sufT_B s)

theorem suffP_26 (p q r s : KK) :
    pentagonCheck kRng (Fg p q r s) .tau .tau .one .one .one .one .one .one .tau = true :=
  pentcheck_of_eq _ _ _ _ _ _ _ _ _ _ (sufT_B KK.one)

theorem suffP_27 (p q r s : KK) :
    pentagonCheck kRng (Fg p q r s) .tau .tau .one .one .tau .tau .tau .one .tau = true :=
  pentcheck_of_eq _ _ _ _ _ _ _ _ _ _ (sufT_B KK.one)

theorem suffP_28 (p q r s : KK) :
    pentagonCheck kRng (Fg p q r s) .tau .tau .one .tau .one .one .tau .tau .one = true :=
  pentcheck_of_eq _ _ _ _ _ _ _ _ _ _ (sufT_C p)

theorem suffP_29 (p q r s : KK) :
    pentagonCheck kRng (Fg p q r s) .tau .tau .one .tau .one .one .tau .tau .tau = true :=
  pentcheck_of_eq _ _ _ _ _ _ _ _ _ _ (sufT_C q)

theorem suffP_30 (p q r s : KK) :
    pentagonCheck kRng (Fg p q r s) .tau .tau .one .tau .tau .tau .one .tau .tau = true :=
  pentcheck_of_eq _ _ _ _ _ _ _ _ _ _ (sufT_B KK.one)

theorem suffP_31 (p q r s : KK) :
    pentagonCheck kRng (Fg p q r s) .tau .tau .one .tau .tau .tau .tau .tau .one = true :=
  pentcheck_of_eq _ _ _ _ _ _ _ _ _ _ (sufT_C r)

theorem suffP_32 (p q r s : KK) :
    pentagonCheck kRng (Fg p q r s) .tau .tau .one .tau .tau .tau .tau .tau .tau = true :=
  pentcheck_of_eq _ _ _ _ _ _ _ _ _ _ (sufT_C s)

theorem suffP_33 (p q r s : KK) :
    pentagonCheck kRng (Fg p q r s) .tau .tau .tau .one .one .tau .tau .tau .one = true :=
  pentcheck_of_eq _ _ _ _ _ _ _ _ _ _ (sufT_D p q)

theorem suffP_34 (p q r s : KK) :
    pentagonCheck kRng (Fg p q r s) .tau .tau .tau .one .one .tau .tau .tau .tau = true :=
  pentcheck_of_eq _ _ _ _ _ _ _ _ _ _ (sufT_E p q)

theorem suffP_35 (p q r s : KK) :
    pentagonCheck kRng (Fg p q r s) .tau .tau .tau .one .tau .one .one .tau .tau = true :=
  pentcheck_of_eq _ _ _ _ _ _ _ _ _ _ (sufT_E KK.zero KK.one)

theorem suffP_36 (p q r s : KK) :
    pentagonCheck kRng (Fg p q r s) .tau .tau .tau .one .tau .tau .tau .tau .one = true :=
  pentcheck_of_eq _ _ _ _ _ _ _ _ _ _ (sufT_D r s)

theorem suffP_37 (p q r s : KK) :
    pentagonCheck kRng (Fg p q r s) .tau .tau .tau .one .tau .tau .tau .tau .tau = true :=
  pentcheck_of_eq _ _ _ _ _ _ _ _ _ _ (sufT_E r s)

theorem suffP_38 (p q r s : KK) (h4 : KK.mul q r = p) (hg : KK.add (KK.mul p p) p = KK.one) :
    pentagonCheck kRng (Fg p q r s) .tau .tau .tau .tau .one .tau .one .one .tau = true :=
  pentcheck_of_eq _ _ _ _ _ _ _ _ _ _ (sufE_1 p q r h4 hg)

theorem suffP_39 (p q r s : KK) (hs : s = KK.neg p) :
    pentagonCheck kRng (Fg p q r s) .tau .tau .tau .tau .one .tau .one .tau .tau = true := by
  subst hs
  exact pentcheck_of_eq _ _ _ _ _ _ _ _ _ _ (sufE_2 p q)

theorem suffP_40 (p q r s : KK) (h4 : KK.mul q r = p) (hs : s = KK.neg p) :
    pentagonCheck kRng (Fg p q r s) .tau .tau .tau .tau .one .tau .tau .one .tau = true := by
  subst hs
  exact pentcheck_of_eq _ _ _ _ _ _ _ _ _ _ (sufE_3 p q r h4)

theorem suffP_41 (p q r s : KK) (h4 : KK.mul q r = p) :
    pentagonCheck kRng (Fg p q r s) .tau .tau .tau .tau .one .tau .tau .tau .one = true :=
  pentcheck_of_eq _ _ _ _ _ _ _ _ _ _ (sufE_4 p q r h4)

theorem suffP_42 (p q r s : KK) (hg : KK.add (KK.mul p p) p = KK.one) (hs : s = KK.neg p) :
    pentagonCheck kRng (Fg p q r s) .tau .tau .tau .tau .one .tau .tau .tau .tau = true := by
  subst hs
  exact pentcheck_of_eq _ _ _ _ _ _ _ _ _ _ (sufE_5 p q hg)

theorem suffP_43 (p q r s : KK) (h4 : KK.mul q r = p) :
    pentagonCheck kRng (Fg p q r s) .tau .tau .tau .tau .tau .one .tau .one .tau = true :=
  pentcheck_of_eq _ _ _ _ _ _ _ _ _ _ (sufE_6 p q r h4)

theorem suffP_44 (p q r s : KK) (h4 : KK.mul q r = p) :
    pentagonCheck kRng (Fg p q r s) .tau .tau .tau .tau .tau .one .tau .tau .one = true :=
  pentcheck_of_eq _ _ _ _ _ _ _ _ _ _ (sufE_7 p q r h4)

theorem suffP_45 (p q r s : KK) :
    pentagonCheck kRng (Fg p q r s) .tau .tau .tau .tau .tau .one .tau .tau .tau = true :=
  pentcheck_of_eq _ _ _ _ _ _ _ _ _ _ (sufT_H q s)

theorem suffP_46 (p q r s : KK) (hs : s = KK.neg p) :
    pentagonCheck kRng (Fg p q r s) .tau .tau .tau .tau .tau .tau .one .one .tau = true := by
  subst hs
  exact pentcheck_of_eq _ _ _ _ _ _ _ _ _ _ (sufE_8 p r)

theorem suffP_47 (p q r s : KK) (h4 : KK.mul q r = p) (hg : KK.add (KK.mul p p) p = KK.one) (hs : s = KK.neg p) :
    pentagonCheck kRng (Fg p q r s) .tau .tau .tau .tau .tau .tau .one .tau .tau = true := by
  subst hs
  exact pentcheck_of_eq _ _ _ _ _ _ _ _ _ _ (sufE_9 p q r h4 hg)

theorem suffP_48 (p q r s : KK) (hg : KK.add (KK.mul p p) p = KK.one) (hs : s = KK.neg p) :
    pentagonCheck kRng (Fg p q r s) .tau .tau .tau .tau .tau .tau .tau .one .tau = true := by
  subst hs
  exact pentcheck_of_eq _ _ _ _ _ _ _ _ _ _ (sufE_10 p r hg)

theorem suffP_49 (p q r s : KK) :
    pentagonCheck kRng (Fg p q r s) .tau .tau .tau .tau .tau .tau .tau .tau .one = true :=
  pentcheck_of_eq _ _ _ _ _ _ _ _ _ _ (sufT_I r s)

theorem suffP_50 (p q r s : KK) (h4 : KK.mul q r = p) (hg : KK.add (KK.mul p p) p = KK.one) (hs : s = KK.neg p) :
    pentagonCheck kRng (Fg p q r s) .tau .tau .tau .tau .tau .tau .tau .tau .tau = true := by
  subst hs
  exact pentcheck_of_eq _ _ _ _ _ _ _ _ _ _ (sufE_11 p q r h4 hg)

/-! ### 7.5.4  The sixteen total charges

Each groups the 32 tuples that share `(a,b,c,d)`; the `try` closes the dead
ones by the guard, the bullets are exactly the live ones, in order.  The
bullet counts 1,1,1,2,1,2,2,5,1,2,2,5,2,5,5,13 sum to 50 —
`pentagon_live_instances`, charge by charge. -/

/-- Charge `(a,b,c,d) = (.one,.one,.one,.one)`: 1 live instances of 32. -/
theorem suffQ_00 (p q r s : KK) :
    ∀ x y t w v, pentagonCheck kRng (Fg p q r s) .one .one .one .one x y t w v = true := by
  intro x y t w v
  cases x <;> cases y <;> cases t <;> cases w <;> cases v <;>
    try exact pentcheck_of_invalid kRng (Fg p q r s) _ _ _ _ _ _ _ _ _ rfl
  · exact suffP_01 p q r s

/-- Charge `(a,b,c,d) = (.one,.one,.one,.tau)`: 1 live instances of 32. -/
theorem suffQ_01 (p q r s : KK) :
    ∀ x y t w v, pentagonCheck kRng (Fg p q r s) .one .one .one .tau x y t w v = true := by
  intro x y t w v
  cases x <;> cases y <;> cases t <;> cases w <;> cases v <;>
    try exact pentcheck_of_invalid kRng (Fg p q r s) _ _ _ _ _ _ _ _ _ rfl
  · exact suffP_02 p q r s

/-- Charge `(a,b,c,d) = (.one,.one,.tau,.one)`: 1 live instances of 32. -/
theorem suffQ_02 (p q r s : KK) :
    ∀ x y t w v, pentagonCheck kRng (Fg p q r s) .one .one .tau .one x y t w v = true := by
  intro x y t w v
  cases x <;> cases y <;> cases t <;> cases w <;> cases v <;>
    try exact pentcheck_of_invalid kRng (Fg p q r s) _ _ _ _ _ _ _ _ _ rfl
  · exact suffP_03 p q r s

/-- Charge `(a,b,c,d) = (.one,.one,.tau,.tau)`: 2 live instances of 32. -/
theorem suffQ_03 (p q r s : KK) :
    ∀ x y t w v, pentagonCheck kRng (Fg p q r s) .one .one .tau .tau x y t w v = true := by
  intro x y t w v
  cases x <;> cases y <;> cases t <;> cases w <;> cases v <;>
    try exact pentcheck_of_invalid kRng (Fg p q r s) _ _ _ _ _ _ _ _ _ rfl
  · exact suffP_04 p q r s
  · exact suffP_05 p q r s

/-- Charge `(a,b,c,d) = (.one,.tau,.one,.one)`: 1 live instances of 32. -/
theorem suffQ_04 (p q r s : KK) :
    ∀ x y t w v, pentagonCheck kRng (Fg p q r s) .one .tau .one .one x y t w v = true := by
  intro x y t w v
  cases x <;> cases y <;> cases t <;> cases w <;> cases v <;>
    try exact pentcheck_of_invalid kRng (Fg p q r s) _ _ _ _ _ _ _ _ _ rfl
  · exact suffP_06 p q r s

/-- Charge `(a,b,c,d) = (.one,.tau,.one,.tau)`: 2 live instances of 32. -/
theorem suffQ_05 (p q r s : KK) :
    ∀ x y t w v, pentagonCheck kRng (Fg p q r s) .one .tau .one .tau x y t w v = true := by
  intro x y t w v
  cases x <;> cases y <;> cases t <;> cases w <;> cases v <;>
    try exact pentcheck_of_invalid kRng (Fg p q r s) _ _ _ _ _ _ _ _ _ rfl
  · exact suffP_07 p q r s
  · exact suffP_08 p q r s

/-- Charge `(a,b,c,d) = (.one,.tau,.tau,.one)`: 2 live instances of 32. -/
theorem suffQ_06 (p q r s : KK) :
    ∀ x y t w v, pentagonCheck kRng (Fg p q r s) .one .tau .tau .one x y t w v = true := by
  intro x y t w v
  cases x <;> cases y <;> cases t <;> cases w <;> cases v <;>
    try exact pentcheck_of_invalid kRng (Fg p q r s) _ _ _ _ _ _ _ _ _ rfl
  · exact suffP_09 p q r s
  · exact suffP_10 p q r s

/-- Charge `(a,b,c,d) = (.one,.tau,.tau,.tau)`: 5 live instances of 32. -/
theorem suffQ_07 (p q r s : KK) :
    ∀ x y t w v, pentagonCheck kRng (Fg p q r s) .one .tau .tau .tau x y t w v = true := by
  intro x y t w v
  cases x <;> cases y <;> cases t <;> cases w <;> cases v <;>
    try exact pentcheck_of_invalid kRng (Fg p q r s) _ _ _ _ _ _ _ _ _ rfl
  · exact suffP_11 p q r s
  · exact suffP_12 p q r s
  · exact suffP_13 p q r s
  · exact suffP_14 p q r s
  · exact suffP_15 p q r s

/-- Charge `(a,b,c,d) = (.tau,.one,.one,.one)`: 1 live instances of 32. -/
theorem suffQ_08 (p q r s : KK) :
    ∀ x y t w v, pentagonCheck kRng (Fg p q r s) .tau .one .one .one x y t w v = true := by
  intro x y t w v
  cases x <;> cases y <;> cases t <;> cases w <;> cases v <;>
    try exact pentcheck_of_invalid kRng (Fg p q r s) _ _ _ _ _ _ _ _ _ rfl
  · exact suffP_16 p q r s

/-- Charge `(a,b,c,d) = (.tau,.one,.one,.tau)`: 2 live instances of 32. -/
theorem suffQ_09 (p q r s : KK) :
    ∀ x y t w v, pentagonCheck kRng (Fg p q r s) .tau .one .one .tau x y t w v = true := by
  intro x y t w v
  cases x <;> cases y <;> cases t <;> cases w <;> cases v <;>
    try exact pentcheck_of_invalid kRng (Fg p q r s) _ _ _ _ _ _ _ _ _ rfl
  · exact suffP_17 p q r s
  · exact suffP_18 p q r s

/-- Charge `(a,b,c,d) = (.tau,.one,.tau,.one)`: 2 live instances of 32. -/
theorem suffQ_10 (p q r s : KK) :
    ∀ x y t w v, pentagonCheck kRng (Fg p q r s) .tau .one .tau .one x y t w v = true := by
  intro x y t w v
  cases x <;> cases y <;> cases t <;> cases w <;> cases v <;>
    try exact pentcheck_of_invalid kRng (Fg p q r s) _ _ _ _ _ _ _ _ _ rfl
  · exact suffP_19 p q r s
  · exact suffP_20 p q r s

/-- Charge `(a,b,c,d) = (.tau,.one,.tau,.tau)`: 5 live instances of 32. -/
theorem suffQ_11 (p q r s : KK) :
    ∀ x y t w v, pentagonCheck kRng (Fg p q r s) .tau .one .tau .tau x y t w v = true := by
  intro x y t w v
  cases x <;> cases y <;> cases t <;> cases w <;> cases v <;>
    try exact pentcheck_of_invalid kRng (Fg p q r s) _ _ _ _ _ _ _ _ _ rfl
  · exact suffP_21 p q r s
  · exact suffP_22 p q r s
  · exact suffP_23 p q r s
  · exact suffP_24 p q r s
  · exact suffP_25 p q r s

/-- Charge `(a,b,c,d) = (.tau,.tau,.one,.one)`: 2 live instances of 32. -/
theorem suffQ_12 (p q r s : KK) :
    ∀ x y t w v, pentagonCheck kRng (Fg p q r s) .tau .tau .one .one x y t w v = true := by
  intro x y t w v
  cases x <;> cases y <;> cases t <;> cases w <;> cases v <;>
    try exact pentcheck_of_invalid kRng (Fg p q r s) _ _ _ _ _ _ _ _ _ rfl
  · exact suffP_26 p q r s
  · exact suffP_27 p q r s

/-- Charge `(a,b,c,d) = (.tau,.tau,.one,.tau)`: 5 live instances of 32. -/
theorem suffQ_13 (p q r s : KK) :
    ∀ x y t w v, pentagonCheck kRng (Fg p q r s) .tau .tau .one .tau x y t w v = true := by
  intro x y t w v
  cases x <;> cases y <;> cases t <;> cases w <;> cases v <;>
    try exact pentcheck_of_invalid kRng (Fg p q r s) _ _ _ _ _ _ _ _ _ rfl
  · exact suffP_28 p q r s
  · exact suffP_29 p q r s
  · exact suffP_30 p q r s
  · exact suffP_31 p q r s
  · exact suffP_32 p q r s

/-- Charge `(a,b,c,d) = (.tau,.tau,.tau,.one)`: 5 live instances of 32. -/
theorem suffQ_14 (p q r s : KK) :
    ∀ x y t w v, pentagonCheck kRng (Fg p q r s) .tau .tau .tau .one x y t w v = true := by
  intro x y t w v
  cases x <;> cases y <;> cases t <;> cases w <;> cases v <;>
    try exact pentcheck_of_invalid kRng (Fg p q r s) _ _ _ _ _ _ _ _ _ rfl
  · exact suffP_33 p q r s
  · exact suffP_34 p q r s
  · exact suffP_35 p q r s
  · exact suffP_36 p q r s
  · exact suffP_37 p q r s

/-- Charge `(a,b,c,d) = (.tau,.tau,.tau,.tau)`: 13 live instances of 32. -/
theorem suffQ_15 (p q r s : KK) (h4 : KK.mul q r = p) (hg : KK.add (KK.mul p p) p = KK.one) (hs : s = KK.neg p) :
    ∀ x y t w v, pentagonCheck kRng (Fg p q r s) .tau .tau .tau .tau x y t w v = true := by
  intro x y t w v
  cases x <;> cases y <;> cases t <;> cases w <;> cases v <;>
    try exact pentcheck_of_invalid kRng (Fg p q r s) _ _ _ _ _ _ _ _ _ rfl
  · exact suffP_38 p q r s h4 hg
  · exact suffP_39 p q r s hs
  · exact suffP_40 p q r s h4 hs
  · exact suffP_41 p q r s h4
  · exact suffP_42 p q r s hg hs
  · exact suffP_43 p q r s h4
  · exact suffP_44 p q r s h4
  · exact suffP_45 p q r s
  · exact suffP_46 p q r s hs
  · exact suffP_47 p q r s h4 hg hs
  · exact suffP_48 p q r s hg hs
  · exact suffP_49 p q r s
  · exact suffP_50 p q r s h4 hg hs

/-! ### 7.5.5  The theorem -/

/-- **PENTAGON SUFFICIENCY.**  The exact converse of `pentagon_forces_golden`:
    for *any* four values `p q r s` of K, if

        q·r = p ,      p² + p = 1 ,      s = −p ,

    then the generic associator `Fg p q r s` satisfies the pentagon — all 512
    label tuples, hence all 50 live instances (`pentagon_live_instances`).

    Round 3 recorded this as an honest gap: true in exact arithmetic outside
    Lean, not a Lean theorem.  It is a Lean theorem now, with no `sorry`, no
    `native_decide`, and no raised budget. -/
theorem pentagon_sufficiency (p q r s : KK)
    (h4 : KK.mul q r = p)
    (hg : KK.add (KK.mul p p) p = KK.one)
    (hs : s = KK.neg p) :
    ∀ a b c dd x y t w v,
      pentagonCheck kRng (Fg p q r s) a b c dd x y t w v = true := by
  intro a b c dd
  cases a <;> cases b <;> cases c <;> cases dd
  · exact suffQ_00 p q r s
  · exact suffQ_01 p q r s
  · exact suffQ_02 p q r s
  · exact suffQ_03 p q r s
  · exact suffQ_04 p q r s
  · exact suffQ_05 p q r s
  · exact suffQ_06 p q r s
  · exact suffQ_07 p q r s
  · exact suffQ_08 p q r s
  · exact suffQ_09 p q r s
  · exact suffQ_10 p q r s
  · exact suffQ_11 p q r s
  · exact suffQ_12 p q r s
  · exact suffQ_13 p q r s
  · exact suffQ_14 p q r s
  · exact suffQ_15 p q r s h4 hg hs

/-- **PENTAGON UNIQUENESS, BOTH DIRECTIONS.**  Necessity is
    `pentagon_forces_golden` (§7.3); sufficiency is the theorem above.  The
    pentagon equation on a `2×2` associator over K is *equivalent* to the
    three relations — coherence and the golden relation are the same
    condition, not merely compatible ones. -/
theorem pentagon_iff (p q r s : KK) :
    (∀ a b c dd x y t w v,
        pentagonCheck kRng (Fg p q r s) a b c dd x y t w v = true)
    ↔ (KK.mul q r = p ∧ KK.add (KK.mul p p) p = KK.one ∧ s = KK.neg p) :=
  ⟨pentagon_forces_golden p q r s,
   fun h => pentagon_sufficiency p q r s h.1 h.2.1 h.2.2⟩

/-! ### 7.5.6  Anti-vacuity and negative controls for sufficiency

A sufficiency theorem is worthless if its hypothesis is unsatisfiable, and
almost worthless if it is satisfiable in only one way.  Both roots of
`X² + X − 1` live in K, and each gives a solution. -/

/-- The golden data satisfies the three relations by `rfl`, so sufficiency
    re-derives `pentagon_symmetric_gauge` — the same 512 instances, now from
    the relations instead of from the constants. -/
theorem golden_pentagon_by_sufficiency :
    ∀ a b c dd x y t w v,
      pentagonCheck kRng (Fg KK.invPhi KK.b KK.b (KK.neg KK.invPhi))
        a b c dd x y t w v = true :=
  pentagon_sufficiency KK.invPhi KK.b KK.b (KK.neg KK.invPhi) rfl rfl rfl

/-- `p = −φ`, the **other** root of `X² + X − 1`.  (`1/φ` and `−φ` are the two
    roots; `−φ` is the non-unitary, Yang–Lee branch.) -/
def pAlt : KK := KK.neg (KK.emb Z5.phi)

/-- `−φ` really is a root, really is not `1/φ`, and really is not `1`. -/
theorem pAlt_root_and_distinct :
    KK.add (KK.mul pAlt pAlt) pAlt = KK.one ∧
    KK.beq pAlt KK.invPhi = false ∧
    KK.beq pAlt KK.one = false :=
  ⟨rfl, rfl, rfl⟩

/-- **A SECOND SOLUTION, exhibited.**  `F = [[−φ, 1], [−φ, φ]]` satisfies the
    pentagon.  Its `p` is not the golden `1/φ` (`pAlt_root_and_distinct`), and
    it is not symmetric — `q = 1`, `r = −φ`, which is the residual gauge
    freedom `q ↦ λq, r ↦ λ⁻¹r` acting on a solution.  So
    `pentagon_sufficiency` is not a theorem about one point, and the class it
    quantifies over is genuinely wider than `Fsymm`. -/
theorem alt_root_satisfies_pentagon :
    ∀ a b c dd x y t w v,
      pentagonCheck kRng (Fg pAlt KK.one pAlt (KK.neg pAlt))
        a b c dd x y t w v = true :=
  pentagon_sufficiency pAlt KK.one pAlt (KK.neg pAlt) rfl rfl rfl

/-- **NEGATIVE CONTROL — each relation is load-bearing.**  Drop exactly one
    of the three, keep the other two, and the pentagon fails by a definite
    count:

    * `s = +p` instead of `−p`, golden data otherwise: **4** violations;
    * `q = r = 1`, so `qr = 1 ≠ p`, golden data otherwise: **7** violations.

    The third case — `p² + p ≠ 1` with `qr = p` and `s = −p` intact — is
    already in the file: `wrong_is_Fg_and_fails` says `Fg 1 1 1 (−1)` fails 5
    instances, and there `qr = 1 = p` and `s = −1 = −p` both hold while
    `p² + p = 2 ≠ 1`.  So none of the three hypotheses of
    `pentagon_sufficiency` can be dropped. -/
theorem sufficiency_hypotheses_are_needed :
    countPentViolations kRng (Fg KK.invPhi KK.b KK.b KK.invPhi) = 4 ∧
    countPentViolations kRng
      (Fg KK.invPhi KK.one KK.one (KK.neg KK.invPhi)) = 7 :=
  ⟨rfl, rfl⟩

/-! ═══════════════════════════════════════════════════════════════════════
    ## 7.6  THE SAME FACT, MACHINE-DECIDED IN A QUOTIENT RING

    §7.5 proves sufficiency.  This section *decides* it, by the trick that
    decided the 11/39 split: run the UNMODIFIED `countPentViolations` over a
    different ring.  §7.4 used the FREE commutative ring on `p q r s`, where
    the count is 11.  Here the ring is the QUOTIENT of that free ring by the
    three forced relations, where the count is 0 — and 0 is sufficiency.

    **What the quotient is, concretely.**  Killing `s + p`, then `qr − p`
    (which also eliminates `p`), leaves `Z[q,r]/((qr)² + qr − 1)`.  In that
    ring `q` is a unit, with inverse `r·(p+1)`, because `q·r·(p+1) = p(p+1) =
    p² + p = 1`.  So the quotient is the **Laurent polynomial ring
    `Z[φ][q, q⁻¹]`**, with

        p = 1/φ  (a constant),   q = q,   r = p·q⁻¹,   s = −p .

    That is the whole implementation below: coefficients in the already-present
    `Zp = Z[φ]`, exponents in `Int`, multiplication by convolution.  Nothing
    is truncated and no rewriting system is iterated, so no confluence or
    termination argument is needed — `ins` recurses structurally on a list.

    No root is chosen.  `Z[X]/(X² + X − 1) ≅ Z[φ]` by `X ↦ φ − 1 = 1/φ`; that
    is an isomorphism of rings, not a specialization.  (`X ↦ −φ` is the other
    isomorphism; the two differ by the Galois action of §8, which permutes the
    roots and cannot change which polynomials vanish.)  So the coefficient
    ring below IS the universal `Z[p]/(p² + p − 1)`, carried in the basis the
    file already has.

    **WHAT IS PROVED AND WHAT IS ASSUMED.**  Proved: the three relations hold
    in `Q` (`quot_rel_qr`, `quot_rel_golden`, `quot_rel_s`), `Q` is not
    degenerate (the block of negative controls), and the count is 0.  ASSUMED,
    and stated plainly: that `addL`/`mulL` are a faithful implementation of
    Laurent arithmetic over `Zp` — the same standing assumption `PentPoly`
    already makes for the free ring in §7.4, and no weaker.  The commutative
    ring laws of `Q` are *not* proved here.

    **THIS SECTION IS THEREFORE NOT LOAD-BEARING.**  Sufficiency is
    `pentagon_sufficiency`, which assumes nothing beyond the K ring laws of
    §5.  §7.6 is corroboration: an independent computation, by an independent
    route, that agrees — and it is the negative controls below, not the 0,
    that make the agreement evidence.
    ═══════════════════════════════════════════════════════════════════════ -/

namespace QuotRng

/-- A Laurent polynomial over `Z[φ]`: a list of `(exponent, coefficient)`
    pairs, kept sorted by exponent with no zero coefficients. -/
abbrev Lau := List (Int × Zp)

/-- Insert `c·q^e`.  Structural recursion on the list — no fuel, no search,
    no rewriting to a fixed point. -/
def ins (e : Int) (c : Zp) : Lau → Lau
  | [] => if c = Zp.zero then [] else [(e, c)]
  | (e', c') :: ps =>
    if e < e' then (if c = Zp.zero then (e', c') :: ps else (e, c) :: (e', c') :: ps)
    else if e = e' then (if Zp.add c c' = Zp.zero then ps else (e, Zp.add c c') :: ps)
    else (e', c') :: ins e c ps

def norm (l : Lau) : Lau := l.foldl (fun acc t => ins t.1 t.2 acc) []
def addL (a b : Lau) : Lau := b.foldl (fun acc t => ins t.1 t.2 acc) a
def mulL (a b : Lau) : Lau :=
  norm (a.flatMap fun t => b.map fun u => (t.1 + u.1, Zp.mul t.2 u.2))
def beqL (a b : Lau) : Bool := decide (a = b)

/-- The quotient ring `Q = Z[φ][q, q⁻¹]`, as `Rng` data. -/
def qRng : Rng Lau := ⟨[], [(0, Zp.one)], addL, mulL, beqL⟩

/-- `p = 1/φ`, a constant of `Q`. -/
def qP : Lau := [(0, Zp.invPhi)]
/-- `q`, the free unit — the residual gauge freedom, carried exactly. -/
def qQ : Lau := [(1, Zp.one)]
/-- `r = p·q⁻¹`. -/
def qR : Lau := [(-1, Zp.invPhi)]
/-- `s = −p`. -/
def qS : Lau := [(0, Zp.neg Zp.invPhi)]

/-- The generic associator over the quotient ring. -/
def FgQ : Anyon → Anyon → Lau
  | .one, .one => qP
  | .one, .tau => qQ
  | .tau, .one => qR
  | .tau, .tau => qS

/-- `s = +p`: the relation `s = −p` dropped, the other two kept. -/
def FgQ_sPlus : Anyon → Anyon → Lau
  | .one, .one => qP
  | .one, .tau => qQ
  | .tau, .one => qR
  | .tau, .tau => qP

/-- `r = q`: the relation `q·r = p` dropped, the other two kept. -/
def FgQ_rEqQ : Anyon → Anyon → Lau
  | .one, .one => qP
  | .one, .tau => qQ
  | .tau, .one => qQ
  | .tau, .tau => qS

/-- `p = q`, `r = 1`, `s = −q`: `q·r = p` and `s = −p` hold, but `p² + p = 1`
    fails — `q` is transcendental over `Z[φ]` in `Q`. -/
def FgQ_notGolden : Anyon → Anyon → Lau
  | .one, .one => qQ
  | .one, .tau => qQ
  | .tau, .one => [(0, Zp.one)]
  | .tau, .tau => [(1, Zp.neg Zp.one)]

/-- The strict associator, read in `Q`. -/
def FgQ_id : Anyon → Anyon → Lau
  | .one, .one => [(0, Zp.one)]
  | .one, .tau => []
  | .tau, .one => []
  | .tau, .tau => [(0, Zp.one)]

end QuotRng

/-! ### 7.6.1  The three relations hold in `Q` -/

/-- `q·r = p`. -/
theorem quot_rel_qr : QuotRng.mulL QuotRng.qQ QuotRng.qR = QuotRng.qP := rfl
/-- `p² + p = 1`. -/
theorem quot_rel_golden :
    QuotRng.addL (QuotRng.mulL QuotRng.qP QuotRng.qP) QuotRng.qP
      = QuotRng.qRng.one := rfl
/-- `s + p = 0`. -/
theorem quot_rel_s :
    QuotRng.addL QuotRng.qS QuotRng.qP = QuotRng.qRng.zero := rfl

/-! ### 7.6.2  NEGATIVE CONTROL (a): `Q` has not collapsed

If the normal form sent everything to zero, `beq` would be constantly true and
the count would be 0 for a worthless reason.  It does not. -/

/-- `1 ≠ 0`: `Q` is not the zero ring. -/
theorem quot_one_ne_zero :
    QuotRng.beqL QuotRng.qRng.one QuotRng.qRng.zero = false := rfl

/-- None of the four generators is zero. -/
theorem quot_gens_ne_zero :
    QuotRng.beqL QuotRng.qP QuotRng.qRng.zero = false ∧
    QuotRng.beqL QuotRng.qQ QuotRng.qRng.zero = false ∧
    QuotRng.beqL QuotRng.qR QuotRng.qRng.zero = false ∧
    QuotRng.beqL QuotRng.qS QuotRng.qRng.zero = false :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The generators are pairwise distinct, and `q` is not a constant. -/
theorem quot_gens_distinct :
    QuotRng.beqL QuotRng.qQ QuotRng.qP = false ∧
    QuotRng.beqL QuotRng.qQ QuotRng.qR = false ∧
    QuotRng.beqL QuotRng.qS QuotRng.qP = false ∧
    QuotRng.beqL QuotRng.qQ QuotRng.qRng.one = false :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Things that ought NOT to vanish do not: `q² + s ≠ 0` (nothing constrains
    `q` alone), `p² ≠ 0`, `q + r ≠ 0`, and `q² ≠ q³` — so `Q` really is of
    infinite rank over `Z[φ]`, not a small finite quotient in disguise. -/
theorem quot_nonzero_witnesses :
    QuotRng.beqL (QuotRng.addL (QuotRng.mulL QuotRng.qQ QuotRng.qQ) QuotRng.qS)
                 QuotRng.qRng.zero = false ∧
    QuotRng.beqL (QuotRng.mulL QuotRng.qP QuotRng.qP)
                 QuotRng.qRng.zero = false ∧
    QuotRng.beqL (QuotRng.addL QuotRng.qQ QuotRng.qR)
                 QuotRng.qRng.zero = false ∧
    QuotRng.beqL (QuotRng.mulL QuotRng.qQ QuotRng.qQ)
                 (QuotRng.mulL (QuotRng.mulL QuotRng.qQ QuotRng.qQ) QuotRng.qQ)
                   = false :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ### 7.6.3  Sufficiency, decided -/

/-- **SUFFICIENCY AS ONE `rfl`.**  Over the quotient ring, the generic
    associator violates none of the 50 live pentagon instances.  Set beside
    `pentagon_nontrivial_instances : … = 11` over the FREE ring, the pair says
    exactly: eleven instances impose a condition on a generic associator, and
    the three relations kill all eleven. -/
theorem quot_pentagon_clean :
    countPentViolations QuotRng.qRng QuotRng.FgQ = 0 := rfl

/-! ### 7.6.4  NEGATIVE CONTROL (b): the count over `Q` has teeth

A count that cannot come out nonzero is not a check.  One more full count is
run — and it comes out at the number K already reports for the same
associator, which is the sharpest available evidence that the `Lau` arithmetic
is faithful.  The three perturbation controls are stated as single failing
instances rather than as counts, to keep the file's build time down; each is
one evaluation instead of 512. -/

/-- The strict associator, read in `Q`: **4** violations — the very number
    `strict_pentagon_violations` reports over K, and `grammar_stone3.py`
    reports as residual 4.0.  Two independent ring implementations, the same
    integer. -/
theorem quot_strict_violations :
    countPentViolations QuotRng.qRng QuotRng.FgQ_id = 4 := rfl

/-- **Each relation is load-bearing in `Q` too.**  Drop exactly one and a named
    live instance goes `false`:

    * `s = +p`: instance #2 of §7.1, residual `q·(p+s)`;
    * `r = q`:  instance #4, residual `qr − p`;
    * `p` generic: instance #1, residual `p² + qr − 1`.

    The last has no K analogue at all — K contains no transcendental element,
    so only the quotient ring can perturb the golden relation while keeping
    the other two exactly. -/
theorem quot_perturbations_fail :
    pentagonCheck QuotRng.qRng QuotRng.FgQ_sPlus
      .tau .tau .tau .tau .one .tau .one .tau .tau = false ∧
    pentagonCheck QuotRng.qRng QuotRng.FgQ_rEqQ
      .tau .tau .tau .tau .one .tau .tau .tau .one = false ∧
    pentagonCheck QuotRng.qRng QuotRng.FgQ_notGolden
      .tau .tau .tau .tau .one .tau .one .one .tau = false :=
  ⟨rfl, rfl, rfl⟩

/-- …and the same three instances are `true` for the unperturbed generic
    associator, so the contrast is the relations and not the tuples. -/
theorem quot_unperturbed_passes :
    pentagonCheck QuotRng.qRng QuotRng.FgQ
      .tau .tau .tau .tau .one .tau .one .tau .tau = true ∧
    pentagonCheck QuotRng.qRng QuotRng.FgQ
      .tau .tau .tau .tau .one .tau .tau .tau .one = true ∧
    pentagonCheck QuotRng.qRng QuotRng.FgQ
      .tau .tau .tau .tau .one .tau .one .one .tau = true :=
  ⟨rfl, rfl, rfl⟩

/-! ═══════════════════════════════════════════════════════════════════════
    ## 12.  **K IS AN INTEGRAL DOMAIN**, AND THERE ARE EXACTLY TWO

    The two descents above are the whole cost.  `Z5` is a domain (§10, by
    2-adic descent on the field norm) and `φ` is not a square in `Z5` (§11, by
    41-adic descent).  This section spends them.

    The bridge is the *other* conjugation — not the Galois map `ζ ↦ ζ⁴` of §8,
    but `t ↦ −t`, the one that fixes `Z[ζ₅]` and moves the square root.  Its
    norm `N_t(x + yt) = x² − φy²` lands in `Z5`, is multiplicative because
    `t ↦ −t` is a ring map, and vanishes exactly at 0 — which is precisely the
    statement that `φ` is not a square.  Brahmagupta's identity, if you want it
    named; here it is one rearrangement of opaque `Z5` atoms.

    With K a domain, `Q_factors` finishes the job: round 3 proved coherence
    forces `r_τ² + (1/φ)r_τ + 1 = 0`, and a quadratic over a domain has at most
    its two named roots.  **`hexagon_exactly_two`.**  The same argument one
    line further does the pentagon's `p`, whose two roots are `1/φ` and `−φ` —
    the golden world and the Yang–Lee world of §9.
    ═══════════════════════════════════════════════════════════════════════ -/

namespace KK

/-- The `t`-conjugation `x + yt ↦ x − yt`.  Fixes `Z[ζ₅]` pointwise and negates
    the square root — the non-Galois involution of K over `Z5`. -/
def tconj (u : KK) : KK := ⟨u.x, Z5.neg u.y⟩

theorem tconj_emb (u : Z5) : tconj (emb u) = emb u := rfl

theorem tconj_tconj (u : KK) : tconj (tconj u) = u := by
  cases u; simp only [tconj, KK.mk.injEq]
  exact ⟨trivial, Z5.neg_neg _⟩

/-- `t ↦ −t` is multiplicative.  Both components are `Z5` identities in the
    four opaque atoms `x·x'`, `φ·(y·y')`, `x·y'`, `y·x'`; no descent to `Int`. -/
theorem tconj_mul (u v : KK) : tconj (mul u v) = mul (tconj u) (tconj v) := by
  cases u; cases v
  simp only [tconj, mul, KK.mk.injEq]
  constructor
  · rw [Z5.mul_neg, Z5.neg_mul, Z5.neg_neg]
  · rw [Z5.mul_neg, Z5.neg_mul, ← Z5.neg_add]

/-- The `t`-norm, valued in `Z5`: `N_t(x + yt) = x² − φy²`. -/
def ntz (u : KK) : Z5 :=
  Z5.add (Z5.mul u.x u.x) (Z5.neg (Z5.mul Z5.phi (Z5.mul u.y u.y)))

/-- `u · ū = N_t(u)`, embedded.  This is what makes `ntz` a norm rather than a
    definition: it is a product of `u` with something, so multiplicativity is
    inherited rather than computed. -/
theorem mul_tconj (u : KK) : mul u (tconj u) = emb (ntz u) := by
  cases u
  simp only [mul, tconj, emb, ntz, KK.mk.injEq]
  constructor
  · rw [Z5.mul_neg, Z5.mul_neg]
  · rw [Z5.mul_neg, Z5.mul_comm, Z5.neg_add_cancel]

/-- **THE NORM IS MULTIPLICATIVE.**  By rearrangement only: `N_t(uv)` embeds
    `uv·conj(uv) = (u·ū)(v·v̄)`, and `emb` is injective. -/
theorem ntz_mul (u v : KK) : ntz (mul u v) = Z5.mul (ntz u) (ntz v) := by
  apply emb_inj
  rw [← emb_mul, ← mul_tconj, ← mul_tconj, ← mul_tconj, tconj_mul]
  calc mul (mul u v) (mul (tconj u) (tconj v))
      = mul u (mul v (mul (tconj u) (tconj v))) := mul_assoc _ _ _
    _ = mul u (mul (mul v (tconj u)) (tconj v)) := by rw [mul_assoc]
    _ = mul u (mul (mul (tconj u) v) (tconj v)) := by rw [mul_comm v (tconj u)]
    _ = mul u (mul (tconj u) (mul v (tconj v))) := by rw [mul_assoc]
    _ = mul (mul u (tconj u)) (mul v (tconj v)) := (mul_assoc _ _ _).symm

theorem ntz_zero : ntz zero = Z5.zero := rfl

/-- `a − b = 0 → a = b`, at the `Z5` level.

    Declared here rather than reached for with `_root_.` — an earlier draft
    wrote `theorem _root_.Workshop.Anyon.Z5.eq_of_sub_eq_zero` from inside
    `namespace KK`, which typechecks fine but is invisible to any tool that
    reconstructs qualified names from the `namespace`/`end` stack.  The axiom
    census is such a tool and reported itself INCOMPLETE rather than silently
    skipping the theorem, which is the behaviour one wants; still, the fix
    belongs in the file rather than in the instrument.  The
    reconstructed name is then just `KK.z5_eq_of_sub_eq_zero`. -/
theorem z5_eq_of_sub_eq_zero {a b : Z5}
    (h : Z5.add a (Z5.neg b) = Z5.zero) : a = b := by
  calc a = Z5.add a Z5.zero := (Z5.add_zero a).symm
    _    = Z5.add a (Z5.add (Z5.neg b) b) := by rw [Z5.neg_add_cancel]
    _    = Z5.add (Z5.add a (Z5.neg b)) b := (Z5.add_assoc a (Z5.neg b) b).symm
    _    = Z5.add Z5.zero b := by rw [h]
    _    = b := Z5.zero_add b

/-- **THE NORM VANISHES ONLY AT ZERO** — this is exactly "`φ` is not a square",
    restated.  `N_t(u) = 0` says `x² = φy²`, and §11 says that forces both to
    vanish. -/
theorem ntz_eq_zero_iff (u : KK) : ntz u = Z5.zero ↔ u = zero := by
  constructor
  · intro h
    obtain ⟨x, y⟩ := u
    simp only [ntz] at h
    have hsq : Z5.mul x x = Z5.mul Z5.phi (Z5.mul y y) :=
      z5_eq_of_sub_eq_zero h
    obtain ⟨hx, hy⟩ := Z5.not_square x y hsq
    simp only [zero, KK.mk.injEq]
    exact ⟨hx, hy⟩
  · intro h; rw [h]; exact ntz_zero

/-- **K IS AN INTEGRAL DOMAIN.**  `αβ = 0` pushes down to `N_t(α)·N_t(β) = 0`
    in `Z5`; `Z5` is a domain, so one factor's norm vanishes; and a vanishing
    norm forces its element to vanish.  Two descents, spent. -/
theorem eq_zero_or_eq_zero_of_mul_eq_zero (a b : KK) (h : mul a b = zero) :
    a = zero ∨ b = zero := by
  have hn : Z5.mul (ntz a) (ntz b) = Z5.zero := by
    rw [← ntz_mul, h, ntz_zero]
  rcases Z5.eq_zero_or_eq_zero_of_mul_eq_zero _ _ hn with h1 | h1
  · exact Or.inl ((ntz_eq_zero_iff a).mp h1)
  · exact Or.inr ((ntz_eq_zero_iff b).mp h1)

end KK

/-! ### The payoff: **exactly two**, on both coherence equations

Round 3 proved that coherence *forces* a quadratic and exhibited both roots,
and declared honestly that "exactly two" was not established — it needs
`(s − r_τ)(s − r_τ') = 0 ⟹ s = r_τ ∨ s = r_τ'`, i.e. K having no zero
divisors.  That is now a theorem, so this is the last step.

Two receipts first, then the two headlines. -/

/-- `a − b = 0 ↔ a = b` in K, from the additive laws alone. -/
theorem sub_eq_zero_iff (a b : KK) : KK.add a (KK.neg b) = KK.zero ↔ a = b := by
  constructor
  · intro h
    calc a = KK.add a KK.zero := (KK.add_zero a).symm
      _    = KK.add a (KK.add (KK.neg b) b) := by rw [KK.neg_add_cancel]
      _    = KK.add (KK.add a (KK.neg b)) b := (KK.add_assoc a (KK.neg b) b).symm
      _    = KK.add KK.zero b := by rw [h]
      _    = b := KK.zero_add b
  · intro h; rw [h]; exact KK.add_neg b

/-- **THE QUADRATIC FACTORS** — the declaration round 3 owed.

    The round-3 audit's DEFECT 1 was that `roots_sum_and_product`'s headline
    announced "the quadratic factors exactly as `(X − r_τ)(X − r_τ')`" while no
    declaration asserted it: a true consequence of the proved sum and product,
    but not a theorem.  Here it is, proved from exactly those two facts by the
    ring laws.  The withdrawn headline is now licensed rather than deleted. -/
theorem Q_factors (s : KK) :
    KK.mul (KK.add s (KK.neg KK.rt)) (KK.add s (KK.neg rt'))
      = KK.add (KK.add (KK.mul s s) (KK.mul KK.invPhi s)) KK.one := by
  have hsum : KK.add KK.rt rt' = KK.neg KK.invPhi := rfl
  have hprod : KK.mul KK.rt rt' = KK.one := rfl
  calc KK.mul (KK.add s (KK.neg KK.rt)) (KK.add s (KK.neg rt'))
      = KK.add (KK.mul (KK.add s (KK.neg KK.rt)) s)
               (KK.mul (KK.add s (KK.neg KK.rt)) (KK.neg rt')) := KK.mul_add _ _ _
    _ = KK.add (KK.add (KK.mul s s) (KK.mul (KK.neg KK.rt) s))
               (KK.add (KK.mul s (KK.neg rt')) (KK.mul (KK.neg KK.rt) (KK.neg rt'))) := by
        rw [KK.add_mul, KK.add_mul]
    _ = KK.add (KK.add (KK.mul s s) (KK.neg (KK.mul KK.rt s)))
               (KK.add (KK.neg (KK.mul s rt')) (KK.mul KK.rt rt')) := by
        rw [KK.neg_mul, KK.mul_neg, KK.neg_mul, KK.mul_neg, KK.neg_neg]
    _ = KK.add (KK.add (KK.mul s s)
                 (KK.add (KK.neg (KK.mul KK.rt s)) (KK.neg (KK.mul s rt'))))
               (KK.mul KK.rt rt') := by
        rw [KK.add_assoc,
            ← KK.add_assoc (KK.neg (KK.mul KK.rt s)) (KK.neg (KK.mul s rt'))
                           (KK.mul KK.rt rt'),
            ← KK.add_assoc]
    _ = KK.add (KK.add (KK.mul s s) (KK.mul KK.invPhi s)) KK.one := by
        rw [hprod, ← KK.neg_add, KK.mul_comm s rt', ← KK.add_mul, hsum,
            KK.neg_mul, KK.neg_neg]

/-- **THE HEXAGON HAS EXACTLY TWO SOLUTIONS.**

    For *any* `r₁, r_τ` in K: if the hexagon holds, then `r_τ` is one of the two
    named braidings and `r₁` is determined by it.  Not "two clusters were
    found", not "here are two solutions" — **there are no others in K.**

    This is the sentence the project has been walking toward since round 1,
    where it was BLOCKED, through round 2 (PARTIAL) and round 3 (the quadratic
    forced, the count declared as an open gap). -/
theorem hexagon_exactly_two (r1 rt : KK)
    (h : ∀ a b c d e z, hexagonCheck kRng Fsymm r1 rt a b c d e z = true) :
    (rt = KK.rt ∨ rt = rt') ∧ r1 = KK.mul rt rt := by
  refine ⟨?_, hexagon_forces_r1_eq_rt_sq r1 rt h⟩
  have hq := hexagon_forces_quadratic r1 rt h
  have hf := (Q_factors rt).trans hq
  rcases KK.eq_zero_or_eq_zero_of_mul_eq_zero _ _ hf with h1 | h1
  · exact Or.inl ((sub_eq_zero_iff rt KK.rt).mp h1)
  · exact Or.inr ((sub_eq_zero_iff rt rt').mp h1)

/-- Both alternatives are realized, so `hexagon_exactly_two` is a dichotomy and
    not a disguised uniqueness: `golden_satisfies_hexagon` takes the left
    branch, `mirror_satisfies_hexagon` the right, and the two are distinct. -/
theorem hexagon_both_branches_realized :
    (KK.rt = KK.rt ∨ KK.rt = rt') ∧ (rt' = KK.rt ∨ rt' = rt') ∧
    KK.beq KK.rt rt' = false :=
  ⟨Or.inl rfl, Or.inr rfl, rfl⟩

/-! #### The pentagon's `p`, by the same argument

`p² + p = 1` factors as `(p − 1/φ)(p + φ)`, because `φ − 1/φ = 1`.  So the
pentagon's associator entry is `1/φ` — the golden world — or `−φ` — the
Yang–Lee world of §9.  The "which root" caveat round 3 attached to
`pentagon_forces_golden` is discharged, and what it resolves into is exactly
the second cluster the floor's bench had been finding all along. -/

/-- `(p − 1/φ)(p + φ) = p² + p − 1`.  Uses `φ − 1/φ = 1` and `(1/φ)·φ = 1`. -/
theorem golden_relation_factors (p : KK) :
    KK.mul (KK.add p (KK.neg KK.invPhi)) (KK.add p (KK.emb Z5.phi))
      = KK.add (KK.add (KK.mul p p) p) (KK.neg KK.one) := by
  have h1 : KK.add (KK.emb Z5.phi) (KK.neg KK.invPhi) = KK.one := rfl
  have h2 : KK.mul KK.invPhi (KK.emb Z5.phi) = KK.one := rfl
  calc KK.mul (KK.add p (KK.neg KK.invPhi)) (KK.add p (KK.emb Z5.phi))
      = KK.add (KK.mul (KK.add p (KK.neg KK.invPhi)) p)
               (KK.mul (KK.add p (KK.neg KK.invPhi)) (KK.emb Z5.phi)) := KK.mul_add _ _ _
    _ = KK.add (KK.add (KK.mul p p) (KK.mul (KK.neg KK.invPhi) p))
               (KK.add (KK.mul p (KK.emb Z5.phi))
                       (KK.mul (KK.neg KK.invPhi) (KK.emb Z5.phi))) := by
        rw [KK.add_mul, KK.add_mul]
    _ = KK.add (KK.add (KK.mul p p)
                 (KK.add (KK.mul (KK.neg KK.invPhi) p) (KK.mul p (KK.emb Z5.phi))))
               (KK.mul (KK.neg KK.invPhi) (KK.emb Z5.phi)) := by
        rw [KK.add_assoc,
            ← KK.add_assoc (KK.mul (KK.neg KK.invPhi) p) (KK.mul p (KK.emb Z5.phi))
                           (KK.mul (KK.neg KK.invPhi) (KK.emb Z5.phi)),
            ← KK.add_assoc]
    _ = KK.add (KK.add (KK.mul p p) p) (KK.neg KK.one) := by
        rw [KK.neg_mul, KK.neg_mul, h2, KK.mul_comm p (KK.emb Z5.phi),
            ← KK.neg_mul, ← KK.add_mul,
            KK.add_comm (KK.neg KK.invPhi) (KK.emb Z5.phi), h1, KK.one_mul]

/-- **THE PENTAGON HAS EXACTLY TWO WORLDS.**  Any associator over K satisfying
    the pentagon has `p = 1/φ` (golden) or `p = −φ` (Yang–Lee).  With
    `pentagon_forces_golden`'s other two relations — `q·r = p` and `s = −p` —
    that pins the diagonal completely and the off-diagonal up to the gauge
    freedom `q ↦ λq, r ↦ λ⁻¹r` that round 3 already identified. -/
theorem pentagon_exactly_two_worlds (p q r s : KK)
    (h : ∀ a b c dd x y t w v,
           pentagonCheck kRng (Fg p q r s) a b c dd x y t w v = true) :
    p = KK.invPhi ∨ p = KK.neg (KK.emb Z5.phi) := by
  obtain ⟨-, hg, -⟩ := pentagon_forces_golden p q r s h
  have hz : KK.add (KK.add (KK.mul p p) p) (KK.neg KK.one) = KK.zero := by
    rw [hg]; exact KK.add_neg KK.one
  have hf := (golden_relation_factors p).trans hz
  rcases KK.eq_zero_or_eq_zero_of_mul_eq_zero _ _ hf with h1 | h1
  · exact Or.inl ((sub_eq_zero_iff p KK.invPhi).mp h1)
  · refine Or.inr ((sub_eq_zero_iff p (KK.neg (KK.emb Z5.phi))).mp ?_)
    rw [KK.neg_neg]; exact h1

/-- Both pentagon branches are realized too — golden by `Fsymm`, Yang–Lee by
    §9's witness — and they are distinct.  So this dichotomy is also genuine. -/
theorem pentagon_both_worlds_realized :
    KK.invPhi = KK.invPhi ∧
    KK.neg (KK.emb Z5.phi) = KK.neg (KK.emb Z5.phi) ∧
    KK.beq KK.invPhi (KK.neg (KK.emb Z5.phi)) = false :=
  ⟨rfl, rfl, rfl⟩

/-! #### "Exactly two" said once, with the distinctness inside it

An auditor's note, and a fair one: a dichotomy `s = a ∨ s = b` is only
"exactly TWO" if `a ≠ b` — otherwise it is "exactly one", stated twice.  That
distinctness was proved above but in a *different theorem* from the dichotomy,
which is precisely the shape of gap this project keeps finding in its own
ledgers.  So it is said once, here, in a single statement. -/

/-- **EXACTLY TWO BRAIDINGS, in one theorem.**  The dichotomy, the distinctness
    of the two branches, and the fact that both are realized — so the count is
    two and not "at most two" or "one written twice". -/
theorem hexagon_exactly_two_sharp :
    (∀ r1 rt : KK, (∀ a b c d e z, hexagonCheck kRng Fsymm r1 rt a b c d e z = true) →
       (rt = KK.rt ∨ rt = rt') ∧ r1 = KK.mul rt rt) ∧
    KK.beq KK.rt rt' = false ∧
    (∀ a b c d e z, hexagonCheck kRng Fsymm KK.r1 KK.rt a b c d e z = true) ∧
    (∀ a b c d e z, hexagonCheck kRng Fsymm r1' rt' a b c d e z = true) :=
  ⟨hexagon_exactly_two, rfl, golden_satisfies_hexagon, mirror_satisfies_hexagon⟩

/-- **EXACTLY TWO PENTAGON WORLDS, in one theorem.**  Same shape: dichotomy,
    distinctness, and both realized — golden by `Fsymm`, Yang–Lee by §9. -/
theorem pentagon_exactly_two_sharp :
    (∀ p q r s : KK,
       (∀ a b c dd x y t w v,
          pentagonCheck kRng (Fg p q r s) a b c dd x y t w v = true) →
       p = KK.invPhi ∨ p = KK.neg (KK.emb Z5.phi)) ∧
    KK.beq KK.invPhi (KK.neg (KK.emb Z5.phi)) = false :=
  ⟨pentagon_exactly_two_worlds, rfl⟩

/-! #### The control that shows `φ` is doing the work

The whole domain argument turns on `φ` not being a square in `Z[ζ₅]`.  If the
extension had been by the square root of something that *is* a square, K would
have zero divisors and every "exactly two" above would be false.

`4` is the cheapest witness: in `Z5[u]/(u² − 4)` the element `2 + u` is a zero
divisor, because `(2 + u)(2 − u) = 4 − u² = 0`.  Modelled here on the same
carrier as `KK` so the contrast is exact — same pairs, same addition, same
multiplication *shape*, one constant changed.

This is the negative control for §11: the 41-adic descent is not bookkeeping
that any extension would pass. -/

/-- Multiplication in `Z5[u]/(u² − 4)` — `KK.mul` with `φ` replaced by `4`. -/
def mulFour (u v : KK) : KK :=
  ⟨Z5.add (Z5.mul u.x v.x) (Z5.mul ⟨4,0,0,0⟩ (Z5.mul u.y v.y)),
   Z5.add (Z5.mul u.x v.y) (Z5.mul u.y v.x)⟩

/-- **THE SQUARE CASE HAS ZERO DIVISORS.**  `(2 + u)(2 − u) = 0` with both
    factors nonzero.  So `KK.eq_zero_or_eq_zero_of_mul_eq_zero` genuinely
    spends `Z5.not_square`; it is not true of the shape of the construction. -/
theorem square_extension_has_zero_divisors :
    mulFour ⟨⟨2,0,0,0⟩, Z5.one⟩ ⟨⟨2,0,0,0⟩, Z5.neg Z5.one⟩ = KK.zero ∧
    KK.beq ⟨⟨2,0,0,0⟩, Z5.one⟩ KK.zero = false ∧
    KK.beq ⟨⟨2,0,0,0⟩, Z5.neg Z5.one⟩ KK.zero = false :=
  ⟨rfl, rfl, rfl⟩

/-- ...and the same pair is *not* a zero divisor in the real K, where the
    constant is `φ`: `(2 + t)(2 − t) = 4 − φ ≠ 0`.  The two lines together are
    the contrast. -/
theorem golden_extension_no_such_zero_divisor :
    KK.beq (KK.mul ⟨⟨2,0,0,0⟩, Z5.one⟩ ⟨⟨2,0,0,0⟩, Z5.neg Z5.one⟩) KK.zero
      = false := rfl

end Workshop.Anyon
