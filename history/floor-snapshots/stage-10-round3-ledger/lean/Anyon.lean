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
/-- **`b = t/√φ` is fixed** — the off-diagonal entry of the associator. -/
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

end Workshop.Anyon
