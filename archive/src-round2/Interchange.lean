/-
  THE WORKSHOP → LEAN 4.  Round 1, Tier 1.

  Bench formalized:  `grammar_interchange.py`  (seventh weld)
  Claim made theorem: EckmannHilton.

  Two binary operations on one type, each with a shared unit, tied by the
  interchange law, are (i) the same operation, (ii) commutative, (iii)
  associative.  This is why scalars commute: End(I) = C is one home carrying
  both composites with one unit, so there is no room left to be
  non-commutative.

  Why channels escape, stated as the bench states it: `grammar_interchange.py`
  lines 25-26 — "Channels escape the collapse only because 'then' and 'while'
  live on different types."  That is the *shared home* hypothesis failing, not
  the unit: ⊗ is not a binary operation on a single set (it takes
  End(H) × End(K) → End(H ⊗ K)), so channels are not two operations on one
  type at all and the theorem below simply does not apply to them.  No
  contradiction with the exhibited ‖[A,B]‖ = 0.49 — that pair never satisfied
  the hypotheses.  (An earlier draft of this header blamed the unit.  Wrong
  diagnosis; the bench is right.)

  Self-contained: NO imports.  Checkable by a bare `lean` with no lake, no
  mathlib, no Std.  Uses only `calc`, `rw`, `exact` — all core tactics.

  Status: PROVED, no `sorry`.
-/

universe u

namespace Workshop.EckmannHilton

/-! ## 1. The units are not two

Before assuming a *shared* unit, note that interchange forces one.  This is
strictly stronger than what the workshop asked for, and it is where the
"shared home" in the bench's phrasing actually comes from: it is not an
assumption, it is a consequence. -/

/-- If `m` has unit `em` and `n` has unit `en` and the two interchange, the
    two units coincide.  (Nothing else is assumed: no associativity, no
    commutativity, no relation between `m` and `n` beyond interchange.) -/
theorem units_agree {A : Type u} (m n : A → A → A) (em en : A)
    (hm  : ∀ a, m em a = a) (hm' : ∀ a, m a em = a)
    (hn  : ∀ a, n en a = a) (hn' : ∀ a, n a en = a)
    (I   : ∀ a b c d, n (m a b) (m c d) = m (n a c) (n b d)) :
    en = em :=
  calc en = n en en               := (hn en).symm
    _     = n (m em en) (m en em) := by rw [hm en, hm' en]
    _     = m (n em en) (n en em) := I em en en em
    _     = m em em               := by rw [hn' em, hn em]
    _     = em                    := hm em

/-! ## 2. The Eckmann–Hilton argument proper

Packaged as a structure so the three conclusions can be stated and reused
without re-threading seven hypotheses at every call site. -/

/-- Two binary operations on one type, sharing a unit, satisfying interchange. -/
structure Interchanging (A : Type u) where
  /-- the first operation (the workshop's "vertical" composite) -/
  m : A → A → A
  /-- the second operation (the workshop's "horizontal" composite) -/
  n : A → A → A
  /-- the shared unit -/
  e : A
  m_id_left   : ∀ a, m e a = a
  m_id_right  : ∀ a, m a e = a
  n_id_left   : ∀ a, n e a = a
  n_id_right  : ∀ a, n a e = a
  /-- `(a·b) ∘ (c·d) = (a∘c) · (b∘d)` — "meanwhile" is well defined. -/
  interchange : ∀ a b c d, n (m a b) (m c d) = m (n a c) (n b d)

namespace Interchanging

variable {A : Type u} (S : Interchanging A)

/-- (i) THE TWO OPERATIONS ARE ONE. -/
theorem ops_agree (a b : A) : S.n a b = S.m a b := by
  have h := S.interchange a S.e S.e b
  rw [S.m_id_right a, S.m_id_left b, S.n_id_right a, S.n_id_left b] at h
  exact h

/-- (ii) THE OPERATION IS COMMUTATIVE.  This is the sentence the workshop
    wanted: scalars are *forced* commutative, they do not choose to be. -/
theorem comm (a b : A) : S.m a b = S.m b a := by
  have h := S.interchange S.e a b S.e
  rw [S.m_id_left a, S.m_id_right b, S.n_id_left b, S.n_id_right a] at h
  exact (S.ops_agree a b).symm.trans h

/-- (iii) THE OPERATION IS ASSOCIATIVE. -/
theorem assoc (a b c : A) : S.m (S.m a b) c = S.m a (S.m b c) := by
  have h := S.interchange a S.e b c
  rw [S.m_id_right a, S.n_id_left c] at h
  have e1 : S.n a (S.m b c) = S.m a (S.m b c) := S.ops_agree a (S.m b c)
  have e2 : S.n a b = S.m a b := S.ops_agree a b
  rw [e1, e2] at h
  exact h.symm

end Interchanging

/-! ## 3. The theorem as the builder stated it

Same content, hypotheses loose rather than bundled — this is the literal
reading of the charge: "two binary operations on one type, each with a
(shared) unit, satisfying interchange, are equal, commutative, and
associative." -/

theorem eckmann_hilton {A : Type u} (m n : A → A → A) (e : A)
    (hm  : ∀ a, m e a = a) (hm' : ∀ a, m a e = a)
    (hn  : ∀ a, n e a = a) (hn' : ∀ a, n a e = a)
    (I   : ∀ a b c d, n (m a b) (m c d) = m (n a c) (n b d)) :
    (∀ a b, n a b = m a b) ∧
    (∀ a b, m a b = m b a) ∧
    (∀ a b c, m (m a b) c = m a (m b c)) :=
  let S : Interchanging A :=
    { m := m, n := n, e := e
      m_id_left := hm, m_id_right := hm'
      n_id_left := hn, n_id_right := hn'
      interchange := I }
  ⟨S.ops_agree, S.comm, S.assoc⟩

/-- **THE SHARED UNIT IS NOT NEEDED AS A HYPOTHESIS.**  Same three conclusions,
    but the two operations start with *separate* units `em` and `en`;
    `units_agree` collapses them first.  This is what makes that lemma
    load-bearing rather than decorative — the parenthesis in the charge's
    "each with a (shared) unit" can be discharged, not assumed. -/
theorem eckmann_hilton_two_units {A : Type u} (m n : A → A → A) (em en : A)
    (hm  : ∀ a, m em a = a) (hm' : ∀ a, m a em = a)
    (hn  : ∀ a, n en a = a) (hn' : ∀ a, n a en = a)
    (I   : ∀ a b c d, n (m a b) (m c d) = m (n a c) (n b d)) :
    (∀ a b, n a b = m a b) ∧
    (∀ a b, m a b = m b a) ∧
    (∀ a b c, m (m a b) c = m a (m b c)) := by
  have h : en = em := units_agree m n em en hm hm' hn hn' I
  subst h
  exact eckmann_hilton m n en hm hm' hn hn' I

/-! ## 4. The consequence the bench cared about

`grammar_interchange.py` exhibits channels with ‖[A,B]‖ = 0.49 — an explicit
NON-commuting pair — and scalars that are forced to commute.  The two facts
are consistent precisely because channels do not satisfy the hypotheses
above.  Below is the scalar corollary, stated in the form the bench used it:
anything living at the shared unit's level commutes. -/

/-- Scalars commute. -/
theorem scalars_commute {A : Type u} (S : Interchanging A) (a b : A) :
    S.m a b = S.m b a := S.comm a b

/-- ...and the "two composites" of a circuit diagram mean one thing. -/
theorem meanwhile_well_defined {A : Type u} (S : Interchanging A) (a b : A) :
    S.n a b = S.m a b := S.ops_agree a b

/-! # ITEM E — spacelike commutation from the composition law alone

`grammar_interchange.py`, claim (2): "Alice's and Bob's local operations
commute exactly — (A ⊗ id) ∘ (id ⊗ B) in either order — so no temporal
ordering between them is needed."  The bench checks this numerically on random
channels to 1e-12.  Below it is a theorem, and the point of the section is
*which hypotheses it needs*.

It needs a unit for the SEQUENTIAL composition only.  It does not need a unit
for the parallel composition, does not need `par` commutative, does not need
either operation associative.  That asymmetry is the whole content: §1–§4
above show that a unit shared by BOTH operations collapses them into one
commutative operation (Eckmann–Hilton), so if spacelike commutation required
the shared unit it would be a fact about a degenerate situation and would say
nothing about channels.  It does not require it.  §6 proves the gap is real by
exhibiting a model of the weaker hypotheses that is not Eckmann–Hilton. -/

/-! ## 5. The structure and the theorem

`PreInterchanging` is `Interchanging` with the two `par` unit laws deleted.
Nothing else changes.  Reading the field list against `Interchanging`'s is the
fastest way to see exactly what is being given up. -/

/-- Two binary operations on one type: `seq` ("then"), `par` ("while"), tied by
    the interchange law, with a two-sided unit for `seq` ONLY.

    Deliberately absent: any unit law for `par`.  There is no `par_id_left` and
    no `par_id_right`, and §6 shows neither is derivable. -/
structure PreInterchanging (A : Type u) where
  /-- sequential composition — "then" -/
  seq : A → A → A
  /-- parallel composition — "while" -/
  par : A → A → A
  /-- the unit, for `seq` alone -/
  id : A
  seq_id_left  : ∀ a, seq id a = a
  seq_id_right : ∀ a, seq a id = a
  /-- `(a ‖ b) ; (c ‖ d) = (a ; c) ‖ (b ; d)` -/
  interchange : ∀ a b c d, seq (par a b) (par c d) = par (seq a c) (seq b d)

namespace PreInterchanging

variable {A : Type u} (S : PreInterchanging A)

/-- Alice-then-Bob is `a ‖ b`.  Interchange at `(a, id, id, b)` turns the
    sequential composite into a parallel one, and the two `seq` unit laws
    clear the resulting `seq a id` and `seq id b`. -/
theorem alice_then_bob (a b : A) :
    S.seq (S.par a S.id) (S.par S.id b) = S.par a b := by
  have h := S.interchange a S.id S.id b
  rw [S.seq_id_right a, S.seq_id_left b] at h
  exact h

/-- Bob-then-Alice is also `a ‖ b`.  Same three rewrites, interchange taken at
    `(id, b, a, id)` instead.  Note the right-hand side is `par a b`, not
    `par b a` — no commutativity of `par` is used or obtained. -/
theorem bob_then_alice (a b : A) :
    S.seq (S.par S.id b) (S.par a S.id) = S.par a b := by
  have h := S.interchange S.id b a S.id
  rw [S.seq_id_left a, S.seq_id_right b] at h
  exact h

/-- **SPACELIKE COMMUTATION.**  Alice's local operation and Bob's local
    operation commute as sequential composites, because each order is a name
    for the single parallel composite `a ‖ b`.  No ordering between them is
    determined by the composition law, which is what "spacelike" means here. -/
theorem spacelike (a b : A) :
    S.seq (S.par a S.id) (S.par S.id b) = S.seq (S.par S.id b) (S.par a S.id) :=
  (S.alice_then_bob a b).trans (S.bob_then_alice a b).symm

end PreInterchanging

/-! ## 6. The separation — the hypotheses really are weaker

Without this section §5 could be a theorem about the empty class of models, or
about a class in which `par` secretly has a unit and Eckmann–Hilton applies
after all.  The model below settles both: it satisfies `PreInterchanging`, its
`par` is not commutative, and its `par` has no left unit.

The model: `A = Bool`, `seq = xor` (unit `false`), `par a b = a`.  Interchange
holds by computation — both sides reduce to `xor a c` — and it holds for the
uninteresting reason that `par` ignores its second argument, which is exactly
why it is a legitimate witness that the axioms permit degenerate `par`. -/

/-- `seq` of the separating model: xor, with unit `false`. -/
def sepSeq : Bool → Bool → Bool
  | true,  b => !b
  | false, b => b

/-- `par` of the separating model: left projection.  It has no left unit, and
    it is the reason the model escapes Eckmann–Hilton. -/
def sepPar (a : Bool) (_ : Bool) : Bool := a

/-- **THE MODEL EXISTS.**  `PreInterchanging` is inhabited, so §5 is not
    vacuous.  `interchange` is `rfl`: both sides reduce to `sepSeq a c`. -/
def SepModel : PreInterchanging Bool where
  seq := sepSeq
  par := sepPar
  id  := false
  seq_id_left  := fun _ => rfl
  seq_id_right := fun a => by cases a <;> rfl
  interchange  := fun _ _ _ _ => rfl

/-- **`par` IS NOT COMMUTATIVE** in the model — a concrete pair.
    `true ‖ false = true` while `false ‖ true = false`. -/
theorem sepPar_not_comm : SepModel.par true false ≠ SepModel.par false true := by
  decide

/-- **`par` HAS NO LEFT UNIT** in the model: for every candidate `e` there is an
    `a` with `e ‖ a ≠ a`.  Witness `a = !e`, since `e ‖ a = e`.

    This is the load-bearing half of the separation.  Eckmann–Hilton needs a
    unit for the second operation; here no element is one, so `SepModel` is not
    an `Interchanging` in disguise and its `par`'s non-commutativity is not a
    contradiction with §2. -/
theorem sepPar_no_left_unit : ∀ e : Bool, ∃ a : Bool, SepModel.par e a ≠ a :=
  fun e => ⟨!e, by cases e <;> decide⟩

/-- Consequently no element is a two-sided unit for `par` either. -/
theorem sepPar_no_unit :
    ∀ e : Bool, ¬ ((∀ a, SepModel.par e a = a) ∧ (∀ a, SepModel.par a e = a)) := by
  intro e h
  have hne := sepPar_no_left_unit e
  exact Exists.elim hne (fun a ha => ha (h.1 a))

/-- The spacelike equation is not an identity between two undefined things: in
    this model both sides of `spacelike true false` compute to `true`, and the
    common value `par a b` is `a`. -/
theorem sepModel_spacelike_computes :
    SepModel.seq (SepModel.par true SepModel.id) (SepModel.par SepModel.id false)
      = true := rfl

/-! ### The mirror model, closing the other side

`sepPar` has no left unit, but every element is a right unit for it
(`sepPar a e = a` always).  Stating "par has no unit" without qualification
would therefore overclaim from `SepModel` alone.  The mirror model — same
`seq`, `par` = right projection — has no right unit.  Taken together, neither
a left-unit law nor a right-unit law for `par` is derivable from
`PreInterchanging`, which is the precise form of "there is deliberately no unit
law for par". -/

/-- `par` of the mirror model: right projection. -/
def mirPar (_ : Bool) (a : Bool) : Bool := a

/-- The mirror model. -/
def MirModel : PreInterchanging Bool where
  seq := sepSeq
  par := mirPar
  id  := false
  seq_id_left  := fun _ => rfl
  seq_id_right := fun a => by cases a <;> rfl
  interchange  := fun _ _ _ _ => rfl

/-- **`par` HAS NO RIGHT UNIT** in the mirror model. -/
theorem mirPar_no_right_unit : ∀ e : Bool, ∃ a : Bool, MirModel.par a e ≠ a :=
  fun e => ⟨!e, by cases e <;> decide⟩

/-! ## 7. Negative controls

Norm: a check that cannot fail is not a check.  Three things are shown to be
capable of failing. -/

/-- **THE INTERCHANGE LAW CAN FAIL.**  `seq = xor`, `par = and` is a pair of
    operations on `Bool` for which interchange is false at a concrete point, so
    `PreInterchanging.interchange` is a real restriction and not something every
    pair of operations satisfies. -/
theorem interchange_can_fail :
    ∃ a b c d : Bool, sepSeq (a && b) (c && d) ≠ (sepSeq a c && sepSeq b d) :=
  ⟨false, true, true, false, by decide⟩

/-- Three elements, for the counterexample below.  `u` is the `seq` unit. -/
inductive Tri where
  | u | x | y

/-- A `seq` with two-sided unit `u` that is NOT commutative: off the unit it is
    left projection, so `x ; y = x` and `y ; x = y`.

    The three first-argument constructors are matched explicitly rather than
    written `| a, _ => a`.  The variable pattern compiles to a match splitter
    whose equation lemmas drag in `propext`; the explicit form reduces by iota
    and keeps this section's theorems free of every axiom. -/
def triSeq : Tri → Tri → Tri
  | .u, b => b
  | .x, _ => .x
  | .y, _ => .y

/-- `triSeq` has `u` as a two-sided unit. -/
theorem triSeq_unit_left (a : Tri) : triSeq .u a = a := rfl

/-- The right unit law needs the case split, since `triSeq` matches on its
    first argument. -/
theorem triSeq_unit_right (a : Tri) : triSeq a .u = a := by cases a <;> rfl

/-- **THE INTERCHANGE HYPOTHESIS IS DOING THE WORK.**  Delete `interchange`
    from `PreInterchanging` and keep everything else — both `seq` unit laws, a
    `par`, the same signature — and the spacelike conclusion fails.  Witness:
    `seq = par = triSeq`, unit `u`, at `a = x`, `b = y`, where the two orders
    give `x` and `y`.

    So `spacelike` is not a consequence of the unit laws alone; it is exactly
    what interchange buys, which is the bench's claim (2) in one sentence. -/
theorem spacelike_needs_interchange :
    ∃ (seq par : Tri → Tri → Tri) (e : Tri),
      (∀ a, seq e a = a) ∧ (∀ a, seq a e = a) ∧
      ∃ a b, seq (par a e) (par e b) ≠ seq (par e b) (par a e) := by
  refine ⟨triSeq, triSeq, .u, triSeq_unit_left, triSeq_unit_right, .x, .y, ?_⟩
  intro h
  have h2 : Tri.x = Tri.y := h
  exact Tri.noConfusion h2

/-! ## 8. The round-1 structure is inhabited

§2's theorems are universally quantified over `Interchanging A`.  If that
structure had no inhabitants they would be true and empty.  It has one: xor
taken twice, with unit `false`.  (Consistent with §2 as it must be — the two
operations are literally equal, and xor is commutative and associative.) -/

/-- **`Interchanging` IS INHABITED.**  `m = n = xor`, shared unit `false`.
    Interchange is the rearrangement `(a⊕b)⊕(c⊕d) = (a⊕c)⊕(b⊕d)`, proved by
    exhausting the 16 bit patterns in the kernel. -/
def XorModel : Interchanging Bool where
  m := sepSeq
  n := sepSeq
  e := false
  m_id_left  := fun _ => rfl
  m_id_right := fun a => by cases a <;> rfl
  n_id_left  := fun _ => rfl
  n_id_right := fun a => by cases a <;> rfl
  interchange := fun a b c d => by cases a <;> cases b <;> cases c <;> cases d <;> rfl

/-- The inhabitant is not the one-element degenerate case: `XorModel`'s
    operation takes both values, so §2's conclusions are asserted about a
    structure with something in it. -/
theorem xorModel_nontrivial :
    XorModel.m true false = true ∧ XorModel.m true true = false := ⟨rfl, rfl⟩

/-- Every `Interchanging` is in particular a `PreInterchanging` — the `par`
    unit laws are forgotten, nothing else changes.  This is the formal sense in
    which §5's hypotheses are weaker than §2's: the map goes this way and, by
    `sepPar_no_left_unit`, not back. -/
def Interchanging.toPre {A : Type u} (S : Interchanging A) : PreInterchanging A where
  seq := S.n
  par := S.m
  id  := S.e
  seq_id_left  := S.n_id_left
  seq_id_right := S.n_id_right
  interchange  := S.interchange

end Workshop.EckmannHilton
