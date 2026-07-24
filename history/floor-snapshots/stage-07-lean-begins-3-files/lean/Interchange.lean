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

end Workshop.EckmannHilton
