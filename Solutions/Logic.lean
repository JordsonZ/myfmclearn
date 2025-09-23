section propositional

variable (P Q R : Prop)


------------------------------------------------
-- Double negation
------------------------------------------------

theorem doubleneg_intro :
  P → ¬ ¬ P  := by
  intro hp
  intro hnp
  have hn : False := hnp hp
  contradiction

theorem doubleneg_elim :
  ¬ ¬ P → P  := by
  intro hnp
  by_cases h : P
  exact h
  have hf : False := hnp h
  contradiction

theorem doubleneg_law :
  ¬ ¬ P ↔ P  := by
  constructor
  intro hnp
  by_cases h : P
  exact h
  have hf : False := hnp h
  contradiction
  intro hp
  intro np
  have hf : False := np hp
  contradiction

------------------------------------------------
-- Commutativity of ∨,∧
------------------------------------------------

theorem disj_comm :
  (P ∨ Q) → (Q ∨ P)  := by
  intro hpq
  rcases hpq with (hp | hq)
  right
  exact hp
  left
  exact hq

theorem conj_comm :
  (P ∧ Q) → (Q ∧ P)  := by
  intro hpq
  rcases hpq with ⟨hp , hq⟩
  constructor
  exact hq
  exact hp

------------------------------------------------
-- Interdefinability of →,∨
------------------------------------------------

theorem impl_as_disj_converse :
  (¬ P ∨ Q) → (P → Q)  := by
  intro hnpq
  intro hp
  rcases hnpq with (hnp | hq)
  have hf : False := hnp hp
  contradiction
  exact hq

theorem disj_as_impl :
  (P ∨ Q) → (¬ P → Q)  := by
  intro hpq
  intro hnp
  rcases hpq with (hp | hq)
  have hf : False := hnp hp
  contradiction
  exact hq


------------------------------------------------
-- Contrapositive
------------------------------------------------

theorem impl_as_contrapositive :
  (P → Q) → (¬ Q → ¬ P)  := by
  intro hpq
  intro hnq
  intro hp
  have hq : Q := hpq hp
  have hf : False := hnq hq
  contradiction

theorem impl_as_contrapositive_converse :
  (¬ Q → ¬ P) → (P → Q)  := by
  intro hnqnp
  intro hp
  by_cases h : Q
  exact h
  have hnp : ¬ P := hnqnp h
  have hf : False := hnp hp
  contradiction

theorem contrapositive_law :
  (P → Q) ↔ (¬ Q → ¬ P)  := by
  constructor
  intro hpq
  intro hnq
  intro hp
  have hq : Q := hpq hp
  have hf : False := hnq hq
  contradiction
  intro hnqnp
  intro hp
  by_cases h : Q
  exact h
  have hnp : ¬ P := hnqnp h
  have hf : False := hnp hp
  contradiction

------------------------------------------------
-- Irrefutability of LEM[P]
------------------------------------------------

theorem lem_irrefutable :
  ¬ ¬ (P ∨ ¬ P)  := by
  intro hnpunp
  apply hnpunp
  right
  intro hp
  apply hnpunp
  left
  exact hp

------------------------------------------------
-- Peirce's law
------------------------------------------------

theorem peirce_law_weak :
  ((P → Q) → P) → ¬ ¬ P  := by
  intro hpqp
  intro hnp
  by_cases h : P
  have hf : False := hnp h
  contradiction
  apply h
  apply hpqp
  intro hp
  have hf : False := h hp
  contradiction

------------------------------------------------
-- Linearity of →
------------------------------------------------

theorem impl_linear :
  (P → Q) ∨ (Q → P)  := by
  by_cases h : P
  right
  intro hq
  exact h
  left
  intro hp
  have hf : False := h hp
  contradiction

------------------------------------------------
-- Interdefinability of ∨,∧
------------------------------------------------

theorem disj_as_negconj :
  P ∨ Q → ¬ (¬ P ∧ ¬ Q)  := by
  intro hpuq
  intro hnpnq
  rcases hnpnq with ⟨hnp , hnq⟩
  rcases hpuq with (hp | hq)
  have hf : False := hnp hp
  contradiction
  have hf: False := hnq hq
  contradiction

theorem conj_as_negdisj :
  P ∧ Q → ¬ (¬ P ∨ ¬ Q)  := by
  intro hpq
  intro hnpnq
  rcases hpq with ⟨hp , hq⟩
  rcases hnpnq with (hnp | hnq)
  have hf : False := hnp hp
  contradiction
  have hf: False := hnq hq
  contradiction

------------------------------------------------
-- De Morgan laws for ∨,∧
------------------------------------------------

theorem demorgan_disj :
  ¬ (P ∨ Q) → (¬ P ∧ ¬ Q)  := by
  intro hnpq
  constructor
  intro hp
  apply hnpq
  left
  exact hp
  intro hq
  apply hnpq
  right
  exact hq

theorem demorgan_disj_converse :
  (¬ P ∧ ¬ Q) → ¬ (P ∨ Q)  := by
  intro hnpnq
  intro hpuq
  rcases hnpnq with ⟨hnp , hnq⟩
  rcases hpuq with (hp | hq)
  have hf : False := hnp hp
  contradiction
  have hf : False := hnq hq
  contradiction

theorem demorgan_conj :
  ¬ (P ∧ Q) → (¬ Q ∨ ¬ P)  := by
  intro hnpq
  by_cases h : Q
  right
  intro hp
  apply hnpq
  constructor
  exact hp
  exact h
  left
  intro hq
  have hf : False := h hq
  contradiction

theorem demorgan_conj_converse :
  (¬ Q ∨ ¬ P) → ¬ (P ∧ Q)  := by
  intro hnqnp
  intro hpq
  rcases hpq with ⟨hp , hq⟩
  rcases hnqnp with (hnq | hnp)
  have hf : False := hnq hq
  contradiction
  have hf : False := hnp hp
  contradiction


theorem demorgan_conj_law :
  ¬ (P ∧ Q) ↔ (¬ Q ∨ ¬ P)  := by
  constructor
  intro hnpq
  by_cases h : Q
  right
  intro hp
  apply hnpq
  constructor
  exact hp
  exact h
  left
  intro hq
  have hf : False := h hq
  contradiction
  intro hnqnp
  intro hpq
  rcases hpq with ⟨hp , hq⟩
  rcases hnqnp with (hnq | hnp)
  have hf : False := hnq hq
  contradiction
  have hf : False := hnp hp
  contradiction


theorem demorgan_disj_law :
  ¬ (P ∨ Q) ↔ (¬ P ∧ ¬ Q)  := by
  constructor
  intro hnpq
  constructor
  intro hp
  apply hnpq
  left
  exact hp
  intro hq
  apply hnpq
  right
  exact hq
  intro hnpnq
  intro hpuq
  rcases hnpnq with ⟨hnp , hnq⟩
  rcases hpuq with (hp | hq)
  have hf : False := hnp hp
  contradiction
  have hf : False := hnq hq
  contradiction

------------------------------------------------
-- Distributivity laws between ∨,∧
------------------------------------------------

theorem distr_conj_disj :
  P ∧ (Q ∨ R) → (P ∧ Q) ∨ (P ∧ R)  := by
  intro hpqr
  rcases hpqr with ⟨hp , hqr⟩
  rcases hqr with (hq | hr)
  left
  constructor
  exact hp
  exact hq
  right
  constructor
  exact hp
  exact hr

theorem distr_conj_disj_converse :
  (P ∧ Q) ∨ (P ∧ R) → P ∧ (Q ∨ R)  := by
  intro hpqpr
  constructor
  rcases hpqpr with (hpq | hpr)
  rcases hpq with ⟨hp , hq⟩
  exact hp
  rcases hpr with ⟨hp , hr⟩
  exact hp
  rcases hpqpr with (hpq | hpr)
  left
  rcases hpq with ⟨hp , hq⟩
  exact hq
  right
  rcases hpr with ⟨hp , hr⟩
  exact hr

theorem distr_disj_conj :
  P ∨ (Q ∧ R) → (P ∨ Q) ∧ (P ∨ R)  := by
  intro hpqr
  rcases hpqr with (hp | hqr)
  constructor
  left
  exact hp
  left
  exact hp
  rcases hqr with ⟨hq , hr⟩
  constructor
  right
  exact hq
  right
  exact hr

theorem distr_disj_conj_converse :
  (P ∨ Q) ∧ (P ∨ R) → P ∨ (Q ∧ R)  := by
  intro hpqpr
  rcases hpqpr with ⟨hpq , hpr⟩
  rcases hpq with (hp | hq)
  left
  exact hp
  rcases hpr with (hp | hr)
  left
  exact hp
  right
  constructor
  exact hq
  exact hr

------------------------------------------------
-- Currying
------------------------------------------------

theorem curry_prop :
  ((P ∧ Q) → R) → (P → (Q → R))  := by
  intro hpqr
  intro hp
  intro hq
  apply hpqr
  constructor
  exact hp
  exact hq


theorem uncurry_prop :
  (P → (Q → R)) → ((P ∧ Q) → R)  := by
  intro hpqr
  intro hpq
  rcases hpq with ⟨hp , hq⟩
  have hqr : Q → R := hpqr hp
  have hr : R := hqr hq
  exact hr


------------------------------------------------
-- Reflexivity of →
------------------------------------------------

theorem impl_refl :
  P → P  := by
  intro hp
  exact hp


------------------------------------------------
-- Weakening and contraction
------------------------------------------------

theorem weaken_disj_right :
  P → (P ∨ Q)  := by
  intro hp
  left
  exact hp

theorem weaken_disj_left :
  Q → (P ∨ Q)  := by
  intro hq
  right
  exact hq

theorem weaken_conj_right :
  (P ∧ Q) → P  := by
  intro hpq
  rcases  hpq with ⟨hp , hq⟩
  exact hp

theorem weaken_conj_left :
  (P ∧ Q) → Q  := by
  intro hpq
  rcases hpq with ⟨hp , hq⟩
  exact hq


------------------------------------------------
-- Idempotence of ∨,∧
------------------------------------------------

theorem disj_idem :
  (P ∨ P) ↔ P  := by
  constructor
  intro hpp
  rcases hpp with (hp | hp)
  exact hp
  exact hp
  intro hp
  left
  exact hp

theorem conj_idem :
  (P ∧ P) ↔ P := by
  constructor
  intro hpp
  rcases hpp with ⟨hp , hp⟩
  exact hp
  intro hp
  constructor
  exact hp
  exact hp


------------------------------------------------
-- Bottom, Top
------------------------------------------------

theorem false_bottom :
  False → P := by
  intro hf
  contradiction

theorem true_top :
  P → True  := by
  intro hp
  trivial


end propositional

----------------------------------------------------------------

section predicate

variable (U : Type)
variable (P Q : U → Type)


------------------------------------------------
-- De Morgan laws for ∃,∀
------------------------------------------------

theorem demorgan_exists :
  ¬ (∃ x, P x) → (∀ x, ¬ P x)  := by
  sorry

theorem demorgan_exists_converse :
  (∀ x, ¬ P x) → ¬ (∃ x, P x)  := by
  sorry

theorem demorgan_forall :
  ¬ (∀ x, P x) → (∃ x, ¬ P x)  := by
  sorry

theorem demorgan_forall_converse :
  (∃ x, ¬ P x) → ¬ (∀ x, P x)  := by
  sorry

theorem demorgan_forall_law :
  ¬ (∀ x, P x) ↔ (∃ x, ¬ P x)  := by
  sorry

theorem demorgan_exists_law :
  ¬ (∃ x, P x) ↔ (∀ x, ¬ P x)  := by
  sorry


------------------------------------------------
-- Interdefinability of ∃,∀
------------------------------------------------

theorem exists_as_neg_forall :
  (∃ x, P x) → ¬ (∀ x, ¬ P x)  := by
  sorry

theorem forall_as_neg_exists :
  (∀ x, P x) → ¬ (∃ x, ¬ P x)  := by
  sorry

theorem forall_as_neg_exists_converse :
  ¬ (∃ x, ¬ P x) → (∀ x, P x)  := by
  sorry

theorem exists_as_neg_forall_converse :
  ¬ (∀ x, ¬ P x) → (∃ x, P x)  := by
  sorry

theorem forall_as_neg_exists_law :
  (∀ x, P x) ↔ ¬ (∃ x, ¬ P x)  := by
  sorry

theorem exists_as_neg_forall_law :
  (∃ x, P x) ↔ ¬ (∀ x, ¬ P x)  := by
  sorry


------------------------------------------------
--  Distributivity between quantifiers
------------------------------------------------

theorem exists_conj_as_conj_exists :
  (∃ x, P x ∧ Q x) → (∃ x, P x) ∧ (∃ x, Q x)  := by
  sorry

theorem exists_disj_as_disj_exists :
  (∃ x, P x ∨ Q x) → (∃ x, P x) ∨ (∃ x, Q x)  := by
  sorry

theorem exists_disj_as_disj_exists_converse :
  (∃ x, P x) ∨ (∃ x, Q x) → (∃ x, P x ∨ Q x)  := by
  sorry

theorem forall_conj_as_conj_forall :
  (∀ x, P x ∧ Q x) → (∀ x, P x) ∧ (∀ x, Q x)  := by
  sorry

theorem forall_conj_as_conj_forall_converse :
  (∀ x, P x) ∧ (∀ x, Q x) → (∀ x, P x ∧ Q x)  := by
  sorry

theorem forall_disj_as_disj_forall_converse :
  (∀ x, P x) ∨ (∀ x, Q x) → (∀ x, P x ∨ Q x)  := by
  sorry


end predicate

------------------------------------------------

section bonus

------------------------------------------------
--  Drinker's paradox
------------------------------------------------

variable (D : U → Prop)

-- There is a person p such that:
-- if p drinks, then everybody drinks
-- p: «person»
-- D x: «x drinks»
theorem drinker :
  ∃ p, (D p → ∀ x, D x)  := by
  sorry

------------------------------------------------
--  Russell's paradox
------------------------------------------------

variable (S : U → U → Prop)

-- It is impossible to have a barber b such that
-- b shaves exactly those people who do not shave themselves
-- b: «barber»
-- S x y: «x shaves y»
theorem russell :
  ¬ ∃ b, ∀ x, (S b x ↔ ¬ S x x)  := by
  sorry


end bonus


/- NOT THEOREMS --------------------------------

theorem forall_disj_as_disj_forall :
  (∀ x, P x ∨ Q x) → (∀ x, P x) ∨ (∀ x, Q x)  := by
  sorry

theorem exists_conj_as_conj_exists_converse :
  (∃ x, P x) ∧ (∃ x, Q x) → (∃ x, P x ∧ Q x)  := by
  sorry

---------------------------------------------- -/
