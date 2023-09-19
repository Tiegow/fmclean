
section propositional

variables P Q R : Prop


------------------------------------------------
-- Proposições de dupla negaço:
------------------------------------------------

theorem doubleneg_intro :
  P → ¬¬P  :=
begin
  intro p,
  intro hp,
  contradiction,
end

theorem doubleneg_elim :
  ¬¬P → P  :=
begin
  intro hp,
  by_cases p:P,
  exact p,
  exfalso,
  contradiction,
end

theorem doubleneg_law :
  ¬¬P ↔ P  :=
begin
  split,
  exact doubleneg_elim P,
  exact doubleneg_intro P,
end

------------------------------------------------
-- Comutatividade dos ∨,∧:
------------------------------------------------

theorem disj_comm :
  (P ∨ Q) → (Q ∨ P)  :=
begin
  intro Hpq,
  cases Hpq with P Q,
  right,
  exact P,
  left,
  exact Q,
end

theorem conj_comm :
  (P ∧ Q) → (Q ∧ P)  :=
begin
  intro Hpq,
  cases Hpq with P Q,
  split,
  exact Q,
  exact P,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos →,∨:
------------------------------------------------

theorem impl_as_disj_converse :
  (¬P ∨ Q) → (P → Q)  :=
begin
  intro Hpq,
  intro Hp,
  cases Hpq with P Q,
  exfalso,
  contradiction,
  exact Q,
end

theorem disj_as_impl :
  (P ∨ Q) → (¬P → Q)  :=
begin
  intro Hpq,
  intro Hp,
  cases Hpq with P Q,
  exfalso,
  contradiction,
  exact Q,
end


------------------------------------------------
-- Proposições de contraposição:
------------------------------------------------

theorem impl_as_contrapositive :
  (P → Q) → (¬Q → ¬P)  :=
begin
  intro Hpq,
  intro Hq,
  intro P,
  have Q : Q := Hpq P,
  contradiction,
end

theorem impl_as_contrapositive_converse :
  (¬Q → ¬P) → (P → Q)  :=
begin
  intro Hqp,
  intro P,
  by_cases Q : Q,
  exact Q,
  exfalso,
  apply Hqp Q,
  exact P,
end

theorem contrapositive_law :
  (P → Q) ↔ (¬Q → ¬P)  :=
begin
  split,
  intro Hpq,
  intro Hq,
  intro P,
  have Q : Q := Hpq P,
  contradiction,
  -- Ou simpesmente (exact impl_as_contrapositive P Q,)
  intro Hqp,
  intro P,
  by_cases Q : Q,
  exact Q,
  exfalso,
  apply Hqp Q,
  exact P,
  -- Ou simpesmente (exact impl_as_contrapositive_converse P Q,)
end


------------------------------------------------
-- A irrefutabilidade do LEM:
------------------------------------------------

theorem lem_irrefutable :
  ¬¬(P∨¬P)  :=
begin
  intro h,
  apply h,
  right,
  intro p,
  apply h,
  left,
  exact p,
end


------------------------------------------------
-- A lei de Peirce
------------------------------------------------

theorem peirce_law_weak :
  ((P → Q) → P) → ¬¬P  :=
begin
  intro h,
  intro np,
  apply np,
  apply h,
  intro p,
  exfalso,
  contradiction,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∨,∧:
------------------------------------------------

theorem disj_as_negconj :
  P∨Q → ¬(¬P∧¬Q)  :=
begin
  intro Hpq,
  intro Npq,
  cases Npq with np nq,
  cases Hpq with p q,
  contradiction,
  contradiction,
end

theorem conj_as_negdisj :
  P∧Q → ¬(¬P∨¬Q)  :=
begin
  intro Hpq,
  cases Hpq with p q,
  intro Npq,
  cases Npq,
  contradiction,
  contradiction,
end


------------------------------------------------
-- As leis de De Morgan para ∨,∧:
------------------------------------------------

theorem demorgan_disj :
  ¬(P∨Q) → (¬P ∧ ¬Q)  :=
begin
  intro Hpq,
  split,
  intro P,
  apply Hpq,
  left,
  exact P,
  intro Q,
  apply Hpq,
  right,
  exact Q,
end

theorem demorgan_disj_converse :
  (¬P ∧ ¬Q) → ¬(P∨Q)  :=
begin
  intro H1,
  intro H2,
  cases H1 with nP nQ,
  cases H2,
  contradiction,
  contradiction,
end

theorem demorgan_conj :
  ¬(P∧Q) → (¬Q ∨ ¬P)  :=
begin
  intro Hpq,
  by_cases p:P,
  by_cases q:Q,
  right,
  exfalso,
  apply Hpq,
  split,
  exact p,
  exact q,
  left,
  exact q,
  right, exact p,
end

theorem demorgan_conj_converse :
  (¬Q ∨ ¬P) → ¬(P∧Q)  :=
begin
  intro H1,
  intro H2,
  cases H2 with p q,
  cases H1,
  contradiction,
  contradiction,
end

theorem demorgan_conj_law :
  ¬(P∧Q) ↔ (¬Q ∨ ¬P)  :=
begin
  split,
  exact demorgan_conj P Q,
  exact demorgan_conj_converse P Q,
end

theorem demorgan_disj_law :
  ¬(P∨Q) ↔ (¬P ∧ ¬Q)  :=
begin
  split,
  exact demorgan_disj P Q,
  exact demorgan_disj_converse P Q,
end

------------------------------------------------
-- Proposições de distributividade dos ∨,∧:
------------------------------------------------

theorem distr_conj_disj :
  P∧(Q∨R) → (P∧Q)∨(P∧R)  :=
begin
  intro H1,
  cases H1 with p Hqr,
  cases Hqr,
  left,
  split,
  exact p,
  exact Hqr,
  right,
  split,
  exact p,
  exact Hqr,
end

theorem distr_conj_disj_converse :
  (P∧Q)∨(P∧R) → P∧(Q∨R)  :=
begin
  intro H1,
  cases H1,
  cases H1 with p q,
  split,
  exact p,
  left,
  exact q,
  cases H1 with p r,
  split,
  exact p,
  right, exact r,
end

theorem distr_disj_conj :
  P∨(Q∧R) → (P∨Q)∧(P∨R)  :=
begin
  intro H1,
  split,
  cases H1,
  left, exact H1,
  cases H1 with q r,
  right, exact q,
  cases H1,
  left, exact H1,
  cases H1 with q r,
  right, exact r,
end

theorem distr_disj_conj_converse :
  (P∨Q)∧(P∨R) → P∨(Q∧R)  :=
begin
  intro H1,
  cases H1 with Hpq Hpr,
  cases Hpq,
  left,
  exact Hpq,
  cases Hpr,
  left,
  exact Hpr,
  right,
  split,
  exact Hpq, exact Hpr,
end


------------------------------------------------
-- Currificação
------------------------------------------------

theorem curry_prop :
  ((P∧Q)→R) → (P→(Q→R))  :=
begin
  intro H1,
  intro p,
  intro q,
  apply H1,
  split,
  exact p, exact q,
end

theorem uncurry_prop :
  (P→(Q→R)) → ((P∧Q)→R)  :=
begin
  intros H1 H2,
  cases H2 with p q,
  have r:=H1 p q,
  exact r, 
end


------------------------------------------------
-- Reflexividade da →:
------------------------------------------------

theorem impl_refl :
  P → P  :=
begin
  intro p, exact p,
end

------------------------------------------------
-- Weakening and contraction:
------------------------------------------------

theorem weaken_disj_right :
  P → (P∨Q)  :=
begin
  intro p,
  left,
  exact p,
end

theorem weaken_disj_left :
  Q → (P∨Q)  :=
begin
  intro q,
  right,
  exact q,
end

theorem weaken_conj_right :
  (P∧Q) → P  :=
begin
  intro H1,
  cases H1 with p q,
  exact p,
end

theorem weaken_conj_left :
  (P∧Q) → Q  :=
begin
  intro H1,
  cases H1 with p q,
  exact q,
end

theorem conj_idempot :
  (P∧P) ↔ P :=
begin
  split,
  intro H1,
  cases H1 with p p',
  exact p,
  intro p,
  split,
  repeat{exact p},
end

theorem disj_idempot :
  (P∨P) ↔ P  :=
begin
  split,
  intro Hp,
  cases Hp,
  repeat{exact Hp},
  intro p,
  left,
  exact p,
end

end propositional


----------------------------------------------------------------


section predicate

variable U : Type
variables P Q : U -> Prop


------------------------------------------------
-- As leis de De Morgan para ∃,∀:
------------------------------------------------

theorem demorgan_exists :
  ¬(∃x, P x) → (∀x, ¬P x)  :=
begin
  intro H1,
  intro y,
  intro H2,
  apply H1,
  existsi y,
  exact H2,
end

theorem demorgan_exists_converse :
  (∀x, ¬P x) → ¬(∃x, P x)  :=
begin
  intro H1,
  intro H2,
  cases H2 with x Px,
  have Px' := H1 x,
  contradiction,
end

theorem demorgan_forall :
  ¬(∀x, P x) → (∃x, ¬P x)  :=
begin
  intro H1,
  by_contra H2,
  apply H1,
  intro y,
  by_contra H3,
  apply H2,
  existsi y,
  exact H3,
end

theorem demorgan_forall_converse :
  (∃x, ¬P x) → ¬(∀x, P x)  :=
begin
  intro H1,
  intro H2,
  cases H1 with y Hy,
  have H3 := H2 y,
  contradiction,
end

theorem demorgan_forall_law :
  ¬(∀x, P x) ↔ (∃x, ¬P x)  :=
begin
  split,
  exact demorgan_forall U P,
  exact demorgan_forall_converse U P,
end

theorem demorgan_exists_law :
  ¬(∃x, P x) ↔ (∀x, ¬P x)  :=
begin
  split,
  exact demorgan_exists U P,
  exact demorgan_exists_converse U P,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∃,∀:
------------------------------------------------

theorem exists_as_neg_forall :
  (∃x, P x) → ¬(∀x, ¬P x)  :=
begin
  intro H1,
  intro H2,
  cases H1 with y Hy,
  have := H2 y,
  contradiction,
end

theorem forall_as_neg_exists :
  (∀x, P x) → ¬(∃x, ¬P x)  :=
begin
  intro H1,
  intro H2,
  cases H2 with y Hy,
  have := H1 y,
  contradiction,
end

theorem forall_as_neg_exists_converse :
  ¬(∃x, ¬P x) → (∀x, P x)  :=
begin
  intro H1,
  intro x,
  by_contra Hx,
  apply H1,
  existsi x,
  exact Hx,
end

theorem exists_as_neg_forall_converse :
  ¬(∀x, ¬P x) → (∃x, P x)  :=
begin
  intro H1,
  by_contra H2,
  apply H1,
  intro x,
  by_contra H3,
  apply H2,
  existsi x,
  exact H3,
end

theorem forall_as_neg_exists_law :
  (∀x, P x) ↔ ¬(∃x, ¬P x)  :=
begin
  split,
  exact forall_as_neg_exists U P,
  exact forall_as_neg_exists_converse U P,
end

theorem exists_as_neg_forall_law :
  (∃x, P x) ↔ ¬(∀x, ¬P x)  :=
begin
  split,
  exact exists_as_neg_forall U P,
  exact exists_as_neg_forall_converse U P,
end


------------------------------------------------
--  Proposições de distributividade de quantificadores:
------------------------------------------------

theorem exists_conj_as_conj_exists :
  (∃x, P x ∧ Q x) → (∃x, P x) ∧ (∃x, Q x)  :=
begin
  intro H1,
  cases H1 with x H2,
  cases H2 with Px Qx,
  split,
  existsi x,
  exact Px,
  existsi x,
  exact Qx,
end

theorem exists_disj_as_disj_exists :
  (∃x, P x ∨ Q x) → (∃x, P x) ∨ (∃x, Q x)  :=
begin
  intro H1,
  cases H1 with x Hx,
  cases Hx,
  left,
  existsi x,
  exact Hx,
  right,
  existsi x,
  exact Hx,
end

theorem exists_disj_as_disj_exists_converse :
  (∃x, P x) ∨ (∃x, Q x) → (∃x, P x ∨ Q x)  :=
begin
  intro H1,
  cases H1,
  cases H1 with x Px,
  existsi x,
  left,
  exact Px,
  cases H1 with x Qx,
  existsi x,
  right,
  exact Qx,
end

theorem forall_conj_as_conj_forall :
  (∀x, P x ∧ Q x) → (∀x, P x) ∧ (∀x, Q x)  :=
begin
  intro H1,
  split,
  intro x,
  have H2 := H1 x,
  cases H2 with Px Qx,
  exact Px,
  intro x,
  have H2 := H1 x,
  cases H2 with Px Qx,
  exact Qx,
end

theorem forall_conj_as_conj_forall_converse :
  (∀x, P x) ∧ (∀x, Q x) → (∀x, P x ∧ Q x)  :=
begin
  intro H1,
  intro x,
  cases H1 with H2 H3,
  split,
  have Px := H2 x,
  exact Px,
  have Qx := H3 x,
  exact Qx,
end


theorem forall_disj_as_disj_forall_converse :
  (∀x, P x) ∨ (∀x, Q x) → (∀x, P x ∨ Q x)  :=
begin
  intro H1,
  intro x,
  cases H1,
  have Px := H1 x,
  left,
  exact Px,
  have Qx := H1 x,
  right,
  exact Qx,
end


/- NOT THEOREMS --------------------------------

theorem forall_disj_as_disj_forall :
  (∀x, P x ∨ Q x) → (∀x, P x) ∨ (∀x, Q x)  :=
begin
end

theorem exists_conj_as_conj_exists_converse :
  (∃x, P x) ∧ (∃x, Q x) → (∃x, P x ∧ Q x)  :=
begin
end

---------------------------------------------- -/

end predicate
