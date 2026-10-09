import Mathlib.Tactic

namespace Chapter05

theorem de_morgan_1 {P Q : Prop} : ¬ (P ∨ Q) -> ¬ P ∧ ¬ Q := by
  intro npoq
  apply And.intro
  · intro p
    exact npoq (Or.inl p)
  · intro q
    exact npoq (Or.inr q)

theorem de_morgan_2 {P Q : Prop} : ¬ (P ∧ Q) -> ¬ P ∨ ¬ Q := by
  intro npaq
  by_cases q : Q
  case pos =>
    left
    intro p
    exact npaq ⟨p, q⟩
  case neg =>
    right
    assumption

theorem dni {P : Prop} : P -> ¬ ¬ P := by
  intro p np
  contradiction

theorem dne {P : Prop} : ¬ ¬ P -> P := by
  intro nnp
  by_contra np
  contradiction

theorem nnem {P : Prop} : ¬ ¬ (P ∨ ¬ P) := by
  intro nponp
  exact nponp (Or.inr (fun p => nponp (Or.inl p)))

theorem em {P : Prop} : P ∨ ¬ P := by
  exact dne nnem

theorem comm_and {P Q : Prop} : P ∧ Q <-> Q ∧ P := by
  constructor
  case mp =>
    intro ⟨p, q⟩
    exact ⟨q, p⟩
  case mpr =>
    intro ⟨q, p⟩
    exact ⟨p, q⟩

theorem assoc_and {P Q R : Prop} : (P ∧ Q) ∧ R <-> P ∧ (Q ∧ R) := by
  constructor
  case mp  =>
    intro ⟨⟨p, q⟩, r⟩
    exact ⟨p, ⟨q, r⟩⟩
  case mpr =>
    intro ⟨p, ⟨q, r⟩⟩
    exact ⟨⟨p, q⟩, r⟩

theorem ncont {P : Prop} : ¬ (P ∧ ¬ P) := by
  intro ⟨p, np⟩
  contradiction

theorem pof {P : Prop} : P ∨ False <-> P := by
  constructor
  case mp  =>
    intro (Or.inl p)
    exact p
  case mpr =>
    intro p
    exact Or.inl p

theorem paf {P : Prop} : P ∧ False <-> False := by
  constructor
  · intro ⟨_, f⟩
    exact f
  · intro f
    contradiction

theorem modus_tollens {P Q : Prop} : (P -> Q) -> (¬ Q → ¬ P) := by
  intro pq nq p
  exact nq (pq p)

theorem peirce_from_em {P Q : Prop} : ((P -> Q) -> P) -> P := by
  intro f
  by_cases h : P
  case pos => exact h
  case neg =>
    apply f
    intro p
    contradiction

theorem peirce_from_dne {P Q : Prop} : ((P -> Q) -> P) -> P := by
  intro f
  have nnp : ¬ ¬ P := by
    intro np
    apply np
    apply f
    intro p
    contradiction
  exact dne nnp

theorem peirce_to_em {P : Prop} : (P ∨ ¬ P) := by
  apply peirce_from_em (Q := False)
  intro f
  right
  intro p
  exact f (Or.inl p)

theorem peirce_to_dne {P : Prop} : ¬ ¬ P -> P := by
  intro nnp
  apply peirce_from_dne (Q := False)
  intro np
  contradiction

theorem lnc {P : Prop} : ¬ (P <-> ¬ P) := by
  intro ⟨ h1, h2 ⟩
  have p : P := h2 (fun p => (h1 p p))
  apply h1 <;> exact p

variable (α : Type) (P Q : α → Prop)
variable (R : Prop)

example : (¬ ∀ x, ¬ P x) <-> (¬ ¬ ∃ x, P x) := by
  constructor
  · intro fa ex
    apply fa
    intro x px
    exact ex ⟨x, px⟩
  · intro ex fa
    apply ex
    intro ⟨x, px⟩
    exact fa x px

example : (∃ x, P x ∧ R) <-> (∃ x, P x) ∧ R := by
  constructor
  · intro ⟨x, ⟨px, r⟩⟩
    exact ⟨⟨x, px⟩, r⟩
  · intro ⟨⟨x, px⟩, r⟩
    exact ⟨x, ⟨px, r⟩⟩

example : (∃ x, P x ∧ Q x) -> (∃ x, P x) ∧ (∃ x, Q x) := by
  intro ⟨x, ⟨px, qx⟩⟩
  exact ⟨⟨x, px⟩, ⟨x, qx⟩⟩

example : (∀ x, P x) <-> ¬ (∃ x, ¬ P x) := by
  constructor
  · intro fa ⟨x, npx⟩
    exact npx (fa x)
  · intro nex x
    by_contra npx
    apply nex
    exact ⟨x, npx⟩

example : (∃ x, P x) <-> ¬ (∀ x, ¬ P x) := by
  constructor
  · intro ⟨x, px⟩ nfa
    exact (nfa x) px
  · intro nfa
    by_contra nex
    apply nfa
    intro x px
    exact nex ⟨x, px⟩

example : (¬ ∃ x, P x) <-> (∀ x, ¬ P x) := by
  constructor
  · intro nex x px
    exact nex ⟨x, px⟩
  · intro fa ⟨x, px⟩
    exact fa x px

example : (¬ ∀ x, P x) <-> (∃ x, ¬ P x) := by
  constructor
  · intro nfa
    by_contra nex
    apply nfa
    intro x
    by_contra npx
    exact nex ⟨x, npx⟩
  · intro ⟨x, npx⟩ fa
    apply npx
    exact fa x

example : (∀ x, P x -> R) <-> (∃ x, P x) -> R := by
  constructor
  · intro fa ⟨x, px⟩
    exact fa x px
  · intro ex x px
    exact ex ⟨x, px⟩

example (a : α) : (∃ x, P x -> R) <-> (∀ x, P x) -> R := by
  constructor
  · intro ⟨x, pxr⟩ fa
    exact pxr (fa x)
  · intro fa
    by_cases h : ∀ (x : α), P x
    · have r : R := fa h
      exact ⟨a, fun _ => r⟩
    · have ⟨x, npx⟩ : ∃ x, ¬ (P x) := by
        by_contra nex
        apply h
        intro x
        by_contra npx
        exact nex ⟨x, npx⟩
      refine ⟨x, ?_⟩
      intro px
      contradiction

example (a : α) : (∃ x, R -> P x) <-> (R -> ∃ x, P x) := by
  constructor
  · intro ⟨x, rpx⟩ r
    exact ⟨x, rpx r⟩
  · intro rex
    by_cases h : R
    · obtain ⟨x, px⟩ := rex h
      exact ⟨x, fun _ => px⟩
    · refine ⟨a, ?_⟩
      intro r
      contradiction

variable (men : Type) (barber : men)
variable (shaves : men -> men -> Prop)

theorem russell_paradox_class (h : ∀ x : men, shaves barber x <-> ¬ shaves x x) : False := by
  let ⟨h1, h2⟩ := h barber
  by_cases h : shaves barber barber
  · exact h1 h h
  · exact h1 (h2 h) (h2 h)

theorem russell_paradox_const (h : ∀ x : men, shaves barber x <-> ¬ shaves x x) : False := by
  let ⟨h1, h2⟩ := h barber
  have s : shaves barber barber := h2 (fun x => False.elim (h1 x x))
  exact h1 s s

example (p q r : Prop) (hp : p) :
  (p ∨ q ∨ r) ∧ (q ∨ p ∨ r) ∧ (q ∨ r ∨ p) := by
  simp [hp]

end Chapter05
