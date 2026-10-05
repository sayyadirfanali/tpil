namespace Chapter03

theorem de_morgan_1 (P Q : Prop) : ¬ (P ∨ Q) -> ¬ P ∧ ¬ Q :=
  fun npoq => ⟨fun p => npoq (Or.inl p), fun Q => npoq (Or.inr Q)⟩

-- needs `Classical.em` as there is no way to generate `P ∨ Q` else
theorem de_morgan_2 (P Q : Prop) : ¬ (P ∧ Q) -> ¬ P ∨ ¬ Q :=
  fun npaq => match (Classical.em Q) with
    | .inl q => .inl (fun p => npaq ⟨p, q⟩)
    | .inr nq => .inr nq

theorem dni {P} : P -> ¬ ¬ P :=
  fun p => (fun np => np p)

theorem dne {P} : ¬ ¬ P -> P :=
  fun nnp => match Classical.em P with
    | .inl p  => p
    | .inr np => absurd np nnp -- False.elim (nnp np)

/--
Negation of Negation of Excluded Middle:
- can be proved in constructive logic unlike LEM
- trick here resembles Wadler's Deal with the Devil
- in order to generate a value of type `P ∨ ¬ P`, we start with `¬ P` which
demands `P` but as soon as we get `P` we return it instead
--/
theorem nnem {P} : ¬ ¬ (P ∨ ¬ P) := fun h => h (Or.inr (fun p => h (Or.inl p)))

/--
Law of Excluded Middle
- only true in constructive logic here proven using `dne` and `nnem`
- NB: `dne` can be proved from a monomorphic `em` but converse requires a
universally quantified `dne` as it is not applied on P but on `P ∨ ¬ P`
--/
theorem em {P} : P ∨ ¬ P := by
  exact (dne nnem)

theorem comm_and {P Q} : P ∧ Q <-> Q ∧ P :=
  Iff.intro (fun ⟨p, q⟩ => ⟨q, p⟩) (fun ⟨q, p⟩ => ⟨p, q⟩)

theorem assoc_and {P Q R} : (P ∧ Q) ∧ R <-> P ∧ (Q ∧ R) :=
  Iff.intro
    (fun ⟨⟨p, q⟩, r⟩ => ⟨p, ⟨q, r⟩⟩)
    (fun ⟨p, ⟨q, r⟩⟩ => ⟨⟨p, q⟩, r⟩)

theorem ncont {P} : ¬ (P ∧ ¬ P) :=
  fun ⟨p, np⟩  => np p

theorem pof {P} : P ∨ False <-> P :=
  Iff.intro (fun (Or.inl p) => p) (fun p => Or.inl p)

theorem paf {P} : P ∧ False <-> False :=
  Iff.intro (fun ⟨_, f⟩ => f) (fun f => False.elim f)

theorem modus_tollens {P Q} : (P -> Q) -> (¬ Q → ¬ P) := fun pq nq p => nq (pq p)

/--
Peirce's Law aka `call/cc`
- `call/cc` takes a function `f` which consumes a continuation `k : P -> Q`
which represents the rest of the program.
- `k` takes `P` as input and is supposed to return some absurd value `q : Q` but
never does as whenever the continuation is evoked inside the function `f`,
`call/cc` just /teleports/ the value passed to that continuation into the
current continuation.
- relies on the same *bait and switch* trick as used in `em` above
--/
theorem peirce_from_em {P Q : Prop} : ((P -> Q) -> P) -> P :=
  fun f => match Classical.em P with
    | .inl p  => p
    | .inr np => f (fun p => absurd p np)

theorem peirce_from_dne {P Q : Prop} : ((P -> Q) -> P) -> P :=
  fun f => dne (fun np => np <| f (fun p => absurd p np))

/--
Peirce's Law was crucial even before `call/cc` because it allowed one to
derive `em` and `dne` with nothing but implication
--/
theorem peirce_to_em {P} : (P ∨ ¬ P) :=
  peirce_from_em (P := P ∨ ¬ P) (Q := False) (fun k => Or.inr (fun p => k (Or.inl p)))

theorem peirce_to_dne {P} : ¬ ¬ P -> P :=
  fun nnp => peirce_from_em (P := P) (Q := False) (fun k => absurd k nnp)

-- Law of Non-Contradition
theorem lnc {P} : ¬ (P <-> ¬ P) :=
  fun ⟨pinp, npip⟩ =>
    have np := fun p => pinp p p
    np (npip np)

end Chapter03
