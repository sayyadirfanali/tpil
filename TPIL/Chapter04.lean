namespace Chapter04

variable (α : Type) (P Q : α → Prop)
variable (R : Prop)

example : (¬ ∀ x, ¬ P x) <-> (¬ ¬ ∃ x, P x) :=
  ⟨
    fun fa ex => fa (fun x px => ex ⟨x, px⟩)
  , fun ex fa => ex (fun ⟨x, px⟩ => fa x px)
  ⟩

example : (∃ x, P x ∧ R) <-> (∃ x, P x) ∧ R :=
  ⟨
    fun ⟨x, ⟨px, r⟩⟩ => ⟨⟨x, px⟩, r⟩
  , fun ⟨⟨x, px⟩, r⟩ => ⟨x, ⟨px, r⟩⟩
  ⟩

example : (∃ x, P x ∧ Q x) -> (∃ x, P x) ∧ (∃ x, Q x) :=
    fun ⟨x, ⟨px, qx⟩⟩ => ⟨⟨x, px⟩, ⟨x, qx⟩⟩

example : (∀ x, P x) <-> ¬ (∃ x, ¬ P x) :=
  ⟨
    fun fa ⟨x, npx⟩ => npx (fa x)
  , fun ex x => Classical.byContradiction (fun npx => ex ⟨x, npx⟩)
  ⟩

example : (∃ x, P x) <-> ¬ (∀ x, ¬ P x) :=
  ⟨
    fun ⟨x, px⟩ fa => fa x px
  , fun fa => Classical.byContradiction (fun ex => fa (fun x px => ex ⟨x, px⟩))
  ⟩

example : (¬ ∃ x, P x) <-> (∀ x, ¬ P x) :=
  ⟨
    fun ex x px => ex ⟨x, px⟩
  , fun fa ⟨x, px⟩ => fa x px
  ⟩

example : (¬ ∀ x, P x) <-> (∃ x, ¬ P x) :=
  ⟨
    fun fa => Classical.byContradiction (fun ex => fa (fun x => Classical.byContradiction (fun npx => ex ⟨x, npx⟩)))
  , fun ⟨x, npx⟩ fa => npx (fa x)
  ⟩

example : (∀ x, P x -> R) <-> (∃ x, P x) -> R :=
  ⟨
    fun fa => Classical.byContradiction (fun ex => ex (fun ⟨x, px⟩ => fa x px))
  , fun ex => fun x px => ex ⟨x, px⟩
  ⟩

example (a : α) : (∃ x, P x -> R) <-> (∀ x, P x) -> R :=
  ⟨
    fun ⟨x, pxr⟩ fa => pxr (fa x)
  , fun fa => Classical.byContradiction
      (fun ex => ex ⟨a, fun _ => fa (fun x => Classical.byContradiction (fun npx => ex ⟨x, fun px => absurd px npx⟩))⟩)
  ⟩

example (a : α) : (∃ x, R -> P x) <-> (R -> ∃ x, P x) :=
  ⟨
    fun ⟨x, rpx⟩ r => ⟨x, rpx r⟩
  , fun rex => Classical.byContradiction
    (fun ex => ex ⟨a, fun r => let ⟨x, px⟩ := rex r; False.elim (ex ⟨x, fun _ => px⟩)⟩)
  ⟩

/--
- same theorem as above but uses `.em` on `R`
- `.byContradiction` does `.em` only on the goal but sometimes `.em` on some
hypothesis is better
-/
example (a : α) : (∃ x, R -> P x) <-> (R -> ∃ x, P x) :=
  ⟨
    fun ⟨x, rpx⟩ r => ⟨x, rpx r⟩
  , fun rex => match Classical.em R with
      | .inl r  => let ⟨x, px⟩ := rex r; ⟨x, fun _ => px⟩
      | .inr nr => ⟨a, fun r => absurd r nr⟩
  ⟩

variable (men : Type) (barber : men)
variable (shaves : men -> men -> Prop)

/--
Russell's Paradox (classical)
-/
theorem russell_paradox_class (h : ∀ x : men, shaves barber x <-> ¬ shaves x x) : False :=
  match Classical.em (shaves barber barber) with
  | .inl b  => ((h barber).mp b) b
  | .inr nb => absurd ((h barber).mpr nb) nb

/--
Russell's Paradox (constructive)
-/
theorem russell_paradox_const (h : ∀ x : men, shaves barber x <-> ¬ shaves x x) : False := by
  obtain ⟨ mp, mpr ⟩ := h barber
  have x := mpr (fun s => mp s s)
  exact (mp x x)

end Chapter04
