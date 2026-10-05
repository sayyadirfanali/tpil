namespace Chapter04

#check Eq.refl "hello"

universe u

variable (α : Type) (P Q : α → Prop)

variable (R : Prop)

/--
- `¬ ¬ P` is proven instead of `P` to make it constructive
- observe the symmetry in the dual legs of `Iff.intro`
-/
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
