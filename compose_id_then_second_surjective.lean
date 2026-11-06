import functions

theorem compose_id_then_second_surjective { S T : Type }
  { f : S → T } { g : T → S }
  ( h : g ∘ f = id )
  : surjective g := by
  intro x
  apply Exists.intro (f x)
  change (g ∘ f) x = x
  rw [h]
  rfl
