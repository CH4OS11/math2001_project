import functions

theorem compose_id_then_first_injective { S T : Type }
  { f : S → T } { g : T → S }
  ( h : g ∘ f = id )
  : injective f := by
  intro x y hxy
  have h1 : g (f x) = g (f y) := by
    rw [hxy]
  have h2 : g (f x) = x := by
    change (g ∘ f) x = x
    rw [h]
    rfl
  have h3 : g (f y) = y := by
    change (g ∘ f) y = y
    rw [h]
    rfl
  rw [h2, h3] at h1
  exact h1
