import CORALean.ContSet.ContSet.ContSet

/-!
# What a layer is

CORA's `nnLayer`, split in two: `Layer` is what a layer *computes* on a set, and
`Layer.Sound` is the obligation tying that to an exact function. Everything
downstream is that obligation composed with itself.

The split is what makes a layer runnable. A structure with a noncomputable field
is noncomputable to construct, and `Vec ℝ n → Vec ℝ m` is such a field: storing
the specification beside `enclose` poisoned the computation next to it. So no
field of `Layer` mentions `ℝ`, every mention of it lives in a `Prop`, and a
float layer is a plain `def` whose soundness is a theorem.

A layer is a structure and not a class because a network holds many of them at
once and they are told apart by their weights, not by their types.

`Sound` is stated against a function of a point rather than a relation, which
makes the obligation an image inclusion: a layer whose behaviour is genuinely
set-valued is sound at the function it refines, and pays into `enclose`.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   07-September-2026
-- Last revision: 07-September-2026


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] {n m k : ℕ}
  {f : Vec ℝ n → Vec ℝ m} {g : Vec ℝ m → Vec ℝ k}


-- ========================================  MAIN TYPE  ========================================= --

structure Layer (S : ℕ → Type) [∀ n, ContSet (S n) (Vec ℝ n)] (n m : ℕ) where
  enclose : S n → S m

/-- The obligation `Layer` no longer carries: what `enclose` encloses. -/
structure Layer.Sound (L : Layer S n m) (f : Vec ℝ n → Vec ℝ m) : Prop where
  enclose_outer (s : S n) (x : Vec ℝ n) (hx : x ∈ construct s) :
    f x ∈ construct (L.enclose s)

/-- Soundness is stable under replacing the function by one that agrees with it
everywhere, which is what lets a caller name the map in its own terms. -/
theorem Layer.Sound.congr {L : Layer S n m} {f' : Vec ℝ n → Vec ℝ m} (h : L.Sound f)
    (hff : ∀ x, f' x = f x) : L.Sound f' :=
  ⟨fun s x hx => (hff x) ▸ h.enclose_outer s x hx⟩

/-- The obligation as an inclusion, which is the form it composes in. -/
theorem Layer.Sound.image_subset {L : Layer S n m} (h : L.Sound f) (s : S n) :
    f '' construct s ⊆ construct (L.enclose s) := by
  rintro _ ⟨x, hx, rfl⟩
  exact h.enclose_outer s x hx

/-- Carries a coordinate past a block untouched, which is how a skip connection
is written: the skipped coordinates travel in the same set as the rest, so the
dependency between them survives. -/
def Layer.identity (S : ℕ → Type) [∀ n, ContSet (S n) (Vec ℝ n)] (n : ℕ) : Layer S n n where
  enclose s := s

theorem Layer.identity_sound : (Layer.identity S n).Sound id := ⟨fun _ _ hx => hx⟩

/-- Applied right to left, as composition is written. -/
def Layer.comp (L₂ : Layer S m k) (L₁ : Layer S n m) : Layer S n k where
  enclose s := L₂.enclose (L₁.enclose s)

theorem Layer.comp_sound {L₂ : Layer S m k} {L₁ : Layer S n m} (h₂ : L₂.Sound g)
    (h₁ : L₁.Sound f) : (L₂.comp L₁).Sound (g ∘ f) :=
  ⟨fun s x hx => h₂.enclose_outer _ _ (h₁.enclose_outer s x hx)⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
