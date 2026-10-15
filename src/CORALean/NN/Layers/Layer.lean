module

public import CORALean.NN.Layers.Interfaces

@[expose] public section

/-!
# What a layer is

CORA's `nnLayer`, split in two: `Layer` is what a layer *computes* on a set, and
`Layer.Sound` is the obligation tying that to an exact function, [1, Prop. 2.14], stated
against a function of a point, so a set-valued layer is sound at the function it refines.
No field of `Layer` mentions `ℝ`: a structure with a noncomputable field is noncomputable
to construct, so every mention of `ℝ` lives in a `Prop` and a float layer is a plain `def`.
A layer is a structure, not a class: a network holds many, told apart by their weights.

The class is one level up, per *kind*, `Enclose` in `Interfaces.lean`. `Enclose.toLayer`
forgets the kind, which is how a chain mixes kinds and is read off a file at run time.

## References

* [1] T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural
      Network Verification using Sensitivity Analysis". HSCC 2023.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   24-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

universe u

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

/-- One layer of a kind, the kind forgotten, which is how a network holds it. -/
def Enclose.toLayer {L : ℕ → ℕ → Type u} [Enclose L S] (l : L n m) : Layer S n m where
  enclose := Enclose.enclose l

/-- What forgetting the kind keeps: the layer is sound at its kind's `eval`. -/
theorem Enclose.toLayer_sound {L : ℕ → ℕ → Type u} [Enclose L S] (l : L n m) :
    (Enclose.toLayer (S := S) l).Sound (Enclose.eval (S := S) l).out :=
  ⟨fun s _x hx => Enclose.enclose_outer l s (Set.mem_image_of_mem _ hx)⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
