module

public import CORALean.Global.Tensor
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Algebra.Group.Pointwise.Set.Basic

@[expose] public section

/-!
# Appending sums coordinatewise

The image of a product of sets under `Fin.append` is the set of their stacked members, and stacking
is additive: the sum of two such sets is the stack of the sums. What lets a Cartesian product of
inflated sets (a nominal set plus an error box, on each side) be one inflated set.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Pointwise

variable {n₁ n₂ : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem append_image_prod_add (A₁ B₁ : Set (Vec ℝ n₁)) (A₂ B₂ : Set (Vec ℝ n₂)) : -- --- STMT ---
    (fun p : Vec ℝ n₁ × Vec ℝ n₂ => Fin.append p.1 p.2) '' (A₁ ×ˢ A₂) +
        (fun p : Vec ℝ n₁ × Vec ℝ n₂ => Fin.append p.1 p.2) '' (B₁ ×ˢ B₂) =
      (fun p : Vec ℝ n₁ × Vec ℝ n₂ => Fin.append p.1 p.2) ''
        ((A₁ + B₁) ×ˢ (A₂ + B₂)) := by -- --- PROOF ---
  ext z
  constructor
  · rintro ⟨_, ⟨⟨a₁, a₂⟩, ⟨ha₁, ha₂⟩, rfl⟩, _, ⟨⟨b₁, b₂⟩, ⟨hb₁, hb₂⟩, rfl⟩, rfl⟩
    refine ⟨(a₁ + b₁, a₂ + b₂), ⟨⟨a₁, ha₁, b₁, hb₁, rfl⟩, ⟨a₂, ha₂, b₂, hb₂, rfl⟩⟩, ?_⟩
    funext i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp
  · rintro ⟨⟨_, _⟩, ⟨⟨a₁, ha₁, b₁, hb₁, rfl⟩, ⟨a₂, ha₂, b₂, hb₂, rfl⟩⟩, rfl⟩
    refine ⟨Fin.append a₁ a₂, ⟨(a₁, a₂), ⟨ha₁, ha₂⟩, rfl⟩, Fin.append b₁ b₂,
      ⟨(b₁, b₂), ⟨hb₁, hb₂⟩, rfl⟩, ?_⟩
    funext i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
