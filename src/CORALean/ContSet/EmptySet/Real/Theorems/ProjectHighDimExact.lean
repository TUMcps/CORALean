module

public import CORALean.ContSet.EmptySet.Real.Operations.ProjectHighDim
public import CORALean.ContSet.EmptySet.Real.Instances

@[expose] public section

/-!
# `EmptySet.projectHighDim_` is exact

`projectHighDim_` embeds the coordinates at `proj` and holds the rest at zero
(`Function.extend`), so the image of `∅` is `∅`.

## Inputs
* `E` – empty set
* `N` – target dimension
* `proj` – coordinates of the old dimensions

## Hypotheses
* none

## Conclusion
* `projectHighDim_` denotes the image under the zero-padded embedding
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open ContSet

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem EmptySet.projectHighDim_exact (E : EmptySet n) (N : ℕ) (proj : Fin n → Fin N) :
    construct (E.projectHighDim_ N proj) =
      (fun (x : Vec ℝ n) => (Function.extend proj x 0 : Vec ℝ N)) '' construct E := by
  change (∅ : Set (Vec ℝ N)) = _ '' (∅ : Set (Vec ℝ n))
  exact (Set.image_empty _).symm

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
