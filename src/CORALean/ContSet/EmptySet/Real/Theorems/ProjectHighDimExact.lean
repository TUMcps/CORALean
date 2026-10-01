import CORALean.ContSet.EmptySet.Real.Operations.ProjectHighDim
import CORALean.ContSet.EmptySet.Real.Instances

/-!
# `EmptySet.projectHighDim_` is exact

`projectHighDim_` embeds the coordinates at `proj` and holds the rest at zero
(`Function.extend`), so the image of `∅` is `∅`.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


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
