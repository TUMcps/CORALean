module

public import CORALean.ContSet.Fullspace.Real.Operations.Project

@[expose] public section

/-!
# `Fullspace.project` is exact

The image of everything under the coordinate selection `dims` is everything, provided
`dims` names distinct coordinates. CORA does not check that: `dims = [1,1]` is a
projection onto the diagonal, which is not the full space of dimension two.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Fullspace.project_exact (F : Fullspace n) (dims : Fin m → Fin n)
    (hdims : Function.Injective dims) :
    (F.project dims).construct =
      (fun (x : Vec ℝ n) (j : Fin m) => x (dims j)) '' F.construct := by -- --- PROOF ---
  ext y
  refine ⟨fun _ => ⟨(Function.extend dims y 0 : Vec ℝ n), Set.mem_univ _, ?_⟩,
    fun _ => Set.mem_univ _⟩
  funext j
  exact hdims.extend_apply y 0 j

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
