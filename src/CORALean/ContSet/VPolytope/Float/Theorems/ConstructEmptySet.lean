module

public import CORALean.ContSet.VPolytope.Float.Operations.EmptySet
public import CORALean.ContSet.VPolytope.Float.Theorems.NominalEq
public import CORALean.ContSet.VPolytope.Real.Operations.ConstructEmptySet

@[expose] public section

/-!
# `VPolytope.emptySet` denotes `∅`

The nominal part is the exact layer's empty vertex list, and the sum of `∅` with
any box is `∅`.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* the polytope with no vertices denotes the empty set
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem VPolytope.construct_emptySet : (VPolytope.emptySet 𝕋 n).construct = ∅ := by -- --- PROOF ---
  have h : InflatedContSet.nominal (VPolytope.emptySet 𝕋 n)
      = Real.VPolytope.emptySet (Vec ℝ n) := by
    rw [VPolytope.nominal_eq]
    show (⟨0, _⟩ : Real.VPolytope (Vec ℝ n)) = ⟨0, _⟩
    congr 1
    funext l
    exact l.elim0
  have hN : InflatedContSet.nominalSet (VPolytope.emptySet 𝕋 n) = ∅ := by
    unfold InflatedContSet.nominalSet
    rw [h]
    exact Real.VPolytope.construct_emptySet
  show InflatedContSet.nominalSet (VPolytope.emptySet 𝕋 n)
      + (VPolytope.emptySet 𝕋 n).I_error.construct = _
  rw [hN, Set.empty_add]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
