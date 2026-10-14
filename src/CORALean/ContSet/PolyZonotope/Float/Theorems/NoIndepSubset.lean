module

public import CORALean.ContSet.PolyZonotope.Float.Operations.NoIndep
public import CORALean.ContSet.PolyZonotope.Real.Theorems.NoIndepSubset
public import CORALean.ContSet.PolyZonotope.Real.Instances

@[expose] public section

/-!
# `PolyZonotope.noIndep` is inside the set, in float too

Inner: the nominal part is the exact layer's `noIndep` of the original's, which is a subset,
and the error box is the same on both sides.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.noIndep_subset (pZ : PolyZonotope (Vec 𝕋 n)) :
    pZ.noIndep.construct ⊆ pZ.construct := by -- --- PROOF ---
  have h : InflatedContSet.nominal pZ.noIndep = (InflatedContSet.nominal pZ).noIndep := by
    show Real.PolyZonotope.mk _ _ _ _ _ _ _ = Real.PolyZonotope.mk _ _ _ _ _ _ _
    congr 1
    funext j
    exact j.elim0
  show InflatedContSet.nominalSet pZ.noIndep + pZ.I_error.construct
    ⊆ InflatedContSet.nominalSet pZ + pZ.I_error.construct
  have h2 : InflatedContSet.nominalSet pZ.noIndep
      = ((InflatedContSet.nominal pZ).noIndep).construct := by
    show ContSet.construct (InflatedContSet.nominal pZ.noIndep) = _
    rw [h]
    rfl
  rw [h2]
  exact Set.add_subset_add_right (Real.PolyZonotope.noIndep_subset _)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
