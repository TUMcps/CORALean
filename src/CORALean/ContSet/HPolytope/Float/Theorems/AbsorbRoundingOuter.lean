module

public import CORALean.Global.Float.ToRealMatMulVec
public import CORALean.ContSet.HPolytope.Float.Operations.AbsorbRounding
public import CORALean.ContSet.HPolytope.Float.Operations.MulVecAppendLeft
public import CORALean.ContSet.HPolytope.Float.Theorems.RowsOfMemConstruct

@[expose] public section

/-!
# `HPolytope.absorbRounding` encloses

The polytope with its error box moved into the rows contains the polytope: a point of the
box adds to a row at most the box's support in that row's direction, and the right-hand side
was raised by exactly that, rounded up.

## Inputs
* `P` – H-polytope

## Hypotheses
* none

## Conclusion
* `P` is contained in `absorbRounding P`
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.absorbRounding_outer (P : HPolytope 𝕋 (Vec 𝕋 n)) :
    P.construct ⊆ P.absorbRounding.construct := by -- --- PROOF ---
  intro x hx
  obtain ⟨hA, hE⟩ := HPolytope.rows_of_mem_construct hx
  rw [HPolytope.mem_construct_iff (HPolytope.errFree_of_origin rfl rfl rfl)]
  refine ⟨Fin.addCases (fun i => ?_) fun k => ?_, fun i => i.elim0⟩
  · simp only [HPolytope.absorbRounding, HPolytope.mulVec_append_left, Fin.append_left]
    exact hA i
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) k
    · simp only [HPolytope.absorbRounding, toRealMat_append_mulVec_natAdd,
        HPolytope.mulVec_append_left, Fin.append_left, Fin.append_right]
      exact (hE i).1
    · simp only [HPolytope.absorbRounding, toRealMat_append_mulVec_natAdd, Fin.append_right]
      exact (congrFun (toRealMat_neg_mulVec P.Ae x) i).trans_le (hE i).2

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
