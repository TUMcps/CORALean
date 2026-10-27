module

public import CORALean.ContSet.Conversion.Float.Operations.VPolytope_to_IntervalMatrix
public import CORALean.ContSet.Conversion.Float.Theorems.Basic
public import CORALean.ContSet.VPolytope.Float.Theorems.UnvecExact
public import CORALean.ContSet.Interval.Float.Theorems.UnvecExact
public import CORALean.ContSet.Interval.Float.Theorems.IntervalMatrixOuter

@[expose] public section

/-!
# `VPolytope.intervalMatrix` contains the matrix polytope

Stacking is exact, the box of the stacked vertices contains the stacked polytope
(`VPolytope.interval_contains`), unstacking is exact, and the rebuild contains the box, so every
member of the matrix polytope lies in the interval matrix.

## Inputs
* `P` – matrix polytope

## Hypotheses
* none

## Conclusion
* every member of the polytope lies in the interval matrix
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open InflatedContSet FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {m n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem VPolytope.intervalMatrix_contains (P : VPolytope (Mat 𝕋 m n)) : -- --- CONCL ---
    InflatedContSet.construct P ⊆ P.intervalMatrix.construct := by -- --- PROOF ---
  intro A hA
  -- the stacked matrix is in the stacked polytope, hence in its box
  have h0 : matVecEquiv A ∈ InflatedContSet.construct P.vec := by
    rw [VPolytope.vec_exact]; exact ⟨A, hA, rfl⟩
  have h1 : matVecEquiv A ∈ P.vec.interval.construct := VPolytope.interval_contains P.vec h0
  -- so the matrix is in the unstacked box, and the rebuild keeps it
  have h2 : A ∈ P.vec.interval.unvec.construct := by
    rw [Interval.unvec_exact]
    exact ⟨_, h1, matVecEquiv.symm_apply_apply A⟩
  exact Interval.intervalMatrix_outer _ h2

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
