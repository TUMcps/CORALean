module

public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_MatPolytope
public import CORALean.ContSet.Conversion.Float.Theorems.IntervalVPolytopeContains
public import CORALean.ContSet.VPolytope.Float.Theorems.UnvecExact

@[expose] public section

/-!
# `Interval.matPolytope` contains the interval matrix

The corners of the stacked box always contain the stacked box, and stacking and unstacking are
exact, so the matrix polytope of the corners contains every matrix of the box, whether or not the
bounds are ordered.

## Inputs
* `I` – interval matrix

## Hypotheses
* none

## Conclusion
* every matrix of the box lies in the corners' polytope
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

theorem Interval.matPolytope_contains (I : Interval (Mat 𝕋 m n)) : -- --- CONCL ---
    I.construct ⊆ InflatedContSet.construct I.matPolytope := by -- --- PROOF ---
  intro A hA
  -- the stacked matrix is in the stacked box, hence in its corners
  have h1 : matVecEquiv A ∈ (Interval.vPolytope I.vec).construct :=
    Interval.vPolytope_contains I.vec (by rw [Interval.vec_exact]; exact ⟨A, hA, rfl⟩)
  rw [Interval.matPolytope, VPolytope.unvec_exact]
  exact ⟨_, h1, matVecEquiv.symm_apply_apply A⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
