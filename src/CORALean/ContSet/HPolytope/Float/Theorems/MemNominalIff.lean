module

public import CORALean.ContSet.HPolytope.Float.HPolytope
public import CORALean.ContSet.HPolytope.Real.Operations.Basic
public import CORALean.ContSet.HPolytope.Real.Theorems.IntersectionExact

@[expose] public section

/-!
# Membership in the nominal part of a float polytope

The nominal part is the exact layer's `ineqs` intersected with its `eqs`, so membership is the
stored rows read as reals.
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

theorem HPolytope.mem_nominal_iff {P : HPolytope 𝕋 (Vec 𝕋 n)} {x : Vec ℝ n} :
    x ∈ P.nominal.construct ↔ (∀ i, (toRealMat P.A *ᵥ x) i ≤ toReal (P.b i))
      ∧ ∀ i, (toRealMat P.Ae *ᵥ x) i = toReal (P.be i) := by
  -- three lemmas of the exact layer, in order
  rw [HPolytope.nominal, Real.HPolytope.mem_intersection_iff, Real.HPolytope.mem_ineqs_iff,
    Real.HPolytope.mem_eqs_iff]
  exact Iff.rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
