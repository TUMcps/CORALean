module

public import CORALean.ContSet.HPolytope.Float.Operations.Intersection
public import CORALean.ContSet.HPolytope.Float.Operations.MemStackRowsNominalIff
public import CORALean.ContSet.HPolytope.Float.Operations.Ineqs
public import CORALean.ContSet.HPolytope.Float.Operations.Basic
public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_HPolytope

@[expose] public section

/-!
# A box as halfspaces, over a floating-point scalar: `negIdentityMat_mulVec`

## Inputs
* `x` – vector
* `i` – row index

## Hypotheses
* none

## Conclusion
* negated identity flips the sign of entry `i`
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

-- the same for the negated identity, which is what turns a lower bound into a row
theorem negIdentityMat_mulVec (x : Vec ℝ n) (i : Fin n) : -- --- CONCL ---
    (toRealMat (negIdentityMat 𝕋 n) *ᵥ x) i = -(x i) := by -- --- PROOF ---
  show ∑ j, toReal (if i = j then neg (one : 𝕋) else zero) * x j = -(x i)
  rw [Finset.sum_eq_single i]
  · rw [if_pos rfl, toReal_neg, toReal_one, neg_one_mul]
  · intro j _ hj
    rw [if_neg (Ne.symm hj), toReal_zero, zero_mul]
  · intro hc
    exact absurd (Finset.mem_univ i) hc

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
