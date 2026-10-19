module

public import CORALean.ContSet.ConZonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.Conversion.Float.Operations.Basic
public import CORALean.ContSet.Interval.Float.Operations.Point
public import CORALean.ContSet.HPolytope.Float.Theorems.MemConstruct
public import CORALean.ContSet.Zonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.InflatedContSet.Theorems.MonoSubset
public import CORALean.ContSet.Conversion.Float.Operations.HPolytope_to_ConZonotope

@[expose] public section

/-!
# A halfspace description as a constrained zonotope, over a floating-point scalar: `rowSplit`
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   08-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n q h : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- A row reads a point as the center's contribution plus the generators'. -/
theorem HPolytope.rowSplit (M : Mat 𝕋 q n) (G : Mat 𝕋 n h) (c : Vec 𝕋 n) (β : Vec ℝ h)
    (x : Vec ℝ n) (hx : ∀ k, x k = toReal (c k) + ∑ j, toReal (G k j) * β j)
    (i : Fin q) : -- --- CONCL ---
    (toRealMat M *ᵥ x) i
      = (∑ k, toReal (M i k) * toReal (c k))
        + ∑ j, (∑ k, toReal (M i k) * toReal (G k j)) * β j := by -- --- PROOF ---
  show ∑ k, toReal (M i k) * x k = _
  rw [Finset.sum_congr rfl fun k (_ : k ∈ Finset.univ) => by rw [hx k]]
  simp only [mul_add, Finset.mul_sum]
  rw [Finset.sum_add_distrib]
  refine congrArg _ ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by ring

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
