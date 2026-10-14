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
# A halfspace description as a constrained zonotope, over a floating-point scalar: `prodError`
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

/-- What the stored product can be off by, on the unit box. -/
theorem HPolytope.prodError (M : Mat 𝕋 q n) (G : Mat 𝕋 n h) (β : Vec ℝ h)
    (hβ : ∀ j, |β j| ≤ 1) (i : Fin q) :
    |(∑ j, (∑ k, toReal (M i k) * toReal (G k j)) * β j)
        - (toRealMat (matMulDown M G) *ᵥ β) i|
      ≤ toReal (radius (matMulDiff M G) i) := by -- --- PROOF ---
  have hd : ∀ (i' : Fin q) (j : Fin h),
      |(∑ k, toReal (M i' k) * toReal (G k j)) - toReal (matMulDown M G i' j)|
        ≤ |toReal (matMulDiff M G i' j)| := by
    intro i' j
    have h₁ : toReal (matMulDown M G i' j) ≤ ∑ k, toReal (M i' k) * toReal (G k j) :=
      dotDown_le (M i') fun k => G k j
    have h₂ : (∑ k, toReal (M i' k) * toReal (G k j)) ≤ toReal (matMulUp M G i' j) :=
      le_dotUp (M i') fun k => G k j
    have h₃ : toReal (matMulUp M G i' j) - toReal (matMulDown M G i' j)
        ≤ toReal (matMulDiff M G i' j) := sub_le_subUp _ _
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    linarith
  -- the difference reshaped into one sum, so `abs_sum_le_radius` applies to it
  have hshape : (∑ j, (∑ k, toReal (M i k) * toReal (G k j)) * β j)
      - (toRealMat (matMulDown M G) *ᵥ β) i
      = ∑ j, ((∑ k, toReal (M i k) * toReal (G k j)) - toReal (matMulDown M G i j)) * β j := by
    show _ - ∑ j, toReal (matMulDown M G i j) * β j = _
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hshape]
  exact abs_sum_le_radius hd hβ i

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
