module

public import CORALean.ContSet.Zonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.Zonotope.Float.Theorems.MemGeneratorError
public import CORALean.ContSet.Interval.Float.Theorems.Basic
public import Mathlib.Data.Matrix.Basic
public import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_Interval

@[expose] public section

/-!
# A zonotope as a box, over a floating-point scalar

`Zonotope.matInterval_contains`: its `matInterval` contains it.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   09-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.matInterval_contains {m : ℕ} (Z : Zonotope (Mat 𝕋 m n)) :
    Z.construct ⊆ Z.matInterval.construct := by -- --- PROOF ---
  rintro _ ⟨a, ⟨β, hβ, ha⟩, e, he, rfl⟩
  show a + e ∈ _
  refine Interval.mem_mat_iff.mpr fun i j => ?_
  have he' : toReal (Z.I_error.inf i j) ≤ e i j ∧ e i j ≤ toReal (Z.I_error.sup i j) :=
    Interval.mem_mat_iff.mp he i j
  -- the generators reach no further than their absolute sum
  have hgen : |∑ k, β k * toReal (Z.G k i j)| ≤ toReal (sumUp fun k => absolute (Z.G k i j)) := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (le_trans ?_ (sum_le_sumUp _))
    refine Finset.sum_le_sum fun k _ => ?_
    rw [abs_mul, toReal_absolute]
    exact mul_le_of_le_one_left (abs_nonneg _) (hβ k)
  have hgen' := abs_le.mp hgen
  have hentry : (a + e) i j = toReal (Z.c i j) + ∑ k, β k * toReal (Z.G k i j) + e i j := by
    rw [ha]
    simp only [Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    rfl
  rw [hentry]
  -- each face on its own, the two roundings going opposite ways
  constructor
  · have h1 := addDown_le_add (subDown (Z.c i j) (sumUp fun k => absolute (Z.G k i j)))
      (Z.I_error.inf i j)
    have h2 := subDown_le_sub (Z.c i j) (sumUp fun k => absolute (Z.G k i j))
    show toReal (addDown (subDown (Z.c i j) (sumUp fun k => absolute (Z.G k i j)))
      (Z.I_error.inf i j)) ≤ _
    linarith [he'.1]
  · have h1 := add_le_addUp (addUp (Z.c i j) (sumUp fun k => absolute (Z.G k i j)))
      (Z.I_error.sup i j)
    have h2 := add_le_addUp (Z.c i j) (sumUp fun k => absolute (Z.G k i j))
    show _ ≤ toReal (addUp (addUp (Z.c i j) (sumUp fun k => absolute (Z.G k i j)))
      (Z.I_error.sup i j))
    linarith [he'.2]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
