import CORALean.ContSet.Zonotope.Float.Operations.MatZonotope
import CORALean.ContSet.Zonotope.Float.Theorems.MemNominalSet
import CORALean.ContSet.Interval.Float.Theorems.MemMatIff
import Mathlib.Data.Matrix.Basic

/-!
# `Zonotope.matZonotope` holds every column of the zonotope

A point of the zonotope, as a one-column matrix, is a point of the reshaped matrix zonotope:
the same coefficients, and the error box moved with it.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   09-October-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.matZonotope_contains (Z : Zonotope (Vec 𝕋 n)) {z : Vec ℝ n}
    (hz : z ∈ Z.construct) :
    (fun i _ => z i : Mat ℝ n 1) ∈ Z.matZonotope.construct := by -- --- PROOF ---
  obtain ⟨a, ha, e, he, rfl⟩ := hz
  obtain ⟨β, hβ, hai⟩ := Zonotope.mem_nominalSet_iff.mp ha
  refine ⟨fun i _ => a i, ⟨β, hβ, ?_⟩, fun i _ => e i, ?_, rfl⟩
  · -- the column of the nominal point is the nominal centre plus the combination
    ext i j
    simp only [Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    rw [hai i]
    simp only [Zonotope.matZonotope]
    exact congrArg _ (Finset.sum_congr rfl fun _ _ => mul_comm _ _)
  · -- the error box, column by column
    refine Interval.mem_mat_iff.mpr fun i j => ?_
    exact he i

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
