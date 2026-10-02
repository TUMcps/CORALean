import CORALean.ContSet.Zonotope.Float.Theorems.MemNominalSet
import CORALean.ContSet.MatZonotope.Float.MatZonotope
import CORALean.ContSet.Interval.Float.Theorems.MemMatIff
import Mathlib.Data.Matrix.Basic

/-!
# Float zonotope to float matrix zonotope

CORA's `zonotope/matZonotope`: the centre and each generator reshaped to an `n × 1` matrix, which
the matrix zonotope's product with a matrix zonotope of conforming shape then consumes. Nothing is
rounded: the entries, and the error box with them, are moved as stored.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

def Zonotope.matZonotope (Z : Zonotope 𝕋 n) : MatZonotope 𝕋 n 1 where
  h := Z.h
  c := fun i _ => Z.c i
  G := fun k i _ => Z.G i k
  E := ⟨fun i _ => Z.E.inf i, fun i _ => Z.E.sup i⟩

open Pointwise SoundFloatArithmetic InflatedContSet

variable [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.matZonotope_contains (Z : Zonotope 𝕋 n) {z : Vec ℝ n} (hz : z ∈ Z.construct) :
    (fun i _ => z i : Mat ℝ n 1) ∈ Z.matZonotope.construct := by -- --- PROOF ---
  obtain ⟨a, ha, e, he, rfl⟩ := hz
  obtain ⟨β, hβ, hai⟩ := Zonotope.mem_nominalSet_iff.mp ha
  refine ⟨fun i _ => a i, ⟨β, hβ, ?_⟩, fun i _ => e i, ?_, rfl⟩
  · -- the column of the nominal point is the nominal centre plus the combination
    ext i j
    simp only [Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    rw [hai i]
    simp only [MatZonotope.nominal, Zonotope.matZonotope, toRealMat]
    exact congrArg _ (Finset.sum_congr rfl fun _ _ => mul_comm _ _)
  · -- the error box, column by column
    refine Interval.mem_mat_iff.mpr fun i j => ?_
    exact he i

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
