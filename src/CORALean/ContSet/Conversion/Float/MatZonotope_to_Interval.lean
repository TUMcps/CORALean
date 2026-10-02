import CORALean.ContSet.Interval.Float.Theorems.MemMatIff
import CORALean.ContSet.MatZonotope.Float.MatZonotope
import Mathlib.Data.Matrix.Basic

/-!
# Float matrix zonotope to interval matrix

`Float.Zonotope.interval` entry by entry: the centre widened by the generators' absolute
sum, rounded outward, plus the box. CORA's `intervalMatrix(matZonotope)`; what the
matrix-zonotope product needs of a factor's error terms, and what bounds a norm.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {m n : ℕ}

def MatZonotope.interval (Z : MatZonotope 𝕋 m n) : Interval (Mat 𝕋 m n) :=
  let r : Mat 𝕋 m n := fun i j => sumUp fun k => absolute (Z.G k i j)   -- Σ |G_k|
  ⟨fun i j => addDown (subDown (Z.c i j) (r i j)) (Z.E.inf i j),
   fun i j => addUp (addUp (Z.c i j) (r i j)) (Z.E.sup i j)⟩

open Pointwise SoundFloatArithmetic

variable [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem MatZonotope.interval_contains (Z : MatZonotope 𝕋 m n) :
    Z.construct ⊆ Z.interval.construct := by -- --- PROOF ---
  rintro _ ⟨a, ⟨β, hβ, ha⟩, e, he, rfl⟩
  show a + e ∈ _
  refine Interval.mem_mat_iff.mpr fun i j => ?_
  have he' := Interval.mem_mat_iff.mp he i j
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
      (Z.E.inf i j)
    have h2 := subDown_le_sub (Z.c i j) (sumUp fun k => absolute (Z.G k i j))
    show toReal (addDown (subDown (Z.c i j) (sumUp fun k => absolute (Z.G k i j)))
      (Z.E.inf i j)) ≤ _
    linarith [he'.1]
  · have h1 := add_le_addUp (addUp (Z.c i j) (sumUp fun k => absolute (Z.G k i j)))
      (Z.E.sup i j)
    have h2 := add_le_addUp (Z.c i j) (sumUp fun k => absolute (Z.G k i j))
    show _ ≤ toReal (addUp (addUp (Z.c i j) (sumUp fun k => absolute (Z.G k i j)))
      (Z.E.sup i j))
    linarith [he'.2]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
