import CORALean.HybridDynamics.Definitions.HitSet
import Mathlib.Tactic.FieldSimp

/-!
# A guard hit within `E` of the state-dependent flow lies in `R_h(x₀)`

[1, Eq. 15], by eq. (1)'s derivation at the flow `Ax₀ + b`: by eq. (14) the state is
`x₀ + (Ax₀ + b)t + e` for some `e ∈ E`; on `nᵀx = d` that fixes
`t = (d - nᵀx₀ - nᵀe)/(nᵀ(Ax₀ + b))`, splitting the state into `y_h(x₀)` and
`(Ax₀ + b)(-nᵀe)/(nᵀ(Ax₀ + b)) + e`. `nᵀ(Ax₀ + b) ≠ 0` is the division the formula makes, the
paper's interval `I` of eq. (16) excluding `0`.

## References

* [1] M. Althoff and B. H. Krogh. "Avoiding Geometric Intersection Operations in
      Reachability Analysis of Hybrid Systems". In Proc. of the 15th ACM
      International Conference on Hybrid Systems: Computation and Control (HSCC),
      2012, pp. 45-54.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Pointwise

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Eq. 15]: a state `x₀ + (Ax₀ + b)t + e` on `nᵀx = d`, `e ∈ E`, lies in `R_h(x₀)`. -/
theorem GuardMap.mem_hitSet {A : Mat ℝ n n} {b nv x₀ e : Vec ℝ n} {d t : ℝ}
    {E : Set (Vec ℝ n)} (hf : nv ⬝ᵥ (A *ᵥ x₀ + b) ≠ 0) (he : e ∈ E)
    (hhit : nv ⬝ᵥ (x₀ + t • (A *ᵥ x₀ + b) + e) = d) :
    x₀ + t • (A *ᵥ x₀ + b) + e ∈ GuardMap.hitSet A b nv d E x₀ := by -- --- PROOF ---
  -- the hitting time, read off the hyperplane
  have ht : t = (d - nv ⬝ᵥ x₀ - nv ⬝ᵥ e) / (nv ⬝ᵥ (A *ᵥ x₀ + b)) := by
    rw [eq_div_iff hf, ← hhit]
    simp only [dotProduct_add, dotProduct_smul, smul_eq_mul]
    ring
  simp only [GuardMap.hitSet]
  refine ⟨_, rfl, _, ⟨_, ⟨e, he, rfl⟩, e, he, rfl⟩, ?_⟩
  ext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [ht]
  field_simp
  ring

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
