import CORALean.ContSet.Zonotope.Real.Operations.ScalarIntervalMul
import CORALean.ContSet.Zonotope.Real.Theorems.MtimesExact
import CORALean.ContSet.Zonotope.Real.Theorems.PlusExact
import CORALean.ContSet.Zonotope.Real.Theorems.UnitIntervalMulOuter

/-!
# `[a, b] ⊗ Z` encloses every product

For `a ≤ b`, `s ∈ [a, b]` and `z ∈ Z`: `s z = c z + σ (g z)` with `σ = (s - c)/g ∈ [-1, 1]`
(`σ = 0` at `g = 0`), the second summand in `[-1, 1] ⊗ (g Z)` [1, Eq. 11]. Outer only: the
products `σ βⱼ` of the coefficients are taken as free ones.

## References

* [1] M. Althoff and B. H. Krogh. "Avoiding Geometric Intersection Operations in
      Reachability Analysis of Hybrid Systems". In Proc. of the 15th ACM
      International Conference on Hybrid Systems: Computation and Control (HSCC),
      2012, pp. 45-54.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.scalarIntervalMul_outer (a b : ℝ) (Z : Zonotope (Vec ℝ n)) {s : ℝ}
    (hs : s ∈ Set.Icc a b) {z : Vec ℝ n} (hz : z ∈ Z.construct) :
    s • z ∈ (Zonotope.scalarIntervalMul a b Z).construct := by -- --- PROOF ---
  -- the centre's part `c z`
  have hmid : ((a + b) / 2) • z
      ∈ (Zonotope.mtimes (((a + b) / 2) • (1 : Mat ℝ n n)) Z).construct := by
    rw [← Zonotope.mtimes_exact]
    exact ⟨z, hz, by simp [Matrix.smul_mulVec]⟩
  -- the position of `s` in `[a, b]`, as `σ ∈ [-1, 1]`
  have hab : a ≤ b := le_trans hs.1 hs.2
  obtain ⟨σ, hσ, hsσ⟩ : ∃ σ : ℝ, σ ∈ Set.Icc (-1 : ℝ) 1 ∧ s = (a + b) / 2 + σ * ((b - a) / 2) := by
    by_cases hg : b - a = 0
    · exact ⟨0, ⟨by norm_num, by norm_num⟩, by
        have : s = a := le_antisymm (by linarith [hs.2]) hs.1
        rw [this]; linarith⟩
    · have hpos : 0 < b - a := lt_of_le_of_ne (by linarith) (Ne.symm hg)
      have hg2 : 0 < (b - a) / 2 := by linarith
      refine ⟨(s - (a + b) / 2) / ((b - a) / 2), ⟨?_, ?_⟩, ?_⟩
      · rw [le_div_iff₀ hg2]; linarith [hs.1]
      · rw [div_le_iff₀ hg2]; linarith [hs.2]
      · rw [div_mul_cancel₀ _ hg2.ne']; ring
  -- the radius' part `σ (g z)` lies in `[-1, 1] ⊗ (g Z)`
  have hrad : σ • (((b - a) / 2) • z)
      ∈ (Zonotope.mtimes (((b - a) / 2) • (1 : Mat ℝ n n)) Z).unitIntervalMul.construct := by
    refine Zonotope.unitIntervalMul_outer _ ⟨(σ, ((b - a) / 2) • z), ⟨hσ, ?_⟩, rfl⟩
    rw [← Zonotope.mtimes_exact]
    exact ⟨z, hz, by simp [Matrix.smul_mulVec]⟩
  -- the sum of the two
  have hkey : s • z = ((a + b) / 2) • z + σ • (((b - a) / 2) • z) := by
    rw [hsσ, add_smul, smul_smul, mul_comm σ]
  rw [Zonotope.scalarIntervalMul, ← Zonotope.plus_exact, hkey]
  exact Set.add_mem_add hmid hrad

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
