import CORALean.ContSet.Zonotope.Real.Operations.Aligned
import Mathlib.Data.Matrix.Basic

/-!
# A feasible point of (max-in) gives an aligned zonotope inside the halfspaces

[1, Prop. 2], corrected: for `α ≥ 0`, `Hc + |HG|α ≤ h` puts `([α₁g₁, …, α_N g_N], c)`
inside `{x | Hx ≤ h}`, each row's maximum over the zonotope being `H_ℓc + |H_ℓG|α`,
(8)-(9). That the point is the *maximizer* is not used.

[1] takes `(H, h)` to be the H-representation of the disturbance set `W` and concludes
the zonotope is inside `EW`. That holds only when `(H, h)` describes `EW` itself;
with `W`'s own description it is false (`aligned_subset_of_maxIn_counterexample`, and
the paper's page). Stated here for any `(H, h)`, so `EW`'s description gives `⊆ EW`.

## References

* [1] L. Yang and N. Ozay. "Scalable zonotopic under-approximation of backward
      reachable sets for uncertain linear systems". IEEE Control Systems Letters,
      6:1555-1560, 2022.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n L : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Prop. 2], for the description `(H, h)` of the set to be inner-approximated: a
feasible point of (max-in) puts the aligned zonotope inside `{x | Hx ≤ h}`. -/
theorem Zonotope.aligned_subset_of_maxIn (Z : Zonotope (Vec ℝ n)) (H : Mat ℝ L n)
    (h : Vec ℝ L) (c : Vec ℝ n) (a : Fin Z.h → ℝ) (ha : ∀ i, 0 ≤ a i)
    (hfeas : ∀ l, (H *ᵥ c) l + ∑ i, |(H *ᵥ Z.G i) l| * a i ≤ h l) :
    (Z.aligned c a).construct ⊆ {x | ∀ l, (H *ᵥ x) l ≤ h l} := by -- --- PROOF ---
  rintro _ ⟨β, hβ, rfl⟩ l
  -- `H_ℓ(c + Σ βᵢαᵢgᵢ) = H_ℓc + Σ βᵢαᵢ H_ℓgᵢ`, and each term is at most `|H_ℓgᵢ| αᵢ`
  have hlin : (H *ᵥ ((Z.aligned c a).c + ∑ i, β i • (Z.aligned c a).G i)) l
      = (H *ᵥ c) l + ∑ i, β i * a i * (H *ᵥ Z.G i) l := by
    simp only [Zonotope.aligned, smul_smul, Matrix.mulVec_add, Pi.add_apply,
      Matrix.mulVec_sum, Matrix.mulVec_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hlin]
  refine le_trans (add_le_add le_rfl (Finset.sum_le_sum fun i _ => ?_)) (hfeas l)
  calc β i * a i * (H *ᵥ Z.G i) l ≤ |β i * a i * (H *ᵥ Z.G i) l| := le_abs_self _
    _ = |β i| * a i * |(H *ᵥ Z.G i) l| := by rw [abs_mul, abs_mul, abs_of_nonneg (ha i)]
    _ ≤ 1 * a i * |(H *ᵥ Z.G i) l| := by gcongr; exacts [ha i, hβ i]
    _ = |(H *ᵥ Z.G i) l| * a i := by ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
