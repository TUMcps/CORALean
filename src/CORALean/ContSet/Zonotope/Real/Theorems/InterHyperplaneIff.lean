module

public import CORALean.ContSet.Zonotope.Real.Zonotope
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# When a zonotope meets a hyperplane

[1, Sec. 3]: a zonotope `Z = ⟨c; g₁, …, g_r⟩` meets the hyperplane `{x | x·n = γ}` iff
`c·n − ∑ |gᵢ·n| ≤ γ ≤ c·n + ∑ |gᵢ·n|`. A point's coordinate along `n` is `c·n + ∑ βᵢ (gᵢ·n)`
with `|βᵢ| ≤ 1`, which stays within the sum of the `|gᵢ·n|` of `c·n`; and every offset
`t = γ − c·n` of that size is reached by `βᵢ = (t/s) sign(gᵢ·n)`, `s = ∑ |gᵢ·n|`.

## Inputs
* `Z` – zonotope
* `nv` – hyperplane normal
* `γ` – hyperplane offset

## Hypotheses
* none

## Conclusion
* `Z` meets the hyperplane iff the offset is within the support range

## References

* [1] A. Girard and C. Le Guernic. "Zonotope/Hyperplane Intersection for Hybrid Systems
      Reachability Analysis". In Hybrid Systems: Computation and Control (HSCC), LNCS 4981,
      Springer, 2008, pp. 215-228.
-/

-- Authors:       Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      16-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Sec. 3]: `Z ∩ {x | x·n = γ} ≠ ∅` iff `γ` is within `∑ |gᵢ·n|` of `c·n`. -/
theorem Zonotope.inter_hyperplane_iff (Z : Zonotope (Vec ℝ n)) (nv : Vec ℝ n)
    (γ : ℝ) : -- --- CONCL ---
    (∃ x ∈ Z.construct, x ⬝ᵥ nv = γ) ↔
      Z.c ⬝ᵥ nv - ∑ i, |Z.G i ⬝ᵥ nv| ≤ γ ∧ γ ≤ Z.c ⬝ᵥ nv + ∑ i, |Z.G i ⬝ᵥ nv| := by -- --- PROOF ---
  constructor
  · rintro ⟨x, ⟨β, hβ, rfl⟩, rfl⟩
    -- the coordinate along `nv` is the center's plus a combination of the `gᵢ·nv`
    have hdot : (Z.c + ∑ j, β j • Z.G j) ⬝ᵥ nv = Z.c ⬝ᵥ nv + ∑ j, β j * (Z.G j ⬝ᵥ nv) := by
      rw [add_dotProduct, sum_dotProduct]
      simp only [smul_dotProduct, smul_eq_mul]
    rw [hdot]
    have habs : |∑ j, β j * (Z.G j ⬝ᵥ nv)| ≤ ∑ i, |Z.G i ⬝ᵥ nv| := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
      rw [abs_mul]
      exact mul_le_of_le_one_left (abs_nonneg _) (hβ j)
    constructor <;> linarith [abs_le.1 habs]
  · rintro ⟨hlo, hhi⟩
    set s := ∑ i, |Z.G i ⬝ᵥ nv| with hs
    set t := γ - Z.c ⬝ᵥ nv with ht
    have hts : |t| ≤ s := abs_le.2 ⟨by linarith, by linarith⟩
    by_cases h0 : s = 0
    · -- no generator moves the coordinate: the center is the point
      refine ⟨Z.c, ⟨fun _ => 0, fun _ => by simp, by simp⟩, ?_⟩
      have : t = 0 := by rw [h0] at hts; exact abs_nonpos_iff.1 hts
      linarith
    · -- coefficients `(t/s)` times the sign of each `gᵢ·nv`
      have hspos : 0 < s :=
        lt_of_le_of_ne (Finset.sum_nonneg fun i _ => abs_nonneg _) (Ne.symm h0)
      refine ⟨Z.c + ∑ j, ((t / s) * (if 0 ≤ Z.G j ⬝ᵥ nv then (1:ℝ) else -1)) • Z.G j,
        ⟨fun j => (t / s) * (if 0 ≤ Z.G j ⬝ᵥ nv then (1:ℝ) else -1), fun j => ?_, rfl⟩, ?_⟩
      · -- `|t/s| ≤ 1` and `|sign| ≤ 1`
        have h1 : |t / s| ≤ 1 := by
          rw [abs_div, abs_of_pos hspos]; exact (div_le_one hspos).2 hts
        rw [abs_mul]
        exact mul_le_one₀ h1 (abs_nonneg _) (by split_ifs <;> simp)
      · -- and they move the coordinate by exactly `t`
        have hdot : (Z.c + ∑ j, ((t / s) * (if 0 ≤ Z.G j ⬝ᵥ nv then (1:ℝ) else -1)) • Z.G j)
              ⬝ᵥ nv = Z.c ⬝ᵥ nv + ∑ j, ((t / s) * (if 0 ≤ Z.G j ⬝ᵥ nv then (1:ℝ) else -1))
                * (Z.G j ⬝ᵥ nv) := by
          rw [add_dotProduct, sum_dotProduct]
          simp only [smul_dotProduct, smul_eq_mul]
        rw [hdot]
        have : ∑ j, ((t / s) * (if 0 ≤ Z.G j ⬝ᵥ nv then (1:ℝ) else -1)) * (Z.G j ⬝ᵥ nv) = t := by
          have : ∀ j, ((t / s) * (if 0 ≤ Z.G j ⬝ᵥ nv then (1:ℝ) else -1)) * (Z.G j ⬝ᵥ nv)
              = (t / s) * |Z.G j ⬝ᵥ nv| := fun j => by
            rw [mul_assoc, mul_comm (if 0 ≤ Z.G j ⬝ᵥ nv then (1:ℝ) else -1)]
            split_ifs with hj
            · rw [mul_one, abs_of_nonneg hj]
            · rw [mul_neg_one, abs_of_neg (not_le.1 hj)]
          simp_rw [this]
          rw [← Finset.mul_sum, ← hs]
          field_simp
        rw [this, ht]
        ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
