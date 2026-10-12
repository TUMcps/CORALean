import CORALean.ContSet.Zonotope.Real.Operations.UnderS
import Mathlib.Algebra.Module.BigOperators

/-!
# The under-approximation lies inside the zonotope

[1, Sec. 5.1]: `Z̲ ⊆ Z`, what makes `Z̲` an under-approximation. A point `u + Σᵢ αᵢgᵢ`,
`gᵢ = Σₖ sign(sᵢ·vₖ)vₖ`, is `u + Σₖ βₖvₖ` with `βₖ = Σᵢ αᵢ sign(sᵢ·vₖ)`, and
`|βₖ| ≤ Σᵢ |αᵢ| ≤ 1`.

## References

* [1] A. Girard, C. Le Guernic and O. Maler. "Efficient Computation of Reachable Sets of
      Linear Time-Invariant Systems with Inputs". In Hybrid Systems: Computation and
      Control (HSCC), LNCS 3927, Springer, 2006, pp. 257-271.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real

open Matrix

variable {n ℓ : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Sec. 5.1]: `Z̲ ⊆ Z`. -/
theorem Zonotope.underS_subset (Z : Zonotope (Vec ℝ n)) (s : Fin ℓ → Vec ℝ n) :
    Z.underS s ⊆ Z.construct := by -- --- PROOF ---
  -- a sign is at most one in absolute value
  have hsg : ∀ r : ℝ, |Real.sign r| ≤ 1 := fun r => by
    rcases Real.sign_apply_eq r with h | h | h <;> simp [h]
  -- generator `k` gets the coefficient `Σᵢ αᵢ sign(sᵢ·vₖ)`, at most `Σᵢ |αᵢ|`
  rintro x ⟨α, hα, rfl⟩
  refine ⟨fun k => ∑ i, α i * Real.sign (s i ⬝ᵥ Z.G k), fun k => ?_, ?_⟩
  · refine (Finset.abs_sum_le_sum_abs _ _).trans (le_trans ?_ hα)
    refine Finset.sum_le_sum fun i _ => ?_
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (hsg _)
  · simp only [Zonotope.extremalGen, Finset.smul_sum, smul_smul, Finset.sum_smul]
    rw [Finset.sum_comm]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
