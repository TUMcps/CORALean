module

public import CORALean.ContSet.Zonotope.Real.Operations.AndAveraging
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# The averaged zonotope encloses the intersection

[1, Thm. 1]: a point `x̄` in every `Z̄ʲ` has coefficients `zʲ ∈ [-1, 1]` with `x̄ = c̄ʲ + Ḡʲ zʲ`
Eq. 16 of [1, Thm. 1]; multiplying by `wʲ` and summing gives `x̄ = ć + Ǵ z` Eq. 17 of
[1, Thm. 1], `z` the stacked `zʲ`, still in `[-1, 1]`. Holds for every weight vector of nonzero
sum, negative entries included, as the coefficient `zʲ` rides on the generator `(wʲ / s) Ḡʲ`.
Outer only: the averaged zonotope holds more than the intersection.

## Inputs
* `Z` – family of zonotopes
* `w` – weights

## Hypotheses
* `hw` – weights sum to nonzero

## Conclusion
* the intersection lies in the averaged zonotope

## References

* [1] A. Alanwar, J. J. Rath, H. Said, K. H. Johansson and M. Althoff. "Distributed Set-Based
      Observers Using Diffusion Strategies". Journal of the Franklin Institute, 2023.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      14-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n N : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.andAveraging_outer (Z : Fin N → Zonotope (Vec ℝ n)) (w : Fin N → ℝ)
    (hw : ∑ j, w j ≠ 0) : -- --- CONCL ---
    (⋂ j, (Z j).construct) ⊆ (Zonotope.andAveraging Z w).construct := by -- --- PROOF ---
  intro x hx
  rw [Set.mem_iInter] at hx
  -- Eq. 16: the coefficients `zʲ` of `x` in each zonotope
  choose z hz hxz using hx
  set s : ℝ := ∑ j, w j with hs
  -- the stacked coefficients: `Fin (Σⱼ hⱼ)` is the sigma type of the blocks' index sets
  let e : Fin (∑ j, (Z j).h) ≃ (Σ j, Fin (Z j).h) :=
    (finSigmaFinEquiv (n := fun j => (Z j).h)).symm
  refine ⟨fun k => z (e k).1 (e k).2, fun k => hz _ _, ?_⟩
  -- Eq. 17: weight Eq. 16 by `wʲ`, sum over the zonotopes, and divide by `s`
  have key : ∀ j, w j • x = w j • (Z j).c + ∑ i, (w j * z j i) • (Z j).G i := by
    intro j
    conv_lhs => rw [hxz j]
    rw [smul_add, Finset.smul_sum]
    simp only [smul_smul]
  have main : x = s⁻¹ • ∑ j, w j • (Z j).c + ∑ k : Fin (∑ j, (Z j).h),
      z (e k).1 (e k).2 • ((s⁻¹ * w (e k).1) • (Z (e k).1).G (e k).2) := by
    -- the sum over `Fin` is the sum over the sigma type, then over each block
    rw [Equiv.sum_comp e (fun p => z p.1 p.2 • ((s⁻¹ * w p.1) • (Z p.1).G p.2)),
      Fintype.sum_sigma]
    calc x = s⁻¹ • ∑ j, w j • x := by
          rw [← Finset.sum_smul, ← hs, smul_smul, inv_mul_cancel₀ hw, one_smul]
      _ = _ := by
          simp only [key, Finset.sum_add_distrib, smul_add, Finset.smul_sum, smul_smul]
          congr 1
          refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
          congr 1
          ring
  exact main

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
