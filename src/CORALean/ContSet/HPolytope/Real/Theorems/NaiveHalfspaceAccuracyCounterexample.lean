import CORALean.ContSet.HPolytope.Real.Definitions.NaiveHalfspaceValue
import CORALean.ContSet.HPolytope.Real.Theorems.PolyNormLeIff
import CORALean.Global.ShenmaierHalfspace
import CORALean.Global.Tensor

/-!
# `[1, Cor. 4.8]`'s accuracy fails at a fixed `ε` too

The printed `r_hs` uses `Eq. 11`'s value `‖G'ᵀλ‖_{p*}/|b|`, below the radius `r(Ê, Ẑ)`
(`HPolytope.naiveHalfspaceValue_le`), and not by a factor a sampling probability can make up.
In `ℝ¹` with `p = 2`, `Ê = E₂(1, 1) = [0, 2]` and `Ẑ = [-1, 1]` (facets `±x ≤ 1`, `d = 0`) the
radius is `2` and the sampled facet `x ≤ 1` gives `r_hs ≤ ‖(1, 1)‖₂ = √2`: at `ε = 1/10` every
sample reaches `(1 - ε) r = 9/5` with probability `0`, while `P_S(1/10) > 0`. So the statement
"`r_hs ≥ (1 - ε) r` with probability at least `P_S(ε)`" fails, whatever the sampling.

## References

* [1] A. Kulmburg, I. Brkan and M. Althoff. "Search-based and Stochastic Solutions to the
      Zonotope and Ellipsotope Containment Problems". In Proc. of the European Control
      Conference (ECC), 2024. doi:10.23919/ECC64448.2024.10590884.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix ENNReal


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.naiveHalfspace_accuracy_counterexample :
    ∃ (G : Vec ℝ 1 →ₗ[ℝ] Vec ℝ 1) (c d : Vec ℝ 1) (Λ : Mat ℝ 2 1) (b : Vec ℝ 2)
      (j : Fin 1 → Fin 2) (ε : ℝ), 0 < ε ∧ ε ≤ 1 ∧ 0 < shenmaierProb 1 1 0 ε ∧
      ∀ r, IsGreatest ((fun α => HPolytope.polyNorm Λ b (G α + c - d)) '' Metric.closedBall 0 1) r →
        HPolytope.naiveHalfspaceValue 2 G c d Λ b Nat.one_pos j < (1 - ε) * r := by -- --- PROOF ---
  let G : Vec ℝ 1 →ₗ[ℝ] Vec ℝ 1 := LinearMap.id
  let c : Vec ℝ 1 := ![1]
  let Λ : Mat ℝ 2 1 := !![1; -1]
  let b : Vec ℝ 2 := fun _ => 1
  -- the sampled row `(1, 1)` has norm at most `√2` by Cauchy-Schwarz
  have hrow : ‖HPolytope.extendedRow 2 G c 0 Λ 0‖ ≤ Real.sqrt 2 := by
    refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg 2) fun x => ?_
    have hx : HPolytope.extendedRow 2 G c 0 Λ 0 x = x.fst 0 + x.snd := by
      simp [HPolytope.extendedRow, Λ, G, c, mulVec, dotProduct]
    have hn : ‖x‖ = Real.sqrt (‖x.fst‖ ^ 2 + ‖x.snd‖ ^ 2) := by
      rw [WithLp.prod_norm_eq_add (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
      simp [Real.sqrt_eq_rpow]
    have hfst : ‖x.fst‖ = |x.fst 0| := by
      simp [Pi.norm_def]
    rw [hx, Real.norm_eq_abs, hn, hfst, Real.norm_eq_abs]
    rw [← Real.sqrt_mul (by norm_num)]
    refine Real.abs_le_sqrt ?_
    nlinarith [sq_nonneg (x.fst 0 - x.snd), sq_abs (x.fst 0), sq_abs x.snd]
  -- the radius is at least `2`, attained at `α = 1`
  have hr2 : ∀ r, IsGreatest ((fun α => HPolytope.polyNorm Λ b (G α + c - 0)) ''
      Metric.closedBall 0 1) r → 2 ≤ r := fun r hr => by
    have hα : (![1] : Vec ℝ 1) ∈ Metric.closedBall (0 : Vec ℝ 1) 1 := by
      simp [Pi.norm_def]
    refine le_trans ?_ (hr.2 ⟨![1], hα, rfl⟩)
    have hx : G ![1] + c - 0 = ![2] := by
      ext i
      fin_cases i
      simp [G, c]
      norm_num
    show 2 ≤ HPolytope.polyNorm Λ b (G ![1] + c - 0)
    rw [hx]
    calc (2 : ℝ) = (Λ *ᵥ (![2] : Vec ℝ 1)) 0 / b 0 := by
          simp [Λ, b, mulVec, dotProduct]
      _ ≤ HPolytope.polyNorm Λ b ![2] := (HPolytope.polyNorm_le_iff.mp le_rfl).2 0
  -- the sampled value is below `9/5` while the radius is at least `2`
  refine ⟨G, c, 0, Λ, b, fun _ => 0, 1 / 10, by norm_num, by norm_num, ?_, fun r hr => ?_⟩
  · simp only [shenmaierProb, pow_one]
    norm_num
  · have h2 := hr2 r hr
    have hval : HPolytope.naiveHalfspaceValue 2 G c 0 Λ b Nat.one_pos (fun _ => 0)
        ≤ Real.sqrt 2 := by
      simp only [HPolytope.naiveHalfspaceValue, Finset.univ_unique, Finset.sup'_singleton]
      simpa [b] using hrow
    have hsq : Real.sqrt 2 < 9 / 5 := by
      rw [Real.sqrt_lt' (by norm_num)]; norm_num
    nlinarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
