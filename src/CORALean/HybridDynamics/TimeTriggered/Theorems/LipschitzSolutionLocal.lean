import Mathlib.Analysis.ODE.ExistUnique

/-!
# A Lipschitz field has a solution on a fixed window around any point

[1, Def. 2] makes every flow Lipschitz. For `f` globally `K`-Lipschitz, a solution of
`ẋ = f(x)` through any point exists on `(-h, h)` with `h = 1 / (2K + 2)` independent of the point:
Picard-Lindelöf on the ball of radius `2h‖f y‖ + 1` about `y`, where `f` is bounded by
`‖f y‖ + K · radius`. The windows are glued in `lipschitzSolution`.

## References

* [1] S. Bak, S. Bogomolov and M. Althoff. "Time-Triggered Conversion of Guards for
      Reachability Analysis of Hybrid Automata". In Formal Modeling and Analysis of Timed
      Systems (FORMATS), LNCS 10419, pp. 133-150, 2017.
-/

-- Authors:       Tobias Ladner
-- Written:       11-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Set Metric
open scoped NNReal

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]


-- =======================================  MAIN THEOREM  ======================================= --

/-- A solution of `ẋ = f(x)` through `y` on `(-h, h)`, `h = 1 / (2K + 2)`, [1, Def. 2]. -/
theorem lipschitzSolutionLocal {f : E → E} {K : ℝ≥0} (hf : LipschitzWith K f) (y : E) :
    ∃ α : ℝ → E, α 0 = y ∧ ∀ u ∈ Ioo (-(1 / (2 * (K : ℝ) + 2))) (1 / (2 * (K : ℝ) + 2)),
      HasDerivAt α (f (α u)) u := by -- --- PROOF ---
  -- the window `h`, the ball radius `R` and the bound `L` on the ball
  set h : ℝ := 1 / (2 * (K : ℝ) + 2) with hh
  have hK : (0 : ℝ) ≤ K := K.2
  have hhpos : 0 < h := by positivity
  have hKh : (K : ℝ) * h ≤ 1 / 2 := by
    rw [hh, mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  set R : ℝ := 2 * h * ‖f y‖ + 1 with hR
  have hRpos : 0 < R := by positivity
  set L : ℝ := ‖f y‖ + K * R with hL
  have hmem : (0 : ℝ) ∈ Icc (-h) h := ⟨by linarith, hhpos.le⟩
  have hLnn : 0 ≤ L := by positivity
  have hpl : IsPicardLindelof (fun (_ : ℝ) => f) (⟨0, hmem⟩ : Icc (-h) h) y
      ⟨R, hRpos.le⟩ 0 ⟨L, hLnn⟩ K := by
    refine ⟨fun _ _ => hf.lipschitzOnWith, fun _ _ => continuousOn_const, ?_, ?_⟩
    · intro _ _ x hx
      -- on the ball `f` is within `K R` of `f y`
      have h1 : ‖f x - f y‖ ≤ K * R := by
        have := hf.dist_le_mul x y
        rw [dist_eq_norm, dist_eq_norm] at this
        have hd : ‖x - y‖ ≤ R := by
          have := mem_closedBall.1 hx
          rwa [dist_eq_norm] at this
        calc ‖f x - f y‖ ≤ K * ‖x - y‖ := this
          _ ≤ K * R := mul_le_mul_of_nonneg_left hd hK
      calc ‖f x‖ = ‖(f x - f y) + f y‖ := by rw [sub_add_cancel]
        _ ≤ ‖f x - f y‖ + ‖f y‖ := norm_add_le _ _
        _ ≤ L := by simp only [hL]; linarith
    · -- the time window times the bound fits in the radius, as `K h ≤ 1/2`
      show (L : ℝ) * max (h - 0) (0 - -h) ≤ R - 0
      have hmax : max (h - 0) (0 - -h) = h := by simp
      rw [hmax]
      have : L * h = h * ‖f y‖ + K * h * R := by simp only [hL]; ring
      have h2 : K * h * R ≤ 1 / 2 * R := mul_le_mul_of_nonneg_right hKh hRpos.le
      nlinarith [norm_nonneg (f y)]
  -- Picard-Lindelöf gives the solution on `[-h, h]`, two-sided inside
  obtain ⟨α, hα0, hα⟩ := hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  refine ⟨α, hα0, fun u hu => ?_⟩
  exact (hα u ⟨hu.1.le, hu.2.le⟩).hasDerivAt (Icc_mem_nhds hu.1 hu.2)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
