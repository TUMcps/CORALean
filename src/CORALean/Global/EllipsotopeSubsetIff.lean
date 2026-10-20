module

public import CORALean.Global.CoeffNormBallEq

@[expose] public section

/-!
# Ellipsotope containment as a maximum

`[1, Eq. 6]`: `E_p(G, c) ⊆ E_q(H, d)` iff `r ≤ 1`, where `r = max_{‖α‖_p ≤ 1} ‖G α + c -
d‖_{E_q(H)}`, for a full-rank `H`. The maximum is attained (continuous norm, compact coefficient
ball), and the containment is the norm bound pointwise, `E_q(H, d)` being `{x | ‖x - d‖_{E_q(H)} ≤
1}` (`coeffNorm_ball_eq`). Any norms on either coefficient space. The containment half of
[2, Thm. 12] is the same statement at a non-degenerate circumbody (`H` onto). Not proved: that `r`
is the smallest scaling, nor the degenerate-circumbody convention.

## Inputs
* `G` – generator map of the inner ellipsotope
* `c` – center of the inner ellipsotope
* `H` – generator map of the outer ellipsotope
* `d` – center of the outer ellipsotope

## Hypotheses
* `hH` – the outer generator map is onto

## Conclusion
* the maximum norm exists and the containment holds exactly when it is at most one

## References

* [1] A. Kulmburg, I. Brkan and M. Althoff. "Search-based and Stochastic Solutions to the
      Zonotope and Ellipsotope Containment Problems". In Proc. of the European Control
      Conference (ECC), 2024. doi:10.23919/ECC64448.2024.10590884.
* [2] A. Kulmburg, L. Schäfer and M. Althoff. "Approximability of the Containment Problem for
      Zonotopes and Ellipsotopes". IEEE Transactions on Automatic Control, 2025.
      doi:10.1109/TAC.2025.3583624. arXiv:2404.11185.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {E₁ E₂ W : Type} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [FiniteDimensional ℝ E₂]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]


-- =======================================  MAIN THEOREM  ======================================= --

theorem ellipsotope_subset_iff (G : E₁ →ₗ[ℝ] W) (c : W) (H : E₂ →ₗ[ℝ] W)
    (hH : Function.Surjective H) (d : W) : -- --- CONCL ---
    ∃ r, IsGreatest ((fun α => coeffNorm H (G α + c - d)) '' Metric.closedBall 0 1) r ∧
      ({x | ∃ α : E₁, ‖α‖ ≤ 1 ∧ x = c + G α} ⊆ {x | ∃ β : E₂, ‖β‖ ≤ 1 ∧ x = d + H β} ↔
        r ≤ 1) := by -- --- PROOF ---
  obtain ⟨-, hball, -⟩ := coeffNorm_ball_eq H hH
  obtain ⟨K, hK⟩ := exists_lipschitzWith_coeffNorm H hH
  have hcont : Continuous fun α => coeffNorm H (G α + c - d) :=
    hK.continuous.comp (((LinearMap.continuous_of_finiteDimensional G).add
      continuous_const).sub continuous_const)
  obtain ⟨α₀, hα₀, hmax⟩ := (isCompact_closedBall (0 : E₁) 1).exists_isMaxOn
    ⟨0, Metric.mem_closedBall_self zero_le_one⟩ hcont.continuousOn
  refine ⟨_, ⟨⟨α₀, hα₀, rfl⟩, fun _ ⟨α, hα, he⟩ => he ▸ hmax hα⟩, ?_⟩
  -- a point lies in the circumbody iff its offset from `d` has norm at most `1`
  have hmem : ∀ x, (∃ β : E₂, ‖β‖ ≤ 1 ∧ x = d + H β) ↔ coeffNorm H (x - d) ≤ 1 := by
    intro x
    have := congrArg (fun S => x - d ∈ S) hball
    simp only [Set.mem_setOf_eq, Set.mem_image, Metric.mem_closedBall, dist_zero_right,
      eq_iff_iff] at this
    rw [this]
    exact ⟨fun ⟨β, hβ, he⟩ => ⟨β, hβ, by rw [he]; abel⟩,
      fun ⟨β, hβ, he⟩ => ⟨β, hβ, by rw [he]; abel⟩⟩
  constructor
  · intro h
    have := (hmem _).mp (h ⟨α₀, by simpa using hα₀, rfl⟩)
    simpa [add_comm] using this
  · rintro h _ ⟨α, hα, rfl⟩
    refine (hmem _).mpr ?_
    have := hmax (show α ∈ Metric.closedBall (0 : E₁) 1 by simpa using hα)
    simp only [Set.mem_setOf_eq] at this
    calc coeffNorm H (c + G α - d) = coeffNorm H (G α + c - d) := by rw [add_comm c]
      _ ≤ _ := this
      _ ≤ 1 := h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
