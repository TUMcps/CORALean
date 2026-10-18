module

public import CORALean.Global.CoeffNorm
public import Mathlib.Topology.Order.OrderClosed
public import Mathlib.Tactic.Module

@[expose] public section

/-!
# The ellipsotope norm and its unit ball

`[1, Prop. 2.2]`: for a full-rank `G`, `x ↦ min_{G α = x} ‖α‖_p` is a norm whose unit ball
is the ellipsotope `E_p(G)`. Stated at any norm on the coefficients, `p`-norms among them:
`coeffNorm`'s norm laws at a surjective map, the unit ball as the image of the coefficient
ball, and its boundary as the unit sphere — the printed "unit circle coincides with
`E_p(G)`" is the ball (`coeffNorm_ball_eq_counterexample`). At the supremum norm this is
the zonotope's `Cor. 1` of Kulmburg and Althoff.

[2, Prop. 7] is the same statement.

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

variable {E W : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]


-- =======================================  MAIN THEOREM  ======================================= --

theorem coeffNorm_ball_eq (G : E →ₗ[ℝ] W) (hG : Function.Surjective G) : -- --- STMT ---
    ((∀ x y, coeffNorm G (x + y) ≤ coeffNorm G x + coeffNorm G y) ∧
      (∀ (a : ℝ) x, coeffNorm G (a • x) = |a| * coeffNorm G x) ∧
      ∀ x, coeffNorm G x = 0 ↔ x = 0) ∧
    {x | coeffNorm G x ≤ 1} = G '' Metric.closedBall 0 1 ∧
    {x | coeffNorm G x = 1} = frontier (G '' Metric.closedBall 0 1) := by -- --- PROOF ---
  have hball : {x | coeffNorm G x ≤ 1} = G '' Metric.closedBall 0 1 := by
    ext x
    simp only [Set.mem_setOf_eq, coeffNorm_le_iff G (hG x), Set.mem_image,
      Metric.mem_closedBall, dist_zero_right]
    exact ⟨fun ⟨α, h, hn⟩ => ⟨α, hn, h⟩, fun ⟨α, hn, h⟩ => ⟨α, h, hn⟩⟩
  refine ⟨⟨fun x y => coeffNorm_add_le G (hG x) (hG y), fun a x => coeffNorm_smul G (hG x) a,
    fun x => coeffNorm_eq_zero_iff G (hG x)⟩, hball, ?_⟩
  obtain ⟨K, hK⟩ := exists_lipschitzWith_coeffNorm G hG
  -- the interior is `{ν < 1}`: open, and a point with `ν = 1` is a limit of points outside
  have hint : interior (G '' Metric.closedBall 0 1) = {x | coeffNorm G x < 1} := by
    apply Set.Subset.antisymm
    · intro x hx
      have hle : coeffNorm G x ≤ 1 := by
        have := interior_subset hx
        rw [← hball] at this
        exact this
      refine lt_of_le_of_ne hle fun heq => ?_
      obtain ⟨ε, hε, hεx⟩ := Metric.isOpen_iff.mp isOpen_interior x hx
      have hne : x ≠ 0 := fun h0 => by rw [h0, coeffNorm_zero] at heq; norm_num at heq
      have hnpos : 0 < ‖x‖ := norm_pos_iff.mpr hne
      set δ := ε / (2 * ‖x‖) with hδ
      have hδ0 : 0 < δ := by positivity
      have hy : x + δ • x ∈ G '' Metric.closedBall 0 1 := by
        refine interior_subset (hεx ?_)
        rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
          abs_of_pos hδ0, hδ]
        have : ε / (2 * ‖x‖) * ‖x‖ = ε / 2 := by field_simp
        rw [this]
        linarith
      -- `ν (x + δ x) = 1 + δ > 1`
      rw [← hball] at hy
      have : coeffNorm G (x + δ • x) = 1 + δ := by
        rw [show x + δ • x = (1 + δ) • x by module, coeffNorm_smul G (hG x), heq,
          abs_of_pos (by linarith), mul_one]
      simp only [Set.mem_setOf_eq, this] at hy
      linarith
    · refine interior_maximal ?_ (isOpen_lt hK.continuous continuous_const)
      intro x hx
      rw [← hball]
      exact le_of_lt (Set.mem_setOf_eq ▸ hx)
  have hclosed : IsClosed (G '' Metric.closedBall 0 1) := by
    rw [← hball]; exact isClosed_le hK.continuous continuous_const
  rw [hclosed.frontier_eq, hint, ← hball]
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_sdiff, not_lt]
  exact ⟨fun h => ⟨h.le, h.ge⟩, fun ⟨h1, h2⟩ => le_antisymm h1 h2⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
