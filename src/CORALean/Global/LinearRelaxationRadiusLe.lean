module

public import CORALean.Global.CoeffNorm
public import CORALean.Global.PiLpNormToLpLeOfAbsLe
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.ToLin

@[expose] public section

/-!
# The linear relaxation bounds the containment radius

[1, Thm. 15 (relaxation)]: for `H` surjective, `LR_q(G, H) = min_{HX = G} ‖X‖_{L⊤₁,q}` (Eq. 29) is
a minimum, attained, and bounds the radius from above, `r(Z(G), E_q(H)) ≤ LR_q(G, H)` (the first
inequality of Eq. 30). `‖X‖_{L⊤₁,q}` is the `q`-norm of the vector of `X`'s rows' absolute sums,
`HX = G` reads `G α = H (X α)` for every `α`, and `r` is the maximum over the cube of
`coeffNorm H`. The feasible set is closed and the norm bounds every entry, so the minimum is over
a compact piece; a minimizer `X` gives every `G α` the preimage `X α`. `LR_q ≤ 1` then gives
`Z(G) ⊆ E_q(H)`, which `zonotope_subset_ellipsotope_of_lr` proves from any feasible `X`.

## Inputs
* `q` – exponent of the coefficient norm
* `G` – zonotope generator map
* `H` – ellipsotope generator map

## Hypotheses
* `hH` – the ellipsotope generator map is onto

## Conclusion
* the relaxation value is attained and bounds every containment radius from above

## References

* [1] [A. Kulmburg, L. Schäfer and M. Althoff. "Approximability of the Containment Problem for
      Zonotopes and Ellipsotopes". IEEE Transactions on Automatic Control,
      2025.](../../../references/2025/kulmburg-tac-approximability-containment.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped ENNReal
open Matrix

variable {m l : ℕ} {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `‖X‖_{L⊤₁,q}` as a function of the entries. -/
private noncomputable def aux_lrNorm (q : ℝ≥0∞) (X : Fin l → Fin m → ℝ) : ℝ :=
  ‖WithLp.toLp q (fun i => ∑ j, |X i j|)‖

/-- It bounds the supremum norm of the entries. -/
private theorem aux_norm_le_lrNorm (q : ℝ≥0∞) [Fact (1 ≤ q)]
    (X : Fin l → Fin m → ℝ) : -- --- CONCL ---
    ‖X‖ ≤ aux_lrNorm q X := by -- --- PROOF ---
  have h0 : 0 ≤ aux_lrNorm q X := norm_nonneg _
  refine (pi_norm_le_iff_of_nonneg h0).mpr fun i => (pi_norm_le_iff_of_nonneg h0).mpr fun j => ?_
  have hrow : |X i j| ≤ ∑ j, |X i j| :=
    Finset.single_le_sum (f := fun j => |X i j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
  have happ := PiLp.norm_apply_le (WithLp.toLp q (fun i => ∑ j, |X i j|)) i
  simp only [Real.norm_eq_abs] at happ
  rw [Real.norm_eq_abs]
  exact hrow.trans ((le_abs_self _).trans happ)

private theorem aux_continuous_lrNorm (q : ℝ≥0∞) [Fact (1 ≤ q)] :
    Continuous (aux_lrNorm (l := l) (m := m) q) :=
  continuous_norm.comp ((PiLp.continuous_toLp q _).comp (continuous_pi fun i =>
    continuous_finsetSum _ fun j _ => ((continuous_apply j).comp (continuous_apply i)).abs))


-- =======================================  MAIN THEOREM  ======================================= --

theorem lr_isLeast_radius_le (q : ℝ≥0∞) [Fact (1 ≤ q)] (G : (Fin m → ℝ) →ₗ[ℝ] W)
    (H : PiLp q (fun _ : Fin l => ℝ) →ₗ[ℝ] W) (hH : Function.Surjective H) : -- --- CONCL ---
    ∃ LR, IsLeast {N | ∃ X : Matrix (Fin l) (Fin m) ℝ,
        (∀ α, G α = H (WithLp.toLp q (X *ᵥ α))) ∧ N = ‖WithLp.toLp q (fun i => ∑ j, |X i j|)‖}
        LR ∧
      ∀ r, IsGreatest ((fun α => coeffNorm H (G α)) '' Metric.closedBall 0 1) r →
        r ≤ LR := by -- --- PROOF ---
  -- the feasible set, over the entries
  set S := {X : Fin l → Fin m → ℝ | ∀ α, G α = H (WithLp.toLp q (Matrix.of X *ᵥ α))} with hS
  have hHc : Continuous H := LinearMap.continuous_of_finiteDimensional H
  have hmv : ∀ α, Continuous fun X : Fin l → Fin m → ℝ => Matrix.of X *ᵥ α := fun α =>
    continuous_pi fun i => by
      simp only [mulVec, dotProduct, Matrix.of_apply]
      fun_prop
  have hSc : IsClosed S := by
    rw [hS, Set.setOf_forall]
    exact isClosed_iInter fun α => isClosed_eq continuous_const
      (hHc.comp ((PiLp.continuous_toLp q _).comp (hmv α)))
  -- a feasible point: a right inverse of `H` after `G`, as a matrix
  obtain ⟨R, hR⟩ := LinearMap.exists_rightInverse_of_surjective H (LinearMap.range_eq_top.mpr hH)
  set M : (Fin m → ℝ) →ₗ[ℝ] (Fin l → ℝ) :=
    (WithLp.linearEquiv q ℝ (Fin l → ℝ)).toLinearMap ∘ₗ R ∘ₗ G
  have hX₀ : (LinearMap.toMatrix' M : Fin l → Fin m → ℝ) ∈ S := fun α => by
    show G α = H (WithLp.toLp q (LinearMap.toMatrix' M *ᵥ α))
    rw [LinearMap.toMatrix'_mulVec]
    have := congrArg (fun f => f (G α)) hR
    simpa [M] using this.symm
  -- a minimizer over the compact piece within `‖X‖ ≤ ‖X₀‖_{L⊤₁,q}`
  set X₀ : Fin l → Fin m → ℝ := LinearMap.toMatrix' M
  have hK : IsCompact (S ∩ Metric.closedBall 0 (aux_lrNorm q X₀)) :=
    (isCompact_closedBall 0 _).inter_left hSc
  obtain ⟨X, ⟨hXS, -⟩, hmin⟩ := hK.exists_isMinOn ⟨X₀, hX₀, by
    rw [Metric.mem_closedBall, dist_zero_right]; exact aux_norm_le_lrNorm q X₀⟩
    (aux_continuous_lrNorm q).continuousOn
  have hX₀mem : X₀ ∈ S ∩ Metric.closedBall 0 (aux_lrNorm q X₀) := ⟨hX₀, by
    rw [Metric.mem_closedBall, dist_zero_right]; exact aux_norm_le_lrNorm q X₀⟩
  have hall : ∀ Y ∈ S, aux_lrNorm q X ≤ aux_lrNorm q Y := fun Y hY => by
    by_cases hb : ‖Y‖ ≤ aux_lrNorm q X₀
    · exact hmin ⟨hY, by rwa [Metric.mem_closedBall, dist_zero_right]⟩
    · exact (hmin hX₀mem).trans ((le_of_not_ge hb).trans (aux_norm_le_lrNorm q Y))
  refine ⟨aux_lrNorm q X, ⟨⟨Matrix.of X, hXS, rfl⟩, ?_⟩, ?_⟩
  · rintro _ ⟨Y, hY, rfl⟩
    exact hall Y hY
  · -- the maximizer's point has the preimage `X α`, of `q`-norm at most `‖X‖_{L⊤₁,q}`
    intro r hr
    obtain ⟨α, hα, rfl⟩ := hr.1
    rw [Metric.mem_closedBall, dist_zero_right] at hα
    simp only
    rw [hXS α]
    refine (coeffNorm_le H _).trans (PiLp.norm_toLp_le_of_abs_le q _ _ fun i => ?_)
    rw [Matrix.mulVec, dotProduct]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) ((norm_le_pi_norm α j).trans hα)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
