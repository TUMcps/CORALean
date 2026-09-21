import CORALean.ContSet.ContSet.ContSet
import CORALean.ContSet.Zonotope.Real.Operations.MinkDiffStretch

/-!
# `Zonotope.minkDiffStretch` under-approximates the Minkowski difference

[1, Thm. 4]. `hμ` is the printed linear program's *constraint* `Âμ ≤ b̂` — its
objective `ζᵀµ` chooses among the feasible `µ` and is not what the guarantee
rests on, so any feasible `µ` is admitted, `µ*` included.

`hCm` is the theorem's own standing premise, made explicit: its proof reads
(12) off [1, Thm. 2], which needs the directions `C` to *describe* the minuend
and not merely enclose it. The enclosing half is free and is proved inline;
the describing half is the one [1, Thm. 2] supplies and this tree does not, so
it is a hypothesis here rather than a silent assumption. Any exact halfspace
description discharges it — the cross-product normals of [1, Thm. 2] are one,
and the statement needs no facet enumeration to say so.

The direction is inner, as `MinkDiff` obliges: `minkDiffStretch_outer` is the
other one and is a different theorem about a different `µ`.

## References

* [1] M. Althoff. "On Computing the Minkowski Difference of Zonotopes".
      arXiv, 2015.
-/

-- Authors:       Tobias Ladner
-- Written:       18-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Thm. 4]: at a `µ` feasible for `Âµ ≤ Δd - Δd_trans`, the stretched
minuend stays inside the Minkowski difference. -/
theorem Zonotope.minkDiffStretch_inner {q : ℕ} (Z₁ Z₂ : Zonotope α)
    (C : Fin q → (α →ₗ[ℝ] ℝ)) (μ : Fin Z₁.h → ℝ) (hμ0 : ∀ υ, 0 ≤ μ υ)
    (hCm : {y | ∀ i, C i (y - Z₁.c) ≤ ∑ υ, |C i (Z₁.G υ)|} ⊆ Z₁.construct)
    (hμ : ∀ i, ∑ υ, |C i (Z₁.G υ)| * μ υ
            ≤ (∑ υ, |C i (Z₁.G υ)|) - ∑ υ, |C i (Z₂.G υ)|) :
    (Z₁.minkDiffStretch Z₂ μ).construct
      ⊆ minkowskiDiff Z₁.construct Z₂.construct := by -- --- PROOF ---
  intro x hx z hz
  dsimp only [Zonotope.minkDiffStretch] at hx
  obtain ⟨β, hβ, rfl⟩ := hx
  obtain ⟨a, ha, rfl⟩ := hz
  refine hCm fun i => ?_
  -- both operands' offsets from the minuend's centre, in one sum each
  have hexp : Z₁.c - Z₂.c + (∑ υ, β υ • μ υ • Z₁.G υ) + (Z₂.c + ∑ j, a j • Z₂.G j) - Z₁.c
      = (∑ υ, (β υ * μ υ) • Z₁.G υ) + ∑ j, a j • Z₂.G j := by
    rw [Finset.sum_congr rfl fun υ _ => smul_smul (β υ) (μ υ) (Z₁.G υ)]
    abel
  rw [hexp, map_add, map_sum, map_sum]
  simp only [map_smul, smul_eq_mul]
  have h1 : ∑ υ, β υ * μ υ * C i (Z₁.G υ) ≤ ∑ υ, |C i (Z₁.G υ)| * μ υ :=
    Finset.sum_le_sum fun υ _ => by
      calc β υ * μ υ * C i (Z₁.G υ) ≤ |β υ * μ υ * C i (Z₁.G υ)| := le_abs_self _
        _ = |β υ| * μ υ * |C i (Z₁.G υ)| := by
            rw [abs_mul, abs_mul, abs_of_nonneg (hμ0 υ)]
        _ ≤ 1 * μ υ * |C i (Z₁.G υ)| :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (hβ υ) (hμ0 υ)) (abs_nonneg _)
        _ = |C i (Z₁.G υ)| * μ υ := by ring
  -- and the subtrahend's own reach is `Δd_trans`, which `hμ` left room for
  have h2 : ∑ j, a j * C i (Z₂.G j) ≤ ∑ j, |C i (Z₂.G j)| :=
    Finset.sum_le_sum fun j _ => by
      calc a j * C i (Z₂.G j) ≤ |a j * C i (Z₂.G j)| := le_abs_self _
        _ = |a j| * |C i (Z₂.G j)| := abs_mul _ _
        _ ≤ 1 * |C i (Z₂.G j)| := mul_le_mul_of_nonneg_right (ha j) (abs_nonneg _)
        _ = |C i (Z₂.G j)| := one_mul _
  linarith [hμ i]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
