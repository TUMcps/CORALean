module

public import CORALean.ContSet.ContSet.ContSet
public import CORALean.ContSet.Zonotope.Real.Operations.MinkDiffStretch

@[expose] public section

/-!
# `Zonotope.minkDiffStretch` over-approximates the Minkowski difference

[1, Thm. 5]. Same operation as `minkDiffStretch_inner`, opposite direction and a different `µ`:
`hμ` is the printed constraint `-Âµ ≤ -b̃`, so the stretched minuend is pushed *out* until it
covers the difference. `b` is [1]'s `b̃`, a parameter rather than (18)'s optimum, with the only
property the proof uses: that it bounds the exact difference in each direction.
`minkowskiDiff_apply_le` proves `Δd - Δd_trans` is one such `b`, the most conservative value.
`hCd` is the standing premise, as in `minkDiffStretch_inner` but read at the *stretched* minuend:
(12b) is an equivalence only when `C` describes the set, and the over-approximation may not drop a
halfspace where the under-approximation may; `hRep_lin_subset` discharges it at [1, Thm. 2]'s rows.

## Inputs
* `ι` – direction index type
* `Z₁` – minuend
* `Z₂` – subtrahend
* `C` – linear directions
* `μ` – stretch factors
* `b` – offset bounds

## Hypotheses
* `hμ0` – factors nonnegative
* `hb` – offsets bound the difference
* `hμ` – factors reach the offset bounds
* `hCd` – directions describe the stretched minuend

## Conclusion
* the Minkowski difference lies in the stretched minuend

## References

* [1] M. Althoff. "On Computing the Minkowski Difference of Zonotopes".
      arXiv, 2015.
-/

-- Authors:       Claude Opus 5
-- Written:       18-September-2026
-- Last update:   21-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Thm. 5]: at a `µ` feasible for `Âµ ≥ b̃`, the stretched minuend covers
the Minkowski difference. -/
theorem Zonotope.minkDiffStretch_outer {ι : Type} (Z₁ Z₂ : Zonotope α)
    (C : ι → (α →ₗ[ℝ] ℝ)) (μ : Fin Z₁.h → ℝ) (hμ0 : ∀ υ, 0 ≤ μ υ) (b : ι → ℝ)
    (hb : ∀ i, ∀ x ∈ minkowskiDiff Z₁.construct Z₂.construct, C i (x - (Z₁.c - Z₂.c)) ≤ b i)
    (hμ : ∀ i, b i ≤ ∑ υ, |C i (Z₁.G υ)| * μ υ)
    (hCd : {y | ∀ i, C i (y - (Z₁.minkDiffStretch Z₂ μ).c)
                ≤ ∑ υ, |C i ((Z₁.minkDiffStretch Z₂ μ).G υ)|}
            ⊆ (Z₁.minkDiffStretch Z₂ μ).construct) : -- --- CONCL ---
    minkowskiDiff Z₁.construct Z₂.construct
      ⊆ (Z₁.minkDiffStretch Z₂ μ).construct := by -- --- PROOF ---
  intro x hx
  refine hCd fun i => ?_
  -- the stretched minuend's own reach is `Âµ`, the factors being nonnegative
  have habs : ∑ υ, |C i ((Z₁.minkDiffStretch Z₂ μ).G υ)| = ∑ υ, |C i (Z₁.G υ)| * μ υ :=
    Finset.sum_congr rfl fun υ _ => by
      show |C i (μ υ • Z₁.G υ)| = _
      rw [map_smul, smul_eq_mul, abs_mul, abs_of_nonneg (hμ0 υ)]
      ring
  rw [habs]
  exact le_trans (hb i x hx) (hμ i)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
