import CORALean.ContSet.ContSet.ContSet
import CORALean.ContSet.Zonotope.Real.Operations.MinkDiffStretch

/-!
# `Zonotope.minkDiffStretch` over-approximates the Minkowski difference

[1, Thm. 5]. Same operation as `minkDiffStretch_inner`, opposite direction and
a different `µ`: `hμ` is the printed constraint `-Âµ ≤ -b̃`, so the stretched
minuend is pushed *out* until it covers the difference rather than in until it
is covered.

`b` is [1]'s `b̃`, and is a parameter rather than (18)'s optimum, with the only
property that proof uses asked of it: that it bounds the exact difference in
each direction. `minkowskiDiff_apply_le` proves `Δd - Δd_trans` is one such
`b`, the most conservative admissible value — (18) only lowers it, and lowering
it weakens `hμ`, which is the whole point of that linear program.

`hCd` is the standing premise, as in `minkDiffStretch_inner` but read at the
*stretched* minuend: (12b) is an equivalence only when `C` describes the set,
and [1] notes in so many words that the over-approximation may not drop a
halfspace where the under-approximation may. `hRep_lin_subset` discharges it at
[1, Thm. 2]'s own normals, whose positive rescaling by `µ` that lemma allows.

## References

* [1] M. Althoff. "On Computing the Minkowski Difference of Zonotopes".
      arXiv, 2015.
-/

-- Authors:       Tobias Ladner
-- Written:       18-September-2026
-- Last update:   21-September-2026
-- Last revision: ---


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
            ⊆ (Z₁.minkDiffStretch Z₂ μ).construct) :
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
