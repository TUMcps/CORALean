module

public import CORALean.ContSet.ContSet.ContSet
public import CORALean.ContSet.Zonotope.Real.Operations.MinkDiffAligned
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

@[expose] public section

/-!
# `Zonotope.minkDiffAligned` needs its scaling in `[0, 1]`

[1, Prop. 5] reads the closed form off an alignment `γᵢ g⁽ᵐ'ⁱ⁾ = g⁽ˢ'ⁱ⁾`, and
[1, Def. 3] lets `γᵢ` be any real. At every `γ` outside `[0, 1]` that printed
statement is false: it is not the difference, and not even an inner
approximation of it, so no reading of "exactly" rescues it.

One generator in `ℝ` is enough. `Z₁ = (0, 1)` is `[-1, 1]`, `Z₂ = (0, γ)` is
`[-|γ|, |γ|]`, and the closed form `(0, 1 - γ)` holds the point `1 - γ`. Taking
`-γ ∈ Z₂` out of it leaves `1 - 2γ`, which is outside `[-1, 1]` exactly when `γ`
is outside `[0, 1]`. At `γ > 1` the difference is empty while the closed form is
not; at `γ < 0` the subtrahend is the same set as at `-γ` but the closed form
grows the generator instead of shortening it.

`minkDiffAligned_inner` and `minkDiffAligned_exact` therefore carry `0 ≤ μᵢ` and
`μᵢ ≤ 1`, one bound for each failure above.

## References

* [1] M. Althoff. "On Computing the Minkowski Difference of Zonotopes".
      arXiv, 2015.
-/

-- Authors:       Claude Opus 5
-- Written:       13-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- Outside `0 ≤ γ ≤ 1` the closed form of [1, Prop. 5] is not an inner
approximation of the difference, let alone equal to it. -/
theorem Zonotope.minkDiffAligned_not_inner (γ : ℝ) (hγ : γ < 0 ∨ 1 < γ) :
    ∃ (Z₁ Z₂ : Zonotope ℝ) (hh : Z₁.h = Z₂.h),
      (∀ i, Z₂.G (Fin.cast hh i) = γ • Z₁.G i) ∧
        ¬ (Z₁.minkDiffAligned Z₂ hh).construct
            ⊆ minkowskiDiff Z₁.construct Z₂.construct := by -- --- PROOF ---
  refine ⟨⟨1, 0, fun _ => 1⟩, ⟨1, 0, fun _ => γ⟩, rfl, fun i => by simp, ?_⟩
  intro hsub
  -- the closed form `(0, 1 - γ)` reaches `1 - γ`, at coefficient `1`
  have hp : (1 - γ) ∈ (Zonotope.minkDiffAligned (⟨1, 0, fun _ => 1⟩ : Zonotope ℝ)
      ⟨1, 0, fun _ => γ⟩ rfl).construct := by
    refine ⟨fun _ => 1, fun j => by norm_num, ?_⟩
    simp [Zonotope.minkDiffAligned]
  have hy : (-γ) ∈ (⟨1, 0, fun _ => γ⟩ : Zonotope ℝ).construct := by
    refine ⟨fun _ => -1, fun j => by norm_num, ?_⟩
    simp
  -- but `1 - γ + (-γ)` is outside `[-1, 1]` at either sign of the violation
  obtain ⟨β, hβ, hx⟩ := hsub hp (-γ) hy
  rw [Fin.sum_univ_one] at hx
  simp only [smul_eq_mul, mul_one, zero_add] at hx
  have hb := abs_le.mp (hβ 0)
  rcases hγ with h | h <;> [linarith [hb.2]; linarith [hb.1]]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
