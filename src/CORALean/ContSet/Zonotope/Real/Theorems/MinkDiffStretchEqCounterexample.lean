import CORALean.ContSet.ContSet.ContSet
import CORALean.ContSet.Zonotope.Real.Operations.MinkDiffStretch
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# `Zonotope.minkDiffStretch` needs a nonnegative `µ`

[1, Prop. 6] reads its closed form off (22), `|Ĉ⁺Ĝ⁽ᵐ⁾| µ = Δd̂ - Δd̂_trans`, and prints no sign
for `µ`. A zonotope generator may be negated without changing the set, so at a negative
solution of (22) the stretched minuend is not the difference. One generator in `ℝ` is
enough: `Z₁ = [-1, 1]`, `Z₂ = [-2, 2]` and the two directions `±1`. Then (22) reads
`µ = 1 - 2`, solved by `µ = -1`; the minuend is described exactly by its halfspaces and so
is the closed form `(0, -1)`, `[-1, 1]`, and yet the difference is empty, since `0 + 2`
leaves `[-1, 1]`.

## References

* [1] M. Althoff. "On Computing the Minkowski Difference of Zonotopes".
      arXiv, 2015.
-/

-- Authors:       Tobias Ladner
-- Written:       08-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Prop. 6] as printed: (22) solved exactly at a negative `µ` does not make the stretched
minuend the Minkowski difference. -/
theorem Zonotope.minkDiffStretch_eq_counterexample :
    ∃ (Z₁ Z₂ : Zonotope ℝ) (C : Fin 2 → (ℝ →ₗ[ℝ] ℝ)) (μ : Fin Z₁.h → ℝ),
      {y | ∀ i, C i (y - Z₁.c) ≤ ∑ υ, |C i (Z₁.G υ)|} ⊆ Z₁.construct ∧
      {y | ∀ i, C i (y - (Z₁.minkDiffStretch Z₂ μ).c)
          ≤ ∑ υ, |C i ((Z₁.minkDiffStretch Z₂ μ).G υ)|} ⊆ (Z₁.minkDiffStretch Z₂ μ).construct ∧
      (∀ i, ∑ υ, |C i (Z₁.G υ)| * μ υ = (∑ υ, |C i (Z₁.G υ)|) - ∑ υ, |C i (Z₂.G υ)|) ∧
      minkowskiDiff Z₁.construct Z₂.construct ≠
        (Z₁.minkDiffStretch Z₂ μ).construct := by -- --- PROOF ---
  refine ⟨⟨1, 0, fun _ => 1⟩, ⟨1, 0, fun _ => 2⟩, ![LinearMap.id, -LinearMap.id],
    fun _ => -1, ?_, ?_, ?_, ?_⟩
  -- the minuend is described by its halfspaces `±y ≤ 1`
  · intro y hy
    have h0 := hy 0
    have h1 := hy 1
    simp [Zonotope.construct] at h0 h1 ⊢
    exact ⟨fun _ => y, abs_le.mpr ⟨by linarith, h0⟩, by simp⟩
  -- and so is the closed form `(0, -1)`
  · intro y hy
    have h0 := hy 0
    have h1 := hy 1
    simp [Zonotope.construct, Zonotope.minkDiffStretch] at h0 h1 ⊢
    exact ⟨fun _ => -y, abs_le.mpr ⟨by linarith, by linarith⟩, by simp⟩
  -- (22) holds at `µ = -1`, both sides being `1 - 2`
  · intro i
    fin_cases i <;> simp <;> norm_num
  -- yet `0` is in the closed form, and not in the difference, as `0 + 2 ∉ [-1, 1]`
  · intro heq
    have h0 : (0 : ℝ) ∈ (Zonotope.minkDiffStretch (⟨1, 0, fun _ => 1⟩ : Zonotope ℝ)
        ⟨1, 0, fun _ => 2⟩ (fun _ => -1)).construct :=
      ⟨fun _ => 0, fun _ => by simp, by simp [Zonotope.minkDiffStretch]⟩
    rw [← heq] at h0
    have h2 : (2 : ℝ) ∈ (⟨1, 0, fun _ => 2⟩ : Zonotope ℝ).construct :=
      ⟨fun _ => 1, fun _ => by simp, by simp⟩
    obtain ⟨β, hβ, hx⟩ := h0 2 h2
    have := abs_le.mp (hβ 0)
    simp at hx
    linarith [this.2]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
