import CORALean.Global.CoordinatePath
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Convex.Topology

/-!
# Mean-value AE extensions of a real-valued function

[1, Thm. 1]: for `f : ℝᵐ → ℝ` on the box `x` with centre `c` and radius `r`,
`f(c) ∈ [f̲₀, f̄₀]` and `|∂ᵢf| ∈ [∇̲ᵢ, ∇̄ᵢ]` on the path set `{(c₁, …, cᵢ₋₁, xᵢ, …, x_m)}`,
`range(f, x) ⊆ [f̲₀, f̄₀] + ⟨∇̄, r⟩[-1, 1]` (1) and
`[f̄₀ - ⟨∇̲, r⟩, f̲₀ + ⟨∇̲, r⟩] ⊆ range(f, x)` (2).

The printed proof of (2) says `∇̲ ≠ 0` means `f` is strictly increasing or decreasing on
the box, and takes the corners `x̲`, `x̄`. That holds for `m = 1`; for `m ≥ 2` the partials
may have different signs (`f(x) = x₁ - x₂`), and the corners do not reach `f(c) ± ⟨∇̲, r⟩`.
Here each coordinate moves the way its own partial points, and an intermediate value
argument over the connected box closes the interval (`exists_ge_add_sum_of_abs_partial_ge`).

## References

* [1] E. Goubault and S. Putot. "Robust Under-Approximations and Application to
      Reachability of Non-Linear Control Systems With Disturbances". IEEE Control Systems
      Letters, 4(4):928-933, 2020.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Set

variable {m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Thm. 1] (1): the range is inside `[f̲₀, f̄₀] + ⟨∇̄, r⟩[-1, 1]`. -/
theorem meanValueAE_outer {f : (Fin m → ℝ) → ℝ} (hf : Differentiable ℝ f) {lo hi : Fin m → ℝ}
    {f0lo f0hi : ℝ} (hf0 : f (fun i => (lo i + hi i) / 2) ∈ Icc f0lo f0hi) (dhi : Fin m → ℝ)
    (hd : ∀ i, ∀ y ∈ Icc lo hi, (∀ j, j < i → y j = (lo j + hi j) / 2) →
      |fderiv ℝ f y (Pi.single i 1)| ≤ dhi i) :
    f '' Icc lo hi ⊆ Icc (f0lo - ∑ i, dhi i * ((hi i - lo i) / 2))
      (f0hi + ∑ i, dhi i * ((hi i - lo i) / 2)) := by
  rintro _ ⟨x, hx, rfl⟩
  have := abs_le.mp (abs_sub_le_sum_of_abs_partial_le hf dhi hd hx)
  exact ⟨by linarith [hf0.1], by linarith [hf0.2]⟩

/-- [1, Thm. 1] (2): `[f̄₀ - ⟨∇̲, r⟩, f̲₀ + ⟨∇̲, r⟩]` is inside the range. -/
theorem meanValueAE_inner {f : (Fin m → ℝ) → ℝ} (hf : Differentiable ℝ f) {lo hi : Fin m → ℝ}
    (hlh : lo ≤ hi) {f0lo f0hi : ℝ} (hf0 : f (fun i => (lo i + hi i) / 2) ∈ Icc f0lo f0hi)
    (dlo : Fin m → ℝ) (hd : ∀ i, ∀ y ∈ Icc lo hi, (∀ j, j < i → y j = (lo j + hi j) / 2) →
      dlo i ≤ |fderiv ℝ f y (Pi.single i 1)|) :
    Icc (f0hi - ∑ i, dlo i * ((hi i - lo i) / 2)) (f0lo + ∑ i, dlo i * ((hi i - lo i) / 2))
      ⊆ f '' Icc lo hi := by -- --- PROOF ---
  -- a point above `f(c) + ⟨∇̲, r⟩`, and one below `f(c) - ⟨∇̲, r⟩` from `-f`
  obtain ⟨p, hp, hfp⟩ := exists_ge_add_sum_of_abs_partial_ge hf hlh dlo hd
  obtain ⟨q, hq, hfq⟩ := exists_ge_add_sum_of_abs_partial_ge hf.neg hlh dlo fun i y hy hyc => by
    rw [fderiv_neg, neg_apply, abs_neg]
    exact hd i y hy hyc
  simp only [Pi.neg_apply] at hfq
  -- the box is connected, so `f` takes every value between `f q` and `f p`
  refine fun z hz => (convex_Icc lo hi).isPreconnected.intermediate_value hq hp
    hf.continuous.continuousOn ⟨?_, ?_⟩
  · linarith [hz.1, hf0.2]
  · linarith [hz.2, hf0.1]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
