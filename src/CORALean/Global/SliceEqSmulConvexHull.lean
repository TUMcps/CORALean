module

public import CORALean.Global.Tensor
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# The slices of a lifted zonotope

`[1, Lemma 5]`: with `Z* = ∑ᵢ [0, 1] (vᵢ + α e_{n+1})` (`[1, Lemma 5, Eq. 33]`), the slice at height
`β ∈ [0, α]` is `(β / α) conv(v₁, …, v_N) × {β}` (`[1, Lemma 5, Eq. 36]`; Eq. 35 is `β = α`).
A point of the slice is `∑ μᵢ vᵢ` with `μᵢ ∈ [0, 1]` and `α ∑ μᵢ = β`; rescaling the `μᵢ`
by `α / β` gives convex weights. The printed proof divides by `β`, and at `β = 0` the slice
is `{0}` for a reason of its own: every `μᵢ` is `0`. The lift is `Vec ℝ n × ℝ`.

## Inputs
* `v` – generator vectors
* `α` – lift height
* `β` – slice height

## Hypotheses
* `hN` – there is at least one generator
* `hα` – the lift height is positive
* `hβ0` – the slice height is nonnegative
* `hβα` – the slice height is at most the lift height

## Conclusion
* the slice at that height is the scaled convex hull of the generators

## References

* [1] [A. Kulmburg and M. Althoff. "On the co-NP-Completeness of the Zonotope Containment Problem".
      European Journal of Control,
      2021.](../../../references/2021/kulmburg-ejc-zonotope-containment.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Pointwise

variable {N n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem slice_eq_smul_convexHull (hN : 0 < N) (v : Fin N → Vec ℝ n) {α β : ℝ} (hα : 0 < α)
    (hβ0 : 0 ≤ β) (hβα : β ≤ α) : -- --- CONCL ---
    {x : Vec ℝ n | ∃ μ : Fin N → ℝ, (∀ i, 0 ≤ μ i ∧ μ i ≤ 1) ∧
        (x, β) = ∑ i, μ i • ((v i, α) : Vec ℝ n × ℝ)}
      = (β / α) • convexHull ℝ (Set.range v) := by -- --- PROOF ---
  -- a point of the lift splits into its two coordinates
  have hsplit : ∀ (x : Vec ℝ n) (μ : Fin N → ℝ),
      (x, β) = ∑ i, μ i • ((v i, α) : Vec ℝ n × ℝ) ↔ x = ∑ i, μ i • v i ∧ β = α * ∑ i, μ i := by
    intro x μ
    rw [Prod.ext_iff, Prod.fst_sum, Prod.snd_sum]
    simp [Finset.mul_sum, mul_comm]
  ext x
  simp only [Set.mem_setOf_eq, hsplit]
  constructor
  · rintro ⟨μ, hμ, rfl, hβ⟩
    rcases hβ0.lt_or_eq with hpos | hzero
    -- `β > 0`: the weights `(α / β) μᵢ` are convex
    · have hs : ∑ i, μ i ≠ 0 := by intro h; rw [h, mul_zero] at hβ; linarith
      refine ⟨∑ i, (α / β * μ i) • v i, ?_, ?_⟩
      · refine (convex_convexHull ℝ _).sum_mem (fun i _ => mul_nonneg (by positivity) (hμ i).1)
          ?_ fun i _ => subset_convexHull ℝ _ ⟨i, rfl⟩
        rw [← Finset.mul_sum, hβ]; field_simp
      · show (β / α) • ∑ i, (α / β * μ i) • v i = ∑ i, μ i • v i
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [smul_smul]; congr 1; field_simp
    -- `β = 0`: every weight vanishes
    · have h0 : ∀ i, μ i = 0 := by
        have hs : ∑ i, μ i = 0 := by
          rw [← hzero] at hβ
          exact (mul_eq_zero.mp hβ.symm).resolve_left hα.ne'
        exact fun i => (Finset.sum_eq_zero_iff_of_nonneg fun i _ => (hμ i).1).mp hs i
          (Finset.mem_univ i)
      refine ⟨v ⟨0, hN⟩, subset_convexHull ℝ _ ⟨_, rfl⟩, ?_⟩
      simp [h0, ← hzero]
  -- the weighted points form a convex set holding every `(β / α) vᵢ`
  · intro hx
    rw [← convexHull_smul] at hx
    refine convexHull_min (t := {x | ∃ μ : Fin N → ℝ, (∀ i, 0 ≤ μ i ∧ μ i ≤ 1) ∧
      x = ∑ i, μ i • v i ∧ β = α * ∑ i, μ i}) ?_ ?_ hx
    · rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
      refine ⟨Pi.single i (β / α), fun j => ?_, ?_, ?_⟩
      · by_cases hj : j = i
        · subst hj; simp only [Pi.single_eq_same]
          exact ⟨by positivity, (div_le_one hα).mpr hβα⟩
        · simp [Pi.single_eq_of_ne hj]
      · simp [Pi.single_apply]
      · simp [Pi.single_apply]; field_simp
    -- a convex combination of weights is a weight
    · rintro _ ⟨μ₁, hμ₁, rfl, hβ₁⟩ _ ⟨μ₂, hμ₂, rfl, hβ₂⟩ a b ha hb hab
      refine ⟨a • μ₁ + b • μ₂, fun i => ⟨?_, ?_⟩, ?_, ?_⟩
      · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        nlinarith [(hμ₁ i).1, (hμ₂ i).1]
      · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        nlinarith [(hμ₁ i).2, (hμ₂ i).2]
      · simp only [Finset.smul_sum, smul_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
          add_smul, Finset.sum_add_distrib]
      · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
          ← Finset.mul_sum, mul_add]
        rw [mul_left_comm, ← hβ₁, mul_left_comm, ← hβ₂, ← add_mul, hab, one_mul]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
