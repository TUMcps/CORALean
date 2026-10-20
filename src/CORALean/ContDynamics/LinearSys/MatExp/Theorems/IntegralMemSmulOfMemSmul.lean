module

public import CORALean.Global.Tensor
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

@[expose] public section

/-!
# A weighted integral of points of a closed convex set

If `f(σ) ∈ w(σ) • K` at every time of `[0, s]`, with `w ≥ 0` and `K` closed and convex, then
`∫₀ˢ f ∈ (∫₀ˢ w) • K`: the integral is the total weight times a weighted average of points of
`K`, and an average of points of a closed convex set stays in it. By separation rather than by
a probability measure: a point outside `K` is cut off by a functional `ℓ` with `ℓ < a` on `K`,
and `ℓ(f(σ)) ≤ w(σ) a` integrates to `ℓ(∫ f) ≤ (∫ w) a`, which the average would violate. `K` may
be unbounded, and nothing is asked of `f` beyond integrability.

## Inputs
* `K` – closed convex set
* `f` – integrand
* `w` – weight function
* `s` – upper limit

## Hypotheses
* `hK` – set convex
* `hKc` – set closed
* `hs` – upper limit nonnegative
* `hf` – integrand integrable
* `hw` – weight integrable
* `hw0` – weight nonnegative
* `hfK` – integrand lies in the weight times the set
* `hW` – total weight positive

## Conclusion
* the integral lies in the total weight times the set
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open MeasureTheory Pointwise

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- A weighted integral of points of a closed convex set is the total weight
times a point of it. -/
theorem integral_mem_smul_of_mem_smul {K : Set (Vec ℝ n)} (hK : Convex ℝ K)
    (hKc : IsClosed K) {f : ℝ → Vec ℝ n} {w : ℝ → ℝ} {s : ℝ} (hs : 0 ≤ s)
    (hf : IntervalIntegrable f volume 0 s) (hw : IntervalIntegrable w volume 0 s)
    (hw0 : ∀ σ ∈ Set.Icc 0 s, 0 ≤ w σ) (hfK : ∀ σ ∈ Set.Icc 0 s, f σ ∈ w σ • K)
    (hW : 0 < ∫ σ in (0:ℝ)..s, w σ) : -- --- CONCL ---
    (∫ σ in (0:ℝ)..s, f σ) ∈ (∫ σ in (0:ℝ)..s, w σ) • K := by -- --- PROOF ---
  set W := ∫ σ in (0:ℝ)..s, w σ with hWdef
  refine ⟨W⁻¹ • ∫ σ in (0:ℝ)..s, f σ, ?_, by
    show W • (W⁻¹ • _) = _; rw [smul_smul, mul_inv_cancel₀ hW.ne', one_smul]⟩
  by_contra hout
  -- a functional cutting the average off from `K`
  obtain ⟨ℓ, a, hKa, hay⟩ := geometric_hahn_banach_closed_point hK hKc hout
  have hpt : ∀ σ ∈ Set.Icc 0 s, ℓ (f σ) ≤ w σ * a := by
    intro σ hσ
    obtain ⟨k, hk, hkf⟩ := hfK σ hσ
    rw [← hkf, map_smul, smul_eq_mul]
    exact mul_le_mul_of_nonneg_left (hKa k hk).le (hw0 σ hσ)
  -- integrated, the functional stays under the weight times the cut
  have hint : ℓ (∫ σ in (0:ℝ)..s, f σ) ≤ W * a := by
    rw [← ℓ.intervalIntegral_comp_comm hf, hWdef, ← intervalIntegral.integral_mul_const]
    exact intervalIntegral.integral_mono_on hs
      ⟨ℓ.integrable_comp hf.1, ℓ.integrable_comp hf.2⟩ (hw.mul_const a) hpt
  rw [map_smul, smul_eq_mul] at hay
  have : a < W⁻¹ * (W * a) := lt_of_lt_of_le hay
    (mul_le_mul_of_nonneg_left hint (inv_nonneg.mpr hW.le))
  rw [← mul_assoc, inv_mul_cancel₀ hW.ne', one_mul] at this
  exact lt_irrefl a this

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
