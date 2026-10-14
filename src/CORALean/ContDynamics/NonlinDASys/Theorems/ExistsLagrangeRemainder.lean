module

public import CORALean.ContSet.ContSet.ContSet
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Convex.Segment

@[expose] public section

/-!
# The first-order Taylor expansion with Lagrange remainder, one coordinate at a time

[1, Eq. 8]: `fᵢ(z) ∈ fᵢ(z*) + ∂fᵢ/∂z|_{z*} (z - z*) ⊕ {½ (z - z*)ᵀ ∂²fᵢ/∂z²|_ξ (z - z*)}`, the
remainder taken at some `ξ` on the segment from `z*` to `z` ("which follows from the mean
value theorem"), and the same for `gⱼ`. Stated for one scalar function `F`, a coordinate
`fᵢ` or `gⱼ`, with first derivative `Ff` and second derivative `Hf`; `Hf ξ ν ν` is the
quadratic form `νᵀ H(ξ) ν` of the Hessian, whose entries are `Hf ξ eⱼ eₖ`.

`ξ` belongs to the coordinate: each `fᵢ` has its own, on the segment and so in `R^z` when
`R^z` is convex, which is [1, Eq. 23]'s `Hᵈ⁽ⁱ⁾(ξ) ∈ Hᵈ⁽ⁱ⁾` row by row. [1, Eq. 10], [1, Eq. 11]
and [1, Eq. 20] take one `ξ` for all coordinates at once, which this does not give and which
fails (`SharedLagrangePoint`).

The proof is the mean value theorem twice along `φ(s) = F(z* + s ν)`: Cauchy's form for
`φ(s) - s φ'(0)` against `s²` on `[0, 1]` gives `c` with `φ'(c) - φ'(0) = 2c (φ(1) - φ(0) - φ'(0))`,
and Lagrange's form for `φ'` on `[0, c]` gives `d` with `φ'(c) - φ'(0) = c φ''(d)`; `ξ = z* + d ν`.
The derivatives are two-sided at every point of the convex set `C` holding both ends.

## References

* [1] M. Althoff and B. H. Krogh. "Reachability Analysis of Nonlinear Differential-Algebraic
      Systems". IEEE Transactions on Automatic Control, 59(2):371-383, 2014.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Set

variable {d : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Eq. 8]: `F z = F z* + F'(z*)(z - z*) + ½ F''(ξ)(z - z*)(z - z*)` for some `ξ` on the
segment from `z*` to `z`. -/
theorem NonlinDASys.exists_lagrange_remainder {C : Set (Vec ℝ d)} (hC : Convex ℝ C)
    {F : Vec ℝ d → ℝ} {Ff : Vec ℝ d → (Vec ℝ d →L[ℝ] ℝ)}
    {Hf : Vec ℝ d → (Vec ℝ d →L[ℝ] Vec ℝ d →L[ℝ] ℝ)}
    (hF : ∀ ξ ∈ C, HasFDerivAt F (Ff ξ) ξ) (hH : ∀ ξ ∈ C, HasFDerivAt Ff (Hf ξ) ξ)
    {zs z : Vec ℝ d} (hzs : zs ∈ C) (hz : z ∈ C) :
    ∃ ξ ∈ segment ℝ zs z,
      F z = F zs + Ff zs (z - zs) + (1 / 2) * Hf ξ (z - zs) (z - zs) := by -- --- PROOF ---
  set h : Vec ℝ d := z - zs with hh
  -- the segment stays inside `C`, which is where both derivatives live
  have hmem : ∀ t ∈ Icc (0:ℝ) 1, zs + t • h ∈ C := fun t ht => hC.add_smul_sub_mem hzs hz ht
  have hpath : ∀ t : ℝ, HasDerivAt (fun s : ℝ => zs + s • h) h t := fun t => by
    simpa using ((hasDerivAt_id t).smul_const h).const_add zs
  set φ : ℝ → ℝ := fun s => F (zs + s • h) with hφdef
  set φ' : ℝ → ℝ := fun s => Ff (zs + s • h) h with hφ'def
  have hφ : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt φ (φ' t) t := fun t ht =>
    (hF _ (hmem t ht)).comp_hasDerivAt t (hpath t)
  -- the second derivative along the segment, the direction held constant
  have hφ' : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt φ' (Hf (zs + t • h) h h) t := by
    intro t ht
    have h3 := ((hH _ (hmem t ht)).clm_apply
      (hasFDerivAt_const h (zs + t • h))).comp_hasDerivAt t (hpath t)
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
      _root_.add_apply, _root_.zero_apply, map_zero,
      zero_add] at h3
    exact h3
  have hIcc : ∀ {a b : ℝ}, 0 ≤ a → b ≤ 1 → Icc a b ⊆ Icc 0 1 := fun ha hb =>
    Icc_subset_Icc ha hb
  have hlin : ∀ t : ℝ, HasDerivAt (fun s : ℝ => s * φ' 0) (φ' 0) t := fun t => by
    simpa using (hasDerivAt_id t).mul_const (φ' 0)
  -- Cauchy's mean value theorem for `φ(s) - s φ'(0)` against `s²` on `[0, 1]`
  obtain ⟨c, hc, hcauchy⟩ := exists_ratio_hasDerivAt_eq_ratio_slope
    (fun s => φ s - s * φ' 0) (fun s => φ' s - φ' 0) zero_lt_one
    (fun t ht => ((hφ t ht).continuousAt.sub
      (continuous_id.mul continuous_const).continuousAt).continuousWithinAt)
    (fun t ht => (hφ t (Ioo_subset_Icc_self ht)).sub (hlin t))
    (fun s => s ^ 2) (fun s => 2 * s)
    (continuous_pow 2).continuousOn (fun t _ => by simpa using hasDerivAt_pow 2 t)
  -- Lagrange's mean value theorem for `φ'` on `[0, c]`
  obtain ⟨e, he, hlag⟩ := exists_hasDerivAt_eq_slope φ' (fun t => Hf (zs + t • h) h h) hc.1
    (fun t ht => (hφ' t (hIcc le_rfl hc.2.le ht)).continuousAt.continuousWithinAt)
    (fun t ht => hφ' t (hIcc le_rfl hc.2.le (Ioo_subset_Icc_self ht)))
  refine ⟨zs + e • h, ?_, ?_⟩
  · rw [segment_eq_image']
    exact ⟨e, ⟨he.1.le, he.2.le.trans hc.2.le⟩, rfl⟩
  -- the two together: `2c (φ(1) - φ(0) - φ'(0)) = c φ''(e)`, and `c > 0`
  · have hc0 : c ≠ 0 := hc.1.ne'
    rw [eq_div_iff (by simpa using hc0)] at hlag
    simp only [one_pow, zero_pow two_ne_zero, sub_zero, one_mul, zero_mul] at hcauchy
    have h1 : φ 1 = F z := by simp [hφdef, hh]
    have h0 : φ 0 = F zs := by simp [hφdef]
    have h0' : φ' 0 = Ff zs h := by simp [hφ'def]
    rw [← h1, ← h0, ← h0']
    have key : (φ 1 - φ 0 - φ' 0) * (2 * c) = Hf (zs + e • h) h h * c := by
      rw [← hlag] at hcauchy
      linarith
    field_simp
    nlinarith [key, hc.1]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
