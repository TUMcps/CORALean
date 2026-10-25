module

public import CORALean.ContDynamics.NonlinearSys.Operations.GainDim
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Mul

@[expose] public section

/-!
# The limit of the gain's derivative as the time span shrinks

The derivative half of `[1, Prop. 2 (derivative)]`, `lim_{h→0} dφᵢ(h;δ)/dh`. As in
`gainDim_tendsto_pow`, `dᵢ(box(R^∞_abs(t)))` is `t^{qᵢ+1}g(t)` with `g(0) ≠ 0`, so
`φᵢ(h;δ) = δ^{qᵢ+1}·g(δh)/g(h)` near `0`, and then `dφᵢ/dh → δ^{qᵢ+1}(δ − 1) g'(0)/g(0)`. This
is not `[1]`'s closing formula, which has only the coefficient of `t^{qᵢ+2}`; `(B.5)` evaluates
`Q` at `δh` where it needs `h`. `g` and `g'` are given as a pair `HasDerivAt g (g' t) t` near `0`;
`[1]` differentiates termwise inside an infinite series, the step this hypothesis stands in for.
`GainDimDerivLimitNonpos` reads the sign off.

## Inputs
* `A` – matrix as a function of the step
* `Ψ` – error set as a function of the step
* `i` – dimension
* `qi` – order of the dimension
* `g` – leading factor of the width
* `g'` – its derivative
* `δ` – shrink factor

## Hypotheses
* `hδ0` – shrink factor nonnegative
* `hδ1` – shrink factor at most one
* `hg` – leading factor differentiable
* `hg'` – derivative continuous at zero
* `hg0` – leading factor nonzero at zero
* `hexp` – width has the power form

## Conclusion
* the gain derivative tends to the stated limit

## References

* [1] M. Wetzlinger, A. Kulmburg, A. Le Penven and M. Althoff. "Adaptive Reachability Algorithms for
      Nonlinear Systems Using Abstraction Error Analysis". Nonlinear Analysis: Hybrid Systems, 2022.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Filter Topology

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `lim_{h→0} dφᵢ(h;δ)/dh = δ^{qᵢ+1}(δ − 1) g'(0)/g(0)` where `dᵢ(box(R^∞_abs(t)))` is
`t^{qᵢ+1}g(t)` near `0` with `g` differentiable near `0`, `g'` continuous at `0` and
`g(0) ≠ 0`. -/
theorem gainDim_deriv_tendsto (A : ℝ → Mat ℝ n n) (Ψ : ℝ → Set (Vec ℝ n)) (i : Fin n)
    {qi : ℕ} {g g' : ℝ → ℝ} {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hg : ∀ᶠ t in 𝓝 (0:ℝ), HasDerivAt g (g' t) t) (hg' : ContinuousAt g' 0) (hg0 : g 0 ≠ 0)
    (hexp : ∀ᶠ t in 𝓝[≥] (0:ℝ), boxDiameter (abstrSolInf A Ψ t) i = t ^ (qi + 1) * g t)
    : -- --- CONCL ---
    Tendsto (fun h => deriv (fun s => gainDim A Ψ s δ i) h) (𝓝[>] (0:ℝ))
      (𝓝 (δ ^ (qi + 1) * (δ - 1) * g' 0 / g 0)) := by -- --- PROOF ---
  -- `g` is continuous at `0`, as it has a derivative there, so it stays off zero near `0`
  have hgc : ContinuousAt g 0 := (hg.self_of_nhds).continuousAt
  have hgne : ∀ᶠ t in 𝓝 (0:ℝ), g t ≠ 0 := hgc.eventually_ne hg0
  -- the three facts, on a ball `[0, ε)` around `0`
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp (hg.and hgne)
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGE_iff_exists_Ico_subset.mp hexp
  -- for small `h > 0` the quotient formula holds on a neighbourhood of `h`
  have hev : ∀ᶠ h in 𝓝[>] (0:ℝ), h < ε ∧ h < u ∧ 0 < h := by
    have h1 : ∀ᶠ h in 𝓝[>] (0:ℝ), h < min ε u := nhdsWithin_le_nhds (Iio_mem_nhds (lt_min hε hu))
    filter_upwards [h1, self_mem_nhdsWithin] with h hh hpos
    exact ⟨lt_of_lt_of_le hh (min_le_left _ _), lt_of_lt_of_le hh (min_le_right _ _), hpos⟩
  have hder : ∀ h, h < ε → h < u → 0 < h →
      deriv (fun s => gainDim A Ψ s δ i) h
        = δ ^ (qi + 1) * ((g' (δ * h) * δ * g h - g (δ * h) * g' h) / g h ^ 2) := by
    intro h hhε hhu hpos
    -- `h` and `δh` both lie in the ball where `g` is differentiable and nonzero
    have hδh : δ * h ∈ Metric.ball (0:ℝ) ε := by
      rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg hδ0 hpos.le)]
      exact lt_of_le_of_lt (mul_le_of_le_one_left hpos.le hδ1) hhε
    have hhb : h ∈ Metric.ball (0:ℝ) ε := by
      rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_nonneg hpos.le]; exact hhε
    obtain ⟨hgd1, -⟩ := hball hδh
    obtain ⟨hgd2, hgh⟩ := hball hhb
    -- near `h`, `φᵢ` is the quotient
    have hnear : (fun s => gainDim A Ψ s δ i) =ᶠ[𝓝 h]
        fun s => δ ^ (qi + 1) * (g (δ * s) / g s) := by
      have hopen : ∀ᶠ s in 𝓝 h, s ∈ Set.Ioo 0 (min ε u) :=
        isOpen_Ioo.mem_nhds ⟨hpos, lt_min hhε hhu⟩
      filter_upwards [hopen] with s hs
      have hsu : s ∈ Set.Ico 0 u := ⟨hs.1.le, lt_of_lt_of_le hs.2 (min_le_right _ _)⟩
      have hsδ : δ * s ∈ Set.Ico 0 u :=
        ⟨mul_nonneg hδ0 hs.1.le, lt_of_le_of_lt (mul_le_of_le_one_left hs.1.le hδ1)
          (lt_of_lt_of_le hs.2 (min_le_right _ _))⟩
      have hne : s ^ (qi + 1) ≠ 0 := pow_ne_zero _ hs.1.ne'
      rw [gainDim, hsub hsu, hsub hsδ, mul_pow]
      rw [div_mul_eq_div_div, mul_comm (δ ^ (qi + 1)) ((s) ^ (qi + 1)), mul_assoc]
      field_simp
    -- the quotient rule on `g(δ·)/g`
    refine (Filter.EventuallyEq.deriv_eq hnear).trans ?_
    have h1 : HasDerivAt (fun s => g (δ * s)) (g' (δ * h) * δ) h := by
      exact (hgd1.comp h ((hasDerivAt_id' h).const_mul δ)).congr_deriv (by ring)
    have h2 := (h1.div hgd2 hgh).const_mul (δ ^ (qi + 1))
    exact h2.deriv
  -- the limit of the right-hand side
  have hlim : Tendsto (fun h : ℝ => δ ^ (qi + 1) * ((g' (δ * h) * δ * g h - g (δ * h) * g' h)
      / g h ^ 2)) (𝓝[>] (0:ℝ)) (𝓝 (δ ^ (qi + 1) * (δ - 1) * g' 0 / g 0)) := by
    -- `g`, `g'` continuous at `0`, along `h → 0` and `δh → 0`
    have hid : Tendsto (fun h : ℝ => h) (𝓝[>] (0:ℝ)) (𝓝 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    have hd : Tendsto (fun h : ℝ => δ * h) (𝓝[>] (0:ℝ)) (𝓝 0) := by
      have hc : Tendsto (fun h : ℝ => δ * h) (𝓝 (0:ℝ)) (𝓝 (δ * 0)) :=
        (continuous_const.mul continuous_id).tendsto 0
      simpa using hc.mono_left nhdsWithin_le_nhds
    have t1 : Tendsto (fun h : ℝ => g' (δ * h)) (𝓝[>] (0:ℝ)) (𝓝 (g' 0)) := hg'.tendsto.comp hd
    have t2 : Tendsto (fun h : ℝ => g h) (𝓝[>] (0:ℝ)) (𝓝 (g 0)) := hgc.tendsto.comp hid
    have t3 : Tendsto (fun h : ℝ => g (δ * h)) (𝓝[>] (0:ℝ)) (𝓝 (g 0)) := hgc.tendsto.comp hd
    have t4 : Tendsto (fun h : ℝ => g' h) (𝓝[>] (0:ℝ)) (𝓝 (g' 0)) := hg'.tendsto.comp hid
    -- the quotient of the limits, and its value in closed form
    have hq := (((t1.mul_const δ).mul t2).sub (t3.mul t4)).div (t2.pow 2) (pow_ne_zero 2 hg0)
    have e : δ ^ (qi + 1) * ((g' 0 * δ * g 0 - g 0 * g' 0) / g 0 ^ 2)
        = δ ^ (qi + 1) * (δ - 1) * g' 0 / g 0 := by
      field_simp
    have := hq.const_mul (δ ^ (qi + 1))
    rw [e] at this
    exact this
  refine hlim.congr' ?_
  filter_upwards [hev] with h hh
  exact (hder h hh.1 hh.2.1 hh.2.2).symm

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
