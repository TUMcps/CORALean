module

public import CORALean.ContDynamics.NonlinearSys.Operations.GainDim
public import CORALean.ContDynamics.NonlinearSys.Theorems.BoxDiameterAbstrSolInf
public import Mathlib.Analysis.Calculus.Deriv.Abs
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Mul

@[expose] public section

/-!
# The gain's derivative need not have a non-positive limit

`[1, Prop. 2 (derivative)]`'s `(41)` claims `lim_{h→0} dφᵢ(h;δ)/dh ≤ 0` for `δ ∈ [0,1]`
whenever every `Q⁽ᵖ⁾ᵢ` is differentiable at `0`. Take `n = 1`, `A = 0` and the zonotope
`Ψ(h) = ⟨0, 1 - h⟩`: both smooth, the only surviving coefficient of the series of row norms
`(35)` is `p = 0` with `q⁽⁰⁾ = 0`, `Q⁽⁰⁾(h) = |1 - h|`, differentiable at `0` with
`Q⁽⁰⁾(0) = 1`, and every other `Q⁽ᵖ⁾` is `0`. The width is `2h(1 - h)` on `[0,1)`, so
`φ(h;δ) = δ(1 - δh)/(1 - h)` and `dφ/dh = δ(1 - δ)/(1 - h)²`, which tends to `δ(1 - δ) = 1/4`
at `δ = 1/2`: positive. The proof's line `(B.5)` replaces `Q(h)` by `Q(δh)` and drops the `Q̇`
terms of the numerator, which here are the whole derivative.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* the gain's derivative tends to a positive limit

## References

* [1] M. Wetzlinger, A. Kulmburg, A. Le Penven and M. Althoff. "Adaptive
      Reachability Algorithms for Nonlinear Systems Using Abstraction Error
      Analysis". Nonlinear Analysis: Hybrid Systems, vol. 46, 2022, p. 101252.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Filter Topology Matrix CORALean.Real

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The width of the example: `2h(1 - h)` on `[0,1)`. -/
theorem aux_boxDiameter_gainDerivExample {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    boxDiameter (abstrSolInf (fun _ => (0 : Mat ℝ 1 1))
      (fun s => (⟨1, 0, fun _ => fun _ => 1 - s⟩ : Zonotope (Vec ℝ 1)).construct) t) 0
      = 2 * (t * (1 - t)) := by -- --- PROOF ---
  rw [boxDiameter_abstrSolInf (fun _ => (0 : Mat ℝ 1 1)) _ ht0 rfl 0]
  congr 1
  rw [tsum_eq_single 0]
  · simp [abs_of_pos (sub_pos.mpr ht1)]
  · intro p hp
    simp [zero_pow hp]

/-- The gain of the example: `δ(1 - δh)/(1 - h)` for `δ = 1/2` on `(0,1)`. -/
theorem aux_gainDim_gainDerivExample {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    gainDim (fun _ => (0 : Mat ℝ 1 1))
      (fun s => (⟨1, 0, fun _ => fun _ => 1 - s⟩ : Zonotope (Vec ℝ 1)).construct) s (1 / 2) 0
      = (1 / 2) * ((1 - s / 2) / (1 - s)) := by
  rw [gainDim, aux_boxDiameter_gainDerivExample (by positivity) (by linarith),
    aux_boxDiameter_gainDerivExample hs0.le hs1]
  have h1 : (1 - s) ≠ 0 := by linarith
  field_simp


-- =======================================  MAIN THEOREM  ======================================= --

/-- `[1, Prop. 2 (derivative)]`'s `(41)` as printed fails: smooth `A` and `G` with every
`Q⁽ᵖ⁾ᵢ = |(Aᵖ(h)G(h))ᵢ|` differentiable at `0` and `Q⁽⁰⁾(0) ≠ 0`, for which `dφ/dh` tends to
`1/4 > 0` at `δ = 1/2`. -/
theorem gainDim_deriv_counterexample : -- --- CONCL ---
    ∃ (A : ℝ → Mat ℝ 1 1) (G : ℝ → Vec ℝ 1),
      (∀ k l, ContDiff ℝ ⊤ (fun t => A t k l)) ∧ (∀ k, ContDiff ℝ ⊤ (fun t => G t k)) ∧
      (∀ p, DifferentiableAt ℝ (fun t => |(A t ^ p *ᵥ G t) 0|) 0) ∧ G 0 0 ≠ 0 ∧
      Tendsto (fun h => deriv (fun s => gainDim A
        (fun s => (⟨1, 0, fun _ => G s⟩ : Zonotope (Vec ℝ 1)).construct) s (1 / 2) 0) h)
        (𝓝[>] (0:ℝ)) (𝓝 (1 / 4)) := by -- --- PROOF ---
  refine ⟨fun _ => 0, fun t _ => 1 - t, fun k l => contDiff_const, fun k => ?_, fun p => ?_,
    by simp, ?_⟩
  · exact contDiff_const.sub contDiff_id
  · cases p with
    | zero =>
      simp only [pow_zero, one_mulVec]
      exact (differentiableAt_const _ |>.sub differentiableAt_id).abs (by simp)
    | succ p => simp
  · -- near `h`, the gain is the explicit quotient
    have hderiv : ∀ h : ℝ, 0 < h → h < 1 →
        deriv (fun s => gainDim (fun _ => (0 : Mat ℝ 1 1))
          (fun s => (⟨1, 0, fun _ => fun _ => 1 - s⟩ : Zonotope (Vec ℝ 1)).construct) s (1 / 2) 0) h
          = 1 / (4 * (1 - h) ^ 2) := by
      intro h hh0 hh1
      have hnear : (fun s => gainDim (fun _ => (0 : Mat ℝ 1 1))
          (fun s => (⟨1, 0, fun _ => fun _ => 1 - s⟩ : Zonotope (Vec ℝ 1)).construct) s (1 / 2) 0)
          =ᶠ[𝓝 h] fun s => (1 / 2) * ((1 - s / 2) / (1 - s)) := by
        filter_upwards [isOpen_Ioo.mem_nhds (show h ∈ Set.Ioo 0 1 from ⟨hh0, hh1⟩)] with s hs
        exact aux_gainDim_gainDerivExample hs.1 hs.2
      refine (Filter.EventuallyEq.deriv_eq hnear).trans ?_
      -- the quotient rule on `(1 - s/2)/(1 - s)`
      have hne : (1 - h) ≠ 0 := by linarith
      have hnum : HasDerivAt (fun s : ℝ => 1 - s / 2) (-(1 / 2)) h := by
        simpa using ((hasDerivAt_id' h).div_const 2).const_sub 1
      have hden : HasDerivAt (fun s : ℝ => 1 - s) (-1) h := by
        simpa using (hasDerivAt_id' h).const_sub 1
      have := (hnum.div hden hne).const_mul (1 / 2)
      refine this.deriv.trans ?_
      field_simp
      ring
    -- the derivative is continuous at `0`, with value `1/4` there
    have hlim : Tendsto (fun h : ℝ => 1 / (4 * (1 - h) ^ 2)) (𝓝[>] (0:ℝ)) (𝓝 (1 / 4)) := by
      have hc : ContinuousAt (fun h : ℝ => 1 / (4 * (1 - h) ^ 2)) 0 := by
        refine continuousAt_const.div (continuousAt_const.mul ?_) (by norm_num)
        exact ((continuousAt_const.sub continuousAt_id).pow 2)
      have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
      simpa using this
    refine hlim.congr' ?_
    filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds (show (0:ℝ) < 1 from one_pos)),
      self_mem_nhdsWithin] with h hh1 hh0
    exact (hderiv h hh0 hh1).symm

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
