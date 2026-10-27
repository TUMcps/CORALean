module

public import CORALean.NN.Layers.Definitions.InvSqrtRelaxation
public import CORALean.NN.Layers.Theorems.Real.Basic
public import CORALean.NN.Layers.Definitions.InvSqrt
public import Mathlib.Analysis.Normed.Order.Lattice
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.Tactic.Positivity
public import CORALean.NN.Layers.Theorems.OfAntitoneEncloses
public import CORALean.NN.Layers.Theorems.Real.SubMulBoundsOfDeriv
public import CORALean.NN.Layers.Theorems.TighterEncloses

@[expose] public section

/-!
# The inverse square root's relaxation over ℝ is sound

ℝ-only, the relaxation being built at `invSqrt` itself: from the clamp point up, the mean
value theorem against the derivative bracket; below it the box straddles the kink, and the range
relaxation, sound everywhere, is what is used; `tighter` keeps both. A sound bound on the error
[1, Lemma 2] computes exactly, at its critical points.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* the relaxation is sound for the clamped inverse square root

## References

* [1] [T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph Convolutional Networks
      with Uncertain Node Features and Uncertain Graph Structure". Transactions on Machine Learning
      Research, 2025.](../../../../../../references/2025/ladner-tmlr-gcn.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       06-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The inverse square root's derivative bracket is nonempty. -/
private theorem aux_invSqrtDeriv_mono {l u : ℝ} (hl : 0 < l) (hlu : l ≤ u) : -- --- CONCL ---
    invSqrtDerivLo l ≤ invSqrtDerivHi u := by -- --- PROOF ---
  unfold invSqrtDerivLo invSqrtDerivHi
  have hupos : (0 : ℝ) < u := hl.trans_le hlu
  have hprod : l * Real.sqrt l ≤ u * Real.sqrt u :=
    mul_le_mul hlu (Real.sqrt_le_sqrt hlu) (Real.sqrt_nonneg l) hupos.le
  have hlpos : (0 : ℝ) < l * Real.sqrt l := by positivity
  gcongr


/-- The clamped inverse square root's derivative above the clamp. -/
private theorem aux_hasDerivAt_invSqrt {x : ℝ} (hx : 1 < x) : -- --- CONCL ---
    HasDerivAt invSqrt (-(2 * x * Real.sqrt x)⁻¹) x := by -- --- PROOF ---
  have heq : invSqrt =ᶠ[nhds x] (fun y => (Real.sqrt y)⁻¹) := by
    filter_upwards [eventually_gt_nhds hx] with y hy
    rw [invSqrt_eq_of_one_le hy.le]
  rw [heq.hasDerivAt_iff]
  have hxpos : (0 : ℝ) < x := by linarith
  have hxne : x ≠ 0 := hxpos.ne'
  have hd := (Real.hasDerivAt_sqrt hxne).inv (Real.sqrt_ne_zero'.mpr hxpos)
  have hval : -(1 / (2 * Real.sqrt x)) / Real.sqrt x ^ 2 = -(2 * x * Real.sqrt x)⁻¹ := by
    rw [Real.sq_sqrt hxpos.le]
    field_simp
  rwa [hval] at hd


/-- The clamped inverse square root is continuous. -/
private theorem aux_continuous_invSqrt : Continuous invSqrt := by
  have h : Continuous fun x : ℝ => Real.sqrt (max x 1) :=
    Real.continuous_sqrt.comp (continuous_id.max continuous_const)
  refine h.inv₀ fun x => ne_of_gt (Real.sqrt_pos.mpr ?_)
  exact lt_of_lt_of_le one_pos (le_max_right _ _)


private theorem aux_invSqrtRelaxationRange_encloses : invSqrtRelaxationRange.Encloses invSqrt :=
  Relaxation.ofAntitone_encloses antitone_invSqrt (enclosure_exact_encloses invSqrt)

private theorem aux_invSqrtRelaxationDeriv_encloses : -- --- CONCL ---
    invSqrtRelaxationDeriv.Encloses invSqrt := by -- --- PROOF ---
  refine ⟨fun {l u t} hl hu => ?_⟩
  show |invSqrt t - (invSqrtRelaxationDeriv.slope l u * t + invSqrtRelaxationDeriv.offset l u)|
    ≤ invSqrtRelaxationDeriv.error l u
  by_cases hl1 : 1 ≤ l
  · -- from the clamp point up: the mean value theorem against the derivative bracket
    simp only [invSqrtRelaxationDeriv, if_pos hl1]
    have hl' : l ≤ t := hl
    have hu' : t ≤ u := hu
    obtain ⟨h₁, h₂⟩ := sub_mul_bounds_of_deriv
      (σ := invSqrt) (σ' := fun x => -(2 * x * Real.sqrt x)⁻¹)
      (lam := (invSqrtDerivLo l + invSqrtDerivHi u) / 2)
      aux_continuous_invSqrt.continuousOn
      (fun x hxl _ => aux_hasDerivAt_invSqrt (lt_of_le_of_lt hl1 hxl))
      (fun x hxl _ => aux_invSqrtDeriv_mono (l := l) (u := x) (by linarith) hxl)
      (fun x _ hxu => aux_invSqrtDeriv_mono (l := x) (u := u) (by linarith) hxu)
      (by linarith [aux_invSqrtDeriv_mono (l := l) (u := u) (by linarith) (le_trans hl' hu')])
      (by linarith [aux_invSqrtDeriv_mono (l := l) (u := u) (by linarith) (le_trans hl' hu')])
      hl' hu'
    rw [abs_le]
    exact ⟨by nlinarith [h₁], by nlinarith [h₂]⟩
  · -- below the clamp: the box straddles the kink, so fall back
    simp only [invSqrtRelaxationDeriv, if_neg hl1]
    exact aux_invSqrtRelaxationRange_encloses.sound hl hu


-- =======================================  MAIN THEOREM  ======================================= --

theorem invSqrtRelaxation_encloses : invSqrtRelaxation.Encloses invSqrt :=
  Relaxation.tighter_encloses aux_invSqrtRelaxationRange_encloses
    aux_invSqrtRelaxationDeriv_encloses

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
