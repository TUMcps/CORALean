module

public import CORALean.NN.Layers.Operations.SigmoidSinghRelaxation
public import CORALean.NN.Layers.Theorems.AbsSubLeSpread
public import CORALean.NN.Layers.Theorems.SigmoidDerivLoLe
public import CORALean.NN.Layers.Theorems.SigmoidEnclosureEncloses
public import CORALean.NN.Layers.Theorems.SShapeUnimodal
public import CORALean.NN.Layers.Theorems.Real.SigmoidDerivSShape
public import CORALean.NN.Layers.Theorems.Real.HasDerivAtSigmoid
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

@[expose] public section

/-!
# The sigmoid relaxation by Singh's transformer is sound

The sigmoid's derivative rises up to `0` and falls after it, so on a box it stays above the smaller
of its two end values, and each is above the stored lower bound: the stored slope `λ` is below the
derivative on the box. Then `σ t - λ t` does not fall, so it lies between its values at the ends,
which the enclosure and the roundings of the two products bracket, and `abs_sub_le_spread`
measures the distance from the stored middle.

## Inputs
* `k` – reduction depth of the exponential

## Hypotheses
* none

## Conclusion
* the relaxation is sound for the sigmoid
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       12-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The sigmoid's derivative stays above the smaller stored end bound anywhere on the box. -/
private theorem aux_slope_le_deriv (k : ℕ) (l u : 𝕋) (x : ℝ) (hl : toReal l ≤ x)
    (hu : x ≤ toReal u) : -- --- CONCL ---
    toReal (minimum (sigmoidDerivLo (sigmoidEnclosure k) l l)
      (sigmoidDerivLo (sigmoidEnclosure k) u u)) ≤ Real.sigmoidDeriv x := by -- --- PROOF ---
  have hE := sigmoidEnclosure_encloses (𝕋 := 𝕋) k
  have hL := sigmoidDerivLo_le hE l l (toReal l) le_rfl le_rfl
  have hU := sigmoidDerivLo_le hE u u (toReal u) le_rfl le_rfl
  have huni := Real.sigmoidDeriv_sShape.unimodal
  rw [toReal_minimum]
  -- before the maximum the derivative rises from its value at `l`, after it falls to `u`'s
  rcases le_total x 0 with hx | hx
  · exact le_trans (min_le_left _ _) (le_trans hL (huni.1 (le_trans hl hx : toReal l ≤ 0) hx hl))
  · exact le_trans (min_le_right _ _) (le_trans hU (huni.2 hx (le_trans hx hu : 0 ≤ toReal u) hu))


-- =======================================  MAIN THEOREM  ======================================= --

theorem sigmoidSinghRelaxation_encloses (k : ℕ) : -- --- CONCL ---
    (sigmoidSinghRelaxation (𝕋 := 𝕋) k).Encloses Real.sigmoid := by -- --- PROOF ---
  have hE := sigmoidEnclosure_encloses (𝕋 := 𝕋) k
  refine ⟨fun {l u t} hl hu => ?_⟩
  set lam := minimum (sigmoidDerivLo (sigmoidEnclosure k) l l)
    (sigmoidDerivLo (sigmoidEnclosure k) u u) with hlam
  -- `σ - λ id` does not fall on the box
  have hg : ∀ x, HasDerivAt (fun y => Real.sigmoid y - toReal lam * y)
      (Real.sigmoidDeriv x - toReal lam) x := fun x => by
    have hlin : HasDerivAt (fun y => toReal lam * y) (toReal lam) x := by
      simpa using (hasDerivAt_id x).const_mul (toReal lam)
    exact (Real.hasDerivAt_sigmoid x).sub hlin
  have hmon : MonotoneOn (fun y => Real.sigmoid y - toReal lam * y)
      (Set.Icc (toReal l) (toReal u)) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc (toReal l) (toReal u))
      (fun x _ => (hg x).continuousAt.continuousWithinAt)
      (fun x _ => (hg x).differentiableAt.differentiableWithinAt) fun x hx => ?_
    rw [interior_Icc] at hx
    rw [(hg x).deriv]
    linarith [aux_slope_le_deriv k l u x hx.1.le hx.2.le]
  have hle : toReal l ≤ toReal u := le_trans hl hu
  have h1 := hmon ⟨le_rfl, hle⟩ ⟨hl, hu⟩ hl
  have h2 := hmon ⟨hl, hu⟩ ⟨hle, le_rfl⟩ hu
  simp only at h1 h2
  -- the two ends bracket `σ t - λ t`, the roundings of the products pushed outward
  have hA : toReal (subDown (sigmoidEnclosure (𝕋 := 𝕋) k |>.enclose l).inf (mulUp lam l))
      ≤ Real.sigmoid t - toReal lam * t := by
    have hint := subDown_le_sub (sigmoidEnclosure (𝕋 := 𝕋) k |>.enclose l).inf (mulUp lam l)
    have hmul := mul_le_mulUp lam l
    have hend := hE.lo_le l
    linarith
  have hB : Real.sigmoid t - toReal lam * t
      ≤ toReal (subUp (sigmoidEnclosure (𝕋 := 𝕋) k |>.enclose u).sup (mulDown lam u)) := by
    have hint := sub_le_subUp (sigmoidEnclosure (𝕋 := 𝕋) k |>.enclose u).sup (mulDown lam u)
    have hmul := mulDown_le_mul lam u
    have hend := hE.le_hi u
    linarith
  have hspread := abs_sub_le_spread
    (c := half (addUp (subDown (sigmoidEnclosure (𝕋 := 𝕋) k |>.enclose l).inf (mulUp lam l))
      (subUp (sigmoidEnclosure (𝕋 := 𝕋) k |>.enclose u).sup (mulDown lam u)))) hA hB
  unfold sigmoidSinghRelaxation
  dsimp only
  convert hspread using 2
  ring

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
