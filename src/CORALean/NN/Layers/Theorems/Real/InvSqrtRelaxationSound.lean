module

public import CORALean.NN.Layers.Definitions.InvSqrtRelaxation
public import CORALean.NN.Layers.Theorems.Real.Basic
public import CORALean.NN.Layers.Theorems.Real.ContinuousInvSqrt
public import CORALean.NN.Layers.Theorems.Real.HasDerivAtInvSqrt
public import CORALean.NN.Layers.Theorems.Real.InvSqrtDerivMono
public import CORALean.NN.Layers.Theorems.OfAntitoneSound
public import CORALean.NN.Layers.Theorems.Real.SubMulBoundsOfDeriv
public import CORALean.NN.Layers.Theorems.TighterSound

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

* [1] T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph
      Convolutional Networks with Uncertain Node Features and Uncertain Graph
      Structure". TMLR, 2025. arXiv:2404.15065.
-/

-- Authors:       Claude Opus 5.5
-- Written:       06-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

theorem aux_invSqrtRelaxationRange_sound : invSqrtRelaxationRange.Sound invSqrt :=
  Relaxation.ofAntitone_sound antitone_invSqrt (enclosure_exact_sound invSqrt)

theorem aux_invSqrtRelaxationDeriv_sound : -- --- CONCL ---
    invSqrtRelaxationDeriv.Sound invSqrt := by -- --- PROOF ---
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
      continuous_invSqrt.continuousOn
      (fun x hxl _ => hasDerivAt_invSqrt (lt_of_le_of_lt hl1 hxl))
      (fun x hxl _ => invSqrtDeriv_mono (l := l) (u := x) (by linarith) hxl)
      (fun x _ hxu => invSqrtDeriv_mono (l := x) (u := u) (by linarith) hxu)
      (by linarith [invSqrtDeriv_mono (l := l) (u := u) (by linarith) (le_trans hl' hu')])
      (by linarith [invSqrtDeriv_mono (l := l) (u := u) (by linarith) (le_trans hl' hu')])
      hl' hu'
    rw [abs_le]
    exact ⟨by nlinarith [h₁], by nlinarith [h₂]⟩
  · -- below the clamp: the box straddles the kink, so fall back
    simp only [invSqrtRelaxationDeriv, if_neg hl1]
    exact aux_invSqrtRelaxationRange_sound.sound hl hu


-- =======================================  MAIN THEOREM  ======================================= --

theorem invSqrtRelaxation_sound : invSqrtRelaxation.Sound invSqrt :=
  Relaxation.tighter_sound aux_invSqrtRelaxationRange_sound aux_invSqrtRelaxationDeriv_sound

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
