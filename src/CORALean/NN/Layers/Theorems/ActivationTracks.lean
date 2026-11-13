module

public import CORALean.ContSet.Conversion.Float.Instances
public import CORALean.ContSet.Zonotope.Float.Instances
public import CORALean.ContSet.Zonotope.Float.Theorems.TracksMtimesPlus
public import CORALean.NN.Layers.Definitions.Tracks
public import CORALean.NN.Layers.Definitions.Relaxation
public import CORALean.NN.Layers.Operations.Activation
public import CORALean.NN.Layers.Theorems.ActivationDeviationMem

@[expose] public section

/-!
# An activation layer keeps the generators of a zonotope in front

On a zonotope the layer is `mtimes` of the slopes the relaxation chose and `plus` of the box that
holds the deviation from them, so the image has the generators of the zonotope first, each scaled
by its coordinate's slope. A point at weights `β` goes to the point of the activation at `β`
followed by the box's weights, whichever relaxation is used: soundness is all it asks.

## Inputs
* `R` – relaxation of the activation
* `σ` – activation

## Hypotheses
* `hR` – relaxation is sound for the activation

## Conclusion
* the layer tracks the activation applied coordinatewise
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       13-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float
open scoped CORALean.Float

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Layer.activation_tracks {R : Relaxation 𝕋} {σ : ℝ → ℝ}
    (hR : R.Encloses σ) : -- --- CONCL ---
    (Layer.activation (S := 𝒵[𝕋]) (n := n) R).Tracks fun x i => σ (x i) := by -- --- PROOF ---
  intro X
  -- the deviation from the slopes is in the box of the zonotope's box
  have h := Zonotope.tracks_mtimes_plus (R.step_slopeMat X.interval) (R.box X.interval) X
    (f := fun x i => σ (x i)) (fun x hx => Relaxation.deviation_mem_box (P := fun _ _ => True)
      ⟨fun _ hl hu => hR.sound hl hu⟩ (Zonotope.interval_contains X hx) fun _ => trivial)
  simpa [Layer.activation, Float.OfInterval.ofInterval, Float.IntervalOuter.interval,
    Plus.plus, Mtimes.mtimes, Zonotope.materialise_eq] using h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
