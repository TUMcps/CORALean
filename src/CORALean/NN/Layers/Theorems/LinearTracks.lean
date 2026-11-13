module

public import CORALean.ContSet.Conversion.Float.Instances
public import CORALean.ContSet.Interval.Float.Theorems.MemPoint
public import CORALean.ContSet.Zonotope.Float.Instances
public import CORALean.ContSet.Zonotope.Float.Theorems.TracksMtimesPlus
public import CORALean.NN.Layers.Definitions.Tracks
public import CORALean.NN.Layers.Operations.Linear

@[expose] public section

/-!
# The linear layer keeps the generators of a zonotope in front

On a zonotope the layer is `mtimes` of the weights and `plus` of the bias's zero-width box, so
the image of a zonotope has the generators of the zonotope first, each mapped by the weights,
and the box's generators after them. A point at weights `β` is mapped to a point at `β` followed
by the box's.

## Inputs
* `W` – weight matrix
* `b` – bias vector

## Hypotheses
* none

## Conclusion
* the layer tracks the affine map the weights denote
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       13-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float Matrix
open scoped CORALean.Float

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Layer.linear_tracks (W : Mat 𝕋 m n) (b : Vec 𝕋 m) : -- --- CONCL ---
    (Layer.linear (S := 𝒵[𝕋]) W b).Tracks
      fun x => toRealMat W *ᵥ x + toRealVec b := by -- --- PROOF ---
  intro X
  -- the bias is the box's point, whatever the point of the zonotope
  have h := Zonotope.tracks_mtimes_plus W (Interval.point b) X
    (f := fun x => toRealMat W *ᵥ x + toRealVec b) (fun x _ => by
      convert Interval.mem_point b using 1
      funext i
      simp; rfl)
  simpa [Layer.linear, Float.OfInterval.ofVec, Float.OfInterval.ofInterval, Plus.plus,
    Mtimes.mtimes, Zonotope.materialise_eq] using h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
