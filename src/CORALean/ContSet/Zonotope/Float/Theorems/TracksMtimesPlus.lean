module

public import CORALean.ContSet.Conversion.Float.Theorems.IntervalZonotopeContains
public import CORALean.ContSet.Zonotope.Float.Definitions.Tracks
public import CORALean.ContSet.Zonotope.Float.Theorems.ContainsAtMtimes
public import CORALean.ContSet.Zonotope.Float.Theorems.ContainsAtPlus
public import CORALean.ContSet.Zonotope.Float.Theorems.MemGeneratorError
public import CORALean.ContSet.Zonotope.Float.Theorems.MemToSetIffContainsAt
public import CORALean.ContSet.Zonotope.Float.Theorems.MtimesOuter
public import CORALean.ContSet.Zonotope.Float.Theorems.PlusOuter

@[expose] public section

/-!
# A linear map plus a box keeps the generators in front

`Zonotope.mtimes` maps the generators and the center one by one and pays its rounding into the
error box, so a point at the weights `β` is mapped to a point at the same `β`. `Zonotope.plus`
puts the generators of its second operand after those of the first. The box of a layer is added
as the zonotope of that box, so a map that is a linear map plus a point of the box at each point
of `X` is tracked by `(X.mtimes M).plus B.zonotope`, with the weights of `X` unchanged.

## Inputs
* `M` – matrix
* `B` – box
* `X` – zonotope
* `f` – map

## Hypotheses
* `hf` – the map differs from the linear map by a point of the box, on every point of `X`

## Conclusion
* the sum of the image and the box tracks the map over the zonotope
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       13-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.tracks_mtimes_plus (M : Mat 𝕋 m n) (B : Interval (Vec 𝕋 m))
    (X : Zonotope (Vec 𝕋 n)) {f : Vec ℝ n → Vec ℝ m}
    (hf : ∀ x ∈ X.toSet, (fun i => f x i - (toRealMat M *ᵥ x) i) ∈ B.toSet) : -- --- CONCL ---
    X.Tracks ((Zonotope.mtimes M X).plus B.zonotope) f := by -- --- PROOF ---
  refine ⟨Nat.le_add_right _ _, fun β x hx => ?_⟩
  -- the box point, at weights of the box's zonotope
  obtain ⟨γ, hγ⟩ := Zonotope.mem_toSet_iff_containsAt.mp
    (Interval.zonotope_contains B (hf x (Zonotope.mem_toSet_iff_containsAt.mpr ⟨β, hx⟩)))
  refine ⟨Fin.append β γ, fun j => Fin.append_left β γ j, ?_⟩
  convert Zonotope.containsAt_plus (Zonotope.containsAt_mtimes M hx) hγ using 1
  funext i
  simp

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
