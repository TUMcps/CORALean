module

public import CORALean.ContSet.Conversion.Real.Interval_to_ConZonotope
public import CORALean.ContSet.Conversion.Real.Interval_to_PolyZonotope
public import CORALean.ContSet.Conversion.Real.Interval_to_Zonotope
public import CORALean.ContSet.ConZonotope.Real.Instances
public import CORALean.ContSet.Interval.Real.Instances
public import CORALean.ContSet.PolyZonotope.Real.Instances
public import CORALean.ContSet.Zonotope.Real.Instances

@[expose] public section

/-!
# Absorbing a box, asked for as a class

The pair where the target is any representation, and the counterpart of
`ContSet_to_Interval`. An algorithm needs it to put a computed box back into
whatever it is propagating — a bias vector, an approximation error — without
naming what that is.

Named for the source, alone among the conversions, the target having no name to
be called after.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open ContSet


-- ========================================  MAIN TYPE  ========================================= --

class OfInterval (S : ℕ → Type) [∀ n, ContSet (S n) (Vec ℝ n)] where
  ofInterval {n : ℕ} : Interval (Vec ℝ n) → S n
  ofInterval_outer {n : ℕ} (I : Interval (Vec ℝ n)) :
    construct I ⊆ construct (ofInterval I)

instance : OfInterval (fun n => Interval (Vec ℝ n)) where
  ofInterval I := I
  ofInterval_outer _ := subset_rfl

noncomputable instance : OfInterval 𝒵 where
  ofInterval I := I.zonotope
  ofInterval_outer I := Interval.zonotope_contains I

noncomputable instance : OfInterval (fun n => ConZonotope (Vec ℝ n)) where
  ofInterval I := I.conZonotope
  ofInterval_outer I := Interval.conZonotope_contains I

noncomputable instance : OfInterval 𝒫𝒵 where
  ofInterval I := I.polyZonotope
  ofInterval_outer I := Interval.polyZonotope_contains I

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
