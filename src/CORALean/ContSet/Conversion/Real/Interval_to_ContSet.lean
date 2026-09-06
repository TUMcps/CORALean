import CORALean.ContSet.Conversion.Real.Interval_to_ConZonotope
import CORALean.ContSet.Conversion.Real.Interval_to_PolyZonotope
import CORALean.ContSet.Conversion.Real.Interval_to_Zonotope
import CORALean.ContSet.ConZonotope.Real.Instances
import CORALean.ContSet.Interval.Real.Instances
import CORALean.ContSet.PolyZonotope.Real.Instances
import CORALean.ContSet.Zonotope.Real.Instances

/-!
# Absorbing a box, asked for as a class

The pair where the target is any representation, and the counterpart of
`ContSet_to_Interval`. An algorithm needs it to put a computed box back into
whatever it is propagating — a bias vector, an approximation error — without
naming what that is.

Named for the source, alone among the conversions, the target having no name to
be called after.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open ContSet

class OfInterval (S : ℕ → Type) [∀ n, ContSet (S n) (Vec ℝ n)] where
  ofInterval {n : ℕ} : Interval (Vec ℝ n) → S n
  ofInterval_outer {n : ℕ} (I : Interval (Vec ℝ n)) :
    construct I ⊆ construct (ofInterval I)

instance : OfInterval (fun n => Interval (Vec ℝ n)) where
  ofInterval I := I
  ofInterval_outer _ := subset_rfl

noncomputable instance : OfInterval 𝒵 where
  ofInterval I := I.zonotope
  ofInterval_outer I := Interval.subset_zonotope I

noncomputable instance : OfInterval (fun n => ConZonotope (Vec ℝ n)) where
  ofInterval I := I.conZonotope
  ofInterval_outer I := Interval.subset_conZonotope I

noncomputable instance : OfInterval 𝒫𝒵 where
  ofInterval I := I.polyZonotope
  ofInterval_outer I := Interval.subset_polyZonotope I

end CORALean.Real
