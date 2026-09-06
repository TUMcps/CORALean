import CORALean.ContSet.Conversion.Float.Interval_to_ConZonotope
import CORALean.ContSet.Conversion.Float.Interval_to_PolyZonotope
import CORALean.ContSet.Conversion.Float.Interval_to_Zonotope
import CORALean.ContSet.ConZonotope.Float.Instances
import CORALean.ContSet.Interval.Float.Instances
import CORALean.ContSet.PolyZonotope.Float.Instances
import CORALean.ContSet.Zonotope.Float.Instances

/-!
# Absorbing a box, over a floating-point scalar

The counterpart of `ContSet_to_Interval`, and what puts a computed box back into
whatever is being propagated: a bias vector, a relaxation's error, an
approximation error.

Nothing here rounds. The box arrives already in `𝕋`, and each conversion pays
whatever its own centring costs — `Interval.zonotope` measures its radius from
the centre it actually stored, so the box is covered by the generators alone.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

open ContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]

/-- Named for the source, alone among the conversions, the target having no name
to be called after. -/
class OfInterval (S : ℕ → Type) (𝕋 : outParam Type) [FloatOps 𝕋]
    [SoundFloatArithmetic 𝕋] [∀ n, ContSet (S n) (Vec ℝ n)] where
  ofInterval {n : ℕ} : Interval 𝕋 n → S n
  ofInterval_outer {n : ℕ} (I : Interval 𝕋 n) : construct I ⊆ construct (ofInterval I)

instance : OfInterval (fun n => Interval 𝕋 n) 𝕋 where
  ofInterval I := I
  ofInterval_outer _ := subset_rfl

instance : OfInterval (fun n => Zonotope 𝕋 n) 𝕋 where
  ofInterval I := I.zonotope
  ofInterval_outer I := Interval.subset_zonotope I

instance : OfInterval (fun n => ConZonotope 𝕋 n) 𝕋 where
  ofInterval I := I.conZonotope
  ofInterval_outer I := Interval.subset_conZonotope I

instance : OfInterval (fun n => PolyZonotope 𝕋 n) 𝕋 where
  ofInterval I := I.polyZonotope
  ofInterval_outer I := Interval.subset_polyZonotope I

end CORALean.Float
