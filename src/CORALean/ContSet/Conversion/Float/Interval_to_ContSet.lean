module

public import CORALean.ContSet.Conversion.Float.Interval_to_ConZonotope
public import CORALean.ContSet.Conversion.Float.Interval_to_PolyZonotope
public import CORALean.ContSet.Conversion.Float.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Interval_to_ContSet
public import CORALean.ContSet.ConZonotope.Float.Instances
public import CORALean.ContSet.Interval.Float.Instances
public import CORALean.ContSet.PolyZonotope.Float.Instances
public import CORALean.ContSet.Zonotope.Float.Instances
public import CORALean.Global.Float.Instances.Real.Instances

@[expose] public section

/-!
# Absorbing a box, over a floating-point scalar

The counterpart of `ContSet_to_Interval`, and what puts a computed box back into
whatever is being propagated: a bias vector, a relaxation's error, an
approximation error.

Nothing here rounds. The box arrives already in `𝕋`, and each conversion pays
whatever its own centring costs — `Interval.zonotope` measures its radius from
the centre it actually stored, so the box is covered by the generators alone.

An exact representation is one at `𝕋 := ℝ`, through its own class, as in
`ContSet_to_Interval`.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open ContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- ========================================  MAIN TYPE  ========================================= --

/-- Named for the source, alone among the conversions, the target having no name
to be called after. -/
class OfInterval (S : ℕ → Type) (𝕋 : outParam Type) [FloatOps 𝕋]
    [SoundFloatArithmetic 𝕋] [∀ n, ContSet (S n) (Vec ℝ n)] where
  ofInterval {n : ℕ} : Interval (Vec 𝕋 n) → S n
  ofInterval_outer {n : ℕ} (I : Interval (Vec 𝕋 n)) : construct I ⊆ construct (ofInterval I)

instance : OfInterval (fun n => Interval (Vec 𝕋 n)) 𝕋 where
  ofInterval I := I
  ofInterval_outer _ := subset_rfl

instance : OfInterval (fun n => Zonotope (Vec 𝕋 n)) 𝕋 where
  ofInterval I := I.zonotope
  ofInterval_outer I := Interval.zonotope_contains I

instance : OfInterval (fun n => ConZonotope 𝕋 (Vec 𝕋 n)) 𝕋 where
  ofInterval I := I.conZonotope
  ofInterval_outer I := Interval.conZonotope_contains I

instance : OfInterval (fun n => PolyZonotope (Vec 𝕋 n)) 𝕋 where
  ofInterval I := I.polyZonotope
  ofInterval_outer I := Interval.polyZonotope_contains I

/-- An exact representation absorbs a box at `𝕋 := ℝ` through its exact class, the box's
bounds being real already. -/
instance {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [Real.OfInterval S] :
    OfInterval S ℝ where
  ofInterval I := Real.OfInterval.ofInterval ⟨I.inf, I.sup⟩
  ofInterval_outer I := Real.OfInterval.ofInterval_outer ⟨I.inf, I.sup⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
