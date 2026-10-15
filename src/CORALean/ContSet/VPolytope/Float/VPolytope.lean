module

public import CORALean.ContSet.InflatedContSet.InflatedContSet
public import CORALean.ContSet.VPolytope.Real.Instances
public import CORALean.ContSet.VPolytope.Real.Theorems.PerturbSubset

@[expose] public section

/-!
# Vertex descriptions over a floating-point scalar: the representation

CORA's `polytope` with `isVRep` set, its vertices held in `𝕋`, plus the error box
that makes it an `InflatedContSet`.

The box is the only sound place to pay. Rounding a vertex moves a point, and
there is no direction to move it that enlarges the hull — a hull has no centre
to move away from — so what rounding costs cannot be absorbed into the vertices
the way an interval absorbs it into its bounds.

`VPolytope α` is generic over its ambient type, vertices a family, as the exact
layer's `VPolytope α` is; `VPolytope (Vec 𝕋 n)` is the vector case, and the
nominal reading copies the family.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   14-October-2026
-- Reviewed:      15-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- ========================================  MAIN TYPE  ========================================= --

structure VPolytope (α : Type) where
  k : ℕ
  V : Fin k → α
  I_error : Interval α

/-- The exact vertex list the stored floats describe, read through `RealImage`. -/
protected abbrev VPolytope.nominal {α β : Type} [RealImage α β] (P : VPolytope α) :
    CORALean.Real.VPolytope β :=
  ⟨P.k, fun l => RealImage.realImage (P.V l)⟩

instance {α β : Type} [RealImage α β] [AddCommGroup β] [Module ℝ β] :
    InflatedContSet (VPolytope α) (CORALean.Real.VPolytope β) α β where
  nominal := VPolytope.nominal
  I_error P := P.I_error

/-- Inherited from `InflatedContSet`; named here so statements read locally. -/
abbrev VPolytope.construct [SoundFloatArithmetic 𝕋] (P : VPolytope (Vec 𝕋 n)) : Set (Vec ℝ n) :=
  InflatedContSet.construct P

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
