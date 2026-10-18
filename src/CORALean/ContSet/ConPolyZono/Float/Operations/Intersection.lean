module

public import CORALean.ContSet.ConPolyZono.Float.Operations.IntersectionDep
public import CORALean.ContSet.ConPolyZono.Float.Operations.Dependent

@[expose] public section

/-!
# `ConPolyZono.intersection`

The operation the representation exists for. Here a set is a nominal one plus an error box, so
the two points that have to agree are `y₁ + e₁` and `y₂ + e₂`, and it is the *nominal* points
the rows can speak about. Those differ by `e₂ - e₁`, which the two boxes bound, so the rows say
the nominal points agree only to within

  `c₂ − c₁ + [err₂.inf − err₁.sup, err₂.sup − err₁.inf]`,

each end rounded away from the other, so the rounding of `c₂ − c₁` costs nothing extra. Only
that interval is computed, and it is recorded as a right-hand side with its slack: the lower end
as `b`, the width above it, rounded up, as `b_error`, which reads it as `[lo, 2 hi − lo]`.

The result keeps `cPZ₁`'s error box and only `cPZ₁`'s generator block: the point it
denotes is `y₁ + e₁`, and `cPZ₂` enters through the constraint system alone, its
generator columns kept at `zero` so the agreement rows can read the second point.
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       03-September-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ConPolyZono.intersection (cPZ₁ cPZ₂ : ConPolyZono 𝕋 (Vec 𝕋 n)) : ConPolyZono 𝕋 (Vec 𝕋 n) :=
  ConPolyZono.intersectionDep cPZ₁.dependent cPZ₂.dependent

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
