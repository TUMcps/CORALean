module

public import CORALean.ContSet.Conversion.Real.Operations.Ellipsoid_to_ConPolyZono
public import CORALean.ContSet.ConPolyZono.Float.ConPolyZono
public import CORALean.ContSet.Ellipsoid.Float.Ellipsoid
public import CORALean.ContSet.Ellipsoid.Float.Operations.BoxRadius
public import CORALean.ContSet.Ellipsoid.Float.Operations.IsOuterFactor
public import CORALean.ContSet.Ellipsoid.Float.Operations.OuterFactor
public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.InflatedContSet.Theorems.MonoSubset

@[expose] public section

/-!
# An ellipsoid as a constrained polynomial zonotope, over a floating-point scalar

CORA's construction with its factor `G = V √D` of `Q` replaced by `outerFactor`, a factor from
above that `isOuterFactor` certifies (`G Gᵀ ⪰ Q`): the constraint entries `one`, `neg (half one)`
and the point `half one` are stored exactly, and the center is copied. Where the factor is not
certified, the generators are zero and the ellipsoid's box `q ± sqrt(diag(Q))` joins the error box.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Ellipsoid.conPolyZono (E : Ellipsoid 𝕋 n) : ConPolyZono 𝕋 (Vec 𝕋 n) :=
  -- a factor of `Q` from above, certified or replaced by `0`
  let G₀ : Mat 𝕋 n n := Ellipsoid.outerFactor E.Q
  let ok : Bool := Ellipsoid.isOuterFactor E.Q G₀
  let G : Mat 𝕋 n n := if ok then G₀ else fun _ _ => zero
  { p := n + 1
    h := n
    qI := 0
    m := 1
    q := n + 1
    c := E.q
    -- the factor's columns are the dependent generators
    G := fun l i => G i l
    E := Real.ConPolyZono.padE (Real.PolyZonotope.identE n) 1
    GI := Fin.elim0
    A := fun _ j => if j.val < n then one else neg (half one)
    b := ⟨fun _ => half one, fun _ => half one⟩
    R := fun r c => if r = c then (if c.val < n then 2 else 1) else 0
    I_error := if ok then E.I_error
      else E.I_error.plus (Interval.symmetric (Ellipsoid.boxRadius 64 E)) }

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
