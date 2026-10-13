module

public import CORALean.ContSet.HPolytope.Float.Operations.Eqs
public import CORALean.ContSet.HPolytope.Float.Operations.Intersection
public import CORALean.ContSet.HPolytope.Float.Operations.Lift

@[expose] public section

/-!
# `HPolytope.projectHighDim`, over a floating-point scalar

The halfspace form of CORA's `projectHighDim`, as over ℝ: `lift_` into the coordinates `dims`,
then one equality `xⱼ = 0` for each coordinate `dims` misses, as a unit row with the interval
right-hand side `[0, 0]`. Nothing rounds: the rows are copied, and `0` and `1` are exact.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n N : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def HPolytope.projectHighDim (P : HPolytope 𝕋 (Vec 𝕋 n)) (dims : Fin n → Fin N) : HPolytope
    𝕋 (Vec 𝕋 N) :=
  -- the coordinates `dims` leaves out
  let new := Finset.univ.filter fun j : Fin N => ∀ k, dims k ≠ j
  (P.lift_ dims).intersection
    (HPolytope.eqs (fun r j => if j = new.orderEmbOfFin rfl r then one else zero)
      ⟨fun _ => zero, fun _ => zero⟩)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
