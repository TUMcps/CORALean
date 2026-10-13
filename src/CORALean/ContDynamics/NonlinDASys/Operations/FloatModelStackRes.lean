import CORALean.ContDynamics.NonlinDASys.Definitions.FloatModel
import CORALean.ContSet.Interval.Float.Operations.Append

/-!
# A float model's residual on the stacked state

`steadyState` solves `f = 0`, `g = 0` together in `z = (x, y)`, stacked as `Vec 𝕋 (n + p)`. A box
`Z` of stacked states is read as the box `X` of its first `n` coordinates and the box `Y` of its
last `p`, and `(f, g)` is enclosed over it by appending the model's two enclosures over `X × Y`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n p m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `(f, g)` over a stacked box, at the input box `U`. -/
def NonlinDASys.FloatModel.stackRes (fm : NonlinDASys.FloatModel 𝕋 n p m)
    (U : Interval (Vec 𝕋 m)) (Z : Interval (Vec 𝕋 (n + p))) : Interval (Vec 𝕋 (n + p)) :=
  let X : Interval (Vec 𝕋 n) := ⟨fun i => Z.inf (Fin.castAdd p i), fun i => Z.sup (Fin.castAdd p i)⟩
  let Y : Interval (Vec 𝕋 p) := ⟨fun j => Z.inf (Fin.natAdd n j), fun j => Z.sup (Fin.natAdd n j)⟩
  Interval.append (fm.f X Y U) (fm.g X Y U)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
