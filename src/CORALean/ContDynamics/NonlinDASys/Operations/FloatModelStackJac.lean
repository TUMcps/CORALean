module

public import CORALean.ContDynamics.NonlinDASys.Definitions.FloatModel
public import CORALean.ContSet.Interval.Float.Operations.Horzcat
public import CORALean.ContSet.Interval.Float.Operations.Basic

@[expose] public section

/-!
# A float model's slopes on the stacked state

The slope enclosure of `(f, g)` over a box `Z` of stacked states `z = (x, y)`, read as the box `X`
of its first `n` coordinates and the box `Y` of its last `p`: the block interval matrix
`[A C; D F]` of the model's four enclosures over `X × Y`.
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

/-- The slopes of `(f, g)` over a stacked box, `[A C; D F]`, at the input box `U`. -/
def NonlinDASys.FloatModel.stackJac (fm : NonlinDASys.FloatModel 𝕋 n p m)
    (U : Interval (Vec 𝕋 m)) (Z : Interval (Vec 𝕋 (n + p))) : Interval (Mat 𝕋 (n + p) (n + p)) :=
  let X : Interval (Vec 𝕋 n) := ⟨fun i => Z.inf (Fin.castAdd p i), fun i => Z.sup (Fin.castAdd p i)⟩
  let Y : Interval (Vec 𝕋 p) := ⟨fun j => Z.inf (Fin.natAdd n j), fun j => Z.sup (Fin.natAdd n j)⟩
  Interval.vertcat (Interval.horzcat (fm.jacA X Y U) (fm.jacC X Y U))
    (Interval.horzcat (fm.jacD X Y U) (fm.jacF X Y U))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
