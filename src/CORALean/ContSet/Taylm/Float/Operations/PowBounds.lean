module

public import CORALean.ContSet.Taylm.Float.Taylm
public import CORALean.ContSet.Interval.Float.Operations.Power

@[expose] public section

/-!
# `Taylm.powBounds`, over a floating-point scalar

The range of `t ^ k` over `[l, u]`, by the float interval power `Interval.power` at one coordinate
(every end rounded outward). `Interval.power` acts on a box `Interval (Vec 𝕋 n)`, so the scalar
interval `[l, u]` is wrapped as a box of one coordinate and read back at coordinate `0`: `P` itself
has the type `Interval (Vec 𝕋 1)`, not the `Interval 𝕋` that `Taylm.prodBounds` multiplies, so
returning it directly does not typecheck. The two ends are those of `P`, nothing else is changed.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   14-October-2026
-- Reviewed:      19-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The range of `t ^ k` over `[l, u]`: the ends of `Interval.power` of the one-coordinate box. -/
def Taylm.powBounds (l u : 𝕋) (k : ℕ) : Interval 𝕋 :=
  let P : Interval (Vec 𝕋 1) := Interval.power ⟨fun _ => l, fun _ => u⟩ k
  ⟨P.inf 0, P.sup 0⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
