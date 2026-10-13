module

public import CORALean.ContSet.HPolytope.Float.Theorems.MemConstruct

@[expose] public section

/-!
# `HPolytope.unitBox`, over a floating-point scalar

The supremum-norm unit ball as `2n` rows, `±xⱼ ≤ 1`. Every entry is `0`, `1` or
`-1`, all of which a format has exactly, so nothing rounds and the right-hand
side stays a point.

It is the coefficient domain a zonotope ranges over, which the constrained
zonotope keeps outside its `P`; an operation that weights the coefficients has
to put the two back together and reads the box from here.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

def HPolytope.unitBox (𝕋 : Type) [FloatOps 𝕋] (n : ℕ) : HPolytope 𝕋 (Vec 𝕋 n) where
  m := n + n
  A := Fin.append (fun j k => if j = k then one else zero)
        fun j k => if j = k then neg one else zero
  b := fun _ => one
  me := 0
  Ae := fun i => i.elim0
  be := ⟨fun i => i.elim0, fun i => i.elim0⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
