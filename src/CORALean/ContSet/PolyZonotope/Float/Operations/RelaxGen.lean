import CORALean.ContSet.PolyZonotope.Float.Operations.RelaxWidth

/-!
# The new independent generator `relaxExp` stores

Split out of `RelaxExp.lean` (issue #62): read again by
`Theorems/RelaxExpOuter.lean`, outside this file.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n d : ℕ}

/-- The new independent generator as stored: `ξ_E` copies of the relaxed
generator, rounded down. -/
def PolyZonotope.relaxGen (PZ : PolyZonotope 𝕋 n)
    (part : Split (Fin PZ.h) into (Fin d) and (Fin 2)) (k₀ : Fin PZ.p) : Vec 𝕋 n :=
  fun i => nsmulDown (PZ.relaxWidth part k₀) (PZ.G i (part.right 0))

end CORALean.Float
