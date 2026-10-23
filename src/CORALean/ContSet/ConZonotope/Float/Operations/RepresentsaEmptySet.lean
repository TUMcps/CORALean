module

public import CORALean.ContSet.ConZonotope.Float.Operations.BoundDotWeights
public import CORALean.ContSet.HPolytope.Float.Operations.EmptyWeights
public import CORALean.ContSet.HPolytope.Real.Operations.RowLin
public import CORALean.Global.Float.SoundFloatArithmetic

@[expose] public section

/-!
# `ConZonotope.representsa_emptySet`, over a floating-point scalar

CORA decides emptiness with a linear program. Here the program's dual certificate is the one
`ConZonotope.boundDotWeights` checks, asked for the zero direction: weights on the constraint
rows, proposed by the exact simplex at ℚ on the margin program (`HPolytope.emptyWeights`) and
verified in rounded arithmetic, bound `0ᵀβ` above by the combination of the right-hand sides, and
a certified negative bound (`ltStrict`) leaves no point (Farkas). One-sided: `true` proves the set
empty; `false` decides nothing, a nonempty set and an exhausted simplex budget alike.

## Inputs
* `cZ` – float constrained zonotope

## Output
* whether emptiness is certified
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ConZonotope.representsa_emptySet (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) : Bool :=
  let w := cZ.P.emptyWeights
  ltStrict (cZ.boundDotWeights
    (c := Real.HPolytope.rowLin (toRealMat (fun (_ : Fin 1) => fun (_ : Fin n) => (zero : 𝕋))) 0)
    (fun _ => zero) (fun _ => rfl) w.1 w.2.1 w.2.2).val zero

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
