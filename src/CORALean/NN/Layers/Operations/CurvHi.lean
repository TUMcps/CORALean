module

public import CORALean.NN.Layers.Definitions.Enclosure

@[expose] public section

/-!
# The upper end a derivative bracket gives

`σ l - λ l + (hi - λ)(u - l)`, rounded up. Both factors of `(hi - λ)(u - l)` are non-negative,
so the widest box makes the product largest, and the width rounds up here too.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The upper end of `σ t - lam t` over the box, rounded up. -/
def Relaxation.curvHi (E : Enclosure 𝕋) (hi lam : 𝕋 → 𝕋 → 𝕋) (l u : 𝕋) : 𝕋 :=
  addUp (subUp (E.hi l) (mulDown (lam l u) l))
    (mulUp (subUp (hi l u) (lam l u)) (subUp u l))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
