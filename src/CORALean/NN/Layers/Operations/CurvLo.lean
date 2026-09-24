import CORALean.NN.Layers.Definitions.Enclosure

/-!
# The lower end a derivative bracket gives

`σ l - λ l + (lo - λ)(u - l)`, the lower end `sub_mul_bounds_of_deriv` gives `σ t - λ t` over
the box, rounded down. `(lo - λ)(u - l)` is a non-positive factor times a non-negative one, so
the *widest* second factor makes it smallest, which is why the width rounds up.
-/

-- Authors:       Tobias Ladner
-- Written:       03-September-2026
-- Last update:   23-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The lower end of `σ t - lam t` over the box, rounded down. -/
def Relaxation.curvLo (E : Enclosure 𝕋) (lo lam : 𝕋 → 𝕋 → 𝕋) (l u : 𝕋) : 𝕋 :=
  addDown (subDown (E.lo l) (mulUp (lam l u) l))
    (mulDown (subDown (lo l u) (lam l u)) (subUp u l))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
