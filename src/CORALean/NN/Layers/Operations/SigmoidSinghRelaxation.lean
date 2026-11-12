module

public import CORALean.NN.Layers.Definitions.Relaxation
public import CORALean.NN.Layers.Operations.SigmoidDerivLo
public import CORALean.NN.Layers.Operations.SigmoidEnclosure

@[expose] public section

/-!
# The sigmoid relaxation by Singh's transformer

CORA's `nnSigmoidLayer` at `poly_method = 'singh'`, order 1 [1, Thm. 3.2]: the slope is the
smaller of the derivative at the two ends, here its lower bound `σ(x) σ(-x)` from below, and the
offset and error are the middle and the half-width of the range of `σ t - λ t`. The derivative
rises up to `0` and falls after it, so its smallest value on the box is at an end.

## Inputs
* `k` – reduction depth of the exponential

## Output
* relaxation of the sigmoid with Singh's slope

## References

* [1] [G. Singh, T. Gehr, M. Mirman, M. Püschel and M. Vechev. "Fast and Effective Robustness
      Certification". Advances in Neural Information Processing Systems,
      2018.](../../../../../references/2018/singh-neurips-deepz.md)
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       12-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Slope the smaller end derivative `λ`; offset and error the middle and the larger distance to
the ends of the range of `σ t - λ t`, each rounded to the outside. -/
def sigmoidSinghRelaxation (k : ℕ) : Relaxation 𝕋 where
  slope l u :=
    minimum (sigmoidDerivLo (sigmoidEnclosure k) l l) (sigmoidDerivLo (sigmoidEnclosure k) u u)
  offset l u :=
    -- σ l - λ l from below and σ u - λ u from above, the middle of the two
    let lam := minimum (sigmoidDerivLo (sigmoidEnclosure k) l l)
      (sigmoidDerivLo (sigmoidEnclosure k) u u)
    half (addUp (subDown ((sigmoidEnclosure k).enclose l).inf (mulUp lam l))
      (subUp ((sigmoidEnclosure k).enclose u).sup (mulDown lam u)))
  error l u :=
    let lam := minimum (sigmoidDerivLo (sigmoidEnclosure k) l l)
      (sigmoidDerivLo (sigmoidEnclosure k) u u)
    let lo := subDown ((sigmoidEnclosure k).enclose l).inf (mulUp lam l)
    let hi := subUp ((sigmoidEnclosure k).enclose u).sup (mulDown lam u)
    let mid := half (addUp lo hi)
    maximum (subUp hi mid) (subUp mid lo)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
