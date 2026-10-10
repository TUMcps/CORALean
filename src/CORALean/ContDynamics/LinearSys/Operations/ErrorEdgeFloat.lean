import CORALean.ContDynamics.LinearSys.MatExp.Operations.IntervalInputTermFloat
import CORALean.ContDynamics.LinearSys.LinearSys
import CORALean.ContSet.Interval.Float.Operations.Point
import CORALean.ContSet.Zonotope.Float.Zonotope

/-!
# The generator sums of the error solution, in floats

`errorEdge` computed in `𝕋`: CORA's `RerrorInt_etanoF`, per coordinate `d` the sum over the
orders `i ≤ η` and the generators `G_j` of `|(Ãᵢ G_j)_d|`, the terms of [1, Prop. 11]. `Ãᵢ`
is the float box `intervalInputTerm`, so each term is bounded above by its entries' magnitudes
against `|G_j|`, every sum rounded up. A tuning quantity: `errorSolutionOrderFloat` reads it,
and the error solution it tunes is sound at any order.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of
      Linear Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE
      Transactions on Automatic Control, vol. 68, no. 12, 2023, pp. 7771–7786.
-/

-- Authors:       Tobias Ladner
-- Written:       08-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The edge length of the generator sum, per coordinate, up to order `η`, rounded up. -/
def LinearSys.errorEdgeFloat (sys : LinearSys 𝕋 n) (Δt : 𝕋) (V : Zonotope 𝕋 n) (η : ℕ) :
    Vec 𝕋 n :=
  let Ã := fun i : Fin (η + 1) => MatExp.intervalInputTerm (Interval.point sys.A) Δt i  -- [Ãᵢ]
  fun d => sumUp fun i : Fin (η + 1) => sumUp fun j : Fin V.h =>      -- Σᵢ Σⱼ
    sumUp fun k => mulUp (maximum (absolute ((Ã i).inf d k)) (absolute ((Ã i).sup d k)))
      (absolute (V.G j k))                                             -- ≥ |(Ãᵢ G_j)_d|

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
