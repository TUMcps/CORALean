import CORALean.ContDynamics.LinearSysDT.Definitions.ObserveStripOptionsFloat
import CORALean.ContDynamics.LinearSysDT.Operations.IntersectStripSeqFloat
import CORALean.ContSet.Zonotope.Float.Operations.Mtimes
import CORALean.ContSet.Zonotope.Float.Operations.Plus
import CORALean.ContSet.Zonotope.Float.Operations.Point

/-!
# One step of the strip-based observer, in floats

CORA's `observe_stripBased` [2, Eq. 4], [1, Alg. 1], one step: the prediction `X̄ = A X̂ ⊕ u ⊕ W`
and its update by the strip of the measurement, in directed rounding, with the strips met together
or one at a time as `options` say. Soundness is `observeStepFloat_outer`.

## References

* [1] V. T. H. Le, C. Stoica, T. Alamo, E. F. Camacho and D. Dumur. "Zonotopic guaranteed state
      estimation for uncertain systems". Automatica, 49(11):3418-3424, 2013.
* [2] M. Althoff. "Guaranteed State Estimation in CORA 2021". In Proc. of the 8th
      International Workshop on Applied Verification of Continuous and Hybrid Systems (ARCH21),
      EPiC Series in Computing, vol. 80, pp. 161-175, 2021.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n p : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def LinearSysDT.observeStepFloat (sys : LinearSysDT 𝕋 n) (C : Mat 𝕋 p n) (σ : Vec 𝕋 p)
    (W : Zonotope (Vec 𝕋 n)) (options : LinearSysDT.ObserveStripOptionsFloat 𝕋 n p) (u : Vec 𝕋 n)
    (y : Vec 𝕋 p) (Xhat : Zonotope (Vec 𝕋 n)) : Zonotope (Vec 𝕋 n) :=
  let Xbar := (Zonotope.plus (Zonotope.mtimes sys.A Xhat) (Zonotope.point u)).plus W  -- Step 1, X̄
  if options.sequential then LinearSysDT.intersectStripSeqFloat C σ y options.gain Xbar
  else Zonotope.intersectStrip C σ y (options.gain Xbar) Xbar     -- Step 2, update X̂_k

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
