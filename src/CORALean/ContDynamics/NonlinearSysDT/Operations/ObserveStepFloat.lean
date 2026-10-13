import CORALean.ContDynamics.LinearSysDT.Definitions.ObserveStripOptionsFloat
import CORALean.ContDynamics.LinearSysDT.Operations.IntersectStripSeqFloat
import CORALean.ContDynamics.NonlinearSysDT.Instances
import CORALean.ContDynamics.NonlinearSysDT.Operations.Reach
import CORALean.ContSet.Zonotope.Float.Operations.IntersectStrip
import CORALean.ContSet.Zonotope.Float.Operations.Plus

/-!
# One step of the nonlinear strip-based observer, in floats

CORA's `observe_stripBased` [2, Eq. 4], [1, Alg. 1], one step, for a `nonlinearSysDT`: the
prediction is the system's `post`, here one step of `NonlinearSysDT.reach` at the certificate
`step` (linearization, widened input, reduction to `o`), plus the disturbance `W`; the update is
the strip of the measurement `y` of the linear output `C x` (CORA's `nlnsysDT.C`; `observe`
refuses an output that is not linear), the strips met together or one at a time as `options`
say. `U` is the input set the certificate is issued for (`params.U` with the known input
`uTrans` already added). Soundness is `observeStepFloat_outer`.

## References

* [1] V. T. H. Le, C. Stoica, T. Alamo, E. F. Camacho and D. Dumur. "Zonotopic guaranteed state
      estimation for uncertain systems". Automatica, 49(11):3418-3424, 2013.
* [2] M. Althoff. "Guaranteed State Estimation in CORA 2021". In Proc. of the 8th
      International Workshop on Applied Verification of Continuous and Hybrid Systems (ARCH21),
      EPiC Series in Computing, vol. 80, pp. 161-175, 2021.
-/

-- Authors:       Tobias Ladner
-- Written:       09-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m p : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The set the observer holds after the measurement `y`, from `Xhat` before it. -/
def NonlinearSysDT.observeStepFloat (sys : NonlinearSysDT n m) {U : Zonotope (Vec 𝕋 m)}
    (step : sys.LinStep (S := fun k => Zonotope (Vec 𝕋 k)) 𝕋 U) (o : NonlinearSysDT.ReachOptions)
    (C : Mat 𝕋 p n) (σ : Vec 𝕋 p)
    (W : Zonotope (Vec 𝕋 n)) (options : LinearSysDT.ObserveStripOptionsFloat 𝕋 n p) (y : Vec 𝕋 p)
    (Xhat : Zonotope (Vec 𝕋 n)) : Zonotope (Vec 𝕋 n) :=
  let Rpost := sys.reach (S := fun k => Zonotope (Vec 𝕋 k)) ⟨Xhat, U, 0, 1⟩ o  -- post(sys,Rnext,..)
    (fun _ => step)
  let Xbar := Rpost.plus W                                      -- Rnext.tp + params.W
  if options.sequential then LinearSysDT.intersectStripSeqFloat C σ y options.gain Xbar
  else Zonotope.intersectStrip C σ y (options.gain Xbar) Xbar     -- priv_observe_intersectionMethod

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
