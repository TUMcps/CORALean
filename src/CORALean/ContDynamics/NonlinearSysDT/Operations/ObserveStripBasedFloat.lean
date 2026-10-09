import CORALean.ContDynamics.NonlinearSysDT.Operations.ObserveStepFloat
import CORALean.ContSet.Zonotope.Float.Operations.Reduce

/-!
# The nonlinear strip-based observer, in floats

CORA's `observe_stripBased` [2, Eq. 4], [1, Alg. 1] for a `nonlinearSysDT`, run over the
measurements `y 0, y 1, …`: `R k` is the set after the measurement `y k`, each step the
prediction and update of `observeStepFloat` at the linearization `steps k`, then reduced to
`options.zonotopeOrder`. CORA's estimators `VolMin-A`, `VolMin-B`, `FRad-A`, `FRad-B` and
`FRad-C` of `executeObserver` are this loop at their own intersection technique (the gain); the
enclosure holds for every gain. Soundness is `observeStripBasedFloat_outer`.

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

/-- `R k`, the set the observer holds after the measurement `y k`. -/
def NonlinearSysDT.observeStripBasedFloat (sys : NonlinearSysDT n m) {U : Zonotope 𝕋 m}
    (steps : ℕ → sys.LinStep 𝕋 U) (o : NonlinearSysDT.ReachOptions) (C : Mat 𝕋 p n)
    (σ : Vec 𝕋 p) (W R₀ : Zonotope 𝕋 n) (y : ℕ → Vec 𝕋 p)
    (options : LinearSysDT.ObserveStripOptionsFloat 𝕋 n p) : ℕ → Zonotope 𝕋 n
  | 0 =>
    if options.sequential then LinearSysDT.intersectStripSeqFloat C σ (y 0) options.gain R₀
    else Zonotope.intersectStrip C σ (y 0) (options.gain R₀) R₀
  | k + 1 =>
    (sys.observeStepFloat (steps k) o C σ W options (y (k + 1))
      (sys.observeStripBasedFloat steps o C σ W R₀ y options k)).reduce options.zonotopeOrder

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
