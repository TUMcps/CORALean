import CORALean.ContDynamics.LinearSysDT.Operations.ErrMatFloat
import CORALean.ContSet.Zonotope.Float.Operations.MtimesIntervalMat
import CORALean.ContSet.Zonotope.Float.Operations.Mtimes
import CORALean.ContSet.Zonotope.Float.Operations.Plus
import CORALean.ContSet.Zonotope.Float.Operations.Point
import CORALean.ContSet.Zonotope.Float.Operations.Reduce

/-!
# The set-propagation observer, in floats

CORA's `observe_propagation`, [1, Eq. 6], in directed rounding: `S' = (A - L C) S ⊕ u ⊕ L y ⊕
(-L) V ⊕ W`, reduced to `order`, with the gain `L` a function of the zonotope it is applied to.
`A - L C` is the interval matrix `errMatFloat`, `L y` the product of `L` with the point `y`.
Soundness is `observePropagationFloat_outer`.

## References

* [1] M. Althoff. "Guaranteed State Estimation in CORA 2021". In Proc. of the 8th
      International Workshop on Applied Verification of Continuous and Hybrid Systems (ARCH21),
      EPiC Series in Computing, vol. 80, pp. 161-175, 2021.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n p : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `S k`, the set the observer holds for the state at step `k`. -/
def LinearSysDT.observePropagationFloat (sys : LinearSysDT 𝕋 n) (C : Mat 𝕋 p n)
    (gain : Zonotope (Vec 𝕋 n) → Mat 𝕋 n p) (order : ℕ) (W R₀ : Zonotope (Vec 𝕋 n))
    (V : Zonotope (Vec 𝕋 p)) (u : ℕ → Vec 𝕋 n) (y : ℕ → Vec 𝕋 p) : ℕ → Zonotope (Vec 𝕋 n)
  | 0 => R₀
  | k + 1 =>
    let S := sys.observePropagationFloat C gain order W R₀ V u y k
    let L := gain S                                                  -- the gain at this step
    let S' := (((((Zonotope.mtimesIntervalMat (LinearSysDT.errMatFloat sys.A L C) S).plus
      (Zonotope.point (u k))).plus (Zonotope.mtimes L (Zonotope.point (y k)))).plus
      (Zonotope.mtimes (fun i j => neg (L i j)) V)).plus W)          -- (6)
    S'.reduce order

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
