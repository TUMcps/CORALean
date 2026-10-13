import CORALean.ContDynamics.LinearSys.MatExp.Operations.CurvatureEnclosureFloat
import CORALean.ContDynamics.LinearSys.LinearSys
import CORALean.ContSet.Zonotope.Float.Instances

/-!
# `comb(H(t_k), H(t_{k+1})) ⊕ C` in floats: lines 8-9 of [1, Alg. 1], lines 27-28 of [1, Alg. 2]

The straight line between a `H(t_k)` and a set `H(t_{k+1})` holding the affine flow's value
one step on, widened by the float curvature enclosure `MatExp.curvatureEnclosure`, whose `G`
is `intervalConstCorrectionMatrix`. A point of `H(t_k)` flowing for any `τ ∈ [0, Δt]` is in it
(`affineWindowFloat_outer`) so long as `H(t_{k+1})` holds where that point is at `Δt`.
Eq. (22) takes `H(t_{k+1}) = [e^{AΔt}] H(t_k) ⊕ P^u(Δt)` (`affineTimeIntervalOuterFloat`),
Alg. 2's line 26 takes `[e^{At_{k+1}}] X₀ ⊕ P^u(t_{k+1})`, which is tighter.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of
      Linear Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE
      Transactions on Automatic Control, vol. 68, no. 12, 2023, pp. 7771–7786.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `Ĥ(τ_k) = comb(H(t_k), H(t_{k+1})) ⊕ C`, for a `H(t_{k+1})` given. -/
def LinearSys.affineWindowFloat (sys : LinearSys 𝕋 n) (H Hnext : Zonotope (Vec 𝕋 n)) (ũ : Vec 𝕋 n)
    (Δt : 𝕋) (η : ℕ) : Zonotope (Vec 𝕋 n) :=
  let C := MatExp.curvatureEnclosure (Interval.point sys.A) H ũ Δt η  -- C, eq. (15)-(16)
  LinComb.linComb H Hnext ⊞ C                                         -- comb(H, H(t_{k+1})) ⊕ C

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
