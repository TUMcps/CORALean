import CORALean.ContDynamics.LinearSys.LinearSys
import CORALean.ContSet.Conversion.Real.Interval_to_Zonotope
import CORALean.ContSet.Conversion.Real.Zonotope_to_Interval
import CORALean.ContSet.Conversion.Real.Zonotope_to_ZonoBundle
import CORALean.ContSet.ZonoBundle.Real.Operations.Mtimes
import CORALean.ContSet.ZonoBundle.Real.Operations.Plus
import CORALean.ContSet.Zonotope.Real.Operations.Mtimes
import CORALean.ContSet.Zonotope.Real.Operations.Plus

/-!
# `bundleReach`: [1, Alg. 1]

Reachable sets `R_k ⊇ R([t_k, t_{k+1}])`, `t_k = k r`, of `x' = Ax + u` on zonotope bundles, by
the superposition principle: from `R^h_0 ⊇ R^h([0, t_1])` (the homogeneous solution, a bundle)
and `R^i_0 ⊇ R^i([0, t_1])` (the input solution), `R^h_k = e^{Ar}R^h_{k-1}`,
`R^i_k = e^{Ar}R^i_{k-1}`, `P_k = P_{k-1} ⊕ box(R^i_k)`, `R_k = R^h_k ⊕ P_k`, one `let` per line.

The input solution is a zonotope: Sec. IV of [1] restricts `U` to zonotopes, and every set the
input part passes through is a linear image of `R^i_0` or a box, so nothing makes it a bundle.
`box` is `Zonotope.interval` read back as a zonotope, and `R^h_k ⊕ P_k` is the sum of a bundle
and a one-member bundle, [1, Prop. 2]. The listing's first two inputs are what a first step
computes; they are arguments here, held to enclosing `R^h([0, t_1])` and `R^i([0, t_1])` by the
soundness theorem. No float refinement: the step is the exact `e^{Ar}`.

## References

* [1] M. Althoff and B. H. Krogh. "Zonotope Bundles for the Efficient Computation of
      Reachable Sets". In Proc. of the 50th IEEE Conference on Decision and Control and
      European Control Conference (CDC-ECC), pp. 6814-6821, 2011.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix Scalar NormedSpace

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 1]: `R_0, ..., R_N` from `R^h_0` and `R^i_0`, propagated by `e^{Ar}`. -/
noncomputable def LinearSys.bundleReach (sys : LinearSys 𝕋 n) (Rh₀ : ZonoBundle (Vec ℝ n))
    (Ri₀ : Zonotope (Vec ℝ n)) (r : ℝ) (N : ℕ) : List (ZonoBundle (Vec ℝ n)) :=
  let E := exp (r • toRealMat sys.A)
  let P₀ := Ri₀.interval.zonotope
  let R₀ := Rh₀.plus P₀.zonoBundle
  ((List.range N).foldl
    (fun (S : (ZonoBundle (Vec ℝ n) × Zonotope (Vec ℝ n) × Zonotope (Vec ℝ n))
        × List (ZonoBundle (Vec ℝ n))) _ =>
      let Rhₖ := S.1.1.mtimes E
      let Riₖ := S.1.2.1.mtimes E
      let Pₖ := S.1.2.2.plus Riₖ.interval.zonotope
      let Rₖ := Rhₖ.plus Pₖ.zonoBundle
      ((Rhₖ, Riₖ, Pₖ), S.2 ++ [Rₖ]))
    ((Rh₀, Ri₀, P₀), [R₀])).2

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
