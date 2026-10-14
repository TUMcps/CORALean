module

public import CORALean.ContDynamics.LinearSys.Operations.ExpIntervalFloat
public import CORALean.ContSet.Conversion.Float.Interval_to_HPolytope
public import CORALean.ContSet.Interval.Float.Operations.MatPlus
public import CORALean.ContSet.Zonotope.Float.Zonotope
public import CORALean.Global.Float.Sqrt

@[expose] public section

/-!
# `Alg. 3` line 3 in floats: the curvature radius `μ`

`maxBackReachMu` computed in `𝕋`: [1, Alg. 3] line 3, `μ ← √γ ‖(e^{AΔt} - I_n)G‖₂`, rounded
**up**. `μ` is the radius of the ball `B_μ` that line 4 and 5 subtract, so a larger one only
shrinks the polytope: the direction is the exact layer's `⊆`, an inner approximation.

The spectral norm has no closed form in floats, so it is bounded by the Frobenius norm,
`‖M‖₂ ≤ ‖M‖_F`, of an entrywise magnitude bound on the product: `[e^{AΔt}] - I` from
`expIntervalFloat`, each entry taken at the larger of its two bounds' magnitudes, times the
magnitudes of `G`, all rounded up; `√γ` and the root are `sqrtUp`.

## References

* [1] M. Wetzlinger and M. Althoff. "Backward Reachability Analysis of Perturbed
      Continuous-Time Linear Systems Using Set Propagation". IEEE Transactions on
      Automatic Control, 71(1):352-367, 2026.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Line 3: `μ ← √γ ‖(e^{AΔt} - I_n)G‖₂`, an upper bound; `G` and `γ` from `box(X_end)`, `B`.
`η` is the Taylor order of the exponential's enclosure and `p` the Newton steps of each root. -/
def LinearSys.maxBackReachMuFloat (sys : LinearSys 𝕋 n) (Δt : 𝕋) (η p : ℕ)
    (B : Zonotope (Vec 𝕋 n)) : 𝕋 :=
  let EI := Interval.matPlus (sys.expIntervalFloat Δt Δt η)         -- [e^{AΔt}] - I
    (Interval.point (negIdentityMat 𝕋 n))
  let mag : Mat 𝕋 n n := fun i k =>                                 -- |e^{AΔt} - I|, entrywise
    maximum (absolute (EI.inf i k)) (absolute (EI.sup i k))
  let m : Mat 𝕋 n B.h := fun i j =>                                 -- |(e^{AΔt} - I)G|, entrywise
    sumUp fun k => mulUp (mag i k) (absolute (B.G j k))
  let frobSq := sumUp fun i => sqSumUp (m i)                        -- ‖(e^{AΔt} - I)G‖_F², up
  mulUp (sqrtUp p (nsmulUp B.h one)) (sqrtUp p frobSq)              -- √γ ‖·‖_F

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
