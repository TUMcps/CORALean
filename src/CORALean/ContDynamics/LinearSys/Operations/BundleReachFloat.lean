module

public import CORALean.ContDynamics.LinearSys.Operations.ExpIntervalFloat
public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_Interval
public import CORALean.ContSet.Conversion.Float.Operations.Basic
public import CORALean.ContSet.ZonoBundle.Float.Instances
public import CORALean.ContSet.Zonotope.Float.Instances
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval

@[expose] public section

/-!
# `bundleReach` over floats: [1, Alg. 1]

`bundleReach` computed in `𝕋`, on float zonotope bundles. The one number the exact layer takes
from the reals is `e^{Ar}`; here it is `[e^{Ar}]`, the order-`η` interval-matrix enclosure
`expIntervalFloat`, and every product with it is a bundle (or zonotope) times an interval
matrix. `box` is `Zonotope.interval` read back as a zonotope, and `R^h_k ⊕ P_k` is the sum of a
bundle and a one-member bundle, as over `ℝ`; one `let` per line of the listing.

## References

* [1] M. Althoff and B. H. Krogh. "Zonotope Bundles for the Efficient Computation of
      Reachable Sets". In Proc. of the 50th IEEE Conference on Decision and Control and
      European Control Conference (CDC-ECC), pp. 6814-6821, 2011.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 1] in floats: `R_0, ..., R_N` from `R^h_0` and `R^i_0`, propagated by `[e^{Ar}]`. -/
def LinearSys.bundleReachFloat (sys : LinearSys 𝕋 n) (Rh₀ : ZonoBundle (Vec 𝕋 n))
    (Ri₀ : Zonotope (Vec 𝕋 n)) (r : 𝕋) (η N : ℕ) : List (ZonoBundle (Vec 𝕋 n)) :=
  let E := sys.expIntervalFloat r r η
  -- 1. P₀ = box(R^i_0)
  let P₀ := Ri₀.interval.zonotope
  -- 2. R_0 = R^h_0 ⊕ P_0
  let R₀ := Plus.plus Rh₀ P₀.zonoBundle
  -- 3. for k = 1 … N
  ((List.range N).foldl
    (fun (S : (ZonoBundle (Vec 𝕋 n) × Zonotope (Vec 𝕋 n) × Zonotope (Vec 𝕋 n)) × List
      (ZonoBundle (Vec 𝕋 n))) _ =>
      -- 4. R^h_k = e^{Ar} R^h_{k-1}
      let Rhₖ := Mtimes.mtimes (𝕄 := ℐ[𝕋])
        (S := 𝒵ℬ[𝕋]) E S.1.1
      -- 5. R^i_k = e^{Ar} R^i_{k-1}
      let Riₖ := Mtimes.mtimes (𝕄 := ℐ[𝕋])
        (S := 𝒵[𝕋]) E S.1.2.1
      -- 6. P_k = P_{k-1} ⊕ box(R^i_k)
      let Pₖ := Plus.plus S.1.2.2 Riₖ.interval.zonotope
      -- 7. R_k = R^h_k ⊕ P_k
      let Rₖ := Plus.plus Rhₖ Pₖ.zonoBundle
      ((Rhₖ, Riₖ, Pₖ), S.2 ++ [Rₖ]))
    ((Rh₀, Ri₀, P₀), [R₀])).2

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
