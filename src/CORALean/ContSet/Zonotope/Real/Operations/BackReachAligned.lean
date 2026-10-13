import CORALean.ContSet.Zonotope.Real.Operations.Aligned
import CORALean.ContSet.Zonotope.Real.Operations.MinkDiffAligned
import CORALean.ContSet.Zonotope.Real.Operations.Plus
import CORALean.ContSet.Zonotope.Real.Operations.Mtimes
import CORALean.ContSet.Zonotope.Real.Operations.Shift
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# `Zonotope.backReachAligned`

[1, Eq. 12] with (11) and (13): zonotopes `Z_k` approximating the robust backward
reachable sets of `x⁺ = Ax + Bu + Ew + K` (`LinearSysDT.backReachSetRobust`), `Z₀` the target and
`Z_{k+1} = A⁻¹(Z_k ⊖ Z(Z_k, EW) ⊕ -BU - K)`. The subtrahend is aligned with `Z_k`, so
the difference is generator-wise ([1, Prop. 3]); its centre and scalings are what `σ`
returns at `Z_k`, the linear program's solution. (12) and (13) are this recursion with
two programs: (min-out), an aligned zonotope around `EW`, gives the inner `Z̲_k`, and
(max-in), one inside `EW`, the outer `Z̄_k`. `E` and `W` enter only through `σ`.
Real layer only, like `combineGens`: the inner half cannot absorb outward rounding.

## References

* [1] L. Yang and N. Ozay. "Scalable zonotopic under-approximation of backward
      reachable sets for uncertain linear systems". IEEE Control Systems Letters,
      6:1555-1560, 2022.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Eq. 12]: `Z_{k+1} = A⁻¹(Z_k ⊖ Z(Z_k, EW) ⊕ -BU - K)`, `Z(Z_k, EW)` aligned
with `Z_k` at the centre and scalings `σ Z_k`. -/
noncomputable def Zonotope.backReachAligned (A : Mat ℝ n n) (B : Mat ℝ n m) (K : Vec ℝ n)
    (U : Zonotope (Vec ℝ m)) (Z₀ : Zonotope (Vec ℝ n))
    (σ : (Z : Zonotope (Vec ℝ n)) → Vec ℝ n × (Fin Z.h → ℝ)) : ℕ → Zonotope (Vec ℝ n)
  | 0 => Z₀                                                      -- (11)
  | k + 1 =>
    let Zk := Zonotope.backReachAligned A B K U Z₀ σ k
    let cα := σ Zk                                               -- the program's solution
    let ZEW := Zk.aligned cα.1 cα.2                              -- Z(Z_k, EW)
    let D := Zk.minkDiffAligned ZEW rfl                          -- Z_k ⊖ Z(Z_k, EW)
    let S := D.plus (U.mtimes (-B))                              -- ⊕ -BU
    let T := S.shift K                                           -- - K
    T.mtimes A⁻¹                                                 -- A⁻¹(·), (12)-(13)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
