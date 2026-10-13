import CORALean.ContDynamics.LinearSys.Definitions.VerifySpecFloat
import CORALean.ContSet.ConZonotope.Float.Instances
import CORALean.ContSet.Zonotope.Float.Instances

/-!
# What float verification needs of its inputs

[1, Alg. 3] at the scalar `𝕋`: `reachFn ε` is an outer approximation of the exact reachable set
`Reach`, `innerApprox R ε` an inner one, and a distance's sign means containment in, or meeting
of, a polytope. The distances are read as the real values of stored floats; the comparison is the
scalar's own `le` and `ltStrict`, whose `true` is a proof, so no exactness is asked of them.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of
      Linear Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE
      Transactions on Automatic Control, vol. 68, no. 12, 2023, pp. 7771–7786.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ========================================  MAIN TYPE  ========================================= --

structure LinearSys.VerifySoundFloat (Reach : Set (Vec ℝ n)) (reachFn : 𝕋 → Zonotope (Vec 𝕋 n))
    (innerApprox : Zonotope (Vec 𝕋 n) → 𝕋 → ConZonotope 𝕋 (Vec 𝕋 n))
    (distG distF : ConZonotope 𝕋 (Vec 𝕋 n) → HPolytope 𝕋 (Vec 𝕋 n) → 𝕋) : Prop where
  outer (ε : 𝕋) : Reach ⊆ (reachFn ε).construct
  inner (R : Zonotope (Vec 𝕋 n)) (ε : 𝕋) : (innerApprox R ε).construct ⊆ Reach
  distG_nonpos (C : ConZonotope 𝕋 (Vec 𝕋 n)) (P : HPolytope 𝕋 (Vec 𝕋 n)) :
    toReal (distG C P) ≤ 0 → C.construct ⊆ P.construct
  distG_pos (C : ConZonotope 𝕋 (Vec 𝕋 n)) (P : HPolytope 𝕋 (Vec 𝕋 n)) :
    0 < toReal (distG C P) → ¬ C.construct ⊆ P.construct
  distF_pos (C : ConZonotope 𝕋 (Vec 𝕋 n)) (P : HPolytope 𝕋 (Vec 𝕋 n)) :
    0 < toReal (distF C P) → Disjoint C.construct P.construct
  distF_nonpos (C : ConZonotope 𝕋 (Vec 𝕋 n)) (P : HPolytope 𝕋 (Vec 𝕋 n)) :
    toReal (distF C P) ≤ 0 → ¬ Disjoint C.construct P.construct

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
