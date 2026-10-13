import CORALean.ContDynamics.LinearSysDT.Definitions.BackReachForallOptions
import CORALean.ContDynamics.LinearSysDT.LinearSysDT
import CORALean.ContDynamics.Reach.Definitions.InputParams

/-!
# Backward reachability, computed

`backReachSetForall`'s two steps at a representation: `diff` for the Minkowski
difference, and `mtimes Ainv` for the preimage under `A`, taken as the image
under a right inverse the caller hands in. `sys` is carried and never read —
the dynamics enter through `backReachForall_inner`'s `hA` alone.

`diff` is an option rather than the `MinkDiff` class because `Zonotope` has
no instance of it and can have none: a zonotope difference exists only at a
checked generator representation, so `Zonotope.minkDiffRep` is `Option`-valued
and a total `minkDiff : S → S → S` has nowhere to fail. This is `Option`-valued
for that reason, and `none` is what an implementation returns where it cannot
certify a subset — never a set it has not earned.

No `reduce` in the loop, and so no `0 < o`: at `Zonotope` the count never grows
— `minkDiffRep` keeps the minuend's generators and `mtimes` keeps them — so an
order would have nothing to bound.
-/

-- Authors:       Claude Sonnet 5
-- Written:       07-September-2026
-- Last update:   30-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar Mtimes

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The computed backward reachable set: `diff` against the input set, then the
image under `Ainv`, and `none` as soon as `diff` cannot certify a step. -/
def LinearSysDT.backReachForall (_sys : LinearSysDT 𝕋 n)
    (params : Reach.InputParams (S n) (S n) ℕ)
    (options : LinearSysDT.BackReachForallOptions 𝕋 S n) : Option (S n) :=
  let T := params.X₀                                                -- the target
  let U := params.U
  let Ainv := options.Ainv
  let diff := options.diff
  let N := params.tFinal - params.tStart                           -- steps, in sampling periods
  let rec P : ℕ → Option (S n)                                     -- P_k, the set k steps back
    | 0 => some T
    | k + 1 => (P k).bind fun Pk => (diff Pk U).map (mtimes Ainv)
  P N

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
