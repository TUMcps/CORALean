import CORALean.ContDynamics.LinearSysDT.Definitions.BackReachExistsOptions
import CORALean.ContDynamics.LinearSysDT.LinearSysDT
import CORALean.ContDynamics.Reach.Definitions.InputParams

/-!
# Backward reachability in the `∃` reading, computed

`backReachSetExists`'s step at a representation: `plus` against the negated
input set, then `mtimes Ainv` for the preimage under `A`, taken as the image
under a left inverse the caller hands in as `options.Ainv`. `sys` is carried and never read — the
dynamics enter through `backReachExists_outer`'s `hA` alone.

Total, and with no operation parameter, where `backReachForall` is `Option`-
valued and takes `diff`: both steps here are the ordinary outer ones, `Plus`
and `Mtimes`, and neither can fail to certify what it returns.

`negU` is `params.U`, a set and not `-U`: no class here negates a set, and `Scalar` gives
`Mat 𝕋` no ring structure to build `-1` in. The caller supplies a representation
enclosing `-U`, which for a centrally symmetric input set is `U` itself.

No `reduce` in the loop, where `backReachForall` had nothing for one to bound:
`Zonotope.plus` appends generators, so at `Zonotope` the result does grow with
`k`. It is left out to keep what this asks for down to two classes.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   30-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar Plus Mtimes

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The computed backward reachable set in the `∃` reading: the negated input
set added on, then the image under `Ainv`. -/
def LinearSysDT.backReachExists (_sys : LinearSysDT 𝕋 n)
    (params : Reach.InputParams (S n) (S n) ℕ)
    (options : LinearSysDT.BackReachExistsOptions 𝕋 n) : S n :=
  let T := params.R0                                                -- the target
  let negU := params.U                                              -- the negated input set
  let Ainv := options.Ainv
  let N := params.tFinal - params.tStart                           -- steps, in sampling periods
  let rec P : ℕ → S n                                              -- P_k, the set k steps back
    | 0 => T
    | k + 1 => mtimes Ainv (plus (P k) negU)
  P N

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
