module

public import CORALean.ContDynamics.LinearSysDT.Definitions.BackReachExistsOptions
public import CORALean.ContDynamics.LinearSysDT.LinearSysDT
public import CORALean.ContDynamics.Reach.Definitions.InputParams

@[expose] public section

/-!
# Backward reachability in the `∃` reading, computed

`backReachSetExistsExact`'s step at a representation: `plus` against the negated input set, then
`mtimes Ainv` for the preimage under `A`, taken as the image under a left inverse the caller hands
in as `options.Ainv`. `sys` is carried and never read — the dynamics enter through
`backReachExists_outer`'s `hA` alone. Total, where `backReachForall` is `Option`-valued and takes
`diff`: both steps are the ordinary outer ones. `negU` is `params.U`, a set and not `-U`: no class
here negates a set. The caller supplies a representation enclosing `-U`, which for a centrally
symmetric input set is `U` itself. No `reduce` in the loop: `Zonotope.plus` appends generators, so
the result grows with `k`, left out to keep what this asks for down to two classes.

## Inputs
* `_sys` – system
* `params` – reachability parameters with inputs
* `options` – backward reachability options

## Output
* the computed backward reachable set
-/

-- Authors:       Claude Sonnet 5
-- Written:       07-September-2026
-- Last update:   30-September-2026
-- Reviewed:      ---


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
  let T := params.X₀                                                -- the target
  let negU := params.U                                              -- the negated input set
  let Ainv := options.Ainv
  let N := params.tFinal - params.tStart                           -- steps, in sampling periods
  let rec P : ℕ → S n                                              -- P_k, the set k steps back
    | 0 => T
    | k + 1 => mtimes Ainv (plus (P k) negU)
  P N

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
