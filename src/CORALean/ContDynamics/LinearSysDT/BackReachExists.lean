import CORALean.ContDynamics.LinearSysDT.LinearSysDT

/-!
# Backward reachability in the `∃` reading, computed

`backReachSetExists`'s step at a representation: `plus` against the negated
input set, then `mtimes Ainv` for the preimage under `A`, taken as the image
under a left inverse the caller hands in. `sys` is carried and never read — the
dynamics enter through `backReachExists_outer`'s `hA` alone.

Total, and with no operation parameter, where `backReachForall` is `Option`-
valued and takes `diff`: both steps here are the ordinary outer ones, `Plus`
and `Mtimes`, and neither can fail to certify what it returns.

`negU` is a set and not `-U`: no class here negates a set, and `Scalar` gives
`Mat 𝕋` no ring structure to build `-1` in. The caller supplies a representation
enclosing `-U`, which for a centrally symmetric input set is `U` itself.

No `reduce` in the loop, where `backReachForall` had nothing for one to bound:
`Zonotope.plus` appends generators, so at `Zonotope` the result does grow with
`k`. It is left out to keep what this asks for down to two classes.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
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
def LinearSysDT.backReachExists (sys : LinearSysDT 𝕋 n) (Ainv : Mat 𝕋 n n)
    (T negU : S n) : ℕ → S n
  | 0 => T
  | k + 1 => mtimes Ainv (plus (sys.backReachExists Ainv T negU k) negU)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
