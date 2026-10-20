module

public import CORALean.ContDynamics.LinearSysDT.LinearSysDT

@[expose] public section

/-!
# The disturbances' part of the conformance check's deviation sets

`Radd` of `priv_conform_reachableHalfspaces` [1]: at sample `k` the output deviation set is
`R_k = C A^k X₀ ⊕ ⊕_{j<k} C A^j (E W) ⊕ F V`, `E{k} = C A^{k-1}`, `Radd` growing by one term per
step. CORA turns it into a polytope for the halfspace test; the set is taken as it is, which
is the same set for a zonotope. `W` and `V` are the sets `params.W`, `params.V` before the
mapping by `E` and `F`, which this applies, as `isconform_dyn` does.

## Inputs
* `sys` – system
* `W` – disturbance set

## Output
* the accumulated disturbance part after each number of steps

## References

* [1] `contDynamics/@linearSysDT/private/priv_conform_reachableHalfspaces.m`
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Plus Mtimes

variable {n : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S] [∀ n, OfPoint (S n) (Vec ℝ n)]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `Radd` after `k` steps, `0` before the first. -/
noncomputable def LinearSysDT.conformAdd (sys : LinearSysDT ℝ n) (W : S sys.r) : ℕ → S sys.q
  | 0 => OfPoint.ofPoint 0
  | k + 1 => plus (LinearSysDT.conformAdd sys W k)
      (Mtimes.mtimes (𝕄 := Mat ℝ) (sys.C * sys.A ^ k : Mat ℝ sys.q n)
        (Mtimes.mtimes (𝕄 := Mat ℝ) sys.E W))                         -- Radd + E{k}*params.W

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
