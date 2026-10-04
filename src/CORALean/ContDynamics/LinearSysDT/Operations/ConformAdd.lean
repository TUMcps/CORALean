import CORALean.ContDynamics.LinearSysDT.LinearSysDT
import CORALean.ContDynamics.OutputEq.OutputEq

/-!
# The disturbances' part of the conformance check's deviation sets

`Radd` of `priv_conform_reachableHalfspaces` [1]: at sample `k` the output deviation set is
`R_k = C A^k X₀ ⊕ ⊕_{j<k} C A^j (E W) ⊕ F V`, `E{k} = C A^{k-1}`, `Radd` growing by one term per
step. CORA turns it into a polytope for the halfspace test; the set is taken as it is, which
is the same set for a zonotope. `W` and `V` are the sets `params.W`, `params.V` before the
mapping by `E` and `F`, which this applies, as `isconform_dyn` does.

## References

* [1] `contDynamics/@linearSysDT/private/priv_conform_reachableHalfspaces.m`
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Plus Mtimes

variable {n q s r : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S] [∀ n, OfPoint (S n) (Vec ℝ n)]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `Radd` after `k` steps, `0` before the first. -/
noncomputable def LinearSysDT.conformAdd (sys : LinearSysDT ℝ n) (C : Mat ℝ r n) (E : Mat ℝ n q)
    (W : S q) : ℕ → S r
  | 0 => OfPoint.ofPoint 0
  | k + 1 => plus (LinearSysDT.conformAdd sys C E W k)
      (Mtimes.mtimes (𝕄 := Mat ℝ) (C * sys.A ^ k : Mat ℝ r n)
        (Mtimes.mtimes (𝕄 := Mat ℝ) E W))                         -- Radd + E{k}*params.W

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
