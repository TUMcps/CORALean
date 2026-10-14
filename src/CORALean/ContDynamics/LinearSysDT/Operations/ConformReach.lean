module

public import CORALean.ContDynamics.LinearSysDT.Operations.ConformAdd

@[expose] public section

/-!
# The deviation sets of the conformance check

`priv_conform_reachableHalfspaces` [1]: at sample `k` the output deviation set is
`R_k = C A^k X₀ ⊕ ⊕_{j<k} C A^j (E W) ⊕ F V`, `E{k} = C A^{k-1}`, `Radd` growing by one term per
step. CORA turns it into a polytope for the halfspace test; the set is taken as it is, which
is the same set for a zonotope. `W` and `V` are the sets `params.W`, `params.V` before the
mapping by `E` and `F`, which this applies, as `isconform_dyn` does.

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

/-- `R = E{k}*X0 + Radd + params.V`. -/
noncomputable def LinearSysDT.conformReach (sys : LinearSysDT ℝ n) (X₀ : S n) (W : S sys.r)
    (V : S sys.s) (k : ℕ) : S sys.q :=
  plus (plus (Mtimes.mtimes (𝕄 := Mat ℝ) (sys.C * sys.A ^ k : Mat ℝ sys.q n) X₀)
    (LinearSysDT.conformAdd sys W k)) (Mtimes.mtimes (𝕄 := Mat ℝ) sys.F V)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
