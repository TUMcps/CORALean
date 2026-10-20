module

public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# `LinearSys.decompOutputCora`: the output offset of `decomp` is added twice

`priv_reach_decomp.m` puts the system into canonical form and then sets
`V = V + v(:,1)` (l. 49), so the offset of the output equation, `v = D*uTrans + k + F*(centerV +
vVec)`, is already in `V`. Every output set is then `priv_outputSet_canonicalForm(linsys,X,V,v,k)`,
which returns `C * X + V + v`, adding `v` once more. The other algorithms hand
`V` as returned by `canonicalForm` (`standard`, `fromStart`, ...), so they add `v` once.
Modelled in `ℝ`: the state `x`, the output matrix `c`, `V` as `canonicalForm` returns it, the offset
`v`. Read from the source, not run.

# CORA's `decomp` shifts every output set by the offset `v` a second time

For `linearSys('s',-1,1,0,1,0,1)` (`ẋ = -x + u`, `y = x + 1`, `D = 0`, `k = 1`), `R0 = {0}`,
`U = {0}`, `partition = [1,1]`, `tFinal = timeStep`: `x = 0`, the true output is `y = 1`, and
`canonicalForm` gives `v_ = k = 1`, `V_ = 0`, so the output set is `{0 + (0 + 1) + 1} = {2}`.

# CORA's `decomp` stops at `reduce`

l. 99-104, `decompose(reduce(recompose(PU, options.reductionTechnique, options.zonotopeOrder),
blocks))`: `recompose` takes one argument (`@contSet/recompose.m`, `global/.../recompose.m`) and
`reduce` receives `blocks` as the method. `PU` is a set (`isa(PU,'contSet')`, l. 101) only with one
block and `U ≠ {0}` (a cell for several blocks, numeric for `U = {0}`): that case stops with a
MATLAB error at the second step, and with several blocks `PU` is never reduced. Read from the
source, not run.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* CORA's output set is off the true output because the offset is counted twice
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- The model: CORA's code as printed, kept only to be refuted.
/-- The output of `decomp`: `V + v(:,1)` is the offset passed on, `priv_outputSet_canonicalForm`
adds `v` again. -/
def LinearSys.decompOutputCora (c x V v : ℝ) : ℝ :=
  let V' := V + v                                                 -- 30.  V = V + v(:,1)
  c * x + V' + v                                                  -- C*X + V + v

/-- The output of the other algorithms: `v` once. -/
def LinearSys.outputCanonical (c x V v : ℝ) : ℝ :=
  c * x + V + v

-- The model: CORA's code as printed, kept only to be refuted.
/-- The reduction of `PU` in the loop of `decomp`, for `numBlocks` blocks and `U` the origin or
not: `none` is the MATLAB error of `recompose` called with three arguments, `some false` that
`PU` is not a set (a cell, or the numeric zero) and no reduction is done. -/
def LinearSys.decompReducePUCora (numBlocks : Nat) (uIsOrigin : Bool) : Option Bool :=
  if numBlocks = 1 ∧ uIsOrigin = false then none else some false


-- =======================================  MAIN THEOREM  ======================================= --

/-- `y = x + 1` at `x = 0`: the output is `1`, CORA's set is `{2}`. -/
theorem LinearSys.decompOutputCora_counterexample :
    LinearSys.outputCanonical 1 0 0 1 = 1 ∧ LinearSys.decompOutputCora 1 0 0 1 = 2 ∧
      (1 : ℝ) ∉ ({LinearSys.decompOutputCora 1 0 0 1} : Set ℝ) := by
  unfold LinearSys.outputCanonical LinearSys.decompOutputCora
  norm_num

/-- One block and a non-zero `U`: the error. Several blocks or `U = {0}`: no reduction at all. -/
theorem LinearSys.decompReducePUCora_crash :
    LinearSys.decompReducePUCora 1 false = none ∧
      LinearSys.decompReducePUCora 2 false = some false ∧
      LinearSys.decompReducePUCora 1 true = some false := by
  simp [LinearSys.decompReducePUCora]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
