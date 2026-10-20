module

public import CORALean.ContDynamics.LinearSysDT.Definitions.GO
public import CORALean.ContDynamics.LinearSysDT.LinearSysDT

@[expose] public section

/-!
# `LinearSysDT.computeGO`

CORA's `linearSysDT/computeGO` [1] for the time-invariant system, with the input entering in
state coordinates (`B = 1`, as everywhere for `LinearSysDT`) and the output equation `out`
read off a state and an input in state coordinates. CORA's loop
`A{k} = A A{k-1}`, `C{k} = C A{k-1}`, `B{k,j} = A{k-j} B`, `D{k,j} = C B{k,j+1}` is written
here as the powers it computes; the time-varying branch (`A` a cell) is not modelled.

## Inputs
* `sys` – system
* `out` – output equation
* `nk` – number of steps

## Output
* the GO parameters as real matrices

## References

* [1] `contDynamics/@linearSysDT/computeGO.m`
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Scalar

variable {n r : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The GO parameters for `nk` steps, as real matrices. -/
noncomputable def LinearSysDT.computeGO (sys : LinearSysDT 𝕋 n) (out : OutputEq 𝕋 n n r)
    (nk : ℕ) : LinearSysDT.GO n r nk where
  A k := toRealMat sys.A ^ (k.val + 1)
  B k j := if j.val ≤ k.val then toRealMat sys.A ^ (k.val - j.val) else 0
  C k := toRealMat out.C * toRealMat sys.A ^ k.val
  D k j :=
    if j = k then toRealMat out.D
    else if j.val < k.val then toRealMat out.C * toRealMat sys.A ^ (k.val - 1 - j.val) else 0

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
