import CORALean.ContDynamics.LinearARX.Definitions.GO
import CORALean.ContDynamics.LinearARX.Operations.Feed
import CORALean.ContDynamics.LinearARX.Operations.OutputEq
import CORALean.ContDynamics.LinearARX.Operations.ToLinearSysDT

/-!
# `LinearARX.computeGO`

CORA's `linearARX/computeGO` [1], on the window of the converted system. The output `y(k)` is
the first block of the window `stack y k`, which `A_ext^k` carries from the initial window and
`A_ext^{k-1-t}` from the input of step `t`, `feed u t = ∑_j B_ext_j u(t+p-j)`: so
`C{k} = C₀ A_ext^k` and `D{k,i}` collects the `A_ext^{k-1-t} B_ext_j` whose input index
`t+p-j` is `i`. CORA reads the output from the last block of the window `k+1-p` steps on
(`E A_ext^{k+1-p}`), the same value; the loop over `A_ext_powerk` is the powers here.

## References

* [1] `contDynamics/@linearARX/computeGO.m`
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Scalar

variable {𝕋 : Type} [Scalar 𝕋] [ExactScalar 𝕋] {dy du p : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The output parameters for `nk` steps, as real matrices. -/
noncomputable def LinearARX.computeGO (sys : LinearARX 𝕋 dy du p) (nk : ℕ) :
    LinearARX.GO dy du p nk where
  C k := toRealMat sys.outputEq.C * toRealMat sys.toLinearSysDT.A ^ k.val
  D k i := ∑ t ∈ Finset.range k.val, ∑ j : Fin (p + 1),
    if t + p - j.val = i.val then
      toRealMat sys.outputEq.C * toRealMat sys.toLinearSysDT.A ^ (k.val - 1 - t)
        * toRealMat (sys.inputMat j)
    else 0

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
