import CORALean.ContDynamics.LinearARX.LinearARX

/-!
# The blocks of an identified ARX matrix

`A = Alist{i}(:,1:n*p)`, `B = Alist{i}(:,n*p+1:end)` of `priv_identifyDMD` [1], cut by
`mat2cell` into `p` blocks `A_i` of width `n` and `p+1` blocks `B_j` of width `m`.

## References

* [1] `contDynamics/@linearARX/private/priv_identifyDMD.m`
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {dy du p : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The system `linearARX(A_, B_, dt)` of the matrix `[A B]`; the step `dt` is not stored. -/
def LinearARX.identifyBlocks (M : Mat ℝ dy (p * dy + (p + 1) * du)) : LinearARX ℝ dy du p where
  Abar i := fun a b => M a (Fin.castAdd _ (finProdFinEquiv (i, b)))
  Bbar j := fun a b => M a (Fin.natAdd _ (finProdFinEquiv (j, b)))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
