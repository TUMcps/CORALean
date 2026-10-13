module

public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.AbsEntryLeNorm

@[expose] public section

/-!
# Reading a matrix `tsum` off one entry at a time

[1, `Prop. 11`]'s entrywise domination of the particular solution's tail needs to
compare a `tsum` of matrices, entry by entry, against another one; both
`NormedSpace.exp` and `MatExp.expIntegral` are themselves matrix `tsum`s, and
`Matrix.linftyOp*`'s norm makes evaluating an entry `1`-Lipschitz, hence
continuous, so it commutes with any convergent sum.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE Transactions on
      Automatic Control, vol. 68, no. 12, 2023, pp. 7771–7786.
-/

-- Authors:       Claude Opus 5
-- Written:       19-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Evaluating a matrix at one entry, as an additive homomorphism — linear, and (below)
`1`-Lipschitz under the `l∞` operator norm, so continuous. -/
def aux_entryAddHom (j k : Fin n) : Mat ℝ n n →+ ℝ where
  toFun M := M j k
  map_zero' := rfl
  map_add' _ _ := rfl

/-- An entry moves by at most the norm of the difference — `abs_entry_le_norm` at `M - N`. -/
theorem aux_lipschitzWith_entryAddHom (j k : Fin n) :
    LipschitzWith 1 (aux_entryAddHom (n := n) j k) := by
  refine LipschitzWith.of_dist_le_mul fun M N => ?_
  rw [NNReal.coe_one, one_mul, Real.dist_eq, dist_eq_norm]
  have h := abs_entry_le_norm (M - N) j k
  simpa only [aux_entryAddHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Matrix.sub_apply] using h


-- =======================================  MAIN THEOREM  ======================================= --

/-- A convergent matrix `tsum`'s value at one entry is the `tsum` of that entry alone. -/
theorem MatExp.tsum_entry_eq {f : ℕ → Mat ℝ n n} (hf : Summable f) (j k : Fin n) :
    (∑' i, f i) j k = ∑' i, (f i) j k := by
  have hc := (aux_lipschitzWith_entryAddHom (n := n) j k).continuous
  have h := hf.hasSum.map (aux_entryAddHom (n := n) j k) hc
  exact h.tsum_eq.symm

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
