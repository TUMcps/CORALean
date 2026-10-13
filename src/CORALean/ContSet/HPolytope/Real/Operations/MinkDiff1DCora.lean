import CORALean.ContSet.HPolytope.Real.Operations.Fullspace

/-!
# `HPolytope.minkDiff1DCora`: CORA's one-dimensional polytope `minkDiff`

`@polytope/minkDiff.m` sends two one-dimensional polytopes to `aux_minkDiff_1D` (l. 78-81,
146-176). It compacts both operands (l. 155, 161), returns the fullspace for a fullspace minuend
or an empty subtrahend (l. 157-165), errors on equality constraints (l. 167-171), and otherwise
returns `polytope(P_.A_.val, P_.b_.val - S_.b_.val)` (l. 174), on the comment "both A matrices are
normalized in minHRep". That subtraction pairs the minuend's rows with the subtrahend's by
position. `priv_compact_1D` ([2], l. 77-89) leaves two rows `[1; -1]` only for a set bounded on both
sides; a subtrahend bounded on one side keeps the single row `1` or `-1`, and MATLAB broadcasts
its one offset over both rows of the minuend, whatever that row's direction.

The compacted operands `P_`, `S_` are the arguments; the compaction itself is
`priv_compact_1D`'s, not modelled. `representsa_` reads as exact. MATLAB's `-` broadcasts a
one-row operand, subtracts equal lengths entrywise and errors otherwise; `none` is an error.
Read from the source, not run.

## References

* [1] `contSet/@polytope/minkDiff.m`, CORA, ll. 77-81, 146-176.
* [2] `contSet/@polytope/private/priv_compact_1D.m`, CORA, ll. 73-110.
-/

-- Authors:       Claude Opus 5.5
-- Written:       13-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1]'s `aux_minkDiff_1D` at the compacted operands `P_` and `S_`; `none` is an error. -/
noncomputable def HPolytope.minkDiff1DCora (P_ S_ : HPolytope (Vec ℝ 1)) :
    Option (HPolytope (Vec ℝ 1)) :=
  open Classical in
  -- l. 157-159: `if representsa_(P_,'fullspace',0)`, `P_out = polytope.Inf(n)`
  if P_.construct = Set.univ then some (HPolytope.fullspace _)
  -- l. 163-165: `if representsa_(S_,'emptySet',1e-10)`, `P_out = fullspace(n)`
  else if S_.construct = ∅ then some (HPolytope.fullspace _)
  -- l. 167-171: equality constraints, `CORA:notSupported`
  else if P_.me ≠ 0 ∨ S_.me ≠ 0 then none
  else
    -- l. 174: `P_.b_.val - S_.b_.val`, broadcast, entrywise, or an error
    let b : Option (Fin P_.m → ℝ) :=
      if h₁ : S_.m = 1 then some fun i => P_.b i - S_.b ⟨0, by omega⟩
      else if h : S_.m = P_.m then some fun i => P_.b i - S_.b (i.cast h.symm)
      else none
    -- l. 174: `P_out = polytope(P_.A_.val, ...)`
    b.map fun b => ⟨P_.m, P_.A, b, 0, Fin.elim0, Fin.elim0⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
