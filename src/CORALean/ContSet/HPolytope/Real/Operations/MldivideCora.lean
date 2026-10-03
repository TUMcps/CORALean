import CORALean.ContSet.HPolytope.Real.HPolytope

/-!
# `HPolytope.mldivideCora`: `mldivide` as CORA's code computes it

`@polytope/mldivide.m` returns `P1 \ P2` as a union of polytopes, but line 26 reads
`P2 = compact_(P1,'all',1e-9);` where it means `compact_(P2, ...)`, so after the two early
returns (`P1` empty, `P2` empty) both operands are `P1`, and the rest of the code, which computes
the difference of its two arguments, returns `P1 \ P1`. `compact_` does not change the set.
The difference algorithm is not formalized; this is the set it denotes at `(P1, P1)`.
Read from the source, not run.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The set CORA's `mldivide` returns: the two early returns, then `P1 \ P1`. -/
noncomputable def HPolytope.mldivideCora (P₁ P₂ : HPolytope (Vec ℝ n)) : Set (Vec ℝ n) :=
  open Classical in
  if P₁.construct = ∅ then ∅
  else if P₂.construct = ∅ then P₁.construct
  else P₁.construct \ P₁.construct

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
