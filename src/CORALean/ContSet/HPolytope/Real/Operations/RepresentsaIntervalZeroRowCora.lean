module

public import CORALean.ContSet.HPolytope.Real.Operations.RowUpperCora
public import CORALean.ContSet.HPolytope.Real.Operations.RowLowerCora

@[expose] public section

/-!
# `HPolytope.representsaIntervalZeroRowCora`: the box of `aux_isInterval` as CORA computes it

`@polytope/representsa_.m`, branch `'interval'` (`aux_isInterval`, l. 236-312) loops over the rows
of `[A; Ae; -Ae]` with offsets `[b; be; -be]` from `lb = -Inf`, `ub = Inf` and skips a row with
`if ~any(constraint) continue` (l. 259): also `0 x ≤ b` with `b < 0`, which is infeasible. A row
with two or more nonzero entries is flagged for the redundancy walk (`checkRedundancy`; modelled
in `HPolytope.representsaIntervalCora`, here the parameter `rest`). If none is flagged the
function ends with `res = true`, `I = interval(lb,ub)` (l. 218, 242). Tolerance `0`. Read from the
source, not run.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       13-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

open Classical in
/-- CORA's `(lb, ub)` of `I = interval(lb,ub)` for `representsa_(P, 'interval')`, H-representation;
`rest` is what the redundancy walk returns when some row is flagged. -/
noncomputable def HPolytope.representsaIntervalZeroRowCora (P : HPolytope (Fin n → ℝ))
    (rest : (Fin n → EReal) × (Fin n → EReal)) : (Fin n → EReal) × (Fin n → EReal) :=
  -- ub(idx) = min([offsets(c) / constraint_norm, ub(idx)]) over the rows [A; Ae; -Ae]
  let ub : Fin n → EReal := fun j =>
    (⨅ i, HPolytope.rowUpperCora (P.A i) (P.b i) j) ⊓
      (⨅ i, HPolytope.rowUpperCora (P.Ae i) (P.be i) j) ⊓
      (⨅ i, HPolytope.rowUpperCora (-P.Ae i) (-P.be i) j)
  -- lb(idx) = max([-offsets(c) / constraint_norm, lb(idx)])
  let lb : Fin n → EReal := fun j =>
    (⨆ i, HPolytope.rowLowerCora (P.A i) (P.b i) j) ⊔
      (⨆ i, HPolytope.rowLowerCora (P.Ae i) (P.be i) j) ⊔
      (⨆ i, HPolytope.rowLowerCora (-P.Ae i) (-P.be i) j)
  -- checkRedundancy(c) = true: the row has two nonzero entries
  let flagged : ((Fin n → ℝ) →ₗ[ℝ] ℝ) → Prop := fun f =>
    ∃ i j, i ≠ j ∧ f (Pi.single i 1) ≠ 0 ∧ f (Pi.single j 1) ≠ 0
  -- if any(checkRedundancy) ... else res = true; I = interval(lb,ub)
  if (∃ i, flagged (P.A i)) ∨ (∃ i, flagged (P.Ae i)) then rest else (lb, ub)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
