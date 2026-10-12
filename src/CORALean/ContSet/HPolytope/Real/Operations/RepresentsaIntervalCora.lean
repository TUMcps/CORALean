import CORALean.ContSet.HPolytope.Real.HPolytope

/-!
# `HPolytope.representsaIntervalCora`: the `'interval'` test as CORA's code computes it

`@polytope/representsa_.m`, branch `'interval'` (`aux_isInterval`, l. 236-312), builds the
interval `I = [lb, ub]` from the axis-aligned rows, then walks the other rows `a x ≤ b`:
`supportFunc_(I, a, 'upper') <= b` makes the row redundant, `supportFunc_(I, a, 'lower') > b`
returns `true` with the empty interval, and otherwise ("cuts through the interval... only hope
now is that the polytope is empty") it returns `representsa_(P, 'emptySet')`.

This models that walk for one non-axis-aligned row `(a, b)` over the box `[lb, ub]`, with the
two support-function values in their closed form for a box. `True` stands for `res = true`
(either `true` return, or the loop ending with every row redundant). Read from the source,
not run.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's answer for `representsa_(P, 'interval')` when the axis-aligned rows give the box
`[lb, ub]` and `(a, b)` is the only non-axis-aligned row. -/
noncomputable def HPolytope.representsaIntervalCora (P : HPolytope (Fin n → ℝ))
    (lb ub a : Fin n → ℝ) (b : ℝ) : Prop :=
  let upper := ∑ i, if 0 ≤ a i then a i * ub i else a i * lb i  -- supportFunc_(I,a,'upper')
  let lower := ∑ i, if 0 ≤ a i then a i * lb i else a i * ub i  -- supportFunc_(I,a,'lower')
  if upper ≤ b then True                 -- constraint is redundant
  else if b < lower then True            -- empty: `res = true; I = interval.empty(n)`
  else P.construct = ∅                   -- `res = representsa_(P,'emptySet',tol)`

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
