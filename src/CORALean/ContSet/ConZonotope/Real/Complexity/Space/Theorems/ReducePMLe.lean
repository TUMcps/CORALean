module

public import CORALean.ContSet.ConZonotope.Real.Operations.Reduce
public import CORALean.ContSet.HPolytope.Real.Operations.Restrict
public import CORALean.ContSet.HPolytope.Real.Operations.ToIneqs

@[expose] public section

/-!
# `ConZonotope.reduce`'s constraint counts

Only a bound, and only on the constraints. Compacting keeps every inequality row, and above the
threshold each one is read on the kept generators (`keepRows`), one row for one, while the equality
rows go into the lifted zonotope and come back as equalities. So the inequality count is the
operand's and the equality count at most the operand's, the trivial rows `0 = 0` being gone.

The generator count is `ConZonotope.reduce_order_le`, under `Theorems/`: it is `reduce`'s own bound,
not one operation's size in terms of another's, which is what `Complexity/Space/` records.

## Inputs
* `cZ` – constrained zonotope
* `o` – target order

## Hypotheses
* none

## Conclusion
* reducing does not increase the inequality count
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       07-September-2026
-- Last update:   27-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- An upper bound on the `P_m` count of `reduce`'s result. -/
theorem ConZonotope.reduce_P_m_le (cZ : ConZonotope (Vec ℝ n)) (o : ℕ) : -- --- CONCL ---
    (cZ.reduce o).P.m ≤ cZ.P.m := by -- --- PROOF ---
  have hc : cZ.compact.P.m = cZ.P.m := by
    simp [ConZonotope.compact, HPolytope.comap, HPolytope.dropTrivialEqs, HPolytope.restrict]
  unfold ConZonotope.reduce
  dsimp only
  by_cases hlt : max o 1 * n + cZ.compact.P.me < cZ.compact.h
  · rw [dif_pos hlt]
    simp only [ConZonotope.reduceLiftBy, ConZonotope.reduceKeepBy, ConZonotope.keepRows,
      HPolytope.intersection, HPolytope.eqs, HPolytope.comap, HPolytope.relax, HPolytope.toIneqs,
      ConZonotope.liftEq, HPolytope.dropEqs]
    omega
  · rw [dif_neg hlt]
    omega

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
