module

public import CORALean.ContSet.ConZonotope.Real.Operations.Reduce
public import CORALean.ContSet.HPolytope.Real.Operations.Restrict
public import CORALean.ContSet.HPolytope.Real.Operations.ToIneqs

@[expose] public section

/-!
# `ConZonotope.reduce_P_me_le`

An upper bound on the `P_me` count of `reduce`'s result: the equality rows come back off the lifted
zonotope one for one, less the trivial rows `0 = 0` compacting deletes.

## Inputs
* `cZ` – constrained zonotope
* `o` – target order

## Hypotheses
* none

## Conclusion
* reducing does not increase the equality count
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       07-September-2026
-- Last update:   27-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- An upper bound on the `P_me` count of `reduce`'s result. -/
theorem ConZonotope.reduce_P_me_le (cZ : ConZonotope (Vec ℝ n)) (o : ℕ) : -- --- CONCL ---
    (cZ.reduce o).P.me ≤ cZ.P.me := by -- --- PROOF ---
  have hc : cZ.compact.P.me ≤ cZ.P.me := by
    simp only [ConZonotope.compact, HPolytope.comap, HPolytope.dropTrivialEqs, HPolytope.restrict]
    exact (Finset.card_le_univ _).trans (by simp)
  unfold ConZonotope.reduce
  dsimp only
  by_cases hlt : max o 1 * n + cZ.compact.P.me < cZ.compact.h
  · rw [dif_pos hlt]
    simp only [ConZonotope.reduceLiftBy, ConZonotope.reduceKeepBy, ConZonotope.keepRows,
      HPolytope.intersection, HPolytope.eqs, HPolytope.comap, HPolytope.relax, HPolytope.toIneqs]
    omega
  · rw [dif_neg hlt]
    exact hc

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
