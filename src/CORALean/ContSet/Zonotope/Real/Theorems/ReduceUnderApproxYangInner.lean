module

public import CORALean.ContSet.Zonotope.Real.Operations.ReduceUnderApproxYang
public import CORALean.ContSet.Zonotope.Real.Theorems.CombineGensInner

@[expose] public section

/-!
# `reduceUnderApproxYang` returns a subset

[1, Sec. IV-B.1]'s reduction, by [1, Prop. 6] once per step: each combination stays
inside the zonotope it came from, whichever pair and sign the heuristic picks, so the
reduced zonotope is inside `Z`.

## Inputs
* `sel` – pair selector
* `N` – target generator count
* `Z` – zonotope

## Hypotheses
* none

## Conclusion
* the reduced zonotope lies in `Z`

## References

* [1] L. Yang and N. Ozay. "Scalable zonotopic under-approximation of backward reachable sets for
      uncertain linear systems". IEEE Control Systems Letters, 2022.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Prop. 6], iterated: the reduced zonotope is inside `Z`, for every selection. -/
theorem Zonotope.reduceUnderApproxYang_inner
    (sel : (Z : Zonotope α) → {m : ℕ} → Z.h = m + 2 → Fin (m + 2) × Fin (m + 1) × Bool)
    (N : ℕ) (Z : Zonotope α) : -- --- CONCL ---
    (Z.reduceUnderApproxYang sel N).construct ⊆ Z.construct := by -- --- PROOF ---
  -- by induction on the remaining steps, for every start
  suffices h : ∀ k (Z : Zonotope α),
      (Zonotope.reduceUnderApproxYang.go sel k Z).construct ⊆ Z.construct from h _ Z
  intro k
  induction k with
  | zero => exact fun _ => subset_rfl
  | succ k ih =>
    intro Z
    unfold Zonotope.reduceUnderApproxYang.go
    split
    · next hm => exact (ih _).trans (Z.combineGens_inner hm _ _ _)
    · exact subset_rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
