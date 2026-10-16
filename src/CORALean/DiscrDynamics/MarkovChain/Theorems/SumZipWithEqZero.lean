module

public import CORALean.DiscrDynamics.MarkovChain.Operations.Basic

@[expose] public section

/-!
# A weighted sum of zeros is zero

A `zipWith` of terms that vanish for every first argument sums to zero.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      16-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

/-- If `g r f = 0` for all `r ∈ R`, the sum of `zipWith g R F` is zero. -/
theorem MarkovChain.sum_zipWith_eq_zero {α β : Type} (g : α → β → ℝ) (R : List α) (F : List β)
    (h : ∀ r ∈ R, ∀ f, g r f = 0) : (List.zipWith g R F).sum = 0 := by -- --- PROOF ---
  induction R generalizing F with
  | nil => simp
  | cons a R ih =>
    cases F with
    | nil => simp
    | cons f F =>
      simp only [List.zipWith_cons_cons, List.sum_cons]
      rw [h a List.mem_cons_self f, ih F (fun r hr => h r (List.mem_cons_of_mem _ hr))]
      simp

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
