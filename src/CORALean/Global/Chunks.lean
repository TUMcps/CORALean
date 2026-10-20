module

public import Mathlib.Data.List.Basic

@[expose] public section

/-!
# A list cut into consecutive chunks of at most `μ` elements

`chunks μ l` is `l` cut into consecutive pieces of at most `μ` elements (one each at `μ = 0`),
each returned as its first element and the rest, so a piece is never empty. Every element of
`l` is in some piece (`exists_mem_chunks`). [1, Sec. 3.2]'s Step 3 unites the contracted boxes
`μ` at a time this way.

## Inputs
* `μ` – largest piece size

## Output
* the list cut into consecutive pieces, each its first element and the rest

## References

* [1] N. Kochdumper and M. Althoff. "Reachability Analysis for Hybrid Systems with Nonlinear
      Guard Sets". In Proc. of the 23rd ACM International Conference on Hybrid Systems:
      Computation and Control (HSCC), 2020.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {α : Type}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `l` in consecutive pieces `(first, rest)` of at most `max μ 1` elements. -/
def chunks (μ : ℕ) : List α → List (α × List α)
  | [] => []
  | x :: xs => (x, xs.take (μ - 1)) :: chunks μ (xs.drop (μ - 1))
termination_by l => l.length
decreasing_by simp only [List.length_drop, List.length_cons]; omega

/-- Every element of `l` is the first element or in the rest of some piece. -/
theorem exists_mem_chunks (μ : ℕ) (l : List α) {y : α} (hy : y ∈ l) :
    ∃ c ∈ chunks μ l, y = c.1 ∨ y ∈ c.2 := by -- --- PROOF ---
  induction l using chunks.induct μ with
  | case1 => simp at hy
  | case2 x xs ih =>
    rw [chunks]
    rcases List.mem_cons.mp hy with rfl | hy
    · exact ⟨_, List.mem_cons_self, Or.inl rfl⟩
    -- `y` is in the first `μ - 1` of `xs` or in the rest
    · rw [← List.take_append_drop (μ - 1) xs, List.mem_append] at hy
      rcases hy with hy | hy
      · exact ⟨_, List.mem_cons_self, Or.inr hy⟩
      · obtain ⟨c, hc, hyc⟩ := ih hy
        exact ⟨c, List.mem_cons_of_mem _ hc, hyc⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
