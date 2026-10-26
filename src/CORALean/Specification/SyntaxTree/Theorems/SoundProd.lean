module

public import CORALean.Specification.SyntaxTree.Definitions.IsSound
public import CORALean.Specification.SyntaxTree.Operations.Basic
public import CORALean.Specification.SyntaxTree.SyntaxTree
public import CORALean.Specification.SyntaxTree.Theorems.Basic

@[expose] public section

/-!
# The product of sound trees is sound

`prod` over sound trees is sound.

## Inputs
* `rest` – remaining trees

## Hypotheses
* `h` – the first tree is sound
* `hs` – the remaining trees are sound

## Conclusion
* the product tree is sound
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ} {B : Real.Interval (Vec ℝ n)} {t : SyntaxTree n}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `prod` of sound trees is sound. -/
theorem SyntaxTree.isSound_prod (h : IsSound B t) (rest : List (SyntaxTree n))
    (hs : ∀ u ∈ rest, IsSound B u) : -- --- CONCL ---
    IsSound B (prod t rest) := by -- --- PROOF ---
  induction rest generalizing t with
  | nil => exact h
  | cons u us ih =>
    exact ih (isSound_times h (hs u (List.mem_cons_self))) (fun v hv => hs v (List.mem_cons_of_mem _
        hv))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
