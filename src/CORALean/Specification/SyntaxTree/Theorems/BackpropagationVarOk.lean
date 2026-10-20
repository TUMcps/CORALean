module

public import CORALean.Specification.SyntaxTree.Operations.Backpropagation
public import CORALean.Specification.SyntaxTree.Operations.Basic
public import CORALean.Specification.SyntaxTree.SyntaxTree

@[expose] public section

/-!
# What a leaf `backpropagation` returns

If `backpropagation` of a variable returns a box, its upper bound at `id` is the smaller of
`value`'s and `int(id)`'s.

## Inputs
* `i` – variable index
* `w` – value interval
* `v` – target interval
* `B` – box
* `r` – result box

## Hypotheses
* `h` – the backpropagation returns the result box

## Conclusion
* the upper bound is the smaller of the target's and the box's
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ} {B : Real.Interval (Vec ℝ n)} {t : SyntaxTree n}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The upper bound a leaf returns at its coordinate. -/
theorem SyntaxTree.backpropagation_var_ok {i : Fin n} {w v : Dom}
    {B r : Real.Interval (Vec ℝ n)} (h : backpropagation (.var i w) v B = .ok r) : -- --- CONCL ---
    r.sup i = min (v.sup 0) (B.sup i) := by -- --- PROOF ---
  simp only [backpropagation] at h
  split_ifs at h with hc
  simp only [Outcome.ok.injEq] at h
  subst h
  simp

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
