module

public import CORALean.NN.Operations.MarginDir
public import CORALean.NN.Definitions.Misclassified
public import CORALean.Global.SupportFunction.SupportFunction
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# A bound per rival separates the exact output from misclassification

`m - 1` bounds discharge it, one per rival label, each in the direction
`eⱼ - e_l` — the objective "how much closer can `j` get to `l`". Negative means
it never catches up. Those are the objects `Global.SupportFunction` already produces,
so a classifier is verified with no machinery beyond a bound per rival.

Needed by both `Robustness` and `Classifies`, so it is public rather than
duplicated into each.

## Inputs
* `O` – output set
* `l` – target label
* `u` – support bound of the output set for each rival

## Hypotheses
* `h` – every rival's bound is negative

## Conclusion
* the output set is disjoint from the misclassified outputs
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

private theorem aux_marginDir_apply (j l : Fin m) (y : Vec ℝ m) : marginDir m j l y = y j - y l :=
    by
  rw [marginDir, LinearMap.sub_apply]
  rfl


-- =======================================  MAIN THEOREM  ======================================= --

theorem disjoint_misclassified_of_bounds {O : Set (Vec ℝ m)} (l : Fin m)
    (u : ∀ j, SupportBound O (marginDir m j l))
    (h : ∀ j, j ≠ l → (u j).val < 0) : -- --- CONCL ---
    Disjoint O (misclassified m l) := by -- --- PROOF ---
  rw [Set.disjoint_left]
  rintro y hy ⟨j, hj, hle⟩
  have hb := (u j).le y hy
  rw [aux_marginDir_apply] at hb
  linarith [h j hj]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
