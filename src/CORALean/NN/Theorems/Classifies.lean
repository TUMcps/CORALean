module

public import CORALean.NN.Theorems.DisjointMisclassifiedOfBounds
public import CORALean.NN.Operations.MarginDir
public import CORALean.NN.Theorems.EncloseOuter

@[expose] public section

/-!
# Every input in the set is classified the same

The network-level form of `disjoint_misclassified_of_bounds`: read at the
enclosed image, a bound per rival label puts every point of that enclosure on
the target's side of every margin.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every input in the set is classified `l`, on the strength of one bound per
rival label against the enclosed image. -/
theorem NeuralNetwork.classifies {nn : NeuralNetwork S n m} {f : Vec ℝ n → Vec ℝ m}
    (hf : nn.Encloses f) (X : S n) (l : Fin m)
    (u : ∀ j, SupportBound (construct (nn.enclose X))
      (marginDir m j l))
    (h : ∀ j, j ≠ l → (u j).val < 0) {x : Vec ℝ n} (hx : x ∈ construct X)
    {j : Fin m} (hj : j ≠ l) : -- --- CONCL ---
    f x j < f x l := by -- --- PROOF ---
  have hd := disjoint_misclassified_of_bounds l u h
  have hmem := hf.enclose_outer X x hx
  have hnot := Set.disjoint_left.mp hd hmem
  by_contra hc
  exact hnot ⟨j, hj, not_lt.mp hc⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
