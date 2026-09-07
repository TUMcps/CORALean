import CORALean.NN.Theorems.EncloseOuter

/-!
# A safe set checked on the enclosed set holds pointwise

`Verified` reads a requirement through the abstract `Specification.Holds`; this
is the same fact read one input at a time, which is how a safety requirement on
a network is normally stated — directly off `enclose_outer`, with no
`Specification` in sight.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open ContSet

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The same read one input at a time, which is how a requirement on a network
is normally stated. -/
theorem NeuralNetwork.mem_safeSet (nn : NeuralNetwork S n m) (X : S n) {safe : Set (Vec ℝ m)}
    (h : construct (nn.enclose X) ⊆ safe) {x : Vec ℝ n} (hx : x ∈ construct X) :
    nn.eval x ∈ safe :=
  h (nn.enclose_outer X x hx)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
