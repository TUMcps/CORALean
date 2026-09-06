import CORALean.NN.Theorems.PropagateOuter

/-!
# An unsafe set disjoint from the propagated set is never reached

`MemSafeSet`'s counterpart, kept in its own file as `Specification`'s own
`Containment` and `Separation` keep the safe and unsafe directions apart:
directly off `propagate_outer`, with no `Specification` in sight.
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

theorem NeuralNetwork.not_mem_unsafeSet (nn : NeuralNetwork S n m) (X : S n)
    {unsafe' : Set (Vec ℝ m)} (h : Disjoint (construct (nn.propagate X)) unsafe')
    {x : Vec ℝ n} (hx : x ∈ construct X) : nn.eval x ∉ unsafe' :=
  Set.disjoint_left.mp h (nn.propagate_outer X x hx)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
