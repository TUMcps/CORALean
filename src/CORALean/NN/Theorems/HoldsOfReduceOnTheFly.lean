import CORALean.NN.Theorems.HoldsOfReducesAt
import CORALean.NN.Theorems.ReduceOnTheFlyReducesAt

/-!
# [1, Thm. 1] for what [1, Alg. 2] actually returns

[1, Thm. 1]: given an input set `X`, a network `Φ` and a reduction rate `ρ`, [1, Alg. 2]
constructs a reduced network `Φ̂_ρ` for which verification entails verifying `Φ` — checking
a specification on the output set `Y` the algorithm computed is checking it on `Φ(X)`.
`reduceOnTheFly_reducesAt` puts the output in `ReducesAt`, and `holds_of_reducesAt` is the
rest. It holds at every `le`, `tol`, `fuel` and `ρ`, and at every instance of a network in
[1, Eq. 2]'s form, the original network — every `I' = [0, 0]` — being the one [1] means.

## References

* [1] T. Ladner and M. Althoff. "Fully Automatic Neural Network Reduction for
      Formal Verification". TMLR. arXiv:2305.01932.
-/

-- Authors:       Tobias Ladner
-- Written:       23-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open ContSet

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat ℝ) S] [IntervalOuter S] [OfInterval S]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Thm. 1]: a specification holding on the output set `Y` of [1, Alg. 2] holds on the
original network's exact image of `X`. -/
theorem holds_of_reduceOnTheFly {le : ℝ → ℝ → Bool} {tol : ℝ} {fuel : ℕ} {ρ : ℝ} {n m : ℕ}
    {X : S n} {Φ Φhat : ReducibleNetwork n m} {Y : S m} {nn : NeuralNetwork S n m}
    {f : Vec ℝ n → Vec ℝ m} (hΦ : Φ.Instance nn f)
    (hrun : reduceOnTheFly le tol fuel X ρ Φ = some (Φhat, Y))
    (spec : Specification (Vec ℝ m)) (hspec : spec.Holds (construct Y)) :
    spec.Holds (f '' construct X) := by
  obtain ⟨hred, rfl⟩ := reduceOnTheFly_reducesAt hΦ hrun
  exact NeuralNetwork.holds_of_reducesAt hred spec hspec

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
