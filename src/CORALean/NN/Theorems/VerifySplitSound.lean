import CORALean.NN.Operations.VerifySplit
import CORALean.NN.Theorems.HoldsOfPropagate
import CORALean.Specification.Theorems.HoldsUnion

/-!
# `verifySplit` is sound

The splitter owes no proof beyond `hcov`, the checker no completeness beyond
`hcheck`: `false` says only that this budget and this `splitter` did not
establish the specification, never that it fails.

Induction on `d`, generalising `X`: the recursive calls sit at different sets.
`d = 0` is `holds_of_propagate`; `d + 1` case-splits the `||`, the left
disjunct the same base case, the right combining both halves — verified at
depth `d` by the induction hypothesis — through `hcov X` and the binary
`Specification.holds_union`, `NeuralNetwork.holds_of_split` covers a single
propagated part, not a recursively re-verified one.

At `Interval`, `Interval.splitAt` supplies `splitter` and `Interval.
splitAt_cover` supplies `hcov`.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open ContSet

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `hverify` at depth `d` gives the specification on the exact image, never a
counterexample from a `false` result, and never that further splitting would help. -/
theorem NeuralNetwork.verifySplit_sound (nn : NeuralNetwork S n m)
    (spec : Specification (Vec ℝ m)) (check : S m → Bool)
    (hcheck : ∀ s, check s = true → spec.Holds (construct s))
    (splitter : S n → S n × S n)
    (hcov : ∀ Y : S n, construct Y ⊆ construct (splitter Y).1 ∪ construct (splitter Y).2)
    (d : ℕ) (X : S n) (hverify : nn.verifySplit check splitter d X = true) :
    spec.Holds (nn.image (construct X)) := by -- --- PROOF ---
  induction d generalizing X with
  | zero => exact nn.holds_of_propagate X spec (hcheck _ hverify)
  | succ d ih =>
    rw [NeuralNetwork.verifySplit, Bool.or_eq_true] at hverify
    rcases hverify with h | h
    · exact nn.holds_of_propagate X spec (hcheck _ h)
    · rw [Bool.and_eq_true] at h
      have hsub : nn.image (construct X)
          ⊆ nn.image (construct (splitter X).1) ∪ nn.image (construct (splitter X).2) :=
        calc nn.image (construct X) = nn.eval '' construct X := rfl
          _ ⊆ nn.eval '' (construct (splitter X).1 ∪ construct (splitter X).2) :=
              Set.image_mono (hcov X)
          _ = nn.eval '' construct (splitter X).1 ∪ nn.eval '' construct (splitter X).2 :=
              Set.image_union ..
      exact spec.holds_of_outer hsub (spec.holds_union (ih _ h.1) (ih _ h.2))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
