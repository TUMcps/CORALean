module

public import CORALean.NN.Operations.VerifySplitWith
public import CORALean.NN.Theorems.SoundHoldsOfEnclose
public import CORALean.Specification.Theorems.HoldsUnion

@[expose] public section

/-!
# `verifySplitWith` is sound, at any checker backed by a proof

The splitter owes no proof beyond `hcov`, the checker no completeness beyond
`hcheck`: `false` says only that this budget and this `splitter` did not
establish the specification, never that it fails.

Induction on `d`, generalising `X`: the recursive calls sit at different sets.
`d = 0` is `holds_of_enclose`; `d + 1` case-splits the `||`, the left
disjunct the same base case, the right combining both halves — verified at
depth `d` by the induction hypothesis — through `hcov X` and the binary
`Specification.holds_union`, `NeuralNetwork.holds_of_split` covers a single
enclosed part, not a recursively re-verified one.

At `Interval`, `Interval.splitAt` supplies `splitter` and `Interval.
splitAt_cover` supplies `hcov`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       06-September-2026
-- Last update:   24-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] {n m : ℕ}
variable {ContSet : Type} [CORALean.ContSet ContSet (Vec ℝ m)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- `hverify` at depth `d` gives the specification on the exact image, never a
counterexample from a `false` result, and never that further splitting would help. -/
theorem NeuralNetwork.Sound.verifySplitWith_sound {nn : NeuralNetwork S n m}
    {f : Vec ℝ n → Vec ℝ m} (hf : nn.Sound f) (spec : Specification ContSet) (check : S m → Bool)
    (hcheck : ∀ s, check s → spec.Holds (construct s))
    (splitter : S n → S n × S n)
    (hcov : ∀ Y : S n, construct Y ⊆ construct (splitter Y).1 ∪ construct (splitter Y).2)
    (d : ℕ) (X : S n) (hverify : nn.verifySplitWith check splitter d X) :
    spec.Holds (f '' construct X) := by -- --- PROOF ---
  induction d generalizing X with
  | zero => exact hf.holds_of_enclose X spec (hcheck _ hverify)
  | succ d ih =>
    rw [NeuralNetwork.verifySplitWith, Bool.or_eq_true] at hverify
    rcases hverify with h | h
    · exact hf.holds_of_enclose X spec (hcheck _ h)
    · rw [Bool.and_eq_true] at h
      have hsub : f '' construct X
          ⊆ f '' construct (splitter X).1 ∪ f '' construct (splitter X).2 :=
        calc f '' construct X
            ⊆ f '' (construct (splitter X).1 ∪ construct (splitter X).2) :=
              Set.image_mono (hcov X)
          _ = f '' construct (splitter X).1 ∪ f '' construct (splitter X).2 :=
              Set.image_union ..
      exact spec.holds_of_outer hsub (spec.holds_union (ih _ h.1) (ih _ h.2))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
