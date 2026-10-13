import CORALean.NN.Operations.Enclose

/-!
# Verification by recursively splitting the input set, at any checker

`spec.Holds (construct s)` is a statement about a set of reals, not decidable,
so there is deliberately no `Decidable` instance here: the loop takes a
**sound checker**, a `Bool`-valued test whose `true` result a proof backs, and
the recursion is only about *where* to spend that checker, never about
deciding anything itself.

`d` is a depth budget, not a step count: the recursion is a binary tree and
`d` bounds its height. The `||` short-circuits, so a box the checker already
verifies is not split further, which is the whole point of the method.

`false` means only that this budget and this `splitter` did not establish the
specification here, not that it fails; see `Theorems.VerifySplitWithSound`.
`VerifySplit` is this at `Specification.check`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       06-September-2026
-- Last update:   24-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Check the whole box; if that fails and depth remains, split it and check both halves,
recursively. `splitter` owes no proof here, only at `Theorems.VerifySplitSound`. -/
def NeuralNetwork.verifySplitWith (nn : NeuralNetwork S n m) (check : S m → Bool)
    (splitter : S n → S n × S n) : ℕ → S n → Bool
  | 0, X => check (nn.enclose X)
  | d + 1, X =>
      check (nn.enclose X) ||
        (nn.verifySplitWith check splitter d (splitter X).1 &&
         nn.verifySplitWith check splitter d (splitter X).2)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
