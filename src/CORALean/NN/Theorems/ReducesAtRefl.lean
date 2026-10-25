module

public import CORALean.NN.Definitions.Reduction
public import CORALean.NN.Definitions.Encloses

@[expose] public section

/-!
# Doing nothing is a reduction

`refl` is what makes `reducesAt_outer` a generalisation of `enclose_outer` rather than a
different claim: taking `nn' = nn` — no `merge` step anywhere — is one of the derivations
`reducesAt_outer` is proved sound for, at the same map, by induction on `IsSound` through
`keep`.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* a network that encloses a map reduces to itself at that map
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat ℝ) S] [Real.IntervalOuter S] [Real.OfInterval S]


-- =======================================  MAIN THEOREM  ======================================= --

/-- No layer is reduced: `nn` "reduces" to itself, through `keep` at every layer. -/
theorem NeuralNetwork.ReducesAt.refl : ∀ {n m : ℕ} {s : S n} {nn : NeuralNetwork S n m}
    {f : Vec ℝ n → Vec ℝ m}, nn.Encloses f → NeuralNetwork.ReducesAt s nn nn f
  | _, _, s, _, _, .output hid => .nil s hid
  | _, _, s, _, _, .layer (inst := _) hL hrest hcomp =>
      .keep s _ hL hcomp (NeuralNetwork.ReducesAt.refl hrest)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
