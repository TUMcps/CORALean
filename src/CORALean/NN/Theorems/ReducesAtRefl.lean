import CORALean.NN.Reduction

/-!
# Doing nothing is a reduction

`refl` is what makes `reducesAt_outer` a generalisation of `enclose_outer` rather than a
different claim: taking `nn' = nn` — no `merge` step anywhere — is one of the derivations
`reducesAt_outer` is proved sound for, at the same map, by induction on `Sound` through
`keep`.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat ℝ) S] [IntervalOuter S] [OfInterval S]


-- =======================================  MAIN THEOREM  ======================================= --

/-- No layer is reduced: `nn` "reduces" to itself, through `keep` at every layer. -/
theorem NeuralNetwork.ReducesAt.refl : ∀ {n m : ℕ} {s : S n} {nn : NeuralNetwork S n m}
    {f : Vec ℝ n → Vec ℝ m}, nn.Sound f → NeuralNetwork.ReducesAt s nn nn f
  | _, _, s, _, _, .nil hid => .nil s hid
  | _, _, s, _, _, .cons hL hrest hcomp =>
      .keep s _ hL hcomp (NeuralNetwork.ReducesAt.refl hrest)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
