import CORALean.NN.Definitions.Reduction

/-!
# `ReducesAt` is about a function, not how it is written

Every constructor of `ReducesAt` names its map only through an equation `∀ x, f x = …`, so
replacing `f` by a map that agrees with it everywhere is one rewrite in that equation. It is
what lets a caller state the map in its own terms, as `NeuralNetwork.Sound.congr` does.
-/

-- Authors:       Tobias Ladner
-- Written:       23-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat ℝ) S] [Real.IntervalOuter S] [Real.OfInterval S]


-- =======================================  MAIN THEOREM  ======================================= --

/-- A reduction at `f` is one at every map agreeing with `f` everywhere. -/
theorem NeuralNetwork.ReducesAt.congr {n m : ℕ} {s : S n} {nn nn' : NeuralNetwork S n m}
    {f f' : Vec ℝ n → Vec ℝ m} (h : NeuralNetwork.ReducesAt s nn nn' f)
    (hff : ∀ x, f' x = f x) : NeuralNetwork.ReducesAt s nn nn' f' := by -- --- PROOF ---
  -- each constructor carries its map in one equation, rewritten here and nowhere else
  cases h with
  | nil _ hf => exact .nil _ fun x => (hff x).trans (hf x)
  | keep _ L hg hf hrest => exact .keep _ L hg (fun x => (hff x).trans (hf x)) hrest
  | merge _ part W0 b0 R hR W1 b1 Y hY hf hrest =>
    exact .merge _ part W0 b0 R hR W1 b1 Y hY (fun x => (hff x).trans (hf x)) hrest
  | widen _ W c b E hc hf hrest =>
    exact .widen _ W c b E hc (fun x => (hff x).trans (hf x)) hrest
  | freeze _ part W0 c0 b0 E0 hc0 R hR W1 c1 Y hY hf hrest =>
    exact .freeze _ part W0 c0 b0 E0 hc0 R hR W1 c1 Y hY (fun x => (hff x).trans (hf x)) hrest

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
