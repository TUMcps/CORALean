module

public import CORALean.NN.Layers.Definitions.Basic
public import CORALean.NN.Layers.Definitions.Relu
public import CORALean.NN.Layers.Operations.ReluStar
public import CORALean.NN.Layers.Theorems.StarSetReluNeuronOuter
public import CORALean.ContSet.StarSet.Real.Theorems.RowBoundsMem

@[expose] public section

/-!
# What the ReLU layer on a star set encloses

`relu (x_i)` coordinatewise. By induction over the neurons still to be visited: the neurons
visited so far are ReLU'd in the set, the rest untouched, and one more neuron's step encloses its
own ReLU on the set it is given, by `reluNeuron_outer` at the bounds that set satisfies.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      16-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet


-- =======================================  MAIN THEOREM  ======================================= --

theorem Layer.reluStar_sound (n : ℕ) :
    (Layer.reluStar n).Sound fun x i => Real.relu (x i) := by -- --- PROOF ---
  -- the ReLU at the neurons of a list, applied one neuron at a time
  have key : ∀ (L : List (Fin n)) (t : Real.StarSet Real.StarSet.LinPred n) (x : Vec ℝ n),
      x ∈ construct t →
      (fun i => if i ∈ L then Real.relu (x i) else x i : Vec ℝ n) ∈ construct
        (L.foldl (fun t j => t.reluNeuron j (t.rowBounds j)) t) := by
    intro L
    induction L with
    | nil => intro t x hx; simpa using hx
    | cons j L ih =>
      -- one more neuron: its step encloses its ReLU, then the rest of the list
      intro t x hx
      have h1 := Real.StarSet.reluNeuron_outer t j (t.rowBounds j)
        (fun y hy => Real.StarSet.rowBounds_mem t j hy) ⟨x, hx, rfl⟩
      have h2 := ih _ _ h1
      -- the two points are the same
      refine (congrArg (· ∈ construct _) ?_).mp h2
      funext i
      by_cases hij : i = j
      · subst hij; simp [Real.relu]
      · by_cases hiL : i ∈ L <;> simp [hij, hiL, Real.relu]
  refine ⟨fun s x hx => ?_⟩
  have := key (List.finRange n) s x hx
  simp only [List.mem_finRange, if_true] at this
  exact this

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
