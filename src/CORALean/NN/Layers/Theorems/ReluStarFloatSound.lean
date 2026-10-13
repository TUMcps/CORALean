module

public import CORALean.NN.Layers.Operations.ReluStarFloat
public import CORALean.NN.Layers.Theorems.StarSetFloatReluNeuronOuter
public import CORALean.NN.Layers.Theorems.StarSetFloatRowBoundsMem

@[expose] public section

/-!
# What the float ReLU layer on a star set encloses

The ReLU image of the star set lies in the set the float layer returns, as in
`Layer.reluStar_sound`, the stored numbers read as reals.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Layer.reluStarFloat_sound (n : ℕ) :
    (Layer.reluStarFloat 𝕋 n).Sound fun x i => max (x i) 0 := by -- --- PROOF ---
  -- the ReLU at the neurons of a list, applied one neuron at a time
  have key : ∀ (L : List (Fin n)) (t : Float.StarSet 𝕋 n) (x : Vec ℝ n), x ∈ construct t →
      (fun i => if i ∈ L then max (x i) 0 else x i : Vec ℝ n) ∈ construct
        (L.foldl (fun t j => t.reluNeuron j (t.rowBounds j)) t) := by
    intro L
    induction L with
    | nil => intro t x hx; simpa using hx
    | cons j L ih =>
      -- one more neuron: its step encloses its ReLU, then the rest of the list
      intro t x hx
      have h1 := Float.StarSet.reluNeuron_outer t j (t.rowBounds j)
        (fun y hy => Float.StarSet.rowBounds_mem t j hy) ⟨x, hx, rfl⟩
      have h2 := ih _ _ h1
      refine (congrArg (· ∈ construct _) ?_).mp h2
      funext i
      by_cases hij : i = j
      · subst hij; simp
      · by_cases hiL : i ∈ L <;> simp [hij, hiL]
  refine ⟨fun s x hx => ?_⟩
  have := key (List.finRange n) s x hx
  simp only [List.mem_finRange, if_true] at this
  exact this

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
