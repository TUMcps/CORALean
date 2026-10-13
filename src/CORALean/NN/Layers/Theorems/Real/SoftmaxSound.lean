module

public import CORALean.NN.Layers.Definitions.Softmax
public import CORALean.NN.Layers.Theorems.Real.RawLeSoftmax
public import CORALean.NN.Layers.Theorems.Real.SoftmaxLeRaw
public import CORALean.NN.Layers.Theorems.Real.SoftmaxMemTightened

@[expose] public section

/-!
# What the exact softmax layer encloses

ℝ-only, the exact box needing both raw bounds and so an upper bound on an exponential: the raw
bounds hold at every point of the box, and the normalization tightens each coordinate by what
the others leave over.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open ContSet IntervalOuter OfInterval

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [IntervalOuter S] [OfInterval S] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Layer.softmax_sound :
    (Layer.softmax (S := S) (n := n)).Sound _root_.CORALean.Real.softmax := by -- --- PROOF ---
  refine ⟨fun s x hx => ?_⟩
  have hbox : ∀ i, (interval s).inf i ≤ x i ∧ x i ≤ (interval s).sup i :=
    interval_outer s hx
  refine ofInterval_outer _ fun i => ?_
  exact softmax_mem_tightened x (softmaxRawLower (interval s))
    (softmaxRawUpper (interval s)) (fun i => raw_le_softmax hbox i)
    (fun i => softmax_le_raw hbox i) i

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
