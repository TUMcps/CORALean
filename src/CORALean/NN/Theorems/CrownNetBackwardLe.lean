module

public import CORALean.NN.Operations.CrownBackward
public import CORALean.NN.Layers.Theorems.Real.CrownActivationStep
public import CORALean.NN.Layers.Theorems.Real.CrownAffineStep

@[expose] public section

/-!
# CROWN's backward pass is a lower bound

The row `μ` and the constant `c` of `CrownNet.backward` bound the row on the outputs from below at
every input where the network is `Holds`: `μ · x + c ≤ Λ · N(x)`. One induction over the layers,
each one step: `crown_affine_step` through a map (an equality), `crown_activation_step` through an
activation (the lines, on the box the input lies in).

## Inputs
* `net` – the network
* `Λ` – the row on the outputs
* `x` – the network's input, where the bound is read

## Hypotheses
* `hv` – every activation's input lies in its box, and the lines hold there

## Conclusion
* the row on the inputs at `x`, plus the constant, is at most the row on the outputs at `N(x)`
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n k : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem CrownNet.backward_le (net : CrownNet n k) (Λ : Vec ℝ k) (x : Vec ℝ n)
    (hv : net.Holds x) : -- --- CONCL ---
    ∑ j, (net.backward Λ).1 j * x j + (net.backward Λ).2
      ≤ ∑ i, Λ i * net.eval x i := by -- --- PROOF ---
  induction net with
  | nil => simp [CrownNet.backward, CrownNet.eval]
  | linear W b rest ih =>
    -- the layers after the map, at its outputs; the map moves the row exactly
    have h := ih Λ _ hv
    have hstep := crown_affine_step (rest.backward Λ).1 W b x
    simp only [CrownNet.backward, CrownNet.eval]
    linarith
  | act σ l u sl bl su bu rest ih =>
    obtain ⟨hbox, hlines, hrest⟩ := hv
    -- the layers after the activation, at its outputs; the lines move the row down
    have h := ih Λ _ hrest
    have hstep := crown_activation_step (rest.backward Λ).1 sl bl su bu x (fun i => σ (x i))
      (fun i => (hlines i (x i) (hbox i).1 (hbox i).2).1)
      (fun i => (hlines i (x i) (hbox i).1 (hbox i).2).2)
    simp only [CrownNet.backward, CrownNet.eval]
    linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
