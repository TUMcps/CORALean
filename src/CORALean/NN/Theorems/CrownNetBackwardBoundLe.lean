module

public import CORALean.NN.Operations.CrownBackwardBound
public import CORALean.NN.Theorems.CrownNetBackwardLe
public import CORALean.NN.Layers.Theorems.Real.CrownBoxLe

@[expose] public section

/-!
# CROWN's backward bound is sound

CORA.cpp's request `backward_bound_sound`: for a chain of affine maps and activations whose inputs
lie in their boxes `[l_k, u_k]` and whose lines hold on them, CROWN's backward bound is at most
`Λ · N(x)` at every `x` of the box `|x - x₀| ≤ r`. `CrownNet.backward_le` at `x`, and the row on
the box at its worst point (`crown_box_le`).

## Inputs
* `net` – the network
* `Λ` – the row on the outputs
* `x₀` – the box's center
* `r` – the box's radius
* `x` – a point of the box

## Hypotheses
* `hx` – the point lies in the box
* `hv` – every activation's input lies in its box at `x`, and the lines hold there

## Conclusion
* the backward bound is at most the row on the outputs at `N(x)`
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n k : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem CrownNet.backwardBound_le (net : CrownNet n k) (Λ : Vec ℝ k) (x₀ r x : Vec ℝ n)
    (hx : ∀ j, |x j - x₀ j| ≤ r j) (hv : net.Holds x) : -- --- CONCL ---
    net.backwardBound Λ x₀ r ≤ ∑ i, Λ i * net.eval x i := by -- --- PROOF ---
  have hback := net.backward_le Λ x hv
  have hbox := crown_box_le (net.backward Λ).1 x₀ r x hx
  show ∑ j, (net.backward Λ).1 j * x₀ j - ∑ j, |(net.backward Λ).1 j| * r j
    + (net.backward Λ).2 ≤ _
  linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
