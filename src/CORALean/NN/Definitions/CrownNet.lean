module

public import CORALean.Global.Tensor
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# The networks of CROWN's backward bound

CORA.cpp's backward bound (`priv_backward_lower`) runs over a chain of affine maps and element-wise
activations, each activation given with the box `[l, u]` of its inputs (the record of the forward
pass) and two lines per neuron, `s_l t + b_l ≤ σ t ≤ s_u t + b_u`. `CrownNet` is that chain over
ℝ; `eval` is the exact network, and `Holds` the two facts the bound rests on, at one input:
every activation's input lies in its box, and the lines hold on the box.

-/

-- Authors:       Claude Opus 5.5
-- Written:       23-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- ========================================  MAIN TYPE  ========================================= --

/-- A chain of affine maps `x ↦ W x + b` and element-wise activations `σ`, an activation with its
input box `[l, u]` and its lower and upper lines `sl t + bl`, `su t + bu`. -/
inductive CrownNet : ℕ → ℕ → Type where
  | nil {n : ℕ} : CrownNet n n
  | linear {n m k : ℕ} (W : Mat ℝ m n) (b : Vec ℝ m) (rest : CrownNet m k) : CrownNet n k
  | act {n k : ℕ} (σ : ℝ → ℝ) (l u sl bl su bu : Vec ℝ n) (rest : CrownNet n k) : CrownNet n k

/-- The exact network: the maps and the activations composed. -/
noncomputable def CrownNet.eval : {n k : ℕ} → CrownNet n k → Vec ℝ n → Vec ℝ k
  | _, _, .nil, x => x
  | _, _, .linear W b rest, x => rest.eval fun i => ∑ j, W i j * x j + b i
  | _, _, .act σ _ _ _ _ _ _ rest, x => rest.eval fun i => σ (x i)

/-- At the input `x`: every activation's input lies in its box, and its lines hold on the box. -/
def CrownNet.Holds : {n k : ℕ} → CrownNet n k → Vec ℝ n → Prop
  | _, _, .nil, _ => True
  | _, _, .linear W b rest, x => rest.Holds fun i => ∑ j, W i j * x j + b i
  | _, _, .act σ l u sl bl su bu rest, z =>
      (∀ i, l i ≤ z i ∧ z i ≤ u i) ∧
      (∀ i t, l i ≤ t → t ≤ u i → sl i * t + bl i ≤ σ t ∧ σ t ≤ su i * t + bu i) ∧
      rest.Holds fun i => σ (z i)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
