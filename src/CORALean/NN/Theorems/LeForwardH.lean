module

public import CORALean.ContSet.Zonotope.Real.Definitions.SetBasedNetForward

@[expose] public section

/-!
# The forward propagation keeps the input's generators

`SetBasedNet.forward` never drops a generator: a linear layer maps each one and an activation
appends its error generators after them, so the input's `q₀` generators are the first `q₀` of
the output's `q_κ` ([1, Sec. 3]), the index range `[q₀] ⊆ [q_κ]` that [1, Prop. 2] reads
`G_y(·,[q₀])` from.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* the output has at least as many generators as the input

## References

* [1] L. Koller, T. Ladner and M. Althoff. "Out of the Shadows: Exploring a Latent Space for
      Neural Network Verification". ICLR, 2026.
-/

-- Authors:       Claude Opus 5.5
-- Written:       21-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- The forward propagation keeps every input generator: `q₀ ≤ q_κ`. -/
theorem SetBasedNet.le_forward_h : ∀ {n k : ℕ} (N : SetBasedNet n k) (X : Zonotope (Vec ℝ n)),
    X.h ≤ (N.forward X).h
  | _, _, .output, _ => le_rfl
  | _, _, .linear W b tail, X => tail.le_forward_h (X.affine W b)
  | _, _, .nonlinear m eLo eUp tail, X =>
      le_trans (Nat.le_add_right _ _) (tail.le_forward_h (X.imageEnclosure m eLo eUp))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
