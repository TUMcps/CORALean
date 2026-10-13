module

public import CORALean.ContSet.Zonotope.Real.Definitions.SetBasedNetForward
public import CORALean.ContSet.Zonotope.Real.Operations.SetBasedNetNeurons

@[expose] public section

/-!
# `SetBasedNet.forward_h_le`

[1, Prop. 16], the size: a set-based forward propagation adds at most `Σ_{k ∈ [κ]} n_k`
generators, `n_k` at each nonlinear layer (`Zonotope.imageEnclosure`) and none at a linear one
(`Zonotope.affine`); from the input set `⟨x, εI_{n₀}⟩` with its `n₀`, at most
`n₀ + Σ_{k ∈ [κ]} n_k`.
Every intermediate set is the output of the first layers, whose sum is a part of this one.

## References

* [1] L. Koller, T. Ladner and M. Althoff. "Set-Based Training for Neural Network Verification".
      Transactions on Machine Learning Research (TMLR), 2025.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem SetBasedNet.forward_h_le : ∀ {n k : ℕ} (net : SetBasedNet n k) (H : Zonotope (Vec ℝ n)),
    (net.forward H).h ≤ H.h + net.neurons
  | _, _, .output, _ => Nat.le_add_right _ _
  | _, _, .linear W b tail, H => by
      have := SetBasedNet.forward_h_le tail (H.affine W b)
      show (tail.forward (H.affine W b)).h ≤ H.h + (_ + tail.neurons)
      have h' : (H.affine W b).h = H.h := rfl
      omega
  | _, _, .nonlinear m eLo eUp tail, H => by
      have := SetBasedNet.forward_h_le tail (H.imageEnclosure m eLo eUp)
      show (tail.forward (H.imageEnclosure m eLo eUp)).h ≤ H.h + (_ + tail.neurons)
      have h' : (H.imageEnclosure m eLo eUp).h = H.h + _ := rfl
      omega

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
