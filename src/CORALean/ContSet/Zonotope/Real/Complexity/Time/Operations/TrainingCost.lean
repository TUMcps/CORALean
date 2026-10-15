module

public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Operations.ForwardCost
public import Mathlib.Tactic.Ring
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Operations.ImageEnclosureCost
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Operations.MtimesCost
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Operations.PlusCost

@[expose] public section

/-!
# `SetBasedNet.trainingCost`

Asserted, not proved, as [1, Prop. 17]'s proof counts one iteration of set-based training,
[1, Alg. 2], which has no Lean definition of its own: per layer the forward step of
`SetBasedNet.forwardCost`; at a linear `m × n` layer the backward map `W_kᵀ 𝒢_k` (line 11,
Prop. 4), the weight gradient `𝒢_k ⊙ H_{k-1}ᵀ = c'cᵀ + G'Gᵀ` with its update (line 12, Prop. 14),
`2mn(h + 1) + 2mn`, and the bias update (line 13), `2m`; at a nonlinear layer `backpropEnclose`
(line 15, Prop. 12), per dimension the sum `c'c + G'Gᵀ` at `2h + 2`, and per entry the gradients
of the slope and the errors at a constant `cBack` and their combination at `10`; and at the
output the loss gradient (line 8, Prop. 9), `n_κ(h + 1)` entries at `cGrad` each. The proved
part is [1, Prop. 17]'s `O(n_max² q κ)`, at most `2 C N² Q κ` for `κ ≥ 1`, with `N` covering
every width, the input's included, as for [1, Prop. 16].

Each count above also writes the result it computes, one unit per scalar: the new weights
`m n` and the new bias `m` at a linear layer, the `n` sums and the `n (h + 1)` combined
gradients at a nonlinear one (the combination at `11`: its `10` operations and the write).
`cGrad`, `cBack` and `cNeuron` count what one application does, the write of its value included.

## References

* [1] L. Koller, T. Ladner and M. Althoff. "Set-Based Training for Neural Network Verification".
      Transactions on Machine Learning Research (TMLR), 2025.
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       11-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What one iteration of [1, Alg. 2] costs from an input set with `h` generators. -/
def SetBasedNet.trainingCost (cNeuron cGrad cBack : Cost) :
    {n k : ℕ} → SetBasedNet n k → ℕ → Cost
  -- 8. the output set `Y`: the loss gradient `G_κ ← ∇_Y L(t, Y)`
  | n, _, .output, h => (n * (h + 1)) • cGrad
  | n, _, @SetBasedNet.linear _ m _ _ _ tail, h =>
      -- 4. the forward step `H_k ← W_k H_{k-1} + b_k`
      Zonotope.mtimesCost m n h + Zonotope.plusCost m h 0 +
        -- 11. the backward map `G_{k-1} ← W_kᵀ G_k`
        Zonotope.mtimesCost n m h +
        -- 12. the weight update `W_k ← W_k - η (G_k ⊙ H_{k-1}ᵀ)`, and 13. the bias update
        ⟨2 * (m * n * (h + 1)) + 2 * (m * n) + m * n⟩ + ⟨2 * m + m⟩ +
        -- 2. the layers after this one, forward (lines 2-6) and back (lines 9-15)
        tail.trainingCost cNeuron cGrad cBack h
  | n, _, .nonlinear _ _ _ tail, h =>
      -- 6. the forward step `H_k ← enclose(ϕ_k, H_{k-1})`
      Zonotope.imageEnclosureCost n h cNeuron + ⟨n * (2 * h + 2) + n + 11 * (n * (h + 1))⟩ +
        -- 15. the backward step `G_{k-1} ← backpropEnclose(ϕ_k, G_k)`
        (n * (h + 1)) • cBack +
        -- 2. the layers after this one, forward (lines 2-6) and back (lines 9-15)
        tail.trainingCost cNeuron cGrad cBack (h + n)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
