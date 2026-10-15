module

public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Operations.MtimesCost
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Operations.PlusCost
public import CORALean.ContSet.Zonotope.Real.Operations.ImageEnclosure

@[expose] public section

/-!
# `Zonotope.imageEnclosureCost`

Asserted, not proved, as [1, Prop. 15]'s proof counts [1, Alg. 1]: the bounds `c ∓ |G| 1` of the
input (line 2, Prop. 2) at `2n(q + 1)`; per neuron the slope and the approximation errors
(lines 3-5, Def. 7 and Prop. 10) at a constant `cNeuron`; `Diag(m) H` (line 6) as Prop. 4's
matrix product, `Zonotope.mtimesCost n n q`, and the `n` additions of the offset; and the sum
with the interval (line 7, Prop. 3), `Zonotope.plusCost n q n`, after the `n * (n + 1)` writes
of the interval as a zonotope, the diagonal of its `n` generators and its center.
`Operations/ImageEnclosure.lean`
reads the same per-row quantities. The proved part is the bound [1, Prop. 15] states,
`O(n² q)` in `n` and `q`: at most `(cNeuron + 17) n² q` once `n, q ≥ 1`.

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

/-- What [1, Alg. 1] costs at `n` dimensions, `q` generators and `cNeuron` per neuron. -/
def Zonotope.imageEnclosureCost (n q : ℕ) (cNeuron : Cost) : Cost :=
  -- 2. the bounds `c ∓ |G| 1` of the input
  let bounds : Cost := ⟨2 * (n * (q + 1))⟩
  -- 3-5. the slope and the errors of every neuron
  let neurons : Cost := n • cNeuron
  -- 6. `Diag(m) H`, and the offset
  let scaled : Cost := Zonotope.mtimesCost n n q + ⟨n⟩
  -- 7. the sum with the interval, written as a zonotope
  let sum : Cost := ⟨n * (n + 1)⟩ + Zonotope.plusCost n q n
  bounds + neurons + scaled + sum

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
