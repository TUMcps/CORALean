module

public import CORALean.ContDynamics.NeurNetContrSys.Operations.AppendU2X
public import CORALean.ContSet.Zonotope.Float.Operations.CompactZeros
public import CORALean.ContSet.Zonotope.Float.Operations.CompactZerosFrom

@[expose] public section

/-!
# The joint set of a state set and a network's image of it

[1, Alg. 2] lines 3-4, `R̂(tᵢ) ← R(tᵢ) × Y` with `Y` the network's image of `R(tᵢ)`, as CORA's
`neurNetContrSys/reach` hands it to the plant (`evaluate_` and `aux_appendU2X`). The state set
is compacted of its zero generators and the network, `E`, run on that; the image is compacted of
its zero generators past those of the state set, which `appendU2X` shares with it, and the two
are joined. `none` if the image has fewer generators than the state set.

## Inputs
* `E` – the network's image of a zonotope
* `X` – state set

## Output
* the joint zonotope of the state and the network's output, or none

## References

* [1] [N. Kochdumper, C. Schilling, M. Althoff and S. Bak. "Open- and Closed-Loop Neural Network
      Verification using Polynomial Zonotopes". arXiv preprint arXiv:2207.02715,
      2022.](../../../../../references/2022/kochdumper-arxiv-nn-polyzono.md)
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       13-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def NeurNetContrSys.joint (E : Zonotope (Vec 𝕋 n) → Zonotope (Vec 𝕋 m))
    (X : Zonotope (Vec 𝕋 n)) : Option (Zonotope (Vec 𝕋 (n + m))) :=
  -- the state set without its zero generators
  let Xc := X.compactZeros
  -- its image, the generators past those of `Xc` kept only if not zero
  let Y := (E Xc).compactZerosFrom Xc.h
  -- 3-4. `R̂(tᵢ) ← R(tᵢ) × Y`
  NeurNetContrSys.appendU2X Xc Y

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
