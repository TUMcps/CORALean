module

public import CORALean.ContDynamics.NeurNetContrSys.Operations.Joint
public import CORALean.ContDynamics.NeurNetContrSys.Theorems.AppendU2XMem
public import CORALean.ContSet.Zonotope.Float.Theorems.CompactZerosExact
public import CORALean.ContSet.Zonotope.Float.Theorems.CompactZerosFromTracks

@[expose] public section

/-!
# The joint set holds the state and the network's output, for every state

The state set loses its zero generators without losing a point (`compactZeros_exact`), the
network is run on what is left, and its image loses its zero generators past those of the state
set without losing the tracking (`compactZerosFrom_tracks`). What remains is `appendU2X_mem`: the
joint set holds the stacked state and output ([1, Alg. 2], lines 3-4).

## Inputs
* `E` – the network's image of a zonotope
* `π` – controller function
* `X` – state set

## Hypotheses
* `hE` – the image of every zonotope tracks the controller over it

## Conclusion
* the state and the controller's output, stacked, lie in the joint set

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

open CORALean.Float FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem NeurNetContrSys.joint_mem {E : Zonotope (Vec 𝕋 n) → Zonotope (Vec 𝕋 m)}
    {π : Vec ℝ n → Vec ℝ m} (hE : ∀ X : Zonotope (Vec 𝕋 n), X.Tracks (E X) π)
    (X : Zonotope (Vec 𝕋 n)) : -- --- CONCL ---
    ∀ J ∈ NeurNetContrSys.joint E X, ∀ x ∈ X.toSet,
      (Fin.append x (π x) : Vec ℝ (n + m)) ∈ J.toSet := by -- --- PROOF ---
  intro J hJ x hx
  -- the state is in the compacted state set, whose image tracks the controller
  rw [← Zonotope.compactZeros_exact X] at hx
  exact NeurNetContrSys.appendU2X_mem (Zonotope.compactZerosFrom_tracks (hE _)) J hJ x hx

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
