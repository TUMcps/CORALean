module

public import CORALean.ContDynamics.NeurNetContrSys.NeurNetContrSys
public import CORALean.NN.Operations.Enclose

@[expose] public section

/-!
# `Alg. 2`: reachable sets of a neural network controlled system

[1, Alg. 2], CORA's `neurNetContrSys/reach`: over the control cycles, the image `Y` of the
current reachable set through the network ([1, Alg. 1]), its Cartesian product with the set
(equation (7), CORA's `aux_appendU2X`), the reachable sets at the end of the cycle and over it
for the extended system of equation (4), projected back (equation (5)). The image is the
network's `enclose`; the Cartesian product `cp`, the projection `pr` and the reachability
algorithm for the extended system `rx` are arguments, as [1] runs "arbitrary reachability
algorithms for nonlinear systems" and CORA's `aux_reachability` chooses the plant's own by its
class. `rx` returns the set at the end of the cycle and the sets over it (CORA's `timePoint` and
`timeInterval`); the result is the set at the end and the sets over the cycles, newest first,
whose union is the paper's `R`.

## References

* [1] N. Kochdumper et al. "Open- and Closed-Loop Neural Network Verification
      using Polynomial Zonotopes". arXiv:2207.02715, 2022.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet
open ContDynamics

variable {n : ℕ} {P : Type} [ContDynamics P n]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 2] over `H` control cycles from `X₀`: the set at the end of the last cycle and the
sets over the cycles, newest first. -/
def NeurNetContrSys.reachWith (sys : NeurNetContrSys P S n)
    (cp : S n → S (nrOfInputs sys.plant) → S (n + nrOfInputs sys.plant))
    (pr : S (n + nrOfInputs sys.plant) → S n)
    (rx : S (n + nrOfInputs sys.plant) → S (n + nrOfInputs sys.plant) × List (S
        (n + nrOfInputs sys.plant)))
    (X₀ : S n) : ℕ → S n × List (S n)
  -- 1. `R(t₀) ← X₀`
  | 0 => (X₀, [])
  | i + 1 =>
    -- the loop so far, `i` cycles
    let R := NeurNetContrSys.reachWith sys cp pr rx X₀ i
    -- 3. the image `Y` through the network, `enclose`
    let Y := sys.contr.enclose R.1
    -- 4. `R̂(tᵢ) ← R(tᵢ) × Y`
    let R' := cp R.1 Y
    -- 6. `R̂(tᵢ₊₁), R̂(τᵢ)` by the reachable-set step
    let Rx := rx R'
    -- 7. project back, `R(tᵢ₊₁) ← proj(R̂(tᵢ₊₁))`
    (pr Rx.1, Rx.2.map pr ++ R.2)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
