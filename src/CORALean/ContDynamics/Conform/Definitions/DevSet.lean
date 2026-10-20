module

public import CORALean.ContDynamics.Conform.Plant
public import Mathlib.Algebra.Group.Pointwise.Set.BigOperators
public import Mathlib.Data.Matrix.Mul

@[expose] public section

/-!
# The deviation set: the reachable outputs, the nominal run subtracted

`C Aᵏ X̃₀ ⊕ ⨁_{i<k} C Aⁱ W ⊕ V` — [1, Eq. 15]'s `R_a(k)` with the initial uncertainty
`X̃₀` of [2, Eq. 8] added (`Λ_k = C A_dᵏ`). Independent of the test case's initial
state and inputs, which is what lets one set check every test case at once.

`⨁` is Mathlib's pointwise sum of sets, over `Fin k`.

## Inputs
* `sys` – plant
* `X0` – initial uncertainty set
* `W` – disturbance set
* `V` – measurement noise set
* `k` – step

## Output
* the deviation set at step `k`: reachable outputs minus the nominal run

## References

* [1] S. B. Liu, B. Schürmann and M. Althoff. "Guarantees for Real Robotic Systems:
      Unifying Formal Controller Synthesis and Reachset-Conformant Identification". IEEE
      Transactions on Robotics, 39(5):3776-3790, 2023.
* [2] M. Althoff. "Checking and Establishing Reachset Conformance in CORA 2023". In Proc. of
      the 10th International Workshop on Applied Verification of Continuous and Hybrid
      Systems (ARCH23), EPiC Series in Computing, vol. 96, pp. 9-33, 2023.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Pointwise

variable {n p q : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Eq. 15]'s `R_a(k)`, with [2, Eq. 8]'s initial term `Λ_k X̃₀`. -/
def Conform.Plant.devSet (sys : Conform.Plant n p q) (X0 : Set (Vec ℝ n)) (W : Set (Vec ℝ n))
    (V : Set (Vec ℝ q)) (k : ℕ) : Set (Vec ℝ q) :=
  (fun x => (sys.C * sys.A ^ k) *ᵥ x) '' X0
    + ∑ i : Fin k, (fun x => (sys.C * sys.A ^ (i : ℕ)) *ᵥ x) '' W + V

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
