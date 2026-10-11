import CORALean.ContDynamics.NeurNetContrSysNL.Operations.Extended
import CORALean.NN.Operations.Enclose

/-!
# `Alg. 2`: reachable sets of a neural network controlled system

[1, Alg. 2]: over the control cycles, the image `Y` of the current reachable set through the network
([1, Alg. 1]), its Cartesian product with the set (equation (7)), the reachable sets at the end of
the cycle and over it for the extended system of equation (4), projected back (equation (5)). The
image is the network's `enclose`; the Cartesian product `cp`, the projection `pr` and the
reachability algorithm for the extended system `rx` are arguments, as [1] runs "arbitrary
reachability algorithms for nonlinear systems" and only writes the product and the projection for
polynomial zonotopes. The result is the set at the end and the sets over each cycle, newest first,
whose union is the paper's `R`.

## References

* [1] N. Kochdumper et al. "Open- and Closed-Loop Neural Network Verification
      using Polynomial Zonotopes". arXiv:2207.02715, 2022.
-/

-- Authors:       Tobias Ladner
-- Written:       11-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet

variable {n m r : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 2] over `H` control cycles from `X₀`: the set at the end of the last cycle and the
sets over the cycles, newest first. -/
def NeurNetContrSysNL.reach (sys : NeurNetContrSysNL S n m r) (cp : S n → S m → S (n + m))
    (pr : S (n + m) → S n) (rx : S (n + m) → S (n + m) × S (n + m)) (X₀ : S n) :
    ℕ → S n × List (S n)
  | 0 => (X₀, [])                                              -- 1: R(t₀) ← X₀
  | i + 1 =>
    let R := NeurNetContrSysNL.reach sys cp pr rx X₀ i           -- the loop so far
    let Y := sys.contr.enclose R.1                               -- 3: image through the network
    let R' := cp R.1 Y                                           -- 4: R̂(tᵢ) ← R(tᵢ) × Y
    let Rx := rx R'                                              -- 6: R̂(tᵢ₊₁), R̂(τᵢ)
    (pr Rx.1, pr Rx.2 :: R.2)                                    -- 7: project back

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
