module

public import CORALean.ContDynamics.LinearSysDT.LinearSysDT
public import CORALean.ContSet.Zonotope.Real.Operations.IntersectDescriptorLPV

@[expose] public section

/-!
# The zonotopic set-membership estimator for descriptor LPV systems

[1, Alg. 1]: from `X̂₀ = X₀` (lines 1-2), at every step the weights `ρ(θ_{k-1})` (line 5) and
the measurement `y_k` (line 6) give the intersection zonotope of [1, Cor. 1] (line 7) from the
reduced previous one, `↓(X̂_{k-1})` [1, Remark 2], with the offline vertex gains `Λᵢ` (line 3,
taken as given; the solver is not part of the algorithm's guarantee). Line 8's bounds are the
zonotope's box, `Zonotope.interval`. The reduction is a parameter, as `↓_{q,W}` is any outer
reduction for the enclosure. Real only, as the other descriptor estimators are.

## Inputs
* `T` – decoupling matrix
* `N` – measurement decoupling matrix
* `C` – output matrix
* `F` – noise matrix
* `Hd` – disturbance generator matrix
* `A` – vertex state matrices
* `B` – vertex input matrices
* `D` – vertex disturbance matrices
* `Λ` – correction matrices
* `ρ` – vertex weights per step
* `red` – zonotope reduction
* `X₀` – initial zonotope
* `u` – inputs
* `y` – measurements

## Output
* the estimator zonotope after each number of steps

## References

* [1] Y. Wang, Z. Wang, V. Puig and G. Cembrano. "Zonotopic set-membership state estimation for
      discrete-time descriptor LPV systems". IEEE Transactions on Automatic Control,
      64(5):2092-2099, 2019.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real

variable {n nu ny nd m r : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `X̂_k`, the estimator's zonotope at step `k`. -/
def LinearSysDT.observeDescriptorLPV (T : Mat ℝ n n) (N : Mat ℝ n ny) (C : Mat ℝ ny n)
    (F : Mat ℝ ny nd) (Hd : Mat ℝ nd m) (A : Fin r → Mat ℝ n n) (B : Fin r → Mat ℝ n nu)
    (D : Fin r → Mat ℝ n nd) (Λ : Fin r → Mat ℝ n ny) (ρ : ℕ → Fin r → ℝ)
    (red : Zonotope (Vec ℝ n) → Zonotope (Vec ℝ n)) (X₀ : Zonotope (Vec ℝ n))
    (u : ℕ → Vec ℝ nu) (y : ℕ → Vec ℝ ny) : ℕ → Zonotope (Vec ℝ n)
  | 0 => X₀  -- line 2
  | k + 1 =>
    let Xprev := red (LinearSysDT.observeDescriptorLPV T N C F Hd A B D Λ ρ red X₀ u y k)
    let θ := ρ k  -- line 5, the weights at `θ_k`
    let yk := y (k + 1)  -- line 6
    Xprev.intersectDescriptorLPV T N θ Λ A B D C F Hd (u k) yk  -- line 7, Eq. 15

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
