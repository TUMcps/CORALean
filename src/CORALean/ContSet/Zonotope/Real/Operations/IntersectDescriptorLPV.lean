module

public import CORALean.ContSet.Zonotope.Real.Zonotope
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-!
# `Zonotope.intersectDescriptorLPV`

The intersection zonotope of [1, Cor. 1], its Eq. 15, for the descriptor LPV system
`E x_k = A(θ) x_{k-1} + B(θ) u_{k-1} + D(θ) d_{k-1}`, `y_k = C x_k + F d_k`, `d ∈ ⟨0, H_d⟩`
[1, Eq. 1], with the vertex matrices `A_j`, `B_j`, `D_j` and correction matrices `Λ_i` weighted
by `ρ_i(θ_{k-1})` [1, Eq. 2]: from `X = ⟨p̂, H̄⟩` (already reduced),
`p̂ = Σᵢ Σⱼ ρᵢρⱼ ((I - ΛᵢC)TAⱼ p̂ + (I - ΛᵢC)TBⱼ u) + Σᵢ ρᵢ (N - ΛᵢCN + Λᵢ) y` and the generators
`[Σᵢ Σⱼ ρᵢρⱼ (I - ΛᵢC)TAⱼ H̄  Σᵢ Σⱼ ρᵢρⱼ (I - ΛᵢC)TDⱼ H_d  Σᵢ ρᵢ (I - ΛᵢC)NF H_d  Σᵢ ρᵢ ΛᵢF H_d]`.
Real only, as `intersectDescriptor` is.

## Inputs
* `T` – decoupling matrix
* `N` – measurement decoupling matrix
* `ρ` – vertex weights
* `Λ` – correction matrices
* `A` – vertex state matrices
* `B` – vertex input matrices
* `D` – vertex disturbance matrices
* `C` – output matrix
* `F` – noise matrix
* `Hd` – disturbance generator matrix
* `u` – control input
* `y` – measurement
* `X` – reduced state zonotope

## Output
* enclosing intersection zonotope

## References

* [1] [Y. Wang, Z. Wang, V. Puig and G. Cembrano. "Zonotopic set-membership state estimation for
      discrete-time descriptor LPV systems". IEEE Transactions on Automatic Control,
      2019.](../../../../../../references/2019/wang-tac-descriptor-lpv-estimation.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n nu ny nd m r : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Zonotope.intersectDescriptorLPV (T : Mat ℝ n n) (N : Mat ℝ n ny) (ρ : Fin r → ℝ)
    (Λ : Fin r → Mat ℝ n ny) (A : Fin r → Mat ℝ n n) (B : Fin r → Mat ℝ n nu)
    (D : Fin r → Mat ℝ n nd) (C : Mat ℝ ny n) (F : Mat ℝ ny nd) (Hd : Mat ℝ nd m)
    (u : Vec ℝ nu) (y : Vec ℝ ny) (X : Zonotope (Vec ℝ n)) : Zonotope (Vec ℝ n) :=
  let p := ∑ i, ∑ j, (ρ i * ρ j) • ((1 - Λ i * C) *ᵥ (T *ᵥ (A j *ᵥ X.c)) +
      (1 - Λ i * C) *ᵥ (T *ᵥ (B j *ᵥ u))) +
    ∑ i, ρ i • ((N - Λ i * C * N + Λ i) *ᵥ y)  -- (15a)
  let H_A : Fin X.h → Vec ℝ n := fun g =>
    ∑ i, ∑ j, (ρ i * ρ j) • ((1 - Λ i * C) *ᵥ (T *ᵥ (A j *ᵥ X.G g))) -- (15b), first block
  let H_D : Fin m → Vec ℝ n := fun g k =>
    (∑ i, ∑ j, (ρ i * ρ j) • ((1 - Λ i * C) * T * D j * Hd) : Mat ℝ n m) k g  -- (15b), second block
  let H_N : Fin m → Vec ℝ n := fun g k =>
    (∑ i, ρ i • ((1 - Λ i * C) * N * F * Hd) : Mat ℝ n m) k g  -- (15b), third block
  let H_F : Fin m → Vec ℝ n := fun g k =>
    (∑ i, ρ i • (Λ i * F * Hd) : Mat ℝ n m) k g  -- (15b), fourth block
  { h := X.h + m + m + m
    c := p
    G := Fin.append (Fin.append (Fin.append H_A H_D) H_N) H_F }

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
