module

public import CORALean.ContSet.Zonotope.Real.Zonotope
public import Mathlib.Data.Matrix.Mul

@[expose] public section

/-!
# `Zonotope.intersectDescriptor`

The intersection zonotope of [1, Thm. 1], one step of the set-membership estimator for the
descriptor system `E x₊ = A x + B u + D ω + D_d d`, `y = C x + F υ` [1, Eq. 4]: from
`X = ⟨p̂, H̄⟩` (already reduced), the measurement `y₊` and the correction matrix `Λ`, Eq. 7 gives
`p̂₊ = (I - ΛC)TA p̂ + (I - ΛC)TB u + (N + Λ - ΛCN) y₊` and
`Ĥ₊ = [(I - ΛC)TA H̄  (I - ΛC)TD  (I - ΛC)NF  ΛF]`, with `T`, `N` decoupling the unknown input,
`TE + NC = I`, `TD_d = 0` [1, Eq. 6]. At `E = I` (`T = I`, `N = 0`) it is `intersectStrip` after
the prediction, as CORA's `FRad-B` and `PRad-C` use it. `Λ` is any matrix; the enclosure holds
for each.

## Inputs
* `T` – decoupling matrix
* `N` – measurement decoupling matrix
* `Λ` – correction matrix
* `A` – state matrix
* `B` – input matrix
* `D` – disturbance matrix
* `C` – output matrix
* `F` – noise matrix
* `u` – control input
* `y` – measurement
* `X` – reduced state zonotope

## Output
* enclosing intersection zonotope

## References

* [1] Y. Wang, V. Puig and G. Cembrano. "Set-membership approach and Kalman observer based on
      zonotopes for discrete-time descriptor systems". Automatica, 93:435-443, 2018.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n nu nw ny nv : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Zonotope.intersectDescriptor (T : Mat ℝ n n) (N Λ : Mat ℝ n ny) (A : Mat ℝ n n)
    (B : Mat ℝ n nu) (D : Mat ℝ n nw) (C : Mat ℝ ny n) (F : Mat ℝ ny nv) (u : Vec ℝ nu)
    (y : Vec ℝ ny) (X : Zonotope (Vec ℝ n)) : Zonotope (Vec ℝ n) :=
  let K : Mat ℝ n n := 1 - Λ * C                                             -- I - ΛC
  let p_plus := K *ᵥ (T *ᵥ (A *ᵥ X.c)) + K *ᵥ (T *ᵥ (B *ᵥ u)) + (N + Λ - Λ * C * N) *ᵥ y  -- Eq. 7a
  let H_A : Fin X.h → Vec ℝ n := fun j => K *ᵥ (T *ᵥ (A *ᵥ X.G j))           -- (I - ΛC)TA H̄
  let H_D : Fin nw → Vec ℝ n := fun j i => (K * T * D) i j                  -- (I - ΛC)TD
  let H_N : Fin nv → Vec ℝ n := fun j i => (K * N * F) i j                  -- (I - ΛC)NF
  let H_F : Fin nv → Vec ℝ n := fun j i => (Λ * F) i j                      -- ΛF
  { h := X.h + nw + nv + nv
    c := p_plus
    G := Fin.append (Fin.append (Fin.append H_A H_D) H_N) H_F }             -- Eq. 7b

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
