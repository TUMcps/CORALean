module

public import CORALean.ContSet.Zonotope.Real.Zonotope
public import Mathlib.Data.Matrix.Mul

@[expose] public section

/-!
# `Zonotope.observeDescriptorCurrent`

The zonotope of the current-estimation-type observer of Eq. 37 of [1, Thm. 7] and Eq. 38 of [1, Thm.
7]: from `X = ⟨p̂, H̄⟩`, the measurement `y₊` and the gain `Ĝ`, Eq. 39 of [1, Thm. 7] gives `p̃₊(Ĝ)
= (I - ĜC)TA p̂ + (I - ĜC)TB u + (N + Ĝ - ĜCN) y₊` and `H̃₊(Ĝ) = [(I - ĜC)TA H̄  (I - ĜC)TD  -(I -
ĜC)NF  -ĜF]`, which [1, Thm. 7] says is the intersection zonotope of Eq. 7 of [1, Thm. 1] at `Λ =
Ĝ`.

## Inputs
* `T` – decoupling matrix
* `N` – measurement decoupling matrix
* `Ghat` – observer gain
* `A` – state matrix
* `B` – input matrix
* `D` – disturbance matrix
* `C` – output matrix
* `F` – noise matrix
* `u` – control input
* `y_plus` – next output
* `X` – state zonotope

## Output
* zonotope of the current-estimate observer

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

def Zonotope.observeDescriptorCurrent (T : Mat ℝ n n) (N Ghat : Mat ℝ n ny) (A : Mat ℝ n n)
    (B : Mat ℝ n nu) (D : Mat ℝ n nw) (C : Mat ℝ ny n) (F : Mat ℝ ny nv) (u : Vec ℝ nu)
    (y_plus : Vec ℝ ny) (X : Zonotope (Vec ℝ n)) : Zonotope (Vec ℝ n) :=
  let K : Mat ℝ n n := 1 - Ghat * C                                          -- I - ĜC
  let p_plus := K *ᵥ (T *ᵥ (A *ᵥ X.c)) + K *ᵥ (T *ᵥ (B *ᵥ u)) +
    (N + Ghat - Ghat * C * N) *ᵥ y_plus                                          -- Eq. 39a
  let H_X : Fin X.h → Vec ℝ n := fun j => K *ᵥ (T *ᵥ (A *ᵥ X.G j))          -- (I - ĜC)TA H̄
  let H_D : Fin nw → Vec ℝ n := fun j i => (K * T * D) i j                 -- (I - ĜC)TD
  let H_N : Fin nv → Vec ℝ n := fun j i => -(K * N * F) i j                -- -(I - ĜC)NF
  let H_G : Fin nv → Vec ℝ n := fun j i => -(Ghat * F) i j                 -- -ĜF
  { h := X.h + nw + nv + nv
    c := p_plus
    G := Fin.append (Fin.append (Fin.append H_X H_D) H_N) H_G }             -- Eq. 39b

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
