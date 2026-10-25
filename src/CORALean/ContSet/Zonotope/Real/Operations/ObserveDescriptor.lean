module

public import CORALean.ContSet.Zonotope.Real.Zonotope
public import Mathlib.Data.Matrix.Mul

@[expose] public section

/-!
# `Zonotope.observeDescriptor`

The prediction-type zonotopic observer of [1, Thm. 5], for the descriptor system of [1, Eq. 4]
and the Luenberger structure of Eq. 30 of [1, Thm. 5], `x̂₊ = TA x̂ + TB u + TD ω + N y₊ - NF υ₊ +
G(y - C x̂ - F υ)`: from `X = ⟨p̂, H̄⟩`, the outputs `y` and `y₊` and the gain `G`,
Eq. 31 of [1, Thm. 5] gives `p̂₊(G) = (TA - GC) p̂ + TB u + G y + N y₊` and
`Ĥ₊(G) = [(TA - GC) H̄  TD  -NF  -GF]`. `G` is any matrix.

## Inputs
* `T` – decoupling matrix
* `N` – measurement decoupling matrix
* `G` – observer gain
* `A` – state matrix
* `B` – input matrix
* `D` – disturbance matrix
* `C` – output matrix
* `F` – noise matrix
* `u` – control input
* `y` – current output
* `y_plus` – next output
* `X` – state zonotope

## Output
* next state-estimate zonotope

## References

* [1] Y. Wang, V. Puig and G. Cembrano. "Set-membership approach and Kalman observer based on
      zonotopes for discrete-time descriptor systems". Automatica, 2018.
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

def Zonotope.observeDescriptor (T : Mat ℝ n n) (N G : Mat ℝ n ny) (A : Mat ℝ n n)
    (B : Mat ℝ n nu) (D : Mat ℝ n nw) (C : Mat ℝ ny n) (F : Mat ℝ ny nv) (u : Vec ℝ nu)
    (y y_plus : Vec ℝ ny) (X : Zonotope (Vec ℝ n)) : Zonotope (Vec ℝ n) :=
  let K : Mat ℝ n n := T * A - G * C                                         -- TA - GC
  let p_plus := K *ᵥ X.c + T *ᵥ (B *ᵥ u) + G *ᵥ y + N *ᵥ y_plus                -- Eq. 31a
  let H_X : Fin X.h → Vec ℝ n := fun j => K *ᵥ X.G j                       -- (TA - GC) H̄
  let H_D : Fin nw → Vec ℝ n := fun j i => (T * D) i j                    -- TD
  let H_N : Fin nv → Vec ℝ n := fun j i => -(N * F) i j                   -- -NF
  let H_G : Fin nv → Vec ℝ n := fun j i => -(G * F) i j                   -- -GF
  { h := X.h + nw + nv + nv
    c := p_plus
    G := Fin.append (Fin.append (Fin.append H_X H_D) H_N) H_G }             -- Eq. 31b

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
