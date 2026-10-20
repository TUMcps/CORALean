module

public import CORALean.ContSet.Zonotope.Real.Zonotope
public import CORALean.Global.Tensor
public import Mathlib.Data.Matrix.Mul

@[expose] public section

/-!
# `Zonotope.faultObserve`

The zonotopic observer of [1, Eq. 10], for `x_{k+1} = A x_k + B u_k + D_x w_k`,
`y_k = C x_k + D_y v_k + E f_k` with `w_k ∈ ⟨0, H_w⟩`, `v_k ∈ ⟨0, H_v⟩` [1, Eq. 3]: from
`X̂_k = ⟨p_k, H_k⟩`, the input `u_k`, the output `y_k` and the gain `L`,
`p_{k+1} = A p_k + B u_k + L(y_k - C p_k)` (10a) and
`H_{k+1} = [(A - LC) ↓_q(H_k)  D_x H_w  -L D_y H_v]` (10b). `X` is the zonotope after the
reduction `↓_q`, which encloses `⟨p_k, H_k⟩` and keeps its center; which reduction it was does
not enter. `L` is any matrix.

## Inputs
* `A` – state matrix
* `B` – input matrix
* `C` – output matrix
* `L` – observer gain
* `Dx` – disturbance matrix
* `Hw` – disturbance generator matrix
* `Dy` – noise matrix
* `Hv` – noise generator matrix
* `u` – control input
* `y` – measured output
* `X` – reduced state zonotope

## Output
* next state-estimate zonotope

## References

* [1] Y. Wang, M. Zhou, V. Puig, G. Cembrano and Z. Wang. "Zonotopic Fault Detection Observer
      with H− Performance". In Proc. of the 36th Chinese Control Conference (CCC),
      pp. 7230-7235, 2017.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n nu ny nw nv rw rv : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Zonotope.faultObserve (A : Mat ℝ n n) (B : Mat ℝ n nu) (C : Mat ℝ ny n) (L : Mat ℝ n ny)
    (Dx : Mat ℝ n nw) (Hw : Mat ℝ nw rw) (Dy : Mat ℝ ny nv) (Hv : Mat ℝ nv rv) (u : Vec ℝ nu)
    (y : Vec ℝ ny) (X : Zonotope (Vec ℝ n)) : Zonotope (Vec ℝ n) :=
  let p_plus := A *ᵥ X.c + B *ᵥ u + L *ᵥ (y - C *ᵥ X.c)                  -- Eq. 10a
  let H_X : Fin X.h → Vec ℝ n := fun j => (A - L * C) *ᵥ X.G j          -- (A - LC) ↓_q(H_k)
  let H_W : Fin rw → Vec ℝ n := fun j i => (Dx * Hw) i j                -- D_x H_w
  let H_V : Fin rv → Vec ℝ n := fun j i => -(L * Dy * Hv) i j           -- -L D_y H_v
  { h := X.h + rw + rv
    c := p_plus
    G := Fin.append (Fin.append H_X H_W) H_V }                           -- Eq. 10b

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
