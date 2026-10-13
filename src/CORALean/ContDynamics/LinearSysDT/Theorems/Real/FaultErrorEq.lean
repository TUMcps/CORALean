module

public import CORALean.Global.Tensor
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Abel

@[expose] public section

/-!
# The error and residual of the fault-detection observer

[1, Eq. 8] and [1, Eq. 9]: for `x_{k+1} = A x_k + B u_k + D_x w_k`, `y_k = C x_k + D_y v_k + E f_k`
[1, Eq. 3] and the Luenberger observer `x̂_{k+1} = A x̂_k + B u_k + L(y_k - C x̂_k)` [1, Eq. 7],
the error `e_k = x_k - x̂_k` follows `e_{k+1} = (A - LC) e_k + D_x w_k - L D_y v_k - L E f_k`, and
the residual is `r_k = M(y_k - C x̂_k) = M C e_k + M D_y v_k + M E f_k`. At `w_k = v_k = 0` and
`x̂_k = p_k`, the centre of [1, Eq. 10], these are [1, Eq. 19] and [1, Eq. 20].

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

namespace CORALean

open Matrix

variable {n nu ny nw nv nf : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSysDT.faultError_eq (A : Mat ℝ n n) (B : Mat ℝ n nu) (C : Mat ℝ ny n)
    (L : Mat ℝ n ny) (M : Mat ℝ ny ny) (Dx : Mat ℝ n nw) (Dy : Mat ℝ ny nv) (E : Mat ℝ ny nf)
    (x xh : Vec ℝ n) (u : Vec ℝ nu) (w : Vec ℝ nw) (v : Vec ℝ nv) (f : Vec ℝ nf) :
    let y := C *ᵥ x + Dy *ᵥ v + E *ᵥ f                                      -- Eq. 3b
    let x_plus := A *ᵥ x + B *ᵥ u + Dx *ᵥ w                                  -- Eq. 3a
    let xh_plus := A *ᵥ xh + B *ᵥ u + L *ᵥ (y - C *ᵥ xh)                     -- Eq. 7
    let e := x - xh
    x_plus - xh_plus = (A - L * C) *ᵥ e + Dx *ᵥ w - (L * Dy) *ᵥ v - (L * E) *ᵥ f ∧  -- Eq. 8
      M *ᵥ (y - C *ᵥ xh) = (M * C) *ᵥ e + (M * Dy) *ᵥ v + (M * E) *ᵥ f := by
  intro y x_plus xh_plus e
  simp only [y, x_plus, xh_plus, e, sub_mulVec, ← mulVec_mulVec, mulVec_add, mulVec_sub]
  constructor <;> abel

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
