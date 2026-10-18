module

public import CORALean.ContSet.Zonotope.Real.Operations.FaultObserve
public import CORALean.ContSet.Zonotope.Real.Operations.FaultResidual
public import Mathlib.Data.Matrix.Basic

@[expose] public section

/-!
# The residual zonotope in terms of the previous estimate

[1, Eq. 12]: substituting [1, Eq. 10] into [1, Eq. 11],
`p^r_{k+1} = M y_{k+1} - M C (A p_k + B u_k + L(y_k - C p_k))` and
`H^r_{k+1} = [M C (A - LC) ↓_q(H_k)  M C D_x H_w  -M C L D_y H_v  M D_y H_v]`. The residual of the
observer's zonotope (`Zonotope.faultResidual` of `Zonotope.faultObserve`) is that zonotope,
generator for generator.

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


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.faultResidual_faultObserve (A : Mat ℝ n n) (B : Mat ℝ n nu) (C : Mat ℝ ny n)
    (L : Mat ℝ n ny) (M : Mat ℝ ny ny) (Dx : Mat ℝ n nw) (Hw : Mat ℝ nw rw) (Dy : Mat ℝ ny nv)
    (Hv : Mat ℝ nv rv) (u : Vec ℝ nu) (y y_plus : Vec ℝ ny)
    (X : Zonotope (Vec ℝ n)) : -- --- STMT ---
    (X.faultObserve A B C L Dx Hw Dy Hv u y).faultResidual M C Dy Hv y_plus =
      { h := X.h + rw + rv + rv
        c := M *ᵥ y_plus - (M * C) *ᵥ (A *ᵥ X.c + B *ᵥ u + L *ᵥ (y - C *ᵥ X.c))   -- Eq. 12a
        G := Fin.append (Fin.append (Fin.append
          (fun j => (M * C * (A - L * C)) *ᵥ X.G j)                              -- Eq. 12b
          (fun j i => (M * C * (Dx * Hw)) i j))
          (fun j i => -(M * C * (L * Dy * Hv)) i j))
          (fun j i => (M * Dy * Hv) i j) } := by -- --- PROOF ---
  simp only [Zonotope.faultResidual, Zonotope.faultObserve, Zonotope.mk.injEq, heq_eq_eq,
    true_and]
  constructor
  · rw [mulVec_sub, mulVec_mulVec]
  · -- block by block: `M C` through each column
    funext j
    refine Fin.addCases (fun j => Fin.addCases (fun j => Fin.addCases (fun j => ?_) (fun j => ?_) j)
      (fun j => ?_) j) (fun j => ?_) j <;>
      simp only [Fin.append_left, Fin.append_right, mulVec_mulVec]
    all_goals ext i; simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
