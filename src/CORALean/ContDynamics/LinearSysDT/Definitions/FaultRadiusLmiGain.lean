import CORALean.ContDynamics.LinearSysDT.LinearSysDT
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Matrix.ColumnRowPartitioned

/-!
# The P-radius inequality of the fault-detection observer, with the gain

[1, Eq. 16]: for the gain `L`, `γ` and `P = Pᵀ ≻ 0`,
`[-γP 0 0 (A - LC)ᵀP; ⋆ -H_wᵀD_xᵀD_xH_w 0 (D_xH_w)ᵀP;
 ⋆ ⋆ -H_vᵀD_yᵀD_yH_v (LD_yH_v)ᵀP; ⋆ ⋆ ⋆ -P] ≺ 0`,
the blocks sized by the state and the generator counts of `⟨0, H_w⟩` and `⟨0, H_v⟩`. Stated as
its negative being positive definite; at `W = PL` it is [1, Eq. 17] (`LinearSysDT.FaultRadiusLmi`).

## References

* [1] Y. Wang, M. Zhou, V. Puig, G. Cembrano and Z. Wang. "Zonotopic Fault Detection Observer
      with H− Performance". In Proc. of the 36th Chinese Control Conference (CCC),
      pp. 7230-7235, 2017.
-/

-- Authors:       Tobias Ladner
-- Written:       11-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n ny nw nv rw rv : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Eq. 16], `≺ 0`. -/
def LinearSysDT.FaultRadiusLmiGain (A : Mat ℝ n n) (C : Mat ℝ ny n) (Dx : Mat ℝ n nw)
    (Hw : Mat ℝ nw rw) (Dy : Mat ℝ ny nv) (Hv : Mat ℝ nv rv) (P : Mat ℝ n n) (L : Mat ℝ n ny)
    (γ : ℝ) : Prop :=
  let Gw := Dx * Hw                                                           -- D_x H_w
  let Gv := Dy * Hv                                                           -- D_y H_v
  let TL : Matrix (Fin n ⊕ (Fin rw ⊕ Fin rv)) (Fin n ⊕ (Fin rw ⊕ Fin rv)) ℝ :=
    fromBlocks (-(γ • P)) 0 0 (fromBlocks (-(Gwᵀ * Gw)) 0 0 (-(Gvᵀ * Gv)))
  let R : Matrix (Fin n ⊕ (Fin rw ⊕ Fin rv)) (Fin n) ℝ :=                     -- the last column
    fromRows ((A - L * C)ᵀ * P) (fromRows (Gwᵀ * P) ((L * Gv)ᵀ * P))
  (-(fromBlocks TL R Rᵀ (-P))).PosDef

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
