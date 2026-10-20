module

public import CORALean.ContDynamics.LinearSysDT.LinearSysDT
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Data.Matrix.ColumnRowPartitioned

@[expose] public section

/-!
# The P-radius inequality of the fault-detection observer

[1, Eq. 17]: for `γ`, `P = Pᵀ ≻ 0` and `W`,
`[-γP 0 0 AᵀP - CᵀWᵀ; ⋆ -H_wᵀD_xᵀD_xH_w 0 H_wᵀD_xᵀP; ⋆ ⋆ -H_vᵀD_yᵀD_yH_v H_vᵀD_yᵀWᵀ; ⋆ ⋆ ⋆ -P] ≺ 0`,
the blocks sized by the state and the generator counts of `⟨0, H_w⟩` and `⟨0, H_v⟩`; at `W = PL`
it is [1, Eq. 16], and the gain is `L = P⁻¹W`. Stated as its negative being positive definite.

## Inputs
* `A` – state matrix
* `C` – output matrix
* `Dx` – disturbance matrix
* `Hw` – disturbance generators
* `Dy` – noise matrix
* `Hv` – noise generators
* `P` – Lyapunov matrix
* `W` – gain variable
* `γ` – radius bound

## Output
* the block matrix is negative definite

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

variable {n ny nw nv rw rv : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Eq. 17], `≺ 0`. -/
def LinearSysDT.FaultRadiusLmi (A : Mat ℝ n n) (C : Mat ℝ ny n) (Dx : Mat ℝ n nw)
    (Hw : Mat ℝ nw rw) (Dy : Mat ℝ ny nv) (Hv : Mat ℝ nv rv) (P : Mat ℝ n n) (W : Mat ℝ n ny)
    (γ : ℝ) : Prop :=
  let Gw := Dx * Hw                                                           -- D_x H_w
  let Gv := Dy * Hv                                                           -- D_y H_v
  let TL : Matrix (Fin n ⊕ (Fin rw ⊕ Fin rv)) (Fin n ⊕ (Fin rw ⊕ Fin rv)) ℝ :=
    fromBlocks (-(γ • P)) 0 0 (fromBlocks (-(Gwᵀ * Gw)) 0 0 (-(Gvᵀ * Gv)))
  let R : Matrix (Fin n ⊕ (Fin rw ⊕ Fin rv)) (Fin n) ℝ :=                     -- the last column
    fromRows (Aᵀ * P - Cᵀ * Wᵀ) (fromRows (Gwᵀ * P) (Gvᵀ * Wᵀ))
  (-(fromBlocks TL R Rᵀ (-P))).PosDef

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
