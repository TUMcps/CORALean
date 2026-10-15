module

public import CORALean.ContSet.Zonotope.Real.Zonotope
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

@[expose] public section

/-!
# The P-radius of a zonotope

[1, Sec. 2]: `L = max_{z ∈ Z} ‖z - p‖²_P` for `P = Pᵀ ≻ 0`, the largest squared `P`-distance of a
point of `Z = p ⊕ H Bᵐ` from its centre; Wang et al. call it the W-radius [2, Def. 5],
`ℓ_W = max_{z ∈ Z} ‖z - p‖²_{2,W}`. Written as the supremum; a zonotope is
compact, so it is attained. `P` is any matrix here: what is proved about it says which `P` it
needs. It is also the P-radius `Prad(Z)` of [3, Eq. 47], one of the sizes whose least value
picks the compression ratio of `cloud2zonotope`.

## References

* [1] V. T. H. Le, C. Stoica, T. Alamo, E. F. Camacho and D. Dumur. "Zonotopic guaranteed state
      estimation for uncertain systems". Automatica, 49(11):3418-3424, 2013.
* [2] Y. Wang, V. Puig and G. Cembrano. "Set-membership approach and Kalman observer based on
      zonotopes for discrete-time descriptor systems". Automatica, 93:435-443, 2018.
* [3] M. Maïga, N. Ramdani, L. Travé-Massuyès and C. Combastel. "A Comprehensive Method for
      Reachability Analysis of Uncertain Nonlinear Hybrid Systems". IEEE Transactions on
      Automatic Control, 61(9):2341-2356, 2016.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      15-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `max_{z ∈ Z} (z - p)ᵀ P (z - p)`. -/
noncomputable def Zonotope.pRadius (P : Mat ℝ n n) (Z : Zonotope (Vec ℝ n)) : ℝ :=
  sSup ((fun z => (z - Z.c) ⬝ᵥ (P *ᵥ (z - Z.c))) '' Z.construct)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
