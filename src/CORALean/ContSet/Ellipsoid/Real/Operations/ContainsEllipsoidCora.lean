import CORALean.ContSet.Ellipsoid.Real.Ellipsoid
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# CORA's ellipsoid-in-ellipsoid `contains_`, as printed

`@ellipsoid/private/priv_containsEllipsoid.m` (l. 46-96), reached from `contains_(E1, E2)` for
an ellipsoid `E2` that is not a point (l. 88-90): `H` and `G` are the generators of `E1` and
`E2` (`E.G` here, CORA's `U*sqrt(D)` of `svd(Q)`); if `rank(H) < n` and `rank([H G]) > rank(H)`
the answer is `false`; otherwise `Theta = pinv(H)*G`, `theta = pinv(H)*(q2 - q1)`, and the SDP
`min rho` s.t. `A - rho*B <= delta*C`, `delta >= 0` with `A = [Theta'Theta Theta'theta;
theta'Theta theta'theta]`, `B = diag(0, …, 0, 1)`, `C = diag(1, …, 1, -1)` decides by `rho <=
1 + tol`. The ranks are exact (`Matrix.rank`; CORA's `rank(·, tol)` agrees on the matrices of
the theorems); `pinv(H)` is the argument `Hp` and the solver (`value(rho)` after `optimize`) the
argument `sdp A B C`, each pinned down by hypotheses in the theorems. The rank test checks the
generators but not the centre offset `q2 - q1`, which `pinv(H)` projects away when `E1` is
degenerate; kept only so that `Ellipsoid.containsEllipsoidCora_counterexample` can state that
this is unsound.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `priv_containsEllipsoid(E1, E2, tol)` as printed, `pinv(H)` being `Hp` and the SDP's
`value(rho)` being `sdp A B C`. -/
def Ellipsoid.containsEllipsoidCora (E₁ E₂ : Ellipsoid n) (Hp : Mat ℝ E₁.k n)
    (sdp : (A B C : Matrix (Fin E₂.k ⊕ Fin 1) (Fin E₂.k ⊕ Fin 1) ℝ) → ℝ) (tol : ℝ) : Prop :=
  let G := E₂.G
  let H := E₁.G
  let r := H.rank
  let r_comb := (Matrix.fromCols H G).rank
  if r < n ∧ r_comb > r then False else
    let Theta := Hp * G
    let theta : Mat ℝ E₁.k 1 := Hp * Matrix.of (fun i (_ : Fin 1) => (E₂.q - E₁.q) i)
    let A := Matrix.fromBlocks (Thetaᵀ * Theta) (Thetaᵀ * theta) (thetaᵀ * Theta) (thetaᵀ * theta)
    let B : Matrix (Fin E₂.k ⊕ Fin 1) (Fin E₂.k ⊕ Fin 1) ℝ := Matrix.fromBlocks 0 0 0 1
    let C : Matrix (Fin E₂.k ⊕ Fin 1) (Fin E₂.k ⊕ Fin 1) ℝ := Matrix.fromBlocks 1 0 0 (-1)
    let rho := sdp A B C
    rho ≤ 1 + tol

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
