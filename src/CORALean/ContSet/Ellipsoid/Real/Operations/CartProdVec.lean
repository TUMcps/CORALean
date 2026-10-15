module

public import CORALean.ContSet.Ellipsoid.Real.Ellipsoid

@[expose] public section

/-!
# `Ellipsoid.cartProdVec`

CORA's `@ellipsoid/cartProd_.m` with a point operand, which is exact: `blkdiag(E.Q, zeros(m))` and
`[E.q; S]`. The block-diagonal matrix is written `P Q Pᵀ` for the embedding `P = [I; 0]` of the
first `n` coordinates, which is the same matrix and positive semi-definite on sight.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- An ellipsoid times a point: `blkdiag(E.Q, 0)` and the center extended by the point. -/
def Ellipsoid.cartProdVec (E : Ellipsoid n) (v : Vec ℝ m) : Ellipsoid (n + m) :=
  -- `P = [I; 0]`, so that `P Q Pᵀ = blkdiag(Q, 0)`
  let P : Mat ℝ (n + m) n := Matrix.of fun i j => Fin.addCases (fun i => if i = j then 1 else 0)
    (fun _ => 0) i
  { Q := P * E.Q * Pᵀ
    q := Fin.append E.q v
    psd := by
      simpa [conjTranspose_eq_transpose_of_trivial] using E.psd.mul_mul_conjTranspose_same P }

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
