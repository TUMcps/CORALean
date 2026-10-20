module

public import CORALean.ContSet.Interval.Real.Operations.Basic
public import Mathlib.LinearAlgebra.Matrix.Kronecker

@[expose] public section

/-!
# `Interval.kron`

CORA's `@interval/kron` of two interval matrices: the entry `(i, k), (j, l)` of the Kronecker
product is `I(i, j) * J(k, l)`, and its bounds are the least and greatest of the four corner
products (`mulLo`, `mulHi`), which is what CORA's `min`/`max` over the four Kronecker products of
the bounds computes. The block `(i, j)` of the result sits at row `i * p + k` and column `j * q + l`
(`finProdFinEquiv`), CORA's layout.

## Inputs
* `I` – left factor
* `J` – right factor

## Output
* interval Kronecker product
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {m n p q : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.kron (I : Interval (Mat ℝ m n)) (J : Interval (Mat ℝ p q)) :
    Interval (Mat ℝ (m * p) (n * q)) where
  inf := Matrix.reindex finProdFinEquiv finProdFinEquiv
    (Matrix.of fun (r : Fin m × Fin p) (c : Fin n × Fin q) =>
      Interval.mulLo (I.inf r.1 c.1) (I.sup r.1 c.1) (J.inf r.2 c.2) (J.sup r.2 c.2))
  sup := Matrix.reindex finProdFinEquiv finProdFinEquiv
    (Matrix.of fun (r : Fin m × Fin p) (c : Fin n × Fin q) =>
      Interval.mulHi (I.inf r.1 c.1) (I.sup r.1 c.1) (J.inf r.2 c.2) (J.sup r.2 c.2))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
