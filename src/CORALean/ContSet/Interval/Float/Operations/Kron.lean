import CORALean.ContSet.Interval.Float.Operations.MulLo
import CORALean.ContSet.Interval.Float.Operations.MulHi
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# `Interval.kron`, over a floating-point scalar

The entry `(i, k), (j, l)` of the Kronecker product is `I(i, j) * J(k, l)`; its bounds are the
least corner product rounded down (`mulLo`) and the greatest rounded up (`mulHi`), exactly as the
real definition, entry by entry. The block `(i, j)` sits at row `i * p + k` and column
`j * q + l` (`finProdFinEquiv`), CORA's layout.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {m n p q : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.kron (I : Interval (Mat 𝕋 m n)) (J : Interval (Mat 𝕋 p q)) :
    Interval (Mat 𝕋 (m * p) (n * q)) where
  inf := Matrix.reindex finProdFinEquiv finProdFinEquiv
    (Matrix.of fun (r : Fin m × Fin p) (c : Fin n × Fin q) =>
      Interval.mulLo (I.inf r.1 c.1) (I.sup r.1 c.1) (J.inf r.2 c.2) (J.sup r.2 c.2))
  sup := Matrix.reindex finProdFinEquiv finProdFinEquiv
    (Matrix.of fun (r : Fin m × Fin p) (c : Fin n × Fin q) =>
      Interval.mulHi (I.inf r.1 c.1) (I.sup r.1 c.1) (J.inf r.2 c.2) (J.sup r.2 c.2))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
