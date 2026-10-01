import CORALean.ContSet.ZonoBundle.Real.Operations.DirPcaCovariance

/-!
# The vertex scatter matrix is Hermitian

Over `ℝ` the conjugate transpose is the transpose, so being Hermitian is being symmetric, and
`∑ₗ aₗᵢ aₗⱼ` is symmetric in `i` and `j` because multiplication is commutative. It earns a file
because Mathlib's spectral theorem takes this hypothesis, which `dirPca` feeds it
[1, Heuristic pca].

## References

* [1] M. Althoff and B. H. Krogh. "Zonotope Bundles for the Efficient Computation of
      Reachable Sets". In Proc. of the 50th IEEE Conference on Decision and Control and
      European Control Conference (CDC-ECC), pp. 6814-6821, 2011.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `dirPcaCovariance` is Hermitian, which over `ℝ` is symmetric. -/
theorem ZonoBundle.dirPcaCovariance_isHermitian {m : ℕ} (V : Fin m → Vec ℝ n) :
    (ZonoBundle.dirPcaCovariance V).IsHermitian := by
  ext i j
  simp [ZonoBundle.dirPcaCovariance, Matrix.conjTranspose_apply, mul_comm]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
