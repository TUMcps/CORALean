module

public import CORALean.ContSet.Interval.Real.Interval
public import Mathlib.Data.Matrix.Mul

@[expose] public section

/-!
# `Ãᵢ`, eq. (19)-(20)

`particularCoeff`: [1]'s eq. (19)-(20): `Ãᵢ` is `Aⁱ Δtⁱ⁺¹/(i+1)!`.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE Transactions on
      Automatic Control, vol. 68, no. 12, 2023, pp. 7771–7786.
-/

-- Authors:       Claude Sonnet 5
-- Written:       19-September-2026
-- Last update:   ---
-- Reviewed:      19-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1]'s eq. (19)-(20): `Ãᵢ` is `Aⁱ Δtⁱ⁺¹/(i+1)!`. -/
noncomputable def MatExp.particularCoeff (A : Mat ℝ n n) (Δt : ℝ) (i : ℕ) : Mat ℝ n n :=
  (Δt ^ (i + 1) / (Nat.factorial (i + 1) : ℝ)) • A ^ i

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
