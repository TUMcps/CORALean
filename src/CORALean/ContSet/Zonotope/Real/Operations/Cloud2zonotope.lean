module

public import CORALean.ContSet.Conversion.Real.Interval_to_Zonotope
public import CORALean.ContSet.Zonotope.Real.Operations.Cloud2zonotopeLoop

@[expose] public section

/-!
# `Zonotope.cloud2zonotope`

[1, Alg. 3] (`cloud2zonotope`): a zonotope `c ⊕ Z(R)` enclosing a cloud `X` of points of `ℝⁿ`,
by at most `s₁` rounds of "compress the cloud along its first principal direction, add the cut
segment" (`cloud2zonotopeLoop`), then the interval hull of what is left as `n` axis-aligned
generators `diag(rad)` (`Interval.zonotope`: centre `mid`, generators `diag(rad)`). Inputs
`ratio`, `s₁`, `s₂` as printed; `dir` stands for `svd(X)(:, 1)`. Every point lies in the result,
for any `dir` and `ratio` (`cloud2zonotope_mem`).

The paper's listing ends at step 13 while its text speaks of "step 14"; the zonotope is returned.

## References

* [1] M. Maïga, N. Ramdani, L. Travé-Massuyès and C. Combastel. "A Comprehensive Method for
      Reachability Analysis of Uncertain Nonlinear Hybrid Systems". IEEE Transactions on
      Automatic Control, 61(9):2341-2356, 2016.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ} {κ : Type}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `[c, R] = cloud2zonotope(X, ratio, s₁, s₂)`, the zonotope `c ⊕ Z(R)`. -/
noncomputable def Zonotope.cloud2zonotope [Fintype κ] [Nonempty κ] (dir : (κ → Vec ℝ n) → Vec ℝ n)
    (ratio : ℝ) (s₁ : ℕ) (s₂ : ℝ) (X : κ → Vec ℝ n) : Zonotope (Vec ℝ n) :=
  let Z₀ : Zonotope (Vec ℝ n) := ⟨0, 0, Fin.elim0⟩
  let loop := Zonotope.cloud2zonotopeLoop dir ratio s₂ s₁ 0 0 Z₀ X
  let I := Interval.enclosePoints loop.2
  loop.1.plus I.zonotope

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
