module

public import CORALean.ContSet.Taylm.Real.Operations.Basic

@[expose] public section

/-!
# Taylor models over a shrinking domain

[1, Thm. 1] is about models of `f` around `x_h` on `x_h + [-h, h]ᵛ` as `h → 0`. Stored the way
the source stores them, over the box with `x = x_h + h·t`, a coefficient of degree `d` is `hᵈ`
times the one of the unnormalized polynomial. `weight` divides that back out and adds the
magnitudes; `Scaled T h C` bounds it by `C` and the remainder by `C·hᴺ⁺¹`, which is the theorem's
`I = O(hⁿ⁺¹)` together with the bound on the polynomial the source leaves unstated.

## References

* [1] K. Makino and M. Berz. "Taylor Models and Other Validated Functional Inclusion
      Methods". International Journal of Pure and Applied Mathematics, 4(4):379-452, 2003.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}

/-- `Σ |a| / hᵈᵉᵍ`: the magnitudes of the unnormalized coefficients. -/
noncomputable def Taylm.weight (L : List (ℝ × (Fin n → ℕ))) (h : ℝ) : ℝ :=
  (L.map fun a => |a.1| / h ^ Taylm.degree a.2).sum


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The polynomial's weight is at most `C` and both remainder ends at most `C·hᴺ⁺¹`. -/
def Taylm.Scaled (T : Taylm n) (h C : ℝ) : Prop :=
  Taylm.weight T.terms h ≤ C ∧ |T.remInf| ≤ C * h ^ (T.maxOrder + 1) ∧
    |T.remSup| ≤ C * h ^ (T.maxOrder + 1)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
