module

public import CORALean.ContSet.Taylm.Real.Taylm

@[expose] public section

/-!
# A term list integrated in one variable

`a·tᵉ ↦ a/(eᵢ + 1)·tᵉ⁺ᵉⁱ`: the antiderivative in `tᵢ` that vanishes at `tᵢ = 0`, term by term,
the `∫₀^{xᵢ} P dxᵢ` of [1, Def. 3 (antiderivation)].

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


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Each term's exponent of `tᵢ` raised by one and its coefficient divided by the new one. -/
noncomputable def Taylm.integrateTerms (i : Fin n) (L : List (ℝ × (Fin n → ℕ))) :
    List (ℝ × (Fin n → ℕ)) :=
  L.map fun a => (a.1 / ((a.2 i : ℝ) + 1), a.2 + Pi.single i 1)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
