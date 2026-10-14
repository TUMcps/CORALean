module

public import CORALean.ContSet.ConPolyZono.Real.ConPolyZono
public import CORALean.ContSet.ConZonotope.Real.ConZonotope
public import CORALean.ContSet.PolyZonotope.Real.Operations.IdentE
public import CORALean.ContSet.PolyZonotope.Real.Operations.MonomialIdentE
public import CORALean.ContSet.Conversion.Real.Operations.ConZonotope_to_ConPolyZono
public import CORALean.ContSet.Conversion.Real.Theorems.ConZonotopeSatisfiesConPolyZonoIff

@[expose] public section

/-!
# A constrained zonotope as a constrained polynomial zonotope

Exact, and it is the interval right-hand side that makes it so. Our
`ConZonotope` carries an `HPolytope` over its coefficients, so it admits
inequalities, and with `A μ(α) ∈ b` an inequality is a row whose interval is
open at one end, with nothing added to `p`.

Open at one end is not something an interval can be, so a lower bound has to be
supplied — and one is free: every factor lies in `[-1,1]`, so a row cannot fall
below minus the sum of its absolute coefficients. That bound cuts nothing, which
is why the conversion is exact rather than enclosing.

The factors are the coefficients themselves, one each and to the first power, so
generators and constraint columns read off the same identity exponent matrix. A
constrained zonotope is exactly the linear fragment of the representation.

`coeffs` is the converse of `HPolytope.rowLin`: a constraint there is a
functional, here a matrix row, and a functional is its values on the unit vectors.
-/

-- Authors:       Claude Opus 5
-- Written:       03-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.conPolyZono_exact (cZ : ConZonotope (Vec ℝ n)) :
    cZ.construct = cZ.conPolyZono.construct := by -- --- PROOF ---
  have hvalue : ∀ β : Vec ℝ cZ.h,
      cZ.c + ∑ j, β j • cZ.G j
        = cZ.c + (∑ i, PolyZonotope.monomial (PolyZonotope.identE cZ.h) β i • cZ.G i)
          + ∑ j : Fin 0, (0:ℝ) • (Fin.elim0 j : Vec ℝ n) := by
    intro β
    simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero,
      PolyZonotope.monomial_identE]
  -- and the point is unchanged, the independent block being empty
  apply Set.eq_of_subset_of_subset
  · rintro _ ⟨β, hβ, hP, rfl⟩
    exact ⟨β, fun _ => 0, hβ, fun j => j.elim0,
      (ConZonotope.satisfies_conPolyZono_iff cZ β hβ).mpr hP, hvalue β⟩
  · rintro _ ⟨β, γ, hβ, -, hsat, rfl⟩
    refine ⟨β, hβ, (ConZonotope.satisfies_conPolyZono_iff cZ β hβ).mp hsat, ?_⟩
    show cZ.c + (∑ i, PolyZonotope.monomial (PolyZonotope.identE cZ.h) β i • cZ.G i)
        + (∑ j : Fin 0, γ j • (Fin.elim0 j : Vec ℝ n))
      = cZ.c + ∑ j, β j • cZ.G j
    simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero,
      PolyZonotope.monomial_identE]
    rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
