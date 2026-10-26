module

public import CORALean.ContSet.ConPolyZono.Real.Theorems.MemRelaxIff
public import CORALean.ContSet.PolyZonotope.Real.Theorems.MonomialIdentE
public import CORALean.ContSet.Conversion.Real.Theorems.ConZonotopeConRowsIff

@[expose] public section

/-!
# A constrained zonotope as a constrained polynomial zonotope

Exact. Our `ConZonotope` carries an `HPolytope` over its coefficients, so it admits inequalities,
and a row of a constrained polynomial zonotope is an equation: each row is held to the interval it
may take over the unit cube, the midpoint relaxed by the radius (`ConPolyZono.relax`, one slack
factor per row). An inequality's interval is open at one end, so a lower bound is supplied, and one
is free: a row cannot fall below minus the sum of its absolute coefficients, and capped by `b` that
cuts nothing. The coefficients are factors themselves, to the first power. `coeffs` is the converse
of `HPolytope.rowLin`: a functional is its values on the unit vectors.

## Inputs
* `cZ` – constrained zonotope

## Hypotheses
* none

## Conclusion
* set equals its constrained polynomial zonotope
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       03-September-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A row's interval is never crossed: `min(-Σ|aⱼ|, b) ≤ b`, and `be ≤ be`. -/
private theorem ConZonotope.aux_conLo_le_conHi (cZ : ConZonotope (Vec ℝ n))
    (i : Fin (cZ.P.m + cZ.P.me)) : ConZonotope.conLo cZ i ≤ ConZonotope.conHi cZ i := by
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · simp only [ConZonotope.conLo, ConZonotope.conHi, Fin.append_left]
    exact min_le_right _ _
  · simp only [ConZonotope.conLo, ConZonotope.conHi, Fin.append_right, le_refl]

/-- Within the radius of the midpoint is within the interval. -/
private theorem ConZonotope.aux_abs_sub_mid_le_iff {lo hi v : ℝ} (h : lo ≤ hi) : -- --- CONCL ---
    |v - (lo + hi) / 2| ≤ |(hi - lo) / 2| ↔ lo ≤ v ∧ v ≤ hi := by -- --- PROOF ---
  rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ (hi - lo) / 2), abs_le]
  constructor
  · rintro ⟨h₁, h₂⟩
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨by linarith, by linarith⟩


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.conPolyZono_exact (cZ : ConZonotope (Vec ℝ n)) : -- --- CONCL ---
    cZ.construct = cZ.conPolyZono.construct := by -- --- PROOF ---
  have hμ : ∀ β : Vec ℝ cZ.h, PolyZonotope.monomial (PolyZonotope.identE cZ.h) β = β :=
    fun β => funext fun j => PolyZonotope.monomial_identE β j
  ext x
  rw [ConZonotope.conPolyZono, ConPolyZono.mem_relax_iff]
  constructor
  -- a coefficient vector the polytope admits meets every row within its radius of its midpoint
  · rintro ⟨β, hβ, hP, rfl⟩
    refine ⟨β, Fin.elim0, hβ, fun j => j.elim0, fun i => ?_, ?_⟩
    · show |(ConZonotope.conA cZ *ᵥ PolyZonotope.monomial (PolyZonotope.identE cZ.h) β) i
          - (ConZonotope.conLo cZ i + ConZonotope.conHi cZ i) / 2|
        ≤ |(ConZonotope.conHi cZ i - ConZonotope.conLo cZ i) / 2|
      rw [hμ, ConZonotope.aux_abs_sub_mid_le_iff (ConZonotope.aux_conLo_le_conHi cZ i)]
      exact (ConZonotope.conRows_iff cZ β hβ).mpr hP i
    · show _ = cZ.c + (∑ i, PolyZonotope.monomial (PolyZonotope.identE cZ.h) β i • cZ.G i)
        + ∑ j : Fin 0, Fin.elim0 j • (Fin.elim0 j : Vec ℝ n)
      simp only [hμ, Finset.univ_eq_empty, Finset.sum_empty, add_zero]
  -- back: rows within their intervals say what the polytope says
  · rintro ⟨β, γ, hβ, -, hrows, rfl⟩
    have hrows' : ∀ i, ConZonotope.conLo cZ i ≤ (ConZonotope.conA cZ *ᵥ β) i
        ∧ (ConZonotope.conA cZ *ᵥ β) i ≤ ConZonotope.conHi cZ i := fun i => by
      have h := hrows i
      rw [hμ] at h
      exact (ConZonotope.aux_abs_sub_mid_le_iff (ConZonotope.aux_conLo_le_conHi cZ i)).mp h
    refine ⟨β, hβ, (ConZonotope.conRows_iff cZ β hβ).mp hrows', ?_⟩
    show cZ.c + (∑ i, PolyZonotope.monomial (PolyZonotope.identE cZ.h) β i • cZ.G i)
        + (∑ j : Fin 0, γ j • (Fin.elim0 j : Vec ℝ n))
      = cZ.c + ∑ j, β j • cZ.G j
    simp only [hμ, Finset.univ_eq_empty, Finset.sum_empty, add_zero]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
