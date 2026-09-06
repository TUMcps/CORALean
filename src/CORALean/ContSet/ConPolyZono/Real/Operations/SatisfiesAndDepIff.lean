import CORALean.ContSet.ConPolyZono.Real.Operations.AndDep
import CORALean.ContSet.ConPolyZono.Real.Operations.HoldsPlusIff
import CORALean.ContSet.ConPolyZono.Real.Operations.MulVecAndALeft
import CORALean.ContSet.ConPolyZono.Real.Operations.MulVecAndAAgree
import CORALean.ContSet.ConPolyZono.Real.Theorems.MonomialAppendELeft
import CORALean.ContSet.ConPolyZono.Real.Theorems.MonomialAppendERight

/-!
# What `ConPolyZono.andDep`'s constraint system says

Each set's own constraints, and that the two points agree coordinate by
coordinate to within `D`.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- What `andDep`'s constraint system says: each set's own constraints, and that
the two points agree coordinate by coordinate to within `D`. -/
theorem ConPolyZono.satisfies_andDep_iff (C₁ C₂ : ConPolyZono (Vec ℝ n))
    (D : Interval (Vec ℝ n)) (a : Fin (C₁.p + C₂.p) → ℝ) :
    (C₁.andDep C₂ D).satisfies a ↔
      (C₁.satisfies (fun k => a (Fin.castAdd C₂.p k))
        ∧ C₂.satisfies (fun k => a (Fin.natAdd C₁.p k)))
      ∧ ∀ i, C₂.c i - C₁.c i + D.inf i
            ≤ (∑ l, C₁.G l i
              * PolyZonotope.monomial C₁.E (fun k => a (Fin.castAdd C₂.p k)) l)
            - ∑ l, C₂.G l i
              * PolyZonotope.monomial C₂.E (fun k => a (Fin.natAdd C₁.p k)) l
          ∧ (∑ l, C₁.G l i
              * PolyZonotope.monomial C₁.E (fun k => a (Fin.castAdd C₂.p k)) l)
            - ∑ l, C₂.G l i
              * PolyZonotope.monomial C₂.E (fun k => a (Fin.natAdd C₁.p k)) l
          ≤ C₂.c i - C₁.c i + D.sup i := by -- --- PROOF ---
  have hcol : (fun l => PolyZonotope.monomial (ConPolyZono.appendE
        (PolyZonotope.plusE C₁.EC C₂.EC) (PolyZonotope.plusE C₁.E C₂.E)) a
          (Fin.castAdd (C₁.h + C₂.h) l))
      = PolyZonotope.monomial (PolyZonotope.plusE C₁.EC C₂.EC) a :=
    funext fun l => ConPolyZono.monomial_appendE_left _ _ a l
  -- the inherited rows first: through the append they are `plusA` on the left block
  have hC : ∀ i : Fin (C₁.m + C₂.m),
      (ConPolyZono.andA C₁ C₂ *ᵥ PolyZonotope.monomial (ConPolyZono.appendE
          (PolyZonotope.plusE C₁.EC C₂.EC) (PolyZonotope.plusE C₁.E C₂.E)) a)
          (Fin.castAdd n i)
        = (ConPolyZono.plusA C₁.A C₂.A *ᵥ
            PolyZonotope.monomial (PolyZonotope.plusE C₁.EC C₂.EC) a) i := by -- --- PROOF ---
    intro i
    rw [ConPolyZono.mulVec_andA_left, hcol]
  -- then the agreement rows, each side's monomials read off its own factors
  have hG : ∀ i : Fin n,
      (ConPolyZono.andA C₁ C₂ *ᵥ PolyZonotope.monomial (ConPolyZono.appendE
          (PolyZonotope.plusE C₁.EC C₂.EC) (PolyZonotope.plusE C₁.E C₂.E)) a)
          (Fin.natAdd (C₁.m + C₂.m) i)
        = (∑ l, C₁.G l i
              * PolyZonotope.monomial C₁.E (fun k => a (Fin.castAdd C₂.p k)) l)
            - ∑ l, C₂.G l i
              * PolyZonotope.monomial C₂.E (fun k => a (Fin.natAdd C₁.p k)) l := by
    intro i
    rw [ConPolyZono.mulVec_andA_agree]
    congr 1
    · exact Finset.sum_congr rfl fun l _ => by
        rw [ConPolyZono.monomial_appendE_right, PolyZonotope.monomial_plusE_left]
    · exact Finset.sum_congr rfl fun l _ => by
        rw [ConPolyZono.monomial_appendE_right, PolyZonotope.monomial_plusE_right]
  constructor
  · intro hsat'
    -- the projections are read away first: `Fin.castAdd` does not fit `Fin (andDep ..).m`
    have hsat : ConPolyZono.holds (ConPolyZono.andA C₁ C₂) (ConPolyZono.andB C₁ C₂ D)
        (ConPolyZono.appendE (PolyZonotope.plusE C₁.EC C₂.EC)
          (PolyZonotope.plusE C₁.E C₂.E)) a := hsat'
    refine ⟨(ConPolyZono.holds_plus_iff C₁.A C₁.b C₁.EC C₂.A C₂.b C₂.EC a).mp
        (fun i => ?_), fun i => ?_⟩
    · have h := hsat (Fin.castAdd n i)
      rw [hC i] at h
      simpa only [ConPolyZono.andB, Fin.append_left] using h
    · have h := hsat (Fin.natAdd (C₁.m + C₂.m) i)
      rw [hG i] at h
      simpa only [ConPolyZono.andB, Fin.append_right] using h
  · rintro ⟨hcon, hagree⟩
    have hplus := (ConPolyZono.holds_plus_iff C₁.A C₁.b C₁.EC C₂.A C₂.b C₂.EC a).mpr hcon
    -- through the projections the index reads `Fin (andDep ..).m`, which `Fin.castAdd` misses
    show ConPolyZono.holds (ConPolyZono.andA C₁ C₂) (ConPolyZono.andB C₁ C₂ D)
      (ConPolyZono.appendE (PolyZonotope.plusE C₁.EC C₂.EC)
        (PolyZonotope.plusE C₁.E C₂.E)) a
    refine Fin.addCases (fun i => ?_) fun i => ?_
    · rw [hC i]
      simpa only [ConPolyZono.andB, Fin.append_left] using hplus i
    · rw [hG i]
      simpa only [ConPolyZono.andB, Fin.append_right] using hagree i

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
