module

public import CORALean.ContSet.ConPolyZono.Real.Operations.IntersectionDep
public import CORALean.ContSet.ConPolyZono.Real.Operations.HoldsPlusIff
public import CORALean.ContSet.ConPolyZono.Real.Operations.MulVecIntersectionALeft
public import CORALean.ContSet.ConPolyZono.Real.Operations.MulVecIntersectionAAgree
public import CORALean.ContSet.ConPolyZono.Real.Theorems.MonomialAppendELeft
public import CORALean.ContSet.ConPolyZono.Real.Theorems.MonomialAppendERight

@[expose] public section

/-!
# What `ConPolyZono.intersectionDep`'s constraint system says

Each set's own constraints, and that the two points agree coordinate by
coordinate.
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- What `intersectionDep`'s constraint system says: each set's own constraints, and that
the two points agree coordinate by coordinate. -/
theorem ConPolyZono.satisfies_intersectionDep_iff (cPZ₁ cPZ₂ : ConPolyZono (Vec ℝ n))
    (a : Fin (cPZ₁.p + cPZ₂.p) → ℝ) : -- --- STMT ---
    (cPZ₁.intersectionDep cPZ₂).satisfies a ↔
      (cPZ₁.satisfies (fun k => a (Fin.castAdd cPZ₂.p k))
        ∧ cPZ₂.satisfies (fun k => a (Fin.natAdd cPZ₁.p k)))
      ∧ ∀ i, (∑ l, cPZ₁.G l i
              * PolyZonotope.monomial cPZ₁.E (fun k => a (Fin.castAdd cPZ₂.p k)) l)
            - ∑ l, cPZ₂.G l i
              * PolyZonotope.monomial cPZ₂.E (fun k => a (Fin.natAdd cPZ₁.p k)) l
          = cPZ₂.c i - cPZ₁.c i := by -- --- PROOF ---
  have hcol : (fun l => PolyZonotope.monomial (ConPolyZono.appendE
        (PolyZonotope.plusE cPZ₁.R cPZ₂.R) (PolyZonotope.plusE cPZ₁.E cPZ₂.E)) a
          (Fin.castAdd (cPZ₁.h + cPZ₂.h) l))
      = PolyZonotope.monomial (PolyZonotope.plusE cPZ₁.R cPZ₂.R) a :=
    funext fun l => ConPolyZono.monomial_appendE_left _ _ a l
  -- the inherited rows first: through the append they are `plusA` on the left block
  have hC : ∀ i : Fin (cPZ₁.m + cPZ₂.m),
      (ConPolyZono.intersectionA cPZ₁ cPZ₂ *ᵥ PolyZonotope.monomial (ConPolyZono.appendE
          (PolyZonotope.plusE cPZ₁.R cPZ₂.R) (PolyZonotope.plusE cPZ₁.E cPZ₂.E)) a)
          (Fin.castAdd n i)
        = (ConPolyZono.plusA cPZ₁.A cPZ₂.A *ᵥ
            PolyZonotope.monomial (PolyZonotope.plusE cPZ₁.R cPZ₂.R) a) i := by
    intro i
    rw [ConPolyZono.mulVec_intersectionA_left, hcol]
  -- then the agreement rows, each side's monomials read off its own factors
  have hG : ∀ i : Fin n,
      (ConPolyZono.intersectionA cPZ₁ cPZ₂ *ᵥ PolyZonotope.monomial (ConPolyZono.appendE
          (PolyZonotope.plusE cPZ₁.R cPZ₂.R) (PolyZonotope.plusE cPZ₁.E cPZ₂.E)) a)
          (Fin.natAdd (cPZ₁.m + cPZ₂.m) i)
        = (∑ l, cPZ₁.G l i
              * PolyZonotope.monomial cPZ₁.E (fun k => a (Fin.castAdd cPZ₂.p k)) l)
            - ∑ l, cPZ₂.G l i
              * PolyZonotope.monomial cPZ₂.E (fun k => a (Fin.natAdd cPZ₁.p k)) l := by
    intro i
    rw [ConPolyZono.mulVec_intersectionA_agree]
    congr 1
    · exact Finset.sum_congr rfl fun l _ => by
        rw [ConPolyZono.monomial_appendE_right, PolyZonotope.monomial_plusE_left]
    · exact Finset.sum_congr rfl fun l _ => by
        rw [ConPolyZono.monomial_appendE_right, PolyZonotope.monomial_plusE_right]
  constructor
  · intro hsat'
    -- the projections are read away first: `Fin.castAdd` does not fit `Fin (intersectionDep ..).m`
    have hsat : ConPolyZono.holds (ConPolyZono.intersectionA cPZ₁ cPZ₂)
        (ConPolyZono.intersectionB cPZ₁ cPZ₂)
        (ConPolyZono.appendE (PolyZonotope.plusE cPZ₁.R cPZ₂.R)
          (PolyZonotope.plusE cPZ₁.E cPZ₂.E)) a := hsat'
    refine ⟨(ConPolyZono.holds_plus_iff cPZ₁.A cPZ₁.b cPZ₁.R cPZ₂.A cPZ₂.b cPZ₂.R a).mp
        (fun i => ?_), fun i => ?_⟩
    · have h := hsat (Fin.castAdd n i)
      rw [hC i] at h
      simpa only [ConPolyZono.intersectionB, Fin.append_left] using h
    · have h := hsat (Fin.natAdd (cPZ₁.m + cPZ₂.m) i)
      rw [hG i] at h
      simpa only [ConPolyZono.intersectionB, Fin.append_right] using h
  · rintro ⟨hcon, hagree⟩
    have hplus :=
      (ConPolyZono.holds_plus_iff cPZ₁.A cPZ₁.b cPZ₁.R cPZ₂.A cPZ₂.b cPZ₂.R a).mpr hcon
    -- the index here reads `Fin (intersectionDep ..).m`, which `Fin.castAdd` misses
    show ConPolyZono.holds (ConPolyZono.intersectionA cPZ₁ cPZ₂)
      (ConPolyZono.intersectionB cPZ₁ cPZ₂)
      (ConPolyZono.appendE (PolyZonotope.plusE cPZ₁.R cPZ₂.R)
        (PolyZonotope.plusE cPZ₁.E cPZ₂.E)) a
    refine Fin.addCases (fun i => ?_) fun i => ?_
    · rw [hC i]
      simpa only [ConPolyZono.intersectionB, Fin.append_left] using hplus i
    · rw [hG i]
      simpa only [ConPolyZono.intersectionB, Fin.append_right] using hagree i

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
