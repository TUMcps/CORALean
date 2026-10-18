module

public import CORALean.ContSet.ConPolyZono.Real.Operations.IntersectionDep
public import CORALean.ContSet.ConPolyZono.Real.Operations.MulVecIntersectionAAgree
public import CORALean.ContSet.ConPolyZono.Real.Operations.MulVecIntersectionALeft
public import CORALean.ContSet.ConPolyZono.Real.Theorems.MulVecPlusAPlusE
public import CORALean.ContSet.ConPolyZono.Real.Theorems.MonomialAppendELeft
public import CORALean.ContSet.ConPolyZono.Real.Theorems.MonomialAppendERight

@[expose] public section

/-!
# The rows of `intersectionDep`

Each set's own rows at its own factors, then the agreement rows, the first set's generator sum
less the second's: the constraint columns are `plusA` over `plusE` on the left block, and the
generator columns `appendE` puts beside them read the generator monomials of either side. What
`satisfies_intersectionDep_iff` reads row by row, as a vector identity any row condition can be
read off.
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `intersectionDep`'s rows: each set's own at its own factors, then the agreement rows. -/
theorem ConPolyZono.mulVec_intersectionDep (cPZ₁ cPZ₂ : ConPolyZono (Vec ℝ n))
    (a : Fin (cPZ₁.p + cPZ₂.p) → ℝ) : -- --- STMT ---
    (cPZ₁.intersectionDep cPZ₂).A *ᵥ PolyZonotope.monomial (cPZ₁.intersectionDep cPZ₂).R a
      = Fin.append (Fin.append
          (cPZ₁.A *ᵥ PolyZonotope.monomial cPZ₁.R fun k => a (Fin.castAdd cPZ₂.p k))
          (cPZ₂.A *ᵥ PolyZonotope.monomial cPZ₂.R fun k => a (Fin.natAdd cPZ₁.p k)))
        fun i => (∑ l, cPZ₁.G l i
            * PolyZonotope.monomial cPZ₁.E (fun k => a (Fin.castAdd cPZ₂.p k)) l)
          - ∑ l, cPZ₂.G l i
            * PolyZonotope.monomial cPZ₂.E (fun k => a (Fin.natAdd cPZ₁.p k))
              l := by -- --- PROOF ---
  -- the exponents: both constraint blocks, then both generator blocks
  set R' := ConPolyZono.appendE (PolyZonotope.plusE cPZ₁.R cPZ₂.R)
    (PolyZonotope.plusE cPZ₁.E cPZ₂.E) with hR'
  have hcol : (fun l => PolyZonotope.monomial R' a (Fin.castAdd (cPZ₁.h + cPZ₂.h) l))
      = PolyZonotope.monomial (PolyZonotope.plusE cPZ₁.R cPZ₂.R) a :=
    funext fun l => ConPolyZono.monomial_appendE_left _ _ a l
  refine funext (Fin.addCases (fun i => ?_) fun i => ?_)
  -- the inherited rows: through the append they are `plusA` on the left block
  · show (ConPolyZono.intersectionA cPZ₁ cPZ₂ *ᵥ PolyZonotope.monomial R' a)
        (Fin.castAdd n i) = _
    rw [ConPolyZono.mulVec_intersectionA_left, hcol, ConPolyZono.mulVec_plusA_plusE,
      Fin.append_left]
  -- then the agreement rows, each side's monomials read off its own factors
  · show (ConPolyZono.intersectionA cPZ₁ cPZ₂ *ᵥ PolyZonotope.monomial R' a)
        (Fin.natAdd (cPZ₁.m + cPZ₂.m) i) = _
    rw [ConPolyZono.mulVec_intersectionA_agree, Fin.append_right]
    congr 1
    · exact Finset.sum_congr rfl fun l _ => by
        rw [ConPolyZono.monomial_appendE_right, PolyZonotope.monomial_plusE_left]
    · exact Finset.sum_congr rfl fun l _ => by
        rw [ConPolyZono.monomial_appendE_right, PolyZonotope.monomial_plusE_right]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
