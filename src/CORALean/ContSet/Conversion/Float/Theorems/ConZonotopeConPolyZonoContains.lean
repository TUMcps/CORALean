module

public import CORALean.ContSet.ConPolyZono.Float.Theorems.MemNominalSet
public import CORALean.ContSet.ConZonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.Conversion.Real.Operations.ConZonotope_to_ConPolyZono
public import CORALean.ContSet.HPolytope.Float.Theorems.MemConstruct
public import CORALean.ContSet.PolyZonotope.Real.Operations.IdentE
public import CORALean.ContSet.InflatedContSet.Theorems.MonoSubset
public import CORALean.ContSet.Conversion.Float.Operations.ConZonotope_to_ConPolyZono
public import CORALean.ContSet.Interval.Float.Theorems.Basic
public import CORALean.ContSet.ConPolyZono.Float.Theorems.AbsSubLeSubUp

@[expose] public section

/-!
# A constrained zonotope as a constrained polynomial zonotope, over a floating-point scalar

The constraint matrix is the two blocks of `P` stacked, each row held to its enclosure over the
unit cube as a right-hand side and a slack, and the error box is carried across. The only values
computed are the lower bound an inequality does not have, computed upward in absolute value,
which makes it a bound rather than a cut, and the enclosures' widths, rounded up.

Not routed through the exact layer's conversion, which adds a slack factor per row; here each
row's slack is recorded beside it instead, so the two constructions do not agree factor for
factor. Membership is the shorter argument.

## Inputs
* `cZ` – constrained zonotope

## Hypotheses
* none

## Conclusion
* set is contained in its constrained polynomial zonotope
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       03-September-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

variable [SoundFloatArithmetic 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The polytope's rows read as a constraint system over the factors themselves. -/
private theorem ConZonotope.aux_satisfies_conPolyZono (cZ : ConZonotope 𝕋 (Vec 𝕋 n))
    {β : Vec ℝ cZ.h} (hβ : ∀ j, |β j| ≤ 1) (hP : β ∈ cZ.P.nominal.construct) : -- --- CONCL ---
    β ∈ cZ.conPolyZono.cons.construct := by -- --- PROOF ---
  obtain ⟨hle, heq⟩ := HPolytope.mem_nominal_iff.mp hP
  have hm : Real.PolyZonotope.monomial (Real.PolyZonotope.identE cZ.h) β = β :=
    funext fun j => Real.PolyZonotope.monomial_identE β j
  have hlin : ∀ i : Fin cZ.P.m,
      (toRealMat (ConZonotope.conA cZ) *ᵥ β) (Fin.castAdd cZ.P.me i)
        = (toRealMat cZ.P.A *ᵥ β) i := by
    intro i
    show ∑ j, toRealMat (ConZonotope.conA cZ) (Fin.castAdd cZ.P.me i) j * β j
      = ∑ j, toRealMat cZ.P.A i j * β j
    exact Finset.sum_congr rfl fun j _ => by
      simp only [toRealMat, ConZonotope.conA, Fin.append_left]
  -- and the equality rows, which are the right half of the same append
  have hEq : ∀ i : Fin cZ.P.me,
      (toRealMat (ConZonotope.conA cZ) *ᵥ β) (Fin.natAdd cZ.P.m i)
        = (toRealMat cZ.P.Ae *ᵥ β) i := by
    intro i
    show ∑ j, toRealMat (ConZonotope.conA cZ) (Fin.natAdd cZ.P.m i) j * β j
      = ∑ j, toRealMat cZ.P.Ae i j * β j
    exact Finset.sum_congr rfl fun j _ => by
      simp only [toRealMat, ConZonotope.conA, Fin.append_right]
  have key : ∀ i, (ConZonotope.conB cZ).nominal.inf i
        ≤ (toRealMat (ConZonotope.conA cZ) *ᵥ β) i
      ∧ (toRealMat (ConZonotope.conA cZ) *ᵥ β) i ≤ (ConZonotope.conB cZ).nominal.sup i := by
    -- an inequality row takes the free lower bound, an equality row its own two
    refine Fin.addCases (fun i => ?_) fun i => ?_
    · rw [hlin i]
      have hrad : |(toRealMat cZ.P.A *ᵥ β) i| ≤ toReal (radius cZ.P.A i) :=
        abs_sum_le_radius (fun _ _ => le_rfl) hβ i
      rw [abs_le] at hrad
      simp only [ConZonotope.conB, Interval.nominal, RealImage.realImage, toRealVec,
        Fin.append_left, Pi.neg_apply, toReal_neg']
      have hu := add_le_addUp (cZ.P.b i) (absolute (cZ.P.b_error i))
      rw [toReal_absolute] at hu
      exact ⟨hrad.1, (hle i).trans hu⟩
    -- an equality row: within its slack of `be`, so inside the widened pair
    · rw [hEq i]
      simp only [ConZonotope.conB, Interval.nominal, RealImage.realImage, toRealVec,
        Fin.append_right]
      have hu := add_le_addUp (cZ.P.be i) (absolute (cZ.P.be_error i))
      have hd := subDown_le_sub (cZ.P.be i) (absolute (cZ.P.be_error i))
      rw [toReal_absolute] at hu hd
      have hab := abs_le.mp (heq i)
      exact ⟨by linarith [hab.1], by linarith [hab.2]⟩
  refine ⟨(Interval.mem_unit_iff β).mpr hβ, fun i => ?_⟩
  show |(toRealMat (ConZonotope.conA cZ) *ᵥ Real.PolyZonotope.monomial
      (Real.PolyZonotope.identE cZ.h) β) i - toReal ((ConZonotope.conB cZ).inf i)|
    ≤ |toReal (subUp ((ConZonotope.conB cZ).sup i) ((ConZonotope.conB cZ).inf i))|
  rw [hm]
  exact ConPolyZono.abs_sub_le_subUp (key i).1 (key i).2


-- =======================================  MAIN THEOREM  ======================================= --

-- the point survives as it stands: identity exponents make every monomial a factor
theorem ConZonotope.conPolyZono_contains (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) : -- --- CONCL ---
    cZ.construct ⊆ cZ.conPolyZono.construct := by -- --- PROOF ---
  refine mono_subset (fun x hx => ?_) subset_rfl
  obtain ⟨β, hβ, hP, hx⟩ := ConZonotope.mem_nominalSet_iff.mp hx
  refine ConPolyZono.mem_nominalSet_iff.mpr ⟨β, fun _ => 0, hβ, fun j => j.elim0,
    ConZonotope.aux_satisfies_conPolyZono cZ hβ hP, fun i => ?_⟩
  rw [hx i]
  simp only [ConZonotope.conPolyZono, Finset.univ_eq_empty, Finset.sum_empty, add_zero,
    Real.PolyZonotope.monomial_identE]
  rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
