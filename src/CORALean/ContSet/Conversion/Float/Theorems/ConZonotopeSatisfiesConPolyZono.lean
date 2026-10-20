module

public import CORALean.ContSet.ConPolyZono.Float.Theorems.MemNominalSet
public import CORALean.ContSet.ConZonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.Conversion.Real.Operations.ConZonotope_to_ConPolyZono
public import CORALean.ContSet.HPolytope.Float.Theorems.MemConstruct
public import CORALean.ContSet.Interval.Float.Theorems.Basic
public import CORALean.ContSet.PolyZonotope.Real.Operations.IdentE
public import CORALean.ContSet.InflatedContSet.Theorems.MonoSubset
public import CORALean.ContSet.Conversion.Float.Operations.ConZonotope_to_ConPolyZono
public import CORALean.ContSet.ConPolyZono.Float.Theorems.AbsSubLeSubUp

@[expose] public section

/-!
# A constrained zonotope's coefficients meet its constrained polynomial zonotope's rows

A coefficient vector in the cube that the polytope admits meets every row of
`ConZonotope.conPolyZono` within its slack: each row value lies in the row's enclosure `conB`, an
inequality's above the free lower bound `-Σ|aⱼ|`, and so within the enclosure's width of its lower
end (`abs_sub_le_subUp`).

## Inputs
* `cZ` – constrained zonotope
* `β` – factor vector

## Hypotheses
* `hβ` – factors in the unit box
* `hP` – factors satisfy the constraint polytope

## Conclusion
* factors satisfy the constraint of the constrained polynomial zonotope
-/

-- Authors:       Claude Opus 5, Claude Sonnet 5.5, Claude Opus 5.5
-- Written:       03-September-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

variable [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

-- the polytope's rows read as a constraint system over the factors themselves
theorem ConZonotope.satisfies_conPolyZono (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) {β : Vec ℝ cZ.h}
    (hβ : ∀ j, |β j| ≤ 1) (hP : β ∈ cZ.P.nominal.construct) : -- --- CONCL ---
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

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
