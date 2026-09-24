import CORALean.ContSet.ConPolyZono.Float.Theorems.MemNominalSet
import CORALean.ContSet.ConZonotope.Float.Theorems.MemNominalSet
import CORALean.ContSet.Conversion.Real.ConZonotope_to_ConPolyZono
import CORALean.ContSet.HPolytope.Float.Theorems.MemConstruct
import CORALean.ContSet.PolyZonotope.Real.Operations.IdentE
import CORALean.ContSet.InflatedContSet.Theorems.MonoSubset

/-!
# A constrained zonotope as a constrained polynomial zonotope, over a
floating-point scalar

Nothing rounds. The constraint matrix is the two blocks of `P` stacked, the
upper bounds are `P`'s own, and the error box is carried across, so the only
value computed is the lower bound an inequality does not have — and it is
computed upward in absolute value, which makes it a bound rather than a cut.

Not routed through the exact layer's conversion. There a constraint is a
functional and the coefficients have to be read back off it; here they are
already a matrix, and the exact layer's `HPolytope` reading of a float one
turns each interval-valued equality into a pair of inequalities, so the two
constructions do not agree row for row even though they denote the same set.
Membership is the shorter argument.
-/

-- Authors:       Tobias Ladner
-- Written:       03-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

/-- The inequality rows, then the equality rows; entries copied. -/
def ConZonotope.conA (cZ : ConZonotope 𝕋 n) : Mat 𝕋 (cZ.P.m + cZ.P.me) cZ.h :=
  Fin.append cZ.P.A cZ.P.Ae

/-- The upper bounds are `P`'s own. An inequality has no lower bound, and gets
the free one: no factor leaves `[-1,1]`, so no row falls below minus its row sum
of absolute values, which `radius` computes upward. -/
def ConZonotope.conB (cZ : ConZonotope 𝕋 n) : Interval (Vec 𝕋 (cZ.P.m + cZ.P.me)) :=
  ⟨Fin.append (fun i => neg (radius cZ.P.A i)) cZ.P.be.inf,
   Fin.append cZ.P.b cZ.P.be.sup⟩

def ConZonotope.conPolyZono (cZ : ConZonotope 𝕋 n) : ConPolyZono 𝕋 n where
  p := cZ.h
  h := cZ.h
  q := 0
  m := cZ.P.m + cZ.P.me
  s := cZ.h
  c := cZ.c
  G := cZ.G
  E := Real.PolyZonotope.identE cZ.h
  GI := fun _ => Fin.elim0
  A := ConZonotope.conA cZ
  b := ConZonotope.conB cZ
  EC := Real.PolyZonotope.identE cZ.h
  err := cZ.E

variable [SoundFloatArithmetic 𝕋]

-- the polytope's rows read as a constraint system over the factors themselves
theorem ConZonotope.satisfies_conPolyZono (cZ : ConZonotope 𝕋 n) {β : Vec ℝ cZ.h}
    (hβ : ∀ j, |β j| ≤ 1) (hP : β ∈ cZ.P.construct) :
    cZ.conPolyZono.satisfies β := by -- --- PROOF ---
  obtain ⟨hle, heq⟩ := HPolytope.mem_construct_iff.mp hP
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
        Fin.append_left, toReal_neg]
      exact ⟨hrad.1, hle i⟩
    · rw [hEq i]
      simp only [ConZonotope.conB, Interval.nominal, RealImage.realImage, toRealVec,
        Fin.append_right]
      exact heq i
  show Real.ConPolyZono.holds (toRealMat (ConZonotope.conA cZ)) (ConZonotope.conB cZ).nominal
    (Real.PolyZonotope.identE cZ.h) β
  intro i
  rw [hm]
  exact key i


-- =======================================  MAIN THEOREM  ======================================= --

-- the point survives as it stands: identity exponents make every monomial a factor
theorem ConZonotope.conPolyZono_contains (cZ : ConZonotope 𝕋 n) :
    cZ.construct ⊆ cZ.conPolyZono.construct := by -- --- PROOF ---
  refine mono_subset (fun x hx => ?_) subset_rfl
  obtain ⟨β, hβ, hP, hx⟩ := ConZonotope.mem_nominalSet_iff.mp hx
  refine ConPolyZono.mem_nominalSet_iff.mpr ⟨β, fun _ => 0, hβ, fun j => j.elim0,
    ConZonotope.satisfies_conPolyZono cZ hβ hP, fun i => ?_⟩
  rw [hx i]
  simp only [ConZonotope.conPolyZono, Finset.univ_eq_empty, Finset.sum_empty, add_zero,
    Real.PolyZonotope.monomial_identE]
  rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
