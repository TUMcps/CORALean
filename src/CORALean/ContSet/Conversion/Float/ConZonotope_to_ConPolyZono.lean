import CORALean.ContSet.ConPolyZono.Float.ConPolyZono
import CORALean.ContSet.ConZonotope.Float.ConZonotope
import CORALean.ContSet.Conversion.Real.ConZonotope_to_ConPolyZono
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

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

/-- The inequality rows, then the equality rows; entries copied. -/
def ConZonotope.conA (C : ConZonotope 𝕋 n) : Mat 𝕋 (C.P.m + C.P.me) C.h :=
  Fin.append C.P.A C.P.Ae

/-- The upper bounds are `P`'s own. An inequality has no lower bound, and gets
the free one: no factor leaves `[-1,1]`, so no row falls below minus its row sum
of absolute values, which `radius` computes upward. -/
def ConZonotope.conB (C : ConZonotope 𝕋 n) : Interval 𝕋 (C.P.m + C.P.me) :=
  ⟨Fin.append (fun i => neg (radius C.P.A i)) C.P.be.inf,
   Fin.append C.P.b C.P.be.sup⟩

def ConZonotope.conPolyZono (C : ConZonotope 𝕋 n) : ConPolyZono 𝕋 n where
  p := C.h
  h := C.h
  q := 0
  m := C.P.m + C.P.me
  s := C.h
  c := C.c
  G := C.G
  E := Real.PolyZonotope.identE C.h
  GI := fun _ => Fin.elim0
  A := ConZonotope.conA C
  b := ConZonotope.conB C
  EC := Real.PolyZonotope.identE C.h
  err := C.E

variable [SoundFloatArithmetic 𝕋]

-- the polytope's rows read as a constraint system over the factors themselves
theorem ConZonotope.satisfies_conPolyZono (C : ConZonotope 𝕋 n) {β : Vec ℝ C.h}
    (hβ : ∀ j, |β j| ≤ 1) (hP : β ∈ C.P.construct) : C.conPolyZono.satisfies β := by
  obtain ⟨hle, heq⟩ := HPolytope.mem_construct_iff.mp hP
  have hm : Real.PolyZonotope.monomial (Real.PolyZonotope.identE C.h) β = β :=
    funext fun j => Real.PolyZonotope.monomial_identE β j
  have hlin : ∀ i : Fin C.P.m,
      (toRealMat (ConZonotope.conA C) *ᵥ β) (Fin.castAdd C.P.me i)
        = (toRealMat C.P.A *ᵥ β) i := by
    intro i
    show ∑ j, toRealMat (ConZonotope.conA C) (Fin.castAdd C.P.me i) j * β j
      = ∑ j, toRealMat C.P.A i j * β j
    exact Finset.sum_congr rfl fun j _ => by
      simp only [toRealMat, ConZonotope.conA, Fin.append_left]
  -- and the equality rows, which are the right half of the same append
  have hEq : ∀ i : Fin C.P.me,
      (toRealMat (ConZonotope.conA C) *ᵥ β) (Fin.natAdd C.P.m i)
        = (toRealMat C.P.Ae *ᵥ β) i := by
    intro i
    show ∑ j, toRealMat (ConZonotope.conA C) (Fin.natAdd C.P.m i) j * β j
      = ∑ j, toRealMat C.P.Ae i j * β j
    exact Finset.sum_congr rfl fun j _ => by
      simp only [toRealMat, ConZonotope.conA, Fin.append_right]
  have key : ∀ i, (ConZonotope.conB C).nominal.inf i
        ≤ (toRealMat (ConZonotope.conA C) *ᵥ β) i
      ∧ (toRealMat (ConZonotope.conA C) *ᵥ β) i ≤ (ConZonotope.conB C).nominal.sup i := by
    -- an inequality row takes the free lower bound, an equality row its own two
    refine Fin.addCases (fun i => ?_) fun i => ?_
    · rw [hlin i]
      have hrad : |(toRealMat C.P.A *ᵥ β) i| ≤ toReal (radius C.P.A i) :=
        abs_sum_le_radius (fun _ _ => le_rfl) hβ i
      rw [abs_le] at hrad
      simp only [ConZonotope.conB, Interval.nominal, toRealVec, Fin.append_left,
        toReal_neg]
      exact ⟨hrad.1, hle i⟩
    · rw [hEq i]
      simp only [ConZonotope.conB, Interval.nominal, toRealVec, Fin.append_right]
      exact heq i
  show Real.ConPolyZono.holds (toRealMat (ConZonotope.conA C)) (ConZonotope.conB C).nominal
    (Real.PolyZonotope.identE C.h) β
  intro i
  rw [hm]
  exact key i

-- the point survives as it stands: identity exponents make every monomial a factor
theorem ConZonotope.conPolyZono_outer (C : ConZonotope 𝕋 n) :
    C.construct ⊆ C.conPolyZono.construct := by
  refine mono_subset (fun x hx => ?_) subset_rfl
  obtain ⟨β, hβ, hP, hx⟩ := ConZonotope.mem_nominalSet_iff.mp hx
  refine ConPolyZono.mem_nominalSet_iff.mpr ⟨β, fun _ => 0, hβ, fun j => j.elim0,
    ConZonotope.satisfies_conPolyZono C hβ hP, fun i => ?_⟩
  rw [hx i]
  simp only [ConZonotope.conPolyZono, Finset.univ_eq_empty, Finset.sum_empty, add_zero,
    Real.PolyZonotope.monomial_identE]
  rfl

end CORALean.Float
