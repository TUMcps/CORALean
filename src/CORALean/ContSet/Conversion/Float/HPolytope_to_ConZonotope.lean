import CORALean.ContSet.ConZonotope.Float.ConZonotope
import CORALean.ContSet.Conversion.Float.HPolytope_to_Zonotope
import CORALean.ContSet.InflatedContSet.Theorems.MonoSubset

/-!
# A halfspace description as a constrained zonotope, over a floating-point scalar

The rows are carried onto the coefficients by composing with the generators,
which is a matrix product and so rounds. That is the difficulty this pair has
and the others do not: a rounded product does not merely shift a bound, it says
something *different* about the coefficients, and a constraint that says
something different can cut off points the original kept.

So the composed rows are stored rounded down and the bounds are widened by what
the rounding can reach — `matMulDiff` records the gap entrywise, and `radius`
sums it over a row, which is the most a coefficient vector in the unit box can
turn that gap into. Both ends of an equality row move outward, which is what its
interval right-hand side is for.

Stated for any zonotope containing the polytope, since nothing depends on it
being the box; `conZonotope` uses the box because that is what the certificates
already give.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n q h : ℕ}

/-- A row reads a point as the centre's contribution plus the generators'. -/
theorem aux_row_split (M : Mat 𝕋 q n) (G : Mat 𝕋 n h) (c : Vec 𝕋 n) (β : Vec ℝ h)
    (x : Vec ℝ n) (hx : ∀ k, x k = toReal (c k) + ∑ j, toReal (G k j) * β j) (i : Fin q) :
    (toRealMat M *ᵥ x) i
      = (∑ k, toReal (M i k) * toReal (c k))
        + ∑ j, (∑ k, toReal (M i k) * toReal (G k j)) * β j := by
  show ∑ k, toReal (M i k) * x k = _
  rw [Finset.sum_congr rfl fun k (_ : k ∈ Finset.univ) => by rw [hx k]]
  simp only [mul_add, Finset.mul_sum]
  rw [Finset.sum_add_distrib]
  refine congrArg _ ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by ring

/-- What the stored product can be off by, on the unit box. -/
theorem aux_prod_error (M : Mat 𝕋 q n) (G : Mat 𝕋 n h) (β : Vec ℝ h)
    (hβ : ∀ j, |β j| ≤ 1) (i : Fin q) :
    |(∑ j, (∑ k, toReal (M i k) * toReal (G k j)) * β j)
        - (toRealMat (matMulDown M G) *ᵥ β) i|
      ≤ toReal (radius (matMulDiff M G) i) := by
  have hd : ∀ (i' : Fin q) (j : Fin h),
      |(∑ k, toReal (M i' k) * toReal (G k j)) - toReal (matMulDown M G i' j)|
        ≤ |toReal (matMulDiff M G i' j)| := by
    intro i' j
    have h₁ : toReal (matMulDown M G i' j) ≤ ∑ k, toReal (M i' k) * toReal (G k j) :=
      dotDown_le (M i') fun k => G k j
    have h₂ : (∑ k, toReal (M i' k) * toReal (G k j)) ≤ toReal (matMulUp M G i' j) :=
      le_dotUp (M i') fun k => G k j
    have h₃ : toReal (matMulUp M G i' j) - toReal (matMulDown M G i' j)
        ≤ toReal (matMulDiff M G i' j) := sub_le_subUp _ _
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    linarith
  have hshape : (∑ j, (∑ k, toReal (M i k) * toReal (G k j)) * β j)
      - (toRealMat (matMulDown M G) *ᵥ β) i
      = ∑ j, ((∑ k, toReal (M i k) * toReal (G k j)) - toReal (matMulDown M G i j)) * β j := by
    show _ - ∑ j, toReal (matMulDown M G i j) * β j = _
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hshape]
  exact abs_sum_le_radius hd hβ i

/-- The rows, carried onto the coefficients and widened by what carrying them
rounds off. -/
def HPolytope.onCoefficients (P : HPolytope 𝕋 n) (Z : Zonotope 𝕋 n) : HPolytope 𝕋 Z.h where
  m := P.m
  A := matMulDown P.A Z.G
  b := fun i => addUp (subUp (P.b i) (dotDown (P.A i) Z.c)) (radius (matMulDiff P.A Z.G) i)
  me := P.me
  Ae := matMulDown P.Ae Z.G
  be := ⟨fun i => subDown (subDown (P.be.inf i) (dotUp (P.Ae i) Z.c))
            (radius (matMulDiff P.Ae Z.G) i),
         fun i => addUp (subUp (P.be.sup i) (dotDown (P.Ae i) Z.c))
            (radius (matMulDiff P.Ae Z.G) i)⟩

def HPolytope.conZonotopeOf (P : HPolytope 𝕋 n) (Z : Zonotope 𝕋 n) : ConZonotope 𝕋 n where
  h := Z.h
  c := Z.c
  G := Z.G
  P := P.onCoefficients Z
  E := Z.E

theorem HPolytope.subset_nominal_conZonotopeOf (P : HPolytope 𝕋 n) (Z : Zonotope 𝕋 n)
    (hZ : P.construct ⊆ nominalSet Z) :
    P.construct ⊆ nominalSet (P.conZonotopeOf Z) := by
  intro x hx
  obtain ⟨β, hβ, hval⟩ := Zonotope.mem_nominalSet_iff.mp (hZ hx)
  obtain ⟨hle, heq⟩ := HPolytope.mem_construct_iff.mp hx
  refine ConZonotope.mem_nominalSet_iff.mpr ⟨β, hβ, ?_, hval⟩
  refine HPolytope.mem_construct_iff.mpr ⟨fun i => ?_, fun i => ⟨?_, ?_⟩⟩
  · show (toRealMat (matMulDown P.A Z.G) *ᵥ β) i
        ≤ toReal (addUp (subUp (P.b i) (dotDown (P.A i) Z.c)) (radius (matMulDiff P.A Z.G) i))
    have hsplit := aux_row_split P.A Z.G Z.c β x hval i
    have herr := abs_le.mp (aux_prod_error P.A Z.G β hβ i)
    have hc := dotDown_le (P.A i) Z.c
    have hb := sub_le_subUp (P.b i) (dotDown (P.A i) Z.c)
    have hadd := add_le_addUp (subUp (P.b i) (dotDown (P.A i) Z.c))
      (radius (matMulDiff P.A Z.G) i)
    have h := hle i
    rw [hsplit] at h
    linarith [herr.1, herr.2]
  · show toReal (subDown (subDown (P.be.inf i) (dotUp (P.Ae i) Z.c))
          (radius (matMulDiff P.Ae Z.G) i))
        ≤ (toRealMat (matMulDown P.Ae Z.G) *ᵥ β) i
    have hsplit := aux_row_split P.Ae Z.G Z.c β x hval i
    have herr := abs_le.mp (aux_prod_error P.Ae Z.G β hβ i)
    have hc := le_dotUp (P.Ae i) Z.c
    have hb := subDown_le_sub (P.be.inf i) (dotUp (P.Ae i) Z.c)
    have hsub := subDown_le_sub (subDown (P.be.inf i) (dotUp (P.Ae i) Z.c))
      (radius (matMulDiff P.Ae Z.G) i)
    have h := (heq i).1
    rw [hsplit] at h
    linarith [herr.1, herr.2]
  · show (toRealMat (matMulDown P.Ae Z.G) *ᵥ β) i
        ≤ toReal (addUp (subUp (P.be.sup i) (dotDown (P.Ae i) Z.c))
          (radius (matMulDiff P.Ae Z.G) i))
    have hsplit := aux_row_split P.Ae Z.G Z.c β x hval i
    have herr := abs_le.mp (aux_prod_error P.Ae Z.G β hβ i)
    have hc := dotDown_le (P.Ae i) Z.c
    have hb := sub_le_subUp (P.be.sup i) (dotDown (P.Ae i) Z.c)
    have hadd := add_le_addUp (subUp (P.be.sup i) (dotDown (P.Ae i) Z.c))
      (radius (matMulDiff P.Ae Z.G) i)
    have h := (heq i).2
    rw [hsplit] at h
    linarith [herr.1, herr.2]

noncomputable def HPolytope.conZonotope {P : HPolytope 𝕋 n}
    (up : ∀ j, FloatBound 𝕋 P.construct (LinearMap.proj j))
    (lo : ∀ j, FloatBound 𝕋 P.construct (-LinearMap.proj j)) : ConZonotope 𝕋 n :=
  P.conZonotopeOf (HPolytope.zonotope up lo)

theorem HPolytope.subset_conZonotope {P : HPolytope 𝕋 n}
    (up : ∀ j, FloatBound 𝕋 P.construct (LinearMap.proj j))
    (lo : ∀ j, FloatBound 𝕋 P.construct (-LinearMap.proj j)) :
    P.construct ⊆ (HPolytope.conZonotope up lo).construct := by
  intro x hx
  refine ⟨x, P.subset_nominal_conZonotopeOf _ (fun y hy =>
    Interval.subset_nominal_zonotope _ (HPolytope.interval_outer up lo hy)) hx, 0, fun i => ?_, ?_⟩
  · show toReal (zero : 𝕋) ≤ (0 : Vec ℝ n) i ∧ (0 : Vec ℝ n) i ≤ toReal (zero : 𝕋)
    rw [toReal_zero]
    exact ⟨le_refl 0, le_refl 0⟩
  · show x + 0 = x
    rw [add_zero]

end CORALean.Float
