import CORALean.ContDynamics.NonlinearSys.Operations.LagrangeRemainder
import CORALean.ContDynamics.NonlinearSys.Theorems.ZonotopeRadiusAttained
import CORALean.ContSet.Conversion.Real.Interval_to_PolyZonotope

/-!
# `lagrangeRemainder` grows with the region it is taken over

`[2, Lemma 3]`'s property (6) for `[1, Sec. 4.1]`'s remainder box, proved rather than
assumed. It holds for a reason worth naming: `γ` is not an artefact of the
zonotope's generators but exactly `max |z - z✱|` over what it denotes, so a
larger denoted set gives a larger `γ` whatever representation carries it — which
is what fails for `zono`, the one step of `[2, Alg. 2]` that does not have this.

`0 ≤ E` is carried and is not an added hypothesis: `E` bounds a third derivative
entrywise, so `AbstractionError.of_lagrange`'s own `hEb` already forces it. The
box would otherwise shrink as `γ` grew, in the coordinates where `E` was negative.

## References

* [1] M. Althoff. "Reachability Analysis of Nonlinear Systems using Conservative
      Polynomialization and Non-Convex Sets". HSCC 2013.
* [2] N. Kochdumper, B. Schürmann and M. Althoff. "Utilizing Dependencies to
      Obtain Subsets of Reachable Sets". HSCC 2020. arXiv:1910.08354.
-/

-- Authors:       Claude Opus 5
-- Written:       13-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real

open Matrix

variable {d n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- One coordinate of a zonotope's point, written as its centre plus what the
generators contribute there. -/
theorem aux_coord_eq (Z : Zonotope (Vec ℝ d)) (β : Fin Z.h → ℝ) (zs : Vec ℝ d) (j : Fin d) :
    (Z.c + ∑ k, β k • Z.G k) j - zs j = (Z.c j - zs j) + ∑ k, β k * Z.G k j := by
  rw [Pi.add_apply, Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- `γ` grows with the set and not with the representation: the point attaining it on the
left is a point of the right. -/
theorem aux_radius_le {Z₁ Z₂ : Zonotope (Vec ℝ d)} (hZ : Z₁.construct ⊆ Z₂.construct)
    (zs : Vec ℝ d) (j : Fin d) :
    |Z₁.c j - zs j| + ∑ k, |Z₁.G k j|
      ≤ |Z₂.c j - zs j| + ∑ k, |Z₂.G k j| := by -- --- PROOF ---
  -- that point is in `Z₁`, hence in `Z₂`, where the same coordinate is bounded by `γ₂`
  obtain ⟨z, hz, hle⟩ := Real.Zonotope.radius_attained Z₁ zs j
  obtain ⟨β', hb', rfl⟩ := hZ hz
  refine le_trans hle ?_
  rw [aux_coord_eq]
  refine le_trans (abs_add_le _ _) (add_le_add le_rfl ?_)
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun k _ => ?_)
  rw [abs_mul]
  exact mul_le_of_le_one_left (abs_nonneg _) (hb' k)

/-- An entrywise nonnegative form is nonnegative, and monotone, at nonnegative
arguments. -/
theorem aux_quad_le {M : Mat ℝ d d} (hM : ∀ k l, 0 ≤ M k l) {γ₁ γ₂ : Vec ℝ d}
    (h0 : ∀ j, 0 ≤ γ₁ j) (h : ∀ j, γ₁ j ≤ γ₂ j) :
    0 ≤ γ₁ ⬝ᵥ (M *ᵥ γ₁) ∧ γ₁ ⬝ᵥ (M *ᵥ γ₁) ≤ γ₂ ⬝ᵥ (M *ᵥ γ₂) := by -- --- PROOF ---
  have hrow : ∀ (γ : Vec ℝ d), (∀ j, 0 ≤ γ j) → ∀ k, 0 ≤ ∑ l, M k l * γ l :=
    fun γ hγ k => Finset.sum_nonneg fun l _ => mul_nonneg (hM k l) (hγ l)
  have h0' : ∀ j, 0 ≤ γ₂ j := fun j => le_trans (h0 j) (h j)
  simp only [dotProduct, Matrix.mulVec]
  refine ⟨Finset.sum_nonneg fun k _ => mul_nonneg (h0 k) (hrow γ₁ h0 k), ?_⟩
  -- each summand grows in both the outer factor and the row it multiplies
  exact Finset.sum_le_sum fun k _ => mul_le_mul (h k)
    (Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left (h l) (hM k l))
    (hrow γ₁ h0 k) (h0' k)


-- =======================================  MAIN THEOREM  ======================================= --

/-- A larger region gives a larger remainder box, once `E` is read as the
entrywise bound it is. -/
theorem lagrangeRemainder_mono {E : Fin n → Fin d → Mat ℝ d d} (hE : ∀ i j k l, 0 ≤ E i j k l)
    {Z₁ Z₂ : Zonotope (Vec ℝ d)} (hZ : Z₁.construct ⊆ Z₂.construct) (zs : Vec ℝ d) :
    (lagrangeRemainder E Z₁ zs).polyZonotope.construct
      ⊆ (lagrangeRemainder E Z₂ zs).polyZonotope.construct := by -- --- PROOF ---
  set γ₁ : Vec ℝ d := fun j => |Z₁.c j - zs j| + ∑ k, |Z₁.G k j| with hγ₁
  set γ₂ : Vec ℝ d := fun j => |Z₂.c j - zs j| + ∑ k, |Z₂.G k j| with hγ₂
  have h0 : ∀ j, 0 ≤ γ₁ j := fun j => by
    rw [hγ₁]
    exact add_nonneg (abs_nonneg _) (Finset.sum_nonneg fun _ _ => abs_nonneg _)
  have h : ∀ j, γ₁ j ≤ γ₂ j := fun j => aux_radius_le hZ zs j
  -- the box's half-width, nonnegative and monotone one coordinate at a time
  have hl : ∀ i : Fin n, 0 ≤ (∑ j, γ₁ j * (γ₁ ⬝ᵥ (E i j *ᵥ γ₁))) / 6
      ∧ (∑ j, γ₁ j * (γ₁ ⬝ᵥ (E i j *ᵥ γ₁))) / 6
        ≤ (∑ j, γ₂ j * (γ₂ ⬝ᵥ (E i j *ᵥ γ₂))) / 6 := by
    intro i
    have hsum : ∀ j, 0 ≤ γ₁ j * (γ₁ ⬝ᵥ (E i j *ᵥ γ₁))
        ∧ γ₁ j * (γ₁ ⬝ᵥ (E i j *ᵥ γ₁)) ≤ γ₂ j * (γ₂ ⬝ᵥ (E i j *ᵥ γ₂)) := fun j =>
      ⟨mul_nonneg (h0 j) (aux_quad_le (hE i j) h0 h).1,
        mul_le_mul (h j) (aux_quad_le (hE i j) h0 h).2 (aux_quad_le (hE i j) h0 h).1
          (le_trans (h0 j) (h j))⟩
    have hnn := Finset.sum_nonneg fun j (_ : j ∈ Finset.univ) => (hsum j).1
    have hmono := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => (hsum j).2
    exact ⟨by linarith, by linarith⟩
  -- a symmetric box inside a wider symmetric one, both well ordered
  refine Interval.polyZonotope_mono (fun i => ?_) (fun i => ?_) (fun i => ?_) <;>
    simp only [lagrangeRemainder, Pi.neg_apply, neg_le_neg_iff] <;>
    linarith [(hl i).1, (hl i).2]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
