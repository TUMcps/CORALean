import CORALean.ContDynamics.NonlinearSys.Operations.LagrangeRemainder
import CORALean.ContSet.Conversion.Real.Interval_to_PolyZonotope

/-!
# `lagrangeRemainder` grows with the region it is taken over

`[2]`'s property (6) for `[1, Sec. 4.1]`'s remainder box, proved rather than
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

-- Authors:       Tobias Ladner
-- Written:       13-September-2026
-- Last update:   ---
-- Last revision: ---


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

/-- `γ` is `max |z - z✱|` over the set, so it grows with the set and not with the
representation: the point attaining it on the left is a point of the right. -/
theorem aux_radius_le {Z₁ Z₂ : Zonotope (Vec ℝ d)} (hZ : Z₁.construct ⊆ Z₂.construct)
    (zs : Vec ℝ d) (j : Fin d) :
    |Z₁.c j - zs j| + ∑ k, |Z₁.G k j|
      ≤ |Z₂.c j - zs j| + ∑ k, |Z₂.G k j| := by -- --- PROOF ---
  -- the sign that turns coordinate `j` of the centre offset into its absolute value
  set s : ℝ := if 0 ≤ Z₁.c j - zs j then 1 else -1 with hsdef
  have hs1 : s = 1 ∨ s = -1 := by rw [hsdef]; split_ifs <;> simp
  have hsabs : |s| = 1 := by rcases hs1 with h | h <;> simp [h]
  have hsc : s * (Z₁.c j - zs j) = |Z₁.c j - zs j| := by
    rw [hsdef]
    split_ifs with h
    · rw [one_mul, abs_of_nonneg h]
    · rw [neg_one_mul, abs_of_neg (lt_of_not_ge h)]
  -- and the coefficients that turn every generator's contribution into its own
  set β : Fin Z₁.h → ℝ := fun k => if 0 ≤ s * Z₁.G k j then 1 else -1 with hβdef
  have hb : ∀ k, |β k| ≤ 1 := by
    intro k
    simp only [hβdef]
    split_ifs <;> simp
  have hg : ∀ k, s * (β k * Z₁.G k j) = |Z₁.G k j| := by
    intro k
    have habs : |s * Z₁.G k j| = |Z₁.G k j| := by rw [abs_mul, hsabs, one_mul]
    simp only [hβdef]
    split_ifs with h
    · rw [← habs, abs_of_nonneg h]; ring
    · rw [← habs, abs_of_neg (lt_of_not_ge h)]; ring
  -- that point is in `Z₁`, hence in `Z₂`, where the same coordinate is bounded by `γ₂`
  obtain ⟨β', hb', heq⟩ := hZ (show Z₁.c + ∑ k, β k • Z₁.G k ∈ Z₁.construct from ⟨β, hb, rfl⟩)
  have hlhs : s * ((Z₁.c + ∑ k, β k • Z₁.G k) j - zs j)
      = |Z₁.c j - zs j| + ∑ k, |Z₁.G k j| := by
    rw [aux_coord_eq, mul_add, hsc, Finset.mul_sum]
    exact congrArg _ (Finset.sum_congr rfl fun k _ => hg k)
  have hrhs : |(Z₂.c + ∑ k, β' k • Z₂.G k) j - zs j| ≤ |Z₂.c j - zs j| + ∑ k, |Z₂.G k j| := by
    rw [aux_coord_eq]
    refine le_trans (abs_add_le _ _) (add_le_add le_rfl ?_)
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun k _ => ?_)
    rw [abs_mul]
    exact mul_le_of_le_one_left (abs_nonneg _) (hb' k)
  -- the left radius is attained, the right one only bounds, and the point is shared
  calc |Z₁.c j - zs j| + ∑ k, |Z₁.G k j|
      = s * ((Z₁.c + ∑ k, β k • Z₁.G k) j - zs j) := hlhs.symm
    _ ≤ |(Z₁.c + ∑ k, β k • Z₁.G k) j - zs j| := by
        rcases hs1 with h | h
        · rw [h, one_mul]
          exact le_abs_self _
        · rw [h, neg_one_mul]
          exact neg_le_abs _
    _ = |(Z₂.c + ∑ k, β' k • Z₂.G k) j - zs j| := by rw [heq]
    _ ≤ _ := hrhs

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
