import CORALean.ContSet.ConZonotope.Float.Theorems.MemNominalSet
import CORALean.ContSet.VPolytope.Float.VPolytope
import CORALean.ContSet.Conversion.Float.Interval_to_HPolytope
import CORALean.ContSet.InflatedContSet.Theorems.MonoSubset

/-!
# A hull as a constrained zonotope, over a floating-point scalar

Exact, and nothing rounds: the vertices become the generators unchanged, the
centre is zero, the error box is carried over, and the constraint polytope is
the standard simplex — whose entries are `one` and `zero` and whose right-hand
side is `one` on both ends of its interval.

The unit box a constrained zonotope also imposes costs nothing, a nonnegative
coefficient in a family summing to one being at most one already.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n k : ℕ}

/-- Nonnegative, summing to one. -/
def VPolytope.simplex (𝕋 : Type) [FloatOps 𝕋] (k : ℕ) : HPolytope 𝕋 (Vec 𝕋 k) :=
  (HPolytope.ineqs (negIdentityMat 𝕋 k) fun _ => zero).intersection
    (HPolytope.eqs (fun (_ : Fin 1) (_ : Fin k) => one) ⟨fun _ => one, fun _ => one⟩)


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

theorem VPolytope.aux_ones_mulVec (β : Vec ℝ k) (i : Fin 1) :
    (toRealMat (fun (_ : Fin 1) (_ : Fin k) => (one : 𝕋)) *ᵥ β) i = ∑ j, β j := by
  show ∑ j, toReal (one : 𝕋) * β j = ∑ j, β j
  exact Finset.sum_congr rfl fun j _ => by rw [toReal_one, one_mul]

theorem VPolytope.mem_simplex_iff {β : Vec ℝ k} :
    β ∈ (VPolytope.simplex 𝕋 k).construct ↔ (∀ j, 0 ≤ β j) ∧ ∑ j, β j = 1 := by -- --- PROOF ---
  simp only [VPolytope.simplex]
  rw [HPolytope.mem_intersection_iff, HPolytope.mem_ineqs_iff, HPolytope.mem_eqs_iff]
  -- both directions: a nonnegativity row each, and the two ends of the ones-row equality
  constructor
  · rintro ⟨hle, heq⟩
    refine ⟨fun j => ?_, ?_⟩
    · have h := hle j
      rw [negIdentityMat_mulVec, toReal_zero] at h
      linarith
    · have h := heq 0
      rw [VPolytope.aux_ones_mulVec] at h
      have h₁ : toReal (one : 𝕋) ≤ ∑ j, β j := h.1
      have h₂ : ∑ j, β j ≤ toReal (one : 𝕋) := h.2
      rw [toReal_one] at h₁ h₂
      linarith
  · rintro ⟨hnn, hsum⟩
    refine ⟨fun j => ?_, fun i => ?_⟩
    · rw [negIdentityMat_mulVec, toReal_zero]
      linarith [hnn j]
    · rw [VPolytope.aux_ones_mulVec, hsum, toReal_one]
      exact ⟨le_refl 1, le_refl 1⟩

-- the vertices become the generators and the simplex their coefficient domain
def VPolytope.conZonotope (P : VPolytope (Vec 𝕋 n)) : ConZonotope 𝕋 (Vec 𝕋 n) where
  h := P.k
  c := fun _ => zero
  G := P.V
  P := VPolytope.simplex 𝕋 P.k
  E := P.E


-- =======================================  MAIN THEOREM  ======================================= --

theorem VPolytope.conZonotope_contains (P : VPolytope (Vec 𝕋 n)) :
    P.construct ⊆ P.conZonotope.construct := by -- --- PROOF ---
  refine mono_subset (fun x hx => ?_) subset_rfl
  obtain ⟨β, hnn, hsum, hval⟩ := hx
  -- a convex coefficient already lies inside the unit box, so that constraint costs nothing
  refine ConZonotope.mem_nominalSet_iff.mpr ⟨β, fun j => ?_, ?_, fun i => ?_⟩
  · rw [abs_of_nonneg (hnn j)]
    exact hsum ▸ Finset.single_le_sum (fun l _ => hnn l) (Finset.mem_univ j)
  · exact VPolytope.mem_simplex_iff.mpr ⟨hnn, hsum⟩
  · have h : x i = ∑ l, β l * toReal (P.V l i) := by
      rw [hval]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rfl
    rw [h]
    show ∑ l, β l * toReal (P.V l i) = toReal (zero : 𝕋) + ∑ l, toReal (P.V l i) * β l
    rw [toReal_zero, zero_add]
    exact Finset.sum_congr rfl fun l _ => mul_comm _ _

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
