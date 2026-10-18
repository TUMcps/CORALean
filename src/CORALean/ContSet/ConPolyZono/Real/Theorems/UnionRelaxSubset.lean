module

public import CORALean.ContSet.ConPolyZono.Real.Theorems.ForallAbsSubAppendIff
public import CORALean.ContSet.ConPolyZono.Real.Theorems.ExistsUnionFactorsLeft
public import CORALean.ContSet.ConPolyZono.Real.Theorems.ExistsUnionFactorsRight
public import CORALean.ContSet.ConPolyZono.Real.Theorems.MemRelaxIff
public import CORALean.ContSet.ConPolyZono.Real.Theorems.MulVecPlusAAppendE
public import CORALean.ContSet.ConPolyZono.Real.Theorems.UnionDomainIff
public import CORALean.ContSet.ConPolyZono.Real.Operations.HoldsUnionUpperIff
public import CORALean.ContSet.ConPolyZono.Real.Operations.MulVecUnionLowerLeft
public import CORALean.ContSet.ConPolyZono.Real.Operations.MulVecUnionLowerRight
public import CORALean.ContSet.ConPolyZono.Real.Operations.SumUnionE
public import CORALean.ContSet.ConPolyZono.Real.Operations.MonomialEqZeroOfNoZeroCol
public import Mathlib.Tactic.Module

@[expose] public section

/-!
# The union of two relaxed sets lies in the relaxed union

The forward half of `union_exact_of_noZeroCol` with each operand's rows met only within a slack:
the union's operand rows carry their operand's slack and its selector rows none. On the branch
that selects an operand its rows are its own, shifted by the selector column and back, so they
are off by what the operand's were; on the other branch the other operand's factors are `0` and
its rows read `0.5 b` against `0.5 b`. This is what a float union's nominal set is checked
against, its rows recording their rounding as slack. The hypotheses are those of
`union_exact_of_noZeroCol` that this half reads.
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The union's rows, the selector rows exactly met and each operand's within its slack. -/
theorem ConPolyZono.aux_union_rows (cPZ₁ cPZ₂ : ConPolyZono α) (s₁ : Vec ℝ cPZ₁.m)
    (s₂ : Vec ℝ cPZ₂.m) (a : Fin (cPZ₁.p + cPZ₂.p + 2) → ℝ)
    (hup : ConPolyZono.holds (ConPolyZono.unionUpperA cPZ₁.p cPZ₂.p) ConPolyZono.unionUpperB
      (ConPolyZono.unionUpperR cPZ₁.p cPZ₂.p) a)
    (hlow₁ : ∀ r, |(ConPolyZono.unionLowerA cPZ₁.A cPZ₁.b cPZ₂.A cPZ₂.b
        *ᵥ PolyZonotope.monomial (ConPolyZono.unionLowerR cPZ₁.R cPZ₂.R) a) (Fin.castAdd cPZ₂.m r)
      - 2⁻¹ * cPZ₁.b r| ≤ |s₁ r|)
    (hlow₂ : ∀ r, |(ConPolyZono.unionLowerA cPZ₁.A cPZ₁.b cPZ₂.A cPZ₂.b
        *ᵥ PolyZonotope.monomial (ConPolyZono.unionLowerR cPZ₁.R cPZ₂.R) a) (Fin.natAdd cPZ₁.m r)
      - 2⁻¹ * cPZ₂.b r| ≤ |s₂ r|) : -- --- STMT ---
    ∀ i, |((cPZ₁.union cPZ₂).A *ᵥ PolyZonotope.monomial (cPZ₁.union cPZ₂).R a) i
      - (cPZ₁.union cPZ₂).b i|
        ≤ |Fin.append (0 : Vec ℝ (1 + 1)) (Fin.append s₁ s₂) i| := by -- --- PROOF ---
  have hv := ConPolyZono.mulVec_plusA_appendE (ConPolyZono.unionUpperA cPZ₁.p cPZ₂.p)
    (ConPolyZono.unionLowerA cPZ₁.A cPZ₁.b cPZ₂.A cPZ₂.b) (ConPolyZono.unionUpperR cPZ₁.p cPZ₂.p)
    (ConPolyZono.unionLowerR cPZ₁.R cPZ₂.R) a
  show ∀ i, |(ConPolyZono.plusA _ _ *ᵥ PolyZonotope.monomial (ConPolyZono.appendE _ _) a) i
    - Fin.append ConPolyZono.unionUpperB (ConPolyZono.unionLowerB cPZ₁.b cPZ₂.b) i| ≤ _
  rw [hv]
  refine (ConPolyZono.forall_abs_sub_append_iff _ _ _ _ _ _).mpr ⟨fun i => ?_, ?_⟩
  · rw [hup i, sub_self, abs_zero]
    exact abs_nonneg _
  · intro i
    refine Fin.addCases (fun r => ?_) (fun r => ?_) i
    · simpa only [ConPolyZono.unionLowerB, Fin.append_left] using hlow₁ r
    · simpa only [ConPolyZono.unionLowerB, Fin.append_right] using hlow₂ r


-- =======================================  MAIN THEOREM  ======================================= --

/-- Both relaxed operands lie in their union relaxed by their slacks, the selector rows by none. -/
theorem ConPolyZono.union_relax_subset (cPZ₁ cPZ₂ : ConPolyZono α) (s₁ : Vec ℝ cPZ₁.m)
    (s₂ : Vec ℝ cPZ₂.m) (hq₁ : cPZ₁.qI = 0) (hq₂ : cPZ₂.qI = 0)
    (hE₁ : ConPolyZono.NoZeroCol cPZ₁.E) (hR₁ : ConPolyZono.NoZeroCol cPZ₁.R)
    (hE₂ : ConPolyZono.NoZeroCol cPZ₂.E) (hR₂ : ConPolyZono.NoZeroCol cPZ₂.R) : -- --- STMT ---
    (cPZ₁.relax s₁).construct ∪ (cPZ₂.relax s₂).construct
      ⊆ ((cPZ₁.union cPZ₂).relax
          (Fin.append (0 : Vec ℝ (1 + 1)) (Fin.append s₁ s₂))).construct := by -- --- PROOF ---
  rintro _ (hx | hx)
  · -- a point of the first operand, at the branch that selects it
    obtain ⟨a₁, β₁, ha₁, -, hs₁, rfl⟩ := (ConPolyZono.mem_relax_iff _ _).mp hx
    obtain ⟨a, hab, hu, hv, hx1, hy1⟩ :=
      ConPolyZono.exists_unionFactors_left (p₂ := cPZ₂.p) 1 (by norm_num) ha₁
    have hz : ∀ k, (fun k => a (Fin.castAdd 2 (Fin.natAdd cPZ₁.p k))) k = 0 := hv
    have h1 : (fun k => a (Fin.castAdd 2 (Fin.castAdd cPZ₂.p k))) = a₁ := funext hu
    refine (ConPolyZono.mem_relax_iff _ _).mpr ⟨a, fun _ => 0, hab, fun j => j.elim0,
      ConPolyZono.aux_union_rows cPZ₁ cPZ₂ s₁ s₂ a ?_ (fun r => ?_) (fun r => ?_), ?_⟩
    · exact (ConPolyZono.holds_unionUpper_iff a).mpr
        ((ConPolyZono.union_domain_iff (a (ConPolyZono.unionSel cPZ₁.p cPZ₂.p))
          (a (Fin.natAdd (cPZ₁.p + cPZ₂.p) 1))
          (fun k => a (Fin.castAdd 2 (Fin.castAdd cPZ₂.p k)))
          (fun k => a (Fin.castAdd 2 (Fin.natAdd cPZ₁.p k)))
          (by rw [hx1]; norm_num) (by rw [hy1]; norm_num)
          (fun k => hab _)).mpr (Or.inl ⟨hx1, hy1, hv⟩))
    · rw [ConPolyZono.mulVec_unionLower_left, h1, hx1]
      have h := hs₁ r
      have e : (cPZ₁.A *ᵥ PolyZonotope.monomial cPZ₁.R a₁) r - 2⁻¹ * cPZ₁.b r * 1
          - 2⁻¹ * cPZ₁.b r = (cPZ₁.A *ᵥ PolyZonotope.monomial cPZ₁.R a₁) r - cPZ₁.b r := by ring
      rw [e]
      exact h
    -- the other operand's rows, its whole left side pinned to zero
    · rw [ConPolyZono.mulVec_unionLower_right]
      have hzero : (cPZ₂.A *ᵥ PolyZonotope.monomial cPZ₂.R
          fun k => a (Fin.castAdd 2 (Fin.natAdd cPZ₁.p k))) r = 0 := by
        show (∑ l, cPZ₂.A r l * PolyZonotope.monomial cPZ₂.R _ l) = 0
        exact Finset.sum_eq_zero fun l _ => by
          rw [ConPolyZono.monomial_eq_zero_of_noZeroCol hR₂ hz l, mul_zero]
      rw [hzero, hx1, zero_add, mul_one, sub_self, abs_zero]
      exact abs_nonneg _
    -- the point itself: at the selector `1` the center moves to `c₁`
    · have hβ₀ : (∑ j, β₁ j • cPZ₁.GI j) = 0 :=
        Finset.sum_eq_zero fun j _ => absurd j.isLt (by omega)
      have hG₂ : (∑ i, PolyZonotope.monomial cPZ₂.E
          (fun k => a (Fin.castAdd 2 (Fin.natAdd cPZ₁.p k))) i • cPZ₂.G i) = 0 :=
        Finset.sum_eq_zero fun i _ => by
          rw [ConPolyZono.monomial_eq_zero_of_noZeroCol hE₂ hz i, zero_smul]
      show cPZ₁.c + (∑ i, PolyZonotope.monomial cPZ₁.E a₁ i • cPZ₁.G i)
          + (∑ j, β₁ j • cPZ₁.GI j)
        = (2:ℝ)⁻¹ • (cPZ₁.c + cPZ₂.c)
          + (∑ i, PolyZonotope.monomial (ConPolyZono.unionE cPZ₁.E cPZ₂.E) a i
              • ConPolyZono.unionG cPZ₁.c cPZ₂.c cPZ₁.G cPZ₂.G i)
          + ∑ j : Fin 0, (0:ℝ) • (Fin.elim0 j : α)
      rw [ConPolyZono.sum_unionE, h1, hG₂, hβ₀, hx1]
      simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero]
      module
  · -- the mirror, a point of the second operand at the other branch
    obtain ⟨a₂, β₂, ha₂, -, hs₂, rfl⟩ := (ConPolyZono.mem_relax_iff _ _).mp hx
    obtain ⟨a, hab, hu, hv, hx1, hy1⟩ :=
      ConPolyZono.exists_unionFactors_right (p₁ := cPZ₁.p) (-1) (by norm_num) ha₂
    have hz : ∀ k, (fun k => a (Fin.castAdd 2 (Fin.castAdd cPZ₂.p k))) k = 0 := hu
    have h2 : (fun k => a (Fin.castAdd 2 (Fin.natAdd cPZ₁.p k))) = a₂ := funext hv
    refine (ConPolyZono.mem_relax_iff _ _).mpr ⟨a, fun _ => 0, hab, fun j => j.elim0,
      ConPolyZono.aux_union_rows cPZ₁ cPZ₂ s₁ s₂ a ?_ (fun r => ?_) (fun r => ?_), ?_⟩
    · exact (ConPolyZono.holds_unionUpper_iff a).mpr
        ((ConPolyZono.union_domain_iff (a (ConPolyZono.unionSel cPZ₁.p cPZ₂.p))
          (a (Fin.natAdd (cPZ₁.p + cPZ₂.p) 1))
          (fun k => a (Fin.castAdd 2 (Fin.castAdd cPZ₂.p k)))
          (fun k => a (Fin.castAdd 2 (Fin.natAdd cPZ₁.p k)))
          (by rw [hx1]; norm_num) (by rw [hy1]; norm_num)
          (fun k => hab _)).mpr (Or.inr ⟨hx1, hy1, hu⟩))
    -- the first operand's rows, its whole left side pinned to zero
    · rw [ConPolyZono.mulVec_unionLower_left]
      have hzero : (cPZ₁.A *ᵥ PolyZonotope.monomial cPZ₁.R
          fun k => a (Fin.castAdd 2 (Fin.castAdd cPZ₂.p k))) r = 0 := by
        show (∑ l, cPZ₁.A r l * PolyZonotope.monomial cPZ₁.R _ l) = 0
        exact Finset.sum_eq_zero fun l _ => by
          rw [ConPolyZono.monomial_eq_zero_of_noZeroCol hR₁ hz l, mul_zero]
      rw [hzero, hx1]
      have e : (0:ℝ) - 2⁻¹ * cPZ₁.b r * -1 - 2⁻¹ * cPZ₁.b r = 0 := by ring
      rw [e, abs_zero]
      exact abs_nonneg _
    · rw [ConPolyZono.mulVec_unionLower_right, h2, hx1]
      have h := hs₂ r
      have e : (cPZ₂.A *ᵥ PolyZonotope.monomial cPZ₂.R a₂) r + 2⁻¹ * cPZ₂.b r * -1
          - 2⁻¹ * cPZ₂.b r = (cPZ₂.A *ᵥ PolyZonotope.monomial cPZ₂.R a₂) r - cPZ₂.b r := by ring
      rw [e]
      exact h
    -- and the point, the selector `-1` moving the center to `c₂`
    · have hβ₀ : (∑ j, β₂ j • cPZ₂.GI j) = 0 :=
        Finset.sum_eq_zero fun j _ => absurd j.isLt (by omega)
      have hG₁ : (∑ i, PolyZonotope.monomial cPZ₁.E
          (fun k => a (Fin.castAdd 2 (Fin.castAdd cPZ₂.p k))) i • cPZ₁.G i) = 0 :=
        Finset.sum_eq_zero fun i _ => by
          rw [ConPolyZono.monomial_eq_zero_of_noZeroCol hE₁ hz i, zero_smul]
      show cPZ₂.c + (∑ i, PolyZonotope.monomial cPZ₂.E a₂ i • cPZ₂.G i)
          + (∑ j, β₂ j • cPZ₂.GI j)
        = (2:ℝ)⁻¹ • (cPZ₁.c + cPZ₂.c)
          + (∑ i, PolyZonotope.monomial (ConPolyZono.unionE cPZ₁.E cPZ₂.E) a i
              • ConPolyZono.unionG cPZ₁.c cPZ₂.c cPZ₁.G cPZ₂.G i)
          + ∑ j : Fin 0, (0:ℝ) • (Fin.elim0 j : α)
      rw [ConPolyZono.sum_unionE, h2, hG₁, hβ₀, hx1]
      simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero]
      module

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
