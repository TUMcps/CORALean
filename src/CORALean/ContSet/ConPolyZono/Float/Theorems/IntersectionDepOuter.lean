module

public import CORALean.ContSet.ConPolyZono.Float.Operations.IntersectionDep
public import CORALean.ContSet.ConPolyZono.Float.Theorems.AbsSubLeSubUp
public import CORALean.ContSet.ConPolyZono.Float.Theorems.MemNominalSet
public import CORALean.ContSet.PolyLevelSet.Float.Theorems.MemAndRowsIff
public import CORALean.ContSet.PolyLevelSet.Float.Theorems.MemCartProdIff
public import CORALean.ContSet.PolyLevelSet.Float.Theorems.MemConstructIffOfEq
public import CORALean.ContSet.PolyZonotope.Real.Theorems.MonomialPlusELeft
public import CORALean.ContSet.PolyZonotope.Real.Theorems.MonomialPlusERight

@[expose] public section

/-!
# `intersectionDep` over-approximates the intersection

A point of both sets is `y₁ + e₁ = y₂ + e₂`, its nominal parts at factors `a₁` and `a₂`. At the
appended factors the constraint, the product of the two sets' stacked on the agreement rows
(`PolyLevelSet.mem_cartProd_iff`, `PolyLevelSet.and_exact`), holds: each set's own rows, within
its slack, and the agreement rows `y₁ - c₁ - (y₂ - c₂)`, which is `c₂ - c₁ + e₂ - e₁`
and lies in the stored interval `intersectionAgree` (`aux_agree_mem`), so within its recorded
slack of the lower end. The rounding of the centers never has to be pushed anywhere.
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       03-September-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- What the two error boxes let the two nominal points differ by, plus the centers' difference,
lies in the stored agreement interval. -/
theorem ConPolyZono.aux_agree_mem (cPZ₁ cPZ₂ : ConPolyZono 𝕋 (Vec 𝕋 n)) {e₁ e₂ : Vec ℝ n}
    (h₁ : e₁ ∈ cPZ₁.I_error.construct) (h₂ : e₂ ∈ cPZ₂.I_error.construct)
    (i : Fin n) : -- --- STMT ---
    toReal ((ConPolyZono.intersectionAgree cPZ₁ cPZ₂).inf i)
        ≤ toReal (cPZ₂.c i) - toReal (cPZ₁.c i) + (e₂ i - e₁ i)
      ∧ toReal (cPZ₂.c i) - toReal (cPZ₁.c i) + (e₂ i - e₁ i)
        ≤ toReal ((ConPolyZono.intersectionAgree cPZ₁ cPZ₂).sup i) := by -- --- PROOF ---
  have hb₁ : toReal (cPZ₁.I_error.inf i) ≤ e₁ i ∧ e₁ i ≤ toReal (cPZ₁.I_error.sup i) := h₁ i
  have hb₂ : toReal (cPZ₂.I_error.inf i) ≤ e₂ i ∧ e₂ i ≤ toReal (cPZ₂.I_error.sup i) := h₂ i
  simp only [ConPolyZono.intersectionAgree]
  constructor
  · linarith [addDown_le_add (subDown (cPZ₂.c i) (cPZ₁.c i))
        (subDown (cPZ₂.I_error.inf i) (cPZ₁.I_error.sup i)),
      subDown_le_sub (cPZ₂.c i) (cPZ₁.c i),
      subDown_le_sub (cPZ₂.I_error.inf i) (cPZ₁.I_error.sup i), hb₁.2, hb₂.1]
  · linarith [add_le_addUp (subUp (cPZ₂.c i) (cPZ₁.c i))
      (subUp (cPZ₂.I_error.sup i) (cPZ₁.I_error.inf i)),
      sub_le_subUp (cPZ₂.c i) (cPZ₁.c i),
      sub_le_subUp (cPZ₂.I_error.sup i) (cPZ₁.I_error.inf i), hb₁.1, hb₂.2]


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.intersectionDep_outer (cPZ₁ cPZ₂ : ConPolyZono 𝕋 (Vec 𝕋 n)) (hq₁ : cPZ₁.qI = 0)
    (hq₂ : cPZ₂.qI = 0) :
    cPZ₁.construct ∩ cPZ₂.construct ⊆ (cPZ₁.intersectionDep cPZ₂).construct := by -- --- PROOF ---
  rintro x ⟨⟨y₁, hy₁, e₁, he₁, hx₁⟩, y₂, hy₂, e₂, he₂, hx₂⟩
  have hx₁' : y₁ + e₁ = x := hx₁
  have hx₂' : y₂ + e₂ = x := hx₂
  obtain ⟨a₁, β₁, ha₁, -, hs₁, hy₁⟩ := ConPolyZono.mem_nominalSet_iff.mp hy₁
  obtain ⟨a₂, β₂, ha₂, -, hs₂, hy₂⟩ := ConPolyZono.mem_nominalSet_iff.mp hy₂
  have hz₁ : ∀ i, ∑ j, toReal (cPZ₁.GI j i) * β₁ j = 0 := fun i =>
    Finset.sum_eq_zero fun j _ => absurd j.isLt (by omega)
  have hz₂ : ∀ i, ∑ j, toReal (cPZ₂.GI j i) * β₂ j = 0 := fun i =>
    Finset.sum_eq_zero fun j _ => absurd j.isLt (by omega)
  have hA₁ : (fun k => Fin.append a₁ a₂ (Fin.castAdd cPZ₂.p k)) = a₁ :=
    funext fun k => Fin.append_left a₁ a₂ k
  have hA₂ : (fun k => Fin.append a₁ a₂ (Fin.natAdd cPZ₁.p k)) = a₂ :=
    funext fun k => Fin.append_right a₁ a₂ k
  refine ⟨y₁, ConPolyZono.mem_nominalSet_iff.mpr ⟨Fin.append a₁ a₂, Fin.elim0,
    Fin.addCases (fun k => by simpa using ha₁ k) (fun k => by simpa using ha₂ k),
    fun j => j.elim0, ?_, fun i => ?_⟩, e₁, he₁, hx₁⟩
  -- the constraints: each set's own rows, then the agreement rows
  · show Fin.append a₁ a₂
      ∈ ((cPZ₁.cons.cartProd cPZ₂.cons).andRows (ConPolyZono.agreeCons cPZ₁ cPZ₂)).construct
    rw [PolyLevelSet.mem_andRows_iff, PolyLevelSet.mem_cartProd_iff, hA₁, hA₂]
    refine ⟨⟨hs₁, hs₂⟩, fun i => ?_⟩
    show |(toRealMat (ConPolyZono.agreeCons cPZ₁ cPZ₂).A *ᵥ Real.PolyZonotope.monomial
        (ConPolyZono.agreeCons cPZ₁ cPZ₂).R (Fin.append a₁ a₂)) i
        - toReal ((ConPolyZono.agreeCons cPZ₁ cPZ₂).b i)|
      ≤ |toReal ((ConPolyZono.agreeCons cPZ₁ cPZ₂).b_error i)|
    -- an agreement row reads each set's generator monomials at its own factors
    have hrow : (toRealMat (ConPolyZono.agreeCons cPZ₁ cPZ₂).A *ᵥ Real.PolyZonotope.monomial
          (ConPolyZono.agreeCons cPZ₁ cPZ₂).R (Fin.append a₁ a₂)) i
        = (∑ l, toReal (cPZ₁.G l i) * Real.PolyZonotope.monomial cPZ₁.E a₁ l)
          - ∑ l, toReal (cPZ₂.G l i) * Real.PolyZonotope.monomial cPZ₂.E a₂ l := by
      show ∑ l : Fin (cPZ₁.h + cPZ₂.h), toReal (ConPolyZono.agreeRow cPZ₁ cPZ₂ i l)
        * Real.PolyZonotope.monomial (Real.PolyZonotope.plusE cPZ₁.E cPZ₂.E) (Fin.append a₁ a₂) l
        = _
      rw [Fin.sum_univ_add]
      simp only [ConPolyZono.agreeRow, Fin.append_left, Fin.append_right, toReal_neg, neg_mul,
        Finset.sum_neg_distrib, Real.PolyZonotope.monomial_plusE_left,
        Real.PolyZonotope.monomial_plusE_right, ← sub_eq_add_neg]
    -- its value is the centers' difference plus the boxes', in the stored interval
    have hag := ConPolyZono.aux_agree_mem cPZ₁ cPZ₂ he₁ he₂ i
    have hv : (∑ l, toReal (cPZ₁.G l i) * Real.PolyZonotope.monomial cPZ₁.E a₁ l)
        - ∑ l, toReal (cPZ₂.G l i) * Real.PolyZonotope.monomial cPZ₂.E a₂ l
        = toReal (cPZ₂.c i) - toReal (cPZ₁.c i) + (e₂ i - e₁ i) := by
      have h₁ := hy₁ i
      have h₂ := hy₂ i
      have hxi : y₁ i + e₁ i = y₂ i + e₂ i := by
        rw [← Pi.add_apply y₁ e₁ i, ← Pi.add_apply y₂ e₂ i, hx₁', hx₂']
      rw [hz₁] at h₁
      rw [hz₂] at h₂
      linarith
    rw [hrow, hv]
    exact ConPolyZono.abs_sub_le_subUp hag.1 hag.2
  -- and the point, where only the first set's generator block is nonzero
  · rw [hy₁ i, hz₁]
    show _ = toReal (cPZ₁.c i) + (∑ l : Fin (cPZ₁.h + cPZ₂.h),
        toReal (Fin.append cPZ₁.G (fun _ _ => zero) l i)
          * Real.PolyZonotope.monomial (Real.PolyZonotope.plusE cPZ₁.E cPZ₂.E)
            (Fin.append a₁ a₂) l) + ∑ j : Fin 0, toReal ((Fin.elim0 j : Vec 𝕋 n) i) * Fin.elim0 j
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, toReal_zero, zero_mul, Finset.sum_const_zero,
      add_zero, Real.PolyZonotope.monomial_plusE_left, Finset.univ_eq_empty,
      Finset.sum_empty]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
