module

public import CORALean.ContSet.ConPolyZono.Real.Operations.Intersection
public import CORALean.ContSet.ConPolyZono.Real.Operations.IntersectionDep
public import CORALean.ContSet.Interval.Real.Operations.Point
public import CORALean.ContSet.Interval.Real.Theorems.Basic
public import CORALean.ContSet.Interval.Real.Theorems.MemAppendIff
public import CORALean.ContSet.PolyLevelSet.Real.Theorems.MemAndRowsIff
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Tactic.Abel
public import CORALean.ContSet.PolyLevelSet.Real.Theorems.MemCartProdIff
public import CORALean.ContSet.PolyLevelSet.Real.Theorems.MemConstructIffOfEq
public import CORALean.ContSet.PolyZonotope.Real.Theorems.MonomialPlusELeft
public import CORALean.ContSet.PolyZonotope.Real.Theorems.MonomialPlusERight
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-!
# `intersectionDep` is exact

The proof turns on the agreement rows being constraints of the same kind the
representation already carries: their coefficients are the generator monomials,
so `appendE` puts their exponent columns beside the constraint ones over one
shared factor vector, and a point of the result reproduces a point of `cPZ₂`.

`hq₁` and `hq₂` say the independent blocks are empty. An independent coefficient
answers to no constraint and could move the two points apart, so the rows cannot
be written until they are gone.

## Inputs
* `cPZ₁` – first operand
* `cPZ₂` – second operand

## Hypotheses
* `hq₁` – first has no independent generators
* `hq₂` – second has no independent generators

## Conclusion
* the intersection is the result's set
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Only the first generator block survives. The second is kept at zero rather
than dropped, so that the agreement rows have columns in which to read it. -/
private theorem ConPolyZono.aux_value_intersectionDep (cPZ₁ cPZ₂ : ConPolyZono (Vec ℝ n))
    (a : Fin (cPZ₁.p + cPZ₂.p) → ℝ) : -- --- CONCL ---
    (∑ l : Fin (cPZ₁.h + cPZ₂.h),
        PolyZonotope.monomial (PolyZonotope.plusE cPZ₁.E cPZ₂.E) a l
          • Fin.append cPZ₁.G (0 : Fin cPZ₂.h → Vec ℝ n) l)
      = ∑ l, PolyZonotope.monomial cPZ₁.E (fun k => a (Fin.castAdd cPZ₂.p k)) l
          • cPZ₁.G l := by -- --- PROOF ---
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right, Pi.zero_apply, smul_zero,
    Finset.sum_const_zero, add_zero, PolyZonotope.monomial_plusE_left]

/-- What `intersectionDep`'s constraint system says: each set's own constraints, and that
the two points agree coordinate by coordinate. -/
private theorem ConPolyZono.aux_mem_cons_intersectionDep_iff (cPZ₁ cPZ₂ : ConPolyZono (Vec ℝ n))
    (a : Fin (cPZ₁.p + cPZ₂.p) → ℝ) : -- --- CONCL ---
    a ∈ (cPZ₁.intersectionDep cPZ₂).cons.construct ↔
      ((fun k => a (Fin.castAdd cPZ₂.p k)) ∈ cPZ₁.cons.construct
        ∧ (fun k => a (Fin.natAdd cPZ₁.p k)) ∈ cPZ₂.cons.construct)
      ∧ ∀ i, (∑ l, cPZ₁.G l i
              * PolyZonotope.monomial cPZ₁.E (fun k => a (Fin.castAdd cPZ₂.p k)) l)
            - ∑ l, cPZ₂.G l i
              * PolyZonotope.monomial cPZ₂.E (fun k => a (Fin.natAdd cPZ₁.p k)) l
          = cPZ₂.c i - cPZ₁.c i := by -- --- PROOF ---
  show a ∈ ((cPZ₁.cons.cartProd cPZ₂.cons).andRows (ConPolyZono.agreeCons cPZ₁ cPZ₂)).construct
    ↔ _
  rw [PolyLevelSet.mem_andRows_iff, PolyLevelSet.mem_cartProd_iff]
  -- an agreement row reads each side's monomials off its own factors
  refine and_congr Iff.rfl (forall_congr' fun i => ?_)
  show (∑ l, Fin.append (fun l => cPZ₁.G l i) (fun l => -cPZ₂.G l i) l
      * PolyZonotope.monomial (PolyZonotope.plusE cPZ₁.E cPZ₂.E) a l)
      - (cPZ₂.c i - cPZ₁.c i) = 0 ↔ _
  rw [sub_eq_zero]
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right, PolyZonotope.monomial_plusE_left,
    PolyZonotope.monomial_plusE_right, neg_mul, Finset.sum_neg_distrib, ← sub_eq_add_neg]


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.intersectionDep_exact (cPZ₁ cPZ₂ : ConPolyZono (Vec ℝ n))
    (hq₁ : cPZ₁.qI = 0) (hq₂ : cPZ₂.qI = 0) : -- --- CONCL ---
    cPZ₁.construct ∩ cPZ₂.construct = (cPZ₁.intersectionDep cPZ₂).construct := by -- --- PROOF ---
  have hz₁ : ∀ b : Fin cPZ₁.qI → ℝ, ∑ j, b j • cPZ₁.GI j = 0 :=
    fun b => Finset.sum_eq_zero fun j _ => absurd j.isLt (by omega)
  have hz₂ : ∀ b : Fin cPZ₂.qI → ℝ, ∑ j, b j • cPZ₂.GI j = 0 :=
    fun b => Finset.sum_eq_zero fun j _ => absurd j.isLt (by omega)
  apply Set.eq_of_subset_of_subset
  · rintro x ⟨⟨a₁, β₁, -, hs₁, hx₁⟩, ⟨a₂, β₂, -, hs₂, hx₂⟩⟩
    have hA₁ : (fun k => Fin.append a₁ a₂ (Fin.castAdd cPZ₂.p k)) = a₁ :=
      funext fun k => Fin.append_left a₁ a₂ k
    have hA₂ : (fun k => Fin.append a₁ a₂ (Fin.natAdd cPZ₁.p k)) = a₂ :=
      funext fun k => Fin.append_right a₁ a₂ k
    have e₁ : ∀ i, x i
        = cPZ₁.c i + ∑ l, cPZ₁.G l i * PolyZonotope.monomial cPZ₁.E a₁ l := by
      intro i
      rw [hx₁, hz₁ β₁, add_zero, Entrywise.add_sum_smul_apply]
    have e₂ : ∀ i, x i
        = cPZ₂.c i + ∑ l, cPZ₂.G l i * PolyZonotope.monomial cPZ₂.E a₂ l := by
      intro i
      rw [hx₂, hz₂ β₂, add_zero, Entrywise.add_sum_smul_apply]
    -- the witness: the two factor vectors appended, with no independent coefficients left
    refine ⟨Fin.append a₁ a₂, fun _ => 0, fun j => j.elim0, ?_, ?_⟩
    · refine (ConPolyZono.aux_mem_cons_intersectionDep_iff cPZ₁ cPZ₂ _).mpr ⟨⟨?_, ?_⟩, fun i => ?_⟩
      · rw [hA₁]
        exact hs₁
      · rw [hA₂]
        exact hs₂
      · rw [hA₁, hA₂]
        linarith [e₁ i, e₂ i]
    -- and the value, where only `cPZ₁`'s half of the generator block is nonzero
    · show x = cPZ₁.c + (∑ l : Fin (cPZ₁.h + cPZ₂.h),
              PolyZonotope.monomial (PolyZonotope.plusE cPZ₁.E cPZ₂.E) (Fin.append a₁ a₂) l
                • Fin.append cPZ₁.G (0 : Fin cPZ₂.h → Vec ℝ n) l)
            + ∑ j : Fin 0, (0:ℝ) • (Fin.elim0 j : Vec ℝ n)
      rw [ConPolyZono.aux_value_intersectionDep, hA₁, hx₁, hz₁ β₁]
      simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero]
  · rintro x ⟨a, β, -, hsat, hx⟩
    obtain ⟨⟨hs₁, hs₂⟩,
        hagree⟩ := (ConPolyZono.aux_mem_cons_intersectionDep_iff cPZ₁ cPZ₂ a).mp hsat
    have hxv : x = cPZ₁.c
        + ∑ l, PolyZonotope.monomial cPZ₁.E (fun k => a (Fin.castAdd cPZ₂.p k)) l • cPZ₁.G l := by
      rw [hx]
      show cPZ₁.c + (∑ l : Fin (cPZ₁.h + cPZ₂.h),
              PolyZonotope.monomial (PolyZonotope.plusE cPZ₁.E cPZ₂.E) a l
                • Fin.append cPZ₁.G (0 : Fin cPZ₂.h → Vec ℝ n) l)
            + (∑ j : Fin 0, β j • (Fin.elim0 j : Vec ℝ n))
          = cPZ₁.c
            + ∑ l, PolyZonotope.monomial cPZ₁.E (fun k => a (Fin.castAdd cPZ₂.p k)) l • cPZ₁.G l
      rw [ConPolyZono.aux_value_intersectionDep]
      simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero]
    -- the agreement rows say `x` is also `cPZ₂`'s point at the right half of `a`
    have hxv₂ : x = cPZ₂.c
        + ∑ l, PolyZonotope.monomial cPZ₂.E (fun k => a (Fin.natAdd cPZ₁.p k)) l • cPZ₂.G l := by
      funext i
      rw [Entrywise.add_sum_smul_apply]
      have h₁ : x i = cPZ₁.c i + ∑ l, cPZ₁.G l i
          * PolyZonotope.monomial cPZ₁.E (fun k => a (Fin.castAdd cPZ₂.p k)) l := by
        rw [hxv, Entrywise.add_sum_smul_apply]
      linarith [hagree i]
    refine ⟨⟨fun k => a (Fin.castAdd cPZ₂.p k), fun _ => 0,
        fun _ => by norm_num, hs₁, ?_⟩, ⟨fun k => a (Fin.natAdd cPZ₁.p k), fun _ => 0,
        fun _ => by norm_num, hs₂, ?_⟩⟩
    · rw [hxv]
      simp only [zero_smul, Finset.sum_const_zero, add_zero]
    · rw [hxv₂]
      simp only [zero_smul, Finset.sum_const_zero, add_zero]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
