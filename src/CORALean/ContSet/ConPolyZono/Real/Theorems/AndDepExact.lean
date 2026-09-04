import CORALean.ContSet.ConPolyZono.Real.Operations.And
import CORALean.ContSet.Interval.Real.Operations.Point

/-!
# Intersection up to a tolerance

The proof turns on the agreement rows being constraints of the same kind the
representation already carries: their coefficients are the generator monomials,
so `appendE` puts their exponent columns beside the constraint ones over one
shared factor vector, and a point of the result reproduces a point of `C₂`.

Stated at a tolerance: the second set is met after a translation by `D`, which
the agreement rows carry in their right-hand interval and which a float layer's
error boxes fill. At `D = {0}` it is the intersection, which is what `and_exact`
reads off it.

`hq₁` and `hq₂` say the independent blocks are empty. An independent coefficient
answers to no constraint and could move the two points apart, so the rows cannot
be written until they are gone.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   04-September-2026
-- Last revision: ---

namespace CORALean.Real

open Pointwise

variable {n : ℕ}

/-- Only the first generator block survives. The second is kept at zero rather
than dropped, so that the agreement rows have columns in which to read it. -/
theorem ConPolyZono.aux_value_andDep (C₁ C₂ : ConPolyZono (Vec ℝ n))
    (a : Fin (C₁.p + C₂.p) → ℝ) :
    (∑ l : Fin (C₁.h + C₂.h),
        PolyZonotope.monomial (PolyZonotope.plusE C₁.E C₂.E) a l
          • Fin.append C₁.G (0 : Fin C₂.h → Vec ℝ n) l)
      = ∑ l, PolyZonotope.monomial C₁.E (fun k => a (Fin.castAdd C₂.p k)) l • C₁.G l := by
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right, Pi.zero_apply, smul_zero,
    Finset.sum_const_zero, add_zero, PolyZonotope.monomial_plusE_left]

theorem ConPolyZono.andDep_exact (C₁ C₂ : ConPolyZono (Vec ℝ n)) (D : Interval (Vec ℝ n))
    (hq₁ : C₁.q = 0) (hq₂ : C₂.q = 0) :
    C₁.construct ∩ (C₂.construct + D.construct) = (C₁.andDep C₂ D).construct := by
  have hz₁ : ∀ b : Fin C₁.q → ℝ, ∑ j, b j • C₁.GI j = 0 :=
    fun b => Finset.sum_eq_zero fun j _ => absurd j.isLt (by omega)
  have hz₂ : ∀ b : Fin C₂.q → ℝ, ∑ j, b j • C₂.GI j = 0 :=
    fun b => Finset.sum_eq_zero fun j _ => absurd j.isLt (by omega)
  apply Set.eq_of_subset_of_subset
  · rintro x ⟨⟨a₁, β₁, ha₁, -, hs₁, hx₁⟩, y, ⟨a₂, β₂, ha₂, -, hs₂, hy⟩, d, hd, hyd⟩
    -- set addition leaves a beta redex, which no rewrite sees through
    have hyd' : y + d = x := hyd
    have hxd : ∀ i, x i = y i + d i := fun i => by rw [← hyd', Pi.add_apply]
    have hA₁ : (fun k => Fin.append a₁ a₂ (Fin.castAdd C₂.p k)) = a₁ :=
      funext fun k => Fin.append_left a₁ a₂ k
    have hA₂ : (fun k => Fin.append a₁ a₂ (Fin.natAdd C₁.p k)) = a₂ :=
      funext fun k => Fin.append_right a₁ a₂ k
    have e₁ : ∀ i, x i
        = C₁.c i + ∑ l, C₁.G l i * PolyZonotope.monomial C₁.E a₁ l := by
      intro i
      rw [hx₁, hz₁ β₁, add_zero, Entrywise.add_sum_smul_apply]
    have e₂ : ∀ i, y i
        = C₂.c i + ∑ l, C₂.G l i * PolyZonotope.monomial C₂.E a₂ l := by
      intro i
      rw [hy, hz₂ β₂, add_zero, Entrywise.add_sum_smul_apply]
    -- the witness: the two factor vectors appended, with no independent coefficients left
    refine ⟨Fin.append a₁ a₂, fun _ => 0,
      Fin.addCases (fun k => by simpa using ha₁ k) (fun k => by simpa using ha₂ k),
      fun j => j.elim0, ?_, ?_⟩
    · refine (ConPolyZono.satisfies_andDep_iff C₁ C₂ D _).mpr ⟨⟨?_, ?_⟩, fun i => ?_⟩
      · rw [hA₁]
        exact hs₁
      · rw [hA₂]
        exact hs₂
      · rw [hA₁, hA₂]
        have h₁ := e₁ i
        have h₂ := e₂ i
        have hx := hxd i
        have hdi : D.inf i ≤ d i ∧ d i ≤ D.sup i := hd i
        exact ⟨by linarith [hdi.1], by linarith [hdi.2]⟩
    -- and the value, where only `C₁`'s half of the generator block is nonzero
    · show x = C₁.c + (∑ l : Fin (C₁.h + C₂.h),
              PolyZonotope.monomial (PolyZonotope.plusE C₁.E C₂.E) (Fin.append a₁ a₂) l
                • Fin.append C₁.G (0 : Fin C₂.h → Vec ℝ n) l)
            + ∑ j : Fin 0, (0:ℝ) • (Fin.elim0 j : Vec ℝ n)
      rw [ConPolyZono.aux_value_andDep, hA₁, hx₁, hz₁ β₁]
      simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero]
  · rintro x ⟨a, β, ha, -, hsat, hx⟩
    obtain ⟨⟨hs₁, hs₂⟩, hagree⟩ := (ConPolyZono.satisfies_andDep_iff C₁ C₂ D a).mp hsat
    have hxv : x = C₁.c
        + ∑ l, PolyZonotope.monomial C₁.E (fun k => a (Fin.castAdd C₂.p k)) l • C₁.G l := by
      rw [hx]
      show C₁.c + (∑ l : Fin (C₁.h + C₂.h),
              PolyZonotope.monomial (PolyZonotope.plusE C₁.E C₂.E) a l
                • Fin.append C₁.G (0 : Fin C₂.h → Vec ℝ n) l)
            + (∑ j : Fin 0, β j • (Fin.elim0 j : Vec ℝ n))
          = C₁.c
            + ∑ l, PolyZonotope.monomial C₁.E (fun k => a (Fin.castAdd C₂.p k)) l • C₁.G l
      rw [ConPolyZono.aux_value_andDep]
      simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero]
    -- the point of `C₂` the agreement rows pin `x` to, up to `D`
    obtain ⟨y, hy⟩ : ∃ y : Vec ℝ n, y = C₂.c
        + ∑ l, PolyZonotope.monomial C₂.E (fun k => a (Fin.natAdd C₁.p k)) l • C₂.G l :=
      ⟨_, rfl⟩
    have e₁ : ∀ i, x i = C₁.c i
        + ∑ l, C₁.G l i * PolyZonotope.monomial C₁.E (fun k => a (Fin.castAdd C₂.p k)) l :=
      fun i => by rw [hxv, Entrywise.add_sum_smul_apply]
    have e₂ : ∀ i, y i = C₂.c i
        + ∑ l, C₂.G l i * PolyZonotope.monomial C₂.E (fun k => a (Fin.natAdd C₁.p k)) l :=
      fun i => by rw [hy, Entrywise.add_sum_smul_apply]
    have hx₁ : x ∈ C₁.construct := by
      refine ⟨fun k => a (Fin.castAdd C₂.p k), fun _ => 0, fun k => ha _,
        fun _ => by norm_num, hs₁, ?_⟩
      rw [hxv]
      simp only [zero_smul, Finset.sum_const_zero, add_zero]
    -- and that point lies in `C₂`, its factors being the right half of `a`
    have hy₂ : y ∈ C₂.construct := by
      refine ⟨fun k => a (Fin.natAdd C₁.p k), fun _ => 0, fun k => ha _,
        fun _ => by norm_num, hs₂, ?_⟩
      rw [hy]
      simp only [zero_smul, Finset.sum_const_zero, add_zero]
    have hd : x - y ∈ D.construct := by
      intro i
      have hg := hagree i
      have h₁ := e₁ i
      have h₂ := e₂ i
      show D.inf i ≤ (x - y) i ∧ (x - y) i ≤ D.sup i
      rw [Pi.sub_apply]
      exact ⟨by linarith [hg.2], by linarith [hg.1]⟩
    refine ⟨hx₁, y, hy₂, x - y, hd, ?_⟩
    show y + (x - y) = x
    abel

end CORALean.Real
