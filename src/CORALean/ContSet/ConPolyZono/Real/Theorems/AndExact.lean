import CORALean.ContSet.ConPolyZono.Real.Operations.And
import CORALean.ContSet.ConPolyZono.Real.Theorems.DependentExact

/-!
# `ConPolyZono.and` is exactly the intersection

The claim the representation exists for, and the one no convex representation
here can make without giving something away: two constrained polynomial
zonotopes intersect to a constrained polynomial zonotope, exactly.

What the proof turns on is that the agreement rows are constraints of the very
same kind the representation already carries. Their coefficients are the
generator monomials, so `appendE` can put the generator exponent columns beside
the constraint ones over one shared factor vector, and a point of the result is
then a point of `C₁` whose factors are forced to reproduce a point of `C₂`.
Membership in both is exactly that, in both directions.

The independent generators are handled before the rows are written, not by them:
`and` intersects the two `dependent` sets. An independent coefficient answers to
no constraint, so it could move the two points apart with nothing in the system
to forbid it — `andDep` is sound only where both independent blocks are empty,
which is what `hq₁` and `hq₂` say, and `dependent_exact` is what makes that
costless.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

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

theorem ConPolyZono.andDep_exact (C₁ C₂ : ConPolyZono (Vec ℝ n))
    (hq₁ : C₁.q = 0) (hq₂ : C₂.q = 0) :
    C₁.construct ∩ C₂.construct = (C₁.andDep C₂).construct := by
  have hz₁ : ∀ b : Fin C₁.q → ℝ, ∑ j, b j • C₁.GI j = 0 :=
    fun b => Finset.sum_eq_zero fun j _ => absurd j.isLt (by omega)
  have hz₂ : ∀ b : Fin C₂.q → ℝ, ∑ j, b j • C₂.GI j = 0 :=
    fun b => Finset.sum_eq_zero fun j _ => absurd j.isLt (by omega)
  apply Set.eq_of_subset_of_subset
  · rintro x ⟨⟨a₁, β₁, ha₁, _, hs₁, hx₁⟩, a₂, β₂, ha₂, _, hs₂, hx₂⟩
    have hA₁ : (fun k => Fin.append a₁ a₂ (Fin.castAdd C₂.p k)) = a₁ :=
      funext fun k => Fin.append_left a₁ a₂ k
    have hA₂ : (fun k => Fin.append a₁ a₂ (Fin.natAdd C₁.p k)) = a₂ :=
      funext fun k => Fin.append_right a₁ a₂ k
    have e₁ : ∀ i, x i
        = C₁.c i + ∑ l, C₁.G l i * PolyZonotope.monomial C₁.E a₁ l := by
      intro i
      rw [hx₁, hz₁ β₁, add_zero, Entrywise.add_sum_smul_apply]
    have e₂ : ∀ i, x i
        = C₂.c i + ∑ l, C₂.G l i * PolyZonotope.monomial C₂.E a₂ l := by
      intro i
      rw [hx₂, hz₂ β₂, add_zero, Entrywise.add_sum_smul_apply]
    refine ⟨Fin.append a₁ a₂, fun _ => 0,
      Fin.addCases (fun k => by simpa using ha₁ k) (fun k => by simpa using ha₂ k),
      fun j => j.elim0, ?_, ?_⟩
    · refine (ConPolyZono.satisfies_andDep_iff C₁ C₂ _).mpr ⟨⟨?_, ?_⟩, fun i => ?_⟩
      · rw [hA₁]
        exact hs₁
      · rw [hA₂]
        exact hs₂
      · rw [hA₁, hA₂]
        have h₁ := e₁ i
        have h₂ := e₂ i
        linarith
    · show x = C₁.c + (∑ l : Fin (C₁.h + C₂.h),
              PolyZonotope.monomial (PolyZonotope.plusE C₁.E C₂.E) (Fin.append a₁ a₂) l
                • Fin.append C₁.G (0 : Fin C₂.h → Vec ℝ n) l)
            + ∑ j : Fin 0, (0:ℝ) • (Fin.elim0 j : Vec ℝ n)
      rw [ConPolyZono.aux_value_andDep, hA₁, hx₁, hz₁ β₁]
      simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero]
  · rintro x ⟨a, β, ha, _, hsat, hx⟩
    obtain ⟨⟨hs₁, hs₂⟩, hagree⟩ := (ConPolyZono.satisfies_andDep_iff C₁ C₂ a).mp hsat
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
    refine ⟨⟨fun k => a (Fin.castAdd C₂.p k), fun _ => 0, fun k => ha _,
        fun _ => by norm_num, hs₁, ?_⟩,
      fun k => a (Fin.natAdd C₁.p k), fun _ => 0, fun k => ha _,
        fun _ => by norm_num, hs₂, ?_⟩
    · rw [hxv]
      simp only [zero_smul, Finset.sum_const_zero, add_zero]
    · simp only [zero_smul, Finset.sum_const_zero, add_zero]
      funext i
      have e₁ : x i = C₁.c i
          + ∑ l, C₁.G l i
              * PolyZonotope.monomial C₁.E (fun k => a (Fin.castAdd C₂.p k)) l := by
        rw [hxv, Entrywise.add_sum_smul_apply]
      have hg := hagree i
      rw [Entrywise.add_sum_smul_apply]
      linarith

theorem ConPolyZono.and_exact (C₁ C₂ : ConPolyZono (Vec ℝ n)) :
    C₁.construct ∩ C₂.construct = (C₁.and C₂).construct := by
  rw [C₁.dependent_exact, C₂.dependent_exact]
  exact ConPolyZono.andDep_exact C₁.dependent C₂.dependent rfl rfl

end CORALean.Real
