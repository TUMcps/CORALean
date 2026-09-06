import CORALean.ContSet.ConPolyZono.Real.Operations.Plus
import CORALean.ContSet.ConPolyZono.Real.Operations.SatisfiesPlusIff

/-!
# `ConPolyZono.plus` is exactly the Minkowski sum

The witnesses are `Fin.append` on the factors and on the independent
coefficients, and the block-diagonal layout is what makes them work twice over:
a generator of one set carries exponent zero on every factor of the other, and
so does every constraint row of one set on every constraint generator of the
other.

Exactness is what the separation buys. Had the two factor sets been identified,
the reverse inclusion would fail — one factor cannot take two values at once —
and had the constraint systems been merged, each set's rows would have
constrained the other's factors.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Pointwise

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

omit [Module ℝ α] in
/-- `Fin.sum_univ_add` at `plus`'s dependent generator count, stated through the
projection because that is the form the goal has and simp will not rewrite a
binder's type. -/
theorem ConPolyZono.aux_sum_univ_plus_h {C₁ C₂ : ConPolyZono α}
    (f : Fin (C₁.h + C₂.h) → α) :
    ∑ i : Fin (C₁.plus C₂).h, f i
      = ∑ i, f (Fin.castAdd C₂.h i) + ∑ i, f (Fin.natAdd C₁.h i) :=
  Fin.sum_univ_add f

omit [Module ℝ α] in
/-- The same at the independent generator count. -/
theorem ConPolyZono.aux_sum_univ_plus_q {C₁ C₂ : ConPolyZono α}
    (f : Fin (C₁.q + C₂.q) → α) :
    ∑ j : Fin (C₁.plus C₂).q, f j
      = ∑ j, f (Fin.castAdd C₂.q j) + ∑ j, f (Fin.natAdd C₁.q j) :=
  Fin.sum_univ_add f


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.plus_exact (C₁ C₂ : ConPolyZono α) :
    C₁.construct + C₂.construct = (C₁.plus C₂).construct := by -- --- PROOF ---
  apply Set.eq_of_subset_of_subset
  · rintro _ ⟨x₁, ⟨a₁, β₁, ha₁, hβ₁, hs₁, rfl⟩, x₂, ⟨a₂, β₂, ha₂, hβ₂, hs₂, rfl⟩, rfl⟩
    have hA₁ : (fun k => Fin.append a₁ a₂ (Fin.castAdd C₂.p k)) = a₁ :=
      funext fun k => Fin.append_left a₁ a₂ k
    have hA₂ : (fun k => Fin.append a₁ a₂ (Fin.natAdd C₁.p k)) = a₂ :=
      funext fun k => Fin.append_right a₁ a₂ k
    -- forward: appended factors and appended coefficients, each read on its own half
    refine ⟨Fin.append a₁ a₂, Fin.append β₁ β₂,
      Fin.addCases (fun k => by simpa using ha₁ k) (fun k => by simpa using ha₂ k),
      Fin.addCases (fun j => by simpa using hβ₁ j) (fun j => by simpa using hβ₂ j),
      ?_, ?_⟩
    · refine (ConPolyZono.satisfies_plus_iff C₁ C₂ _).mpr ⟨?_, ?_⟩
      · rw [hA₁]
        exact hs₁
      · rw [hA₂]
        exact hs₂
    · rw [ConPolyZono.aux_sum_univ_plus_h, ConPolyZono.aux_sum_univ_plus_q]
      simp only [ConPolyZono.plus, PolyZonotope.monomial_plusE_left,
        PolyZonotope.monomial_plusE_right, Fin.append_left, Fin.append_right]
      abel
  -- back: the appended data split again, giving one point of each set
  · rintro x ⟨a, β, ha, hβ, hsat, rfl⟩
    obtain ⟨hs₁, hs₂⟩ := (ConPolyZono.satisfies_plus_iff C₁ C₂ a).mp hsat
    refine ⟨C₁.c
              + ∑ i, PolyZonotope.monomial C₁.E (fun k => a (Fin.castAdd C₂.p k)) i • C₁.G i
              + ∑ j, β (Fin.castAdd C₂.q j) • C₁.GI j,
            ⟨fun k => a (Fin.castAdd C₂.p k), fun j => β (Fin.castAdd C₂.q j),
              fun k => ha _, fun j => hβ _, hs₁, rfl⟩,
            C₂.c
              + ∑ i, PolyZonotope.monomial C₂.E (fun k => a (Fin.natAdd C₁.p k)) i • C₂.G i
              + ∑ j, β (Fin.natAdd C₁.q j) • C₂.GI j,
            ⟨fun k => a (Fin.natAdd C₁.p k), fun j => β (Fin.natAdd C₁.q j),
              fun k => ha _, fun j => hβ _, hs₂, rfl⟩, ?_⟩
    rw [ConPolyZono.aux_sum_univ_plus_h, ConPolyZono.aux_sum_univ_plus_q]
    simp only [ConPolyZono.plus, PolyZonotope.monomial_plusE_left,
      PolyZonotope.monomial_plusE_right, Fin.append_left, Fin.append_right]
    abel

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
