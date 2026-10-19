module

public import CORALean.ContSet.ConPolyZono.Real.Operations.ExactPlus
public import CORALean.ContSet.PolyZonotope.Real.Theorems.ExactPlusPoint
public import CORALean.ContSet.Conversion.Real.Operations.ConPolyZono_to_PolyZonotope

@[expose] public section

/-!
# `ConPolyZono.exactPlus` is the sum over shared factors

As for `PolyZonotope.exactPlus_point`, the claim is about the evaluation map and not about the
Minkowski sum: the result's points are the sum of the two sets' points at one shared factor vector
`a` that satisfies the constraints, the independent blocks adding freely. The constraints are the
first operand's. CORA requires the second's to be identical and throws otherwise; that check is
not a hypothesis here, since the statement is exact for the constructed set whatever it is, and
it is what makes the second operand's own points constrained in the same way.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.exactPlus_construct (cPZ₁ cPZ₂ : ConPolyZono α)
    (hp : cPZ₁.p = cPZ₂.p) : -- --- STMT ---
    (cPZ₁.exactPlus cPZ₂ hp).construct
      = {x | ∃ a : Fin cPZ₁.p → ℝ, ∃ β₁ : Fin cPZ₁.qI → ℝ, ∃ β₂ : Fin cPZ₂.qI → ℝ,
          (∀ j, |β₁ j| ≤ 1) ∧ (∀ j, |β₂ j| ≤ 1) ∧ a ∈ cPZ₁.cons.construct
          ∧ x = (cPZ₁.polyZonotope.point a + ∑ j, β₁ j • cPZ₁.GI j)
              + (cPZ₂.polyZonotope.point (fun k => a (Fin.cast hp.symm k))
                + ∑ j, β₂ j • cPZ₂.GI j)} := by -- --- PROOF ---
  ext x
  constructor
  · -- a coefficient vector of the sum splits into the two independent blocks
    rintro ⟨a, β, hβ, hs, rfl⟩
    refine ⟨a, fun j => β (Fin.castAdd cPZ₂.qI j), fun j => β (Fin.natAdd cPZ₁.qI j),
      fun j => hβ _, fun j => hβ _, hs, ?_⟩
    have hpt := PolyZonotope.exactPlus_point cPZ₁.polyZonotope cPZ₂.polyZonotope hp a
    have hsum : ∑ j : Fin (cPZ₁.qI + cPZ₂.qI), β j • (Fin.append cPZ₁.GI cPZ₂.GI) j
        = ∑ j, β (Fin.castAdd cPZ₂.qI j) • cPZ₁.GI j
          + ∑ j, β (Fin.natAdd cPZ₁.qI j) • cPZ₂.GI j := by
      rw [Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right]
      rfl
    -- the dependent points add at the shared factor vector, the independent blocks split
    show (cPZ₁.polyZonotope.exactPlus cPZ₂.polyZonotope hp).point a
        + ∑ j : Fin (cPZ₁.qI + cPZ₂.qI), β j • (Fin.append cPZ₁.GI cPZ₂.GI) j = _
    rw [hpt, hsum, add_add_add_comm]
    rfl
  · -- two independent coefficient vectors are one on the concatenated block
    rintro ⟨a, β₁, β₂, hβ₁, hβ₂, hs, rfl⟩
    refine ⟨a, Fin.append β₁ β₂, ?_, hs, ?_⟩
    · refine Fin.addCases (fun l => ?_) fun l => ?_
      · rw [Fin.append_left]; exact hβ₁ l
      · rw [Fin.append_right]; exact hβ₂ l
    · have hpt := PolyZonotope.exactPlus_point cPZ₁.polyZonotope cPZ₂.polyZonotope hp a
      have hsum : ∑ j : Fin (cPZ₁.qI + cPZ₂.qI),
          (Fin.append β₁ β₂) j • (Fin.append cPZ₁.GI cPZ₂.GI) j
          = ∑ j, β₁ j • cPZ₁.GI j + ∑ j, β₂ j • cPZ₂.GI j := by
        rw [Fin.sum_univ_add]
        simp only [Fin.append_left, Fin.append_right]
      show _ = (cPZ₁.polyZonotope.exactPlus cPZ₂.polyZonotope hp).point a
        + ∑ j : Fin (cPZ₁.qI + cPZ₂.qI), (Fin.append β₁ β₂) j • (Fin.append cPZ₁.GI cPZ₂.GI) j
      rw [hpt, hsum]
      rw [add_add_add_comm]; rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
