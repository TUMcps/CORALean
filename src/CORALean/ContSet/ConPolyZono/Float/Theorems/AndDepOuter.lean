import CORALean.ContSet.ConPolyZono.Float.Theorems.AndD
import CORALean.ContSet.ConPolyZono.Float.Theorems.NominalAndDep
import CORALean.ContSet.ConPolyZono.Real.Theorems.AndExact

/-!
# `andDep` over-approximates the intersection

The exact layer's `andDep_exact` at the tolerance `andD` already covers what
the two error boxes let the nominal points differ by — `aux_mem_andD` is the
fitting — so the rounding of the centres never has to be pushed anywhere.
-/

-- Authors:       Tobias Ladner
-- Written:       03-September-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- What the two error boxes let the two nominal points differ by, and the
tolerance the stored rows amount to covers it. -/
theorem ConPolyZono.aux_mem_andD (C₁ C₂ : ConPolyZono 𝕋 n) {e₁ e₂ : Vec ℝ n}
    (h₁ : e₁ ∈ C₁.err.construct) (h₂ : e₂ ∈ C₂.err.construct) :
    e₂ - e₁ ∈ (ConPolyZono.andD C₁ C₂).construct := by
  intro i
  have hb₁ : toReal (C₁.err.inf i) ≤ e₁ i ∧ e₁ i ≤ toReal (C₁.err.sup i) := h₁ i
  have hb₂ : toReal (C₂.err.inf i) ≤ e₂ i ∧ e₂ i ≤ toReal (C₂.err.sup i) := h₂ i
  show (ConPolyZono.andD C₁ C₂).inf i ≤ (e₂ - e₁) i
    ∧ (e₂ - e₁) i ≤ (ConPolyZono.andD C₁ C₂).sup i
  rw [Pi.sub_apply]
  simp only [ConPolyZono.andD, ConPolyZono.andAgree]
  constructor
  · linarith [addDown_le_add (subDown (C₂.c i) (C₁.c i)) (subDown (C₂.err.inf i) (C₁.err.sup i)),
      subDown_le_sub (C₂.c i) (C₁.c i),
      subDown_le_sub (C₂.err.inf i) (C₁.err.sup i), hb₁.2, hb₂.1]
  · linarith [add_le_addUp (subUp (C₂.c i) (C₁.c i)) (subUp (C₂.err.sup i) (C₁.err.inf i)),
      sub_le_subUp (C₂.c i) (C₁.c i),
      sub_le_subUp (C₂.err.sup i) (C₁.err.inf i), hb₁.1, hb₂.2]


-- =======================================  MAIN THEOREM  ======================================= --

-- the nominal side is the exact layer's intersection, at the tolerance `andD` supplies
theorem ConPolyZono.andDep_outer (C₁ C₂ : ConPolyZono 𝕋 n) (hq₁ : C₁.q = 0)
    (hq₂ : C₂.q = 0) : C₁.construct ∩ C₂.construct ⊆ (C₁.andDep C₂).construct := by
  have hnom : nominalSet (C₁.andDep C₂)
      = nominalSet C₁ ∩ (nominalSet C₂ + (ConPolyZono.andD C₁ C₂).construct) := by
    show Real.ConPolyZono.construct (nominal (C₁.andDep C₂)) = _
    rw [ConPolyZono.nominal_andDep,
      ← Real.ConPolyZono.andDep_exact (nominal C₁) (nominal C₂) _ hq₁ hq₂]
    rfl
  -- one point, two decompositions: the nominal parts differ by exactly `e₂ - e₁`
  rintro x ⟨⟨y₁, hy₁, e₁, he₁, hx₁⟩, y₂, hy₂, e₂, he₂, hx₂⟩
  have hx₁' : y₁ + e₁ = x := hx₁
  have hx₂' : y₂ + e₂ = x := hx₂
  have hy : y₂ + (e₂ - e₁) = y₁ := by
    have h : y₂ + e₂ = y₁ + e₁ := hx₂'.trans hx₁'.symm
    have h' : y₂ + e₂ - e₁ = y₁ := by
      rw [h]
      abel
    calc y₂ + (e₂ - e₁) = y₂ + e₂ - e₁ := by abel
      _ = y₁ := h'
  exact ⟨y₁, hnom ▸ ⟨hy₁, y₂, hy₂, e₂ - e₁,
    ConPolyZono.aux_mem_andD C₁ C₂ he₁ he₂, hy⟩, e₁, he₁, hx₁⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
