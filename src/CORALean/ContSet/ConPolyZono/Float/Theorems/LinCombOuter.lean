import CORALean.ContSet.ConPolyZono.Float.Theorems.MemNominalSet
import CORALean.ContSet.ConPolyZono.Float.Theorems.SatisfiesLinCombIff
import CORALean.ContSet.InflatedContSet.Theorems.LinCombSubset
import CORALean.ContSet.Interval.Float.Theorems.LinCombOuter
import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
import CORALean.ContSet.PolyZonotope.Float.Theorems.LinCombNominalAt

/-!
# `ConPolyZono.linComb` contains every segment between the two sets

`InflatedContSet.linComb_subset` again, and the nominal obligation is the
polynomial zonotope's at named factors (`PolyZonotope.linComb_nominal_at`): the
segment point lands on the nominal point at `[a₁; a₂; 2λ-1]`, up to the
rounding the box holds. What a constrained set adds is that those factors satisfy
the carried constraints, and they do: `satisfies_linComb_iff` reads each system
on the factors its operand came with, which are `a₁` and `a₂` themselves.

Outer only, as over ℝ: the independent coefficients cannot be tied to `λ`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

theorem ConPolyZono.aux_linComb_nominal (cPZ₁ cPZ₂ : ConPolyZono 𝕋 (Vec 𝕋 n)) :
    segments (nominalSet cPZ₁) (nominalSet cPZ₂) ⊆
      nominalSet (cPZ₁.linComb cPZ₂)
        + ((PolyZonotope.midpointResidual cPZ₁.c cPZ₂.c).construct
            + ((PolyZonotope.halfDiffError cPZ₁.c cPZ₂.c).construct
                + (Zonotope.generatorError
                    (PolyZonotope.linCombGIDiff cPZ₁.polyZonotope
                      cPZ₂.polyZonotope)).construct)) := by -- --- PROOF ---
  rintro _ ⟨y₁, hy₁', y₂, hy₂', lam, ⟨hl0, hl1⟩, rfl⟩
  obtain ⟨a₁, β₁, ha₁, hβ₁, hs₁, hy₁⟩ := ConPolyZono.mem_nominalSet_iff.mp hy₁'
  obtain ⟨a₂, β₂, ha₂, hβ₂, hs₂, hy₂⟩ := ConPolyZono.mem_nominalSet_iff.mp hy₂'
  obtain ⟨β, hβ, _, rfl, e, he, hx⟩ :=
    PolyZonotope.linComb_nominal_at cPZ₁.polyZonotope cPZ₂.polyZonotope
      (a₁ := a₁) (a₂ := a₂) hβ₁ hβ₂ hl0 hl1
  have hA₁ : (fun k => Fin.append (Fin.append a₁ a₂) (fun _ : Fin 1 => 2 * lam - 1)
      (Fin.castAdd 1 (Fin.castAdd cPZ₂.p k))) = a₁ :=
    funext fun k => by rw [Fin.append_left, Fin.append_left]
  have hA₂ : (fun k => Fin.append (Fin.append a₁ a₂) (fun _ : Fin 1 => 2 * lam - 1)
      (Fin.castAdd 1 (Fin.natAdd cPZ₁.p k))) = a₂ :=
    funext fun k => by rw [Fin.append_left, Fin.append_right]
  -- the nominal point at `[a₁; a₂; 2λ-1]`
  refine ⟨_, ConPolyZono.mem_nominalSet_iff.mpr
    ⟨Fin.append (Fin.append a₁ a₂) (fun _ : Fin 1 => 2 * lam - 1), β, ?_, hβ, ?_,
      fun _ => rfl⟩, e, he, ?_⟩
  -- every factor admissible, the fresh one because `2λ-1` lies in `[-1,1]`
  · refine Fin.addCases ?_ ?_
    · refine Fin.addCases ?_ ?_
      · intro k
        simpa using ha₁ k
      · intro k
        simpa using ha₂ k
    · intro _
      simp only [Fin.append_right]
      rw [abs_le]
      constructor <;> linarith
  -- each constraint system read on the factors its operand came with
  · refine (ConPolyZono.satisfies_linComb_iff cPZ₁ cPZ₂ _).mpr ⟨?_, ?_⟩
    · rw [hA₁]
      exact hs₁
    · rw [hA₂]
      exact hs₂
  · rw [funext hy₁, funext hy₂]
    exact hx

/-- The box absorbs the two incoming boxes, both centre roundings and the
independent block's, exactly as for the unconstrained set. -/
theorem ConPolyZono.aux_linComb_error (cPZ₁ cPZ₂ : ConPolyZono 𝕋 (Vec 𝕋 n)) :
    segments cPZ₁.err.construct cPZ₂.err.construct
        + ((PolyZonotope.midpointResidual cPZ₁.c cPZ₂.c).construct
            + ((PolyZonotope.halfDiffError cPZ₁.c cPZ₂.c).construct
                + (Zonotope.generatorError
                    (PolyZonotope.linCombGIDiff cPZ₁.polyZonotope
                      cPZ₂.polyZonotope)).construct))
      ⊆ (cPZ₁.linComb cPZ₂).err.construct :=
  subset_trans
    (Set.add_subset_add (Interval.linComb_outer cPZ₁.err cPZ₂.err)
      (subset_trans (Set.add_subset_add_left (Interval.plus_outer _ _))
        (Interval.plus_outer _ _)))
    (Interval.plus_outer _ _)


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.linComb_outer (cPZ₁ cPZ₂ : ConPolyZono 𝕋 (Vec 𝕋 n)) :
    segments cPZ₁.construct cPZ₂.construct ⊆ (cPZ₁.linComb cPZ₂).construct :=
  InflatedContSet.linComb_subset (ConPolyZono.aux_linComb_nominal cPZ₁ cPZ₂)
    (ConPolyZono.aux_linComb_error cPZ₁ cPZ₂)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
