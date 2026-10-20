module

public import CORALean.ContSet.PolyZonotope.Float.Operations.RepresentsaPoint
public import CORALean.ContSet.PolyZonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.PolyZonotope.Real.Theorems.RepresentsaPointConstruct
public import CORALean.ContSet.Interval.Float.Theorems.RepresentsaPointSound

@[expose] public section

/-!
# `PolyZonotope.representsa_point` is sound

`representsa_point = true` means the set is a single point (a `true` only, a `false` decides
nothing). The exact layer's `construct_eq_of_representsa_point` carries the nominal part, the
interval's soundness the box.

## Inputs
* `pZ` – polynomial zonotope

## Hypotheses
* `h` – the test returns true

## Conclusion
* the set is a single point
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.representsa_point_sound {pZ : PolyZonotope (Vec 𝕋 n)}
    (h : pZ.representsa_point = true) : -- --- CONCL ---
    ∃ v, pZ.construct = {v} := by -- --- PROOF ---
  simp only [PolyZonotope.representsa_point, Bool.and_eq_true, List.all_eq_true,
    List.mem_finRange, forall_const] at h
  obtain ⟨⟨hG, hGI⟩, hE⟩ := h
  have hz : ∀ x : 𝕋, FloatOps.le x zero = true → FloatOps.le zero x = true → toReal x = 0 :=
    fun x h₁ h₂ => le_antisymm (by simpa [toReal_zero] using toReal_le_of_le h₁)
      (by simpa [toReal_zero] using toReal_le_of_le h₂)
  obtain ⟨v, hv⟩ := Interval.representsa_point_sound hE
  refine ⟨toRealVec pZ.c + v, ?_⟩
  have hN : nominalSet pZ = {(nominal pZ).c} :=
    Real.PolyZonotope.construct_eq_of_representsa_point (nominal pZ)
      ⟨fun l => funext fun i => hz _ (hG l i).1 (hG l i).2,
        fun j => funext fun i => hz _ (hGI j i).1 (hGI j i).2⟩
  show nominalSet pZ + pZ.I_error.construct = _
  rw [hN, hv, Set.singleton_add_singleton]
  rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
