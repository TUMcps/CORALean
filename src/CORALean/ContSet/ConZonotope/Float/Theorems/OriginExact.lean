module

public import CORALean.ContSet.ConZonotope.Float.Operations.Origin
public import CORALean.ContSet.HPolytope.Float.Operations.Basic
public import CORALean.ContSet.Interval.Float.Theorems.OriginExact

@[expose] public section

/-!
# `ConZonotope.origin` is exactly the origin

`zero` reads as `0` and no constraint restricts the empty coefficient family, so
the nominal part is `{0}`; the error box is the origin box.

## Inputs
* `n` – dimension

## Hypotheses
* none

## Conclusion
* the origin constrained zonotope denotes the origin point
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.origin_exact (n : ℕ) : -- --- CONCL ---
    (ConZonotope.origin n : ConZonotope 𝕋 (Vec 𝕋 n)).construct = {0} := by -- --- PROOF ---
  -- the stored zeros read as ℝ's, so the nominal part is the exact layer's point
  have hc : toRealVec (fun _ : Fin n => (zero : 𝕋)) = 0 := funext fun _ => toReal_zero
  -- the nominal part denotes `{0}`, and so does the box
  have hN : InflatedContSet.nominalSet (ConZonotope.origin n : ConZonotope 𝕋 (Vec 𝕋 n)) = {0} := by
    ext x
    constructor
    -- no generator, so the point is the center
    · rintro ⟨β, -, -, h⟩
      haveI : IsEmpty (Fin (InflatedContSet.nominal
        (ConZonotope.origin n : ConZonotope 𝕋 (Vec 𝕋 n))).h) :=
        inferInstanceAs (IsEmpty (Fin 0))
      have h2 := h
      simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero] at h2
      have h' : x = toRealVec (fun _ : Fin n => (zero : 𝕋)) := h2
      rw [h', hc]
      rfl
    · intro hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      refine ⟨fun j => j.elim0, fun j => j.elim0,
        (HPolytope.mem_nominal_of_origin rfl).mp (HPolytope.mem_fullspace _), ?_⟩
      show (0 : Vec ℝ n) = toRealVec (fun _ : Fin n => (zero : 𝕋)) + ∑ j : Fin 0, _
      simp [hc]
  have hE : (ConZonotope.origin n : ConZonotope 𝕋 (Vec 𝕋 n)).I_error.construct = {0} :=
    Interval.origin_exact n
  -- the sum of the two singletons
  show InflatedContSet.nominalSet (ConZonotope.origin n : ConZonotope 𝕋 (Vec 𝕋 n))
      + (ConZonotope.origin n : ConZonotope 𝕋 (Vec 𝕋 n)).I_error.construct = _
  rw [hN, hE, Set.singleton_add_singleton, add_zero]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
