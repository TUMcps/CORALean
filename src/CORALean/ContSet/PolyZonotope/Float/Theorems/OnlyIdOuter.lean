module

public import CORALean.ContSet.PolyZonotope.Float.Operations.OnlyId
public import CORALean.ContSet.PolyZonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.PolyZonotope.Real.Theorems.OnlyIdPoint
public import CORALean.ContSet.PolyZonotope.Float.Theorems.OnlyIdPoint
public import CORALean.ContSet.Interval.Float.Theorems.OriginExact

@[expose] public section

/-!
# `PolyZonotope.onlyId` encloses the original

The original lies in the Minkowski sum of the two results, the error box being the second's.
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

/-- Outer: the original lies in the sum of the two parts. -/
theorem PolyZonotope.onlyId_outer (pZ : PolyZonotope (Vec 𝕋 n)) (S : Finset (Fin pZ.p)) :
    pZ.construct ⊆ (pZ.onlyId S).1.construct + (pZ.onlyId S).2.construct := by -- --- PROOF ---
  rintro _ ⟨_, ⟨a, β, ha, hβ, rfl⟩, e, he, rfl⟩
  have hpt := PolyZonotope.onlyId_point pZ S a
  have h0 : (0 : Vec ℝ n) ∈ (pZ.onlyId S).1.I_error.construct := by
    show (0 : Vec ℝ n) ∈ (Interval.origin n : Interval (Vec 𝕋 n)).construct
    rw [Interval.origin_exact]; rfl
  -- the part of the first piece at the factors of `S`, and the remainder's point
  set y₁ := (nominal (pZ.onlyId S).1).point (fun k' => a (S.orderIsoOfFin rfl k').1) with hy₁
  set y₂ := (nominal (pZ.onlyId S).2).point a with hy₂
  have hq : (nominal (pZ.onlyId S).1).q = 0 := rfl
  -- the first piece has no independent generators, so its point is a point of the set
  have hmem : y₁ ∈ nominalSet (pZ.onlyId S).1 := by
    show y₁ ∈ (nominal (pZ.onlyId S).1).construct
    refine ⟨fun k' => a (S.orderIsoOfFin rfl k').1, fun j => (j : Fin 0).elim0, fun k => ha _,
      fun j => (j : Fin 0).elim0, ?_⟩
    have : ∑ j : Fin (nominal (pZ.onlyId S).1).q,
        (fun j : Fin (nominal (pZ.onlyId S).1).q => ((j : Fin 0).elim0 : ℝ)) j •
          (nominal (pZ.onlyId S).1).GI j = (0 : Vec ℝ n) :=
      Finset.sum_eq_zero fun j _ => (j : Fin 0).elim0
    rw [this, add_zero]
    exact hy₁
  refine ⟨y₁ + 0, ⟨y₁, hmem, 0, h0, rfl⟩,
    y₂ + ∑ j, β j • (nominal pZ).GI j + e,
    ⟨y₂ + ∑ j, β j • (nominal pZ).GI j, ⟨a, β, ha, hβ, rfl⟩, e, he, rfl⟩, ?_⟩
  calc y₁ + 0 + (y₂ + ∑ j, β j • (nominal pZ).GI j + e)
      = (y₁ + y₂) + ∑ j, β j • (nominal pZ).GI j + e := by abel
    _ = (nominal pZ).point a + ∑ j, β j • (nominal pZ).GI j + e := by rw [hpt]; rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
