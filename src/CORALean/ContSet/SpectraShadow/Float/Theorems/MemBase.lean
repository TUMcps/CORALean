module

public import CORALean.ContSet.SpectraShadow.Float.Operations.Base
public import CORALean.ContSet.SpectraShadow.Float.Theorems.MemNominalSet
public import CORALean.ContSet.Interval.Float.Theorems.OriginExact

@[expose] public section

/-!
# The base spectrahedron holds every feasible `β`

At `β` the base shadow's inequality is the shadow's own, its point is `β` (identity generators,
center `0`), and its box is the origin.

## Inputs
* `S` – spectrahedral shadow
* `β` – vector of length `S.m`

## Hypotheses
* `hP` – `(toRealMat S.A₀ + ∑ i, β i • toRealMat (S.A i))` is positive semidefinite

## Conclusion
* the base spectrahedron holds every feasible `β`
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem SpectraShadow.mem_base {S : SpectraShadow 𝕋 (Vec 𝕋 n)} {β : Vec ℝ S.m}
    (hP : (toRealMat S.A₀ + ∑ i, β i • toRealMat (S.A i)).PosSemidef) : -- --- CONCL ---
    β ∈ S.base.construct := by -- --- PROOF ---
  refine ⟨β, SpectraShadow.mem_nominalSet_iff.mpr ⟨β, hP, fun r => ?_⟩, 0, ?_, add_zero β⟩
  · -- the identity generators pick `β r`
    show β r = toReal (zero : 𝕋) + ∑ j, toReal (if r = j then (one : 𝕋) else zero) * β j
    have hunit : ∀ j, toReal (if r = j then (one : 𝕋) else zero) = if r = j then 1 else 0 :=
      fun j => by split_ifs <;> simp [toReal_one, toReal_zero]
    simp [hunit, toReal_zero]
  · show (0 : Vec ℝ S.m) ∈ (Interval.origin S.m : Interval (Vec 𝕋 S.m)).construct
    rw [Interval.origin_exact]
    rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
