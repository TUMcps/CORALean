module

public import CORALean.ContSet.PolyZonotope.Float.Operations.PartZonotope
public import CORALean.ContSet.PolyZonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.PolyZonotope.Real.Theorems.PartZonotopeOuter

@[expose] public section

/-!
# The nominal part of `partZonotope` is the exact layer's

Halving is exact and the rest of the construction is over the exponent matrix, so the nominal part
of the float `partZonotope` is the exact layer's `partZonotope` of the original's nominal part.

## Inputs
* `pZ` – polynomial zonotope
* `V` – selected factors

## Hypotheses
* none

## Conclusion
* nominal set equals the exact layer's one
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- An appended pair of blocks, read as reals and at one coordinate. -/
theorem PolyZonotope.aux_toReal_append {m : ℕ} {r : ℕ} (u v : Fin m → 𝕋) (U V : Fin m → Vec ℝ r)
    (i : Fin r) (hu : ∀ j, toReal (u j) = U j i) (hv : ∀ j, toReal (v j) = V j i)
    (l : Fin (m + m)) : toReal (Fin.append u v l) = (Fin.append U V l) i := by
  refine Fin.addCases (fun j => ?_) (fun j => ?_) l
  · rw [Fin.append_left, Fin.append_left]; exact hu j
  · rw [Fin.append_right, Fin.append_right]; exact hv j


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.partZonotope_nominal (pZ : PolyZonotope (Vec 𝕋 n))
    (V : Finset (Fin pZ.p)) : -- --- CONCL ---
    nominal (pZ.partZonotope V) =
      Real.PolyZonotope.partZonotope (nominal pZ) V := by -- --- PROOF ---
  unfold PolyZonotope.partZonotope Real.PolyZonotope.partZonotope
  change Real.PolyZonotope.mk _ _ _ _ _ _ _ = Real.PolyZonotope.mk _ _ _ _ _ _ _
  congr 1
  -- the generator blocks agree entry by entry: halved when the pattern is even and not zero
  funext l i
  refine PolyZonotope.aux_toReal_append (𝕋 := 𝕋)
    (fun j : Fin pZ.h =>
      if decide ((∀ k ∈ V, pZ.E k j % 2 = 0) ∧ ¬ ∀ k ∈ V, pZ.E k j = 0) = true
        then half (pZ.G j i) else pZ.G j i)
    (fun j : Fin pZ.h =>
      if decide ((∀ k ∈ V, pZ.E k j % 2 = 0) ∧ ¬ ∀ k ∈ V, pZ.E k j = 0) = true
        then half (pZ.G j i) else zero)
    (fun j : Fin pZ.h => if (∀ k ∈ V, pZ.E k j % 2 = 0) ∧ ¬ ∀ k ∈ V, pZ.E k j = 0 then
      (1 / 2 : ℝ) • (nominal pZ).G j else (nominal pZ).G j)
    (fun j : Fin pZ.h => if (∀ k ∈ V, pZ.E k j % 2 = 0) ∧ ¬ ∀ k ∈ V, pZ.E k j = 0 then
      (1 / 2 : ℝ) • (nominal pZ).G j else 0) i (fun j => ?_) (fun j => ?_) l
  · by_cases hP : (∀ k ∈ V, pZ.E k j % 2 = 0) ∧ ¬ ∀ k ∈ V, pZ.E k j = 0
    · rw [if_pos (decide_eq_true hP), if_pos hP, toReal_half]
      simp only [nominal, Pi.smul_apply, smul_eq_mul, RealImage.realImage, toRealVec]
      ring
    · rw [if_neg (by simpa using hP), if_neg hP]
      rfl
  -- the second block holds the halves alone, and zero for the other columns
  · by_cases hP : (∀ k ∈ V, pZ.E k j % 2 = 0) ∧ ¬ ∀ k ∈ V, pZ.E k j = 0
    · rw [if_pos (decide_eq_true hP), if_pos hP, toReal_half]
      simp only [nominal, Pi.smul_apply, smul_eq_mul, RealImage.realImage, toRealVec]
      ring
    · rw [if_neg (by simpa using hP), if_neg hP, toReal_zero]
      rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
