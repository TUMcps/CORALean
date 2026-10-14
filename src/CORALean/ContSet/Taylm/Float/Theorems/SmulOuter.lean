module

public import CORALean.ContSet.Interval.Float.Theorems.MulBetweenCorners
public import CORALean.ContSet.Taylm.Float.Operations.Smul
public import CORALean.ContSet.Taylm.Float.Theorems.AbsPolyOfRoundLe
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfCons
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfNil
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfSmul

@[expose] public section

/-!
# `Taylm.smul` encloses the scaled function

For every factor in `[alo, ahi]`: the remainder by the corner products, the stored
coefficients by `abs_polyOf_round_le`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.smul_outer {alo ahi : 𝕋} {a : ℝ} (ha : toReal alo ≤ a ∧ a ≤ toReal ahi)
    {T : Taylm 𝕋 n} {f : Vec ℝ n → ℝ} (h : T.Encloses f) :
    (T.smul alo ahi).Encloses fun t => a * f t := by -- --- PROOF ---
  intro t ht
  have hr := h t ht
  simp only [Taylm.nominal, Real.Taylm.poly] at hr
  have hm := Interval.mul_between_corners ha.1 ha.2 hr.1 hr.2
  -- the exact scaled coefficients against the stored upper corners
  have hround := Taylm.abs_polyOf_round_le T.terms
    (fun b => Interval.mulLo alo ahi b.1 b.1) (fun b => Interval.mulHi alo ahi b.1 b.1)
    (fun b => a * toReal b.1) (fun b => b.2)
    (fun b _ => Interval.mul_between_corners ha.1 ha.2 (le_refl _) (le_refl _)) ht
  have hex : Real.Taylm.polyOf (T.terms.map fun b => (a * toReal b.1, b.2)) t
      = a * Real.Taylm.polyOf (T.terms.map fun b => (toReal b.1, b.2)) t := by
    rw [← Real.Taylm.polyOf_smul, List.map_map]
    rfl
  rw [hex] at hround
  have := abs_le.1 hround
  have := subDown_le_sub (Interval.mulLo alo ahi T.remInf T.remSup)
    (listSumUp (T.terms.map fun b =>
      subUp (Interval.mulHi alo ahi b.1 b.1) (Interval.mulLo alo ahi b.1 b.1)))
  have := add_le_addUp (Interval.mulHi alo ahi T.remInf T.remSup)
    (listSumUp (T.terms.map fun b =>
      subUp (Interval.mulHi alo ahi b.1 b.1) (Interval.mulLo alo ahi b.1 b.1)))
  simp only [Taylm.smul, Taylm.nominal, Real.Taylm.poly, List.map_map] at *
  simp only [Function.comp_def] at *
  constructor <;> nlinarith [hm.1, hm.2]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
