module

public import CORALean.ContSet.Zoo.Float.Operations.OfInterval
public import CORALean.ContSet.Conversion.Float.Operations.Basic
public import CORALean.ContSet.Zoo.Float.Theorems.DiagonalBlockSum
public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope

@[expose] public section

/-!
# `Zoo.ofInterval` encloses

The variable `c + r tᵢ` of the box's float zonotope (stored centre `c`, generator `r`) is enclosed
by both members.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

theorem Zoo.aux_ofInterval_poly (Z : Zonotope (Vec 𝕋 n)) (N : ℕ) (i : Fin n) (t : Vec ℝ Z.h) :
    (Z.taylm N i).nominal.poly t = toReal (Z.c i) + ∑ j, toReal (Z.G j i) * t j := by
  simp only [Zonotope.taylm, Taylm.nominal, Real.Taylm.poly, List.map_cons, List.map_ofFn,
    Real.Taylm.polyOf_cons, Real.Taylm.polyOf_ofFn, Real.Taylm.monomial_zero,
    Function.comp_def, Real.Taylm.monomial_single, mul_one]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zoo.ofInterval_encloses (I : Interval (Vec 𝕋 n)) (N : ℕ) (i : Fin n) :
    (Zoo.ofInterval I N i).Encloses
      fun t => toReal (I.center i) + toReal (I.radiusFrom i) * t i := by -- --- PROOF ---
  refine ⟨fun T hT => ?_, fun J hJ t ht => ?_⟩
  · -- the Taylor model: remainder zero, polynomial the variable
    obtain rfl : I.taylm N i = T := Option.some.inj hT
    intro t _
    -- the stored polynomial is the zonotope's centre plus its generators
    have hp : (I.taylm N i).nominal.poly t = toReal (I.zonotope.c i) +
        ∑ j, toReal (I.zonotope.G j i) * t j := Zoo.aux_ofInterval_poly I.zonotope N i t
    have hs : ∑ j, toReal (I.zonotope.G j i) * t j = toReal (I.radiusFrom i) * t i :=
      Zoo.diagonalBlock_sum I i t
    have h0 : toReal (I.zonotope.I_error.inf i) = 0 := toReal_zero
    have h1 : toReal (I.zonotope.I_error.sup i) = 0 := toReal_zero
    have hc : toReal (I.zonotope.c i) = toReal (I.center i) := rfl
    show toReal (I.zonotope.I_error.inf i) ≤ toReal (I.center i) + toReal (I.radiusFrom i) * t i -
        (I.taylm N i).nominal.poly t ∧ toReal (I.center i) + toReal (I.radiusFrom i) * t i -
        (I.taylm N i).nominal.poly t ≤ toReal (I.zonotope.I_error.sup i)
    rw [hp, hs, hc, h0, h1]
    constructor <;> linarith
  · -- the interval: `c ± abs r` contains `c + r t` for `|t| ≤ 1`
    obtain rfl : (⟨fun _ => subDown (I.center i) (absolute (I.radiusFrom i)),
        fun _ => addUp (I.center i) (absolute (I.radiusFrom i))⟩ : Interval (Vec 𝕋 1)) = J :=
      Option.some.inj hJ
    have habs : toReal (absolute (I.radiusFrom i)) = |toReal (I.radiusFrom i)| := by
      rw [absolute, toReal_maximum, toReal_neg, abs_eq_max_neg]
    have h1 := abs_le.1 (ht i)
    have hlo := subDown_le_sub (I.center i) (absolute (I.radiusFrom i))
    have hhi := add_le_addUp (I.center i) (absolute (I.radiusFrom i))
    rw [habs] at hlo hhi
    have hr : |toReal (I.radiusFrom i)| * (-1) ≤ toReal (I.radiusFrom i) * t i ∧
        toReal (I.radiusFrom i) * t i ≤ |toReal (I.radiusFrom i)| * 1 := by
      have ha := abs_nonneg (toReal (I.radiusFrom i))
      constructor <;> cases abs_cases (toReal (I.radiusFrom i)) <;> nlinarith
    intro k
    constructor
    · show toReal (subDown _ _) ≤ toReal (I.center i) + toReal (I.radiusFrom i) * t i
      linarith [hr.1]
    · show toReal (I.center i) + toReal (I.radiusFrom i) * t i ≤ toReal (addUp _ _)
      linarith [hr.2]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
