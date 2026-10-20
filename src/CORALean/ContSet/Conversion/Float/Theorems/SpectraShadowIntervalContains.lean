module

public import CORALean.ContSet.SpectraShadow.Float.Theorems.DualBoundLe
public import CORALean.ContSet.Interval.Float.Interval
public import CORALean.ContSet.Conversion.Float.Operations.SpectraShadow_to_Interval

@[expose] public section

/-!
# A spectrahedral shadow's interval hull, over a floating-point scalar

CORA's `interval(SpS)`: per coordinate the range of `supportFunc_` along `±eᵢ`, two semidefinite
programs. Their solutions are the caller's: one dual certificate per bound (`Yup i` along `eᵢ`,
`Ylo i` along `-eᵢ`), each checked by `SpectraShadow.dualCertified`, and the box is the bounds
they prove (`SpectraShadow.dualBound`, rounded outward). `none` when a certificate fails. An
enclosure only: the bounds are the solver's, not the support values themselves.

## Inputs
* `S` – spectrahedral shadow
* `Yup` – upper certificate matrices per coordinate
* `Ylo` – lower certificate matrices per coordinate

## Hypotheses
* none

## Conclusion
* shadow is contained in every returned interval
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem SpectraShadow.interval_contains {S : SpectraShadow 𝕋 (Vec 𝕋 n)}
    {Yup Ylo : Fin n → Mat 𝕋 S.k S.k} :
    ∀ I ∈ S.interval Yup Ylo,
      S.construct ⊆ I.construct := by -- --- PROOF ---
  intro I (h : S.interval Yup Ylo = some I)
  simp only [SpectraShadow.interval] at h
  split_ifs at h with hc
  simp only [Option.some.injEq] at h
  subst h
  simp only [List.all_eq_true, List.mem_finRange, Bool.and_eq_true, forall_const] at hc
  intro x hx i
  have hunit : ∀ r : Fin n, toReal (if r = i then (one : 𝕋) else zero) = if r = i then 1 else 0 :=
    fun r => by split_ifs <;> simp [toReal_one, toReal_zero]
  -- the two bounds, along `eᵢ` and `-eᵢ`, are the coordinate's
  have hup := SpectraShadow.dualBound_le (hc i).1 x hx
  have hlo := SpectraShadow.dualBound_le (hc i).2 x hx
  simp only [Pi.neg_apply, toReal_neg', hunit, ite_mul, one_mul, zero_mul, neg_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true] at hup hlo
  simp only [Finset.sum_neg_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true] at hlo
  show toReal (neg _) ≤ x i ∧ x i ≤ toReal _
  rw [toReal_neg]
  constructor <;> linarith

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
