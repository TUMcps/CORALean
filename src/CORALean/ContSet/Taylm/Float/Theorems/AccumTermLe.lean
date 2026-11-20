module

public import CORALean.ContSet.Taylm.Float.Operations.AccumTerm
public import CORALean.ContSet.Taylm.Real.Theorems.AbsMonomialLeOne
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfCons
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfNil

@[expose] public section

/-!
# `Taylm.accumTerm` adds the term up to its bound

## Inputs
* `L` – term list
* `c` – coefficient of the new term
* `e` – exponents of the new term
* `t` – point of the box

## Hypotheses
* `ht` – `t` lies in the box `[-1, 1]ⁿ`

## Conclusion
* the polynomial of the result is that of `L` plus the term, up to the bound returned
-/

-- Authors:       Claude Opus 5.5
-- Written:       20-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A sum stored rounded up, times a number of magnitude at most one, is off by at most the
width of the sum between its roundings. -/
private theorem Taylm.aux_round (u c : 𝕋) {m : ℝ} (hm : |m| ≤ 1) : -- --- CONCL ---
    |(toReal (addUp u c) - (toReal u + toReal c)) * m|
      ≤ toReal (subUp (addUp u c) (addDown u c)) := by -- --- PROOF ---
  have h₁ := add_le_addUp u c
  have h₂ := addDown_le_add u c
  have h₃ := add_le_addUp (addUp u c) (neg (addDown u c))
  rw [toReal_neg] at h₃
  have hd : 0 ≤ toReal (addUp u c) - (toReal u + toReal c) := by linarith
  rw [abs_mul, abs_of_nonneg hd]
  have := mul_le_mul_of_nonneg_left hm hd
  simp only [subUp]
  linarith


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.accumTerm_le (L : List (𝕋 × (Fin n → ℕ))) (c : 𝕋) (e : Fin n → ℕ)
    {t : Vec ℝ n} (ht : t ∈ Real.Taylm.box n) : -- --- CONCL ---
    |Real.Taylm.polyOf ((Taylm.accumTerm L c e).1.map fun a => (toReal a.1, a.2)) t
        - Real.Taylm.polyOf (L.map fun a => (toReal a.1, a.2)) t
        - toReal c * Real.Taylm.monomial e t|
      ≤ toReal (Taylm.accumTerm L c e).2 := by -- --- PROOF ---
  have hm := Real.Taylm.abs_monomial_le_one ht e
  induction L with
  | nil =>
    have := Taylm.aux_round zero c hm
    simp only [Taylm.accumTerm, List.map_cons, List.map_nil, Real.Taylm.polyOf_cons,
      Real.Taylm.polyOf_nil, toReal_zero] at this ⊢
    convert this using 2
    ring
  | cons a L ih =>
    simp only [Taylm.accumTerm]
    split_ifs with h₁ h₂
    · -- the exponents equal: the coefficient is the rounded sum
      have := Taylm.aux_round a.1 c hm
      simp only [List.map_cons, Real.Taylm.polyOf_cons, h₁]
      convert this using 2
      ring
    · -- a new term in front
      have := Taylm.aux_round zero c hm
      simp only [List.map_cons, Real.Taylm.polyOf_cons, toReal_zero] at this ⊢
      convert this using 2
      ring
    · -- further down the list: the head cancels
      simp only [List.map_cons, Real.Taylm.polyOf_cons]
      convert ih using 2
      ring

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
