import CORALean.ContSet.Taylm.Float.Operations.RepresentsaPoint

/-!
# `Taylm.representsa_point` is sound

A `true` answer makes every coordinate's polynomial the constant `poly 0` on the whole box, with
remainder `[0, 0]`, so the range set is within the point `(poly 0)ᵢ`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- With every positive-degree coefficient zero, the polynomial is its value at `0`. -/
theorem Taylm.aux_polyOf_const (L : List (ℝ × (Fin n → ℕ))) (t : Vec ℝ n)
    (h : ∀ a ∈ L, (∀ k, a.2 k = 0) ∨ a.1 = 0) :
    Real.Taylm.polyOf L t = Real.Taylm.polyOf L 0 := by -- --- PROOF ---
  induction L with
  | nil => rfl
  | cons a L ih =>
    rw [Real.Taylm.polyOf_cons, Real.Taylm.polyOf_cons,
      ih fun b hb => h b (List.mem_cons_of_mem a hb)]
    congr 1
    rcases h a List.mem_cons_self with h0 | h0
    · -- degree zero: both monomials are `1`
      have he : a.2 = 0 := funext h0
      rw [he, Real.Taylm.monomial_zero, Real.Taylm.monomial_zero]
    · rw [h0, zero_mul, zero_mul]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.representsa_point_sound {T : Fin m → Taylm 𝕋 n}
    (h : Taylm.representsa_point T = true) :
    Taylm.construct T ⊆ {fun i => (T i).nominal.poly 0} := by -- --- PROOF ---
  rintro x ⟨t, -, ht⟩
  funext i
  -- the checks of coordinate `i`
  have hi := (List.all_eq_true.1 h) i (List.mem_finRange i)
  simp only [Bool.and_eq_true] at hi
  obtain ⟨⟨hterms, hlo⟩, hhi⟩ := hi
  have h0 := toReal_zero (𝕋 := 𝕋)
  have hlo' : |toReal (T i).remInf| ≤ 0 := by
    have := SoundFloatArithmetic.toReal_le_of_le hlo
    rwa [toReal_absolute, h0] at this
  have hhi' : |toReal (T i).remSup| ≤ 0 := by
    have := SoundFloatArithmetic.toReal_le_of_le hhi
    rwa [toReal_absolute, h0] at this
  -- the polynomial of the nominal model is constant
  have hpoly : (T i).nominal.poly t = (T i).nominal.poly 0 := by
    refine Taylm.aux_polyOf_const _ t fun a ha => ?_
    obtain ⟨b, hb, rfl⟩ := List.mem_map.1 ha
    have hb' := List.all_eq_true.1 hterms b hb
    rcases Bool.or_eq_true_iff.1 hb' with hb' | hb'
    · exact Or.inl (of_decide_eq_true hb')
    · right
      have := SoundFloatArithmetic.toReal_le_of_le hb'
      rw [toReal_absolute, h0] at this
      exact abs_nonpos_iff.1 this
  -- the remainder is `[0, 0]`, so the point equals the polynomial
  have a := ht i
  have e1 : toReal (T i).remInf = 0 := abs_nonpos_iff.1 hlo'
  have e2 : toReal (T i).remSup = 0 := abs_nonpos_iff.1 hhi'
  have : (T i).nominal.remInf = 0 := e1
  have : (T i).nominal.remSup = 0 := e2
  show x i = (T i).nominal.poly 0
  rw [← hpoly]
  have b1 := a.1
  have b2 := a.2
  simp only [Taylm.nominal, Real.Taylm.poly] at *
  linarith

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
