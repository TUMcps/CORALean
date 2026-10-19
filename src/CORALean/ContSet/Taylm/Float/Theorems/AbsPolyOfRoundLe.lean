module

public import CORALean.ContSet.Taylm.Float.Taylm
public import CORALean.ContSet.Taylm.Real.Theorems.AbsMonomialLeOne
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfCons
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfNil
public import CORALean.Global.Float.ListSum

@[expose] public section

/-!
# What storing one end of each coefficient's enclosure costs

For real coefficients `x a ∈ [lo a, hi a]`, the polynomial with `hi a` stored differs from
the exact one by at most the summed widths on the box, every monomial being in `[-1, 1]`.
Every float operation that computes a coefficient pays its rounding through this.
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

theorem Taylm.abs_polyOf_round_le {α : Type} (L : List α) (lo hi : α → 𝕋) (x : α → ℝ)
    (e : α → (Fin n → ℕ)) (hx : ∀ a ∈ L, toReal (lo a) ≤ x a ∧ x a ≤ toReal (hi a))
    {t : Vec ℝ n} (ht : t ∈ Real.Taylm.box n) : -- --- CONCL ---
    |Real.Taylm.polyOf (L.map fun a => (x a, e a)) t
        - Real.Taylm.polyOf (L.map fun a => (toReal (hi a), e a)) t|
      ≤ toReal (listSumUp (L.map fun a => subUp (hi a) (lo a))) := by -- --- PROOF ---
  induction L with
  | nil => simp [listSumUp, toReal_zero]
  | cons a L ih =>
    have ih' := ih fun b hb => hx b (List.mem_cons_of_mem a hb)
    have ha := hx a List.mem_cons_self
    have hm := Real.Taylm.abs_monomial_le_one ht (e a)
    have hsub := sub_le_subUp (hi a) (lo a)
    have hadd := add_le_addUp (subUp (hi a) (lo a))
      (listSumUp (L.map fun a => subUp (hi a) (lo a)))
    simp only [List.map_cons, Real.Taylm.polyOf_cons, listSumUp]
    -- the head term: its coefficient error times a monomial of magnitude at most one
    have h1 : |x a * Real.Taylm.monomial (e a) t - toReal (hi a) * Real.Taylm.monomial (e a) t|
        ≤ toReal (hi a) - toReal (lo a) := by
      rw [← sub_mul, abs_mul]
      have : |x a - toReal (hi a)| ≤ toReal (hi a) - toReal (lo a) := by
        rw [abs_le]; constructor <;> linarith [ha.1, ha.2]
      calc |x a - toReal (hi a)| * |Real.Taylm.monomial (e a) t|
          ≤ (toReal (hi a) - toReal (lo a)) * 1 :=
            mul_le_mul this hm (abs_nonneg _) (by linarith [ha.1, ha.2])
        _ = _ := mul_one _
    calc _ = |(x a * Real.Taylm.monomial (e a) t - toReal (hi a) * Real.Taylm.monomial (e a) t)
          + (Real.Taylm.polyOf (L.map fun a => (x a, e a)) t
            - Real.Taylm.polyOf (L.map fun a => (toReal (hi a), e a)) t)| := by ring_nf
      _ ≤ _ := abs_add_le _ _
      _ ≤ _ := add_le_add h1 ih'
      _ ≤ _ := by linarith

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
