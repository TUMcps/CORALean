import CORALean.ContSet.VPolytope.Real.VPolytope
import CORALean.ContSet.Interval.Real.Interval
import CORALean.Global.Corners

/-!
# A box as its corners

`2ⁿ` vertices, exponential and inherently so: a box in `n` dimensions has that
many corners and a vertex description has to name them all.

The witness is explicit. Each coordinate sits some fraction `t j` of the way up
its own range, and a corner's weight is the product over coordinates of `t j` or
`1 - t j` according to which end that corner took. Both obligations are then the
same combinatorial identity — the weights sum to one because each coordinate's
pair does, and they reproduce `x` because for one coordinate at a time every
other coordinate's pair sums away.

A flat coordinate is the case to watch: `t j` divides by the range's width, so it
is set to zero there, which is correct because a flat range leaves `x j` no
choice.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}

/-- The corner that takes each coordinate's upper end where `σ` says so. -/
def Interval.corner (I : Interval (Vec ℝ n)) (σ : Fin n → Bool) : Vec ℝ n :=
  fun j => if σ j then I.sup j else I.inf j

noncomputable def Interval.vPolytope (I : Interval (Vec ℝ n)) : VPolytope (Vec ℝ n) where
  k := 2 ^ n
  V := fun l => I.corner (signEquiv n l)


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.vPolytope_contains (I : Interval (Vec ℝ n)) :
    I.construct ⊆ I.vPolytope.construct := by -- --- PROOF ---
  intro x hx
  have hlo : ∀ j, I.inf j ≤ x j := fun j => (hx j).1
  have hhi : ∀ j, x j ≤ I.sup j := fun j => (hx j).2
  -- how far up its own range each coordinate sits, and zero where there is no range
  obtain ⟨t, ht0, ht1, hval⟩ : ∃ t : Fin n → ℝ, (∀ j, 0 ≤ t j) ∧ (∀ j, t j ≤ 1) ∧
      ∀ j, t j * I.sup j + (1 - t j) * I.inf j = x j := by
    refine ⟨fun j => if I.sup j = I.inf j then 0 else (x j - I.inf j) / (I.sup j - I.inf j),
      fun j => ?_, fun j => ?_, fun j => ?_⟩ <;>
    · by_cases h : I.sup j = I.inf j
      · simp only [if_pos h]
        first
          | linarith
          | (rw [h]; linarith [hlo j, hhi j, h ▸ hhi j])
      · simp only [if_neg h]
        have hd : 0 < I.sup j - I.inf j := by
          rcases lt_or_eq_of_le (le_trans (hlo j) (hhi j)) with hlt | heq
          · linarith
          · exact absurd heq.symm h
        first
          | exact div_nonneg (by linarith [hlo j]) hd.le
          | exact (div_le_one hd).mpr (by linarith [hhi j])
          | (field_simp; ring)
  -- a corner's convex weight is the product of the per-coordinate ones
  refine ⟨fun l => ∏ j, (if signEquiv n l j then t j else 1 - t j), fun l => ?_, ?_, ?_⟩
  · exact Finset.prod_nonneg fun j _ => by
      cases signEquiv n l j <;> simp <;> linarith [ht0 j, ht1 j]
  · show ∑ l : Fin (2 ^ n), (∏ j, (if signEquiv n l j then t j else 1 - t j)) = 1
    rw [Fintype.sum_equiv (signEquiv n)
        (fun l => ∏ j, (if signEquiv n l j then t j else 1 - t j))
        (fun σ => ∏ j, (if σ j then t j else 1 - t j)) fun _ => rfl,
      sum_prod_bool]
    simp
  -- the value: the sum over corners factorises coordinate by coordinate
  · funext i
    have hsum : (∑ l : Fin (2 ^ n),
          (∏ j, (if signEquiv n l j then t j else 1 - t j)) • I.corner (signEquiv n l)) i
        = ∑ l : Fin (2 ^ n), (∏ j, (if signEquiv n l j then t j else 1 - t j))
            * (if signEquiv n l i then I.sup i else I.inf i) := by
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rfl
    show x i = (∑ l : Fin (2 ^ n),
      (∏ j, (if signEquiv n l j then t j else 1 - t j)) • I.corner (signEquiv n l)) i
    rw [hsum, Fintype.sum_equiv (signEquiv n) _
        (fun σ : Fin n → Bool => (∏ j, (if σ j then t j else 1 - t j))
          * (if σ i then I.sup i else I.inf i)) fun _ => rfl,
      sum_prod_bool_mul t I.sup I.inf i, hval i]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
