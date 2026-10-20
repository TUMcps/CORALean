module

public import CORALean.ContSet.Interval.Float.Theorems.Basic
public import CORALean.ContSet.Interval.Float.Theorems.MrdivideOuter
public import CORALean.ContSet.Zonotope.Float.Operations.EncloseManyBasisInv

@[expose] public section

/-!
# The box holds the inverse of the rotation

When the entry of `newGen` at the dropped axis is provably nonzero, the matrix `A` of the exact
quotients `1/g_d` and `-g_{i_j}/g_d` and the exact unit entries lies in the box
`Zonotope.encloseManyBasisInv`, and it inverts the matrix `Zonotope.encloseManyBasis` reads as,
`R (A x) = x` for every `x`: the first coordinate `x_d / g_d` of `A x` scales `newGen` to give the
`d`-th coordinate back, and the other coordinates of `A x` are what is left of `x` after subtracting
that multiple, which the axes then add back. So an image under `R⁻¹` is an image under a member of
the box. Source: [1].

## Inputs
* `newGen` – new first generator

## Hypotheses
* `hg` – dropped entry provably nonzero

## Conclusion
* exact inverse lies in the box and inverts the basis

## References

* [1] `contSet/@zonotope/encloseMany.m`, CORA (Sep. 2025). No paper behind the
      rule was confirmed.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open scoped Matrix
open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.encloseManyBasisInv_mem (newGen : Vec 𝕋 (m + 1))
    (hg : ltStrict zero (newGen (Zonotope.encloseManyDropped newGen)) = true
      ∨ ltStrict (newGen (Zonotope.encloseManyDropped newGen)) zero = true) : -- --- CONCL ---
    ∃ A ∈ (Zonotope.encloseManyBasisInv newGen).construct,
      ∀ x : Vec ℝ (m + 1),
        toRealMat (Zonotope.encloseManyBasis newGen) *ᵥ (A *ᵥ x) = x := by -- --- PROOF ---
  -- name the dropped axis, and the divisor, which is not zero
  unfold Zonotope.encloseManyBasisInv Zonotope.encloseManyBasis
  dsimp only
  generalize Zonotope.encloseManyDropped newGen = d at hg ⊢
  have hne : toReal (newGen d) ≠ 0 := by
    rcases hg with h | h
    · have := toReal_lt_of_ltStrict h
      rw [toReal_zero] at this
      exact this.ne'
    · have := toReal_lt_of_ltStrict h
      rw [toReal_zero] at this
      exact this.ne
  -- the exact matrix: the quotients in column `d`, the unit entries elsewhere
  set w : Vec 𝕋 (m + 1) := Fin.cons one fun j => neg (newGen (d.succAbove j)) with hw
  set ud := toReal (newGen d) with hud
  let A : Mat ℝ (m + 1) (m + 1) := Matrix.of fun r k =>
    if k = d then toReal (w r) / ud
    else Fin.cases (0 : ℝ) (fun j => if k = d.succAbove j then 1 else 0) r
  refine ⟨A, ?_, ?_⟩
  · -- it lies in the box: the column `d` by the outward quotient, the rest exactly
    refine Interval.mem_mat_iff.mpr fun r k => ?_
    by_cases hk : k = d
    · have hq := Interval.mrdivide_outer ⟨w, w⟩ (newGen d) hg
        ⟨toRealVec w, fun i => ⟨le_refl _, le_refl _⟩, rfl⟩
      simp only [hk, if_true, A, Matrix.of_apply]
      exact ⟨(hq r).1, (hq r).2⟩
    · simp only [hk, if_false, A, Matrix.of_apply]
      refine Fin.cases ?_ (fun j => ?_) r
      · simp [toReal_zero]
      · simp only [Fin.cases_succ]
        split_ifs <;> simp [toReal_one, toReal_zero]
  · intro x
    funext i
    -- `A x` at row 0, and at row `j + 1`
    have hv0 : (A *ᵥ x) 0 = x d / ud := by
      simp only [Matrix.mulVec, dotProduct, A, Matrix.of_apply, hw, Fin.cons_zero, Fin.cases_zero,
        toReal_one, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      ring
    have hvs : ∀ j : Fin m, (A *ᵥ x) j.succ
        = -toReal (newGen (d.succAbove j)) / ud * x d + x (d.succAbove j) := by
      intro j
      have hA : ∀ k, A j.succ k = (if k = d then -toReal (newGen (d.succAbove j)) / ud else 0)
          + (if k = d.succAbove j then 1 else 0) := by
        intro k
        by_cases hk : k = d
        · simp [A, hk, hw, toReal_neg]
        · by_cases hk' : k = d.succAbove j
          · simp [A, hk']
          · simp [A, hk, hk', hw]
      simp only [Matrix.mulVec, dotProduct, hA, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul,
        one_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    -- `R` applied to a vector, row `i`: the first column scaled, the axes picked
    have hR : ∀ v : Vec ℝ (m + 1), (toRealMat (Matrix.of fun i => (Fin.cons (newGen i) fun j =>
        if i = d.succAbove j then one else zero : Fin (m + 1) → 𝕋)) *ᵥ v) i
        = toReal (newGen i) * v 0
          + ∑ j : Fin m, (if i = d.succAbove j then 1 else 0) * v j.succ := by
      intro v
      simp only [Matrix.mulVec, dotProduct, toRealMat, Matrix.of_apply, Fin.sum_univ_succ,
        Fin.cons_zero, Fin.cons_succ]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      split_ifs <;> simp [toReal_one, toReal_zero]
    rw [hR (A *ᵥ x)]
    by_cases hi : i = d
    · -- the dropped axis: the first column alone reaches it
      subst hi
      have h0 : ∀ j : Fin m, (if i = i.succAbove j then (1 : ℝ) else 0) = 0 := fun j =>
        if_neg (Fin.succAbove_ne i j).symm
      simp only [h0, zero_mul, Finset.sum_const_zero, add_zero, hv0, hud]
      rw [mul_div_assoc', mul_div_cancel_left₀ _ hne]
    · -- any other axis `succAbove j₀`: the multiple of the first column, then what the axis adds
      obtain ⟨j₀, rfl⟩ := Fin.exists_succAbove_eq hi
      rw [Finset.sum_eq_single j₀]
      · rw [hvs j₀, hv0]
        simp only [if_true, one_mul]
        field_simp
        ring
      · intro j _ hj
        rw [if_neg (fun h => hj (Fin.succAbove_right_injective h).symm), zero_mul]
      · intro h
        exact absurd (Finset.mem_univ j₀) h

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
