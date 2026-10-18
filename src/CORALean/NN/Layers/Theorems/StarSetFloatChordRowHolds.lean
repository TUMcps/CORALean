module

public import CORALean.NN.Layers.Definitions.Relu
public import CORALean.ContSet.Interval.Float.Theorems.MulBetweenCorners
public import CORALean.NN.Layers.Operations.StarSetFloatChordRow
public import CORALean.NN.Layers.Operations.StarSetFloatChordGuard

@[expose] public section

/-!
# The float chord row holds at the ReLU of a bounded neuron

At a point of the star set, the neuron lying within its bounds, the value `β = relu(y)` of
its ReLU satisfies the chord row, whenever `StarSet.chordGuard` accepts the bounds. The
rounding of `k` and of its products with the generators is paid by the right-hand side.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem StarSet.chordRow_holds (s : StarSet 𝕋 n) (j : Fin n) (b : Interval 𝕋)
    (hg : StarSet.chordGuard b = true) (α : Fin s.m → ℝ)
    (hα : ∀ k, toReal (s.pred.l k) ≤ α k ∧ α k ≤ toReal (s.pred.u k))
    (hy : toReal b.inf ≤ toReal (s.c j) + ∑ k, toReal (s.G j k) * α k ∧
      toReal (s.c j) + ∑ k, toReal (s.G j k) * α k ≤ toReal b.sup) : -- --- STMT ---
    ∑ k : Fin (s.m + 1), toReal ((s.chordRow j b).1 k)
        * Fin.snoc (α := fun _ => ℝ) α
          (Real.relu (toReal (s.c j) + ∑ k, toReal (s.G j k) * α k)) k
      ≤ toReal (s.chordRow j b).2 := by -- --- PROOF ---
  -- the guard gives `l < 0 < u` and a positive rounded `u - l`
  set y := toReal (s.c j) + ∑ k, toReal (s.G j k) * α k with hydef
  set lf := toReal b.inf with hlf
  set uf := toReal b.sup with huf
  unfold StarSet.chordGuard at hg
  simp only [Bool.and_eq_true] at hg
  obtain ⟨⟨h1, h2⟩, h3⟩ := hg
  have hl0 : lf < 0 := by
    have := toReal_lt_of_ltStrict h1; rwa [toReal_zero] at this
  have hu0 : 0 < uf := by
    have := toReal_lt_of_ltStrict h2; rwa [toReal_zero] at this
  have hdL : 0 < toReal (subDown b.sup b.inf) := by
    have := toReal_lt_of_ltStrict h3; rwa [toReal_zero] at this
  have hd : 0 < uf - lf := by linarith
  have hdLle : toReal (subDown b.sup b.inf) ≤ uf - lf := subDown_le_sub _ _
  have hdUge : uf - lf ≤ toReal (subUp b.sup b.inf) := sub_le_subUp _ _
  have hdU : 0 < toReal (subUp b.sup b.inf) := lt_of_lt_of_le hd hdUge
  -- the slope `k` is bracketed by its two roundings
  set k := uf / (uf - lf) with hk
  have hklo : toReal (divDown b.sup (subUp b.sup b.inf)) ≤ k :=
    le_trans (divDown_le_div _ _ hdU) (div_le_div_of_nonneg_left hu0.le hd hdUge)
  have hkhi : k ≤ toReal (divUp b.sup (subDown b.sup b.inf)) :=
    le_trans (div_le_div_of_nonneg_left hu0.le hdL hdLle) (div_le_divUp _ _ hdL)
  set klo := divDown b.sup (subUp b.sup b.inf) with hkloD
  set khi := divUp b.sup (subDown b.sup b.inf) with hkhiD
  set β := Real.relu y with hβ
  -- the chord lies above the ReLU
  have hchord : β ≤ k * (y - lf) := by
    rw [hk, div_mul_eq_mul_div, le_div_iff₀ hd]
    rcases le_total y 0 with h | h
    · rw [hβ, Real.relu, max_eq_right h]; nlinarith [hy.1]
    · rw [hβ, Real.relu, max_eq_left h]; nlinarith [hy.2]
  have hS : y - lf = (toReal (s.c j) - lf) + ∑ i, toReal (s.G j i) * α i := by
    rw [hydef]; ring
  -- the products with the generators, and the widest factor of the box
  have hP := fun i => Interval.mul_between_corners hklo hkhi
    (le_refl (toReal (s.G j i))) (le_refl (toReal (s.G j i)))
  -- per generator: the two rounded products with the slope's corners, and the widest factor
  set lo : Fin s.m → 𝕋 := fun i => Interval.mulLo klo khi (s.G j i) (s.G j i) with hlo
  set hi : Fin s.m → 𝕋 := fun i => Interval.mulHi klo khi (s.G j i) (s.G j i) with hhi
  set wd : Fin s.m → 𝕋 := fun i => maximum (absolute (s.pred.l i)) (absolute (s.pred.u i)) with hwd
  have hmag : ∀ i, |α i| ≤ toReal (wd i) := fun i => by
    rw [toReal_maximum, toReal_absolute, toReal_absolute]
    exact abs_le_max_abs_abs (hα i).1 (hα i).2
  -- what the rounding of one generator's product costs over the box
  have hterm : ∀ i, (k * toReal (s.G j i) - toReal (lo i))
      * α i ≤ toReal (mulUp
        (subUp (hi i)
          (lo i))
        (wd i)) := fun i => by
    have hδ0 : 0 ≤ k * toReal (s.G j i)
        - toReal (lo i) := by linarith [(hP i).1]
    have hw : k * toReal (s.G j i) - toReal (lo i)
        ≤ toReal (subUp (hi i)
          (lo i)) :=
      le_trans (by linarith [(hP i).2]) (sub_le_subUp _ _)
    -- the cost is nonnegative, so it is at most its size against the widest factor
    calc (k * toReal (s.G j i) - toReal (lo i)) * α i
        ≤ (k * toReal (s.G j i) - toReal (lo i))
          * |α i| := mul_le_mul_of_nonneg_left (le_abs_self _) hδ0
      _ ≤ toReal (subUp (hi i)
            (lo i))
          * toReal (wd i) :=
        mul_le_mul hw (hmag i) (abs_nonneg _) (le_trans hδ0 hw)
      _ ≤ _ := mul_le_mulUp _ _
  have hsumterm := le_trans (Finset.sum_le_sum fun i _ => hterm i) (sum_le_sumUp _)
  have hc := Interval.mul_between_corners hklo hkhi
    (subDown_le_sub (s.c j) b.inf : toReal (subDown (s.c j) b.inf) ≤ toReal (s.c j) - lf)
    (sub_le_subUp (s.c j) b.inf : toReal (s.c j) - lf ≤ toReal (subUp (s.c j) b.inf))
  -- the right-hand side is the two rounded parts added up
  have hrhs := add_le_addUp (Interval.mulHi klo khi (subDown (s.c j) b.inf) (subUp (s.c j) b.inf))
    (sumUp fun i => mulUp
      (subUp (hi i)
        (lo i))
      (wd i))
  -- the sums, then assemble
  have hsplit : ∑ i, (k * toReal (s.G j i)
      - toReal (lo i)) * α i
      = k * ∑ i, toReal (s.G j i) * α i
        - ∑ i, toReal (lo i) * α i := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hk' : k * (y - lf) = k * (toReal (s.c j) - lf) + k * ∑ i, toReal (s.G j i) * α i := by
    rw [hS]; ring
  -- read the row off the definition
  unfold StarSet.chordRow
  simp only [Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last, toReal_neg, toReal_one,
    one_mul]
  have e : ∑ i : Fin s.m, -toReal (lo i) * α i
      = -∑ i, toReal (lo i) * α i := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e]
  linarith [hc.2, hsplit, hk', hchord, hsumterm, hrhs]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
