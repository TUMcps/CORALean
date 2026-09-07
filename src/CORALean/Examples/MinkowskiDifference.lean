import CORALean.ContSet.HPolytope.Real.Theorems.MinusOfInner
import CORALean.ContSet.Interval.Real.Theorems.MinusExact

/-!
# A difference is a guarantee, so it may only under-approximate

`Minus`'s obligation is *inner* — the only class here whose direction flips: an
implementation may only ever return less than the true difference, never more.
`Interval.minus` happens to be exact (`minus_exact`); `HPolytope.minusOf` is
not, and a loose `SupportBound` shows the gap directly — a point genuinely in
the true difference that the representation excludes.

A subtrahend moving along an equality direction has no difference at all:
`minusOf_inner`'s `hker` needs `T` in the kernel of every equality row, so a
polytope built with no equality rows (`me = 0`) makes that hypothesis vacuous.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

-- `Interval.minus`, exact: a box of half-width `0.2` taken from a box of half-width `1`.

def MDiff.I1 : Interval (Vec ℝ 1) := ⟨![(-1:ℝ)], ![(1:ℝ)]⟩
def MDiff.I2 : Interval (Vec ℝ 1) := ⟨![(-0.2:ℝ)], ![(0.2:ℝ)]⟩

theorem MDiff.I2_nonempty : MDiff.I2.IsNonempty := by
  intro i
  fin_cases i
  show MDiff.I2.inf 0 ≤ MDiff.I2.sup 0
  norm_num [MDiff.I2]

/-- The exact difference is `[-0.8, 0.8]`, and `0.5` sits inside it. -/
example : (![(0.5:ℝ)] : Vec ℝ 1) ∈ minkowskiDiff MDiff.I1.construct MDiff.I2.construct := by
  rw [Interval.minus_exact MDiff.I1 MDiff.I2 MDiff.I2_nonempty]
  intro i
  fin_cases i
  constructor
  · show (MDiff.I1.minus MDiff.I2).inf 0 ≤ (![(0.5:ℝ)] : Vec ℝ 1) 0
    norm_num [Interval.minus, MDiff.I1, MDiff.I2]
  · show (![(0.5:ℝ)] : Vec ℝ 1) 0 ≤ (MDiff.I1.minus MDiff.I2).sup 0
    norm_num [Interval.minus, MDiff.I1, MDiff.I2]

/-- `0.9` sits outside it — cheap, since the representation itself already
excludes it. -/
example : (![(0.9:ℝ)] : Vec ℝ 1) ∉ minkowskiDiff MDiff.I1.construct MDiff.I2.construct := by
  rw [Interval.minus_exact MDiff.I1 MDiff.I2 MDiff.I2_nonempty]
  intro h
  have h2 : (![(0.9:ℝ)] : Vec ℝ 1) 0 ≤ (MDiff.I1.minus MDiff.I2).sup 0 := (h 0).2
  norm_num [Interval.minus, MDiff.I1, MDiff.I2] at h2


-- `HPolytope.minusOf`, only inner: the same box `[-1, 1]`, no equality rows.

/-- `[-1, 1]` in one dimension, as two inequalities against the one coordinate,
`Ae`/`be` empty. -/
def MDiff.P : HPolytope (Vec ℝ 1) where
  m := 2
  A := ![LinearMap.proj (0 : Fin 1), -LinearMap.proj (0 : Fin 1)]
  b := ![(1:ℝ), 1]
  me := 0
  Ae := Fin.elim0
  be := Fin.elim0

/-- The half-width-`0.2` box, held as a plain set rather than a representation:
`minusOf` takes the subtrahend uninterpreted. -/
def MDiff.T : Set (Vec ℝ 1) := {y : Vec ℝ 1 | -0.2 ≤ y 0 ∧ y 0 ≤ 0.2}

/-- `T`'s true support in both constraint directions is `0.2`; `0.3` is a valid
but loose bound, chosen to expose that `minusOf` need not be tight. -/
def MDiff.u : ∀ i : Fin 2, SupportBound MDiff.T (MDiff.P.A i) := fun i =>
  ⟨0.3, by
    fin_cases i <;>
    · intro y hy
      simp [MDiff.P, Matrix.cons_val_zero, Matrix.cons_val_one,
        LinearMap.proj_apply, LinearMap.neg_apply]
      linarith [hy.1, hy.2]⟩

/-- No equality rows at all, so `hker` is vacuous. -/
theorem MDiff.hker : ∀ i : Fin MDiff.P.me, ∀ y ∈ MDiff.T, MDiff.P.Ae i y = 0 := by
  exact fun i => i.elim0

/-- `0.5` is in the certified difference `[-0.7, 0.7]`, and so — by
`minusOf_inner` — genuinely in the true difference. -/
example : (![(0.5:ℝ)] : Vec ℝ 1) ∈ minkowskiDiff MDiff.P.construct MDiff.T := by
  have hmem : (![(0.5:ℝ)] : Vec ℝ 1) ∈ (MDiff.P.minusOf MDiff.T MDiff.u).construct := by
    refine ⟨fun i => ?_, fun i => i.elim0⟩
    fin_cases i <;>
      simp [HPolytope.minusOf, MDiff.P, MDiff.u, Matrix.cons_val_zero, Matrix.cons_val_one,
        LinearMap.proj_apply, LinearMap.neg_apply] <;>
      norm_num
  exact HPolytope.minusOf_inner MDiff.P MDiff.T MDiff.u MDiff.hker hmem

/-- `0.75` genuinely sits in the true difference — every point of `T` still
lands back in `P` — yet the loose `0.3` bound leaves it out of `minusOf`'s
`[-0.7, 0.7]`, exactly the under-approximation the class allows. -/
example : (![(0.75:ℝ)] : Vec ℝ 1) ∈ minkowskiDiff MDiff.P.construct MDiff.T ∧
    (![(0.75:ℝ)] : Vec ℝ 1) ∉ (MDiff.P.minusOf MDiff.T MDiff.u).construct := by
  constructor
  · rintro y ⟨hlo, hhi⟩
    refine ⟨fun i => ?_, fun i => i.elim0⟩
    fin_cases i <;>
      simp [MDiff.P, Matrix.cons_val_zero, Matrix.cons_val_one,
        LinearMap.proj_apply, LinearMap.neg_apply, Matrix.vecHead] <;>
      linarith
  · rintro ⟨h, -⟩
    have h0 : MDiff.P.A (0 : Fin 2) (![(0.75:ℝ)] : Vec ℝ 1)
        ≤ (MDiff.P.minusOf MDiff.T MDiff.u).b (0 : Fin 2) := h (0 : Fin 2)
    simp [HPolytope.minusOf, MDiff.P, MDiff.u, Matrix.cons_val_zero, LinearMap.proj_apply]
      at h0
    norm_num at h0

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
