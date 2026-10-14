import CORALean.ContSet.HPolytope.Real.Theorems.MinkDiffOfInner

/-!
# The Minkowski difference of a halfspace description is only inner

`MinkDiff`'s obligation is *inner* — the only class whose direction flips: an implementation may
only ever return less than the true difference. `HPolytope.minkDiffOf` meets it by tightening
each row by a `SupportBound` of the subtrahend, and a loose bound shows the gap directly: `[-1, 1]`
less `[-0.2, 0.2]`, with the bound `0.3` in place of the true `0.2`, is `[-0.7, 0.7]` rather than
`[-0.8, 0.8]`, so `0.75` is a point genuinely in the true difference that the representation
excludes.

`minkDiffOf_inner`'s `hker` needs the subtrahend in the kernel of every equality row, so a
polytope built with no equality rows (`me = 0`) makes that hypothesis vacuous; a subtrahend moving
along an equality direction has no difference at all.
-/

-- Authors:       Claude Opus 5, Claude Sonnet 5.5
-- Written:       07-September-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

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
`minkDiffOf` takes the subtrahend uninterpreted. -/
def MDiff.T : Set (Vec ℝ 1) := {y : Vec ℝ 1 | -0.2 ≤ y 0 ∧ y 0 ≤ 0.2}

/-- `T`'s true support in both constraint directions is `0.2`; `0.3` is a valid
but loose bound, chosen to expose that `minkDiffOf` need not be tight. -/
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
`minkDiffOf_inner` — genuinely in the true difference. -/
example : (![(0.5:ℝ)] : Vec ℝ 1) ∈ minkowskiDiff MDiff.P.construct MDiff.T := by
  have hmem : (![(0.5:ℝ)] : Vec ℝ 1) ∈ (MDiff.P.minkDiffOf MDiff.T MDiff.u).construct := by
    refine ⟨fun i => ?_, fun i => i.elim0⟩
    fin_cases i <;>
      simp [HPolytope.minkDiffOf, MDiff.P, MDiff.u, Matrix.cons_val_zero, Matrix.cons_val_one,
        LinearMap.proj_apply, LinearMap.neg_apply] <;>
      norm_num
  exact HPolytope.minkDiffOf_inner MDiff.P MDiff.T MDiff.u MDiff.hker hmem

/-- `0.75` genuinely sits in the true difference — every point of `T` still
lands back in `P` — yet the loose `0.3` bound leaves it out of `minkDiffOf`'s
`[-0.7, 0.7]`, exactly the under-approximation the class allows. -/
example : (![(0.75:ℝ)] : Vec ℝ 1) ∈ minkowskiDiff MDiff.P.construct MDiff.T ∧
    (![(0.75:ℝ)] : Vec ℝ 1) ∉ (MDiff.P.minkDiffOf MDiff.T MDiff.u).construct := by
  constructor
  · rintro y ⟨hlo, hhi⟩
    refine ⟨fun i => ?_, fun i => i.elim0⟩
    fin_cases i <;>
      simp [MDiff.P, Matrix.cons_val_zero, Matrix.cons_val_one,
        LinearMap.proj_apply, LinearMap.neg_apply, Matrix.vecHead] <;>
      linarith
  · rintro ⟨h, -⟩
    have h0 : MDiff.P.A (0 : Fin 2) (![(0.75:ℝ)] : Vec ℝ 1)
        ≤ (MDiff.P.minkDiffOf MDiff.T MDiff.u).b (0 : Fin 2) := h (0 : Fin 2)
    simp [HPolytope.minkDiffOf, MDiff.P, MDiff.u, Matrix.cons_val_zero, LinearMap.proj_apply]
      at h0
    norm_num at h0

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
