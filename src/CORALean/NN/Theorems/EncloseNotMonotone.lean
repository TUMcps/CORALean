import CORALean.NN.Layers.Activation

/-!
# `Layer.enclose` is not monotone in its input set

`Relaxation` lets `slope` depend on the box however it likes — deliberately, since
`Relaxation.tighter` [1] picks per box and `Relaxation.ofDeriv`'s `lam` is free inside its bracket.
That freedom also lets a relaxation be sloppy on a narrow box and exact on a wide one, so a small
set's loose enclosure can escape a large set's tight one: `enclose` is not monotone in its input
set. The witness relaxes the zero function, slope `1` below width `2` and `0` at or above it;
enclosing `[0, 1]` reaches `1`, enclosing the containing `[0, 3]` only `0`.

This is not a defect to fix, but it costs a proof strategy: a network reduced at several layers
cannot be reached by composing single-layer containments through `enclose`, the way
`NeuronMergingNetworkOuter.lean` does for one layer. Each of #69's Alg. 2/Thm. 1 and #68's Prop. 2
needs its own induction over the network instead.

`enclose_outer` is unaffected: every layer's `enclose` still contains the exact image of every
point in its input set. That is soundness at each point, which is a different property from
monotonicity in the set, and only the latter fails.

## References

* [1] `CORALean.Real.Relaxation.tighter`.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open ContSet


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The zero function: cheap to relax at any slope, which is the freedom the
counterexample exploits. -/
def aux_encloseNotMonotone_sigma : ℝ → ℝ := fun _ => 0

/-- Slope `1` below width `2`, slope `0` at or above it. Both branches are sound:
the deviation from the chosen line never exceeds half the box's width. -/
noncomputable def aux_encloseNotMonotone_R : Relaxation aux_encloseNotMonotone_sigma where
  slope l u := if u - l < 2 then 1 else 0
  offset l u := if u - l < 2 then -(l + u) / 2 else 0
  error l u := if u - l < 2 then (u - l) / 2 else 0
  sound {l u t} hl hu := by
    split_ifs with h
    · -- narrow branch: `σ` is zero, so this is a midpoint-distance bound
      simp only [aux_encloseNotMonotone_sigma]
      rw [abs_le]
      constructor <;> linarith
    · -- wide branch: slope, offset and error are all `0`, and so is `σ`
      simp [aux_encloseNotMonotone_sigma]

/-- The narrow box `[0, 1]`. -/
def aux_encloseNotMonotone_s : Interval (Vec ℝ 1) := ⟨fun _ => 0, fun _ => 1⟩

/-- The wide box `[0, 3]`, which contains `aux_encloseNotMonotone_s`. -/
def aux_encloseNotMonotone_t : Interval (Vec ℝ 1) := ⟨fun _ => 0, fun _ => 3⟩

theorem aux_encloseNotMonotone_subset :
    construct aux_encloseNotMonotone_s ⊆ construct aux_encloseNotMonotone_t := by
  intro x hx i
  have h1 : (0 : ℝ) ≤ x i := (hx i).1
  have h2 : x i ≤ (1 : ℝ) := (hx i).2
  exact ⟨h1, by show x i ≤ (3 : ℝ); linarith⟩

-- both boxes decide the same `if`, since it reads only the width `u - l`
theorem aux_encloseNotMonotone_R_narrow :
    aux_encloseNotMonotone_R.slope 0 1 = 1 ∧ aux_encloseNotMonotone_R.offset 0 1 = -1 / 2
      ∧ aux_encloseNotMonotone_R.error 0 1 = 1 / 2 := by
  have h : (1 : ℝ) - 0 < 2 := by norm_num
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [aux_encloseNotMonotone_R, if_pos h]

theorem aux_encloseNotMonotone_R_wide :
    aux_encloseNotMonotone_R.slope 0 3 = 0 ∧ aux_encloseNotMonotone_R.offset 0 3 = 0
      ∧ aux_encloseNotMonotone_R.error 0 3 = 0 := by
  have h : ¬ ((3 : ℝ) - 0 < 2) := by norm_num
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [aux_encloseNotMonotone_R, if_neg h]

/-- The constant `1` vector lies in the narrow box's own propagation, `[-1, 1]`. -/
theorem aux_encloseNotMonotone_mem_s :
    (fun _ : Fin 1 => (1 : ℝ)) ∈ construct
      ((Layer.activation (S := fun n => Interval (Vec ℝ n)) aux_encloseNotMonotone_R).enclose
        aux_encloseNotMonotone_s) := by -- --- PROOF ---
  intro i
  have hi : i = (0 : Fin 1) := by omega
  subst hi
  obtain ⟨hs, ho, he⟩ := aux_encloseNotMonotone_R_narrow
  -- the propagation is `mtimes (diag 1) s ⊞ box`; unfold both at the only coordinate
  show (Interval.mtimes (aux_encloseNotMonotone_R.slopeMat aux_encloseNotMonotone_s)
        aux_encloseNotMonotone_s).inf 0
      + (aux_encloseNotMonotone_R.offset 0 1 - aux_encloseNotMonotone_R.error 0 1) ≤ (1 : ℝ)
    ∧ (1 : ℝ) ≤ (Interval.mtimes (aux_encloseNotMonotone_R.slopeMat aux_encloseNotMonotone_s)
        aux_encloseNotMonotone_s).sup 0
      + (aux_encloseNotMonotone_R.offset 0 1 + aux_encloseNotMonotone_R.error 0 1)
  have hM : aux_encloseNotMonotone_R.slopeMat aux_encloseNotMonotone_s 0 0 = 1 := by
    simp [Relaxation.slopeMat, aux_encloseNotMonotone_s, Matrix.diagonal_apply_eq, hs]
  -- fix the slope first, before unfolding `s` erases the pattern `hM` rewrites
  simp only [Interval.mtimes, Fin.sum_univ_one, hM]
  simp only [one_mul, aux_encloseNotMonotone_s, ho, he]
  exact ⟨by linarith [min_le_right (0 : ℝ) 1], by linarith [le_max_right (0 : ℝ) 1]⟩

/-- The wide box's own propagation is the single point `0`: slope `0` drops every
dependence on the input, so nothing at `1` survives. -/
theorem aux_encloseNotMonotone_not_mem_t :
    (fun _ : Fin 1 => (1 : ℝ)) ∉ construct
      ((Layer.activation (S := fun n => Interval (Vec ℝ n)) aux_encloseNotMonotone_R).enclose
        aux_encloseNotMonotone_t) := by -- --- PROOF ---
  intro hmem
  have h0 : (Interval.mtimes (aux_encloseNotMonotone_R.slopeMat aux_encloseNotMonotone_t)
        aux_encloseNotMonotone_t).inf 0
      + (aux_encloseNotMonotone_R.offset 0 3 - aux_encloseNotMonotone_R.error 0 3) ≤ (1 : ℝ)
    ∧ (1 : ℝ) ≤ (Interval.mtimes (aux_encloseNotMonotone_R.slopeMat aux_encloseNotMonotone_t)
        aux_encloseNotMonotone_t).sup 0
      + (aux_encloseNotMonotone_R.offset 0 3 + aux_encloseNotMonotone_R.error 0 3) :=
    hmem (0 : Fin 1)
  obtain ⟨hs, ho, he⟩ := aux_encloseNotMonotone_R_wide
  have hM : aux_encloseNotMonotone_R.slopeMat aux_encloseNotMonotone_t 0 0 = 0 := by
    simp [Relaxation.slopeMat, aux_encloseNotMonotone_t, Matrix.diagonal_apply_eq, hs]
  -- the slope `0` kills the sum, and the box is the point `0`
  simp only [Interval.mtimes, Fin.sum_univ_one, hM] at h0
  simp only [zero_mul, min_self, max_self, ho, he] at h0
  linarith [h0.2]


-- =======================================  MAIN THEOREM  ======================================= --

/-- The zero-function relaxation above witnesses that no such law holds: `[0, 1]`
encloses past `1`, while its superset `[0, 3]` encloses only to `0`. -/
theorem Layer.enclose_not_monotone :
    ¬ ∀ {σ : ℝ → ℝ} (R : Relaxation σ) (s t : Interval (Vec ℝ 1)),
        construct s ⊆ construct t →
          construct ((Layer.activation (S := fun n => Interval (Vec ℝ n)) R).enclose s)
            ⊆ construct ((Layer.activation (S := fun n => Interval (Vec ℝ n)) R).enclose t) := by
  intro h
  exact aux_encloseNotMonotone_not_mem_t
    (h aux_encloseNotMonotone_R aux_encloseNotMonotone_s aux_encloseNotMonotone_t
      aux_encloseNotMonotone_subset aux_encloseNotMonotone_mem_s)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
