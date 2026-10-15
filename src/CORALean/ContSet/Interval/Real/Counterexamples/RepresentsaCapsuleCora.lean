module

public import CORALean.ContSet.Interval.Real.Operations.Basic
public import CORALean.ContSet.Capsule.Real.Capsule
public import CORALean.ContSet.Ellipsoid.Real.Ellipsoid
public import CORALean.Global.EuclideanNorm
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# `Interval.representsaCapsuleCora`: the `'capsule'` test as CORA's code computes it

`@interval/representsa_.m`, branch `'capsule'` (l. 70-75; `'ellipsoid'`, l. 92-99, is the same
test, `Interval.representsaEllipsoidCora`), under the comment "either 1D, a point, or at most one
dimension has non-zero width":

```
isPoint = all(withinTol(rad(I),0,tol));                                   % l. 53
res = n == 1 || isPoint || nnz(withinTol(rad(I),0,tol)) <= 1;
```

`withinTol(rad(I),0,tol)` is `true` exactly for the dimensions of width **zero**, so the third
disjunct counts the zero-width dimensions and tests them `<= 1`, where "at most one non-zero
width" is `nnz(~withinTol(rad(I),0,tol)) <= 1`. Tolerance `0`. Read from the source, not run.

# `Interval.representsaEllipsoidCora`: the `'ellipsoid'` test as CORA's code computes it

`@interval/representsa_.m`, branch `'ellipsoid'` (l. 92-99), the same test as `'capsule'`
(`Interval.representsaCapsuleCora`), under the comment "either 1D, a point, or at most one
dimension has non-zero width": `n == 1 || isPoint || nnz(withinTol(rad(I),0,tol)) <= 1`, which
counts the zero-width dimensions. Tolerance `0`. Read from the source, not run.

# CORA's `interval/representsa_(I, 'capsule')` accepts the unit square

For `I = [0,1]²` the radius is `(1/2, 1/2)`, no dimension has zero width, so
`nnz(withinTol(rad(I),0,tol))` is `0 <= 1` and CORA answers `'capsule'` (and, by the same
test, `'ellipsoid'`) with `true`. The unit square is no capsule: a capsule `{x | dist(x, segment)
≤ r}` that lies in the square keeps the whole ball of radius `r` around each segment point in the
square, so its segment stays at distance `≥ r` from the sides, and a corner at distance `≤ r`
from such a point forces `r = 0`; a segment holds no three corners of the square. A wrong
answer, not unsound. Read from the source, not run.

The unit square is no ellipsoid either: the second coordinate of `q + G u` over `‖u‖ ≤ 1` has
minimum `q₁ - ‖Gᵀe₂‖`, attained at one point of the ball only (or the coordinate is constant),
while the corners `(0,0)` and `(1,0)` both attain the minimum `0` of the square.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       13-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- The model: CORA's code as printed, kept only to be refuted.
open Classical in
/-- CORA's `res` for `representsa_(I, 'capsule')` (the `n` is `dim(I)`). -/
noncomputable def Interval.representsaCapsuleCora (I : Interval (Vec ℝ n)) : Bool :=
  let rad := I.radius                                          -- rad(I)
  let isPoint := if ∀ i, rad i = 0 then true else false        -- all(withinTol(rad(I),0,tol))
  let nnzZero := (Finset.univ.filter fun i => rad i = 0).card  -- nnz(withinTol(rad(I),0,tol))
  (if n = 1 then true else false) || isPoint ||                -- n == 1 || isPoint ||
    (if nnzZero ≤ 1 then true else false)                      -- nnz(withinTol(..)) <= 1

end CORALean.Real

namespace CORALean.Real

variable {n : ℕ}


-- The model: CORA's code as printed, kept only to be refuted.
open Classical in
/-- CORA's `res` for `representsa_(I, 'ellipsoid')`: the same test as `'capsule'`. -/
noncomputable def Interval.representsaEllipsoidCora (I : Interval (Vec ℝ n)) : Bool :=
  let rad := I.radius                                          -- rad(I)
  let isPoint := if ∀ i, rad i = 0 then true else false        -- all(withinTol(rad(I),0,tol))
  let nnzZero := (Finset.univ.filter fun i => rad i = 0).card  -- nnz(withinTol(rad(I),0,tol))
  (if n = 1 then true else false) || isPoint ||                -- n == 1 || isPoint ||
    (if nnzZero ≤ 1 then true else false)                      -- nnz(withinTol(..)) <= 1

end CORALean.Real

namespace CORALean.Real

open Entrywise


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The unit square `[0,1]²`. -/
def Interval.aux_unitSquare : Interval (Vec ℝ 2) := ⟨![0, 0], ![1, 1]⟩

theorem Interval.aux_mem_unitSquare (x : Vec ℝ 2) :
    x ∈ Interval.aux_unitSquare.construct ↔
      (0 ≤ x 0 ∧ x 0 ≤ 1) ∧ (0 ≤ x 1 ∧ x 1 ≤ 1) := by -- --- PROOF ---
  unfold Interval.construct Interval.aux_unitSquare
  simp only [Set.mem_setOf_eq]
  constructor
  · intro h
    exact ⟨h 0, h 1⟩
  · rintro ⟨h0, h1⟩ i
    fin_cases i
    · exact h0
    · exact h1


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.aux_r_zero (r s0 s1 : ℝ) (hr : 0 ≤ r) (h : s0 ^ 2 + s1 ^ 2 ≤ r ^ 2)
    (a0 : 0 ≤ s0 - r) (a1 : 0 ≤ s1 - r) : r = 0 := by
  have h0 : r ^ 2 ≤ s0 ^ 2 := by nlinarith
  have h1 : r ^ 2 ≤ s1 ^ 2 := by nlinarith
  have : r ^ 2 = 0 := le_antisymm (by linarith) (sq_nonneg r)
  exact pow_eq_zero_iff (two_ne_zero) |>.mp this

theorem Interval.aux_sq_zero (a b : ℝ) (h : a ^ 2 + b ^ 2 ≤ 0 ^ 2) : a = 0 ∧ b = 0 := by
  constructor <;> nlinarith [sq_nonneg a, sq_nonneg b]

theorem Interval.aux_lines (g0 g1 d0 d1 : ℝ) (h1 : d0 * g0 = 1) (h2 : d1 * g0 = 0)
    (h3 : d1 * g1 = 1) : False := by
  have hg : g0 ≠ 0 := fun hz => by rw [hz] at h1; simp at h1
  have : d1 = 0 := (mul_eq_zero.mp h2).resolve_right hg
  rw [this] at h3
  simp at h3

/-- No capsule is the unit square. -/
theorem Interval.aux_unitSquare_not_capsule (C : Capsule 2) :
    C.construct ≠ Interval.aux_unitSquare.construct := by -- --- PROOF ---
  intro h
  have hmem : ∀ x : Vec ℝ 2, x ∈ C.construct ↔
      (0 ≤ x 0 ∧ x 0 ≤ 1) ∧ (0 ≤ x 1 ∧ x 1 ≤ 1) := fun x => by
    rw [h]; exact Interval.aux_mem_unitSquare x
  -- every point of the capsule has a parameter `t` with squared distance `≤ r²`
  have dist : ∀ x : Vec ℝ 2, ((0 ≤ x 0 ∧ x 0 ≤ 1) ∧ (0 ≤ x 1 ∧ x 1 ≤ 1)) →
      ∃ t ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ C.r ∧
        (x 0 - (C.c 0 + t * C.g 0)) ^ 2 + (x 1 - (C.c 1 + t * C.g 1)) ^ 2 ≤ C.r ^ 2 := by
    intro x hx
    obtain ⟨t, ht, hd⟩ := (hmem x).mpr hx
    rw [Real.sqrt_le_iff, Fin.sum_univ_two] at hd
    exact ⟨t, ht, hd.1, hd.2⟩
  -- the radius is `0`
  obtain ⟨t0, ht0, hr, hd0⟩ := dist ![0, 0] (by simp)
  -- the ball around a segment point stays in the square
  have ball : ∀ (p q : ℝ) (e0 e1 : ℝ), p = C.c 0 + t0 * C.g 0 → q = C.c 1 + t0 * C.g 1 →
      e0 ^ 2 + e1 ^ 2 = 1 →
      (0 ≤ p + C.r * e0 ∧ p + C.r * e0 ≤ 1) ∧ (0 ≤ q + C.r * e1 ∧ q + C.r * e1 ≤ 1) := by
    intro p q e0 e1 hp hq he
    refine (hmem ![p + C.r * e0, q + C.r * e1]).mp ⟨t0, ht0, ?_⟩
    rw [Real.sqrt_le_iff, Fin.sum_univ_two]
    refine ⟨hr, ?_⟩
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, hp, hq]
    have : (C.r * e0) ^ 2 + (C.r * e1) ^ 2 = C.r ^ 2 := by
      rw [mul_pow, mul_pow, ← mul_add, he, mul_one]
    linarith
  -- so the segment point is at distance `≥ r` from the sides, and `r = 0`
  have a0 := (ball _ _ (-1) 0 rfl rfl (by norm_num)).1.1
  have a1 := (ball _ _ 0 (-1) rfl rfl (by norm_num)).2.1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hd0
  have hr0 : C.r = 0 :=
    Interval.aux_r_zero _ _ _ hr (by nlinarith) (by linarith) (by linarith)
  -- three corners lie on the segment: impossible
  obtain ⟨t1, -, -, d1⟩ := dist ![0, 0] (by simp)
  obtain ⟨t2, -, -, d2⟩ := dist ![1, 0] (by simp)
  obtain ⟨t3, -, -, d3⟩ := dist ![0, 1] (by simp)
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, hr0] at d1 d2 d3
  obtain ⟨e10, e11⟩ := Interval.aux_sq_zero _ _ d1
  obtain ⟨e20, e21⟩ := Interval.aux_sq_zero _ _ d2
  obtain ⟨e30, e31⟩ := Interval.aux_sq_zero _ _ d3
  exact Interval.aux_lines (C.g 0) (C.g 1) (t2 - t1) (t3 - t1)
    (by linarith) (by linarith) (by linarith)

/-- The face of a ball cut by a supporting hyperplane is one point: if `Σ aⱼ wⱼ = -q₁` with
`q₁ ≥ ‖a‖` and `‖w‖ ≤ 1`, then `w = -a / ‖a‖`. -/
theorem Interval.aux_face_unique {k : ℕ} (a u v : Fin k → ℝ) (q1 : ℝ)
    (hpos : 0 < ∑ j, a j ^ 2) (hq : Real.sqrt (∑ j, a j ^ 2) ≤ q1)
    (hu : ∑ j, u j ^ 2 ≤ 1) (hv : ∑ j, v j ^ 2 ≤ 1)
    (hau : q1 + ∑ j, a j * u j = 0) (hav : q1 + ∑ j, a j * v j = 0) :
    u = v := by -- --- PROOF ---
  -- `m = ‖a‖` and its basic facts
  set N := ∑ j, a j ^ 2 with hN
  set m := Real.sqrt N with hm
  have hm2 : m ^ 2 = N := Real.sq_sqrt hpos.le
  have hmpos : 0 < m := Real.sqrt_pos.mpr hpos
  -- on the face, `‖w m + a‖² ≤ 0`, so `w = -a / m`
  have key : ∀ w : Fin k → ℝ, ∑ j, w j ^ 2 ≤ 1 → q1 + ∑ j, a j * w j = 0 →
      ∀ j, w j * m + a j = 0 := by
    intro w hw hqw
    have hexp : ∑ j, (w j * m + a j) ^ 2 =
        m ^ 2 * ∑ j, w j ^ 2 + 2 * m * ∑ j, a j * w j + N := by
      rw [hN, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    have hle : ∑ j, (w j * m + a j) ^ 2 ≤ 0 := by
      rw [hexp]
      have h1 : ∑ j, a j * w j = -q1 := by linarith
      rw [h1]
      have : m ^ 2 * ∑ j, w j ^ 2 ≤ m ^ 2 * 1 :=
        mul_le_mul_of_nonneg_left hw (sq_nonneg m)
      nlinarith
    have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg _)).mp
      (le_antisymm hle (Finset.sum_nonneg fun j _ => sq_nonneg _))
    intro j
    exact pow_eq_zero_iff two_ne_zero |>.mp (hz j (Finset.mem_univ j))
  -- both `u` and `v` are `-a / m`
  funext j
  have h1 := key u hu hau j
  have h2 := key v hv hav j
  have : (u j - v j) * m = 0 := by linarith
  exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hmpos.ne')

/-- No ellipsoid is the unit square. -/
theorem Interval.aux_unitSquare_not_ellipsoid (E : Ellipsoid 2) :
    E.construct ≠ Interval.aux_unitSquare.construct := by -- --- PROOF ---
  intro h
  -- membership in the ellipsoid is membership in the square
  have hmem : ∀ x : Vec ℝ 2, x ∈ E.construct ↔
      (0 ≤ x 0 ∧ x 0 ≤ 1) ∧ (0 ≤ x 1 ∧ x 1 ≤ 1) := fun x => by
    rw [h]; exact Interval.aux_mem_unitSquare x
  -- a point of the ellipsoid, coordinatewise
  have coord : ∀ (x : Vec ℝ 2) (u : Vec ℝ 2), x = E.q + E.G.mulVec u → ∀ i,
      x i = E.q i + ∑ j, E.G i j * u j := by
    intro x u hx i
    rw [hx]
    simp [Matrix.mulVec, dotProduct]
  have sq_le : ∀ u : Vec ℝ 2, ‖u‖₂ ≤ 1 → ∑ j, u j ^ 2 ≤ 1 := by
    intro u hu
    rw [← norm₂_sq]
    nlinarith [norm₂_nonneg u]
  -- the corners `(0,0)`, `(1,0)`, `(0,1)` have preimages `u`, `v`, `u'`
  obtain ⟨u, hu, hxu⟩ := (hmem ![0, 0]).mpr (by simp)
  obtain ⟨v, hv, hxv⟩ := (hmem ![1, 0]).mpr (by simp)
  obtain ⟨u', hu', hxu'⟩ := (hmem ![0, 1]).mpr (by simp)
  have cu0 := coord _ u hxu 0
  have cu1 := coord _ u hxu 1
  have cv0 := coord _ v hxv 0
  have cv1 := coord _ v hxv 1
  have cw0 := coord _ u' hxu' 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at cu0 cu1 cv0 cv1 cw0
  -- either the second coordinate is constant on the ellipsoid, or it has a unique minimum
  by_cases hN : ∑ j, E.G 1 j ^ 2 = 0
  · -- the second coordinate is constant on the ellipsoid
    have hz : ∀ j, E.G 1 j = 0 := fun j =>
      pow_eq_zero_iff two_ne_zero |>.mp
        ((Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg _)).mp hN j
          (Finset.mem_univ j))
    simp [hz] at cu1 cw0
    linarith
  · have hpos : 0 < ∑ j, E.G 1 j ^ 2 :=
      lt_of_le_of_ne (Finset.sum_nonneg fun j _ => sq_nonneg _) (Ne.symm hN)
    -- `m = ‖a‖` for the row `a` of `G`
    set N := ∑ j, E.G 1 j ^ 2 with hNdef
    set m := Real.sqrt N with hm
    have hm2 : m ^ 2 = N := Real.sq_sqrt hpos.le
    have hmpos : 0 < m := Real.sqrt_pos.mpr hpos
    -- the point `q - G a / ‖a‖` is in the ellipsoid, so `q₁ ≥ ‖a‖`
    have hq : m ≤ E.q 1 := by
      let w : Vec ℝ 2 := fun j => -(E.G 1 j) / m
      -- `w` has norm `1`
      have hw : ‖w‖₂ ≤ 1 := by
        have : ∑ j, w j ^ 2 = 1 := by
          have : ∑ j, w j ^ 2 = N / m ^ 2 := by
            rw [hNdef, Finset.sum_div]
            exact Finset.sum_congr rfl fun j _ => by simp only [w]; rw [neg_div, neg_sq, div_pow]
          rw [this, hm2, div_self hpos.ne']
        unfold norm₂
        rw [this, Real.sqrt_one]
      -- its image has a non-negative second coordinate, `q₁ - m`
      have hmemw := (hmem (E.q + E.G.mulVec w)).mp ⟨w, hw, rfl⟩
      have c1 := coord _ w rfl 1
      have hdot : ∑ j, E.G 1 j * w j = -m := by
        have : ∑ j, E.G 1 j * w j = -(N / m) := by
          rw [hNdef, Finset.sum_div, ← Finset.sum_neg_distrib]
          exact Finset.sum_congr rfl fun j _ => by simp only [w]; ring
        rw [this]
        have : N / m = m := by rw [← hm2]; field_simp
        rw [this]
      have := hmemw.2.1
      rw [c1, hdot] at this
      linarith
    -- both corners sit on the minimal face, which is one point, so they coincide
    have huv := Interval.aux_face_unique (fun j => E.G 1 j) u v (E.q 1) hpos hq (sq_le u hu)
      (sq_le v hv) (by linarith) (by linarith)
    rw [huv] at cu0
    linarith

/-- CORA reports the unit square as a capsule (and as an ellipsoid), though no capsule is it. -/
theorem Interval.representsa_capsule_cora_counterexample :
    Interval.aux_unitSquare.representsaCapsuleCora = true ∧
      Interval.aux_unitSquare.representsaEllipsoidCora = true ∧
      (∀ C : Capsule 2, C.construct ≠ Interval.aux_unitSquare.construct) ∧
      (∀ E : Ellipsoid 2, E.construct ≠ Interval.aux_unitSquare.construct) := by -- --- PROOF ---
  have hrad : ∀ i, Interval.aux_unitSquare.radius i = 1 / 2 := by
    intro i
    fin_cases i <;> simp [Interval.radius, Interval.aux_unitSquare]
  refine ⟨?_, ?_, Interval.aux_unitSquare_not_capsule, Interval.aux_unitSquare_not_ellipsoid⟩
  · simp [Interval.representsaCapsuleCora, hrad]
  · simp [Interval.representsaEllipsoidCora, hrad]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
