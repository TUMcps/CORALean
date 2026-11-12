module

public import CORALean.Examples.DockingPolytopeFloat
public import CORALean.Examples.DockingPolytopeSubsetSafe
public import CORALean.ContSet.HPolytope.Float.Theorems.MemIneqsIff

@[expose] public section

/-!
# The float Docking polytope lies inside the safe set

For every sound scalar, the set of `dockingPolytopeFloat` is inside the safe set. Each rounded
coefficient is bracketed (`cosDown ≤ cos ≤ cosUp` at the rounded angle, the angle itself between
`angleDown` and `angleUp`), the largest error `maxErr` lowers `c` by `√2 · maxErr`, and
`dockingDist_le_of_row` finishes the row at the direction that
`exists_regularPolygon_dot_ge_of_abs_sub_le` picks. The tests of `certified` give `c > 0`,
`N > 0` and `n ≥ 0`.

## Inputs
* `p` – tuning of the sine, cosine and square root enclosures
* `k` – tuning of the arctangent enclosure
* `N` – number of sides
* `n` – mean motion

## Hypotheses
* none

## Conclusion
* the set of the polytope is inside the safe set of the Docking instance
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       12-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋]

namespace Docking

variable [SoundFloatArithmetic 𝕋]

/-- `piDown` is below `π`. -/
theorem piDown_le (p k : ℕ) : -- --- CONCL ---
    toReal (piDown p k : 𝕋) ≤ Real.pi := by -- --- PROOF ---
  set a : 𝕋 := atanDown p k one
  have h : toReal a ≤ Real.pi / 4 := by
    simpa [toReal_one, Real.arctan_one] using atanDown_le p k (one : 𝕋)
  have h1 := addDown_le_add a a
  have h2 := addDown_le_add (addDown a a) (addDown a a)
  simp only [piDown]; linarith

/-- `piUp` is above `π`. -/
theorem le_piUp (p k : ℕ) : -- --- CONCL ---
    Real.pi ≤ toReal (piUp p k : 𝕋) := by -- --- PROOF ---
  set a : 𝕋 := atanUp p k one
  have h : Real.pi / 4 ≤ toReal a := by
    simpa [toReal_one, Real.arctan_one] using le_atanUp p k (one : 𝕋)
  have h1 := add_le_addUp a a
  have h2 := add_le_addUp (addUp a a) (addUp a a)
  simp only [piUp]; linarith

/-- The angle `2π j / N` lies between `angleDown` and `angleUp`. -/
theorem angle_bounds (pD pU : 𝕋) (hPD : toReal pD ≤ Real.pi) (hPU : Real.pi ≤ toReal pU)
    (N j : ℕ) (hN : 0 < toReal (intDown N : 𝕋)) : -- --- CONCL ---
    toReal (angleDown pD N j : 𝕋) ≤ 2 * Real.pi * j / N ∧
      2 * Real.pi * j / N ≤ toReal (angleUp pU N j : 𝕋) := by -- --- PROOF ---
  have hpi := Real.pi_pos
  obtain ⟨hNle, hNge⟩ := intDown_le_intUp (𝕋 := 𝕋) N
  obtain ⟨hjle, hjge⟩ := intDown_le_intUp (𝕋 := 𝕋) j
  push_cast at hNle hNge hjle hjge
  have hN0 : (0 : ℝ) < N := lt_of_lt_of_le hN hNle
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  constructor
  · -- from below: the factors `2π` and `j` are clamped at `0` and the divisor is `intUp N`
    set TD : 𝕋 := maximum zero (addDown pD pD) with hTD
    have hTD' : toReal TD ≤ 2 * Real.pi := by
      have := addDown_le_add pD pD
      rw [hTD, toReal_maximum, toReal_zero]; exact max_le (by positivity) (by linarith)
    have hTD0 : 0 ≤ toReal TD := by rw [hTD, toReal_maximum, toReal_zero]; exact le_max_left _ _
    set JD : 𝕋 := maximum zero (intDown j) with hJD
    have hJD' : toReal JD ≤ j := by
      rw [hJD, toReal_maximum, toReal_zero]; exact max_le hj0 hjle
    have hJD0 : 0 ≤ toReal JD := by rw [hJD, toReal_maximum, toReal_zero]; exact le_max_left _ _
    have hm : toReal (mulDown TD JD) ≤ 2 * Real.pi * j :=
      (mulDown_le_mul TD JD).trans (mul_le_mul hTD' hJD' hJD0 (by positivity))
    have hNU : (0 : ℝ) < toReal (intUp N : 𝕋) := lt_of_lt_of_le hN0 hNge
    refine (divDown_le_div (mulDown TD JD) (intUp N : 𝕋) hNU).trans ?_
    by_cases hneg : toReal (mulDown TD JD) < 0
    · exact (div_neg_of_neg_of_pos hneg hNU).le.trans (by positivity)
    · rw [not_lt] at hneg
      calc toReal (mulDown TD JD) / toReal (intUp N : 𝕋) ≤ toReal (mulDown TD JD) / N :=
            div_le_div_of_nonneg_left hneg hN0 hNge
        _ ≤ 2 * Real.pi * j / N := div_le_div_of_nonneg_right hm hN0.le
  · -- from above: `2π` is `pU + pU`, the factor `j` is `intUp j` and the divisor `intDown N`
    set TU : 𝕋 := addUp pU pU with hTU
    have hTU' : 2 * Real.pi ≤ toReal TU := by have := add_le_addUp pU pU; rw [hTU]; linarith
    have hm : 2 * Real.pi * j ≤ toReal (mulUp TU (intUp j : 𝕋)) :=
      (mul_le_mul hTU' hjge hj0 (by linarith)).trans (mul_le_mulUp TU (intUp j : 𝕋))
    refine le_trans ?_ (div_le_divUp (mulUp TU (intUp j : 𝕋)) (intDown N : 𝕋) hN)
    calc 2 * Real.pi * j / N ≤ 2 * Real.pi * j / toReal (intDown N : 𝕋) :=
          div_le_div_of_nonneg_left (by positivity) hN hNle
      _ ≤ _ := div_le_div_of_nonneg_right hm hN.le

/-- The angle `π / N` lies between `halfDown` and `halfUp`. -/
theorem half_bounds (pD pU : 𝕋) (hPD : toReal pD ≤ Real.pi) (hPU : Real.pi ≤ toReal pU)
    (N : ℕ) (hN : 0 < toReal (intDown N : 𝕋)) : -- --- CONCL ---
    toReal (halfDown pD N : 𝕋) ≤ Real.pi / N ∧
      Real.pi / N ≤ toReal (halfUp pU N : 𝕋) := by -- --- PROOF ---
  have hpi := Real.pi_pos
  obtain ⟨hNle, hNge⟩ := intDown_le_intUp (𝕋 := 𝕋) N
  push_cast at hNle hNge
  have hN0 : (0 : ℝ) < N := lt_of_lt_of_le hN hNle
  have hNU : (0 : ℝ) < toReal (intUp N : 𝕋) := lt_of_lt_of_le hN0 hNge
  constructor
  · -- from below: `pD / intUp N`
    refine (divDown_le_div pD (intUp N : 𝕋) hNU).trans ?_
    by_cases hneg : toReal pD < 0
    · exact (div_neg_of_neg_of_pos hneg hNU).le.trans (by positivity)
    · rw [not_lt] at hneg
      calc toReal pD / toReal (intUp N : 𝕋) ≤ toReal pD / N :=
            div_le_div_of_nonneg_left hneg hN0 hNge
        _ ≤ Real.pi / N := div_le_div_of_nonneg_right hPD hN0.le
  · -- from above: `pU / intDown N`
    refine le_trans ?_ (div_le_divUp pU (intDown N : 𝕋) hN)
    calc Real.pi / N ≤ Real.pi / toReal (intDown N : 𝕋) :=
          div_le_div_of_nonneg_left hpi.le hN hNle
      _ ≤ _ := div_le_div_of_nonneg_right hPU hN.le

/-- The cosine coefficient is within `cosErr` of `cos (2π j / N)`. -/
theorem cos_coeff_err (p : ℕ) (pD pU : 𝕋) (hPD : toReal pD ≤ Real.pi)
    (hPU : Real.pi ≤ toReal pU) (N j : ℕ) (hN : 0 < toReal (intDown N : 𝕋)) : -- --- CONCL ---
    |toReal (cosDown p (angleUp pU N j) : 𝕋) - Real.cos (2 * Real.pi * j / N)| ≤
      toReal (cosErr p pD pU N j : 𝕋) := by -- --- PROOF ---
  obtain ⟨hlo, hhi⟩ := angle_bounds pD pU hPD hPU N j hN
  set a : 𝕋 := angleUp pU N j
  have h1 := sub_le_subUp a (angleDown pD N j)
  have h2 := sub_le_subUp (cosUp p a : 𝕋) (cosDown p a)
  have h3 := add_le_addUp (subUp (cosUp p a : 𝕋) (cosDown p a)) (subUp a (angleDown pD N j))
  have hc1 := cosDown_le p a
  have hc2 := le_cosUp p a
  -- the cosine moves by at most the angle
  have hl := abs_le.mp (Real.abs_cos_sub_cos_le (toReal a) (2 * Real.pi * j / N))
  rw [abs_of_nonneg (by linarith : 0 ≤ toReal a - 2 * Real.pi * j / N)] at hl
  simp only [cosErr]
  rw [abs_le]
  constructor <;> nlinarith [hl.1, hl.2]

/-- The sine coefficient is within `sinErr` of `sin (2π j / N)`. -/
theorem sin_coeff_err (p : ℕ) (pD pU : 𝕋) (hPD : toReal pD ≤ Real.pi)
    (hPU : Real.pi ≤ toReal pU) (N j : ℕ) (hN : 0 < toReal (intDown N : 𝕋)) : -- --- CONCL ---
    |toReal (sinDown p (angleUp pU N j) : 𝕋) - Real.sin (2 * Real.pi * j / N)| ≤
      toReal (sinErr p pD pU N j : 𝕋) := by -- --- PROOF ---
  obtain ⟨hlo, hhi⟩ := angle_bounds pD pU hPD hPU N j hN
  set a : 𝕋 := angleUp pU N j
  have h1 := sub_le_subUp a (angleDown pD N j)
  have h2 := sub_le_subUp (sinUp p a : 𝕋) (sinDown p a)
  have h3 := add_le_addUp (subUp (sinUp p a : 𝕋) (sinDown p a)) (subUp a (angleDown pD N j))
  have hc1 := sinDown_le p a
  have hc2 := le_sinUp p a
  -- the sine moves by at most the angle
  have hl := abs_le.mp (Real.abs_sin_sub_sin_le (toReal a) (2 * Real.pi * j / N))
  rw [abs_of_nonneg (by linarith : 0 ≤ toReal a - 2 * Real.pi * j / N)] at hl
  simp only [sinErr]
  rw [abs_le]
  constructor <;> nlinarith [hl.1, hl.2]

/-- `maxErr` is not negative. -/
theorem maxErr_nonneg (p : ℕ) (pD pU : 𝕋) (N : ℕ) : 0 ≤ toReal (maxErr p pD pU N : 𝕋) := by
  simp only [maxErr, toReal_maximum, toReal_zero]; exact le_max_left _ _

/-- `maxErr` bounds `cosErr`. -/
theorem cosErr_le_maxErr (p : ℕ) (pD pU : 𝕋) (N : ℕ) (j : Fin N) :
    toReal (cosErr p pD pU N j : 𝕋) ≤ toReal (maxErr p pD pU N : 𝕋) := by
  have h := le_maximumOver
    (fun j : Fin N => (maximum (cosErr p pD pU N j) (sinErr p pD pU N j) : 𝕋)) j
  simp only [maxErr, toReal_maximum] at h ⊢
  exact (le_max_left _ _).trans (h.trans (le_max_right _ _))

/-- `maxErr` bounds `sinErr`. -/
theorem sinErr_le_maxErr (p : ℕ) (pD pU : 𝕋) (N : ℕ) (j : Fin N) :
    toReal (sinErr p pD pU N j : 𝕋) ≤ toReal (maxErr p pD pU N : 𝕋) := by
  have h := le_maximumOver
    (fun j : Fin N => (maximum (cosErr p pD pU N j) (sinErr p pD pU N j) : 𝕋)) j
  simp only [maxErr, toReal_maximum] at h ⊢
  exact (le_max_right _ _).trans (h.trans (le_max_right _ _))

/-- `cosHalf` is below `cos(π/N) - √2 · maxErr`. -/
theorem cosHalf_le (p : ℕ) (pD pU : 𝕋) (hPD : toReal pD ≤ Real.pi)
    (hPU : Real.pi ≤ toReal pU) (N : ℕ) (hN : 0 < toReal (intDown N : 𝕋)) : -- --- CONCL ---
    toReal (cosHalf p pD pU N : 𝕋) ≤
      Real.cos (Real.pi / N) - √2 * toReal (maxErr p pD pU N : 𝕋) := by -- --- PROOF ---
  obtain ⟨hlo, hhi⟩ := half_bounds pD pU hPD hPU N hN
  set e : 𝕋 := maxErr p pD pU N
  set h : 𝕋 := halfUp pU N
  have h1 := sub_le_subUp h (halfDown pD N)
  have h2 := add_le_addUp e e
  have h3 := add_le_addUp (subUp h (halfDown pD N)) (addUp e e)
  have h4 := subDown_le_sub (cosDown p h : 𝕋) (addUp (subUp h (halfDown pD N)) (addUp e e))
  have h5 := cosDown_le p h
  -- the cosine moves by at most the angle
  have hl := abs_le.mp (Real.abs_cos_sub_cos_le (toReal h) (Real.pi / N))
  rw [abs_of_nonneg (by linarith : 0 ≤ toReal h - Real.pi / N)] at hl
  have h6 : √2 ≤ 2 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  have h8 : √2 * toReal e ≤ 2 * toReal e :=
    mul_le_mul_of_nonneg_right h6 (maxErr_nonneg p pD pU N)
  show toReal (subDown _ _) ≤ _
  linarith [hl.1, hl.2]

/-- `shrink` lies in `[0, 1]`. -/
theorem shrink_bounds : 0 ≤ toReal (shrink : 𝕋) ∧ toReal (shrink : 𝕋) ≤ 1 := by
  simp only [shrink, toReal_maximum, toReal_minimum, toReal_zero, toReal_one]
  exact ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

/-- A positive `radius` is below the positive `cosHalf`. -/
theorem radius_le_cosHalf (p : ℕ) (pD pU : 𝕋) (N : ℕ)
    (hr : 0 < toReal (radius p pD pU N : 𝕋)) : -- --- CONCL ---
    toReal (radius p pD pU N : 𝕋) ≤ toReal (cosHalf p pD pU N : 𝕋) ∧
      0 < toReal (cosHalf p pD pU N : 𝕋) := by -- --- PROOF ---
  obtain ⟨hs0, hs1⟩ := shrink_bounds (𝕋 := 𝕋)
  set κ := toReal (cosHalf p pD pU N : 𝕋)
  have h : toReal (radius p pD pU N : 𝕋) ≤ κ * toReal (shrink : 𝕋) :=
    mulDown_le_mul (cosHalf p pD pU N : 𝕋) (shrink : 𝕋)
  -- a nonpositive `κ` would make the product, and so the radius, nonpositive
  have hpos : 0 < κ := by
    by_contra hneg
    rw [not_lt] at hneg
    have := mul_nonpos_of_nonpos_of_nonneg hneg hs0
    exact absurd (lt_of_lt_of_le hr (h.trans this)) (lt_irrefl _)
  exact ⟨h.trans (by nlinarith), hpos⟩

/-- `slope` is between `0` and `c · 2n/√2`. -/
theorem slope_bounds (p : ℕ) (C n : 𝕋) (hr : 0 < toReal C) (hn : 0 ≤ toReal n) : -- --- CONCL ---
    0 ≤ toReal (slope p C n) ∧
      toReal (slope p C n) ≤ toReal C * (2 * toReal n / √2) := by -- --- PROOF ---
  obtain ⟨hs0, hs1⟩ := shrink_bounds (𝕋 := 𝕋)
  set c := toReal C with hc
  have h2 : (0 : ℝ) < √2 := Real.sqrt_pos.mpr two_pos
  -- the products `C · 2` and `C · 2 · n`, rounded down
  set M1 : 𝕋 := mulDown C (addDown one one) with hM1
  set M2 : 𝕋 := mulDown M1 n with hM2
  have ht := addDown_le_add (one : 𝕋) one
  rw [toReal_one] at ht
  have hm1 : toReal M1 ≤ c * 2 :=
    (mulDown_le_mul C (addDown one one : 𝕋)).trans
      (mul_le_mul_of_nonneg_left (by linarith) hr.le)
  have hm2 : toReal M2 ≤ c * 2 * toReal n :=
    (mulDown_le_mul M1 n).trans (mul_le_mul_of_nonneg_right hm1 hn)
  -- the divisor is at least `√2`
  set Q : 𝕋 := sqrtUp p (addUp (one : 𝕋) one) with hQ
  have hq1 := add_le_addUp (one : 𝕋) one
  rw [toReal_one] at hq1
  have hq2 : √2 ≤ toReal Q := (Real.sqrt_le_sqrt (by linarith)).trans (le_sqrtUp p _)
  have hq0 : 0 < toReal Q := lt_of_lt_of_le h2 hq2
  have hB : 0 ≤ c * (2 * toReal n / √2) := by positivity
  -- the quotient is below `c · 2n/√2`
  set M3 : 𝕋 := divDown M2 Q with hM3
  have hm3 : toReal M3 ≤ c * (2 * toReal n / √2) := by
    refine (divDown_le_div M2 Q hq0).trans ?_
    calc toReal M2 / toReal Q ≤ c * 2 * toReal n / toReal Q :=
          div_le_div_of_nonneg_right hm2 hq0.le
      _ ≤ c * 2 * toReal n / √2 := div_le_div_of_nonneg_left (by positivity) h2 hq2
      _ = _ := by ring
  -- and the shrink, a factor in `[0, 1]`, keeps it below
  have hm4 := mulDown_le_mul M3 (shrink : 𝕋)
  simp only [slope, toReal_maximum, toReal_zero]
  refine ⟨le_max_left _ _, max_le hB (hm4.trans ?_)⟩
  by_cases hm : 0 ≤ toReal M3
  · nlinarith
  · rw [not_le] at hm
    nlinarith

/-- `rhs` is below `0.2 c`. -/
theorem rhs_le (C : 𝕋) (hr : 0 < toReal C) : -- --- CONCL ---
    toReal (rhs C) ≤ 1 / 5 * toReal C := by -- --- PROOF ---
  -- the divisor `((1 + 1) + (1 + 1)) + 1` is at least `5`
  set F : 𝕋 := addUp (addUp (addUp (one : 𝕋) one) (addUp one one)) one with hF
  have h1 := add_le_addUp (one : 𝕋) one
  have h2 := add_le_addUp (addUp (one : 𝕋) one) (addUp (one : 𝕋) one)
  have h3 := add_le_addUp (addUp (addUp (one : 𝕋) one) (addUp (one : 𝕋) one)) one
  rw [toReal_one] at h1 h3
  have h5 : 5 ≤ toReal F := by rw [hF]; linarith
  have h5' : 0 < toReal F := by linarith
  have hd : toReal (divDown (one : 𝕋) F) ≤ 1 / 5 := by
    have := divDown_le_div (one : 𝕋) F h5'
    rw [toReal_one] at this
    exact this.trans (one_div_le_one_div_of_le (by norm_num) h5)
  simp only [rhs]
  exact (mulDown_le_mul (divDown (one : 𝕋) F) C).trans (mul_le_mul_of_nonneg_right hd hr.le)

end Docking


-- =======================================  MAIN THEOREM  ======================================= --

/-- The set of the float Docking polytope is inside the safe set, whatever the scalar. -/
theorem dockingPolytopeFloat_subset_safe [SoundFloatArithmetic 𝕋]
    (p k N : ℕ) (n : 𝕋) : -- --- CONCL ---
    (dockingPolytopeFloat p k N n).toSet ⊆ dockingSafeSet (toReal n) := by -- --- PROOF ---
  intro x hx
  set pD : 𝕋 := Docking.piDown p k with hpD
  set pU : 𝕋 := Docking.piUp p k with hpU
  have hPD : toReal pD ≤ Real.pi := Docking.piDown_le p k
  have hPU : Real.pi ≤ toReal pU := Docking.le_piUp p k
  unfold dockingPolytopeFloat at hx
  simp only [] at hx
  split_ifs at hx with hc
  · -- the tests passed: `N > 0`, `c > 0` and `n ≥ 0`
    rw [HPolytope.mem_ineqs_iff] at hx
    simp only [Docking.certified, Bool.and_eq_true] at hc
    obtain ⟨⟨hN, hr⟩, hn⟩ := hc
    have hN' : 0 < toReal (intDown N : 𝕋) := by
      have := toReal_lt_of_ltStrict hN; rwa [toReal_zero] at this
    have hr' : 0 < toReal (Docking.radius p pD pU N : 𝕋) := by
      have := toReal_lt_of_ltStrict hr; rwa [toReal_zero] at this
    have hn' : 0 ≤ toReal n := by
      have := toReal_le_of_le hn; rwa [toReal_zero] at this
    have hNle := (intDown_le_intUp (𝕋 := 𝕋) N).1
    push_cast at hNle
    have hNpos : 0 < N := by
      have : (0 : ℝ) < N := lt_of_lt_of_le hN' hNle
      exact_mod_cast this
    -- the bounds on `c`, `w` and `0.2 c`
    obtain ⟨hrc, hκ⟩ := Docking.radius_le_cosHalf p pD pU N hr'
    obtain ⟨hw0, hw⟩ := Docking.slope_bounds (𝕋 := 𝕋) p _ n hr' hn'
    have hβ := Docking.rhs_le _ hr'
    have hκle := Docking.cosHalf_le p pD pU hPD hPU N hN'
    -- a direction of the polygon within half a step of `v`, with the coefficient errors
    set ε := toReal (Docking.maxErr p pD pU N : 𝕋)
    obtain ⟨j, hj⟩ := exists_regularPolygon_dot_ge_of_abs_sub_le hNpos (ε := ε)
      (fun j : Fin N => toReal (cosDown p (Docking.angleUp pU N j) : 𝕋))
      (fun j : Fin N => toReal (sinDown p (Docking.angleUp pU N j) : 𝕋))
      (fun j => (Docking.cos_coeff_err p pD pU hPD hPU N j hN').trans
        (Docking.cosErr_le_maxErr p pD pU N j))
      (fun j => (Docking.sin_coeff_err p pD pU hPD hPU N j hN').trans
        (Docking.sinErr_le_maxErr p pD pU N j))
      (x 2) (x 3)
    have hrow := hx j
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four, toRealMat,
      SoundFloatArithmetic.toReal_neg] at hrow
    have hV : 0 ≤ √(x 2 ^ 2 + x 3 ^ 2) := Real.sqrt_nonneg _
    have hdot : toReal (Docking.cosHalf p pD pU N : 𝕋) * √(x 2 ^ 2 + x 3 ^ 2) ≤
        toReal (cosDown p (Docking.angleUp pU N j) : 𝕋) * x 2 +
          toReal (sinDown p (Docking.angleUp pU N j) : 𝕋) * x 3 :=
      (mul_le_mul_of_nonneg_right hκle hV).trans hj
    exact dockingDist_le_of_row hn' hκ hrc hw0 hw hβ hdot (by linarith)
  · -- the tests failed: the polytope is the row `0 ≤ -1`, which has no point
    rw [HPolytope.mem_ineqs_iff] at hx
    have h0 := hx 0
    simp [Matrix.mulVec, dotProduct, toRealMat, toReal_zero, SoundFloatArithmetic.toReal_neg,
      toReal_one] at h0
    exact absurd h0 (by norm_num)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
