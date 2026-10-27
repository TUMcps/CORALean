module

public import CORALean.Global.Brouwer
public import CORALean.Global.CoordinateGain
public import CORALean.Global.CoordinatePathOff
public import Mathlib.Analysis.Calculus.ContDiff.Basic

@[expose] public section

/-!
# Boxes inside the range of a vector-valued function from mean-value AE extensions

[1, Thm. 3]: for `f : ℝᵐ → ℝⁿ` and `π : {1, …, m} → {1, …, n}`, the product of the mean-value AE
extensions of [1, Thm. 2] of the components, component `i` having the inputs `π⁻¹(i)` existential
and every other input universal, is inside `range(f, x)`. [1, Remark 1] leaves some inputs out of
`π`, the disturbances: they stay universal and the product is inside the robust range. Both are
the case of this file's theorem, which solves `f(x) = z` for the inputs in the image of `π`. The
proof is [1]'s Brouwer argument with the continuous selections replaced by one the hypotheses give
directly: where `∇̲ⱼ > 0` the inputs of `π⁻¹(i)` lie on a segment from a corner to the opposite one
(`exists_coord_ends_gain`), and a fixed point of `τ ↦ clamp(τ + z - f(x(τ)))` solves `f(x(τ)) = z`.

## Inputs
* `f` – function from inputs to components
* `π` – assignment of inputs to components, none for disturbances
* `lo` – lower corner of the input box
* `hi` – upper corner of the input box
* `f0lo` – lower bounds on the center values
* `f0hi` – upper bounds on the center values
* `dwhi` – upper bounds on the partials of the uncontrolled inputs
* `dulo` – lower bounds on the partials of the controlled inputs
* `z` – target point in the product of inner intervals
* `w` – prescribed value of the disturbance inputs

## Hypotheses
* `hlh` – the input box is nonempty
* `hf` – every component is continuously differentiable
* `hf0` – the center values lie within their bounds
* `hw` – the uncontrolled partials are bounded above on the path sets
* `hu` – the controlled partials are bounded below
* `hz` – the target lies in the product of the inner intervals
* `hw'` – the prescribed disturbance lies in the box

## Conclusion
* a box point with the prescribed disturbance maps to the target

## References

* [1] [E. Goubault and S. Putot. "Robust Under-Approximations and Application to Reachability of
      Non-Linear Control Systems With Disturbances". IEEE Control Systems Letters,
      2020.](../../../references/2020/goubault-lcss-robust-underapproximations.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Set

variable {m n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Thm. 3] and [1, Remark 1]: a point of the product of the `Thm. 2` inner intervals is
`f(x)` for an `x` in the box with the inputs outside the image of `π` (`π j = none`) at any
prescribed `w`; `dulo`, `dwhi` bound `|∂ⱼfᵢ|` below on `π j = some i` and above elsewhere. -/
theorem exists_eq_of_mean_value_box {f : (Fin m → ℝ) → Fin n → ℝ} {π : Fin m → Option (Fin n)}
    {lo hi : Fin m → ℝ} (hlh : lo ≤ hi) (hf : ∀ i, ContDiff ℝ 1 fun x => f x i)
    {f0lo f0hi : Fin n → ℝ}
    (hf0 : ∀ i, f (fun j => (lo j + hi j) / 2) i ∈ Icc (f0lo i) (f0hi i))
    (dwhi dulo : Fin n → Fin m → ℝ)
    (hw : ∀ i, ∀ y ∈ Icc lo hi, (∀ j, π j = some i → y j = (lo j + hi j) / 2) →
      ∀ j, π j ≠ some i → |fderiv ℝ (fun x => f x i) y (Pi.single j 1)| ≤ dwhi i j)
    (hu : ∀ i, ∀ y ∈ Icc lo hi, ∀ j, π j = some i →
      dulo i j ≤ |fderiv ℝ (fun x => f x i) y (Pi.single j 1)|)
    {z : Fin n → ℝ}
    (hz : z ∈ Icc
      (fun i => f0hi i - ∑ j with π j = some i, dulo i j * ((hi j - lo j) / 2)
        + ∑ j with π j ≠ some i, dwhi i j * ((hi j - lo j) / 2))
      (fun i => f0lo i + ∑ j with π j = some i, dulo i j * ((hi j - lo j) / 2)
        - ∑ j with π j ≠ some i, dwhi i j * ((hi j - lo j) / 2)))
    {w : Fin m → ℝ} (hw' : w ∈ Icc lo hi) : -- --- CONCL ---
    ∃ x ∈ Icc lo hi, (∀ j, π j = none → x j = w j) ∧ f x = z := by -- --- PROOF ---
  classical
  set c : Fin m → ℝ := fun j => (lo j + hi j) / 2 with hc
  have hcm : c ∈ Icc lo hi := ⟨fun j => by simp only [hc]; linarith [hlh j],
    fun j => by simp only [hc]; linarith [hlh j]⟩
  -- the two corners of every existential input of every component
  have hends : ∀ i j, ∃ a b : ℝ, π j = some i →
      (a ∈ Icc (lo j) (hi j) ∧ b ∈ Icc (lo j) (hi j) ∧
      (∀ p ∈ Icc lo hi, f (Function.update p j (c j)) i + dulo i j * ((hi j - lo j) / 2)
        ≤ f (Function.update p j b) i) ∧
      (∀ p ∈ Icc lo hi, f (Function.update p j a) i + dulo i j * ((hi j - lo j) / 2)
        ≤ f (Function.update p j (c j)) i)) := by
    intro i j
    by_cases h : π j = some i
    · obtain ⟨a, ha, b, hb, h1, h2⟩ := exists_coord_ends_gain (hf i) hlh j (dulo i j)
        (fun y hy => hu i y hy j h)
      exact ⟨a, b, fun _ => ⟨ha, hb, h1, h2⟩⟩
    · exact ⟨0, 0, fun h' => absurd h' h⟩
  choose a b hab using hends
  -- component `i` on its segment from corner `a` (`τ i = 0`) to `b` (`τ i = 1`), the rest at `w`
  let X : (Fin n → ℝ) → Fin m → ℝ := fun τ j =>
    (π j).elim (w j) fun i => a i j + τ i * (b i j - a i j)
  -- the inputs outside `π` are at `w`, those of `π⁻¹(i)` on the segment of `i`
  have hXnone : ∀ τ j, π j = none → X τ j = w j := fun τ j h => by simp [X, h]
  have hXsome : ∀ τ i j, π j = some i → X τ j = a i j + τ i * (b i j - a i j) :=
    fun τ i j h => by simp [X, h]
  -- it is continuous in `τ`, and stays in the box for `τ ∈ [0, 1]ⁿ`
  have hXcont : Continuous X := continuous_pi fun j => by
    rcases h : π j with _ | i
    · simp only [X, h, Option.elim_none]; exact continuous_const
    · simp only [X, h, Option.elim_some]
      exact continuous_const.add (((continuous_apply i).mul continuous_const))
  have hXmem : ∀ τ ∈ Icc (0 : Fin n → ℝ) 1, X τ ∈ Icc lo hi := fun τ hτ => by
    refine ⟨fun j => ?_, fun j => ?_⟩
    -- lower bounds
    · rcases h : π j with _ | i
      · simp only [X, h, Option.elim_none]; exact hw'.1 j
      · simp only [X, h, Option.elim_some]
        obtain ⟨ha, hb, -⟩ := hab i j h
        have := hτ.1 i; have := hτ.2 i
        simp only [Pi.zero_apply, Pi.one_apply] at *
        nlinarith [ha.1, hb.1, ha.2, hb.2]
    -- upper bounds
    · rcases h : π j with _ | i
      · simp only [X, h, Option.elim_none]; exact hw'.2 j
      · simp only [X, h, Option.elim_some]
        obtain ⟨ha, hb, -⟩ := hab i j h
        have := hτ.1 i; have := hτ.2 i
        simp only [Pi.zero_apply, Pi.one_apply] at *
        nlinarith [ha.1, hb.1, ha.2, hb.2]
  -- the sums of the interval ends
  have hsumE : ∀ (g : Fin m → ℝ) (i : Fin n), ∑ j, (if π j = some i then g j else 0)
      = ∑ j with π j = some i, g j := fun g i => (Finset.sum_filter _ _).symm
  -- at the upper end of its segment, component `i` is at least the upper end of its interval
  have hup : ∀ τ ∈ Icc (0 : Fin n → ℝ) 1, ∀ i, τ i = 1 →
      f0lo i + ∑ j with π j = some i, dulo i j * ((hi j - lo j) / 2)
        - ∑ j with π j ≠ some i, dwhi i j * ((hi j - lo j) / 2) ≤ f (X τ) i := by
    intro τ hτ i hτi
    -- move the inputs of `π⁻¹(i)` to the center and back to the corner, one at a time
    set x₀ : Fin m → ℝ := fun j => if π j = some i then c j else X τ j with hx₀
    have hx₀m : x₀ ∈ Icc lo hi := ⟨fun j => by
        by_cases h : π j = some i
        · simp only [hx₀, h, if_true]; exact hcm.1 j
        · simp only [hx₀, h, if_false]; exact (hXmem τ hτ).1 j, fun j => by
        by_cases h : π j = some i
        · simp only [hx₀, h, if_true]; exact hcm.2 j
        · simp only [hx₀, h, if_false]; exact (hXmem τ hτ).2 j⟩
    have hgain := le_of_coord_gain (f := fun y => f y i) hx₀m (hXmem τ hτ)
      (fun j => if π j = some i then dulo i j * ((hi j - lo j) / 2) else 0) (fun j p hp => by
        by_cases h : π j = some i
        · have hxj : X τ j = b i j := by
            rw [hXsome τ i j h, hτi]; ring
          simp only [hx₀, h, if_true, hxj]
          exact (hab i j h).2.2.1 p hp
        · simp [hx₀, h])
    rw [hsumE (fun j => dulo i j * ((hi j - lo j) / 2)) i] at hgain
    -- the disturbances move `fᵢ` from the center by at most `⟨∇̄w, r⟩`
    have hb := abs_le.mp (abs_sub_le_sum_filter_of_abs_partial_le
      ((hf i).differentiable one_ne_zero) hlh (fun j => π j = some i) (dwhi i)
      (fun y hy hyE j hj => hw i y hy hyE j hj) hx₀m (fun j hj => by simp [hx₀, hj, hc]))
    linarith [(hf0 i).1]
  -- at the lower end of its segment, it is at most the lower end of its interval
  have hdn : ∀ τ ∈ Icc (0 : Fin n → ℝ) 1, ∀ i, τ i = 0 →
      f (X τ) i ≤ f0hi i - ∑ j with π j = some i, dulo i j * ((hi j - lo j) / 2)
        + ∑ j with π j ≠ some i, dwhi i j * ((hi j - lo j) / 2) := by
    intro τ hτ i hτi
    -- move the inputs of `π⁻¹(i)` to the center and back to the corner, one at a time
    set x₀ : Fin m → ℝ := fun j => if π j = some i then c j else X τ j with hx₀
    have hx₀m : x₀ ∈ Icc lo hi := ⟨fun j => by
        by_cases h : π j = some i
        · simp only [hx₀, h, if_true]; exact hcm.1 j
        · simp only [hx₀, h, if_false]; exact (hXmem τ hτ).1 j, fun j => by
        by_cases h : π j = some i
        · simp only [hx₀, h, if_true]; exact hcm.2 j
        · simp only [hx₀, h, if_false]; exact (hXmem τ hτ).2 j⟩
    have hgain := le_of_coord_gain (f := fun y => - f y i) hx₀m (hXmem τ hτ)
      (fun j => if π j = some i then dulo i j * ((hi j - lo j) / 2) else 0) (fun j p hp => by
        by_cases h : π j = some i
        · have hxj : X τ j = a i j := by
            rw [hXsome τ i j h, hτi]; ring
          simp only [hx₀, h, if_true, hxj]
          linarith [(hab i j h).2.2.2 p hp]
        · simp [hx₀, h])
    rw [hsumE (fun j => dulo i j * ((hi j - lo j) / 2)) i] at hgain
    -- the disturbances move `fᵢ` from the center by at most `⟨∇̄w, r⟩`
    have hb := abs_le.mp (abs_sub_le_sum_filter_of_abs_partial_le
      ((hf i).differentiable one_ne_zero) hlh (fun j => π j = some i) (dwhi i)
      (fun y hy hyE j hj => hw i y hy hyE j hj) hx₀m (fun j hj => by simp [hx₀, hj, hc]))
    linarith [(hf0 i).2]
  -- Brouwer on the parameters
  have hΦc : Continuous fun τ : Fin n → ℝ => fun i =>
      max 0 (min 1 (τ i + z i - f (X τ) i)) := continuous_pi fun i =>
    continuous_const.max (continuous_const.min (((continuous_apply i).add continuous_const).sub
      (((hf i).continuous).comp hXcont)))
  obtain ⟨τ, hτ, hfix⟩ := exists_fixedPoint_of_isCompact_convex (K := Icc (0 : Fin n → ℝ) 1)
    isCompact_Icc (convex_Icc _ _) ⟨0, le_rfl, fun _ => zero_le_one⟩ hΦc.continuousOn
    (f := fun τ i => max 0 (min 1 (τ i + z i - f (X τ) i)))
    (fun τ _ => ⟨fun i => le_max_left _ _, fun i => max_le zero_le_one (min_le_left _ _)⟩)
  refine ⟨X τ, hXmem τ hτ, fun j h => hXnone τ j h, funext fun i => ?_⟩
  have hi' := congrFun hfix i
  have hzl := hz.1 i
  have hzu := hz.2 i
  rcases le_total (τ i + z i - f (X τ) i) 0 with h0 | h0
  · -- clamped at zero
    rw [min_eq_right (by linarith), max_eq_left h0] at hi'
    linarith [hdn τ hτ i hi'.symm]
  · rcases le_total 1 (τ i + z i - f (X τ) i) with h1 | h1
    · rw [min_eq_left h1, max_eq_right zero_le_one] at hi'
      linarith [hup τ hτ i hi'.symm]
    · rw [min_eq_right h1, max_eq_right h0] at hi'
      linarith

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
