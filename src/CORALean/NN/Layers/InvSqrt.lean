import CORALean.NN.Layers.Curvature

/-!
# The inverse square root, clamped at the degree bound the self-loop gives

CORA's `nnInvSqrtRootLayer`: a graph convolutional network normalises by
`D̃⁻ᐟ² Ã D̃⁻ᐟ²`, `D̃` the degree matrix of `Ã = A + I`. The self-loop puts every
degree at `1` or above, so `x ↦ x^(-1/2)` is only ever evaluated at or above `1` —
which is what makes `invSqrt` total: it clamps its argument at `1` first, a
clamp that costs nothing exactly because `1` is the bound already guaranteed.

Two relaxations, kept together because neither dominates. `invSqrtRelaxationRange`
is `ofAntitone`, total and cheap. `invSqrtRelaxationDeriv` adds a derivative
bracket from `1 ≤ l` up, and not merely from `1 < l`: `invSqrt` has a kink at `1`
— derivative `0` from the left, `-1/2` from the right — so no global derivative
exists for `Relaxation.ofDeriv`, but at `l = 1` the kink sits at the box's left
end, where the bracket asks only for continuity. That box is the common one: a
node whose only fixed edge is its self-loop has degree exactly `1`. Below `1` the
box straddles the kink and the range bound takes over. On a wide box the bracket
loses to the range (`[1,5]`: 0.91 against 0.28), on a narrow one it wins, and
`Relaxation.tighter` takes whichever is smaller.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

/-- The inverse square root, clamped below at the degree bound `1` the self-loop
guarantees, which is what makes it total. -/
noncomputable def invSqrt (x : ℝ) : ℝ := (Real.sqrt (max x 1))⁻¹

/-- The agreement with the unclamped function above the clamp point — the
whole reason this file exists rather than using `(Real.sqrt ·)⁻¹` directly. -/
theorem invSqrt_eq_of_one_le {x : ℝ} (hx : 1 ≤ x) : invSqrt x = (Real.sqrt x)⁻¹ := by
  unfold invSqrt
  rw [max_eq_left hx]

theorem invSqrt_pos (x : ℝ) : 0 < invSqrt x := by
  unfold invSqrt
  have : (0 : ℝ) < max x 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  positivity

theorem invSqrt_le_one (x : ℝ) : invSqrt x ≤ 1 := by -- --- PROOF ---
  unfold invSqrt
  rw [inv_le_one_iff₀]
  right
  rw [Real.le_sqrt' (by norm_num)]
  simp

theorem antitone_invSqrt : Antitone invSqrt := by
  intro a b hab
  unfold invSqrt
  gcongr

/-- Ties the name to the paper's notation, once `1 ≤ x` licenses reading the
clamp away. -/
theorem invSqrt_eq_rpow {x : ℝ} (hx : 1 ≤ x) : invSqrt x = x ^ (-(1 / 2) : ℝ) := by
  rw [invSqrt_eq_of_one_le hx, Real.sqrt_eq_rpow, ← Real.rpow_neg (by linarith : (0 : ℝ) ≤ x)]

/-- Continuous everywhere, the clamp included: `max x 1` never reaches zero, so
the square root it feeds never does either. -/
theorem continuous_invSqrt : Continuous invSqrt := by
  have h : Continuous fun x : ℝ => Real.sqrt (max x 1) :=
    Real.continuous_sqrt.comp (continuous_id.max continuous_const)
  refine h.inv₀ fun x => ne_of_gt (Real.sqrt_pos.mpr ?_)
  exact lt_of_lt_of_le one_pos (le_max_right _ _)

/-- Above the clamp the function is `(Real.sqrt ·)⁻¹`, whose derivative
`Real.hasDerivAt_sqrt` and `HasDerivAt.inv` give; `heq` moves it across the
agreement on a neighbourhood of `x`, all of it above `1`. -/
theorem hasDerivAt_invSqrt {x : ℝ} (hx : 1 < x) :
    HasDerivAt invSqrt (-(2 * x * Real.sqrt x)⁻¹) x := by -- --- PROOF ---
  have heq : invSqrt =ᶠ[nhds x] (fun y => (Real.sqrt y)⁻¹) := by
    filter_upwards [eventually_gt_nhds hx] with y hy
    rw [invSqrt_eq_of_one_le hy.le]
  rw [heq.hasDerivAt_iff]
  have hxpos : (0 : ℝ) < x := by linarith
  have hxne : x ≠ 0 := hxpos.ne'
  have hd := (Real.hasDerivAt_sqrt hxne).inv (Real.sqrt_ne_zero'.mpr hxpos)
  have hval : -(1 / (2 * Real.sqrt x)) / Real.sqrt x ^ 2 = -(2 * x * Real.sqrt x)⁻¹ := by
    rw [Real.sq_sqrt hxpos.le]
    field_simp
  rwa [hval] at hd

/-- Total and sound on every box, on nothing but `antitone_invSqrt` — already an
enclosure a network can propagate through. -/
noncomputable def invSqrtRelaxationRange : Relaxation invSqrt :=
  Relaxation.ofAntitone antitone_invSqrt


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The derivative's lower end on a box starting at `l`: least negative at the
box's own right end is where `x√x` is smallest, i.e. at `l`. -/
noncomputable def aux_invSqrtDerivLo (l : ℝ) : ℝ := -(2 * l * Real.sqrt l)⁻¹

/-- The derivative's upper end, symmetric in `u`. -/
noncomputable def aux_invSqrtDerivHi (u : ℝ) : ℝ := -(2 * u * Real.sqrt u)⁻¹

/-- `y ↦ -(2 y √y)⁻¹` rises toward `0`, since `y √y` itself rises: the bracket
`[lo l, hi u]` is nonempty exactly because `l ≤ u`. -/
theorem aux_invSqrtDeriv_mono {l u : ℝ} (hl : 0 < l) (hlu : l ≤ u) :
    aux_invSqrtDerivLo l ≤ aux_invSqrtDerivHi u := by -- --- PROOF ---
  unfold aux_invSqrtDerivLo aux_invSqrtDerivHi
  have hupos : (0 : ℝ) < u := hl.trans_le hlu
  have hprod : l * Real.sqrt l ≤ u * Real.sqrt u :=
    mul_le_mul hlu (Real.sqrt_le_sqrt hlu) (Real.sqrt_nonneg l) hupos.le
  have hlpos : (0 : ℝ) < l * Real.sqrt l := by positivity
  gcongr

/-- The mean-value bracket from the clamp point up, the midpoint of
`[lo l, hi u]` as its slope; below it the range bound, sound everywhere. -/
noncomputable def invSqrtRelaxationDeriv : Relaxation invSqrt where
  slope l u := if 1 ≤ l then (aux_invSqrtDerivLo l + aux_invSqrtDerivHi u) / 2
      else invSqrtRelaxationRange.slope l u
  offset l u := if 1 ≤ l then invSqrt l - (aux_invSqrtDerivLo l + aux_invSqrtDerivHi u) / 2 * l
      else invSqrtRelaxationRange.offset l u
  error l u := if 1 ≤ l then (aux_invSqrtDerivHi u - aux_invSqrtDerivLo l) * (u - l) / 2
      else invSqrtRelaxationRange.error l u
  sound {l u t} hl hu := by
    by_cases hl1 : 1 ≤ l
    · -- from the clamp point up: the mean value theorem against the derivative bracket
      rw [if_pos hl1, if_pos hl1, if_pos hl1]
      have hlam := aux_invSqrtDeriv_mono (l := l) (u := u) (by linarith) (le_trans hl hu)
      obtain ⟨h₁, h₂⟩ := sub_mul_bounds_of_deriv
        (σ := invSqrt) (σ' := fun x => -(2 * x * Real.sqrt x)⁻¹)
        (lam := (aux_invSqrtDerivLo l + aux_invSqrtDerivHi u) / 2)
        continuous_invSqrt.continuousOn
        (fun x hxl _ => hasDerivAt_invSqrt (lt_of_le_of_lt hl1 hxl))
        (fun x hxl _ => aux_invSqrtDeriv_mono (l := l) (u := x) (by linarith) hxl)
        (fun x _ hxu => aux_invSqrtDeriv_mono (l := x) (u := u) (by linarith) hxu)
        (by linarith) (by linarith) hl hu
      rw [abs_le]
      exact ⟨by nlinarith [h₁], by nlinarith [h₂]⟩
    · -- below the clamp: the box straddles the kink, so fall back
      rw [if_neg hl1, if_neg hl1, if_neg hl1]
      exact invSqrtRelaxationRange.sound hl hu


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The smaller error of the two at each box, both sound everywhere so the
choice is free: the plain range on a wide box, the derivative bracket once it
is tight enough to pay for itself. -/
noncomputable def invSqrtRelaxation : Relaxation invSqrt :=
  Relaxation.tighter invSqrtRelaxationRange invSqrtRelaxationDeriv

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
