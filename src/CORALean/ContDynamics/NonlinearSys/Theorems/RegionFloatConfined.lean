module

public import CORALean.ContDynamics.NonlinearSys.Operations.RegionFloat
public import CORALean.ContDynamics.NonlinearSys.Theorems.ConfinedOfBall
public import Mathlib.Analysis.Calculus.Deriv.Prod

@[expose] public section

/-!
# A run stays in the box `regionFloat` returns

Two arguments, one after the other. `confined_of_ball` keeps the run in the
inflated box `X ⊕ [-δ, δ]`, which holds a sup-norm ball of radius `δ > MΔt`
about every state of `X`. Inside it the field lies in the model's box `F`, so
each coordinate moves at a rate in `[F_i⁻, F_i⁺]`; the mean value inequality,
applied to the coordinate minus its mid rate, keeps it in
`X_i + [min(0, ΔtF_i⁻), max(0, ΔtF_i⁺)]` — the Picard step, taken twice.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps SoundFloatArithmetic ContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `maximumOver` of non-negative entries is non-negative, at every length. -/
theorem aux_maximumOver_nonneg : ∀ {k : ℕ} (g : Fin k → 𝕋), (∀ i, 0 ≤ toReal (g i)) →
    0 ≤ toReal (maximumOver g) := by
  intro k
  cases k with
  | zero => intro _ _; rw [maximumOver, toReal_zero]
  | succ k => exact fun g hg => le_trans (hg 0) (le_maximumOver g 0)

/-- The sup norm of a point of a box is at most the box's `bound`. -/
theorem aux_norm_le_bound {I : Interval (Vec 𝕋 n)} {y : Vec ℝ n} (hy : y ∈ I.construct) :
    ‖y‖ ≤ toReal (maximumOver fun i => maximum (absolute (I.inf i)) (absolute (I.sup i)))
      := by -- --- PROOF ---
  have hnn := aux_maximumOver_nonneg (fun i => maximum (absolute (I.inf i)) (absolute (I.sup i)))
    fun i => by rw [toReal_maximum, toReal_absolute]; exact le_max_of_le_left (abs_nonneg _)
  refine (pi_norm_le_iff_of_nonneg hnn).mpr fun i => ?_
  refine le_trans ?_ (le_maximumOver _ i)
  rw [Real.norm_eq_abs, toReal_maximum, toReal_absolute, toReal_absolute]
  exact abs_le_max_abs_abs (hy i).1 (hy i).2

/-- One Picard step: a run in `Ω` over `[a, a + Δt]`, from `X` at `a`, is in
`X ⊕ [0, Δt] f(Ω × U)` over the same window. -/
theorem aux_picard {fm : NonlinearSys.FloatModel 𝕋 n m} {sys : NonlinearSys n m}
    (h : fm.Encloses sys) {Δt : 𝕋} {X Ω : Interval (Vec 𝕋 n)}
    {Ub : Interval (Vec 𝕋 m)} {T : Set ℝ} {R₀ : Set (Vec ℝ n)} {U : Set (Vec ℝ m)}
    {x : ℝ → Vec ℝ n} {u : ℝ → Vec ℝ m}
    (traj : sys.IsTrajectory (S := 𝒮) T R₀ U x u)
    (hU : U ⊆ Ub.construct) {a : ℝ} (hT : Set.Icc a (a + toReal Δt) ⊆ T)
    (hxa : x a ∈ X.construct) (hΩ : ∀ t ∈ Set.Icc a (a + toReal Δt), x t ∈ Ω.construct) :
    ∀ t ∈ Set.Icc a (a + toReal Δt), x t ∈ (⟨fun i => addDown (X.inf i)
        (minimum zero (mulDown Δt ((fm.f Ω Ub).inf i))), fun i => addUp (X.sup i)
        (maximum zero (mulUp Δt ((fm.f Ω Ub).sup i)))⟩ :
          Interval (Vec 𝕋 n)).construct := by -- --- PROOF ---
  intro t ht i
  set lo := toReal ((fm.f Ω Ub).inf i)
  set hi := toReal ((fm.f Ω Ub).sup i)
  -- the field's coordinate stays in `[lo, hi]` over the window
  have hF : ∀ s ∈ Set.Icc a (a + toReal Δt), lo ≤ sys.f (x s) (u s) i ∧ sys.f (x s) (u s) i ≤ hi :=
    fun s hs => h.f_mem Ω Ub _ (hΩ s hs) _ (hU (traj.input s (hT hs))) i
  -- the coordinate minus its mid rate moves at most `(hi - lo)/2` per unit time
  have hd : ∀ s ∈ Set.Icc a (a + toReal Δt), HasDerivWithinAt
      (fun r => (x r i : ℝ) - (lo + hi) / 2 * r) ((sys.f (x s) (u s) i : ℝ) - (lo + hi) / 2)
      (Set.Icc a (a + toReal Δt)) s := fun s hs => by
    have hx : HasDerivWithinAt (fun r => (x r i : ℝ)) (sys.f (x s) (u s) i : ℝ)
        (Set.Icc a (a + toReal Δt)) s := hasDerivWithinAt_pi.mp ((traj.flow s (hT hs)).mono hT) i
    have hc := ((hasDerivAt_id s).const_mul ((lo + hi) / 2)).hasDerivWithinAt
      (s := Set.Icc a (a + toReal Δt))
    rw [mul_one] at hc
    exact hx.sub hc
  have hb := norm_image_sub_le_of_norm_deriv_le_segment' hd (C := (hi - lo) / 2)
    (fun s hs => by
      obtain ⟨h1, h2⟩ := hF s (Set.Ico_subset_Icc_self hs)
      rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith) t ht
  rw [Real.norm_eq_abs, abs_le] at hb
  -- so the coordinate moved by between `(t - a) lo` and `(t - a) hi`
  obtain ⟨ht1, ht2⟩ := ht
  obtain ⟨hb1, hb2⟩ := hb
  set xt : ℝ := x t i
  set xa : ℝ := x a i
  have hxa1 : toReal (X.inf i) ≤ xa := (hxa i).1
  have hxa2 : xa ≤ toReal (X.sup i) := (hxa i).2
  have hlo : xa + (t - a) * lo ≤ xt := by nlinarith
  have hhi : xt ≤ xa + (t - a) * hi := by nlinarith
  -- the two faces, each rounding outward
  constructor
  · have r1 := addDown_le_add (X.inf i) (minimum zero (mulDown Δt ((fm.f Ω Ub).inf i)))
    have r2 := mulDown_le_mul Δt ((fm.f Ω Ub).inf i)
    rw [toReal_minimum, toReal_zero] at r1
    have hmin : min 0 (toReal Δt * lo) ≤ (t - a) * lo := by
      rcases le_total 0 lo with hl | hl
      · exact le_trans (min_le_left _ _) (mul_nonneg (by linarith) hl)
      · exact le_trans (min_le_right _ _) (by nlinarith)
    have hm := min_le_min_left 0 r2
    show toReal (addDown (X.inf i) (minimum zero (mulDown Δt ((fm.f Ω Ub).inf i)))) ≤ xt
    linarith
  -- the upper face
  · have r1 := add_le_addUp (X.sup i) (maximum zero (mulUp Δt ((fm.f Ω Ub).sup i)))
    have r2 := mul_le_mulUp Δt ((fm.f Ω Ub).sup i)
    rw [toReal_maximum, toReal_zero] at r1
    have hmax : (t - a) * hi ≤ max 0 (toReal Δt * hi) := by
      rcases le_total 0 hi with hl | hl
      · exact le_trans (by nlinarith) (le_max_right _ _)
      · exact le_trans (mul_nonpos_of_nonneg_of_nonpos (by linarith) hl) (le_max_left _ _)
    have hm := max_le_max_left 0 r2
    show xt ≤ toReal (addUp (X.sup i) (maximum zero (mulUp Δt ((fm.f Ω Ub).sup i))))
    linarith


-- =======================================  MAIN THEOREM  ======================================= --

/-- Where `fm` encloses `sys`, a run under inputs in `Ub` that starts a window of
length `Δt` in `X` stays, over the whole window, in the box `regionFloat` returns. -/
theorem NonlinearSys.FloatModel.Encloses.regionFloat_confined
    {fm : NonlinearSys.FloatModel 𝕋 n m} {sys : NonlinearSys n m} (h : fm.Encloses sys)
    {Δt : 𝕋} {X Ω : Interval (Vec 𝕋 n)} {Ub : Interval (Vec 𝕋 m)}
    (hΩ : fm.regionFloat Δt X Ub = some Ω) (hΔt : 0 ≤ toReal Δt) {T : Set ℝ}
    {R₀ : Set (Vec ℝ n)} {U : Set (Vec ℝ m)} {x : ℝ → Vec ℝ n} {u : ℝ → Vec ℝ m}
    (traj : sys.IsTrajectory (S := 𝒮) T R₀ U x u)
    (hU : U ⊆ Ub.construct) {a : ℝ} (hT : Set.Icc a (a + toReal Δt) ⊆ T)
    (hxa : x a ∈ X.construct) :
    ∀ t ∈ Set.Icc a (a + toReal Δt), x t ∈ Ω.construct := by -- --- PROOF ---
  -- the check passed, and `Ω` is the twice-refined box
  rw [NonlinearSys.FloatModel.regionFloat] at hΩ
  split_ifs at hΩ with hlt
  obtain rfl := Option.some.inj hΩ
  set M₀ := maximumOver fun i => maximum (absolute ((fm.f X Ub).inf i))
    (absolute ((fm.f X Ub).sup i))
  set δ := mulUp (addUp (addUp M₀ M₀) one) Δt
  set Ω₀ : Interval (Vec 𝕋 n) := ⟨fun i => subDown (X.inf i) δ, fun i => addUp (X.sup i) δ⟩
  set M := maximumOver fun i => maximum (absolute ((fm.f Ω₀ Ub).inf i))
    (absolute ((fm.f Ω₀ Ub).sup i))
  have hM₀ : 0 ≤ toReal M := aux_maximumOver_nonneg _ fun i => by
    rw [toReal_maximum, toReal_absolute]; exact le_max_of_le_left (abs_nonneg _)
  -- the field's bound over `Ω₀`, and the strict margin `MΔt < δ`
  have hM : ∀ y ∈ (Ω₀.construct : Set (Vec ℝ n)), ∀ v ∈ construct U, ‖sys.f y v‖ ≤ toReal M :=
    fun y hy v hv => aux_norm_le_bound (h.f_mem Ω₀ Ub y hy v (hU hv))
  have hρ : toReal M * (a + toReal Δt - a) < toReal δ := by
    rw [add_sub_cancel_left]
    exact lt_of_le_of_lt (mul_le_mulUp _ _) (toReal_lt_of_ltStrict hlt)
  -- the ball of radius `δ` about `x a` lies in `Ω₀`
  have hball : Metric.closedBall (x a) (toReal δ) ⊆ Ω₀.construct := by
    intro y hy i
    have hd : ‖y - x a‖ ≤ toReal δ := by
      rw [← dist_eq_norm]; exact Metric.mem_closedBall.mp hy
    have hyi : |(y i : ℝ) - x a i| ≤ toReal δ := by
      have := (norm_le_pi_norm (y - x a) i).trans hd
      rwa [Real.norm_eq_abs] at this
    -- each face of `Ω₀` is `δ` beyond `X`'s, rounded outward
    obtain ⟨h1, h2⟩ := abs_le.mp hyi
    have r1 := subDown_le_sub (X.inf i) δ
    have r2 := add_le_addUp (X.sup i) δ
    have hx1 : toReal (X.inf i) ≤ (x a i : ℝ) := (hxa i).1
    have hx2 : (x a i : ℝ) ≤ toReal (X.sup i) := (hxa i).2
    exact ⟨by show toReal (subDown (X.inf i) δ) ≤ (y i : ℝ); linarith,
      by show (y i : ℝ) ≤ toReal (addUp (X.sup i) δ); linarith⟩
  have hcoarse := traj.confined_of_ball (by linarith) hT hM₀ hM hρ hball
  exact aux_picard h traj hU hT hxa (aux_picard h traj hU hT hxa hcoarse)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
