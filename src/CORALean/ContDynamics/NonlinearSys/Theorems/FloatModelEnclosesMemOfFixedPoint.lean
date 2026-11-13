module

public import CORALean.ContDynamics.NonlinearSys.Definitions.FloatModel
public import CORALean.ContDynamics.NonlinearSys.Theorems.IsTrajectoryMemOfFixedPoint
public import CORALean.ContSet.Conversion.Float.Theorems.ZonotopeIntervalContains
public import CORALean.ContSet.Interval.Float.Theorems.MemPoint
public import CORALean.ContSet.Zonotope.Float.Instances
public import CORALean.ContSet.Zonotope.Float.Theorems.IsCompact
public import CORALean.ContSet.Zonotope.Float.Theorems.MemNominalSet

@[expose] public section

/-!
# A closed set in a zonotope that holds the dominated runs holds the run of the enclosed system

`IsTrajectory.mem_of_fixedPoint` needs the field Lipschitz in the state near the set `K`. For a
system enclosed by a float model, `Encloses.slope_mem` gives it on any box: take the box of a
zonotope `Rbox` that holds `K`, joined with `x✱`, widened by `1` on every side. This is the
Lipschitz bound and the neighborhood for the adaptive theorems, whose set `K` is the window of a
linear step (`Rmax`) or, for polynomial zonotopes, its decomposition `x✱ + Rdelta + Rdiff`.

## Inputs
* `fm` – float model
* `sys` – system
* `Δt` – window length
* `R` – start set
* `V` – input set of the linear step
* `K` – set holding the dominated runs
* `U` – input zonotope
* `Rbox` – zonotope holding `K`
* `A` – state matrix
* `xs` – expansion point
* `x` – state signal
* `u` – input signal
* `y` – output signal

## Hypotheses
* `h` – model encloses system
* `hΔt` – window length nonnegative
* `hVb` – `V` bounded
* `hVne` – `V` nonempty
* `hKc` – `K` closed
* `hKR` – `Rbox` holds `K`
* `hdom` – `K` holds every run of every system whose field less `A (x - x✱)` stays in `V`
* `hK` – the field of `sys` less `A (x - x✱)` lies in `V` on `K`
* `traj` – `x` is a run of `sys` from `R` under inputs in `U`

## Conclusion
* the run stays in `K`
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       12-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps SoundFloatArithmetic ContSet ContSetLike Matrix

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The slope matrices of a box bound the field's change in the state, over the box. -/
private theorem aux_fp_lipschitz {fm : NonlinearSys.FloatModel 𝕋 n m} {sys : NonlinearSys n m}
    (h : fm.Encloses sys) (X : Interval (Vec 𝕋 n))
    (Ub : Interval (Vec 𝕋 m)) : -- --- CONCL ---
    ∃ L : ℝ, 0 ≤ L ∧ ∀ y ∈ X.toSet, ∀ y' ∈ X.toSet, ∀ v ∈ Ub.toSet,
      ‖sys.f y v - sys.f y' v‖ ≤ L * ‖y - y'‖ := by -- --- PROOF ---
  set M := fm.jacX X Ub with hM
  set S : ℝ := ∑ i, ∑ k, (|toReal (M.inf i k)| + |toReal (M.sup i k)|) with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun k _ => by positivity
  refine ⟨n * S, by positivity, fun y hy y' hy' v hv => ?_⟩
  obtain ⟨Jx, hJx, Ju, -, hslope⟩ := h.slope_mem X Ub y hy y' hy' v hv v hv
  rw [hslope, sub_self, Matrix.mulVec_zero, add_zero]
  -- every entry of `Jx` is at most `S`
  have hent : ∀ i k, |Jx i k| ≤ S := by
    intro i k
    obtain ⟨h1, h2⟩ := Interval.mem_mat_iff.mp hJx i k
    have hle : |Jx i k| ≤ |toReal (M.inf i k)| + |toReal (M.sup i k)| := by
      rw [abs_le]
      constructor
      · linarith [neg_abs_le (toReal (M.inf i k)), abs_nonneg (toReal (M.sup i k))]
      · linarith [le_abs_self (toReal (M.sup i k)), abs_nonneg (toReal (M.inf i k))]
    -- and a single term is at most the double sum
    refine hle.trans ?_
    calc |toReal (M.inf i k)| + |toReal (M.sup i k)|
        ≤ ∑ k', (|toReal (M.inf i k')| + |toReal (M.sup i k')|) :=
          Finset.single_le_sum (f := fun k' => |toReal (M.inf i k')| + |toReal (M.sup i k')|)
            (fun k' _ => by positivity) (Finset.mem_univ k)
      _ ≤ S := Finset.single_le_sum (f := fun i' => ∑ k', (|toReal (M.inf i' k')| +
            |toReal (M.sup i' k')|)) (fun i' _ => Finset.sum_nonneg fun k' _ => by positivity)
            (Finset.mem_univ i)
  -- each row of `Jx (y - y')` is at most `n S ‖y - y'‖`
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => ?_
  rw [Real.norm_eq_abs]
  calc |(Jx *ᵥ (y - y')) i| = |∑ k, Jx i k * (y - y') k| := rfl
    _ ≤ ∑ k, |Jx i k * (y - y') k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : Fin n, S * ‖y - y'‖ := Finset.sum_le_sum fun k _ => by
        rw [abs_mul]
        exact mul_le_mul (hent i k) (by simpa using norm_le_pi_norm (y - y') k) (abs_nonneg _) hS0
    _ = n * S * ‖y - y'‖ := by simp [mul_assoc]

/-- A point of a box is in the interior of the box widened by `1` on every side. -/
private theorem aux_fp_ball {X : Interval (Vec 𝕋 n)} {y : Vec ℝ n}
    (hy : y ∈ X.toSet) : -- --- CONCL ---
    Metric.ball y 1 ⊆ (⟨fun i => subDown (X.inf i) one, fun i => addUp (X.sup i) one⟩ :
      Interval (Vec 𝕋 n)).toSet := by -- --- PROOF ---
  intro z hz i
  have hd : |z i - y i| < 1 := by
    have := dist_le_pi_dist z y i
    rw [Real.dist_eq] at this
    exact lt_of_le_of_lt this (Metric.mem_ball.mp hz)
  obtain ⟨hd1, hd2⟩ := abs_lt.mp hd
  have r1 := subDown_le_sub (X.inf i) one
  have r2 := add_le_addUp (X.sup i) one
  rw [toReal_one] at r1 r2
  have hy1 : toReal (X.inf i) ≤ y i := (hy i).1
  have hy2 : y i ≤ toReal (X.sup i) := (hy i).2
  exact ⟨by show toReal (subDown (X.inf i) one) ≤ z i; linarith,
    by show z i ≤ toReal (addUp (X.sup i) one); linarith⟩


-- =======================================  MAIN THEOREM  ======================================= --

/-- A closed set in a zonotope, holding every run of every system dominated by the linear step
with input `V`, holds every run of an enclosed system whose field less `A (x - x✱)` lies in `V` on
the set. -/
theorem NonlinearSys.FloatModel.Encloses.mem_of_fixedPoint
    {fm : NonlinearSys.FloatModel 𝕋 n m} {sys : NonlinearSys n m} (h : fm.Encloses sys)
    {Δt : ℝ} (hΔt : 0 ≤ Δt) {R V K : Set (Vec ℝ n)} {U : Zonotope (Vec 𝕋 m)}
    (Rbox : Zonotope (Vec 𝕋 n)) (A : Mat ℝ n n) (xs : Vec 𝕋 n)
    (hVb : Bornology.IsBounded V) (hVne : V.Nonempty) (hKc : IsClosed K)
    (hKR : K ⊆ Rbox.toSet)
    (hdom : ∀ (m' : ℕ) (sys' : NonlinearSys n m') (U' : Set (Vec ℝ m')) (x' : ℝ → Vec ℝ n)
        (u' : ℝ → Vec ℝ m') (y' : ℝ → Vec ℝ sys'.q),
        sys'.IsTrajectory (S := ExactSet) (Set.Icc 0 Δt) R U' x' u' y' →
        (∀ t ∈ Set.Icc 0 Δt, sys'.f (x' t) (u' t) - A *ᵥ (x' t - toRealVec xs) ∈ V) →
        ∀ t ∈ Set.Icc 0 Δt, x' t ∈ K)
    (hK : ∀ y ∈ K, ∀ v ∈ U.toSet, sys.f y v - A *ᵥ (y - toRealVec xs) ∈ V)
    {x : ℝ → Vec ℝ n} {u : ℝ → Vec ℝ m} {y : ℝ → Vec ℝ sys.q}
    (traj : sys.IsTrajectory (S := ExactSet) (Set.Icc 0 Δt) R U.toSet x u y) : -- --- CONCL ---
    ∀ t ∈ Set.Icc 0 Δt, x t ∈ K := by -- --- PROOF ---
  -- the box of `Rbox` joined with `x✱`, widened by `1`, is where the field is Lipschitz
  set X : Interval (Vec 𝕋 n) := ⟨fun i => minimum (Rbox.interval.inf i) (xs i),
    fun i => maximum (Rbox.interval.sup i) (xs i)⟩ with hX
  have hKX : Rbox.toSet ⊆ X.toSet := fun y hy i => by
    obtain ⟨h1, h2⟩ := Zonotope.interval_contains Rbox hy i
    show toReal (minimum (Rbox.interval.inf i) (xs i)) ≤ y i ∧
      y i ≤ toReal (maximum (Rbox.interval.sup i) (xs i))
    rw [toReal_minimum, toReal_maximum]
    exact ⟨min_le_of_left_le h1, le_max_of_le_left h2⟩
  obtain ⟨L, hL0, hL⟩ := aux_fp_lipschitz h
    (⟨fun i => subDown (X.inf i) one, fun i => addUp (X.sup i) one⟩ : Interval (Vec 𝕋 n))
    U.interval
  exact NonlinearSys.IsTrajectory.mem_of_fixedPoint (sys := sys) hΔt (K := K) A (toRealVec xs)
    hVb hVne hKc (fun y hy => aux_fp_ball (hKX (hKR hy))) hL0
    (fun y hy y' hy' v hv => hL y hy y' hy' v (Zonotope.interval_contains U hv)) hdom hK traj

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
