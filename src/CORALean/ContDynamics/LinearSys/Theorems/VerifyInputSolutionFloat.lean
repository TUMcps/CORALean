module

public import CORALean.ContDynamics.LinearSys.Operations.VerifyInputSolutionFloat
public import CORALean.ContDynamics.LinearSys.Theorems.ExistsEqTaylorAddOfMemInputReach
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.AbsParticularTailEntryLe
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.PowDownFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.PowUpFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ScaledRemainderFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.VerifyPowerFloat
public import CORALean.ContSet.Interval.Float.Theorems.Basic
public import CORALean.ContSet.Interval.Float.Theorems.MatMulOuter
public import CORALean.ContSet.Interval.Float.Theorems.SmulOuter
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-!
# `LinearSys.verifyInputSolutionFloat` encloses one step of the input

With `u₀` in its box and `M` in its box, and `Pᵢ = Δt^{i+1}/(i+1)! Aⁱ` (`MatExp.particularCoeff`):
every `Pᵢ M` is in its box `Vᵢ` and their sum in `Vs`; `PG = (∫₀^Δt e^{sA} ds) M` is within `ρ_l`
of that sum in row `l` (the tail past order `η - 1`, `MatExp.abs_particularTail_entry_le`, under
the scaled remainder `W`); every contribution of an input in `M [-1, 1]^m` over the step is
`Σᵢ Pᵢ M bᵢ` plus a vector within `ρ` (`LinearSys.exists_eq_taylor_add_of_mem_inputReach`); and the
constant input's solution `(∫₀^Δt e^{sA} ds) u₀` is in `w`. The search returns the orders
`0, …, η - 1` in their order, `η ≥ 1`.

## Inputs
* `sys` – linear system
* `s` – positive float scales
* `Δt` – float step length
* `u₀` – float box of the constant input
* `M` – float box of the generators
* `u0r` – constant input
* `Mr` – generator matrix

## Hypotheses
* `hs` – scales positive
* `hΔt` – step length positive
* `hu` – the constant input lies in its box
* `hM` – the generator matrix lies in its box

## Conclusion
* the orders, their sum, the remainder and the varying input's contributions, and the constant
  input's solution, each in its box
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps SoundFloatArithmetic Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m k : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A fold of `addUp` from `a` is at least `a` plus the exact sum. -/
private theorem LinearSys.aux_le_foldl_up {α : Type} (f : α → 𝕋) : -- --- CONCL ---
    ∀ (L : List α) (a : 𝕋),
      toReal a + (L.map fun X => toReal (f X)).sum
        ≤ toReal (L.foldl (fun acc X => addUp acc (f X)) a) := by -- --- PROOF ---
  intro L
  induction L with
  | nil => intro a; simp
  | cons X L ih =>
    intro a
    simp only [List.map_cons, List.sum_cons, List.foldl_cons]
    have h := ih (addUp a (f X))
    linarith [add_le_addUp a (f X)]

/-- A fold of `addDown` from `a` is at most `a` plus the exact sum. -/
private theorem LinearSys.aux_foldl_down_le {α : Type} (f : α → 𝕋) : -- --- CONCL ---
    ∀ (L : List α) (a : 𝕋),
      toReal (L.foldl (fun acc X => addDown acc (f X)) a)
        ≤ toReal a + (L.map fun X => toReal (f X)).sum := by -- --- PROOF ---
  intro L
  induction L with
  | nil => intro a; simp
  | cons X L ih =>
    intro a
    simp only [List.map_cons, List.sum_cons, List.foldl_cons]
    have h := ih (addDown a (f X))
    linarith [addDown_le_add a (f X)]

/-- Members of a list of boxes sum into the box of the folded bounds. -/
private theorem LinearSys.aux_sum_mem_fold (L : List (Interval (Mat 𝕋 n k)))
    (Y : Fin L.length → Mat ℝ n k) (hY : ∀ i, Y i ∈ (L[i.1]).toSet) (l : Fin n) (c
        : Fin k) : -- --- CONCL ---
    toReal (L.foldl (fun acc (X : Interval (Mat 𝕋 n k)) => addDown acc (X.inf l c)) FloatOps.zero)
        ≤ (∑ i, Y i) l c
      ∧ (∑ i, Y i) l c
        ≤ toReal (L.foldl (fun acc (X : Interval (Mat 𝕋 n k)) => addUp acc (X.sup l c))
          FloatOps.zero) := by -- --- PROOF ---
  have hup := LinearSys.aux_le_foldl_up (fun X : Interval (Mat 𝕋 n k) => X.sup l c) L zero
  have hdn := LinearSys.aux_foldl_down_le (fun X : Interval (Mat 𝕋 n k) => X.inf l c) L zero
  rw [toReal_zero, zero_add, ← Fin.sum_univ_fun_getElem] at hup hdn
  rw [Matrix.sum_apply]
  exact ⟨le_trans hdn (Finset.sum_le_sum fun i _ => (Interval.mem_mat_iff.mp (hY i) l c).1),
    le_trans (Finset.sum_le_sum fun i _ => (Interval.mem_mat_iff.mp (hY i) l c).2) hup⟩

/-- The order's coefficient `Δt^{i+1}/(i+1)` lies between its float bounds. -/
private theorem LinearSys.aux_coeff {Δt : 𝕋} (hΔt : 0 < toReal Δt) (i : ℕ) : -- --- CONCL ---
    toReal (divDown (MatExp.powDown (i + 1) Δt) (nsmulUp (i + 1) one))
        ≤ toReal Δt ^ (i + 1) / ((i : ℝ) + 1)
      ∧ toReal Δt ^ (i + 1) / ((i : ℝ) + 1)
        ≤ toReal (divUp (MatExp.powUp (i + 1) Δt) (maximum one (nsmulDown (i + 1)
            one))) := by -- --- PROOF ---
  have hk0 : (0 : ℝ) < (i : ℝ) + 1 := by positivity
  have hp0 : 0 ≤ toReal Δt ^ (i + 1) := pow_nonneg hΔt.le _
  -- the divisors: `dHi ≥ i + 1`, `1 ≤ dLo ≤ i + 1`
  have hdHi : (i : ℝ) + 1 ≤ toReal (nsmulUp (i + 1) (one : 𝕋)) := by
    have h := le_nsmulUp (i + 1) (one : 𝕋)
    rw [toReal_one, mul_one] at h
    exact_mod_cast h
  -- the lower divisor: `1 ≤ dLo ≤ i + 1`
  set dLo : 𝕋 := maximum one (nsmulDown (i + 1) one)
  have hd1 : 1 ≤ toReal dLo := by rw [toReal_maximum, toReal_one]; exact le_max_left _ _
  have hdk : toReal dLo ≤ (i : ℝ) + 1 := by
    have h := nsmulDown_le (i + 1) (one : 𝕋)
    rw [toReal_one, mul_one] at h
    rw [toReal_maximum, toReal_one]
    exact max_le (by linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)]) (by exact_mod_cast h)
  have hd0 : 0 < toReal dLo := by linarith
  have hH0 : 0 < toReal (nsmulUp (i + 1) (one : 𝕋)) := by linarith
  -- the two bounds, by the bracketed power over the bracketed divisor
  constructor
  · refine le_trans (divDown_le_div _ _ hH0) ?_
    have hpd := MatExp.powDown_le hΔt.le (i + 1)
    rcases le_total (toReal (MatExp.powDown (i + 1) Δt)) 0 with hneg | hpos
    · exact le_trans (div_nonpos_of_nonpos_of_nonneg hneg hH0.le) (div_nonneg hp0 hk0.le)
    · exact le_trans (div_le_div_of_nonneg_left hpos hk0 hdHi)
        (div_le_div_of_nonneg_right hpd hk0.le)
  · refine le_trans ?_ (div_le_divUp _ _ hd0)
    have hpu := MatExp.le_powUp hΔt.le (i + 1)
    exact le_trans (div_le_div_of_nonneg_left hp0 hd0 hdk)
      (div_le_div_of_nonneg_right hpu hd0.le)

/-- Order `i`'s boxes hold `Pᵢ u₀` and `Pᵢ M`. -/
private theorem LinearSys.aux_order_mem (A : Mat 𝕋 n n) {Δt : 𝕋} (hΔt : 0 < toReal Δt)
    {u₀ : Interval (Mat 𝕋 n 1)} {M : Interval (Mat 𝕋 n m)} {u0r : Mat ℝ n 1} (hu : u0r ∈ u₀.toSet)
    {Mr : Mat ℝ n m} (hM : Mr ∈ M.toSet) (i : ℕ) : -- --- CONCL ---
    Real.MatExp.particularCoeff (toRealMat A) (toReal Δt) i * u0r
        ∈ (LinearSys.step_verifyInputOrderFloat A Δt u₀ M i).1.toSet
      ∧ Real.MatExp.particularCoeff (toRealMat A) (toReal Δt) i * Mr
        ∈ (LinearSys.step_verifyInputOrderFloat A Δt u₀ M i).2.toSet := by -- --- PROOF ---
  obtain ⟨hlo, hhi⟩ := LinearSys.aux_coeff hΔt i
  have hT := Interval.smul_outer hlo hhi (MatExp.verifyPowerFloat A i)
    (MatExp.pow_div_factorial_mem_verifyPowerFloat A i)
  have hP : (toReal Δt ^ (i + 1) / ((i : ℝ) + 1)) • ((Nat.factorial i : ℝ)⁻¹ • toRealMat A ^ i)
      = Real.MatExp.particularCoeff (toRealMat A) (toReal Δt) i := by
    rw [Real.MatExp.particularCoeff, smul_smul]
    congr 1
    rw [Nat.factorial_succ]
    have h1 : ((i : ℝ) + 1) ≠ 0 := by positivity
    have h2 : (Nat.factorial i : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero i)
    push_cast
    field_simp
  rw [hP] at hT
  unfold LinearSys.step_verifyInputOrderFloat
  simp only [Interval.materialiseMat_eq]
  exact ⟨Interval.matMul_outer _ _ hT hu, Interval.matMul_outer _ _ hT hM⟩

omit [SoundFloatArithmetic 𝕋] in
/-- The search returns the orders `0, …, η - 1`, `η ≥ 1`, from orders `0, …, i - 1` so far. -/
private theorem LinearSys.aux_search (A : Mat 𝕋 n n) (Δt : 𝕋) (u₀ : Interval (Mat 𝕋 n 1))
    (M : Interval (Mat 𝕋 n m)) : -- --- CONCL ---
    ∀ fuel i acc S η O, LinearSys.step_verifyInputSearchFloat A Δt u₀ M fuel i acc S = some (η, O) →
      acc.reverse = (List.range i).map (LinearSys.step_verifyInputOrderFloat A Δt u₀ M) →
      O = (List.range η).map (LinearSys.step_verifyInputOrderFloat A Δt u₀ M) ∧ 1
          ≤ η := by -- --- PROOF ---
  intro fuel
  induction fuel with
  | zero => intro i acc S η O h; simp [LinearSys.step_verifyInputSearchFloat] at h
  | succ fuel ih =>
    intro i acc S η O h hacc
    rw [LinearSys.step_verifyInputSearchFloat] at h
    split_ifs at h with hstop
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨hacc, ?_⟩
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hstop
      exact hstop.1
    · refine ih _ _ _ η O h ?_
      rw [List.reverse_cons, hacc, List.range_succ, List.map_append, List.map_singleton]


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.verifyInputSolutionFloat_mem (sys : LinearSys 𝕋 n) {s : Vec 𝕋 n}
    (hs : ∀ i, 0 < toReal (s i)) {Δt : 𝕋} (hΔt : 0 < toReal Δt) {u₀ : Interval (Mat 𝕋 n 1)}
    {M : Interval (Mat 𝕋 n m)} {u0r : Mat ℝ n 1} (hu : u0r ∈ u₀.toSet) {Mr : Mat ℝ n m}
    (hM : Mr ∈ M.toSet) : -- --- CONCL ---
    ∀ sol ∈ LinearSys.verifyInputSolutionFloat sys.A s Δt u₀ M,
      Real.MatExp.expIntegral (toRealMat sys.A) (toReal Δt) * u0r ∈ sol.w.toSet ∧
      ∃ X : Fin sol.V.length → Mat ℝ n m, (∀ i, X i ∈ (sol.V[i.1]).toSet) ∧
        (∑ i, X i) ∈ sol.Vs.toSet ∧
        (∀ l, ∑ c, |(Real.MatExp.expIntegral (toRealMat sys.A) (toReal Δt) * Mr) l c
          - (∑ i, X i) l c| ≤ toReal (sol.ρ l)) ∧
        ∀ z ∈ sys.inputReach (S := ExactSet) ((fun β => Mr *ᵥ β) '' Set.Icc (-1) 1) (toReal Δt),
          ∃ b : Fin sol.V.length → Fin m → ℝ, (∀ i c, |b i c| ≤ 1) ∧ ∃ y : Vec ℝ n,
            (∀ l, |y l| ≤ toReal (sol.ρ l)) ∧ z = (∑ i, X i *ᵥ b i) + y := by -- --- PROOF ---
  intro sol hsol
  set A := toRealMat sys.A with hA
  set ord := LinearSys.step_verifyInputOrderFloat sys.A Δt u₀ M
  rw [Option.mem_def] at hsol
  unfold LinearSys.verifyInputSolutionFloat at hsol
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at hsol
  obtain ⟨⟨η, O⟩, hsearch, W, hW, rfl⟩ := hsol
  obtain ⟨hO, hη⟩ := LinearSys.aux_search sys.A Δt u₀ M 75 0 [] _ η O hsearch (by simp)
  simp only at hW
  simp only [Interval.materialiseMat_eq, Interval.materialise_eq, Interval.point]
  -- the remainder: `|R_lk| ≤ Δt W_lk`, `R` the tail of `∫₀^Δt e^{sA} ds` past the orders `i < η`
  set R := Real.MatExp.expIntegral A (toReal Δt)
    - ∑ i ∈ Finset.range η, Real.MatExp.particularCoeff A (toReal Δt) i with hR
  have hRle : ∀ l j, |R l j| ≤ toReal Δt * toReal (W l j) := by
    intro l j
    have h := Real.MatExp.abs_particularTail_entry_le A hΔt.le (η - 1) l j
    rw [show η - 1 + 1 = η by omega] at h
    exact le_trans h (mul_le_mul_of_nonneg_left
      (MatExp.expRemainderMat_le_scaledRemainderFloat sys.A hs hΔt.le (η - 1) W
        (Option.mem_def.mpr hW) l j) hΔt.le)
  have hW0 : ∀ l j, 0 ≤ toReal (W l j) := fun l j =>
    nonneg_of_mul_nonneg_right (le_trans (abs_nonneg _) (hRle l j)) hΔt
  -- `|R x|_l ≤ Δt Σ_j W_lj Σ_c |x_jc|`, rounded up
  have hRx : ∀ {k' : ℕ} (x : Mat ℝ n k') (mx : Fin n → 𝕋)
      (hmx : ∀ j, ∑ c, |x j c| ≤ toReal (mx j)) (l : Fin n),
      ∑ c, |(R * x) l c| ≤ toReal (mulUp Δt (sumUp fun j => mulUp (W l j) (mx j))) := by
    intro k' x mx hmx l
    have h1 : ∑ c, |(R * x) l c| ≤ ∑ j, |R l j| * ∑ c, |x j c| := by
      simp only [Matrix.mul_apply]
      refine le_trans (Finset.sum_le_sum fun c _ => Finset.abs_sum_le_sum_abs _ _) ?_
      rw [Finset.sum_comm]
      refine le_of_eq (Finset.sum_congr rfl fun j _ => ?_)
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun c _ => abs_mul _ _
    -- `|R| ≤ Δt W` entrywise, then the float sums above the exact ones
    refine le_trans h1 (le_trans ?_ (mul_le_mulUp _ _))
    calc ∑ j, |R l j| * ∑ c, |x j c|
        ≤ ∑ j, toReal Δt * (toReal (W l j) * toReal (mx j)) :=
          Finset.sum_le_sum fun j _ => by
            rw [← mul_assoc]
            exact mul_le_mul (hRle l j) (hmx j) (Finset.sum_nonneg fun c _ => abs_nonneg _)
              (mul_nonneg hΔt.le (hW0 l j))
      _ = toReal Δt * ∑ j, toReal (W l j) * toReal (mx j) := by rw [Finset.mul_sum]
      _ ≤ toReal Δt * toReal (sumUp fun j => mulUp (W l j) (mx j)) :=
          mul_le_mul_of_nonneg_left (le_trans (Finset.sum_le_sum fun j _ => mul_le_mulUp _ _)
            (sum_le_sumUp _)) hΔt.le
  -- the orders as a list: `O[i]` is order `i`
  have hlen : O.length = η := by rw [hO]; simp
  have hget : ∀ i (h : i < O.length), O[i] = ord i := by
    intro i h; simp [hO, ord]
  set Vl := O.map Prod.snd with hVl
  have hVlen : Vl.length = η := by simp [hVl, hlen]
  set X : Fin Vl.length → Mat ℝ n m := fun i => Real.MatExp.particularCoeff A (toReal Δt) i.1 * Mr
  have hX : ∀ i, X i ∈ (Vl[i.1]).toSet := by
    intro i
    have hi : i.1 < O.length := by simpa [hVl] using i.2
    simp only [hVl, List.getElem_map, hget i.1 hi]
    exact (LinearSys.aux_order_mem sys.A hΔt hu hM i.1).2
  have hXsum : (∑ i, X i) = (∑ i ∈ Finset.range η, Real.MatExp.particularCoeff A (toReal Δt) i) * Mr
      := by
    rw [Matrix.sum_mul, ← hVlen]
    exact Fin.sum_univ_eq_sum_range (fun i => Real.MatExp.particularCoeff A (toReal Δt) i * Mr) _
  -- the magnitudes of the boxes bound the members
  have hmu : ∀ j, ∑ c, |u0r j c| ≤ toReal (u₀.magnitudeMat j 0) := by
    intro j
    rw [Fin.sum_univ_one, Interval.magnitudeMat, toReal_maximum, toReal_absolute, toReal_absolute]
    exact abs_le_max_abs_abs (Interval.mem_mat_iff.mp hu j 0).1 (Interval.mem_mat_iff.mp hu j 0).2
  have hmM : ∀ j, ∑ c, |Mr j c| ≤ toReal (sumUp fun c => M.magnitudeMat j c) := by
    intro j
    refine le_trans (Finset.sum_le_sum fun c _ => ?_) (sum_le_sumUp _)
    rw [Interval.magnitudeMat, toReal_maximum, toReal_absolute, toReal_absolute]
    exact abs_le_max_abs_abs (Interval.mem_mat_iff.mp hM j c).1 (Interval.mem_mat_iff.mp hM j c).2
  refine ⟨?_, X, hX, ?_, ?_, ?_⟩
  · -- the constant input's solution: the orders' sum plus `R u₀`
    set Ul := O.map Prod.fst with hUl
    have hUlen : Ul.length = η := by simp [hUl, hlen]
    set Y : Fin Ul.length → Mat ℝ n 1 := fun i =>
      Real.MatExp.particularCoeff A (toReal Δt) i.1 * u0r
    have hY : ∀ i, Y i ∈ (Ul[i.1]).toSet := by
      intro i
      have hi : i.1 < O.length := by simpa [hUl] using i.2
      simp only [hUl, List.getElem_map, hget i.1 hi]
      exact (LinearSys.aux_order_mem sys.A hΔt hu hM i.1).1
    -- the orders sum to the truncated series, the rest is `R u₀`
    have hYsum : (∑ i, Y i)
        = (∑ i ∈ Finset.range η, Real.MatExp.particularCoeff A (toReal Δt) i) * u0r := by
      rw [Matrix.sum_mul, ← hUlen]
      exact Fin.sum_univ_eq_sum_range (fun i => Real.MatExp.particularCoeff A (toReal Δt) i * u0r) _
    have hsplit : Real.MatExp.expIntegral A (toReal Δt) * u0r = (∑ i, Y i) + R * u0r := by
      rw [hYsum, hR, Matrix.sub_mul]; abel
    -- entry by entry: the folds hold the orders' sum, `ρu` the rest
    refine Interval.mem_mat_iff.mpr fun l c => ?_
    have hc : c = 0 := Subsingleton.elim _ _
    subst hc
    obtain ⟨h1, h2⟩ := LinearSys.aux_sum_mem_fold Ul Y hY l 0
    have hr := hRx u0r (fun j => u₀.magnitudeMat j 0) hmu l
    rw [Fin.sum_univ_one] at hr
    have hr' := abs_le.mp (le_trans (le_refl _) hr)
    rw [hsplit, Matrix.add_apply]
    simp only [hUl, List.foldl_map] at h1 h2
    constructor
    · refine le_trans (subDown_le_sub _ _) ?_
      linarith [hr'.1]
    · refine le_trans ?_ (add_le_addUp _ _)
      linarith [hr'.2]
  · -- the orders' sum
    refine Interval.mem_mat_iff.mpr fun l c => ?_
    obtain ⟨h1, h2⟩ := LinearSys.aux_sum_mem_fold Vl X hX l c
    simp only [hVl, List.foldl_map] at h1 h2
    exact ⟨h1, h2⟩
  · -- `PG` within `ρ` of the orders' sum
    intro l
    have h := hRx Mr (fun j => sumUp fun c => M.magnitudeMat j c) hmM l
    have heq : ∀ c, (Real.MatExp.expIntegral A (toReal Δt) * Mr) l c - (∑ i, X i) l c
        = (R * Mr) l c := by
      intro c
      rw [hXsum, hR, Matrix.sub_mul, Matrix.sub_apply]
    simp only [heq]
    exact h
  · -- every contribution of the varying input
    intro z hz
    obtain ⟨b, hb, y, hy, hzeq⟩ := sys.exists_eq_taylor_add_of_mem_inputReach Mr hΔt (η - 1) hz
    rw [show η - 1 + 1 = η by omega] at hzeq
    refine ⟨fun i => b i.1, fun i c => hb i.1 c, y, fun l => ?_, ?_⟩
    · refine le_trans (hy l) ?_
      have h := hRx (k' := 1) 0 (fun j => sumUp fun c => M.magnitudeMat j c) (fun j => by
        simp only [Matrix.zero_apply, abs_zero, Finset.sum_const_zero]
        exact le_trans (Finset.sum_nonneg fun c _ => abs_nonneg (Mr j c)) (hmM j)) l
      refine le_trans ?_ (mul_le_mulUp _ _)
      refine mul_le_mul_of_nonneg_left (le_trans (Finset.sum_le_sum fun j _ => ?_)
        (sum_le_sumUp _)) hΔt.le
      -- the exact remainder below the scaled one
      refine le_trans (mul_le_mul_of_nonneg_right (MatExp.expRemainderMat_le_scaledRemainderFloat
        sys.A hs hΔt.le (η - 1) W (Option.mem_def.mpr hW) l j)
          (Finset.sum_nonneg fun c _ => abs_nonneg _)) ?_
      exact le_trans (mul_le_mul_of_nonneg_left (hmM j) (hW0 l j)) (mul_le_mulUp _ _)
    -- the decomposition: the orders' terms as a sum over the list
    · rw [hzeq]
      congr 1
      rw [← hVlen] at *
      refine (Fin.sum_univ_eq_sum_range (fun i =>
        Real.MatExp.particularCoeff A (toReal Δt) i *ᵥ (Mr *ᵥ b i)) Vl.length).symm.trans ?_
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [X, Matrix.mulVec_mulVec]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
