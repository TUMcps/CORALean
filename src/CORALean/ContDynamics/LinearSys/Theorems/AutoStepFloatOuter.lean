module

public import CORALean.ContDynamics.LinearSys.Definitions.IsAutoInvariantFloat
public import CORALean.ContDynamics.LinearSys.Definitions.IsOrderAdmissibleFloat
public import CORALean.ContDynamics.LinearSys.Operations.AutoStepFloat
public import CORALean.ContDynamics.LinearSys.Theorems.AffineWindowFloatOuter
public import CORALean.ContDynamics.LinearSys.Theorems.ExpIntegralAddMulVec
public import CORALean.ContDynamics.LinearSys.Theorems.ExpIntegralConstInput
public import CORALean.ContDynamics.LinearSys.Theorems.ExpMemExpSquaringFloat
public import CORALean.ContDynamics.LinearSys.Theorems.InputReachMono
public import CORALean.ContDynamics.LinearSys.Theorems.InputReachSeparationSubset
public import CORALean.ContDynamics.LinearSys.Theorems.InputReachSubsetInputSolutionFloat
public import CORALean.ContDynamics.LinearSys.Operations.InputTaylorSumTailFloat
public import CORALean.ContDynamics.LinearSys.Theorems.InputRemainderSubsetFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.IntervalInputTermFloat
public import CORALean.ContDynamics.LinearSys.Operations.InputTaylorSumTail
public import CORALean.ContSet.Interval.Float.Theorems.Basic
public import CORALean.ContDynamics.LinearSys.Theorems.SquaringsFloatSpec
public import CORALean.ContDynamics.LinearSys.Theorems.IsTrajectorySubMemInputReachRecenter
public import CORALean.ContSet.ContSet.Theorems.Basic
public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_Interval
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval
public import CORALean.ContSet.Conversion.Float.Theorems.IntervalZonotopeContains
public import CORALean.ContSet.Conversion.Float.Theorems.ZonotopeIntervalContains
public import CORALean.ContSet.Conversion.Real.Theorems.IntervalZonotopeContains
public import CORALean.ContSet.Conversion.Real.Theorems.ZonotopeIntervalContains

@[expose] public section

/-!
# One `Alg. 2` iteration keeps its invariant and its window holds every run

From a state holding `IsAutoInvariantFloat`, `autoStepFloat` returns one holding it `Δt_k` later,
and a window `R̂(τ_k)` holding every run over `[t_k, t_{k+1}]`. `autoStepFloat` checks the pair
`(Δt_k, η_k)` it returns, so the tuning is no hypothesis. The free motion and the constant input's
share from `H(t_k)` are in the affine window (`affineWindowFloat_outer`, lines 27-28). The
`Ũ`-input's share by `t_{k+1}` comes apart at `t_k` (`inputReach_separation_subset`), its newest
step is in `bPU_0 ⊕ bPU_∞` (`aux_inputReach_subset_split_float`), and `e^{At_k}` carries the halves
to `P̂^U_0` and into the box of `P̂^U_∞` (lines 17-18). The window's `P̂^U(t_{k+1})` reduces
`P̂^U_0` and keeps `P̂^U_∞` (line 23).

## Inputs
* `sys` – linear system
* `X₀` – initial float zonotope
* `V` – input float zonotope
* `tend` – final float time
* `εmax` – admissible error
* `ζ` – error budget share
* `ηmax` – maximal Taylor order
* `fuel` – number of shrinkings
* `s` – float loop state

## Hypotheses
* `hinv` – state holds the invariant

## Conclusion
* the iteration keeps the invariant and its window holds every run
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps SoundFloatArithmetic NormedSpace Matrix MeasureTheory Pointwise

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

section
open ContSet
open scoped CORALean.Real
attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

/-- The Minkowski sum of plain sets, exactly. -/
@[reducible] def aux_setPlusTail (k : ℕ) : Plus (Set (Vec ℝ k)) (Vec ℝ k) :=
  ⟨fun a b => a + b, fun _ _ => le_rfl⟩


/-- A plain matrix's image of a plain set, exactly. -/
@[reducible] def aux_setMtimesTail : Mtimes (Mat ℝ) 𝒮 where
  mtimes M s := (M *ᵥ ·) '' s
  mtimes_outer M s := by
    simp only [ContSet.construct_mat, Scalar.toRealMat_real, Set.biUnion_singleton]
    exact le_rfl

end


section
open ContSet
open scoped CORALean.Real
attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}
attribute [local instance] aux_setPlusTail aux_setMtimesTail

/-- At `r ≥ 0`, every order count `i`: the exact tail at plain sets is in the float tail. -/
theorem LinearSys.aux_inputTaylorSumTail_subset_float (sys : LinearSys 𝕋 n) {r : 𝕋}
    (hr : 0 ≤ toReal r) (U : Zonotope (Vec 𝕋 n)) : -- --- CONCL ---
    ∀ i,
    construct (sys.inputTaylorSumTail (S := 𝒮) (toReal r) U.construct i)
      ⊆ (sys.inputTaylorSumTailFloat r U i).construct := by -- --- PROOF ---
  -- a matrix in a float box maps `U` into the float product
  have hprod : ∀ {B : Interval (Mat 𝕋 n n)} {M : Mat ℝ n n}, M ∈ B.construct →
      (M *ᵥ ·) '' U.construct
        ⊆ construct (Mtimes.mtimes (𝕄 := ℐ[𝕋])
          (S := 𝒵[𝕋]) B U) :=
    fun {B} {_} hM => (Set.subset_biUnion_of_mem (u := fun A => (A *ᵥ ·) '' U.construct) hM).trans
      (Mtimes.mtimes_outer (𝕄 := ℐ[𝕋])
        (S := 𝒵[𝕋]) B U)
  have hterm : ∀ i, (sys.inputTerm (toReal r) i *ᵥ ·) '' U.construct
      ⊆ construct (Mtimes.mtimes (𝕄 := ℐ[𝕋])
        (S := 𝒵[𝕋])
        (MatExp.intervalInputTerm (Interval.point sys.A) r i) U) :=
    fun i => hprod (MatExp.smul_pow_mem_intervalInputTerm _ hr (Interval.mem_point sys.A) i)
  -- the tail, term by term, by strong induction on the order
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    match i, ih with
    | 0, _ =>
      exact hprod (Interval.mem_mat_iff.mpr fun _ _ => by simp [Interval.point, toReal_zero])
    | 1, _ => exact hterm 1
    | i + 2, ih =>
      exact (Set.add_subset_add (ih (i + 1) (by omega)) (hterm (i + 2))).trans
        (Plus.plus_outer (sys.inputTaylorSumTailFloat r U (i + 1)) _)

end


section
open ContSet
open scoped CORALean.Real
attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

/-- The Minkowski sum of plain sets, exactly. -/
@[reducible] def aux_setPlusSplit (k : ℕ) : Plus (Set (Vec ℝ k)) (Vec ℝ k) :=
  ⟨fun a b => a + b, fun _ _ => le_rfl⟩


/-- A plain matrix's image of a plain set, exactly. -/
@[reducible] def aux_setMtimesSplit : Mtimes (Mat ℝ) 𝒮 where
  mtimes M s := (M *ᵥ ·) '' s
  mtimes_outer M s := by
    simp only [ContSet.construct_mat, Scalar.toRealMat_real, Set.biUnion_singleton]
    exact le_rfl


/-- An interval matrix's images of a plain set, closed and convexified. -/
@[reducible] noncomputable def aux_setMtimesIntervalSplit :
    Mtimes ℐ 𝒮 where
  mtimes I s := closure (convexHull ℝ (⋃ A ∈ construct I, (A *ᵥ ·) '' s))
  mtimes_outer _ _ := (subset_convexHull ℝ _).trans subset_closure

end


section
open ContSet
open scoped CORALean.Real
attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}
attribute [local instance] aux_setPlusSplit aux_setMtimesSplit aux_setMtimesIntervalSplit

/-- From order `1` on, the exact sum is order `0` and the exact tail. -/
theorem LinearSys.aux_inputTaylorSum_eq_term_add_tail (sys : LinearSys 𝕋 n) (r : ℝ)
    (U : Set (Vec ℝ n)) (m : ℕ) : -- --- CONCL ---
    sys.inputTaylorSum (S := 𝒮) r U (m + 1)
      = (sys.inputTerm r 0 *ᵥ ·) '' U
        + sys.inputTaylorSumTail (S := 𝒮) r U (m + 1) := by -- --- PROOF ---
  induction m with
  | zero => rfl
  | succ m ih =>
    show sys.inputTaylorSum (S := 𝒮) r U (m + 1)
        + (sys.inputTerm r (m + 2) *ᵥ ·) '' U
      = (sys.inputTerm r 0 *ᵥ ·) '' U
        + (sys.inputTaylorSumTail (S := 𝒮) r U (m + 1)
          + (sys.inputTerm r (m + 2) *ᵥ ·) '' U)
    rw [ih, add_assoc]


/-- The input's share over a step lies in `bPU_0 ⊕ bPU_∞`. -/
theorem LinearSys.aux_inputReach_subset_split_float (sys : LinearSys 𝕋 n) {Δt : 𝕋} {η : ℕ}
    (hΔt : 0 < toReal Δt) (hη : sys.IsOrderAdmissibleFloat Δt Δt η)
    (V : Zonotope (Vec 𝕋 n)) : -- --- CONCL ---
    sys.inputReach (S := 𝒵[𝕋]) V (toReal Δt)
      ⊆ (Mtimes.mtimes (𝕄 := ℐ[𝕋]) (S := 𝒵[𝕋])
          (MatExp.intervalInputTerm (Interval.point sys.A) Δt 0) V).construct
        + (sys.inputTaylorSumTailFloat Δt V η ⊞ Mtimes.mtimes (S := 𝒵[𝕋])
          (𝕄 := ℐ[𝕋]) (MatExp.intervalInputRemainder
            (Interval.point sys.A) Δt η) V).construct := by -- --- PROOF ---
  have hε : ‖toReal Δt • Scalar.toRealMat sys.A‖ / ((η : ℝ) + 2) < 1 := by
    have hnorm := MatExp.norm_smul_le_normUpperBound (Interval.point sys.A) Δt
      (Interval.mem_point sys.A)
    have hpos : (0:ℝ) < (η : ℝ) + 2 := by positivity
    calc ‖toReal Δt • Scalar.toRealMat sys.A‖ / ((η : ℝ) + 2)
        ≤ toReal (MatExp.normUpperBound (Interval.smul Δt Δt (Interval.point sys.A)))
          / ((η : ℝ) + 2) := div_le_div_of_nonneg_right hnorm hpos.le
      _ ≤ 1 / 2 := hη.2
      _ < 1 := by norm_num
  -- the exact theorem at plain sets, its remainder inside the float product
  have hrem := sys.inputRemainder_subset_float hΔt.le hη V
  have hexact := sys.inputReach_subset_inputSolution (S := 𝒮) hΔt η hε
    (U := V.construct) (ConvexSet.convex_construct V) (CompactSet.isClosed_construct V)
    (CompactSet.isBounded_construct V) (convex_convexHull ℝ _).closure isClosed_closure
    ((CompactSet.isBounded_construct _).subset hrem)
  -- order `0`'s matrix is in its float box, so its image is in the float product
  have hterm0 : (sys.inputTerm (toReal Δt) 0 *ᵥ ·) '' V.construct
      ⊆ construct (Mtimes.mtimes (𝕄 := ℐ[𝕋])
        (S := 𝒵[𝕋])
        (MatExp.intervalInputTerm (Interval.point sys.A) Δt 0) V) :=
    (Set.subset_biUnion_of_mem (u := fun A => (A *ᵥ ·) '' V.construct)
      (MatExp.smul_pow_mem_intervalInputTerm _ hΔt.le (Interval.mem_point sys.A) 0)).trans
      (Mtimes.mtimes_outer (𝕄 := ℐ[𝕋]) (S := 𝒵[𝕋])
        (MatExp.intervalInputTerm (Interval.point sys.A) Δt 0) V)
  -- from order `1` on, the exact sum is order `0` and the exact tail, and the float sets hold both
  obtain ⟨m, rfl⟩ : ∃ m, η = m + 1 := ⟨η - 1, by have := hη.1; omega⟩
  refine hexact.trans ?_
  unfold LinearSys.inputSolution
  show sys.inputTaylorSum (S := 𝒮) (toReal Δt) V.construct (m + 1) + _ ⊆ _
  rw [sys.aux_inputTaylorSum_eq_term_add_tail, add_assoc]
  exact Set.add_subset_add hterm0 ((Set.add_subset_add
    (sys.aux_inputTaylorSumTail_subset_float hΔt.le V (m + 1)) hrem).trans
    (Plus.plus_outer (sys.inputTaylorSumTailFloat Δt V (m + 1)) _))

end


-- =======================================  MAIN THEOREM  ======================================= --

/-- An iteration from a state holding the invariant reaches one holding it later in time, and
its window holds every run over `[t_k, t_{k+1}]`. -/
theorem LinearSys.autoStepFloat_outer (sys : LinearSys 𝕋 n) {X₀ V : Zonotope (Vec 𝕋 n)} {tend : 𝕋}
    {εmax ζ : ℚ} {ηmax fuel : ℕ} {s : LinearSys.AutoStateFloat 𝕋 n}
    (hinv : sys.IsAutoInvariantFloat X₀ V s) : -- --- CONCL ---
    ∀ s' R, (s', R) ∈ sys.autoStepFloat X₀ V tend εmax ζ ηmax fuel s →
      sys.IsAutoInvariantFloat X₀ V s' ∧ s.t < s'.t ∧
        ∀ {T : ℝ} {U : Set (Vec ℝ n)} {x u : ℝ → Vec ℝ n},
          sys.IsCanonicalTrajectory (S := 𝒮) (Set.Icc 0 T) X₀.construct U x u →
          U ⊆ V.construct → ∀ t ∈ Set.Icc (s.t : ℝ) s'.t, t ≤ T →
            x t ∈ R.construct := by -- --- PROOF ---
  intro s' R (h : sys.autoStepFloat X₀ V tend εmax ζ ηmax fuel s = some (s', R))
  obtain ⟨h0, hlo, hhi, hH, hPu, hPU⟩ := hinv
  unfold LinearSys.autoStepFloat at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨sq, hsq, ⟨Δt, η⟩, -, h⟩ := h
  dsimp only at h
  split_ifs at h with hcheck
  obtain ⟨hΔ, hη2, hnrm, -, -⟩ := hcheck
  simp only [Option.bind_eq_some_iff] at h
  obtain ⟨sq1, hsq1, ρ, hρ, h⟩ := h
  simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  set A := Scalar.toRealMat sys.A with hA
  set eAtk := sys.expSquaringFloat s.tEnc.inf s.tEnc.sup (max ηmax 2) sq with heAtk
  -- the squaring that the first step's exponential comes from
  set E₁ := sys.expSquaringFloat (addDown s.tEnc.inf Δt) (addUp s.tEnc.sup Δt) η sq1 with hE₁
  set ũ := Recenter.center V with hũ
  set Ũ := Recenter.recenter V with hŨ
  set tk : ℝ := (s.t : ℝ) with htk
  have htk0 : 0 ≤ tk := by rw [htk]; exact_mod_cast h0
  have hΔr : 0 < toReal Δt := by rw [← ToRat.toReal_toRat]; exact_mod_cast hΔ
  -- the order the check admitted, read back from ℚ
  have hadm : sys.IsOrderAdmissibleFloat Δt Δt η := ⟨hη2, by
    have h := (Rat.cast_le (K := ℝ)).mpr hnrm
    push_cast at h
    rwa [← ToRat.toReal_toRat]⟩
  have hΔq : ((ToRat.toRat Δt : ℚ) : ℝ) = toReal Δt := ToRat.toReal_toRat Δt
  have ht' : (((s.t + ToRat.toRat Δt : ℚ)) : ℝ) = toReal Δt + tk := by
    push_cast; rw [hΔq]; ring
  -- `[e^{At_k}] Z` and `[e^{At_{k+1}}] Z` hold `e^{At_k} z` and `e^{At_{k+1}} z`
  have hmt : ∀ {Z : Zonotope (Vec 𝕋 n)} {z : Vec ℝ n}, z ∈ Z.construct → exp (tk • A) *ᵥ z
      ∈ ContSet.construct (Mtimes.mtimes (𝕄 := ℐ[𝕋])
        (S := 𝒵[𝕋]) eAtk Z) :=
    fun {Z} {_} hz => Mtimes.mtimes_outer (𝕄 := ℐ[𝕋])
      (S := 𝒵[𝕋]) eAtk Z
      (Set.mem_biUnion (sys.exp_mem_expSquaringFloat
        (LinearSys.squaringsFloat_spec (le_max_right _ _) _ hsq) hlo hhi)
        (Set.mem_image_of_mem _ hz))
  have hmt1 : ∀ {Z : Zonotope (Vec 𝕋 n)} {z : Vec ℝ n}, z ∈ Z.construct
      → exp ((toReal Δt + tk) • A) *ᵥ z
        ∈ ContSet.construct (Mtimes.mtimes (𝕄 := ℐ[𝕋])
          (S := 𝒵[𝕋])
          E₁ Z) :=
    fun {Z} {_} hz => Mtimes.mtimes_outer (𝕄 := ℐ[𝕋])
      (S := 𝒵[𝕋]) _ Z
      (Set.mem_biUnion (sys.exp_mem_expSquaringFloat
        (LinearSys.squaringsFloat_spec hη2 _ hsq1)
        ((addDown_le_add _ _).trans (by linarith)) (le_trans (by linarith) (add_le_addUp _ _)))
        (Set.mem_image_of_mem _ hz))
  -- `{ũ}` holds what it is built from
  have hpt : ũ ∈ (Interval.point V.c).zonotope.construct :=
    Interval.zonotope_contains _ (Interval.mem_point V.c)
  -- the constant `ũ` held over `[0, τ]` is an admissible input of any set holding `ũ`
  have hconst : ∀ {W : Zonotope (Vec 𝕋 n)}, ũ ∈ W.construct → ∀ {τ : ℝ}, 0 ≤ τ →
      Real.MatExp.expIntegral A τ *ᵥ ũ ∈ sys.inputReach (S := 𝒵[𝕋]) W τ :=
    fun hW _ hτ => ⟨fun _ => ũ, fun _ _ => hW, aestronglyMeasurable_const,
      (Real.MatExp.expIntegral_constInput A ũ hτ).symm⟩
  have hPuΔ := sys.inputReach_subset_inputSolutionFloat hΔr hadm _ (hconst hpt hΔr.le)
  have hsplit := sys.aux_inputReach_subset_split_float hΔr hadm Ũ
  -- the `Ũ`-input's share by `t_k + Δt`, in the two halves of eq. (27)
  have hPU' : ∀ y ∈ sys.inputReach (S := 𝒵[𝕋]) Ũ (toReal Δt + tk),
      y ∈ (s.PU0 ⊞ Mtimes.mtimes (𝕄 := ℐ[𝕋])
        (S := 𝒵[𝕋]) eAtk
          (Mtimes.mtimes (𝕄 := ℐ[𝕋]) (S := 𝒵[𝕋])
            (MatExp.intervalInputTerm (Interval.point sys.A) Δt 0) Ũ)).construct
        + (s.PUinf ⊞ (Mtimes.mtimes (𝕄 := ℐ[𝕋])
          (S := 𝒵[𝕋]) eAtk
          (sys.inputTaylorSumTailFloat Δt Ũ η ⊞ Mtimes.mtimes (S := 𝒵[𝕋])
            (𝕄 := ℐ[𝕋])
            (MatExp.intervalInputRemainder (Interval.point sys.A) Δt η) Ũ)).interval.zonotope
          ).construct := by
    -- split `y` at `t_k` and send each part to its summand
    intro y hy
    obtain ⟨_, ⟨p, hp, rfl⟩, q, hq, rfl⟩ := sys.inputReach_separation_subset hΔr.le
      htk0 (CompactSet.isBounded_construct Ũ) hy
    obtain ⟨q0, hq0, qi, hqi, rfl⟩ := hPU q hq
    obtain ⟨p0, hp0, pi, hpi, rfl⟩ := hsplit hp
    refine ⟨q0 + exp (tk • A) *ᵥ p0, Plus.plus_outer (S := Zonotope (Vec 𝕋 n)) _ _
        (Set.add_mem_add hq0 (hmt hp0)),
      qi + exp (tk • A) *ᵥ pi, Plus.plus_outer (S := Zonotope (Vec 𝕋 n)) _ _ (Set.add_mem_add hqi
        (Interval.zonotope_contains _ (Zonotope.interval_contains _ (hmt hpi)))), ?_⟩
    beta_reduce; rw [Matrix.mulVec_add]; abel
  -- the constant's share by `t_{k+1}` is in the box `P^u(t_{k+1})` of the stored input's reach
  set PuI := ((s.Pu.zonotope ⊞ Mtimes.mtimes (𝕄 := ℐ[𝕋]) (S := 𝒵[𝕋]) eAtk
    (sys.inputSolutionFloat Δt η (Interval.point V.c).zonotope)).interval) with hPuI
  have hPu' : Real.MatExp.expIntegral A (toReal Δt + tk) *ᵥ ũ
      ∈ PuI.construct := by
    rw [Real.MatExp.expIntegral_add_mulVec A ũ hΔr.le htk0, add_comm]
    exact Zonotope.interval_contains _ (Plus.plus_outer (S := Zonotope (Vec 𝕋 n)) _ _
      (Set.add_mem_add (Interval.zonotope_contains _ hPu) (hmt hPuΔ)))
  -- `H(t_{k+1})` holds the affine flow from `X₀`
  have hH' : ∀ x₀ ∈ X₀.construct, exp ((toReal Δt + tk) • A) *ᵥ x₀
      + Real.MatExp.expIntegral A (toReal Δt + tk) *ᵥ ũ ∈
        (Mtimes.mtimes (S := 𝒵[𝕋])
        (𝕄 := ℐ[𝕋])
        E₁ X₀
        ⊞ PuI.zonotope
        ).construct := fun x₀ hx₀ =>
    Plus.plus_outer (S := Zonotope (Vec 𝕋 n)) _ _
      (Set.add_mem_add (hmt1 hx₀) (Interval.zonotope_contains _ hPu'))
  -- the invariant at `t_{k+1}`, field by field, then the time and the window
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · have : (0 : ℝ) ≤ ((s.t + ToRat.toRat Δt : ℚ) : ℝ) := by rw [ht']; linarith
    exact_mod_cast this
  · show toReal (addDown s.tEnc.inf Δt) ≤ _
    rw [ht']; exact (addDown_le_add _ _).trans (by linarith)
  · show _ ≤ toReal (addUp s.tEnc.sup Δt)
    rw [ht']; exact le_trans (by linarith) (add_le_addUp _ _)
  · intro x₀ hx₀
    rw [ht']
    exact hH' x₀ hx₀
  · rw [ht']; exact hPu'
  · intro y hy
    rw [ht'] at hy
    exact hPU' y hy
  · show s.t < s.t + ToRat.toRat Δt
    linarith
  -- the window: the run is the affine flow from `H(t_k)` plus its departure from it
  · intro T U x u traj hUV t ht htT
    rw [ht'] at ht
    have ht0 : 0 ≤ t := htk0.trans ht.1
    set τ := t - tk with hτ
    have hτ0 : 0 ≤ τ := sub_nonneg.mpr ht.1
    have hτΔ : τ ≤ toReal Δt := by linarith [ht.2]
    -- the run's departure from the affine flow by `t`, inside the input's share by `t_{k+1}`
    have hd := traj.sub_mem_inputReach_recenter (S' := 𝒵[𝕋]) (V := V)
      hUV ⟨ht0, htT⟩
    have hd' := sys.inputReach_mono (S := 𝒵[𝕋])
      (CompactSet.isBounded_construct Ũ)
      (Recenter.zero_mem_recenter V) ht0 ht.2 hd
    obtain ⟨d0, hd0, di, hdi, hdeq⟩ := hPU' _ hd'
    -- the affine flow from `H(t_k)`: where its point `x_k` is one step on is in `H(t_{k+1})`
    have hxk := hH (x 0) traj.init
    have hnext : exp (toReal Δt • A) *ᵥ (exp (tk • A) *ᵥ x 0 + Real.MatExp.expIntegral A tk *ᵥ ũ)
        + Real.MatExp.expIntegral A (toReal Δt) *ᵥ ũ ∈
          (Mtimes.mtimes (S := 𝒵[𝕋])
          (𝕄 := ℐ[𝕋])
          E₁ X₀
          ⊞ PuI.zonotope
          ).construct := by
      -- both the exponential and the integral split at `t_k`, so `x_k` one step on is `t_{k+1}`'s
      have hG := Real.MatExp.expIntegral_add_mulVec A ũ htk0 hΔr.le
      have hE : exp ((toReal Δt + tk) • A) = exp (toReal Δt • A) * exp (tk • A) := by
        rw [add_smul]
        exact exp_add_of_commute (((Commute.refl A).smul_left _).smul_right _)
      have := hH' (x 0) traj.init
      rw [hE, add_comm (toReal Δt) tk, hG, ← Matrix.mulVec_mulVec] at this
      rwa [Matrix.mulVec_add, add_assoc]
    -- the affine window holds the flow over `[0, τ]` from `x_k`
    have hwin := sys.affineWindowFloat_outer (ũ := V.c) hΔr hadm hxk hnext hτ0 hτΔ
    have hexp : exp (t • A) = exp (τ • A) * exp (tk • A) := by
      rw [show t = τ + tk by ring, add_smul]
      exact exp_add_of_commute (((Commute.refl A).smul_left _).smul_right _)
    -- the run at `t` is the flow from `x_k` over `τ`, plus its departure from the free motion
    have hx : x t = (exp (τ • A) *ᵥ (exp (tk • A) *ᵥ x 0 + Real.MatExp.expIntegral A tk *ᵥ ũ)
        + Real.MatExp.expIntegral A τ *ᵥ ũ)
        + (x t - (exp (t • A) *ᵥ x 0 + Real.MatExp.expIntegral A t *ᵥ ũ)) := by
      rw [show Real.MatExp.expIntegral A t *ᵥ ũ = Real.MatExp.expIntegral A (tk + τ) *ᵥ ũ by
          rw [show tk + τ = t by ring],
        Real.MatExp.expIntegral_add_mulVec A ũ htk0 hτ0, hexp, ← Matrix.mulVec_mulVec,
        Matrix.mulVec_add]
      abel
    -- the departure, in `P̂^U(t_{k+1})`: `P̂^U_0` reduced, `P̂^U_∞` kept
    have hPUk1 : x t - (exp (t • A) *ᵥ x 0 + Real.MatExp.expIntegral A t *ᵥ ũ) ∈ (Reduce.reduce
        (s.PU0 ⊞ Mtimes.mtimes (𝕄 := ℐ[𝕋])
          (S := 𝒵[𝕋]) eAtk
          (Mtimes.mtimes (𝕄 := ℐ[𝕋]) (S := 𝒵[𝕋])
            (MatExp.intervalInputTerm (Interval.point sys.A) Δt 0) Ũ)) ρ
        ⊞ (s.PUinf ⊞ (Mtimes.mtimes (𝕄 := ℐ[𝕋])
          (S := 𝒵[𝕋]) eAtk
          (sys.inputTaylorSumTailFloat Δt Ũ η ⊞ Mtimes.mtimes (S := 𝒵[𝕋])
            (𝕄 := ℐ[𝕋])
            (MatExp.intervalInputRemainder (Interval.point sys.A) Δt η) Ũ)).interval.zonotope)
        ).construct := by
      rw [← hdeq]
      exact Plus.plus_outer (S := Zonotope (Vec 𝕋 n)) _ _
        (Set.add_mem_add (Reduce.reduce_outer (S := Zonotope (Vec 𝕋 n)) _ _ hd0) hdi)
    rw [hx]
    exact Plus.plus_outer (S := Zonotope (Vec 𝕋 n)) _ _ (Set.add_mem_add hwin hPUk1)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
