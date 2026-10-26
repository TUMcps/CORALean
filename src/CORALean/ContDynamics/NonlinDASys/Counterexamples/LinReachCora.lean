module

public import CORALean.ContDynamics.NonlinDASys.Counterexamples.LinErrorCora
public import CORALean.ContDynamics.LinearSys.Operations.OneStep
public import CORALean.ContSet.Zonotope.Real.Instances
public import CORALean.ContSet.Zonotope.Real.Operations.OfPoint
public import CORALean.ContDynamics.LinearSys.Operations.Canonical
public import CORALean.ContDynamics.NonlinDASys.Theorems.LinReachOuter
public import CORALean.ContDynamics.NonlinDASys.Theorems.LinErrorOuter
public import CORALean.ContSet.Zonotope.Real.Theorems.MtimesExact
public import CORALean.ContSet.Zonotope.Real.Theorems.PlusExact
public import CORALean.ContSet.Zonotope.Real.Theorems.OfPointMemIff
public import CORALean.ContSet.Zonotope.Real.Theorems.MemConstruct
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope

@[expose] public section

/-!
# `NonlinDASys.linReachCora`

CORA's `@nonlinDASys/linReach.m` for one step as printed, at the error-loop pass that ends it:
`priv_linearize` builds `Ã = A - CF⁻¹D`, `B̃ = B - CF⁻¹E` and `f0 = f(z*) - CF⁻¹g(z*)`, `oneStep`
runs the linearized system from `Rinit - x*` without the error, and the error set `Verror` of
`priv_linError_mixed_noInt` (`NonlinDASys.linErrorCora`, `+ CF_inv` on the algebraic part) enters
afterwards as `Rerror = particularSolution_timeVarying(linsys, Verror)`. The `while` loop that
grows the assumed error is not run: its last pass's deviation zonotope and the Hessians' midpoints
and radii are the arguments `R_Δ`, `Hd_c`, `Hd_Δ`, `Ha_c`, `Ha_Δ`, as in `linErrorCora`; the
algebraic set `Rti_y` and the split decision are left out.

# CORA's `nonlinDASys/linReach` misses a reachable state

The sign error of `priv_linError_mixed_noInt` (`+ CF_inv` where [1, Cor. 1] has `- CF⁻¹`) reaches
the step CORA's `reach` takes for a DAE with the default `'lin'` algorithm. `ẋ = y`,
`0 = y - u²`, `x(0) = 0`, `u ∈ [-1, 1]`, linearized at `z* = 0`: `Ã = 0`, `B̃ = 0`, `f0 = 0`,
`C F⁻¹ = 1`. The one nonzero Hessian is the constraint's, `-2` in `u`; on the constraint
`ẋ = u² ∈ [0, 1]` while the linearization gives `0`. CORA's error set is `½ (-2) [0, 1] = [-1, 0]`,
its time-point set `Δt [-1, 0]`, and the run under `u ≡ 1`, `x(t) = t`, ends outside it. With
[1, Cor. 1]'s set the tree's `linReach` holds it (`linReach_outer`), at every `Δt > 0`.

## Inputs
* `Δt` – step size
* `η` – Taylor order

## Hypotheses
* `hΔt` – step positive

## Conclusion
* the run ends outside CORA's time-point set but inside the paper-based one

## References

* [1] M. Althoff and B. H. Krogh. "Reachability Analysis of Nonlinear Differential-Algebraic
      Systems". IEEE Transactions on Automatic Control, 2014.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real Matrix

variable {n p m q : ℕ}


-- The model: CORA's code as printed, kept only to be refuted.
/-- One step of CORA's `nonlinDASys/linReach` as printed, the error set
`priv_linError_mixed_noInt`'s (`linErrorCora`): the time-point and the time-interval set. -/
noncomputable def NonlinDASys.linReachCora (f₀ : Vec ℝ n) (g₀ : Vec ℝ p) (A : Mat ℝ n n)
    (B : Mat ℝ n m) (C : Mat ℝ n p) (D : Mat ℝ p n) (E : Mat ℝ p m) (F_inv : Mat ℝ p p)
    (xs : Vec ℝ n) (us : Vec ℝ m) (Rinit : Zonotope (Vec ℝ n)) (U : Zonotope (Vec ℝ m))
    (Hd_c Hd_Δ : Fin n → Mat ℝ q q) (Ha_c Ha_Δ : Fin p → Mat ℝ q q) (R_Δ : Zonotope (Vec ℝ q))
    (Δt : ℝ) (η : ℕ) : Zonotope (Vec ℝ n) × Zonotope (Vec ℝ n) :=
  let CF_inv : Mat ℝ n p := C * F_inv                                     -- CF_inv
  let f0 : Vec ℝ n := f₀ - CF_inv *ᵥ g₀                                  -- f0 = linParams.uTrans
  let A_lin : Mat ℝ n n := A - CF_inv * D                                 -- A_lin
  let B_lin : Mat ℝ n m := B - CF_inv * E                                 -- B_lin
  let U_lin : Zonotope (Vec ℝ n) :=                                       -- linParams.U
    (U.plus (Zonotope.ofPoint (-us))).mtimes B_lin
  let linsys : LinearSys ℝ n := LinearSys.canonical A_lin  -- linearSys(A_lin, 1)
  let Rdelta : Zonotope (Vec ℝ n) := Rinit.plus (Zonotope.ofPoint (-xs))  -- Rinit - p.x
  let R := linsys.oneStep (S := 𝒵) Rdelta U_lin f0 Δt η                  -- [Rtp,Rti] = oneStep
  let Verror : Zonotope (Vec ℝ n) :=                                    -- priv_linError_mixed_noInt
    NonlinDASys.linErrorCora Hd_c Hd_Δ Ha_c Ha_Δ CF_inv R_Δ
  let Rerror : Zonotope (Vec ℝ n) :=                                      -- Rerror
    linsys.inputSolution (S := 𝒵) Δt η Verror
  let Rti : Zonotope (Vec ℝ n) := R.Rti.plus (Zonotope.ofPoint xs)          -- Rti + p.x
  let Rtp : Zonotope (Vec ℝ n) := R.Rtp.plus (Zonotope.ofPoint xs)          -- Rtp + p.x
  (Rtp.plus Rerror, Rti.plus Rerror)                                      -- + Rerror

end CORALean

namespace CORALean

open CORALean.Real Matrix ContSet

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A point of `Z₁ ⊕ Z₂` is a sum of points of each. -/
private theorem NonlinDASys.aux_linReachCora_mem_plus {Z₁ Z₂ : Zonotope (Vec ℝ n)} {v : Vec ℝ n}
    (hv : v ∈ (Z₁.plus Z₂).construct) :
    ∃ a ∈ Z₁.construct, ∃ b ∈ Z₂.construct, v = a + b := by
  obtain ⟨a, ha, b, hb, rfl⟩ := (Zonotope.plus_exact _ _).symm.subset hv
  exact ⟨a, ha, b, hb, rfl⟩

/-- A point of `M Z` is `M` times a point of `Z`. -/
private theorem NonlinDASys.aux_linReachCora_mem_mtimes {m : ℕ} {M : Mat ℝ m n}
    {Z : Zonotope (Vec ℝ n)} {v : Vec ℝ m} (hv : v ∈ (Zonotope.mtimes M Z).construct) :
    ∃ w ∈ Z.construct, v = M *ᵥ w := by
  obtain ⟨w, hw, rfl⟩ := (Zonotope.mtimes_exact _ _).symm.subset hv
  exact ⟨w, hw, rfl⟩

/-- At `A = 0` the remainder of an input solution, `E(r)·r U`, is `{0}`. -/
private theorem NonlinDASys.aux_linReachCora_remainder_eq_zero {A : Mat ℝ n n} (hA : A = 0) (r : ℝ)
    (η : ℕ) (Z : Zonotope (Vec ℝ n)) {v : Vec ℝ n}
    (hv : v ∈ (Zonotope.mtimesIntervalMat (MatExp.inputRemainder A r η) Z).construct)
    : -- --- CONCL ---
    v = 0 := by -- --- PROOF ---
  subst hA
  have hE : MatExp.expRemainderBound (0 : Mat ℝ n n) η = 0 := by
    simp [MatExp.expRemainderBound]
  have hinf : (MatExp.inputRemainder (0 : Mat ℝ n n) r η).inf = 0 := by
    funext j k
    simp [MatExp.inputRemainder, hE]
  have hsup : (MatExp.inputRemainder (0 : Mat ℝ n n) r η).sup = 0 := by
    funext j k
    simp [MatExp.inputRemainder, hE]
  obtain ⟨β, -, hβ⟩ := Zonotope.mem_construct_iff.mp hv
  funext i
  rw [hβ i]
  simp only [Zonotope.mtimesIntervalMat, Interval.center, Zonotope.radiusReach, Interval.radius,
    hinf, hsup]
  simp only [add_zero, sub_zero, smul_zero, zero_mulVec, Pi.zero_apply, zero_add]
  refine Finset.sum_eq_zero fun j _ => ?_
  induction j using Fin.addCases <;> simp

/-- At `A = 0` an input solution is the step times the input set. -/
private theorem NonlinDASys.aux_linReachCora_inputSolution {sys : LinearSys ℝ n} (hA : sys.A = 0)
    (r : ℝ) (η : ℕ) (Z : Zonotope (Vec ℝ n)) {v : Vec ℝ n}
    (hv : v ∈ (sys.inputSolution (S := 𝒵) r η Z).construct) : -- --- CONCL ---
    ∃ w ∈ Z.construct, v = r • w := by -- --- PROOF ---
  -- the Taylor orders past `0` vanish
  have hsum : ∀ (i : ℕ) (a : Vec ℝ n), a ∈ (sys.inputTaylorSum (S := 𝒵) r Z i).construct →
      ∃ w ∈ Z.construct, a = r • w := by
    intro i
    induction i with
    | zero =>
      intro a ha
      obtain ⟨w, hw, rfl⟩ := NonlinDASys.aux_linReachCora_mem_mtimes ha
      exact ⟨w, hw, by simp [LinearSys.inputTerm, Matrix.smul_mulVec]⟩
    | succ i ih =>
      intro a ha
      obtain ⟨a', ha', b', hb', rfl⟩ := NonlinDASys.aux_linReachCora_mem_plus ha
      obtain ⟨w', -, rfl⟩ := NonlinDASys.aux_linReachCora_mem_mtimes hb'
      obtain ⟨w, hw, rfl⟩ := ih a' ha'
      exact ⟨w, hw, by simp [LinearSys.inputTerm, hA]⟩
  obtain ⟨a, ha, b, hb, rfl⟩ := NonlinDASys.aux_linReachCora_mem_plus hv
  rw [NonlinDASys.aux_linReachCora_remainder_eq_zero (by simpa using hA) r η Z hb, add_zero]
  exact hsum η a ha

/-- CORA's error set over `[-1, 1]` for `ẋ = y`, `0 = y - u²` lies in `v ≤ 0`. -/
private theorem NonlinDASys.aux_linReachCora_error_nonpos {w : Vec ℝ 1}
    (hw : w ∈ (NonlinDASys.linErrorCora (p := 1) (q := 1) 0 0 (fun _ => !![-2]) 0 1
      ⟨1, 0, fun _ => ![1]⟩).construct) : -- --- CONCL ---
    w 0 ≤ 0 := by -- --- PROOF ---
  obtain ⟨β, hβ, hx⟩ := hw
  change _ = _ + ∑ j : Fin 5, β j • _ at hx
  have h0 := congrFun hx 0
  simp [NonlinDASys.linErrorCora, Zonotope.quadMap, Zonotope.plus, Zonotope.mtimes,
    Interval.zonotope, Zonotope.absBound, Fin.sum_univ_succ, dotProduct, mulVec, Fin.append,
    Fin.addCases] at h0
  have hb := abs_le.mp (hβ (1 : Fin 5))
  -- the pair generator of a one-generator zonotope is `0`
  split_ifs at h0 with hc
  · exact absurd hc (by
      rw [Subsingleton.elim (finProdFinEquiv.symm (0 : Fin (1 * 1))).2
        (finProdFinEquiv.symm (0 : Fin (1 * 1))).1]
      exact lt_irrefl _)
  · rw [h0]
    linarith [hb.1, hb.2]


-- =======================================  MAIN THEOREM  ======================================= --

/-- `ẋ = y`, `0 = y - u²`, `x(0) = 0`, `u ∈ [-1, 1]`, linearized at `0`: the run under `u ≡ 1`
ends at `x(Δt) = Δt`, outside CORA's time-point set `Δt [-1, 0]` and inside the tree's
`linReach` with [1, Cor. 1]'s error set, at every `Δt > 0` and Taylor order `η`. -/
theorem NonlinDASys.linReachCora_misses_counterexample {Δt : ℝ} (hΔt : 0 < Δt)
    (η : ℕ) : -- --- CONCL ---
    let sys : NonlinDASys 1 1 1 := ⟨fun _ y _ => y, fun _ y u => y - fun _ => u 0 ^ 2, 1,
      fun x _ _ => x⟩
    let Rinit : Zonotope (Vec ℝ 1) := Zonotope.ofPoint 0
    let U : Zonotope (Vec ℝ 1) := ⟨1, 0, fun _ => ![1]⟩
    let x : ℝ → Vec ℝ 1 := fun t _ => t
    sys.IsTrajectory (S := 𝒵) (Set.Icc 0 Δt) Rinit U x (fun _ _ => 1) (fun _ _ => 1) x ∧
      x Δt ∉ (NonlinDASys.linReachCora (sys.f 0 0 0) (sys.g 0 0 0) 0 0 1 0 0 1 0 0 Rinit U
        0 0 (fun _ => !![-2]) 0 U Δt η).1.construct ∧
      x Δt ∈ (NonlinDASys.linReach (sys.f 0 0 0) (sys.g 0 0 0) 0 0 1 0 0 1 0 0 0 Rinit U
        (NonlinDASys.linError (p := 1) 0 0 (fun _ => !![-2]) 0 1 U)
        ⟨1, fun _ => -1 / 2, fun _ _ => 1 / 2⟩ Δt (η + 2)).1.construct := by -- --- PROOF ---
  intro sys Rinit U x
  -- the run: `y = u² = 1`, `ẋ = 1`
  have traj : sys.IsTrajectory (S := 𝒵) (Set.Icc 0 Δt) Rinit U x (fun _ _ => 1) (fun _ _ => 1)
      x :=
    { init := (Zonotope.mem_ofPoint_iff _ _).mpr (funext fun _ => rfl)
      input := fun _ _ => ⟨fun _ => 1, fun _ => by simp, by funext i; fin_cases i; simp [U]⟩
      meas := MeasureTheory.aestronglyMeasurable_const
      integrable := fun _ _ => intervalIntegrable_const
      cont := continuousOn_pi.mpr fun _ => continuousOn_id
      flow := fun t _ => by funext i; simp [sys, x]
      constraint := fun _ _ => by funext i; simp [sys]
      output := fun _ _ => rfl }
  refine ⟨traj, ?_, ?_⟩
  · -- CORA's set: `Δt` times its error set, all of whose points are `≤ 0`
    intro hmem
    obtain ⟨a, ha, b, hb, hab⟩ := NonlinDASys.aux_linReachCora_mem_plus hmem
    obtain ⟨w, hw, rfl⟩ := NonlinDASys.aux_linReachCora_inputSolution (by simp) Δt η _ hb
    rw [mul_one] at hw
    have hw0 := NonlinDASys.aux_linReachCora_error_nonpos hw
    -- the rest of the step is `{0}`
    have ha0 : a = 0 := by
      obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := NonlinDASys.aux_linReachCora_mem_plus ha
      rw [(Zonotope.mem_ofPoint_iff _ _).mp ha₂, add_zero]
      obtain ⟨h, hh, p, hp, rfl⟩ := NonlinDASys.aux_linReachCora_mem_plus ha₁
      obtain ⟨h₁, hh₁, h₂, hh₂, rfl⟩ := NonlinDASys.aux_linReachCora_mem_plus hh
      obtain ⟨d, hd, rfl⟩ := NonlinDASys.aux_linReachCora_mem_mtimes hh₁
      obtain ⟨d₁, hd₁, d₂, hd₂, rfl⟩ := NonlinDASys.aux_linReachCora_mem_plus hd
      obtain ⟨c, hc, rfl⟩ := NonlinDASys.aux_linReachCora_inputSolution (by simp) Δt η _ hh₂
      obtain ⟨e, he, rfl⟩ := NonlinDASys.aux_linReachCora_inputSolution (by simp) Δt η _ hp
      obtain ⟨e', -, rfl⟩ := NonlinDASys.aux_linReachCora_mem_mtimes he
      rw [(Zonotope.mem_ofPoint_iff _ _).mp hd₁, (Zonotope.mem_ofPoint_iff _ _).mp hd₂,
        (Zonotope.mem_ofPoint_iff _ _).mp hc]
      funext i
      simp [sys]
    have := congrFun hab 0
    rw [ha0] at this
    simp [x] at this
    nlinarith
  · -- [1, Cor. 1]'s set holds the error `u²`, and `linReach_outer` the run
    have hlin : ∀ ν : Vec ℝ 1, |ν 0| ≤ 1 → (fun _ => ν 0 ^ 2 : Vec ℝ 1)
        ∈ (NonlinDASys.linError 0 0 (fun _ : Fin 1 => !![-2]) 0 (1 : Mat ℝ 1 1) U).construct := by
      intro ν hν
      have h := NonlinDASys.linError_outer 0 0 (fun _ : Fin 1 => !![-2]) 0 (1 : Mat ℝ 1 1) U
        (Hd := 0) (Ha := fun _ => !![-2]) (by simp) (by simp)
        (ν := ν) ⟨fun _ => ν 0, fun _ => hν, by funext i; fin_cases i; simp [U]⟩
      convert h using 1
      funext i
      simp [dotProduct, mulVec]
      ring
    -- confined to `|u| ≤ 1`; the constraint's error `-u²` lies in `[-1, 0]`
    refine (traj.linReach_outer hΔt (F := 1) (by simp)
      (Rz := {z | |z.2.2 0| ≤ 1}) (fun _ _ => by simp) ?_ ?_ ?_ ?_ (by simp)).1
    · intro x' y' u' hz _
      convert hlin u' hz using 1
      funext i
      fin_cases i
      simp [sys]
    · intro x' y' u' hz _
      refine ⟨fun _ => 1 - 2 * u' 0 ^ 2, fun _ => ?_, ?_⟩
      · have hz' : |u' 0| ≤ 1 := hz
        have h2 : u' 0 ^ 2 ≤ 1 := by nlinarith [abs_le.mp hz']
        rw [abs_le]
        constructor <;> nlinarith
      · funext i
        fin_cases i
        simp [sys]
        ring
    -- `u* = 0 ∈ U`, and `0` in the error set at `ν = 0`
    · exact ⟨fun _ => 0, fun _ => by simp, by funext i; fin_cases i; simp [U]⟩
    · convert hlin 0 (by simp) using 1
      funext i
      simp

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
