module

public import CORALean.ContDynamics.LinParamSys.Operations.InitReachInputDependence
public import CORALean.ContDynamics.LinParamSys.Operations.Canonical
public import CORALean.ContDynamics.NonlinParamSys.Operations.Linearize
public import CORALean.ContSet.Zonotope.Real.Operations.OfPoint
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval

@[expose] public section

/-!
# `NonlinParamSys.linReachCora`, one step of `linReach` with an interval `paramInt`

The path `reach(nonlinParamSys)` takes with `paramInt` an interval: `@contDynamics/linReach.m` [2]
calls `linearize` [1] (`NonlinParamSys.linearize`), translates the initial set by the
linearization point, and, as `isa(sys,'nonlinParamSys') && isa(params.paramInt,'interval')`,
runs `initReach_inputDependence` on the `linParamSys` of `zA` with the constant input `zf`
(`LinParamSys.initReachInputDependence`, corrected where CORA's `inputCorr` is too small; for the
zero matrix `zA` and `B = 1`, which has no deviation from its center, of the counterexample
the two coincide), then translates back and adds the
abstraction error `Rerror`.

Not modelled: the time-varying input `zB (U + uTrans - p.u)` (`linParams.U`), the choice of the
linearization point, and the computation of `Rerror` by the Lagrange remainder over the enclosing
set with its tightening loop, which is a parameter here.

# `linReach` of a `nonlinParamSys` with an interval `paramInt` misses states

`reach(nonlinParamSys)` with an interval `paramInt` goes through `linReach.m` [2], which calls
`linearize` [1] and, because `isa(params.paramInt,'interval')`, runs `initReach_inputDependence`
on the linearized system. `linearize` builds `zf` from `f(x, u, 0)` and unit-vector differences,
which is the dynamics only for `f` affine in `p` (`linearize_f_counterexample`), and nothing
checks that. So the reachable set misses states: for `ẋ = p²`, `p ∈ [1, 2]`, from the point
`x₀`, the state `x₀ + 4 r` of the run at `p = 2` after a step `r` is in neither set
`NonlinParamSys.linReachCora` returns. The abstraction error cannot cover it: the remainder is
zero (`linReachCora_remainder_zero`), `Rerror = {0}`. The linearized system here has `zA = 0` and
`zf = [1, 2]`, so its step set is `x₀ + r [1, 2]`.

## References

* [1] `contDynamics/@nonlinParamSys/linearize.m`
* [2] `contDynamics/@contDynamics/linReach.m`
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       12-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real ContSet

variable {n m q : ℕ}


-- The model: CORA's code as printed, kept only to be refuted.
/-- CORA's `(Rtp, Rti)` of `linReach` for one step `r` at Taylor order `η`, from `Rinit` about
`(xs, us)` over the parameter box `paramInt`, with abstraction error `Rerror`. -/
noncomputable def NonlinParamSys.linReachCora (sys : NonlinParamSys n m q) (xs : Vec ℝ n)
    (us : Vec ℝ m) (paramInt : Interval (Vec ℝ q)) (Rinit : Zonotope (Vec ℝ n))
    (Rerror : Zonotope (Vec ℝ n)) (r : ℝ) (η : ℕ) : Zonotope (Vec ℝ n) × Zonotope (Vec ℝ n) :=
  -- [sys,linsys,linParams,linOptions] = linearize(sys,Rinit,params,options);
  let lin := sys.linearize xs us paramInt
  let linsys : LinParamSys 𝕄𝒵 n := LinParamSys.canonical lin.zA
  -- Rdelta = Rinit + (-sys.linError.p.x);
  let Rdelta : Zonotope (Vec ℝ n) := Rinit ⊞ Zonotope.ofPoint (-lin.xs)
  -- [linsys,R] = initReach_inputDependence(linsys,Rdelta,linParams,linOptions);
  let R := linsys.initReachInputDependence r η Rdelta lin.zf.c lin.zf.G
  -- Rti = Rti+sys.linError.p.x;  Rtp = Rtp+sys.linError.p.x;
  let Rtp := R.1 ⊞ Zonotope.ofPoint lin.xs
  let Rti := R.2 ⊞ Zonotope.ofPoint lin.xs
  -- Rti=Rti+Rerror;  Rtp=Rtp+Rerror;
  (Rtp ⊞ Rerror, Rti ⊞ Rerror)

end CORALean

namespace CORALean

open CORALean.Real ContSet Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The zero zonotope in `ℝ¹`: center and every generator `0`. -/
def LinParamSys.IsNullZono (Z : Zonotope (Vec ℝ 1)) : Prop := Z.c = 0 ∧ ∀ l, Z.G l = 0

theorem LinParamSys.IsNullZono.plus {Z₁ Z₂ : Zonotope (Vec ℝ 1)} (h₁ : IsNullZono Z₁)
    (h₂ : IsNullZono Z₂) : IsNullZono (Z₁ ⊞ Z₂) := by
  refine ⟨by show Z₁.c + Z₂.c = 0; rw [h₁.1, h₂.1]; simp, fun l => ?_⟩
  show Fin.append Z₁.G Z₂.G l = 0
  refine Fin.addCases (fun i => ?_) (fun j => ?_) l <;>
    simp [Fin.append_left, Fin.append_right, h₁.2, h₂.2]

theorem LinParamSys.IsNullZono.mtimesInterval {Z : Zonotope (Vec ℝ 1)} (hZ : IsNullZono Z)
    (IM : Interval (Mat ℝ 1 1)) :
    IsNullZono (Mtimes.mtimes (𝕄 := ℐ) (S := 𝒵) IM Z) := by -- --- PROOF ---
  refine ⟨by show IM.center *ᵥ Z.c = 0; rw [hZ.1]; simp, fun l => ?_⟩
  show Fin.append (fun l => IM.center *ᵥ Z.G l)
    (Matrix.diagonal fun i => Zonotope.radiusReach IM Z i) l = 0
  refine Fin.addCases (fun i => ?_) (fun j => ?_) l
  · simp [Fin.append_left, hZ.2]
  · simp only [Fin.append_right]
    ext k
    simp [Matrix.diagonal_apply, Zonotope.radiusReach, Zonotope.absBound, hZ.1, hZ.2]

theorem LinParamSys.IsNullZono.mtimesMatZonotope {Z : Zonotope (Vec ℝ 1)} (hZ : IsNullZono Z)
    (M : Zonotope (Mat ℝ 1 1)) :
    IsNullZono (Mtimes.mtimes (𝕄 := 𝕄𝒵) (S := 𝒵) M Z) := by -- --- PROOF ---
  refine ⟨by simp [Mtimes.mtimes, Zonotope.mtimesMatZonotope, Zonotope.bilin, hZ.1], fun l => ?_⟩
  simp only [Mtimes.mtimes, Zonotope.mtimesMatZonotope, Zonotope.bilin]
  refine Fin.addCases (fun i => ?_) (fun k => ?_) l
  · refine Fin.addCases (fun a => ?_) (fun b => ?_) i <;>
      simp [Fin.append_left, Fin.append_right, hZ.1, hZ.2]
  · simp [Fin.append_right, hZ.2]

theorem LinParamSys.IsNullZono.mtimesMatZonotope_zero {Z : Zonotope (Vec ℝ 1)}
    {M : Zonotope (Mat ℝ 1 1)} (hc : M.c = 0) (hh : M.h = 0) :
    IsNullZono (Mtimes.mtimes (𝕄 := 𝕄𝒵) (S := 𝒵) M Z) := by -- --- PROOF ---
  refine ⟨by simp [Mtimes.mtimes, Zonotope.mtimesMatZonotope, Zonotope.bilin, hc], fun l => ?_⟩
  simp only [Mtimes.mtimes, Zonotope.mtimesMatZonotope, Zonotope.bilin]
  refine Fin.addCases (fun i => ?_) (fun k => ?_) l
  · refine Fin.addCases (fun a => ?_) (fun b => ?_) i
    · exact absurd a.2 (by omega)
    · simp [Fin.append_left, Fin.append_right, hc]
  · exact absurd (finProdFinEquiv.symm k).1.2 (by omega)

/-- For the identity `B`, the deviation of `B` from its center is the zero zonotope, so the
independent input `initReachInputDependence` adds for it is the zero set. -/
theorem LinParamSys.aux_inputSolutionZono_null (zA : Zonotope (Mat ℝ 1 1))
    (UG : Fin zA.h → Vec ℝ 1) (Uc : Vec ℝ 1) (r : ℝ) (S : Zonotope (Vec ℝ 1) → ℝ)
    (hS : ∀ Z, S Z = Z.c 0 + ∑ l, |Z.G l 0|) : -- --- STMT ---
    let X := (LinParamSys.canonical zA : LinParamSys 𝕄𝒵 1).inputSolutionZono (S := 𝒵) r 2
      (Mtimes.mtimes (𝕄 := 𝕄𝒵) (S := 𝒵)
        (⟨(LinParamSys.canonical zA : LinParamSys 𝕄𝒵 1).B.h, 0,
          (LinParamSys.canonical zA : LinParamSys 𝕄𝒵 1).B.G⟩ : Zonotope (Mat ℝ 1 1))
        (⟨zA.h, Uc, UG⟩ : Zonotope (Vec ℝ 1)))
    X.c 0 = 0 ∧ S X = 0 := by -- --- PROOF ---
  intro X
  have hV := LinParamSys.IsNullZono.mtimesMatZonotope_zero (Z := (⟨zA.h, Uc, UG⟩ :
    Zonotope (Vec ℝ 1))) (M := (⟨(LinParamSys.canonical zA : LinParamSys 𝕄𝒵 1).B.h, 0,
      (LinParamSys.canonical zA : LinParamSys 𝕄𝒵 1).B.G⟩ : Zonotope (Mat ℝ 1 1))) rfl rfl
  have hX : IsNullZono X := by
    simp only [X, LinParamSys.inputSolutionZono]
    exact ((hV.mtimesMatZonotope _ |>.plus (hV.mtimesMatZonotope _)).plus
      (hV.mtimesInterval _)).plus (hV.mtimesInterval _)
  simp [hS, hX.1, hX.2]


-- =======================================  MAIN THEOREM  ======================================= --

/-- For `ẋ = p²`, `p ∈ [1, 2]`, the state of the run at `p = 2` after a step `r` lies outside
both sets of `linReachCora`, which is run with `Rerror = {0}` (the remainder is zero). -/
theorem NonlinParamSys.linReachCora_misses_counterexample {r : ℝ} (hr : 0 < r)
    (x₀ : ℝ) : -- --- STMT ---
    let sys : NonlinParamSys 1 1 1 := ⟨fun _ _ p => fun _ => p 0 ^ 2, 1, fun x _ _ => x⟩
    let P : Zonotope (Vec ℝ 1) := ⟨1, fun _ => 3 / 2, fun _ _ => 1 / 2⟩
    let I : Interval (Vec ℝ 1) := ⟨fun _ => 1, fun _ => 2⟩
    let R := sys.linReachCora (fun _ => x₀) 0 I (Zonotope.ofPoint fun _ => x₀)
      (Zonotope.ofPoint 0) r 2
    ∃ x u : ℝ → Vec ℝ 1,
      sys.IsConstTrajectory (S := 𝒵) (Set.Icc 0 r) (Zonotope.ofPoint fun _ => x₀)
        (Zonotope.ofPoint 0) P x u (fun _ => 2) ∧
      x r ∉ construct R.1 ∧ x r ∉ construct R.2 := by -- --- PROOF ---
  intro sys P I R
  -- the size of a zonotope in coordinate `0`: center plus the absolute generators
  obtain ⟨S, hS⟩ : ∃ S : Zonotope (Vec ℝ 1) → ℝ, ∀ Z, S Z = Z.c 0 + ∑ l, |Z.G l 0| :=
    ⟨_, fun _ => rfl⟩
  have hSplus : ∀ Z₁ Z₂ : Zonotope (Vec ℝ 1), S (Z₁ ⊞ Z₂) = S Z₁ + S Z₂ := by
    intro Z₁ Z₂
    simp only [hS]
    show (Z₁.c + Z₂.c) 0 + ∑ l, |(Fin.append Z₁.G Z₂.G l) 0| = _
    rw [Fin.sum_univ_add]
    simp [Fin.append_left, Fin.append_right]
    ring
  have hSmt : ∀ (IM : Interval (Mat ℝ 1 1)) (Z : Zonotope (Vec ℝ 1)),
      (∀ i j, IM.radius i j = 0) → S (Mtimes.mtimes (𝕄 := ℐ) (S := 𝒵) IM Z)
        = IM.center 0 0 * Z.c 0 + ∑ l, |IM.center 0 0 * Z.G l 0| := by
    intro IM Z hrad
    simp only [hS]
    show (IM.center *ᵥ Z.c) 0 + ∑ l, |(Fin.append (fun l => IM.center *ᵥ Z.G l)
      (Matrix.diagonal fun i => Zonotope.radiusReach IM Z i) l) 0| = _
    rw [Fin.sum_univ_add]
    simp [Fin.append_left, Fin.append_right, Matrix.mulVec, dotProduct, Zonotope.radiusReach,
      hrad]
  -- the size of a point
  have hSpt : ∀ v : Vec ℝ 1, S (Zonotope.ofPoint v) = v 0 := by
    intro v; simp [hS, Zonotope.ofPoint]
  -- every point of a zonotope is below its size
  have hbound : ∀ (Z : Zonotope (Vec ℝ 1)) z, z ∈ construct Z → z 0 ≤ S Z := by
    rintro Z z ⟨β, hβ, rfl⟩
    rw [hS]
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    have : ∑ j, β j * Z.G j 0 ≤ ∑ j, |Z.G j 0| := by
      refine Finset.sum_le_sum fun j _ => ?_
      calc β j * Z.G j 0 ≤ |β j * Z.G j 0| := le_abs_self _
        _ = |β j| * |Z.G j 0| := abs_mul _ _
        _ ≤ |Z.G j 0| := mul_le_of_le_one_left (abs_nonneg _) (hβ j)
    linarith
  -- the step of `initReach_inputDependence` for `A = 0`, `Uconst = [1, 2]` stays below `d + 2 r`
  have core : ∀ (r : ℝ) (hr : 0 ≤ r) (Uc : Vec ℝ 1) (hUc : Uc = fun _ => 3 / 2)
      (zA : Zonotope (Mat ℝ 1 1)) (hA : zA = ⟨1, 0, fun _ => 0⟩)
      (UG : Fin zA.h → Vec ℝ 1) (hUG : ∀ i, UG i = fun _ => 1 / 2)
      (Rd : Zonotope (Vec ℝ 1)) (hh : Rd.h = 0),
      S ((LinParamSys.canonical zA).initReachInputDependence r 2 Rd Uc UG).1 ≤ Rd.c 0 + 2 * r ∧
      S ((LinParamSys.canonical zA).initReachInputDependence r 2 Rd Uc UG).2 ≤ Rd.c 0 + 2 * r := by
    intro r hr Uc hUc zA hA UG hUG Rd hh
    have hSRd : S Rd = Rd.c 0 := by
      haveI : IsEmpty (Fin Rd.h) := by rw [hh]; infer_instance
      simp [hS]
    have hSapp : ∀ (a b : ℕ) (f : Fin a → Vec ℝ 1) (g : Fin b → Vec ℝ 1),
        ∑ l : Fin (a + b), |Fin.append f g l 0| = ∑ l, |f l 0| + ∑ l, |g l 0| := by
      intro a b f g
      rw [Fin.sum_univ_add]
      simp [Fin.append_left, Fin.append_right]
    -- `linComb` of a point and a set with a larger center is no bigger than the latter
    have hlin : ∀ Z₁ Z₂ : Zonotope (Vec ℝ 1), Z₁.h = 0 → Z₁.c 0 ≤ Z₂.c 0 →
        S (Zonotope.linComb Z₁ Z₂) ≤ S Z₂ := by
      rintro ⟨h₁, c₁, G₁⟩ ⟨h₂, c₂, G₂⟩ hz1 hc
      simp only at hz1 hc
      subst hz1
      simp only [hS, Zonotope.linComb, hSapp]
      simp [Zonotope.pairSum, Zonotope.pairDiff]
      rw [abs_of_nonpos (sub_nonpos.2 hc)]
      linarith
    -- the identity `B` and `c = 0` carry the input to the state space unchanged
    have hVc : (LinParamSys.canonical zA : LinParamSys 𝕄𝒵 1).B.c *ᵥ Uc
        + (LinParamSys.canonical zA : LinParamSys 𝕄𝒵 1).c = Uc := by
      show (1 : Mat ℝ 1 1) *ᵥ Uc + 0 = Uc
      simp
    have hVG : ∀ i, (LinParamSys.canonical zA : LinParamSys 𝕄𝒵 1).B.c *ᵥ UG i = UG i :=
      fun i => by
        show (1 : Mat ℝ 1 1) *ᵥ UG i = UG i
        simp
    have hfst : ((LinParamSys.canonical zA : LinParamSys 𝕄𝒵 1).initReachInputDependence
        r 2 Rd Uc UG).1 = (LinParamSys.canonical zA : LinParamSys 𝕄𝒵 1).dependentHomSol
          r 2 Rd Uc UG ⊞ (LinParamSys.canonical zA : LinParamSys 𝕄𝒵 1).inputSolutionZono
            (S := 𝒵) r 2 (Mtimes.mtimes (𝕄 := 𝕄𝒵) (S := 𝒵)
              (⟨(LinParamSys.canonical zA : LinParamSys 𝕄𝒵 1).B.h, 0,
                (LinParamSys.canonical zA : LinParamSys 𝕄𝒵 1).B.G⟩ : Zonotope (Mat ℝ 1 1))
              (⟨zA.h, Uc, UG⟩ : Zonotope (Vec ℝ 1))) := by
      simp only [LinParamSys.initReachInputDependence, hVc, hVG]
    have hextS' := LinParamSys.aux_inputSolutionZono_null zA UG Uc r S hS
    subst hA
    -- the second-order `R_lowOrder`: center `d + 3 r / 2`, one generator `r / 2`
    have hlow : S (LinParamSys.dependentLowOrder (0 : Mat ℝ 1 1) (fun _ => 0) Rd.c Uc UG r)
        = Rd.c 0 + 2 * r := by
      simp only [hS, LinParamSys.dependentLowOrder, hSapp]
      simp [hUc, hUG, Matrix.mulVec, dotProduct, abs_of_nonneg hr]
      ring
    -- every interval matrix of the step is the zero or the identity box
    have hz : ∀ i j, (Zonotope.interval (⟨1, 0, fun _ => 0⟩ : Zonotope (Mat ℝ 1 1))).inf i j = 0 ∧
        (Zonotope.interval (⟨1, 0, fun _ => 0⟩ : Zonotope (Mat ℝ 1 1))).sup i j = 0 := by
      intro i j; simp [Zonotope.interval]; rfl
    generalize hB : Zonotope.interval (⟨1, 0, fun _ => 0⟩ : Zonotope (Mat ℝ 1 1)) = B at hz
    -- the entries of the interval operations the step uses
    have hsmI : ∀ (c : ℝ) (I : Interval (Mat ℝ 1 1)) i j,
        (Interval.smul c I).inf i j = min (c * I.inf i j) (c * I.sup i j) := fun _ _ _ _ => rfl
    have hsmS : ∀ (c : ℝ) (I : Interval (Mat ℝ 1 1)) i j,
        (Interval.smul c I).sup i j = max (c * I.inf i j) (c * I.sup i j) := fun _ _ _ _ => rfl
    have hplI : ∀ (I J : Interval (Mat ℝ 1 1)) i j,
        (Interval.plus I J).inf i j = I.inf i j + J.inf i j := fun _ _ _ _ => rfl
    have hplS : ∀ (I J : Interval (Mat ℝ 1 1)) i j,
        (Interval.plus I J).sup i j = I.sup i j + J.sup i j := fun _ _ _ _ => rfl
    have hpow : ∀ (B : Interval (Mat ℝ 1 1)), (∀ i j, B.inf i j = 0 ∧ B.sup i j = 0) →
        ∀ k i j, (B.matPow (k+1)).inf i j = 0 ∧ (B.matPow (k+1)).sup i j = 0 := by
      intro B hz k i j
      rw [Interval.matPow]
      simp [Interval.matMul, (hz _ _).1, (hz _ _).2, Interval.mulLo, Interval.mulHi]
    -- the powers of the zero box
    have hp0 : ∀ (B : Interval (Mat ℝ 1 1)) i j,
        (B.matPow 0).inf i j = (if i = j then 1 else 0) ∧
        (B.matPow 0).sup i j = (if i = j then 1 else 0) := by
      intro B i j; simp [Interval.matPow, Interval.point, Matrix.one_apply]
    have habs : ∀ (B : Interval (Mat ℝ 1 1)), (∀ i j, B.inf i j = 0 ∧ B.sup i j = 0) →
        B.absMax = 0 := by
      intro B hz; ext i j; simp [Interval.absMax, (hz i j).1, (hz i j).2]
    have hE : ∀ η, MatExp.expRemainderBound (0 : Mat ℝ 1 1) η = 0 := by
      intro η; simp [MatExp.expRemainderBound]
    have hzC : ∀ i j, (Interval.smul r B).inf i j = 0 ∧ (Interval.smul r B).sup i j = 0 := by
      intro i j; simp [hsmI, hsmS, (hz i j).1, (hz i j).2]
    generalize hC : Interval.smul r B = C at hzC
    have hEI : ∀ i j, (MatExp.expIntervalEnclosure C 2).inf i j = (if i = j then 1 else 0) ∧
        (MatExp.expIntervalEnclosure C 2).sup i j = (if i = j then 1 else 0) := by
      intro i j
      simp [MatExp.expIntervalEnclosure, MatExp.expIntervalTaylor, hplI, hplS, hsmI, hsmS,
        (hpow C hzC _ _ _).1, (hpow C hzC _ _ _).2, habs C hzC, hE, (hp0 C _ _).1, (hp0 C _ _).2]
    -- the center and the size of an interval matrix times a zonotope
    have hcmt : ∀ (IM : Interval (Mat ℝ 1 1)) (Z : Zonotope (Vec ℝ 1)),
        (Mtimes.mtimes (𝕄 := ℐ) (S := 𝒵) IM Z).c 0 = IM.center 0 0 * Z.c 0 := by
      intro IM Z
      show (IM.center *ᵥ Z.c) 0 = _
      simp [Matrix.mulVec, dotProduct]
    have hZ : ∀ (IM : Interval (Mat ℝ 1 1)) (Z : Zonotope (Vec ℝ 1)),
        (∀ i j, IM.inf i j = 0 ∧ IM.sup i j = 0) →
        S (Mtimes.mtimes (𝕄 := ℐ) (S := 𝒵) IM Z) = 0 := by
      intro IM Z h0
      rw [hSmt IM Z (fun i j => by simp [Interval.radius, (h0 i j).1, (h0 i j).2])]
      simp [Interval.center, (h0 0 0).1, (h0 0 0).2]
    have hI1 : ∀ (IM : Interval (Mat ℝ 1 1)) (Z : Zonotope (Vec ℝ 1)),
        (∀ i j, IM.inf i j = (if i = j then 1 else 0) ∧ IM.sup i j = (if i = j then 1 else 0)) →
        S (Mtimes.mtimes (𝕄 := ℐ) (S := 𝒵) IM Z) = S Z := by
      intro IM Z h0
      rw [hSmt IM Z (fun i j => by simp [Interval.radius, (h0 i j).1, (h0 i j).2])]
      simp [Interval.center, (h0 0 0).1, (h0 0 0).2, hS]
      norm_num
    -- the Taylor tails vanish
    have hT : ∀ i j, (MatExp.expIntervalTaylorTail C 2).inf i j = 0 ∧
        (MatExp.expIntervalTaylorTail C 2).sup i j = 0 := fun i j => ⟨rfl, rfl⟩
    have hTi : ∀ i j, (MatExp.inputIntervalTaylorTail C r 2).inf i j = 0 ∧
        (MatExp.inputIntervalTaylorTail C r 2).sup i j = 0 := fun i j => ⟨rfl, rfl⟩
    -- the two interval matrices `eIhigh` and `eIhigh_input`, both zero
    obtain ⟨E1, hE1⟩ : ∃ E1 : Interval (Mat ℝ 1 1), E1 = ⟨fun i j =>
        (MatExp.expIntervalTaylorTail C 2).inf i j - MatExp.expRemainderBound C.absMax 2,
        fun i j => (MatExp.expIntervalTaylorTail C 2).sup i j
          + MatExp.expRemainderBound C.absMax 2⟩ := ⟨_, rfl⟩
    obtain ⟨E2, hE2⟩ : ∃ E2 : Interval (Mat ℝ 1 1), E2 = (MatExp.inputIntervalTaylorTail C r 2).plus
        (MatExp.intervalInputRemainder B r 2) := ⟨_, rfl⟩
    have hE1z : ∀ i j, E1.inf i j = 0 ∧ E1.sup i j = 0 := by
      intro i j
      simp [hE1, habs C hzC, hE, (hT i j).1, (hT i j).2]
    have hE2z : ∀ i j, E2.inf i j = 0 ∧ E2.sup i j = 0 := by
      intro i j
      simp [hE2, hplI, hplS, MatExp.intervalInputRemainder, hC, habs C hzC, hE, (hTi i j).1,
        (hTi i j).2]
    -- the center of the time-point set is at least the center of the start
    have hctp : Rd.c 0 ≤ (LinParamSys.dependentHomSol
        (LinParamSys.canonical (⟨1, 0, fun _ => 0⟩ : Zonotope (Mat ℝ 1 1))) r 2 Rd Uc UG).c 0 := by
      have hcplus : ∀ Z₁ Z₂ : Zonotope (Vec ℝ 1), (Z₁ ⊞ Z₂).c 0 = Z₁.c 0 + Z₂.c 0 :=
        fun _ _ => rfl
      have hcen0 : ∀ IM : Interval (Mat ℝ 1 1), (∀ i j, IM.inf i j = 0 ∧ IM.sup i j = 0) →
          IM.center 0 0 = 0 := by
        intro IM h0; simp [Interval.center, (h0 0 0).1, (h0 0 0).2]
      have hcen1 : (MatExp.expIntervalEnclosure C 2).center 0 0 = 1 := by
        simp [Interval.center, (hEI 0 0).1, (hEI 0 0).2]; norm_num
      simp only [LinParamSys.dependentHomSol, hB, hC, ← hE1, ← hE2, hcplus, hcmt, hcen0 E1 hE1z,
        hcen0 E2 hE2z, hcen1]
      simp [LinParamSys.dependentLowOrder, hUc, Zonotope.ofPoint]
      positivity
    -- the time-point set: state part `0`, `R_lowOrder` `d + 2 r`, the remainders `0`
    have htp : S (LinParamSys.dependentHomSol
        (LinParamSys.canonical (⟨1, 0, fun _ => 0⟩ : Zonotope (Mat ℝ 1 1))) r 2 Rd Uc UG) = Rd.c 0
            + 2 * r := by
      simp only [LinParamSys.dependentHomSol, hSplus, hB, hC, hlow]
      rw [← hE1, ← hE2, hI1 _ _ hEI, hSplus, hSpt, hSRd, hZ E1 _ hE1z, hZ E2 _ hE2z]
      simp
    have hFz : ∀ i j, (MatExp.intervalCorrectionMatrix B r 2).inf i j = 0 ∧
        (MatExp.intervalCorrectionMatrix B r 2).sup i j = 0 := by
      intro i j
      simp [MatExp.intervalCorrectionMatrix, MatExp.intervalCorrTerm, hsmI, hsmS, hC,
        habs C hzC, hE, (hpow B hz _ _ _).1, (hpow B hz _ _ _).2]
    have hFiz : ∀ i j, (MatExp.intervalConstCorrectionMatrix B r 2).inf i j = 0 ∧
        (MatExp.intervalConstCorrectionMatrix B r 2).sup i j = 0 := by
      intro i j
      simp [MatExp.intervalConstCorrectionMatrix, MatExp.intervalConstCorrTerm, hsmI, hsmS, hC,
        habs C hzC, hE, (hpow B hz _ _ _).1, (hpow B hz _ _ _).2]
    -- the time-interval set: the hull of start and time-point set, plus the zero terms
    have hti : S (LinParamSys.initReachInputDependence
        (LinParamSys.canonical (⟨1, 0, fun _ => 0⟩ : Zonotope (Mat ℝ 1 1))) r 2 Rd Uc UG).2 ≤ Rd.c
            0 + 2 * r := by
      simp only [LinParamSys.initReachInputDependence, hVc, hVG, hSplus, hB, hZ _ _ hFz,
        hZ _ _ hFiz]
      change S (Zonotope.linComb _ _) + 0 + 0 ≤ _
      rw [add_zero, add_zero]
      refine (hlin Rd _ hh ?_).trans ?_
      · rw [show ∀ Z₁ Z₂ : Zonotope (Vec ℝ 1), (Z₁ ⊞ Z₂).c 0 = Z₁.c 0 + Z₂.c 0 from fun _ _ => rfl,
          hextS'.1]
        simpa using hctp
      · rw [hSplus, hextS'.2]
        simpa using htp.le
    exact ⟨by rw [hfst, hSplus, hextS'.2]; simpa using htp.le, hti⟩
  -- the linearization of `ẋ = p²` over `[1, 2]`: `zA = 0`, `zf = [1, 2]`
  have hA : (sys.linearize (fun _ => x₀) 0 I).zA = ⟨1, 0, fun _ => 0⟩ := by
    simp [sys, I, NonlinParamSys.linearize, jacobianMat, Interval.center, Interval.radius]
  have hUc : (sys.linearize (fun _ => x₀) 0 I).zf.c = fun _ => 3 / 2 := by
    funext i
    simp [sys, I, NonlinParamSys.linearize, Interval.center, Interval.radius]
    norm_num
  have hUG : ∀ i, (sys.linearize (fun _ => x₀) 0 I).zf.G i = fun _ => 1 / 2 := by
    intro i
    funext j
    fin_cases i
    simp [sys, I, NonlinParamSys.linearize, Interval.center, Interval.radius]
    norm_num
  have hc := core r hr.le _ hUc (sys.linearize (fun _ => x₀) 0 I).zA hA _ hUG
    (Zonotope.ofPoint (fun _ => x₀) ⊞ Zonotope.ofPoint (-(sys.linearize (fun _ => x₀) 0 I).xs))
    rfl
  have hSRdc : (Zonotope.ofPoint (fun _ : Fin 1 => x₀)
      ⊞ Zonotope.ofPoint (-(sys.linearize (fun _ => x₀) 0 I).xs)).c 0 = 0 := by
    show (fun _ : Fin 1 => x₀) 0 + (-fun _ : Fin 1 => x₀) 0 = 0
    simp
  -- both sets of `linReachCora` stay below `x₀ + 2 r`, the run at `p = 2` is at `x₀ + 4 r`
  have hx : ∀ x : ℝ → Vec ℝ 1, (∀ t, x t = fun _ => x₀ + 4 * t) →
      x r ∉ construct R.1 ∧ x r ∉ construct R.2 := by
    intro x hx
    have hxr : x r 0 = x₀ + 4 * r := by rw [hx]
    -- the time-point and the time-interval set
    have h1 : S R.1 ≤ x₀ + 2 * r := by
      simp only [R, NonlinParamSys.linReachCora, hSplus, hSpt]
      have := hc.1
      rw [hSRdc] at this
      have e0 : ((0 : Vec ℝ 1) : Fin 1 → ℝ) 0 = 0 := rfl
      have e1 : (sys.linearize (fun _ => x₀) 0 I).xs 0 = x₀ := rfl
      rw [e0, e1]
      linarith
    have h2 : S R.2 ≤ x₀ + 2 * r := by
      simp only [R, NonlinParamSys.linReachCora, hSplus, hSpt]
      have := hc.2
      rw [hSRdc] at this
      have e0 : ((0 : Vec ℝ 1) : Fin 1 → ℝ) 0 = 0 := rfl
      have e1 : (sys.linearize (fun _ => x₀) 0 I).xs 0 = x₀ := rfl
      rw [e0, e1]
      linarith
    exact ⟨fun hmem => by linarith [hbound _ _ hmem], fun hmem => by linarith [hbound _ _ hmem]⟩
  -- the run `x t = x₀ + 4 t` at `p = 2` is a constant-parameter trajectory
  refine ⟨fun t => fun _ => x₀ + 4 * t, fun _ => 0, ⟨?_, ?_, ?_, ?_⟩, hx _ fun _ => rfl⟩
  · exact ⟨fun _ => 0, fun _ => by simp, by simp [Zonotope.ofPoint]⟩
  · intro t _; exact ⟨fun _ => 0, fun _ => by simp, by simp [Zonotope.ofPoint]⟩
  · exact ⟨fun _ => 1, fun _ => by simp, by funext i; simp [P]; norm_num⟩
  · intro t _
    refine hasDerivWithinAt_pi.2 fun i => ?_
    have h : HasDerivWithinAt (fun s : ℝ => x₀ + 4 * s) (4 * 1) (Set.Icc 0 r) t :=
      (((hasDerivAt_id t).const_mul 4).const_add x₀).hasDerivWithinAt
    simpa [sys] using h.congr_deriv (by norm_num)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
