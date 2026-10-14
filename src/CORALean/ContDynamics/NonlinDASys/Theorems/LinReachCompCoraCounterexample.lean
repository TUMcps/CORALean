module

public import CORALean.ContDynamics.NonlinDASys.Operations.LinReachCompCora
public import CORALean.ContSet.Zonotope.Real.Theorems.MtimesExact
public import CORALean.ContSet.Zonotope.Real.Theorems.PlusExact
public import CORALean.ContSet.Zonotope.Real.Theorems.OfPointMemIff
public import CORALean.ContSet.Zonotope.Real.Theorems.MemConstruct
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Prod

@[expose] public section

/-!
# CORA's compositional `nonlinDASys/linReach` misses a reachable state

`ẋ₁ = y₁`, `0 = y₁ - y₂` (subsystem 1, input `y₂`), `ẋ₂ = y₂`, `0 = y₂ - x₂²` (subsystem 2),
`x(0) ∈ {0} × [-1, 1]`, run with `options.index` through `linReach` (`linReachCompCora`). At the
centre `0` CORA linearizes (`p.x = 0`, `p.y = 0`): `A = B = D = E = 0`, `C = I`, `f0 = 0`, so
`Ã = B̃ = 0` whatever `pinv(F)` returns. Subsystem 1 is linear: its Hessians are `0` and its
local error ([1, Sec. V-B]) `error{1}` is `{0}` for every `R_xyu`, `Csub`, `Fsub`; `index{2}.X'`
has a zero first row, and `reduce` keeps a zero row. So `x₁` of CORA's time-point set is
`x₁(0) = 0`. The solution from `x(0) = (0, -1)`, `x₂ = -1/(1+t)`, `x₁ = 1 - 1/(1+t)`,
`y₁ = y₂ = x₂²`, has `x₁(Δt) > 0`. Not the sign issue: the miss holds at every `Csub`, `Fsub` of
either sign, and with every value of subsystem 2's terms.

Which pass of the `while` loop accepts does not matter (all `R_xyu` are quantified). It does
accept: with `maxError_* = Inf` (default) `perfInd = 0`; `error_x = 0` gives `0/0 = NaN`, not
`> 1`; pass 1 has `appliedError_y = 0` (`initReach` starts at `0`), pass 2 `1.1 · 1`, and
`error_y₂ = (1 + 1.1 Δt)² ≤ 1.1` for `Δt ≤ 0.044` (read from the source, not run).
`options.index` draws a redundancy warning from `validateOptions` and is kept.

## References

* [1] M. Althoff. "Formal and Compositional Analysis of Power Systems using Reachable Sets".
      IEEE Transactions on Power Systems, 29(5):2270-2280, 2014.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real Matrix ContSet

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A point of `Z₁ ⊕ Z₂` is a sum of points of each. -/
theorem NonlinDASys.aux_linReachCompCora_mem_plus {Z₁ Z₂ : Zonotope (Vec ℝ n)} {v : Vec ℝ n}
    (hv : v ∈ (Z₁.plus Z₂).construct) :
    ∃ a ∈ Z₁.construct, ∃ b ∈ Z₂.construct, v = a + b := by
  obtain ⟨a, ha, b, hb, rfl⟩ := (Zonotope.plus_exact _ _).symm.subset hv
  exact ⟨a, ha, b, hb, rfl⟩

/-- A point of `M Z` is `M` times a point of `Z`. -/
theorem NonlinDASys.aux_linReachCompCora_mem_mtimes {m : ℕ} {M : Mat ℝ m n}
    {Z : Zonotope (Vec ℝ n)} {v : Vec ℝ m} (hv : v ∈ (Zonotope.mtimes M Z).construct) :
    ∃ w ∈ Z.construct, v = M *ᵥ w := by
  obtain ⟨w, hw, rfl⟩ := (Zonotope.mtimes_exact _ _).symm.subset hv
  exact ⟨w, hw, rfl⟩

/-- At `A = 0` the remainder of an input solution, `E(r)·r U`, is `{0}`. -/
theorem NonlinDASys.aux_linReachCompCora_remainder_eq_zero {A : Mat ℝ n n} (hA : A = 0) (r : ℝ)
    (η : ℕ) (Z : Zonotope (Vec ℝ n)) {v : Vec ℝ n}
    (hv : v ∈ (Zonotope.mtimesIntervalMat (MatExp.inputRemainder A r η) Z).construct) :
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
theorem NonlinDASys.aux_linReachCompCora_inputSolution {sys : LinearSys ℝ n} (hA : sys.A = 0)
    (r : ℝ) (η : ℕ) (Z : Zonotope (Vec ℝ n)) {v : Vec ℝ n}
    (hv : v ∈ (sys.inputSolution (S := 𝒵) r η Z).construct) :
    ∃ w ∈ Z.construct, v = r • w := by -- --- PROOF ---
  -- the Taylor orders past `0` vanish
  have hsum : ∀ (i : ℕ) (a : Vec ℝ n), a ∈ (sys.inputTaylorSum (S := 𝒵) r Z i).construct →
      ∃ w ∈ Z.construct, a = r • w := by
    intro i
    induction i with
    | zero =>
      intro a ha
      obtain ⟨w, hw, rfl⟩ := NonlinDASys.aux_linReachCompCora_mem_mtimes ha
      exact ⟨w, hw, by simp [LinearSys.inputTerm, Matrix.smul_mulVec]⟩
    | succ i ih =>
      intro a ha
      obtain ⟨a', ha', b', hb', rfl⟩ := NonlinDASys.aux_linReachCompCora_mem_plus ha
      obtain ⟨w', -, rfl⟩ := NonlinDASys.aux_linReachCompCora_mem_mtimes hb'
      obtain ⟨w, hw, rfl⟩ := ih a' ha'
      exact ⟨w, hw, by simp [LinearSys.inputTerm, hA]⟩
  obtain ⟨a, ha, b, hb, rfl⟩ := NonlinDASys.aux_linReachCompCora_mem_plus hv
  rw [NonlinDASys.aux_linReachCompCora_remainder_eq_zero (by simpa using hA) r η Z hb, add_zero]
  exact hsum η a ha

/-- A zonotope whose centre and generators vanish at `i` has only points vanishing at `i`. -/
theorem NonlinDASys.aux_linReachCompCora_mem_coord {Z : Zonotope (Vec ℝ n)} {i : Fin n}
    (hc : Z.c i = 0) (hG : ∀ j, Z.G j i = 0) {v : Vec ℝ n} (hv : v ∈ Z.construct) :
    v i = 0 := by
  obtain ⟨β, -, h⟩ := Zonotope.mem_construct_iff.mp hv
  rw [h i, hc]
  simp [hG]

/-- Girard's `reduce` keeps a coordinate at which centre and generators vanish. -/
theorem NonlinDASys.aux_linReachCompCora_reduce_coord {Z : Zonotope (Vec ℝ n)} (o : ℕ)
    {i : Fin n} (hc : Z.c i = 0) (hG : ∀ j, Z.G j i = 0) :
    (Z.reduce o).c i = 0 ∧ ∀ j, (Z.reduce o).G j i = 0 := by -- --- PROOF ---
  unfold Zonotope.reduce Zonotope.reduceGirard
  by_cases hlt : o * n < Z.h
  · rw [dif_pos hlt]
    refine ⟨hc, fun j => ?_⟩
    simp only [Zonotope.reduceBy]
    refine Fin.addCases (fun l => ?_) (fun l => ?_) j
    · simp [hG]
    · simp only [Fin.append_right, diagonal_apply]
      split_ifs with h
      · subst h
        simp [hG]
      · rfl
  · rw [dif_neg hlt]
    exact ⟨hc, hG⟩

/-- `Z₁ ⊕ Z₂` keeps a coordinate at which both vanish. -/
theorem NonlinDASys.aux_linReachCompCora_plus_coord {Z₁ Z₂ : Zonotope (Vec ℝ n)} {i : Fin n}
    (h₁ : Z₁.c i = 0 ∧ ∀ j, Z₁.G j i = 0) (h₂ : Z₂.c i = 0 ∧ ∀ j, Z₂.G j i = 0) :
    (Z₁.plus Z₂).c i = 0 ∧ ∀ j, (Z₁.plus Z₂).G j i = 0 := by -- --- PROOF ---
  refine ⟨by simp [Zonotope.plus, h₁.1, h₂.1], fun j => ?_⟩
  simp only [Zonotope.plus]
  refine Fin.addCases (fun l => ?_) (fun l => ?_) j
  · simp [h₁.2]
  · simp [h₂.2]


-- =======================================  MAIN THEOREM  ======================================= --

/-- The solution of `ẋ₁ = y₁`, `0 = y₁ - y₂`, `ẋ₂ = y₂`, `0 = y₂ - x₂²` from `(0, -1)` ends
outside CORA's compositional time-point set, at every `Δt > 0`, Taylor order, `pinv(F)`, reduction
order, `Csub`, `Fsub`, `R_xyu` and subsystem-2 Hessian. -/
theorem NonlinDASys.linReachCompCora_misses_counterexample {Δt : ℝ} (hΔt : 0 < Δt) (η o : ℕ)
    (F_inv : Mat ℝ 2 2) (Csub Fsub : Fin 2 → Mat ℝ 1 1) (R_xyu : Fin 2 → Zonotope (Vec ℝ 3))
    (Hf₂ Hf₂' Hg₂ Hg₂' : Fin 1 → Mat ℝ 3 3) :
    let sys : NonlinDASys 2 2 1 :=
      ⟨fun _ y _ => y, fun x y _ => ![y 0 - y 1, y 1 - x 1 ^ 2], 2, fun x _ _ => x⟩
    let Rinit : Zonotope (Vec ℝ 2) := ⟨1, 0, fun _ => ![0, 1]⟩
    let U : Zonotope (Vec ℝ 1) := Zonotope.ofPoint 0
    let X : Fin 2 → Mat ℝ 1 2 := ![!![1, 0], !![0, 1]]
    let x : ℝ → Vec ℝ 2 := fun t => ![1 - (1 + t)⁻¹, -(1 + t)⁻¹]
    let y : ℝ → Vec ℝ 2 := fun t => ![(1 + t)⁻¹ ^ 2, (1 + t)⁻¹ ^ 2]
    sys.Trajectory (S := 𝒵) (Set.Icc 0 Δt) Rinit U x y (fun _ => 0) ∧
      x Δt ∉ (NonlinDASys.linReachCompCora (sys.f 0 0 0) (sys.g 0 0 0) 0 0 1 0 0 F_inv 0 0
        Rinit U X ![0, Hf₂] ![0, Hf₂'] ![0, Hg₂] ![0, Hg₂'] Csub Fsub R_xyu o Δt η).1.construct
      := by -- --- PROOF ---
  intro sys Rinit U X x y
  have h1 : ∀ t : ℝ, 0 ≤ t → (1 + t) ≠ 0 := fun t ht => by positivity
  refine ⟨?_, ?_⟩
  · -- the run: `x₂ = -1/(1+t)`, `x₁ = x₂ + 1`, `y₁ = y₂ = x₂²`
    refine
      { init := ⟨fun _ => -1, fun _ => by simp, by funext i; fin_cases i <;> simp [x, Rinit]⟩
        input := fun _ _ => (Zonotope.mem_ofPoint_iff _ _).mpr rfl
        flow := fun t ht => ?_
        constraint := fun t _ => by funext i; fin_cases i <;> simp [sys, x, y] }
    have hd : HasDerivAt (fun s : ℝ => (1 + s)⁻¹) (-(1 : ℝ) / (1 + t) ^ 2) t :=
      ((hasDerivAt_id' t).const_add 1).inv (h1 t ht.1)
    refine (hasDerivAt_pi.mpr fun i => ?_).hasDerivWithinAt
    fin_cases i
    · convert (hd.const_sub 1) using 1
      · funext s
        simp [x]
      · simp [sys, y, div_eq_mul_inv]
    · convert hd.neg using 1
      · funext s
        simp [x]
      · simp [sys, y, div_eq_mul_inv]
  · intro hmem
    obtain ⟨a, ha, b, hb, hab⟩ := NonlinDASys.aux_linReachCompCora_mem_plus hmem
    -- `Ã = 0`: the error part is `Δt` times a point of `Verror`
    obtain ⟨w, hw, rfl⟩ := NonlinDASys.aux_linReachCompCora_inputSolution (by simp) Δt η _ hb
    -- `Verror` vanishes at `x₁`: `error{1}` is `{0}` as a representation, `X₂'` has a zero row
    let E₁ : Zonotope (Vec ℝ 1) := (NonlinDASys.compLocalErrorCora (0 : Fin 1 → Mat ℝ 3 3) 0
      (0 : Fin 1 → Mat ℝ 3 3) 0 (Csub 0) (Fsub 0) (R_xyu 0)).reduce o
    -- subsystem 2's error, whatever it is
    let E₂ : Zonotope (Vec ℝ 1) :=
      (NonlinDASys.compLocalErrorCora Hf₂ Hf₂' Hg₂ Hg₂' (Csub 1) (Fsub 1) (R_xyu 1)).reduce o
    have herr₁ : ∀ i, E₁.c i = 0 ∧ ∀ j, E₁.G j i = 0 := by
      intro i
      refine NonlinDASys.aux_linReachCompCora_reduce_coord o ?_ fun j => ?_
      · simp [NonlinDASys.compLocalErrorCora, Zonotope.quadMap, Zonotope.plus,
          Zonotope.mtimes, Interval.zonotope, ← Pi.zero_def]
      · simp only [NonlinDASys.compLocalErrorCora, Zonotope.plus]
        refine Fin.addCases (fun l => ?_) (fun l => ?_) j
        · simp [Zonotope.quadMap, Fin.append, Fin.addCases, ← Pi.zero_def]
        · simp [Interval.zonotope, Zonotope.mtimes, Fin.append, Fin.addCases, ← Pi.zero_def]
    -- `errorTotal = 0 + X₁' error{1} + X₂' error{2}`, then `reduce`
    have hZ := NonlinDASys.aux_linReachCompCora_plus_coord (i := 0)
      (NonlinDASys.aux_linReachCompCora_plus_coord (Z₁ := Zonotope.ofPoint (0 : Vec ℝ 2))
        ⟨rfl, fun j => j.elim0⟩
        (Z₂ := Zonotope.mtimes (X 0)ᵀ E₁)
        ⟨by simp [Zonotope.mtimes, X, mulVec, dotProduct, (herr₁ 0).1],
          fun j => by simp [Zonotope.mtimes, X, mulVec, dotProduct, (herr₁ 0).2]⟩)
      (Z₂ := Zonotope.mtimes (X 1)ᵀ E₂)
      ⟨by simp [Zonotope.mtimes, X, mulVec, dotProduct],
        fun j => by simp [Zonotope.mtimes, X, mulVec, dotProduct]⟩
    have htot := NonlinDASys.aux_linReachCompCora_reduce_coord o hZ.1 hZ.2
    have hw0 : w 0 = 0 := NonlinDASys.aux_linReachCompCora_mem_coord htot.1 htot.2 hw
    -- the linear part keeps `x₁(0) = 0`
    have ha0 : a 0 = 0 := by
      obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := NonlinDASys.aux_linReachCompCora_mem_plus ha
      rw [(Zonotope.mem_ofPoint_iff _ _).mp ha₂]
      obtain ⟨h, hh, p, hp, rfl⟩ := NonlinDASys.aux_linReachCompCora_mem_plus ha₁
      obtain ⟨h₁, hh₁, h₂, hh₂, rfl⟩ := NonlinDASys.aux_linReachCompCora_mem_plus hh
      -- `e^{0} Rdelta`, the constant input `f0 = 0` and `B̃ U = 0`
      obtain ⟨d, hd, rfl⟩ := NonlinDASys.aux_linReachCompCora_mem_mtimes hh₁
      obtain ⟨d₁, hd₁, d₂, hd₂, rfl⟩ := NonlinDASys.aux_linReachCompCora_mem_plus hd
      obtain ⟨c, hc, rfl⟩ := NonlinDASys.aux_linReachCompCora_inputSolution (by simp) Δt η _ hh₂
      obtain ⟨e, he, rfl⟩ := NonlinDASys.aux_linReachCompCora_inputSolution (by simp) Δt η _ hp
      obtain ⟨e', -, rfl⟩ := NonlinDASys.aux_linReachCompCora_mem_mtimes he
      have hd₁0 : d₁ 0 = 0 :=
        NonlinDASys.aux_linReachCompCora_mem_coord (Z := Rinit) (by simp [Rinit])
          (fun _ => by simp [Rinit]) hd₁
      rw [(Zonotope.mem_ofPoint_iff _ _).mp hd₂, (Zonotope.mem_ofPoint_iff _ _).mp hc]
      simp [sys, hd₁0, mulVec, dotProduct, Fin.sum_univ_succ]
    -- `x₁(Δt) = 1 - 1/(1+Δt) > 0`
    have := congrFun hab 0
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, ha0, hw0, mul_zero, add_zero] at this
    have hlt : (1 + Δt)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
    simp [x] at this
    linarith

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
