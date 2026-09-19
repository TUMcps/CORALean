import CORALean.ContDynamics.NonlinearSys.AbstrReach
import CORALean.ContDynamics.NonlinearSys.EstimateGain
import CORALean.ContDynamics.NonlinearSys.TuneAbstrOrder

/-!
# `Alg. 2`: one adaptively-tuned step

[1, Alg. 2] for `k > 1`: line 1 updates the finite horizon from the last step's
gain, lines 2-15 run the step twice — once over the horizon, to get `R_abs(h)`
and from it the optimal step size, once over that step size, to get the
reachable set — and lines 16-18 report the gain, add the error and reduce.

Lines 3-6 are `adaptLinPass`, the half of the body both passes share; lines 4-5
are the caller's `lin`, as in `Alg. 1`. `Φ` is indexed by the abstraction order
`κ`, which is what lets line 13 compare the two orders eq. (47) weighs.

Two departures. `optDeltat` reports the `λ'` it stopped at beside `Δt*`, line
16's `estimateGain` needing it; and line 10 as printed reads `φ⁽¹⁾_k`, which
line 16 only produces afterwards, so the last step's gain is passed — see the
reference page's finding.

`rad` and `dbox` are the caller's, §5.4 reducing every set to one number; the
first step's horizon, gain and order are `adaptInit`'s arguments.

## References

* [1] M. Wetzlinger, A. Kulmburg, A. Le Penven and M. Althoff. "Adaptive
      Reachability Algorithms for Nonlinear Systems Using Abstraction Error
      Analysis". Nonlinear Analysis: Hybrid Systems, vol. 46, 2022, p. 101252.
-/

-- Authors:       Tobias Ladner
-- Written:       18-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n m : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)]
variable [∀ n, OfPoint (S n) (Vec ℝ n)] [∀ n, Recentre (S n) (Vec ℝ n)]
variable [Mtimes (Mat ℝ) S] [Mtimes ℐ S] [Real.OfInterval S]

/-- What one step of [1, Alg. 2] hands the next: its own outputs, and the
inputs those become. -/
structure NonlinearSys.AdaptState (S : ℕ → Type) (n : ℕ) where
  /-- `t_k`. -/
  t : ℝ
  /-- `R(t_k)`, line 17, as line 18 reduced it. -/
  R : S n
  /-- `R(τ_k)`, line 17, as line 18 reduced it. -/
  Rτ : S n
  /-- `h_{k-1}`, the finite time horizon of the last step. -/
  h : ℝ
  /-- `φ⁽¹⁾_{k-1}`, the gain of the last step, line 16. -/
  φ : ℝ
  /-- `κ_k`, the abstraction order, line 13. -/
  κ : ℕ
  /-- `r^{(λ*)}_{abs,k'}` of the last evaluation of eq. (47). -/
  rabs : ℝ

/-- The state [1, Alg. 2] needs before its first step, which [1] describes for
`k = 1` in prose rather than in the algorithm. -/
def NonlinearSys.adaptInit (X₀ : S n) (h₀ φ₀ rabs₀ : ℝ) (κ₀ : ℕ) :
    NonlinearSys.AdaptState S n :=
  { t := 0, R := X₀, Rτ := X₀, h := h₀, φ := φ₀, κ := κ₀, rabs := rabs₀ }

/-- Lines 3-6: the linearized system and the two sets it reaches, the half of
the loop body both passes share. -/
noncomputable def NonlinearSys.adaptLinPass (sys : NonlinearSys n m) (U : S m)
    (lin : Vec ℝ n → Vec ℝ m → Mat ℝ n n × Mat ℝ n m) (Δt : ℝ) (ηlin : ℕ) (R : S n) :
    Mat ℝ n n × S n × S n :=
  let zs := sys.linPoint Δt R U                                   -- 3. linPoint, eq. (6)
  let AB := lin zs.1 zs.2                                         -- 4.-5. taylor, linSys
  let lsys := NonlinearSys.linearize AB.1                         -- 5. the linearized system
  let Ulin := linInput sys.f AB.1 AB.2 zs.1 zs.2 U                -- 5. w ⊞ B(U ⊖ u✱)
    (OfPoint.ofPoint (0 : Vec ℝ n))
  (AB.1, lsys.timePointStep Δt ηlin R Ulin,                       -- 6. linReachAdaptive, eq. (10)
    lsys.timeIntervalStep Δt ηlin R ⊞ lsys.inputSolution Δt ηlin Ulin)  -- 6. eq. (12)


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 2]: one adaptively-tuned step, and `none` where an abstraction
error loop gave out. -/
noncomputable def NonlinearSys.adaptStep (sys : NonlinearSys n m) (U : S m)
    (lin : Vec ℝ n → Vec ℝ m → Mat ℝ n n × Mat ℝ n m) (Φ : ℕ → S n → S n → S n)
    (sub : S n → S n → Bool) (enlarge : S n → S n) (le : ℝ → ℝ → Bool) (rad : S n → ℝ)
    (dbox : S n → Fin n → ℝ) (ζδ ζh ζZ ζK : ℝ) (ηlin ηabs o fuel : ℕ)
    (s : NonlinearSys.AdaptState S n) : Option (NonlinearSys.AdaptState S n) :=
  let hk := s.h * (ζδ - ζh) / (ζδ - s.φ)                          -- 1. h_k, eq. (59)
  let p₁ := sys.adaptLinPass U lin hk ηlin s.R                    -- 3.-6. a = 1, at Δt_k = h_k
  match abstrErrLoop sub enlarge (Φ s.κ p₁.2.2) (OfPoint.ofPoint 0) fuel with  -- 7. abstrErrLoop
  | none => none
  | some Ψh =>
    let rabs1 := rad ((NonlinearSys.linearize p₁.1).inputSolution hk ηabs Ψh)  -- 9. r⁽¹⁾_abs,k
    let ζA := Real.exp (Matrix.trace p₁.1 * hk)                   -- eq. (50)'s e^{tr(Ah)}
    let opt := optDeltat le ζδ ζZ ζA s.φ (rad s.R) rabs1 hk fuel  -- 10. optDeltat, Δt_k ← Δt*
    let p₂ := sys.adaptLinPass U lin opt.1 ηlin s.R               -- 3.-6. a = 2, at Δt_k = Δt*
    match abstrErrLoop sub enlarge (Φ 1 p₂.2.2) (OfPoint.ofPoint 0) fuel,      -- 7. abstrErrLoop,
      abstrErrLoop sub enlarge (Φ 2 p₂.2.2) (OfPoint.ofPoint 0) fuel with      --    at both orders
    | some Ψ₁, some Ψ₂ =>
      let lsys := NonlinearSys.linearize p₂.1
      let Rabs₁ := lsys.inputSolution opt.1 ηabs Ψ₁               -- 12. abstrSolAdaptive at κ = 1
      let Rabs₂ := lsys.inputSolution opt.1 ηabs Ψ₂               -- 12. abstrSolAdaptive at κ = 2
      let Rabs := if s.κ = 1 then Rabs₁ else Rabs₂                -- 12. R_abs(Δt*) at κ_k
      let rabsOpt := rad Rabs                                     -- 12. r^{(λ*)}_abs,k
      let κ' := tuneAbstrOrder le ζK s.φ rabsOpt s.rabs           -- 13. tuneAbstrOrder
        (dbox Rabs₁) (dbox Rabs₂) s.κ
      let φk := estimateGain le ζδ ((1 / ζδ) ^ opt.2) rabs1 rabsOpt opt.2 fuel -- 16. estimateGain
      let Rt := p₂.2.1 ⊞ Rabs                                     -- 17. R(t_{k+1})
      let Rτ := p₂.2.2 ⊞ Rabs                                     -- 17. R(τ_{k+1})
      some { t := s.t + opt.1, R := Reduce.reduce Rt o,           -- 18. redAdaptive
             Rτ := Reduce.reduce Rτ o, h := hk, φ := φk, κ := κ', rabs := rabsOpt }
    | _, _ => none

/-- Iterate [1, Alg. 2] while `t_k < t_end`, as `Alg. 1`'s line 2 does. -/
noncomputable def NonlinearSys.adaptRun (sys : NonlinearSys n m) (U : S m)
    (lin : Vec ℝ n → Vec ℝ m → Mat ℝ n n × Mat ℝ n m) (Φ : ℕ → S n → S n → S n)
    (sub : S n → S n → Bool) (enlarge : S n → S n) (le : ℝ → ℝ → Bool) (rad : S n → ℝ)
    (dbox : S n → Fin n → ℝ) (ζδ ζh ζZ ζK tend : ℝ) (ηlin ηabs o fuel : ℕ)
    (s₀ : NonlinearSys.AdaptState S n) : ℕ → Option (NonlinearSys.AdaptState S n)
  | 0 => some s₀
  | k + 1 =>
    match sys.adaptRun U lin Φ sub enlarge le rad dbox ζδ ζh ζZ ζK tend ηlin ηabs o fuel s₀ k with
    | none => none
    | some s =>
      if s.t < tend                                               -- the horizon of Alg. 1 line 2
      then sys.adaptStep U lin Φ sub enlarge le rad dbox ζδ ζh ζZ ζK ηlin ηabs o fuel s
      else some s

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
