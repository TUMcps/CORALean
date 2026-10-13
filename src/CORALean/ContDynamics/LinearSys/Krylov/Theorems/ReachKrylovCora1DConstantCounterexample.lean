import CORALean.ContDynamics.LinearSys.Definitions.ClassicalTrajectory
import CORALean.ContDynamics.LinearSys.Krylov.Operations.ReachKrylovCora1D
import CORALean.ContSet.Zonotope.Real.Theorems.MemConstruct
import CORALean.ContSet.Zonotope.Real.Theorems.OfPointMemIff
import CORALean.ContSet.Zonotope.Real.Theorems.PlusExact
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# CORA's Krylov `reach` drops the constant input `c`

`reach` with `linAlg = 'krylov'` on `linearSys(0, 1, 1)` (`A = 0`, `B = 1`, `c = 1`, default
`C = 1`, `D = 0`, `k = 0`) from `R0 = {0}` with `U = {0}`: `ẋ = 1`, so the run from `0` is at
`x(Δt) = Δt`. `Krylov.reachKrylovCora1D` is CORA's first time-point set on this path; it does
not read `c`, and here it is `zonotope([0, ε, ε])` (`{0}` at `krylovError ≤ 2 eps`), within `2ε`
of `0`. So `Δt` is missed for every `krylovError = ε ∈ [0, Δt/2)` (CORA checks `ε ≥ 0`), every
`eps ≥ 0` and every order `o ≥ 2` (`o = 1` would box the two generators, the same interval). In
CORALean's `LinearSys` the input `B u + c = 1` is the input set `{1}`. The Arnoldi pass on
`[0 0; 0 0]` from `e₂` is exact, and breaks down, so the multiprecision branch is never run.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

/-- CORA's first Krylov time-point set for `ẋ = 0·x + 1·u + 1`, `R0 = {0}`, `U = {0}`, step `Δt`,
misses `x(Δt) = Δt` of the run, for `0 ≤ krylovError < Δt/2`, any `eps ≥ 0` and order `o ≥ 2`. -/
theorem Krylov.reachKrylovCora1D_constant_counterexample (Δt ε eps : ℝ) (o : ℕ)
    (hε0 : 0 ≤ ε) (hε : 2 * ε < Δt) (heps : 0 ≤ eps) (ho : 2 ≤ o) :
    ∃ R, Krylov.reachKrylovCora1D 0 1 1 Δt ε eps o = some R ∧
      ∃ x w : ℝ → Vec ℝ 1,
        (LinearSys.mk (0 : Mat ℝ 1 1) : LinearSys ℝ 1).ClassicalTrajectory
          (S := fun k => Set (Vec ℝ k)) (Set.Icc 0 Δt) {0} {fun _ => 1} x w ∧
        x Δt ∉ R.construct := by -- --- PROOF ---
  -- Arnoldi on the zero matrix from `e₂`: `v⁽¹⁾ = e₂`, `h₁,₁ = h₂,₁ = 0`
  set K := Krylov.arnoldi (!![0, 1 * 0; 0, 0] : Mat ℝ 2 2) (Pi.single 1 1) 1 with hKdef
  have hK0 : K.1 0 = Pi.single 1 1 := by
    simp [K, Krylov.arnoldi, norm₂, Fin.sum_univ_two]
  have h10 : K.2 1 0 = 0 := by
    simp [K, Krylov.arnoldi, Krylov.gramSchmidtStep, norm₂, Fin.sum_univ_two, dotProduct]
  have h00 : K.2 0 0 = 0 := by
    simp [K, Krylov.arnoldi, Krylov.gramSchmidtStep, norm₂, Fin.sum_univ_two, dotProduct]
  -- the breakdown branch is taken and `c_new = 1 · (1 · 0) · e⁰ = 0`
  simp only [Krylov.reachKrylovCora1D, ← hKdef, h10, hK0, h00, not_lt.2 heps, if_false]
  refine ⟨_, rfl, fun s => fun _ => s, fun _ => fun _ => 1, ⟨?_, fun _ _ => rfl, ?_⟩, ?_⟩
  -- the run `x(s) = s` from `0` under the input `B u + c = 1`
  · exact funext fun _ => rfl
  · intro t _
    refine HasDerivAt.hasDerivWithinAt (hasDerivAt_pi.2 fun _ => (hasDerivAt_id t).congr_deriv ?_)
    simp
  -- every point of CORA's set is within `2 |ε|` of `0`
  intro hx
  have hred : ∀ Z : Zonotope (Vec ℝ 1), Z.h ≤ 2 → Z.reduceGirard o = Z := by
    intro Z hZ
    unfold Zonotope.reduceGirard
    rw [dif_neg (by omega)]
  by_cases hp : 2 * eps < ε
  -- `krylovError > 2 eps`: two generators `ε`, so `|Δt| ≤ 2ε`
  · simp only [hp, if_true] at hx
    rw [hred _ (by simp [Zonotope.plus, Zonotope.ofPoint]), ← Zonotope.plus_exact,
      ← Zonotope.plus_exact] at hx
    obtain ⟨y, ⟨a, ha, b, hb, rfl⟩, p, hp, hxe⟩ := hx
    rw [Zonotope.mem_ofPoint_iff] at hp
    obtain ⟨β, hβ, ha⟩ := Zonotope.mem_construct_iff.1 ha
    obtain ⟨γ, hγ, hb⟩ := Zonotope.mem_construct_iff.1 hb
    have h0 := congrFun hxe 0
    simp only [Pi.add_apply, ha 0, hb 0, hp, Fin.sum_univ_one] at h0
    simp at h0
    have h1 := abs_le.1 (hβ 0)
    have h2 := abs_le.1 (hγ 0)
    nlinarith
  -- otherwise the set is the point `0`
  · simp only [hp, if_false] at hx
    rw [hred _ (by simp [Zonotope.plus, Zonotope.ofPoint]), Zonotope.mem_construct_iff] at hx
    obtain ⟨β, -, hx⟩ := hx
    have h0 := hx 0
    simp [Zonotope.plus, Zonotope.ofPoint] at h0
    linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
