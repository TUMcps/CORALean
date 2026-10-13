import CORALean.ContDynamics.LinearSys.Definitions.ReachFloatInputInvariant
import CORALean.ContDynamics.LinearSys.Operations.ReachFloatInputStep
import CORALean.ContDynamics.LinearSys.Theorems.ExpIntegralAddMulVec
import CORALean.ContDynamics.LinearSys.Theorems.InputReachSeparationSubset
import CORALean.ContSet.ContSet.Theorems.IsBoundedConstruct
import Mathlib.Algebra.Order.Ring.Star

/-!
# One pass of `reachFloatInput`'s loop keeps what its state owes

The free motion and the constant's contribution advance together:
`e^{A(a+Δt)} x₀ + Γ(a+Δt) ũ = e^{AΔt}(e^{Aa} x₀ + Γ(a) ũ) + Γ(Δt) ũ`
(`expIntegral_add_mulVec`), which `[e^{AΔt}] H ⊕ P̃(Δt)` holds once `e^{AΔt}`
is in the float box and `Γ(Δt) ũ` in `P̃(Δt)`. The `Ũ`-input's share comes
apart at `Δt` (`inputReach_separation_subset`): its first step carried across
`t_{k+1}`, which the propagated one-step set holds, plus its share by
`t_{k+1}`, which `P^R(t_{k+1})` holds.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float NormedSpace Matrix Pointwise

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.reachFloatInputStep_invariant (sys : LinearSys 𝕋 n) {Δt : ℝ} (hΔt : 0 ≤ Δt)
    {X₀ : Set (Vec ℝ n)} {ũ : Vec ℝ n} {Ũ : Zonotope (Vec 𝕋 n)} {eAΔt : Interval (Mat 𝕋 n n)}
    {Pu : Zonotope (Vec 𝕋 n)} (ρ : ℕ) (heA : exp (Δt • Scalar.toRealMat sys.A) ∈ eAΔt.construct)
    (hPu : Real.MatExp.expIntegral (Scalar.toRealMat sys.A) Δt *ᵥ ũ ∈ Pu.construct) {k : ℕ}
    {s : Zonotope (Vec 𝕋 n) × Zonotope (Vec 𝕋 n) × Zonotope (Vec 𝕋 n) × Zonotope (Vec 𝕋 n)}
    (h : sys.ReachFloatInputInvariant Δt X₀ ũ Ũ k s) :
    sys.ReachFloatInputInvariant Δt X₀ ũ Ũ (k + 1)
      (LinearSys.reachFloatInputStep eAΔt Pu ρ s) := by -- --- PROOF ---
  obtain ⟨h1, h2, h3, h4⟩ := h
  set A := Scalar.toRealMat sys.A with hA
  -- `[e^{AΔt}] Z` holds `e^{AΔt} z`
  have hmt : ∀ {Z : Zonotope (Vec 𝕋 n)} {z : Vec ℝ n}, z ∈ Z.construct → exp (Δt • A) *ᵥ z
      ∈ ContSet.construct (Mtimes.mtimes (𝕄 := fun m n => Interval (Mat 𝕋 m n))
        (S := fun k => Zonotope (Vec 𝕋 k)) eAΔt Z) :=
    fun {Z} {_} hz => Mtimes.mtimes_outer (𝕄 := fun m n => Interval (Mat 𝕋 m n))
      (S := fun k => Zonotope (Vec 𝕋 k)) eAΔt Z
      (Set.mem_biUnion heA (Set.mem_image_of_mem _ hz))
  -- `e^{A(a+Δt)} = e^{AΔt} e^{Aa}`, both powers of the same matrix
  have hexp : ∀ a : ℝ, exp ((a + Δt) • A) = exp (Δt • A) * exp (a • A) := fun a => by
    rw [add_comm a Δt, add_smul]
    exact exp_add_of_commute (((Commute.refl A).smul_left _).smul_right _)
  -- the free motion and the constant's contribution, one step on
  have hnext : ∀ {Z : Zonotope (Vec 𝕋 n)} {a : ℝ}, 0 ≤ a → ∀ {x₀ : Vec ℝ n},
      exp (a • A) *ᵥ x₀ + Real.MatExp.expIntegral A a *ᵥ ũ ∈ Z.construct →
      exp ((a + Δt) • A) *ᵥ x₀ + Real.MatExp.expIntegral A (a + Δt) *ᵥ ũ ∈ ContSet.construct
        (Reduce.reduce (Mtimes.mtimes (𝕄 := fun m n => Interval (Mat 𝕋 m n))
          (S := fun k => Zonotope (Vec 𝕋 k)) eAΔt Z ⊞ Pu) ρ) := by
    intro Z a ha x₀ hz
    rw [hexp, ← Matrix.mulVec_mulVec, Real.MatExp.expIntegral_add_mulVec A ũ ha hΔt, ← add_assoc,
      ← Matrix.mulVec_add]
    exact Reduce.reduce_outer _ ρ (Plus.plus_outer _ _ (Set.add_mem_add (hmt hz) hPu))
  -- the one-step set carried across `t_{k+1}` rather than `t_k`
  have h4' : (fun y => exp ((((k + 1 : ℕ) : ℝ) * Δt) • A) *ᵥ y)
      '' sys.inputReach (S := fun k => Zonotope (Vec 𝕋 k)) Ũ Δt ⊆ ContSet.construct
        (Mtimes.mtimes (𝕄 := fun m n => Interval (Mat 𝕋 m n)) (S := fun k => Zonotope (Vec 𝕋 k))
          eAΔt s.2.2.2) := by
    rintro _ ⟨y, hy, rfl⟩
    have ht : (((k + 1 : ℕ) : ℝ) * Δt) = (k : ℝ) * Δt + Δt := by push_cast; ring
    simp only [ht, hexp, ← Matrix.mulVec_mulVec]
    exact hmt (h4 ⟨y, hy, rfl⟩)
  refine ⟨fun x₀ hx₀ => ?_, fun x₀ hx₀ τ hτ => ?_, fun y hy => ?_, h4'⟩
  · -- `H(t_{k+2})`
    have ht : (((k + 1 + 1 : ℕ) : ℝ) * Δt) = ((k + 1 : ℕ) : ℝ) * Δt + Δt := by push_cast; ring
    rw [ht]
    exact hnext (by positivity) (h1 x₀ hx₀)
  · -- `H(τ_{k+1})`
    have ht : (((k + 1 : ℕ) : ℝ) * Δt + τ) = ((k : ℝ) * Δt + τ) + Δt := by push_cast; ring
    rw [ht]
    exact hnext (by have := hτ.1; positivity) (h2 x₀ hx₀ τ hτ)
  · -- `P^R(t_{k+2})`: the first step carried across `t_{k+1}`, plus the share by `t_{k+1}`
    have ht : (((k + 1 + 1 : ℕ) : ℝ) * Δt) = Δt + ((k + 1 : ℕ) : ℝ) * Δt := by push_cast; ring
    rw [ht] at hy
    obtain ⟨p, hp, q, hq, rfl⟩ := sys.inputReach_separation_subset hΔt (by positivity)
      (CompactSet.isBounded_construct Ũ) hy
    exact Reduce.reduce_outer _ ρ (Plus.plus_outer _ _ ⟨q, h3 hq, p, h4' hp, add_comm q p⟩)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
