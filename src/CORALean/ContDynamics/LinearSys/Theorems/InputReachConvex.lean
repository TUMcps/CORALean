import CORALean.ContDynamics.LinearSys.Theorems.IntervalIntegrableExpSubMulVec

/-!
# The input reach set is convex

Half of what an inner approximation asks of the set `timePointStep` is measured
against. Mixing two admissible inputs pointwise is admissible — that is `U`'s
own convexity — and the integral is linear in the input, so the contributions
mix the same way. Integrability is what makes the second step legal, and it is
where `U`'s boundedness enters.

The other half, closedness, is *not* here and is not a technicality. Closing
`inputReach` is the statement that a limit of contributions is itself the
contribution of some admissible input, which is a weak-compactness argument
about the admissible inputs in `L^∞` — Banach–Alaoglu and Mazur, neither of
which this development has. So the continuous-time inner approximations go
through `expIntegral_mem_inputReach` and a zonotope instead, and never through
this set.
-/

-- Authors:       Claude Opus 5
-- Written:       08-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar NormedSpace MeasureTheory

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every point the input can drive the system to over a window forms a convex
set, whenever the input set is convex and bounded. -/
theorem LinearSys.inputReach_convex (sys : LinearSys 𝕋 n) {U : S n} {τ : ℝ} (hτ : 0 ≤ τ)
    (hconv : Convex ℝ (construct U)) (hbdd : Bornology.IsBounded (construct U)) :
    Convex ℝ (sys.inputReach U τ) := by -- --- PROOF ---
  rintro _ ⟨u₁, hu₁, hm₁, rfl⟩ _ ⟨u₂, hu₂, hm₂, rfl⟩ a b ha hb hab
  set A := toRealMat sys.A with hA
  have hi₁ := intervalIntegrable_expSub_mulVec (A := A) (c := τ) hτ hbdd hu₁ hm₁
  have hi₂ := intervalIntegrable_expSub_mulVec (A := A) (c := τ) hτ hbdd hu₂ hm₂
  have hsplit : ∀ s : ℝ, exp ((τ - s) • A) *ᵥ (a • u₁ s + b • u₂ s)
      = a • (exp ((τ - s) • A) *ᵥ u₁ s) + b • (exp ((τ - s) • A) *ᵥ u₂ s) := fun s => by
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
  -- the integral is linear in the input, both halves being integrable
  have hj₁ : IntervalIntegrable (fun s => a • (exp ((τ - s) • A) *ᵥ u₁ s)) volume 0 τ :=
    hi₁.smul a
  have hj₂ : IntervalIntegrable (fun s => b • (exp ((τ - s) • A) *ᵥ u₂ s)) volume 0 τ :=
    hi₂.smul b
  have hval : (∫ s in (0:ℝ)..τ, exp ((τ - s) • A) *ᵥ (a • u₁ s + b • u₂ s))
      = a • (∫ s in (0:ℝ)..τ, exp ((τ - s) • A) *ᵥ u₁ s)
        + b • (∫ s in (0:ℝ)..τ, exp ((τ - s) • A) *ᵥ u₂ s) := by
    rw [intervalIntegral.integral_congr (g := fun s => a • (exp ((τ - s) • A) *ᵥ u₁ s)
        + b • (exp ((τ - s) • A) *ᵥ u₂ s)) fun s _ => hsplit s,
      intervalIntegral.integral_add hj₁ hj₂,
      intervalIntegral.integral_smul, intervalIntegral.integral_smul]
  -- and the mixed input is admissible pointwise, which is `U`'s own convexity
  exact ⟨fun s => a • u₁ s + b • u₂ s, fun s hs => hconv (hu₁ s hs) (hu₂ s hs) ha hb hab,
    (hm₁.const_smul a).add (hm₂.const_smul b), hval.symm⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
