module

public import CORALean.ContDynamics.NonlinDASys.Operations.SteadyState
public import CORALean.ContDynamics.NonlinDASys.Theorems.NewtonIterateSpec

@[expose] public section

/-!
# What `steadyState` returns

The returned `(x', y')` is `(x + Δx, y + Δy)` for an iterate `(x, y)`, the stacked step having
2-norm below `tol`, the code's own stopping test, and, when the block matrix `M` is invertible
there, solving `A Δx + C Δy = -f` and `D Δx + F Δy = -g`. The test is on the step: `f = 0` and
`g = 0` at `(x', y')` are not claimed.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      14-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n p m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The result is a Newton step of stacked norm below `tol` taken from some iterate. -/
theorem NonlinDASys.steadyState_spec (sys : NonlinDASys n p m)
    (A : Vec ℝ n → Vec ℝ p → Vec ℝ m → Mat ℝ n n) (C : Vec ℝ n → Vec ℝ p → Vec ℝ m → Mat ℝ n p)
    (D : Vec ℝ n → Vec ℝ p → Vec ℝ m → Mat ℝ p n) (F : Vec ℝ n → Vec ℝ p → Vec ℝ m → Mat ℝ p p)
    (tol : ℝ) (fuel : ℕ) (x₀ : Vec ℝ n) (y₀ : Vec ℝ p) (u₀ : Vec ℝ m) : -- --- STMT ---
    ∀ x' y', (x', y') ∈ sys.steadyState A C D F tol fuel x₀ y₀ u₀ →
      ∃ (x : Vec ℝ n) (y : Vec ℝ p) (Δx : Vec ℝ n) (Δy : Vec ℝ p), x' = x + Δx ∧ y' = y + Δy ∧
        Real.sqrt (∑ i, Δx i ^ 2 + ∑ j, Δy j ^ 2) < tol ∧
        (IsUnit (Matrix.fromBlocks (A x y u₀) (C x y u₀) (D x y u₀) (F x y u₀)).det →
          A x y u₀ *ᵥ Δx + C x y u₀ *ᵥ Δy = -(sys.f x y u₀) ∧
          D x y u₀ *ᵥ Δx + F x y u₀ *ᵥ Δy = -(sys.g x y u₀)) := by -- --- PROOF ---
  intro x' y' (h : sys.steadyState A C D F tol fuel x₀ y₀ u₀ = some (x', y'))
  unfold NonlinDASys.steadyState at h
  obtain ⟨z', hz', hz⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨z, hz1, hs⟩ := newtonIterate_spec _ _ fuel _ z' hz'
  dsimp only at hz1 hs
  -- name the stacked step, and split it into its two blocks
  generalize hΔ : (fromBlocks (A (fun i => z (Sum.inl i)) (fun j => z (Sum.inr j)) u₀)
    (C (fun i => z (Sum.inl i)) (fun j => z (Sum.inr j)) u₀)
    (D (fun i => z (Sum.inl i)) (fun j => z (Sum.inr j)) u₀)
    (F (fun i => z (Sum.inl i)) (fun j => z (Sum.inr j)) u₀))⁻¹ *ᵥ
    -Sum.elim (sys.f (fun i => z (Sum.inl i)) (fun j => z (Sum.inr j)) u₀)
      (sys.g (fun i => z (Sum.inl i)) (fun j => z (Sum.inr j)) u₀) = Δ at hz1 hs
  have hx : x' = (fun i => z (Sum.inl i)) + fun i => Δ (Sum.inl i) := by
    rw [← (Prod.mk.inj hz).1, hz1]; rfl
  have hy : y' = (fun j => z (Sum.inr j)) + fun j => Δ (Sum.inr j) := by
    rw [← (Prod.mk.inj hz).2, hz1]; rfl
  refine ⟨fun i => z (Sum.inl i), fun j => z (Sum.inr j), fun i => Δ (Sum.inl i),
    fun j => Δ (Sum.inr j), hx, hy, ?_, fun hdet => ?_⟩
  · rw [← Fintype.sum_sum_type (fun i => Δ i ^ 2)]
    exact of_decide_eq_true hs
  · -- the block system, solved
    have hMΔ := congrArg (Matrix.fromBlocks (A (fun i => z (Sum.inl i)) (fun j => z (Sum.inr j)) u₀)
        (C (fun i => z (Sum.inl i)) (fun j => z (Sum.inr j)) u₀)
        (D (fun i => z (Sum.inl i)) (fun j => z (Sum.inr j)) u₀)
        (F (fun i => z (Sum.inl i)) (fun j => z (Sum.inr j)) u₀) *ᵥ ·) hΔ.symm
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec] at hMΔ
    rw [← Sum.elim_comp_inl_inr Δ, Matrix.fromBlocks_mulVec] at hMΔ
    constructor
    · funext i
      have := congrFun hMΔ (Sum.inl i)
      simp only [Sum.elim_inl, Pi.add_apply, Pi.neg_apply] at this
      exact this
    · funext j
      have := congrFun hMΔ (Sum.inr j)
      simp only [Sum.elim_inr, Pi.add_apply, Pi.neg_apply] at this
      exact this

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
