module

public import CORALean.ContDynamics.NonlinearSys.Theorems.Reparametrize

@[expose] public section

/-!
# A run before the guard is a run of the pancake-scaled system

CORA's `guardIntersect_pancake` replaces `f` by `F(x, u) = g(x) f(x, u)` with
`g(x) = (c·x − b)/p`, `c·x = b` the guard hyperplane. A classical run that stays strictly on
the positive side of the hyperplane up to `T` is, reparametrized by `NonlinearSys.reparametrize`,
a run of `F` on `[0, S]` that passes through the same states: the original reach set up to the
hit is inside the scaled system's.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Set ContSet

variable {n m : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- A run on `[0, T]` with `b < c·x(t)` is, at some `s ∈ [0, S]`, at each of its states, on a run of
`F = ((c·x − b)/p) f` from the same `R₀` and `U`. -/
theorem NonlinearSys.pancake_isTrajectory (sys : NonlinearSys n m) (T : ℝ) (hT : 0 ≤ T)
    (R₀ : S n) (U : S m) (c : Vec ℝ n) (b p : ℝ) (hp : 0 < p) (x : ℝ → Vec ℝ n)
    (u : ℝ → Vec ℝ m) (hrun : sys.IsTrajectory (Icc 0 T) R₀ U x u)
    (hpos : ∀ t ∈ Icc 0 T, b < c ⬝ᵥ x t) : -- --- STMT ---
    ∃ (S' : ℝ) (y : ℝ → Vec ℝ n) (v : ℝ → Vec ℝ m), 0 ≤ S' ∧
      (⟨fun z w => ((c ⬝ᵥ z - b) / p) • sys.f z w, sys.q, sys.g⟩ : NonlinearSys n m).IsTrajectory
        (Icc 0 S') R₀ U y v ∧ ∀ t ∈ Icc 0 T, ∃ s ∈ Icc 0 S', y s = x t := by -- --- PROOF ---
  have hgc : Continuous (fun z : Vec ℝ n => (c ⬝ᵥ z - b) / p) := by
    unfold dotProduct; fun_prop
  obtain ⟨σ, h0, -, hmaps, -, hy, himg⟩ := sys.reparametrize T hT x u
    (fun z => (c ⬝ᵥ z - b) / p) hrun.flow hgc.continuousOn
    (fun t ht => div_pos (sub_pos.2 (hpos t ht)) hp)
  set S' := ∫ r in (0 : ℝ)..T, ((c ⬝ᵥ x r - b) / p)⁻¹
  refine ⟨S', x ∘ σ, u ∘ σ, ?_, ⟨?_, fun s hs => (hrun.input _ (hmaps hs)), hy⟩, ?_⟩
  · exact intervalIntegral.integral_nonneg hT (fun r hr =>
      inv_nonneg.2 (div_pos (sub_pos.2 (hpos r hr)) hp).le)
  · simpa [h0] using hrun.init
  · intro t ht
    have : x t ∈ (x ∘ σ) '' Icc 0 S' := by rw [himg]; exact ⟨t, ht, rfl⟩
    obtain ⟨s, hs, e⟩ := this
    exact ⟨s, hs, e⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
