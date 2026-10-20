module

public import CORALean.ContDynamics.NonlinearSys.Theorems.IsTrajectoryHasDerivWithinAt
public import CORALean.ContDynamics.NonlinearSys.Theorems.IsTrajectoryOfHasDerivWithinAt
public import CORALean.ContDynamics.NonlinearSys.Theorems.Reparametrize

@[expose] public section

/-!
# A run before the guard is a run of the pancake-scaled system

CORA's `guardIntersect_pancake` replaces `f` by `F(x, u) = g(x) f(x, u)` with
`g(x) = (c·x − b)/p`, `c·x = b` the guard hyperplane. A run with a continuous field along it, so
a classical one (`IsTrajectory.hasDerivWithinAt`), that stays strictly on the positive side of
the hyperplane up to `T` is, reparametrized by `NonlinearSys.reparametrize`, a run of `F` on
`[0, S]` that passes through the same states: the original reach set up to the hit is inside the
scaled system's. The time change is the classical chain rule, which is why the field's
continuity is asked; a Carathéodory time change would need the chain rule for absolutely
continuous functions.

## Inputs
* `sys` – system
* `T` – final time
* `R₀` – initial set
* `U` – input set
* `c` – guard normal
* `b` – guard offset
* `p` – scaling constant
* `x` – state trajectory
* `u` – input trajectory
* `y` – output trajectory

## Hypotheses
* `hT` – final time nonnegative
* `hp` – scaling constant positive
* `hrun` – trajectory of the system
* `hf` – field continuous along run
* `hpos` – run strictly before the guard

## Conclusion
* the states lie on a run of the scaled system
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   18-October-2026
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
    (u : ℝ → Vec ℝ m) {y : ℝ → Vec ℝ sys.q} (hrun : sys.IsTrajectory (Icc 0 T) R₀ U x u y)
    (hf : ContinuousOn (fun t => sys.f (x t) (u t)) (Icc 0 T))
    (hpos : ∀ t ∈ Icc 0 T, b < c ⬝ᵥ x t) : -- --- CONCL ---
    ∃ (S' : ℝ) (ξ : ℝ → Vec ℝ n) (v : ℝ → Vec ℝ m), 0 ≤ S' ∧
      (⟨fun z w => ((c ⬝ᵥ z - b) / p) • sys.f z w, sys.q, sys.g⟩ : NonlinearSys n m).IsTrajectory
        (Icc 0 S') R₀ U ξ v (fun s => sys.g (ξ s) (v s)) ∧
          ∀ t ∈ Icc 0 T, ∃ s ∈ Icc 0 S', ξ s = x t := by -- --- PROOF ---
  have hgc : Continuous (fun z : Vec ℝ n => (c ⬝ᵥ z - b) / p) := by
    unfold dotProduct; fun_prop
  obtain ⟨σ, h0, -, hmaps, hσ, hy, himg⟩ := sys.reparametrize T hT x u
    (fun z => (c ⬝ᵥ z - b) / p) (fun t ht => hrun.hasDerivWithinAt ⟨le_rfl, hT⟩ hf ht)
    hgc.continuousOn (fun t ht => div_pos (sub_pos.2 (hpos t ht)) hp)
  set S' := ∫ r in (0 : ℝ)..T, ((c ⬝ᵥ x r - b) / p)⁻¹
  have hS' : 0 ≤ S' := intervalIntegral.integral_nonneg hT (fun r hr =>
    inv_nonneg.2 (div_pos (sub_pos.2 (hpos r hr)) hp).le)
  -- the scaled field along the reparametrized run, continuous, so integrable
  have hσc : ContinuousOn σ (Icc 0 S') := fun s hs => (hσ s hs).continuousWithinAt
  have hFc : ContinuousOn (fun s => ((c ⬝ᵥ x (σ s) - b) / p) • sys.f (x (σ s)) (u (σ s)))
      (Icc 0 S') :=
    (hgc.comp_continuousOn (hrun.cont.comp hσc hmaps)).smul (hf.comp hσc hmaps)
  refine ⟨S', x ∘ σ, u ∘ σ, hS', NonlinearSys.IsTrajectory.of_hasDerivWithinAt (convex_Icc 0 S')
    ⟨le_rfl, hS'⟩ (by simpa [h0] using hrun.init) (fun s hs => hrun.input _ (hmaps hs)) hy
    (fun s hs => (hFc.mono (uIcc_subset_Icc ⟨le_rfl, hS'⟩ hs)).intervalIntegrable), ?_⟩
  intro t ht
  have : x t ∈ (x ∘ σ) '' Icc 0 S' := by rw [himg]; exact ⟨t, ht, rfl⟩
  obtain ⟨s, hs, e⟩ := this
  exact ⟨s, hs, e⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
