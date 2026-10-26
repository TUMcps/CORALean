module

public import Mathlib.Topology.Order.IntermediateValue
public import CORALean.HybridDynamics.TimeTriggered.Operations.SpaceTriggered
public import CORALean.HybridDynamics.TimeTriggered.Theorems.HasDerivWithinAtIciOfDeriv
public import CORALean.HybridDynamics.TimeTriggered.Theorems.LipschitzSolutionUnique

@[expose] public section

/-!
# An execution of the original automaton follows two solutions

An execution of `spaceTriggered` of duration `d` ends, in `m₁`, at a solution of `ẋ = f₁(x)` from an
initial state at time `d` that stays in `a·x ≤ b`, and in `m₂` at a solution of `ẋ = f₂(x)` from the
guard point `z(τ)` reached by such a solution at the time `τ` of the transition, [1, Def. 6]. The
chain of continuous successors of an execution is replaced by the solutions, which are unique
(`aux_lipschitzPiece_eq`): the statement is for every solution from the initial state, so the next
piece is a shifted one. The invariant `a·x ≤ b` is read on `(0, t)` by [1, Def. 4], and holds on
`[0, t]` by continuity. [1, Cor. 1] builds its execution of `H_final` from it.

## Inputs
* `I` – initial states
* `f₁` – flow in the first mode
* `f₂` – flow in the second mode
* `a` – guard normal
* `b` – guard offset
* `K₁` – Lipschitz constant of the first flow
* `K₂` – Lipschitz constant of the second flow
* `d` – duration
* `m` – mode
* `x` – end state

## Hypotheses
* `hf₁` – first flow is Lipschitz
* `hf₂` – second flow is Lipschitz
* `h` – execution of the space-triggered automaton

## Conclusion
* the execution follows solutions of the two flows

## References

* [1] S. Bak, S. Bogomolov and M. Althoff. "Time-Triggered Conversion of Guards for Reachability
      Analysis of Hybrid Automata". Formal Modeling and Analysis of Timed Systems, 2017.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Set
open scoped NNReal

variable {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℝ X]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

section
variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- A piece `g` with `ġ = f(g)` on `(0, t)` equals a solution `w` of `ẋ = f(x)` it starts with. -/
private theorem aux_lipschitzPiece_eq {f : X → X} {K : ℝ≥0} (hf : LipschitzWith K f) {g w : ℝ → X}
    {t : ℝ} (ht : 0 < t) (hgd : DifferentiableOn ℝ g (Icc 0 t))
    (hgder : ∀ u ∈ Ioo 0 t, deriv g u = f (g u)) (hw : ∀ u ∈ Icc 0 t, HasDerivAt w (f (w u)) u)
    (h0 : g 0 = w 0) : ∀ u ∈ Icc 0 t, g u = w u :=
  ODE_solution_unique (v := fun _ => f) (a := 0) (b := t) (fun _ => hf) hgd.continuousOn
    (hasDerivWithinAt_Ici_of_deriv_eq hf.continuous ht hgd hgder)
    (fun u hu => (hw u hu).continuousAt.continuousWithinAt)
    (fun u hu => (hw u ⟨hu.1, hu.2.le⟩).hasDerivWithinAt) h0

end


/-- A bound that holds on `(0, t)` holds on `[0, t]` for a continuous function. -/
private theorem aux_le_of_Ioo {h : ℝ → ℝ} {t b : ℝ} (ht : 0 < t) (hc : ContinuousOn h (Icc 0 t))
    (hb : ∀ u ∈ Ioo 0 t, h u ≤ b) : -- --- CONCL ---
    ∀ u ∈ Icc 0 t, h u ≤ b := by -- --- PROOF ---
  have hcl : IsClosed (Icc 0 t ∩ h ⁻¹' Iic b) :=
    hc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hsub : Ioo 0 t ⊆ Icc 0 t ∩ h ⁻¹' Iic b := fun u hu => ⟨Ioo_subset_Icc_self hu, hb u hu⟩
  intro u hu
  have := closure_minimal hsub hcl
  rw [closure_Ioo ht.ne] at this
  exact (this hu).2


-- =======================================  MAIN THEOREM  ======================================= --

/-- The end state of an execution of `spaceTriggered`, as a value of the solutions of `f₁`, `f₂`. -/
theorem DiffInclAutomaton.spaceTriggered_isExec_orbit {I : Set X} {f₁ f₂ : X → X} {a : X} {b : ℝ}
    {K₁ K₂ : ℝ≥0} (hf₁ : LipschitzWith K₁ f₁) (hf₂ : LipschitzWith K₂ f₂) {d : ℝ} {m : Fin 2}
    {x : X} (h : (spaceTriggered I f₁ f₂ a b).IsExec d m x) : -- --- CONCL ---
    0 ≤ d ∧
      (m = 0 → ∃ x₀ ∈ I, ∀ z : ℝ → X, z 0 = x₀ → (∀ u ∈ Icc 0 d, HasDerivAt z (f₁ (z u)) u) →
        z d = x ∧ (0 < d → ∀ u ∈ Icc 0 d, inner ℝ a (z u) ≤ b)) ∧
      (m = 1 → ∃ x₀ ∈ I, ∃ τ, 0 ≤ τ ∧ τ ≤ d ∧ ∀ z w : ℝ → X, z 0 = x₀ →
        (∀ u ∈ Icc 0 τ, HasDerivAt z (f₁ (z u)) u) → w 0 = z τ →
        (∀ u ∈ Icc 0 (d - τ), HasDerivAt w (f₂ (w u)) u) →
          w (d - τ) = x ∧ inner ℝ a (z τ) = b ∧ (∀ u ∈ Icc 0 τ, inner ℝ a (z u) ≤ b) ∧
            (spaceTriggered I f₁ f₂ a b).IsExec τ 0 (z τ)) := by -- --- PROOF ---
  set Hs := spaceTriggered I f₁ f₂ a b with hHs
  induction h with
  | init hx =>
    -- an initial state is in `m₁`, the empty solution of duration zero
    rename_i m x
    have hm : m = 0 := by
      by_contra hne
      simp [hHs, spaceTriggered, hne] at hx
    subst hm
    simp only [hHs, spaceTriggered, if_true] at hx
    exact ⟨le_rfl, fun _ => ⟨x, hx, fun z hz _ => ⟨hz, fun h0 => absurd h0 (lt_irrefl _)⟩⟩,
      fun h01 => by simp at h01⟩
  | jump h e he hm hx ih =>
    -- the transition is taken at the end of the `m₁` solution, which is on the guard
    rename_i d m x
    have hE := DiffInclAutomaton.IsExec.jump h e he hm hx
    obtain rfl : e = ⟨0, {x | inner ℝ a x = b}, id, 1⟩ := by simpa [hHs, spaceTriggered] using he
    have hm0 : (0 : Fin 2) = m := hm
    subst hm0
    obtain ⟨x₀, hx₀, hz⟩ := ih.2.1 rfl
    refine ⟨ih.1, fun h01 => by simp at h01, fun _ => ⟨x₀, hx₀, d, ih.1, le_rfl, ?_⟩⟩
    intro z w hz0 hzd hw0 hwd
    obtain ⟨hzx, hzle⟩ := hz z hz0 hzd
    have hgz : inner ℝ a (z d) = b := by rw [hzx]; exact hx
    refine ⟨by simpa [hzx] using hw0.trans hzx, hgz, fun u hu => ?_, by rw [hzx]; exact h⟩
    rcases ih.1.eq_or_lt with hd | hd
    · have hu0 : u = d := by linarith [hu.1, hu.2]
      rw [hu0, hgz]
    · exact hzle hd u hu
  | flow h hf' ih =>
    rename_i d t m x x'
    obtain ⟨ht, g, hgd, hg0, hgt, hgi⟩ := hf'
    refine ⟨by linarith [ih.1], ?_⟩
    fin_cases m
    · -- a piece in `m₁`: the solution continues as the piece, and the invariant holds on it
      have hder : ∀ u ∈ Ioo 0 t, deriv g u = f₁ (g u) := fun u hu => by
        simpa [hHs, spaceTriggered] using (hgi u hu).2
      have hinv : ∀ u ∈ Ioo 0 t, inner ℝ a (g u) ≤ b := fun u hu => by
        simpa [hHs, spaceTriggered] using (hgi u hu).1
      have hleb : ∀ u ∈ Icc 0 t, inner ℝ a (g u) ≤ b := aux_le_of_Ioo ht
        ((continuous_const.inner continuous_id).comp_continuousOn hgd.continuousOn) hinv
      obtain ⟨x₀, hx₀, hz⟩ := ih.2.1 rfl
      refine ⟨fun _ => ⟨x₀, hx₀, fun z hz0 hzd => ?_⟩, fun h01 => by simp at h01⟩
      obtain ⟨hzx, hzle⟩ := hz z hz0 fun u hu => hzd u ⟨hu.1, hu.2.trans (by linarith)⟩
      -- the piece agrees with `z` shifted to start at `d`
      have hshift : ∀ u ∈ Icc 0 t, g u = z (d + u) := aux_lipschitzPiece_eq hf₁ ht hgd hder
        (fun u hu => by
          have := (hzd (d + u) ⟨by linarith [ih.1, hu.1], by linarith [hu.2]⟩).comp_const_add d u
          simpa using this) (by simp [hg0, hzx])
      refine ⟨by rw [← hgt, hshift t ⟨ht.le, le_rfl⟩], fun _ u hu => ?_⟩
      by_cases hud : u ≤ d
      · rcases ih.1.eq_or_lt with hd | hd
        · have hu0 : u = d := by linarith [hu.1]
          rw [hu0, hzx, ← hg0]
          exact hleb 0 ⟨le_rfl, ht.le⟩
        · exact hzle hd u ⟨hu.1, hud⟩
      · have := hleb (u - d) ⟨by linarith, by linarith [hu.2]⟩
        rwa [hshift (u - d) ⟨by linarith, by linarith [hu.2]⟩, add_sub_cancel] at this
    · -- a piece in `m₂`: the solution of `f₂` continues as the piece
      have hder : ∀ u ∈ Ioo 0 t, deriv g u = f₂ (g u) := fun u hu => by
        simpa [hHs, spaceTriggered] using (hgi u hu).2
      obtain ⟨x₀, hx₀, τ, hτ0, hτd, hz⟩ := ih.2.2 rfl
      refine ⟨fun h10 => by simp at h10, fun _ => ⟨x₀, hx₀, τ, hτ0, by linarith, ?_⟩⟩
      intro z w hz0 hzd hw0 hwd
      obtain ⟨hwx, hga, hle, hex⟩ := hz z w hz0 hzd hw0 fun u hu =>
        hwd u ⟨hu.1, hu.2.trans (by linarith)⟩
      refine ⟨?_, hga, hle, hex⟩
      -- the piece agrees with `w` shifted to start at `d - τ`
      have hshift := aux_lipschitzPiece_eq hf₂ ht hgd hder
        (w := fun u => w (d - τ + u)) (fun u hu => by
          have := (hwd (d - τ + u) ⟨by linarith [hu.1, hτd], by linarith [hu.2]⟩).comp_const_add
            (d - τ) u
          simpa using this) (by simp [hg0, hwx])
      rw [← hgt, hshift t ⟨ht.le, le_rfl⟩]
      congr 1; ring

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
