module

public import CORALean.Specification.STL.Operations.DFormulaBound

@[expose] public section

/-!
# A bounded formula is decided by the window of its bound

[1, Sec. II-B (bound)]: the bound of a formula, the maximum over the sums of all nested upper
bounds, is a conservative trajectory length to decide its satisfiability; `□[0,10] □[1,6] φ`
needs `N ≥ 10 + 6 = 16`. Whether `φ` holds at `t` depends only on the run on `[t, t + bound(φ)]`;
the bound of the example is `16` for a predicate `φ`. That the bound takes time linear in the
formula is the shape of its structural recursion, one step per operator.

## References

* [1] V. Raman, A. Donzé, M. Maasoumy, R. M. Murray, A. Sangiovanni-Vincentelli and
      S. A. Seshia. "Model Predictive Control with Signal Temporal Logic Specifications". In
      Proc. of the 53rd IEEE Conference on Decision and Control (CDC), pp. 81-87, 2014.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {X : Type}


-- =======================================  MAIN THEOREM  ======================================= --

theorem STL.DFormula.sat_congr : -- --- STMT ---
    (∀ (φ : STL.DFormula X) (x y : ℕ → X) (t : ℕ),
      (∀ i ≤ φ.bound, x (t + i) = y (t + i)) → (φ.Sat x t ↔ φ.Sat y t)) ∧
    ∀ μ : X → ℝ, (STL.DFormula.always 0 10 (by norm_num)
      (STL.DFormula.always 1 6 (by norm_num) (.pred μ))).bound = 16 := by -- --- PROOF ---
  refine ⟨fun φ => ?_, fun μ => rfl⟩
  induction φ with
  | pred μ =>
    intro x y t h
    have h0 := h 0 (Nat.zero_le _)
    simp only [add_zero] at h0
    simp only [STL.DFormula.Sat, h0]
  | npred μ =>
    intro x y t h
    have h0 := h 0 (Nat.zero_le _)
    simp only [add_zero] at h0
    simp only [STL.DFormula.Sat, h0]
  -- the window of each operand lies inside that of the conjunction
  | and φ ψ ihφ ihψ =>
    intro x y t h
    simp only [STL.DFormula.bound] at h
    exact and_congr (ihφ x y t fun i hi => h i (by omega)) (ihψ x y t fun i hi => h i (by omega))
  | or φ ψ ihφ ihψ =>
    intro x y t h
    simp only [STL.DFormula.bound] at h
    exact or_congr (ihφ x y t fun i hi => h i (by omega)) (ihψ x y t fun i hi => h i (by omega))
  | always a b hab φ ih =>
    -- a step `t' ≤ t + b` of the window leaves `bound(φ)` steps inside `t + bound`
    intro x y t h
    simp only [STL.DFormula.bound] at h
    refine forall₂_congr fun t' ht' => ih x y t' fun i hi => ?_
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp ht'
    have h' := h (t' - t + i) (by omega)
    rwa [show t + (t' - t + i) = t' + i by omega] at h'
  -- as for `□`, with a witness in place of every step
  | eventually a b hab φ ih =>
    intro x y t h
    simp only [STL.DFormula.bound] at h
    refine exists_congr fun t' => and_congr_right fun ht' => ih x y t' fun i hi => ?_
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp ht'
    have h' := h (t' - t + i) (by omega)
    rwa [show t + (t' - t + i) = t' + i by omega] at h'
  | «until» a b hab φ ψ ihφ ihψ =>
    intro x y t h
    simp only [STL.DFormula.bound] at h
    refine exists_congr fun t' => and_congr_right fun ht' =>
      and_congr (ihψ x y t' fun i hi => ?_) (forall₂_congr fun s hs => ihφ x y s fun i hi => ?_)
    -- `φ₂` at the witness, then `φ₁` at each step `s ≤ t'`, both inside the window
    · obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp ht'
      have h' := h (t' - t + i) (by omega)
      rwa [show t + (t' - t + i) = t' + i by omega] at h'
    · obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp ht'
      obtain ⟨h3, h4⟩ := Finset.mem_Icc.mp hs
      have h' := h (s - t + i) (by omega)
      rwa [show t + (s - t + i) = s + i by omega] at h'

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
