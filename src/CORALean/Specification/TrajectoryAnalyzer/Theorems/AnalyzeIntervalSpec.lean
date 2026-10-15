module

public import CORALean.Specification.TrajectoryAnalyzer.Definitions.TrueAt
public import CORALean.Specification.TrajectoryAnalyzer.Operations.AnalyzeInterval
public import CORALean.Specification.TrajectoryAnalyzer.Theorems.MarkKeySpec
public import CORALean.Specification.TrajectoryAnalyzer.Theorems.SignalsRepresentOfIff

@[expose] public section

/-!
# What one interval of the simulation marks

If the signals represent `M` and the interval `[t(l),t(l+1))` is proper, `analyzeInterval`
succeeds and the signals then represent `M` plus the times that the time point `l` marks true
(`TrueAt`) for the propositions that hold at its point.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {𝕋 : Type} [Scalar 𝕋] {S : ℕ → Type} {n : ℕ} [∀ k, ContSet (S k) (Vec ℝ k)]
  [OfScalarPoint 𝕋 S] [∀ k, Contains (S k) (S k)]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The loop over the propositions `L` of the analyzer, for a point, location and interval. -/
theorem aux_analyzeInterval_loop (aps : List (String × AtomicProposition S n)) (dur : ℝ)
    (point : Vec 𝕋 n) (loc : ℕ) (lo hi : ℝ) (hlh : lo < hi) :
    ∀ L : List (String × AtomicProposition S n), (∀ q ∈ L, q ∈ aps) →
    ∀ (sigs : List (String × FiniteSignal ℝ Bool)) (M : String → ℝ → Prop),
      TrajectoryAnalyzer.SignalsRepresent aps dur sigs M → ∃ sigs', L.foldlM (fun sigs p =>
        if p.2.evaluatePoint point loc = true then TrajectoryAnalyzer.markKey dur lo hi sigs p.1
        else some sigs) sigs = some sigs' ∧ TrajectoryAnalyzer.SignalsRepresent aps dur sigs'
          (fun k τ => M k τ ∨ ∃ ap, (k, ap) ∈ L ∧ ap.evaluatePoint point loc = true ∧
            FiniteKleeneSignalBuilder.Covers dur τ lo hi) := by -- --- PROOF ---
  intro L
  induction L with
  | nil =>
    intro _ sigs M h
    exact ⟨sigs, rfl,
      TrajectoryAnalyzer.signalsRepresent_of_iff aps dur sigs h (fun k τ => by simp)⟩
  | cons p L ih =>
    intro hL sigs M h
    -- the first proposition marks its signal only if it holds at the point
    have hstep : ∃ sigs1, (if p.2.evaluatePoint point loc = true then
        TrajectoryAnalyzer.markKey dur lo hi sigs p.1 else some sigs) = some sigs1 ∧
        TrajectoryAnalyzer.SignalsRepresent aps dur sigs1 (fun k τ => M k τ ∨
          (k = p.1 ∧ p.2.evaluatePoint point loc = true ∧
            FiniteKleeneSignalBuilder.Covers dur τ lo hi)) := by
      by_cases he : p.2.evaluatePoint point loc = true
      · obtain ⟨sigs1, h1, h2⟩ := TrajectoryAnalyzer.markKey_spec aps dur sigs M h lo hi hlh p
          (hL p List.mem_cons_self)
        exact ⟨sigs1, by rw [if_pos he]; exact h1,
          TrajectoryAnalyzer.signalsRepresent_of_iff aps dur sigs1 h2 (fun k τ => by simp [he])⟩
      · exact ⟨sigs, by rw [if_neg he],
          TrajectoryAnalyzer.signalsRepresent_of_iff aps dur sigs h (fun k τ => by simp [he])⟩
    obtain ⟨sigs1, h1, hr1⟩ := hstep
    -- and the others on what it leaves
    obtain ⟨sigs', h2, hr2⟩ := ih (fun q hq => hL q (List.mem_cons_of_mem _ hq)) sigs1 _ hr1
    refine ⟨sigs', ?_, TrajectoryAnalyzer.signalsRepresent_of_iff aps dur sigs' hr2
      (fun k τ => ?_)⟩
    · rw [List.foldlM_cons, h1]
      exact h2
    · constructor
      · rintro ((h | ⟨rfl, he, hc⟩) | ⟨ap, hap, hh⟩)
        · exact Or.inl h
        · exact Or.inr ⟨p.2, List.mem_cons_self, he, hc⟩
        · exact Or.inr ⟨ap, List.mem_cons_of_mem _ hap, hh⟩
      · rintro (h | ⟨ap, hap, hh⟩)
        · exact Or.inl (Or.inl h)
        · rcases List.mem_cons.mp hap with rfl | hap
          · exact Or.inl (Or.inr ⟨rfl, hh⟩)
          · exact Or.inr ⟨ap, hap, hh⟩


-- =======================================  MAIN THEOREM  ======================================= --

theorem TrajectoryAnalyzer.analyzeInterval_spec (obj : TrajectoryAnalyzer 𝕋 S n) (s : ℕ)
    (dur : ℝ) (sigs : List (String × FiniteSignal ℝ Bool)) (M : String → ℝ → Prop)
    (h : TrajectoryAnalyzer.SignalsRepresent obj.aps dur sigs M) (l : ℕ)
    (hlh : obj.traj.t.getD (l - 1) 0 < obj.traj.t.getD l 0) :
    ∃ sigs', obj.analyzeInterval s dur sigs l = some sigs' ∧
      TrajectoryAnalyzer.SignalsRepresent obj.aps dur sigs'
        (fun k τ => M k τ ∨ obj.TrueAt s dur k l τ) := by -- --- PROOF ---
  obtain ⟨sigs', h1, h2⟩ := aux_analyzeInterval_loop obj.aps dur (obj.traj.x l s)
    (if obj.traj.loc ≠ [] then obj.traj.loc.getD (l - 1) 0 else 1) _ _ hlh obj.aps
    (fun q hq => hq) sigs M h
  exact ⟨sigs', h1, h2⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
