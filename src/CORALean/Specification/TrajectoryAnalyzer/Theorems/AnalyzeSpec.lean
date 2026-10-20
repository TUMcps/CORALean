module

public import CORALean.Global.LookupMapConst
public import CORALean.Specification.FiniteSignal.Theorems.MkSingletonSpec
public import CORALean.Specification.TrajectoryAnalyzer.Operations.Analyze
public import CORALean.Specification.TrajectoryAnalyzer.Theorems.AnalyzeIntervalSpec

@[expose] public section

/-!
# What `analyze` computes

For a simulation with strictly increasing nonnegative time points and distinct propositions,
`analyze(obj,s)` succeeds and gives, for every proposition, a valid Boolean signal of duration
`dur = t(:,end)` that is true at the time `τ` of `[0,dur]` exactly when some time point `l` of the
realization marks the proposition true at `τ` (`TrueAt`): it holds at the point `x(:,l,s)` and
`τ` lies in `[t(l),t(l+1))` (closed at `dur`). Combined with `evaluatePoint_sound`: a signal that
is true at `τ` means the proposition is satisfied by the sampled point of the interval around `τ`.

## Inputs
* `obj` – analyzer
* `s` – realization index

## Hypotheses
* `hnd` – the proposition keys are distinct
* `ht` – there are time points
* `hsorted` – the time points strictly increase
* `hnn` – the time points are nonnegative

## Conclusion
* the analysis succeeds and the signals represent the marked times
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

/-- The loop over the time points `ls`, all with proper intervals. -/
theorem aux_analyze_loop (obj : TrajectoryAnalyzer 𝕋 S n) (s : ℕ) (dur : ℝ) : -- --- CONCL ---
    ∀ ls : List ℕ, (∀ l ∈ ls, obj.traj.t.getD (l - 1) 0 < obj.traj.t.getD l 0) →
    ∀ (sigs : List (String × FiniteSignal ℝ Bool)) (M : String → ℝ → Prop),
      TrajectoryAnalyzer.SignalsRepresent obj.aps dur sigs M → ∃ sigs',
        ls.foldlM (fun sigs l => obj.analyzeInterval s dur sigs l) sigs = some sigs' ∧
        TrajectoryAnalyzer.SignalsRepresent obj.aps dur sigs'
          (fun k τ => M k τ ∨ ∃ l ∈ ls, obj.TrueAt s dur k l τ) := by -- --- PROOF ---
  intro ls
  induction ls with
  | nil =>
    intro _ sigs M h
    exact ⟨sigs, rfl, TrajectoryAnalyzer.signalsRepresent_of_iff _ dur sigs h (fun k τ => by simp)⟩
  | cons l ls ih =>
    intro hls sigs M h
    -- the first time point, then the others on what it leaves
    obtain ⟨sigs1, h1, hr1⟩ := TrajectoryAnalyzer.analyzeInterval_spec obj s dur sigs M h l
      (hls l List.mem_cons_self)
    obtain ⟨sigs', h2, hr2⟩ := ih (fun q hq => hls q (List.mem_cons_of_mem _ hq)) sigs1 _ hr1
    refine ⟨sigs', ?_, TrajectoryAnalyzer.signalsRepresent_of_iff _ dur sigs' hr2
      (fun k τ => ?_)⟩
    · rw [List.foldlM_cons, h1]
      exact h2
    · constructor
      · rintro ((h | h) | ⟨q, hq, hh⟩)
        · exact Or.inl h
        · exact Or.inr ⟨l, List.mem_cons_self, h⟩
        · exact Or.inr ⟨q, List.mem_cons_of_mem _ hq, hh⟩
      · rintro (h | ⟨q, hq, hh⟩)
        · exact Or.inl (Or.inl h)
        · rcases List.mem_cons.mp hq with rfl | hq
          · exact Or.inl (Or.inr hh)
          · exact Or.inr ⟨q, hq, hh⟩


-- =======================================  MAIN THEOREM  ======================================= --

theorem TrajectoryAnalyzer.analyze_spec (obj : TrajectoryAnalyzer 𝕋 S n) (s : ℕ)
    (hnd : (obj.aps.map Prod.fst).Nodup) (ht : obj.traj.t ≠ [])
    (hsorted : obj.traj.t.Pairwise (· < ·)) (hnn : ∀ x ∈ obj.traj.t, 0 ≤ x) : -- --- CONCL ---
    ∃ dur sigs, obj.traj.t.getLast? = some dur ∧ obj.analyze s = some sigs ∧
      TrajectoryAnalyzer.SignalsRepresent obj.aps dur sigs (fun k τ =>
        ∃ l ∈ List.range' 1 (obj.traj.t.length - 1), obj.TrueAt s dur k l τ) := by -- --- PROOF ---
  -- the duration, the last time
  obtain ⟨dur, hdur⟩ : ∃ dur, obj.traj.t.getLast? = some dur :=
    ⟨_, List.getLast?_eq_getLast_of_ne_nil ht⟩
  have hd0 : 0 ≤ dur := hnn dur (List.mem_of_getLast? hdur)
  -- the signals made false
  obtain ⟨sig0, hsig0, hv0, hdur0, hat0⟩ := (FiniteSignal.mk?_singleton_spec dur false).2 hd0
  have hinit : TrajectoryAnalyzer.SignalsRepresent obj.aps dur (obj.aps.map fun p => (p.1, sig0))
      (fun _ _ => False) := by
    refine ⟨hnd, by simp, fun p hp => ⟨sig0, lookup_map_const obj.aps sig0 p hp, hv0, hdur0,
      fun τ h0 h1 => ⟨false, hat0 τ h0 h1, by simp⟩⟩⟩
  -- every interval is proper: the time points increase
  have hproper : ∀ l ∈ List.range' 1 (obj.traj.t.length - 1),
      obj.traj.t.getD (l - 1) 0 < obj.traj.t.getD l 0 := by
    intro l hl
    rw [List.mem_range'_1] at hl
    have h1 : l - 1 < obj.traj.t.length := by omega
    have h2 : l < obj.traj.t.length := by omega
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1,
      List.getElem?_eq_getElem h2]
    exact List.pairwise_iff_getElem.mp hsorted (l - 1) l h1 h2 (by omega)
  -- run the loop over the time points, then read the result off the definition
  obtain ⟨sigs, hloop, hr⟩ := aux_analyze_loop obj s dur _ hproper _ _ hinit
  refine ⟨dur, sigs, hdur, ?_, TrajectoryAnalyzer.signalsRepresent_of_iff _ dur sigs hr
    (fun k τ => by simp)⟩
  have hall : ∀ l : List (String × AtomicProposition S n),
      (l.mapM fun p => (FiniteSignal.mk? [dur] [false]).map fun sig => (p.1, sig)) =
        some (l.map fun p => (p.1, sig0)) := by
    intro l
    simp only [hsig0, Option.map_some]
    induction l with
    | nil => rfl
    | cons p ps ih => simp [List.mapM_cons, ih]
  simp only [TrajectoryAnalyzer.analyze, hdur, Option.bind_some, hall]
  exact hloop

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
