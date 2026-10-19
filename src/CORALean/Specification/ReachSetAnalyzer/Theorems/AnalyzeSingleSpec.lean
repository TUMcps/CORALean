module

public import CORALean.Specification.ReachSetAnalyzer.Operations.AnalyzeSingle
public import CORALean.Specification.ReachSetAnalyzer.Theorems.AnalyzeTimeIntervalSpec
public import CORALean.Specification.ReachSetAnalyzer.Theorems.TrueMarkCongr

@[expose] public section

/-!
# What one reach set records

If the analyzer represents `PT` and `PF` and every time interval of the entry `R` is proper
(`lo < hi`), `analyzeSingle` succeeds and leaves the analyzer representing the same plus the times
that any set of `R`, at the location of `R`, marks in its time interval.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {𝕋 : Type} [Scalar 𝕋] [ExactScalar 𝕋] {S : ℕ → Type} {n : ℕ}
  [∀ k, ContSet (S k) (Vec ℝ k)] [Mtimes (Mat 𝕋) S] [∀ k, Contains (S k) (S k)]
  [∀ k, IsDisjoint (S k) (S k)]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The loop over the time intervals `l` of the entry. -/
theorem aux_analyzeSingle_loop (obj : ReachSetAnalyzer S n) (d : ℝ) (loc : ℕ) : -- --- CONCL ---
    ∀ l : List (ReachSetAnalyzer.TimedSet S n), (∀ s ∈ l, s.time.inf < s.time.sup) →
    ∀ (PT PF : String → ℝ → Prop) (obj0 : ReachSetAnalyzer S n), obj0.aps = obj.aps →
      obj0.masks = obj.masks → obj0.Represents d PT PF → ∃ obj', l.foldlM
        (fun o t => o.analyzeTimeInterval (𝕋 := 𝕋) t.set loc t.time.inf t.time.sup) obj0 =
          some obj' ∧
        obj'.aps = obj.aps ∧ obj'.masks = obj.masks ∧ obj'.Represents d
          (fun k t => PT k t ∨ ∃ s ∈ l, obj.TrueMark (𝕋 := 𝕋) k s.set loc s.time.inf s.time.sup d t)
          (fun k t => PF k t ∨ ∃ s ∈ l,
            obj.FalseMark (𝕋 := 𝕋) k s.set loc s.time.inf s.time.sup d t) := by -- --- PROOF ---
  intro l
  induction l with
  | nil =>
    intro _ PT PF obj0 ha hm hr
    exact ⟨obj0, rfl, ha, hm, ReachSetAnalyzer.represents_of_iff obj0 d hr (fun k t => by simp)
      (fun k t => by simp)⟩
  | cons s l ih =>
    intro hl PT PF obj0 ha hm hr
    -- the first time interval, on the analyzer as it is
    obtain ⟨obj1, h1, ha1, hm1, hr1⟩ := ReachSetAnalyzer.analyzeTimeInterval_spec (𝕋 := 𝕋) obj0 d
      PT PF hr s.set loc s.time.inf s.time.sup (hl s List.mem_cons_self)
    rw [(ReachSetAnalyzer.marks_congr (𝕋 := 𝕋) obj obj0 ha hm).1,
      (ReachSetAnalyzer.marks_congr (𝕋 := 𝕋) obj obj0 ha hm).2] at hr1
    -- and the others on what it leaves
    obtain ⟨obj', h2, ha2, hm2, hr2⟩ := ih (fun q hq => hl q (List.mem_cons_of_mem _ hq)) _ _ obj1
      (ha1.trans ha) (hm1.trans hm) hr1
    refine ⟨obj', ?_, ha2, hm2, ReachSetAnalyzer.represents_of_iff obj' d hr2
      (fun k t => ?_) (fun k t => ?_)⟩
    · rw [List.foldlM_cons, h1]
      exact h2
    -- the times marked as possibly true: those of the first step or of the others
    · constructor
      · rintro ((h | h) | ⟨q, hq, hh⟩)
        · exact Or.inl h
        · exact Or.inr ⟨s, List.mem_cons_self, h⟩
        · exact Or.inr ⟨q, List.mem_cons_of_mem _ hq, hh⟩
      · rintro (h | ⟨q, hq, hh⟩)
        · exact Or.inl (Or.inl h)
        · rcases List.mem_cons.mp hq with rfl | h
          · exact Or.inl (Or.inr hh)
          · exact Or.inr ⟨q, h, hh⟩
    -- the times marked as possibly false: likewise
    · constructor
      · rintro ((h | h) | ⟨q, hq, hh⟩)
        · exact Or.inl h
        · exact Or.inr ⟨s, List.mem_cons_self, h⟩
        · exact Or.inr ⟨q, List.mem_cons_of_mem _ hq, hh⟩
      · rintro (h | ⟨q, hq, hh⟩)
        · exact Or.inl (Or.inl h)
        · rcases List.mem_cons.mp hq with rfl | h
          · exact Or.inl (Or.inr hh)
          · exact Or.inr ⟨q, h, hh⟩


-- =======================================  MAIN THEOREM  ======================================= --

theorem ReachSetAnalyzer.analyzeSingle_spec (obj : ReachSetAnalyzer S n) (d : ℝ)
    (PT PF : String → ℝ → Prop) (hobj : obj.Represents d PT PF)
    (R : ReachSetAnalyzer.Entry S n)
    (hR : ∀ s ∈ R.timeInterval, s.time.inf < s.time.sup) : -- --- CONCL ---
    ∃ obj', obj.analyzeSingle (𝕋 := 𝕋) R = some obj' ∧ obj'.aps = obj.aps ∧
      obj'.masks = obj.masks ∧ obj'.Represents d
        (fun k t => PT k t ∨ ∃ s ∈ R.timeInterval,
          obj.TrueMark (𝕋 := 𝕋) k s.set R.loc s.time.inf s.time.sup d t)
        (fun k t => PF k t ∨ ∃ s ∈ R.timeInterval,
          obj.FalseMark (𝕋 := 𝕋) k s.set R.loc s.time.inf s.time.sup d t) :=
  aux_analyzeSingle_loop (𝕋 := 𝕋) obj d R.loc R.timeInterval hR PT PF obj rfl rfl hobj

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
