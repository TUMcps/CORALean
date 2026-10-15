module

public import CORALean.Specification.ReachSetAnalyzer.Theorems.AnalyzeSingleSpec

@[expose] public section

/-!
# What the entries of a branch record

If the analyzer represents `PT` and `PF` and every entry named by the branch `w` (the entry
`R(j)` for `j` in `w`) has proper time intervals, analyzing the entries one after the other
succeeds and leaves the analyzer representing the same plus the times that any set of any of these
entries marks in its time interval.
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


-- =======================================  MAIN THEOREM  ======================================= --

theorem ReachSetAnalyzer.analyzeBranch_spec (obj : ReachSetAnalyzer S n) (d : ℝ)
    (R : List (ReachSetAnalyzer.Entry S n)) :
    ∀ (w : List ℕ), (∀ j ∈ w, ∃ e, R[j - 1]? = some e ∧ ∀ s ∈ e.timeInterval, s.lo < s.hi) →
    ∀ (PT PF : String → ℝ → Prop) (obj0 : ReachSetAnalyzer S n), obj0.aps = obj.aps →
      obj0.masks = obj.masks → obj0.Represents d PT PF →
      ∃ obj', w.foldlM (fun o j => (R[j - 1]?).bind fun e => o.analyzeSingle (𝕋 := 𝕋) e) obj0 =
        some obj' ∧ obj'.aps = obj.aps ∧ obj'.masks = obj.masks ∧ obj'.Represents d
          (fun k t => PT k t ∨ ∃ j ∈ w, ∃ e, R[j - 1]? = some e ∧ ∃ s ∈ e.timeInterval,
            obj.TrueMark (𝕋 := 𝕋) k s.set e.loc s.lo s.hi d t)
          (fun k t => PF k t ∨ ∃ j ∈ w, ∃ e, R[j - 1]? = some e ∧ ∃ s ∈ e.timeInterval,
            obj.FalseMark (𝕋 := 𝕋) k s.set e.loc s.lo s.hi d t) := by -- --- PROOF ---
  intro w
  induction w with
  | nil =>
    intro _ PT PF obj0 ha hm hr
    exact ⟨obj0, rfl, ha, hm, ReachSetAnalyzer.represents_of_iff obj0 d hr (fun k t => by simp)
      (fun k t => by simp)⟩
  | cons j w ih =>
    intro hw PT PF obj0 ha hm hr
    -- the first entry, on the analyzer as it is
    obtain ⟨e, he, hproper⟩ := hw j List.mem_cons_self
    obtain ⟨obj1, h1, ha1, hm1, hr1⟩ := ReachSetAnalyzer.analyzeSingle_spec (𝕋 := 𝕋) obj0 d PT PF
      hr e hproper
    rw [(ReachSetAnalyzer.marks_congr (𝕋 := 𝕋) obj obj0 ha hm).1,
      (ReachSetAnalyzer.marks_congr (𝕋 := 𝕋) obj obj0 ha hm).2] at hr1
    -- and the others on what it leaves
    obtain ⟨obj', h2, ha2, hm2, hr2⟩ := ih (fun q hq => hw q (List.mem_cons_of_mem _ hq)) _ _ obj1
      (ha1.trans ha) (hm1.trans hm) hr1
    refine ⟨obj', ?_, ha2, hm2, ReachSetAnalyzer.represents_of_iff obj' d hr2
      (fun k t => ?_) (fun k t => ?_)⟩
    · rw [List.foldlM_cons, he, Option.bind_some, h1]
      exact h2
    -- the times marked as possibly true: those of the first step or of the others
    · constructor
      · rintro ((h | ⟨s, hs, hh⟩) | ⟨q, hq, e', he', hh⟩)
        · exact Or.inl h
        · exact Or.inr ⟨j, List.mem_cons_self, e, he, s, hs, hh⟩
        · exact Or.inr ⟨q, List.mem_cons_of_mem _ hq, e', he', hh⟩
      · rintro (h | ⟨q, hq, e', he', hh⟩)
        · exact Or.inl (Or.inl h)
        · rcases List.mem_cons.mp hq with rfl | hq
          · obtain rfl : e' = e := Option.some.inj (he'.symm.trans he)
            exact Or.inl (Or.inr hh)
          · exact Or.inr ⟨q, hq, e', he', hh⟩
    -- the times marked as possibly false: likewise
    · constructor
      · rintro ((h | ⟨s, hs, hh⟩) | ⟨q, hq, e', he', hh⟩)
        · exact Or.inl h
        · exact Or.inr ⟨j, List.mem_cons_self, e, he, s, hs, hh⟩
        · exact Or.inr ⟨q, List.mem_cons_of_mem _ hq, e', he', hh⟩
      · rintro (h | ⟨q, hq, e', he', hh⟩)
        · exact Or.inl (Or.inl h)
        · rcases List.mem_cons.mp hq with rfl | hq
          · obtain rfl : e' = e := Option.some.inj (he'.symm.trans he)
            exact Or.inl (Or.inr hh)
          · exact Or.inr ⟨q, hq, e', he', hh⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
