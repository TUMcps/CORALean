module

public import CORALean.Specification.ReachSetAnalyzer.Definitions.FalseMark
public import CORALean.Specification.ReachSetAnalyzer.Definitions.TrueMark
public import CORALean.Specification.ReachSetAnalyzer.Operations.AnalyzeTimeInterval
public import CORALean.Specification.ReachSetAnalyzer.Theorems.AnalyzeKeySpec
public import CORALean.Specification.ReachSetAnalyzer.Theorems.RepresentsOfIff

@[expose] public section

/-!
# What one set in one time interval records

If the analyzer represents `PT` and `PF` and `lo < hi`, analyzing a set in `[lo,hi]` succeeds and
leaves the analyzer representing the same plus the times the set marks (`TrueMark`, `FalseMark`) for
the propositions it concerns. The propositions and masks are untouched.

## Inputs
* `obj` – analyzer
* `d` – signal duration
* `PT` – times where each proposition can be true
* `PF` – times where each proposition can be false
* `set` – reachable set
* `loc` – location
* `lo` – interval lower bound
* `hi` – interval upper bound

## Hypotheses
* `hobj` – the analyzer represents `PT` and `PF`
* `hlh` – the interval is proper

## Conclusion
* analysis succeeds and adds the set's marks in the interval
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

/-- The loop over the propositions of a list `l` of those of `obj`. -/
theorem aux_analyzeTimeInterval_loop (obj : ReachSetAnalyzer ℝ S n) (d : ℝ)
    (set : S n) (loc : ℕ) (lo hi : ℝ) (hlh : lo < hi) : -- --- CONCL ---
    ∀ (l : List (String × AtomicProposition S n)), (∀ q ∈ l, q ∈ obj.aps) →
    ∀ (PT PF : String → ℝ → Prop) (obj0 : ReachSetAnalyzer ℝ S n), obj0.aps = obj.aps →
      obj0.masks = obj.masks →
      obj0.Represents d PT PF → ∃ obj', l.foldlM
        (fun o p => o.analyzeKey (𝕋 := 𝕋) set loc lo hi p) obj0 = some obj' ∧
        obj'.aps = obj.aps ∧ obj'.masks = obj.masks ∧ obj'.Represents d
          (fun k t => PT k t ∨ ∃ ap, (k, ap) ∈ l ∧ obj.maskOk k lo hi = true ∧
            ap.canBeTrue (𝕋 := 𝕋) set loc = true ∧ FiniteKleeneSignalBuilder.Covers d t lo hi)
          (fun k t => PF k t ∨ ∃ ap, (k, ap) ∈ l ∧ obj.maskOk k lo hi = true ∧
            ap.canBeFalse (𝕋 := 𝕋) set loc = true ∧
              FiniteKleeneSignalBuilder.Covers d t lo hi) := by -- --- PROOF ---
  intro l
  induction l with
  | nil =>
    intro _ PT PF obj0 ha hm hr
    exact ⟨obj0, rfl, ha, hm, ReachSetAnalyzer.represents_of_iff obj0 d hr (fun k t => by simp)
      (fun k t => by simp)⟩
  | cons p l ih =>
    intro hl PT PF obj0 ha hm hr
    -- the first proposition, on the analyzer as it is
    have hmask : obj0.maskOk = obj.maskOk := by
      funext k lo hi; simp [ReachSetAnalyzer.maskOk, hm]
    obtain ⟨obj1, h1, ha1, hm1, hr1⟩ := ReachSetAnalyzer.analyzeKey_spec (𝕋 := 𝕋) obj0 d PT PF hr
      set loc lo hi hlh p (ha ▸ hl p (List.mem_cons_self))
    simp only [hmask] at hr1
    -- and the others on what it leaves
    obtain ⟨obj', h2, ha2, hm2, hr2⟩ := ih (fun q hq => hl q (List.mem_cons_of_mem _ hq)) _ _ obj1
      (ha1.trans ha) (hm1.trans hm) hr1
    refine ⟨obj', ?_, ha2, hm2, ReachSetAnalyzer.represents_of_iff obj' d hr2
      (fun k t => ?_) (fun k t => ?_)⟩
    · rw [List.foldlM_cons, h1]
      exact h2
    -- the times marked as possibly true: those of the first proposition or of the others
    · constructor
      · rintro ((h | ⟨rfl, hh⟩) | ⟨ap, hap, hh⟩)
        · exact Or.inl h
        · exact Or.inr ⟨p.2, List.mem_cons.mpr (Or.inl rfl), hh⟩
        · exact Or.inr ⟨ap, List.mem_cons_of_mem _ hap, hh⟩
      · rintro (h | ⟨ap, hap, hh⟩)
        · exact Or.inl (Or.inl h)
        · rcases List.mem_cons.mp hap with h | h
          · obtain ⟨rfl⟩ := (Prod.ext_iff.mp h).1
            obtain ⟨rfl⟩ := (Prod.ext_iff.mp h).2
            exact Or.inl (Or.inr ⟨rfl, hh⟩)
          · exact Or.inr ⟨ap, h, hh⟩
    -- the times marked as possibly false: likewise
    · constructor
      · rintro ((h | ⟨rfl, hh⟩) | ⟨ap, hap, hh⟩)
        · exact Or.inl h
        · exact Or.inr ⟨p.2, List.mem_cons.mpr (Or.inl rfl), hh⟩
        · exact Or.inr ⟨ap, List.mem_cons_of_mem _ hap, hh⟩
      · rintro (h | ⟨ap, hap, hh⟩)
        · exact Or.inl (Or.inl h)
        · rcases List.mem_cons.mp hap with h | h
          · obtain ⟨rfl⟩ := (Prod.ext_iff.mp h).1
            obtain ⟨rfl⟩ := (Prod.ext_iff.mp h).2
            exact Or.inl (Or.inr ⟨rfl, hh⟩)
          · exact Or.inr ⟨ap, h, hh⟩


-- =======================================  MAIN THEOREM  ======================================= --

theorem ReachSetAnalyzer.analyzeTimeInterval_spec (obj : ReachSetAnalyzer ℝ S n) (d : ℝ)
    (PT PF : String → ℝ → Prop) (hobj : obj.Represents d PT PF) (set : S n) (loc : ℕ)
    (lo hi : ℝ) (hlh : lo < hi) : -- --- CONCL ---
    ∃ obj', obj.analyzeTimeInterval (𝕋 := 𝕋) set loc lo hi = some obj' ∧ obj'.aps = obj.aps ∧
      obj'.masks = obj.masks ∧ obj'.Represents d
        (fun k t => PT k t ∨ obj.TrueMark (𝕋 := 𝕋) k set loc lo hi d t)
        (fun k t => PF k t ∨ obj.FalseMark (𝕋 := 𝕋) k set loc lo hi d t) := by -- --- PROOF ---
  obtain ⟨obj', h, ha, hm, hr⟩ := aux_analyzeTimeInterval_loop (𝕋 := 𝕋) obj d set loc lo hi hlh
    obj.aps (fun q hq => hq) PT PF obj rfl rfl hobj
  exact ⟨obj', h, ha, hm, hr⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
