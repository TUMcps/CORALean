module

public import CORALean.Specification.FiniteKleeneSignalBuilder.Theorems.RepresentsOfIff
public import CORALean.Specification.FiniteKleeneSignalBuilder.Theorems.SetPossiblyFalseSpec
public import CORALean.Specification.FiniteKleeneSignalBuilder.Theorems.SetPossiblyTrueSpec
public import CORALean.Specification.ReachSetAnalyzer.Definitions.Represents
public import CORALean.Specification.ReachSetAnalyzer.Operations.AnalyzeKey
public import CORALean.Global.LookupReplaceKey

@[expose] public section

/-!
# What one proposition over one set records

If the analyzer represents `PT` and `PF` and `lo < hi`, analyzing a set for a proposition `p`
succeeds and leaves the analyzer representing the same plus, for `p` only, the times of `[lo,hi)` it
covers (`Covers`) when the mask allows the proposition there (`maskOk`): possibly true if
`canBeTrue` of the set, possibly false if `canBeFalse` of the set. The propositions and masks are
untouched.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open FiniteKleeneSignalBuilder

variable {𝕋 : Type} [Scalar 𝕋] [ExactScalar 𝕋] {S : ℕ → Type} {n : ℕ}
  [∀ k, ContSet (S k) (Vec ℝ k)] [Mtimes (Mat 𝕋) S] [∀ k, Contains (S k) (S k)]
  [∀ k, IsDisjoint (S k) (S k)]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The builder after `if c, setPossiblyTrue(int)`. -/
theorem aux_stepTrue (b : FiniteKleeneSignalBuilder) (d : ℝ) (PT PF : ℝ → Prop) (lo hi : ℝ)
    (hlh : lo < hi) (hb : b.Represents d PT PF) (c : Bool) :
    ∃ b1, (if c = true then b.setPossiblyTrue? lo hi else some b) = some b1 ∧
      b1.Represents d (fun t => PT t ∨ (c = true ∧ Covers d t lo hi)) PF := by -- --- PROOF ---
  by_cases hc : c = true
  · obtain ⟨b1, h1, h2⟩ := ((FiniteKleeneSignalBuilder.setPossiblyTrue?_spec b lo hi).2
      (by exact_mod_cast hlh)) d PT PF hb
    exact ⟨b1, by rw [if_pos hc]; exact h1, FiniteKleeneSignalBuilder.represents_of_iff b1 d h2
      (fun t => by simp [hc]) (fun t => Iff.rfl)⟩
  · refine ⟨b, by rw [if_neg hc], FiniteKleeneSignalBuilder.represents_of_iff b d hb
      (fun t => ?_) (fun t => Iff.rfl)⟩
    simp [hc]

/-- The builder after `if c, setPossiblyFalse(int)`. -/
theorem aux_stepFalse (b : FiniteKleeneSignalBuilder) (d : ℝ) (PT PF : ℝ → Prop) (lo hi : ℝ)
    (hlh : lo < hi) (hb : b.Represents d PT PF) (c : Bool) :
    ∃ b1, (if c = true then b.setPossiblyFalse? lo hi else some b) = some b1 ∧
      b1.Represents d PT (fun t => PF t ∨ (c = true ∧ Covers d t lo hi)) := by -- --- PROOF ---
  by_cases hc : c = true
  · obtain ⟨b1, h1, h2⟩ := ((FiniteKleeneSignalBuilder.setPossiblyFalse?_spec b lo hi).2
      (by exact_mod_cast hlh)) d PT PF hb
    exact ⟨b1, by rw [if_pos hc]; exact h1, FiniteKleeneSignalBuilder.represents_of_iff b1 d h2
      (fun t => Iff.rfl) (fun t => by simp [hc])⟩
  · refine ⟨b, by rw [if_neg hc], FiniteKleeneSignalBuilder.represents_of_iff b d hb
      (fun t => Iff.rfl) (fun t => ?_)⟩
    simp [hc]

omit [∀ k, ContSet (S k) (Vec ℝ k)] [Mtimes (Mat 𝕋) S] [∀ k, Contains (S k) (S k)]
  [∀ k, IsDisjoint (S k) (S k)] in
/-- Replacing the builder of key `k` changes what the analyzer says of `k` only. -/
theorem aux_represents_setBuilder (obj : ReachSetAnalyzer S n) (d : ℝ) (PT PF : String → ℝ → Prop)
    (hobj : obj.Represents d PT PF) (k : String) (hk : ∃ q ∈ obj.aps, q.1 = k)
    (b' : FiniteKleeneSignalBuilder) (X Y : ℝ → Prop) (hb' : b'.Represents d X Y) : -- --- STMT ---
    ({ obj with sigBuilder := replaceKey obj.sigBuilder k b' }
      : ReachSetAnalyzer S n).Represents d (fun k' => if k' = k then X else PT k')
        (fun k' => if k' = k then Y else PF k') := by -- --- PROOF ---
  obtain ⟨hnd, hall⟩ := hobj
  refine ⟨hnd, fun q hq => ?_⟩
  obtain ⟨b, hlk, hb⟩ := hall q hq
  by_cases hqk : q.1 = k
  · -- the replaced key
    obtain ⟨q0, hq0, hq0k⟩ := hk
    obtain ⟨b0, hlk0, -⟩ := hall q0 hq0
    refine ⟨b', ?_, by simpa [hqk] using hb'⟩
    show (replaceKey obj.sigBuilder k b').lookup q.1 = some b'
    have hk0 : obj.sigBuilder.lookup k = some b0 := by rw [← hq0k]; exact hlk0
    rw [lookup_replaceKey, if_pos hqk, hk0]
    rfl
  · -- any other key
    refine ⟨b, ?_, by simpa [hqk] using hb⟩
    show (replaceKey obj.sigBuilder k b').lookup q.1 = some b
    rw [lookup_replaceKey, if_neg hqk, hlk]


-- =======================================  MAIN THEOREM  ======================================= --

theorem ReachSetAnalyzer.analyzeKey_spec (obj : ReachSetAnalyzer S n) (d : ℝ)
    (PT PF : String → ℝ → Prop) (hobj : obj.Represents d PT PF) (set : S n) (loc : ℕ)
    (lo hi : ℝ) (hlh : lo < hi) (p : String × AtomicProposition S n)
    (hp : p ∈ obj.aps) : -- --- STMT ---
    ∃ obj', obj.analyzeKey (𝕋 := 𝕋) set loc lo hi p = some obj' ∧ obj'.aps = obj.aps ∧
      obj'.masks = obj.masks ∧ obj'.Represents d
        (fun k t => PT k t ∨ (k = p.1 ∧ obj.maskOk p.1 lo hi = true ∧
          p.2.canBeTrue (𝕋 := 𝕋) set loc = true ∧ Covers d t lo hi))
        (fun k t => PF k t ∨ (k = p.1 ∧ obj.maskOk p.1 lo hi = true ∧
          p.2.canBeFalse (𝕋 := 𝕋) set loc = true ∧ Covers d t lo hi)) := by -- --- PROOF ---
  obtain ⟨b, hlk, hb⟩ := hobj.2 p hp
  unfold ReachSetAnalyzer.analyzeKey
  rw [hlk, Option.bind_some]
  by_cases hm : obj.maskOk p.1 lo hi = true
  · -- the mask lets the proposition through: both steps run
    rw [if_pos hm]
    obtain ⟨b1, h1, hb1⟩ := aux_stepTrue b d _ _ lo hi hlh hb (p.2.canBeTrue (𝕋 := 𝕋) set loc)
    obtain ⟨b2, h2, hb2⟩ := aux_stepFalse b1 d _ _ lo hi hlh hb1
      (p.2.canBeFalse (𝕋 := 𝕋) set loc)
    rw [h1, Option.bind_some, h2, Option.map_some]
    refine ⟨_, rfl, rfl, rfl, ?_⟩
    have hrep := aux_represents_setBuilder obj d PT PF hobj p.1 ⟨p, hp, rfl⟩ b2 _ _ hb2
    refine ⟨hrep.1, fun q hq => ?_⟩
    obtain ⟨c, hc, hcr⟩ := hrep.2 q hq
    refine ⟨c, hc, FiniteKleeneSignalBuilder.represents_of_iff c d hcr (fun t => ?_) (fun t => ?_)⟩
    · by_cases hqk : q.1 = p.1 <;> simp [hqk, hm]
    · by_cases hqk : q.1 = p.1 <;> simp [hqk, hm]
  · -- the mask rules the proposition out: nothing changes
    rw [if_neg hm]
    refine ⟨obj, rfl, rfl, rfl, hobj.1, fun q hq => ?_⟩
    obtain ⟨c, hc, hcr⟩ := hobj.2 q hq
    refine ⟨c, hc, FiniteKleeneSignalBuilder.represents_of_iff c d hcr (fun t => ?_) (fun t => ?_)⟩
    · simp [hm]
    · simp [hm]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
