module

public import CORALean.Specification.PointSegmentSignal.Definitions.IsUnitary
public import CORALean.Specification.PointSegmentSignal.Theorems.IntervalUntilSpec
public import CORALean.Specification.STLInterval.Theorems.SetOrdConnected
public import CORALean.Specification.STLInterval.Theorems.InfimumValue
public import CORALean.Specification.STLInterval.Theorems.SupremumValue
public import CORALean.Specification.STLInterval.Theorems.SetLeftClosure
public import CORALean.Specification.STLInterval.Theorems.SetRightClosure
public import CORALean.Specification.STLInterval.Theorems.ZeroLeOfMemSet

@[expose] public section

/-!
# The unitary until is the until

For unitary Boolean signals `λ₁`, `λ₂` (with `I⁺` the intervals `J₁`, `J₂`) and an interval `U` over
`ℝ≥0`, the unitary until of [1, Eq. 1] (`intervalUntil` of the one-element lists `[J₁]`, `[J₂]`,
`PointSegmentSignal.intervalUntil_spec`) is valid and, at every `t ≥ 0`, `true` iff
`∃t' ∈ t ⊕ U: λ₂(t') = ⊤` and `∀t'' ∈ (t,t'): λ₁(t'') = ⊤`, and `false` otherwise: [1, Lemma 1]. Its
proof is the paper's: `t ∈ cll(I⁺_{λ₁})` and `t' ∈ clr(I⁺_{λ₁})` for `t < t'` iff the open interval
`(t,t')` lies in the contiguous `I⁺_{λ₁}`.

## References

* [1] F. Lercher and M. Althoff. "Using Four-Valued Signal Temporal Logic for Incremental
      Verification of Hybrid Systems". CAV, LNCS 14683, pp. 259-281, 2024.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A point `t < x` of the left closure has a time of `J` below `x`. -/
theorem PointSegmentSignal.aux_exists_lt (J : STLInterval) (t x : ℝ) (ht : t ∈ J.leftClosure.set)
    (htx : t < x) : ∃ s ∈ J.set, s < x := by -- --- PROOF ---
  rw [STLInterval.set_leftClosure] at ht
  rcases ht with ht | ht
  · exact ⟨t, ht, htx⟩
  -- `t` is the infimum of the times of `J`, which is nonempty, and `t < x`
  · have hJ : J ≠ .empty := by
      rintro rfl
      simp [STLInterval.infimum] at ht
    rw [STLInterval.infimum_value J hJ] at ht
    have h := Option.some.inj ht
    have hlt : (⨅ s ∈ J.set, (s : EReal)) < (x : EReal) := by
      rw [h]; exact_mod_cast htx
    rw [iInf_lt_iff] at hlt
    obtain ⟨s, hs⟩ := hlt
    rw [iInf_lt_iff] at hs
    obtain ⟨hsJ, hsx⟩ := hs
    exact ⟨s, hsJ, by exact_mod_cast hsx⟩

/-- A point `t > x` of the right closure has a time of `J` above `x`. -/
theorem PointSegmentSignal.aux_exists_gt (J : STLInterval) (t x : ℝ) (ht : t ∈ J.rightClosure.set)
    (hxt : x < t) : ∃ s ∈ J.set, x < s := by -- --- PROOF ---
  rw [STLInterval.set_rightClosure] at ht
  rcases ht with ht | ht
  · exact ⟨t, ht, hxt⟩
  -- `t` is the supremum of the times of `J`, which is nonempty, and `x < t`
  · have hJ : J ≠ .empty := by
      rintro rfl
      simp [STLInterval.supremum] at ht
    rw [STLInterval.supremum_value J hJ] at ht
    have h := Option.some.inj ht
    have hlt : (x : EReal) < (⨆ s ∈ J.set, (s : EReal)) := by
      rw [h]; exact_mod_cast hxt
    rw [lt_iSup_iff] at hlt
    obtain ⟨s, hs⟩ := hlt
    rw [lt_iSup_iff] at hs
    obtain ⟨hsJ, hsx⟩ := hs
    exact ⟨s, hsJ, by exact_mod_cast hsx⟩

/-- If `J` contains everything strictly between `t < t'`, `t` is in its left closure. -/
theorem PointSegmentSignal.aux_mem_leftClosure (J : STLInterval) (t t' : ℝ) (htt : t < t')
    (h : ∀ x, t < x → x < t' → x ∈ J.set) : t ∈ J.leftClosure.set := by -- --- PROOF ---
  rw [STLInterval.set_leftClosure]
  by_cases htJ : t ∈ J.set
  · exact Or.inl htJ
  right
  -- otherwise `t` is the infimum: the midpoint is in `J`, so `J` is nonempty
  have hm : (t + t') / 2 ∈ J.set := h _ (by linarith) (by linarith)
  have hJ : J ≠ .empty := by
    rintro rfl
    simp [STLInterval.set_empty] at hm
  show J.infimum.value = some (t : EReal)
  rw [STLInterval.infimum_value J hJ]
  congr 1
  apply le_antisymm
  · -- the infimum is at most `t`
    by_contra hgt
    rw [not_le] at hgt
    obtain ⟨r, hr1, hr2⟩ := EReal.lt_iff_exists_real_btwn.1 hgt
    have hr1' : t < r := by exact_mod_cast hr1
    have hx : min r ((t + t') / 2) ∈ J.set :=
      h _ (lt_min hr1' (by linarith)) (lt_of_le_of_lt (min_le_right _ _) (by linarith))
    have := iInf₂_le (f := fun (s : ℝ) (_ : s ∈ J.set) => (s : EReal)) _ hx
    have h2 : ((min r ((t + t') / 2) : ℝ) : EReal) ≤ (r : EReal) := by
      exact_mod_cast min_le_left _ _
    exact absurd (lt_of_le_of_lt (this.trans h2) hr2) (lt_irrefl _)
  · -- and at least `t`: a time of `J` below `t` would put `t` in `J`
    by_contra hlt
    rw [not_le] at hlt
    rw [iInf_lt_iff] at hlt
    obtain ⟨s, hs⟩ := hlt
    rw [iInf_lt_iff] at hs
    obtain ⟨hsJ, hst⟩ := hs
    have hst' : s < t := by exact_mod_cast hst
    exact htJ ((STLInterval.set_ordConnected J).out hsJ hm ⟨hst'.le, by linarith⟩)

/-- If `J` contains everything strictly between `t < t'`, `t'` is in its right closure. -/
theorem PointSegmentSignal.aux_mem_rightClosure (J : STLInterval) (t t' : ℝ) (htt : t < t')
    (h : ∀ x, t < x → x < t' → x ∈ J.set) : t' ∈ J.rightClosure.set := by -- --- PROOF ---
  rw [STLInterval.set_rightClosure]
  by_cases htJ : t' ∈ J.set
  · exact Or.inl htJ
  right
  -- otherwise `t'` is the supremum: the midpoint is in `J`, so `J` is nonempty
  have hm : (t + t') / 2 ∈ J.set := h _ (by linarith) (by linarith)
  have hJ : J ≠ .empty := by
    rintro rfl
    simp [STLInterval.set_empty] at hm
  show J.supremum.value = some (t' : EReal)
  rw [STLInterval.supremum_value J hJ]
  congr 1
  -- the supremum is `t'`: at least `t'`, else a time of `J` above `t'` would put `t'` in `J`
  apply le_antisymm
  · by_contra hgt
    rw [not_le] at hgt
    rw [lt_iSup_iff] at hgt
    obtain ⟨s, hs⟩ := hgt
    rw [lt_iSup_iff] at hs
    obtain ⟨hsJ, hst⟩ := hs
    have hst' : t' < s := by exact_mod_cast hst
    exact htJ ((STLInterval.set_ordConnected J).out hm hsJ ⟨by linarith, hst'.le⟩)
  · by_contra hlt
    rw [not_le] at hlt
    obtain ⟨r, hr1, hr2⟩ := EReal.lt_iff_exists_real_btwn.1 hlt
    have hr2' : r < t' := by exact_mod_cast hr2
    have hx : max r ((t + t') / 2) ∈ J.set :=
      h _ (lt_of_lt_of_le (by linarith) (le_max_right _ _)) (max_lt hr2' (by linarith))
    have := le_iSup₂ (f := fun (s : ℝ) (_ : s ∈ J.set) => (s : EReal)) _ hx
    have h2 : (r : EReal) ≤ ((max r ((t + t') / 2) : ℝ) : EReal) := by
      exact_mod_cast le_max_left _ _
    exact absurd (lt_of_lt_of_le hr1 (h2.trans this)) (lt_irrefl _)


-- =======================================  MAIN THEOREM  ======================================= --

/-- The unitary until of `Eq. 1` is `true` exactly where the until semantics says. -/
theorem PointSegmentSignal.intervalUntil_unitary (l₁ l₂ : PointSegmentSignal ℝ)
    (J₁ J₂ U : STLInterval) (h₁ : l₁.IsUnitary J₁) (h₂ : l₂.IsUnitary J₂) :
    (PointSegmentSignal.intervalUntil [J₁] U [J₂]).IsValid ∧ ∀ t : ℝ, 0 ≤ t →
      ((PointSegmentSignal.intervalUntil [J₁] U [J₂]).at t = true ↔
        ∃ t', t' - t ∈ U.set ∧ l₂.at t' = true ∧
          ∀ x, t < x → x < t' → l₁.at x = true) := by -- --- PROOF ---
  obtain ⟨hv, h⟩ := PointSegmentSignal.intervalUntil_spec [J₁] [J₂] U
  refine ⟨hv, fun t ht => ?_⟩
  rw [h t ht]
  simp only [List.mem_singleton, exists_eq_left]
  constructor
  -- a witness `t'` of the pair of intervals, or `t` itself in `I⁺_{λ₂}`
  · rintro (⟨t', ht'J, ht'cl, htcl, hu, hne⟩ | ⟨h0, htJ⟩)
    · have hd := STLInterval.zero_le_of_mem_set U _ hu
      have htt : t < t' := lt_of_le_of_ne (by linarith) (Ne.symm hne)
      refine ⟨t', hu, (h₂ t' (by linarith)).2 ht'J, fun x hx1 hx2 => ?_⟩
      obtain ⟨s, hs, hsx⟩ := PointSegmentSignal.aux_exists_lt J₁ t x htcl hx1
      obtain ⟨s', hs', hxs⟩ := PointSegmentSignal.aux_exists_gt J₁ t' x ht'cl hx2
      exact (h₁ x (by linarith)).2
        ((STLInterval.set_ordConnected J₁).out hs hs' ⟨hsx.le, hxs.le⟩)
    · exact ⟨t, by simpa using h0, (h₂ t ht).2 htJ, fun x hx1 hx2 => absurd hx2 (by linarith)⟩
  -- conversely, `t' = t` is the second case, and `t < t'` puts `(t,t')` into `I⁺_{λ₁}`
  · rintro ⟨t', hu, h2, h1⟩
    have hd := STLInterval.zero_le_of_mem_set U _ hu
    have ht'0 : 0 ≤ t' := by linarith
    have ht'J : t' ∈ J₂.set := (h₂ t' ht'0).1 h2
    rcases eq_or_lt_of_le (show t ≤ t' by linarith) with heq | htt
    · subst heq
      exact Or.inr ⟨by simpa using hu, ht'J⟩
    · have hJ : ∀ x, t < x → x < t' → x ∈ J₁.set := fun x hx1 hx2 =>
        (h₁ x (by linarith)).1 (h1 x hx1 hx2)
      exact Or.inl ⟨t', ht'J, PointSegmentSignal.aux_mem_rightClosure J₁ t t' htt hJ,
        PointSegmentSignal.aux_mem_leftClosure J₁ t t' htt hJ, hu, ne_of_gt htt⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
