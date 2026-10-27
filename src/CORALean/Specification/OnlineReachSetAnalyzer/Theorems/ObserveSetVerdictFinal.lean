module

public import CORALean.Specification.OnlineReachSetAnalyzer.Operations.GetVerdict
public import CORALean.Specification.OnlineReachSetAnalyzer.Theorems.ObserveSetCorrect

@[expose] public section

/-!
# A conclusive verdict of the analyzer is never revised

Under the hypotheses of `observeSet_correct`, a `True` or `False` verdict after the observations
`obs` stays after any further observations `obs'`: the four-valued semantics on more observations
refines the semantics on fewer, and the root signal is that semantics [1, Alg. 1].

## Inputs
* `φ` – formula
* `dp` – whether to propagate down
* `obs` – first observations
* `obs'` – later observations

## Hypotheses
* `hlabel` – a label names one atom in `φ`
* `hne` – at least one first observation
* `hI` – every observation interval is nonempty
* `hdisj` – the observation intervals are pairwise disjoint

## Conclusion
* for the analyzer of `φ` that propagates after every observation, the exact run on `obs` from it
  and the exact run on `obs'` after that, a conclusive verdict after `obs` is the verdict after
  `obs'`

## References

* [1] F. Lercher and M. Althoff. "Using Four-Valued Signal Temporal Logic for Incremental
      Verification of Hybrid Systems". Computer Aided Verification, 2024.
-/

-- Authors:       Claude Opus 5.5
-- Written:       27-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


variable {𝕋 : Type} [Scalar 𝕋] [ExactScalar 𝕋] {S : ℕ → Type} {d : ℕ}
  [∀ k, ContSet (S k) (Vec ℝ k)] [Mtimes (Mat 𝕋) S] [∀ k, Contains (S k) (S k)]
  [∀ k, IsDisjoint (S k) (S k)]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Observations on intervals disjoint from each other and from what `sig` knows refine `sig`. -/
private theorem aux_observeAtoms_refines (obs : List (S d × STLInterval ℝ × ℕ)) : -- --- CONCL ---
    obs.Pairwise (fun o o' => Disjoint o.2.1.set o'.2.1.set) → ∀
        (sig : AtomicProposition S d → FourValuedSignal ℝ), (∀ a, (sig a).IsValid) →
      (∀ a (t : ℝ), 0 ≤ t → (sig a).at t ≠ .ii → ∀ o ∈ obs, t ∉ o.2.1.set) →
      ∀ a, (OnlineReachSetAnalyzer.observeAtoms (𝕋 := 𝕋) sig obs a).Refines (sig a)
    := by -- --- PROOF ---
  induction obs with
  | nil => intro _ sig _ _ a; exact FourValuedSignal.Refines.refl _
  | cons o obs ih =>
    intro hpw sig hv hfresh a
    have hpw' := List.pairwise_cons.1 hpw
    have hv1 : ∀ a, (OnlineReachSetAnalyzer.observeAtoms (𝕋 := 𝕋) sig [o] a).IsValid := by
      intro a; simp only [OnlineReachSetAnalyzer.observeAtoms, List.foldl_cons, List.foldl_nil]
      split
      · exact (FourValuedSignal.set_spec _ (hv a) _ _).1
      · exact hv a
    -- the first observation writes only times no earlier value knows
    have h1 : ∀ a, (OnlineReachSetAnalyzer.observeAtoms (𝕋 := 𝕋) sig [o] a).Refines (sig a) := by
      intro a t ht hne
      simp only [OnlineReachSetAnalyzer.observeAtoms, List.foldl_cons, List.foldl_nil]
      split
      · rw [((FourValuedSignal.set_spec _ (hv a) _ _).2 t ht).2
          (hfresh a t ht hne o (by simp))]
      · rfl
    refine (ih hpw'.2 _ hv1 (fun a t ht hne o' ho' hmem => ?_) a).trans (h1 a)
    rcases (OnlineReachSetAnalyzer.observeAtoms_spec (𝕋 := 𝕋) [o] sig hv).2 a t ht hne with h |
        ⟨o'', ho'', ht''⟩
    · exact hfresh a t ht h o' (by simp [ho']) hmem
    · simp only [List.mem_singleton] at ho''; subst ho''
      exact Set.disjoint_left.1 (hpw'.1 o' ho') ht'' hmem


-- =======================================  MAIN THEOREM  ======================================= --

theorem OnlineReachSetAnalyzer.observeSet_verdict_final
    (φ : OnlineReachSetAnalyzer.Formula ℝ (AtomicProposition S d))
    (hlabel : ∀ l x y, (OnlineReachSetAnalyzer.Formula.ap l x).IsSub φ →
      (OnlineReachSetAnalyzer.Formula.ap l y).IsSub φ → x = y)
    (dp : Bool) (obs obs' : List (S d × STLInterval ℝ × ℕ)) (hne : obs ≠ [])
    (hI : ∀ o ∈ obs ++ obs', o.2.1 ≠ .empty)
    (hdisj : (obs ++ obs').Pairwise fun o o' => Disjoint o.2.1.set o'.2.1.set) : -- --- CONCL ---
    ∀ obj₀ ∈ OnlineReachSetAnalyzer.mk? φ 1 dp,
      ∀ obj ∈ obs.foldlM (fun o x => o.observeSet (𝕋 := 𝕋) 0 x.1 x.2.1 x.2.2) obj₀,
      ∀ obj' ∈ obs'.foldlM (fun o x => o.observeSet (𝕋 := 𝕋) 0 x.1 x.2.1 x.2.2) obj,
      ∀ v ∈ obj.getVerdict, v ≠ .ii → obj'.getVerdict = some v := by -- --- PROOF ---
  intro obj₀ h₀ obj hrun obj' hrun' v hv hconc
  -- the root signals after `obs` and after `obs ++ obs'` are the semantics
  obtain ⟨s, hs, root, hr, hroot⟩ := OnlineReachSetAnalyzer.observeSet_correct (𝕋 := 𝕋) φ hlabel
    dp obs hne (fun o ho => hI o (by simp [ho]))
    (List.Pairwise.sublist (List.sublist_append_left _ _) hdisj) obj₀ h₀ obj hrun
  have hrun2 : obj' ∈ (obs ++ obs').foldlM
      (fun o x => o.observeSet (𝕋 := 𝕋) 0 x.1 x.2.1 x.2.2) obj₀ := by
    rw [List.foldlM_append, Option.mem_def.1 hrun]; exact hrun'
  obtain ⟨s', hs', root', hr', hroot'⟩ := OnlineReachSetAnalyzer.observeSet_correct (𝕋 := 𝕋) φ
    hlabel dp (obs ++ obs') (by simp [hne]) hI hdisj obj₀ h₀ obj' hrun2
  -- the semantics after more observations refines the one before
  set σ : AtomicProposition S d → FourValuedSignal ℝ :=
    fun _ => FourValuedSignal.uniformSignal .ii with hσ
  have hv0 : ∀ a, (σ a).IsValid := fun _ => (FourValuedSignal.uniformSignal_spec _).1
  obtain ⟨hva, hii⟩ := OnlineReachSetAnalyzer.observeAtoms_spec (𝕋 := 𝕋) obs σ hv0
  have hpw := List.pairwise_append.1 hdisj
  have href : ∀ a, (OnlineReachSetAnalyzer.observeAtoms (𝕋 := 𝕋) σ (obs ++ obs') a).Refines
      (OnlineReachSetAnalyzer.observeAtoms (𝕋 := 𝕋) σ obs a) := by
    intro a
    have e : OnlineReachSetAnalyzer.observeAtoms (𝕋 := 𝕋) σ (obs ++ obs') =
        OnlineReachSetAnalyzer.observeAtoms (𝕋 := 𝕋)
          (OnlineReachSetAnalyzer.observeAtoms (𝕋 := 𝕋) σ obs) obs' := by
      simp [OnlineReachSetAnalyzer.observeAtoms, List.foldl_append]
    rw [e]
    refine aux_observeAtoms_refines (𝕋 := 𝕋) obs' hpw.2.1 _ hva
      (fun a t ht hne o' ho' hmem => ?_) a
    rcases hii a t ht hne with h | ⟨o, ho, ht'⟩
    · exact h ((FourValuedSignal.uniformSignal_spec _).2 t ht)
    · exact Set.disjoint_left.1 (hpw.2.2 o ho o' ho') ht' hmem
  have hva' := (OnlineReachSetAnalyzer.observeAtoms_spec (𝕋 := 𝕋) (obs ++ obs') σ hv0).1
  have hss := φ.sat_refines _ _ hva hva' href s s' hs hs'
  -- the verdict is the root value at time `0`
  simp only [OnlineReachSetAnalyzer.getVerdict, hr, Option.map_some, Option.mem_def,
    Option.some.injEq] at hv
  simp only [OnlineReachSetAnalyzer.getVerdict, hr', Option.map_some, Option.some.injEq]
  rw [hroot' 0 le_rfl, hss 0 le_rfl (by rw [← hroot 0 le_rfl, hv]; exact hconc),
    ← hroot 0 le_rfl, hv]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
