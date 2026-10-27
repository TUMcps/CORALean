module

public import CORALean.Specification.OnlineReachSetAnalyzer.Theorems.ObserveSetCorrectNonvacuous
public import CORALean.Specification.OnlineReachSetAnalyzer.Theorems.ObserveSetFloatSound
public import CORALean.Specification.OnlineAnalyzerNode.Theorems.InitSignalMapTime
public import CORALean.Specification.TentativeKleeneSignal.Theorems.EmptySignalMapTime

@[expose] public section

/-!
# The hypotheses of the float analyzer's soundness can be met

For an atom `ap l a` the labels name one atom, its float analyzer is its analyzer read as reals,
and one observation on an interval holding `0` is a run of `observeSetFloat_sound`: the float and
the exact run both succeed and both have the atom's value on the observed set as verdict
[1, Alg. 1].

## Inputs
* `l` – label
* `a` – atomic proposition
* `dp` – whether to propagate down
* `eps` – tolerance
* `set` – observed set
* `loc` – location
* `I` – observation interval

## Hypotheses
* `heps` – `eps` is `0` as a real
* `hne` – `I` is nonempty
* `h0` – `I` read as reals holds `0`

## Conclusion
* for the value `val` of `a` on `set`, the labels of `ap l a` name one atom, and a float analyzer
  of `ap l a` that is its analyzer read as reals has float and exact runs on the one observation
  that both succeed with verdict `val`

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

open Float SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ExactLe 𝕋] [Scalar 𝕋]
  [ExactScalar 𝕋] {S : ℕ → Type} {d : ℕ} [∀ k, ContSet (S k) (Vec ℝ k)] [Mtimes (Mat 𝕋) S]
  [∀ k, Contains (S k) (S k)] [∀ k, IsDisjoint (S k) (S k)]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- One float observation of a one-atom analyzer, read as reals, is the exact observation. -/
private theorem aux_single (eps : 𝕋) (heps : toReal eps = 0)
    (objF : OnlineReachSetAnalyzer 𝕋 S d)
    (N : OnlineAnalyzerNode 𝕋 (AtomicProposition S d)) (hn : objF.nodes = [N])
    (hl : objF.leaves = [1]) (hf : objF.propagationFrequency = 1) (hk : N.kind = .ap)
    (hch : N.children = []) (set : S d) (I : STLInterval 𝕋) (loc : ℕ) : -- --- CONCL ---
    (objF.observeSetFloat eps set I loc).map OnlineReachSetAnalyzer.toRealAnalyzer =
      objF.toRealAnalyzer.observeSet (𝕋 := 𝕋) 0 set I.toRealInterval loc := by -- --- PROOF ---
  -- the leaf's float observation read as reals is its exact observation
  have hobs := OnlineAnalyzerNode.observeSetFloat_toRealNode eps N set I loc false
  rw [heps] at hobs
  rcases I with _ | ⟨lo, u, lc, rc, hu, hlt, hz⟩
  · simp [OnlineReachSetAnalyzer.observeSetFloat, OnlineReachSetAnalyzer.observeSet,
      STLInterval.toRealInterval]
  · simp only [STLInterval.toRealInterval] at hobs
    simp only [OnlineReachSetAnalyzer.observeSetFloat, OnlineReachSetAnalyzer.observeSet,
      STLInterval.toRealInterval, OnlineReachSetAnalyzer.toRealAnalyzer, hn, hl, hf,
      List.foldlM_cons, List.foldlM_nil, OnlineReachSetAnalyzer.updateNode, List.map_cons,
      List.map_nil]
    -- observing keeps the leaf an atom without children
    have hkc : ∀ N' ∈ N.observeSetFloat eps set (.nonempty lo u lc rc hu hlt hz) loc false,
        N'.kind = .ap ∧ N'.children = [] := by
      intro N' hN'
      simp only [OnlineAnalyzerNode.observeSetFloat, hk, Option.mem_def] at hN'
      simp [Option.bind_eq_some_iff] at hN'
      obtain ⟨_, _, _, _, _, _, rfl⟩ := hN'
      exact ⟨rfl, hch⟩
    rcases u with _ | u <;>
    · simp only at hobs ⊢
      -- the observation fails in both runs, or succeeds with the same node read as reals
      rcases hF : N.observeSetFloat eps set _ loc false with _ | N'
      · rw [hF] at hobs
        simp [← hobs, hF]
      · rw [hF] at hobs
        obtain ⟨hk', hch'⟩ := hkc N' hF
        have hp := (OnlineAnalyzerNode.propagateFloat_toRealNode eps N' [] .empty).1
          (Or.inr (Or.inr hk'))
        rw [heps] at hp
        simp only [Option.map_some] at hobs
        simp only [Nat.sub_self, one_ne_zero, if_false, List.getElem?_cons_zero,
          Option.bind_some, Option.isSome_none]
        rw [hF, ← hobs]
        -- one leaf without children: propagation is the leaf's own
        simp only [OnlineReachSetAnalyzer.propagateFloat, OnlineReachSetAnalyzer.propagate,
          OnlineReachSetAnalyzer.propagateRecFloat, OnlineReachSetAnalyzer.propagateRec]
        simp only [Option.map_some, Option.bind_eq_bind, Option.bind_some, List.set_cons_zero,
          List.length_singleton, List.replicate_one, List.getElem?_cons_zero, hch',
          show N'.toRealNode.children = [] from hch', List.filter_nil, List.eraseDups_nil,
          List.mergeSort_nil, List.foldlM_nil, List.mapM_nil, Option.pure_def, List.zip_nil_left,
          List.foldl_nil, Nat.mod_one, if_true, Nat.sub_self, Option.getD_none]
        simp only [List.map_nil, STLInterval.toRealInterval] at hp
        rw [← hp]
        rcases OnlineAnalyzerNode.propagateFloat eps N' [] STLInterval.empty with _ | ⟨r1, r2⟩
        · simp
        · simp [OnlineReachSetAnalyzer.toRealAnalyzer]


-- =======================================  MAIN THEOREM  ======================================= --

theorem OnlineReachSetAnalyzer.observeSetFloat_sound_nonvacuous (l : String)
    (a : AtomicProposition S d) (dp : Bool) (eps : 𝕋) (heps : toReal eps = 0) (set : S d)
    (loc : ℕ) (I : STLInterval 𝕋) (hne : I ≠ .empty)
    (h0 : (0 : ℝ) ∈ I.toRealInterval.set) : -- --- CONCL ---
    ∀ val ∈ OnlineAnalyzerNode.apValue (𝕋 := 𝕋) a set loc,
    (∀ l' x y, (OnlineReachSetAnalyzer.Formula.ap l' x).IsSub (.ap l a) →
      (OnlineReachSetAnalyzer.Formula.ap l' y).IsSub (.ap l a) → x = y) ∧
    ∃ (objF₀ objF : OnlineReachSetAnalyzer 𝕋 S d) (obj : OnlineReachSetAnalyzer ℝ S d),
      OnlineReachSetAnalyzer.mk? (.ap l a) 1 dp = some objF₀.toRealAnalyzer ∧
      [(set, I, loc)].foldlM (fun o x => o.observeSetFloat eps x.1 x.2.1 x.2.2) objF₀ = some objF ∧
      ([(set, I, loc)].map fun x => (x.1, x.2.1.toRealInterval, x.2.2)).foldlM
        (fun o x => o.observeSet (𝕋 := 𝕋) 0 x.1 x.2.1 x.2.2) objF₀.toRealAnalyzer = some obj ∧
      objF.getVerdict = some (FourValued.fromKleene val) ∧
      obj.getVerdict = some (FourValued.fromKleene val) := by -- --- PROOF ---
  intro val hval
  have hneR : I.toRealInterval ≠ .empty := by
    rcases I with _ | ⟨lo, _ | u, lc, rc, hu, hlt, hz⟩
    · exact absurd rfl hne
    · simp [STLInterval.toRealInterval]
    · simp [STLInterval.toRealInterval]
  refine ⟨(OnlineReachSetAnalyzer.observeSet_correct_nonvacuous (𝕋 := 𝕋) l a dp set loc
    I.toRealInterval hneR h0 val hval).1, ?_⟩
  -- the float analyzer of an atom is one fresh node, which read as reals is the exact one
  obtain ⟨objF₀, N, -, hR, hn, hl, hf, hk, hch⟩ : ∃ (objF₀ : OnlineReachSetAnalyzer 𝕋 S d)
      (N : OnlineAnalyzerNode 𝕋 (AtomicProposition S d)),
      OnlineReachSetAnalyzer.mk? (.ap l a) 1 dp = some objF₀ ∧
      OnlineReachSetAnalyzer.mk? (.ap l a) 1 dp = some objF₀.toRealAnalyzer ∧
      objF₀.nodes = [N] ∧ objF₀.leaves = [1] ∧ objF₀.propagationFrequency = 1 ∧
      N.kind = .ap ∧ N.children = [] := by
    simp [OnlineReachSetAnalyzer.mk?, OnlineReachSetAnalyzer.parse,
      OnlineReachSetAnalyzer.parseNew, OnlineAnalyzerNode.mk?, OnlineReachSetAnalyzer.Formula.kind,
      OnlineReachSetAnalyzer.Formula.key, OnlineReachSetAnalyzer.Formula.interval?,
      OnlineReachSetAnalyzer.Formula.ap?, OnlineReachSetAnalyzer.toRealAnalyzer,
      OnlineAnalyzerNode.toRealNode, OnlineAnalyzerNode.initSignal_mapTime,
      TentativeKleeneSignal.emptySignal_mapTime, STLInterval.toRealInterval]
  -- the exact run
  obtain ⟨obj, hobj, hv⟩ := OnlineReachSetAnalyzer.getVerdict_ap (𝕋 := 𝕋) l a dp 0 set loc
    I.toRealInterval hneR h0 val hval _ hR
  -- the float run read as reals is the exact run
  have hmap := aux_single eps heps objF₀ N hn hl hf hk hch set I loc
  rw [hobj] at hmap
  obtain ⟨objF, hobjF, rfl⟩ := Option.map_eq_some_iff.mp hmap
  refine ⟨objF₀, objF, objF.toRealAnalyzer, hR, by simpa using hobjF, by simpa using hobj, ?_,
    hv.1⟩
  rw [← OnlineReachSetAnalyzer.getVerdict_toRealAnalyzer]
  exact hv.1

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
