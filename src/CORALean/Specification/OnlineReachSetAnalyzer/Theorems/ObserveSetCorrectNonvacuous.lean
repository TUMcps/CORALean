module

public import CORALean.Specification.OnlineReachSetAnalyzer.Definitions.IsSub
public import CORALean.Specification.OnlineReachSetAnalyzer.Theorems.GetVerdictAp

@[expose] public section

/-!
# The hypotheses of the analyzer's correctness can be met

For an atom `ap l a` the labels name one atom, its analyzer exists, and one observation on an
interval holding `0` is a run of `observeSet_correct` with a conclusive verdict whenever the atom
is decided on the observed set [1, Alg. 1].

## Inputs
* `l` – label
* `a` – atomic proposition
* `dp` – whether to propagate down
* `set` – observed set
* `loc` – location
* `I` – observation interval

## Hypotheses
* `hne` – `I` is nonempty
* `h0` – `I` holds `0`

## Conclusion
* for the value `val` of `a` on `set`, the labels of `ap l a` name one atom, and the run from its
  analyzer on the one observation succeeds with verdict `val`

## References

* [1] [F. Lercher and M. Althoff. "Using Four-Valued Signal Temporal Logic for Incremental
      Verification of Hybrid Systems". Computer Aided Verification,
      2024.](../../../../../references/2024/lercher-cav-four-valued-stl.md)
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


-- =======================================  MAIN THEOREM  ======================================= --

theorem OnlineReachSetAnalyzer.observeSet_correct_nonvacuous (l : String)
    (a : AtomicProposition S d) (dp : Bool) (set : S d) (loc : ℕ) (I : STLInterval ℝ)
    (hne : I ≠ .empty) (h0 : (0 : ℝ) ∈ I.set) : -- --- CONCL ---
    ∀ val ∈ OnlineAnalyzerNode.apValue (𝕋 := 𝕋) a set loc,
    (∀ l' x y, (OnlineReachSetAnalyzer.Formula.ap l' x).IsSub (.ap l a) →
      (OnlineReachSetAnalyzer.Formula.ap l' y).IsSub (.ap l a) → x = y) ∧
    ∃ obj₀ obj : OnlineReachSetAnalyzer ℝ S d,
      OnlineReachSetAnalyzer.mk? (.ap l a) 1 dp = some obj₀ ∧
      [(set, I, loc)].foldlM (fun o x => o.observeSet (𝕋 := 𝕋) 0 x.1 x.2.1 x.2.2) obj₀ =
        some obj ∧ obj.getVerdict = some (FourValued.fromKleene val) := by -- --- PROOF ---
  intro val hval
  refine ⟨fun l' x y hx hy => ?_, ?_⟩
  · simp only [OnlineReachSetAnalyzer.Formula.IsSub, OnlineReachSetAnalyzer.Formula.ap.injEq]
      at hx hy
    rw [hx.2, hy.2]
  · -- the analyzer of an atom exists, and one observation at time 0 decides it
    obtain ⟨obj₀, h₀⟩ : ∃ obj₀ : OnlineReachSetAnalyzer ℝ S d, OnlineReachSetAnalyzer.mk?
        (.ap l a) 1 dp = some obj₀ := by
      simp [OnlineReachSetAnalyzer.mk?, OnlineReachSetAnalyzer.parse,
        OnlineReachSetAnalyzer.parseNew, OnlineAnalyzerNode.mk?,
            OnlineReachSetAnalyzer.Formula.kind,
        OnlineReachSetAnalyzer.Formula.key, OnlineReachSetAnalyzer.Formula.interval?,
        OnlineReachSetAnalyzer.Formula.ap?]
    obtain ⟨obj, h1, h2, -⟩ := OnlineReachSetAnalyzer.getVerdict_ap (𝕋 := 𝕋) l a dp 0 set loc I
      hne h0 val hval obj₀ h₀
    exact ⟨obj₀, obj, h₀, by simpa using h1, h2⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
