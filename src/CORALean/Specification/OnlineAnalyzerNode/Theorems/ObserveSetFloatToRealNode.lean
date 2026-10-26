module

public import CORALean.Specification.FourValuedSignal.Theorems.SetMapTime
public import CORALean.Specification.OnlineAnalyzerNode.Operations.ObserveSet
public import CORALean.Specification.OnlineAnalyzerNode.Operations.ObserveSetFloat
public import CORALean.Specification.OnlineAnalyzerNode.Operations.ToRealNode
public import CORALean.Specification.OnlineAnalyzerNode.Theorems.ConflictsFloatToReal
public import CORALean.Specification.TentativeKleeneSignal.Theorems.ObserveMapTime

@[expose] public section

/-!
# What `observeSetFloat` does, read as reals

Over a float scalar the conflict test compares the bounds exactly (`conflictsFloat_toReal`) and the
observation sets the signal, or the tentative signal, on the interval by exact comparisons
(`set_mapTime`, `observe_mapTime`), so the float result read as reals is `observeSet` on the node
and interval read as reals, and both throw together.

## Inputs
* `eps` – machine epsilon
* `n` – leaf node
* `set` – observed set
* `interval` – observed time interval
* `loc` – location
* `tentative` – observation is tentative

## Hypotheses
* none

## Conclusion
* the float result, read as reals, is the real one
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ExactLe 𝕋] [Scalar 𝕋]
  [ExactScalar 𝕋] {S : ℕ → Type} {d : ℕ} [∀ k, ContSet (S k) (Vec ℝ k)] [Mtimes (Mat 𝕋) S]
  [∀ k, Contains (S k) (S k)] [∀ k, IsDisjoint (S k) (S k)]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

omit [ExactLe 𝕋] [Scalar 𝕋] [ExactScalar 𝕋] in
/-- The infimum of an interval read as reals is the infimum read as reals. -/
private theorem aux_infimum_toRealInterval (I : STLInterval 𝕋) :
    I.toRealInterval.infimum.value = I.infimum.value.map (·.map toReal) ∧
      I.toRealInterval.infimum.closed = I.infimum.closed := by
  rcases I with _ | ⟨l, u, lc, rc, hu, hlt, h0⟩
  · exact ⟨rfl, rfl⟩
  · rcases u with _ | u <;> exact ⟨rfl, rfl⟩


-- =======================================  MAIN THEOREM  ======================================= --

theorem OnlineAnalyzerNode.observeSetFloat_toRealNode (eps : 𝕋)
    (n : OnlineAnalyzerNode 𝕋 (AtomicProposition S d)) (set : S d) (interval : STLInterval 𝕋)
    (loc : ℕ) (tentative : Bool) : -- --- CONCL ---
    (n.observeSetFloat eps set interval loc tentative).map OnlineAnalyzerNode.toRealNode =
      n.toRealNode.observeSet (𝕋 := 𝕋) (toReal eps) set interval.toRealInterval loc
        tentative := by -- --- PROOF ---
  unfold OnlineAnalyzerNode.observeSetFloat OnlineAnalyzerNode.observeSet
  have hk : n.toRealNode.kind = n.kind := rfl
  rw [hk]
  by_cases hleaf : n.kind ≠ .true ∧ n.kind ≠ .false ∧ n.kind ≠ .ap
  · rw [if_pos hleaf, if_pos hleaf]; rfl
  · rw [if_neg hleaf, if_neg hleaf]
    obtain ⟨hi1, hi2⟩ := aux_infimum_toRealInterval interval
    have hp : n.toRealNode.prop = n.prop.map (·.toRealInterval) := rfl
    rw [hi1, hi2, hp, OnlineAnalyzerNode.conflictsFloat_toReal]
    generalize OnlineAnalyzerNode.conflicts (toReal eps)
      (interval.infimum.value.map (·.map toReal)) interval.infimum.closed
      (n.prop.map (·.toRealInterval)) = c
    rcases c with _ | bad
    · rfl
    · simp only [Option.bind_some]
      by_cases hb : bad = true
      · rw [if_pos hb, if_pos hb]; rfl
      · rw [if_neg hb, if_neg hb]
        -- the leaf kinds: the proposition's value, then the tentative or the final signal
        have ha : n.toRealNode.ap = n.ap := rfl
        have ht : n.toRealNode.tentative = n.tentative.map (·.mapTime toReal) := rfl
        rcases hkn : n.kind with _ | _ | _ | _ | _ | _ | _ <;> simp only [hkn] at hleaf ⊢ <;>
          first | rfl | skip
        · -- an AP node derives its value from the set
          simp only [ha, ht]
          rcases n.ap with _ | ap
          · rfl
          · simp only [Option.bind_some]
            rcases OnlineAnalyzerNode.apValue (𝕋 := 𝕋) ap set loc with _ | val
            · rfl
            · simp only [Option.bind_some]
              by_cases htent : tentative = true
              · rw [if_pos htent, if_pos htent]
                rcases hnt : n.tentative with _ | tent
                · rfl
                · simp [OnlineAnalyzerNode.toRealNode, TentativeKleeneSignal.observe_mapTime]
              · rw [if_neg htent, if_neg htent]
                simp [OnlineAnalyzerNode.toRealNode, FourValuedSignal.set_mapTime]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
