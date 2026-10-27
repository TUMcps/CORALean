module

public import CORALean.Specification.OnlineAnalyzerNode.Operations.GetAllProp
public import CORALean.Specification.OnlineAnalyzerNode.Operations.GetAllPropFloat
public import CORALean.Specification.OnlineAnalyzerNode.Operations.ToRealNode
public import CORALean.Specification.STLInterval.Theorems.Basic
public import CORALean.Specification.STLInterval.Theorems.StlIntervalToRealInterval
public import CORALean.Specification.STLInterval.Theorems.WithinTolFloatIff

@[expose] public section

/-!
# `getAllPropFloat` read as reals is `getAllProp`

Over a float scalar the loop of `getAllPropFloat` compares the bounds and tests `withinTol` exactly
on the reals they denote, so it picks the bound `getAllProp` picks on the node read as reals, and
the interval it builds, read as reals, is the one `getAllProp` builds.

## Inputs
* `eps` – machine epsilon
* `n` – node

## Hypotheses
* none

## Conclusion
* the float interval read as reals is the exact one
-/

-- Authors:       Claude Opus 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ExactLe 𝕋] {A : Type}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The loop picks the same bound, read as a real. -/
private theorem OnlineAnalyzerNode.aux_propBoundFloat_toReal (eps : 𝕋)
    (ps : List (STLInterval 𝕋)) : -- --- CONCL ---
    ∀ st : WithTop 𝕋 × Bool,
      Prod.map (WithTop.map toReal) id (OnlineAnalyzerNode.step_propBoundFloat eps ps st) =
        OnlineAnalyzerNode.propBound (toReal eps) (ps.map STLInterval.toRealInterval)
          (Prod.map (WithTop.map toReal) id st) := by -- --- PROOF ---
  induction ps with
  | nil => intro st; rfl
  | cons p rest ih =>
    intro st
    obtain ⟨ub, rc⟩ := st
    rcases p with _ | ⟨l, u, lc', rc', hu, hlt, h0⟩
    · -- an empty interval: the bound `0`, open
      simp [OnlineAnalyzerNode.step_propBoundFloat, OnlineAnalyzerNode.propBound,
        STLInterval.toRealInterval, toReal_zero_eq]
    · -- the new bound and the old compared exactly
      obtain ⟨h1, h2, h3, hp⟩ : ∃ h1 h2 h3,
          STLInterval.toRealInterval (STLInterval.nonempty l u lc' rc' hu hlt h0) =
            STLInterval.nonempty (toReal l) (u.map toReal) lc' rc' h1 h2 h3 := by
        rcases u with _ | u <;> exact ⟨_, _, _, rfl⟩
      rw [List.map_cons, hp]
      simp only [OnlineAnalyzerNode.step_propBoundFloat, OnlineAnalyzerNode.propBound,
        Prod.map_apply, id_eq, STLInterval.toEReal_map_toReal]
      open Classical in
      by_cases hc : STLInterval.toEReal u < STLInterval.toEReal ub ∨
          (STLInterval.withinTolFloat eps u ub = true ∧ rc' = false)
      · rw [if_pos hc, if_pos, ih]
        · rfl
        · simpa [STLInterval.withinTolFloat_iff] using hc
      · rw [if_neg hc, if_neg, ih]
        · rfl
        · simpa [STLInterval.withinTolFloat_iff] using hc


-- =======================================  MAIN THEOREM  ======================================= --

theorem OnlineAnalyzerNode.getAllPropFloat_toRealInterval (eps : 𝕋)
    (n : OnlineAnalyzerNode 𝕋 A) : -- --- CONCL ---
    (n.getAllPropFloat eps).toRealInterval =
      n.toRealNode.getAllProp (toReal eps) := by -- --- PROOF ---
  have h := OnlineAnalyzerNode.aux_propBoundFloat_toReal eps n.prop (⊤, true)
  unfold OnlineAnalyzerNode.getAllPropFloat OnlineAnalyzerNode.getAllProp
  rw [STLInterval.stlInterval_toRealInterval]
  simp only [OnlineAnalyzerNode.toRealNode]
  rw [← show (Prod.map (WithTop.map (toReal (𝕋 := 𝕋))) id ((⊤ : WithTop 𝕋), true) :
    WithTop ℝ × Bool) = (⊤, true) from rfl, ← h]
  simp only [Prod.map_fst, Prod.map_snd, id_eq, toReal_zero_eq]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
