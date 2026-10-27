module

public import CORALean.Specification.OnlineReachSetAnalyzer.Theorems.SatSpec
public import CORALean.Specification.FourValuedSignal.Definitions.Refines
public import CORALean.Specification.FourValuedSignal.Theorems.AtAndTwo
public import CORALean.Specification.FourValuedSignal.Theorems.AtOrTwo
public import CORALean.Specification.FourValuedSignal.Theorems.UntilRefines
public import CORALean.Specification.FourValuedSignal.Theorems.AtNot
public import CORALean.Specification.FourValued.Theorems.Basic

@[expose] public section

/-!
# More observed atoms refine the satisfaction signal

If the atom signals `sig'` refine `sig`, the satisfaction signal of every formula over `sig'`
refines the one over `sig`: a value other than ⊣₂ is never revised by refining the atoms. This is
the monotonicity [1, Sec. 4.3 (operators)] builds the `U₂`-operators on (`Lemma 3`), lifted to
formulas; `FourValuedSTL.sound_fourValued` ([1, Thm. 2]) is the case of a total extension.

## Inputs
* `sig` – atom signals that know less
* `sig'` – atom signals that know more
* `φ` – formula

## Hypotheses
* `hv` – `sig` is valid
* `hv'` – `sig'` is valid
* `h` – `sig'` refines `sig`

## Conclusion
* the satisfaction signal over `sig'` refines the one over `sig`

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


variable {A : Type}


-- =======================================  MAIN THEOREM  ======================================= --

theorem OnlineReachSetAnalyzer.Formula.sat_refines (sig sig' : A → FourValuedSignal ℝ)
    (hv : ∀ a, (sig a).IsValid) (hv' : ∀ a, (sig' a).IsValid)
    (h : ∀ a, (sig' a).Refines (sig a)) (φ : OnlineReachSetAnalyzer.Formula ℝ A) : -- --- CONCL ---
    ∀ s s', φ.sat sig = some s → φ.sat sig' = some s' → s'.Refines s := by -- --- PROOF ---
  -- each operator respects refinement
  induction φ with
  | tt => intro s s' hs hs'; simp [OnlineReachSetAnalyzer.Formula.sat] at hs hs'; subst hs hs'
          exact FourValuedSignal.Refines.refl _
  | ff => intro s s' hs hs'; simp [OnlineReachSetAnalyzer.Formula.sat] at hs hs'; subst hs hs'
          exact FourValuedSignal.Refines.refl _
  | ap _ a => intro s s' hs hs'; simp [OnlineReachSetAnalyzer.Formula.sat] at hs hs'; subst hs hs'
              exact h a
  | not φ ih =>
    -- pointwise, through the value of `¬`
    intro s s' hs hs'
    obtain ⟨l, hl, hlv⟩ := φ.sat_spec sig hv
    obtain ⟨l', hl', hlv'⟩ := φ.sat_spec sig' hv'
    simp [OnlineReachSetAnalyzer.Formula.sat, hl, hl'] at hs hs'; subst hs hs'
    intro t ht hne
    rw [FourValuedSignal.at_not _ hlv] at hne ⊢
    rw [FourValuedSignal.at_not _ hlv']
    exact FourValued.not_refines _ _ (ih l l' hl hl' t ht) hne
  | and φ ψ ih ih' =>
    -- pointwise, through the value of `&`
    intro s s' hs hs'
    obtain ⟨l, hl, hlv⟩ := φ.sat_spec sig hv
    obtain ⟨l', hl', hlv'⟩ := φ.sat_spec sig' hv'
    obtain ⟨r, hr, hrv⟩ := ψ.sat_spec sig hv
    obtain ⟨r', hr', hrv'⟩ := ψ.sat_spec sig' hv'
    simp only [OnlineReachSetAnalyzer.Formula.sat, hl, hl', hr, hr', Option.bind_some] at hs hs'
    obtain ⟨a, ha, -, ha'⟩ := FourValuedSignal.at_and_two ![l, r] (by
      intro k; fin_cases k <;> simpa)
    obtain ⟨b, hb, -, hb'⟩ := FourValuedSignal.at_and_two ![l', r'] (by
      intro k; fin_cases k <;> simpa)
    rw [ha] at hs; rw [hb] at hs'; cases hs; cases hs'
    intro t ht hne
    rw [ha' t ht] at hne ⊢; rw [hb' t ht]
    exact FourValued.and_refines _ _ _ _ (ih l l' hl hl' t ht) (ih' r r' hr hr' t ht) hne
  | or φ ψ ih ih' =>
    -- pointwise, through the value of `|`
    intro s s' hs hs'
    obtain ⟨l, hl, hlv⟩ := φ.sat_spec sig hv
    obtain ⟨l', hl', hlv'⟩ := φ.sat_spec sig' hv'
    obtain ⟨r, hr, hrv⟩ := ψ.sat_spec sig hv
    obtain ⟨r', hr', hrv'⟩ := ψ.sat_spec sig' hv'
    simp only [OnlineReachSetAnalyzer.Formula.sat, hl, hl', hr, hr', Option.bind_some] at hs hs'
    obtain ⟨a, ha, -, ha'⟩ := FourValuedSignal.at_or_two ![l, r] (by
      intro k; fin_cases k <;> simpa)
    obtain ⟨b, hb, -, hb'⟩ := FourValuedSignal.at_or_two ![l', r'] (by
      intro k; fin_cases k <;> simpa)
    rw [ha] at hs; rw [hb] at hs'; cases hs; cases hs'
    intro t ht hne
    rw [ha' t ht] at hne ⊢; rw [hb' t ht]
    exact FourValued.or_refines _ _ _ _ (ih l l' hl hl' t ht) (ih' r r' hr hr' t ht) hne
  | «until» I φ ψ ih ih' =>
    -- through the refinements of the operands
    intro s s' hs hs'
    obtain ⟨l, hl, hlv⟩ := φ.sat_spec sig hv
    obtain ⟨l', hl', hlv'⟩ := φ.sat_spec sig' hv'
    obtain ⟨r, hr, hrv⟩ := ψ.sat_spec sig hv
    obtain ⟨r', hr', hrv'⟩ := ψ.sat_spec sig' hv'
    simp only [OnlineReachSetAnalyzer.Formula.sat, hl, hl', hr, hr', Option.bind_some] at hs hs'
    obtain ⟨a, b, ha, hb, -, -, hab, -⟩ := FourValuedSignal.until_refines l r l' r' hlv hrv hlv'
      hrv' I
    rw [ha] at hs; rw [hb] at hs'; cases hs; cases hs'
    exact hab (ih l l' hl hl') (ih' r r' hr hr')

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
