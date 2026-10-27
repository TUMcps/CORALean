module

public import CORALean.Specification.OnlineReachSetAnalyzer.Operations.Sat
public import CORALean.Specification.FourValuedSignal.Theorems.AtAnd
public import CORALean.Specification.FourValuedSignal.Theorems.AtOr
public import CORALean.Specification.FourValuedSignal.Theorems.UntilSpec
public import CORALean.Specification.FourValuedSignal.Theorems.UniformSignalSpec
public import CORALean.Specification.FourValuedSignal.Theorems.Basic

@[expose] public section

/-!
# The satisfaction signal exists and is valid

For valid atom signals the four-valued satisfaction signal of every formula exists: none of the
operators throws, and each is valid on valid operands.

## Inputs
* `sig` – signal of each atom
* `φ` – formula

## Hypotheses
* `hv` – the atom signals are valid

## Conclusion
* `φ.sat sig` is a valid signal
-/

-- Authors:       Claude Opus 5.5
-- Written:       27-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


variable {A : Type}


-- =======================================  MAIN THEOREM  ======================================= --

theorem OnlineReachSetAnalyzer.Formula.sat_spec (sig : A → FourValuedSignal ℝ)
    (hv : ∀ a, (sig a).IsValid) (φ : OnlineReachSetAnalyzer.Formula ℝ A) : -- --- CONCL ---
    ∃ s, φ.sat sig = some s ∧ s.IsValid := by -- --- PROOF ---
  -- by the operators, each of which exists and is valid on valid operands
  induction φ with
  | tt => exact ⟨_, rfl, (FourValuedSignal.uniformSignal_spec _).1⟩
  | ff => exact ⟨_, rfl, (FourValuedSignal.uniformSignal_spec _).1⟩
  | ap _ a => exact ⟨_, rfl, hv a⟩
  | not φ ih =>
    obtain ⟨s, hs, hsv⟩ := ih
    exact ⟨s.not, by simp [OnlineReachSetAnalyzer.Formula.sat, hs],
      FourValuedSignal.not_isValid _ hsv⟩
  | and φ ψ ih ih' =>
    obtain ⟨s, hs, hsv⟩ := ih
    obtain ⟨s', hs', hsv'⟩ := ih'
    obtain ⟨r, hr, hrv, -⟩ := FourValuedSignal.at_and ![s, s'] (by
      intro k; fin_cases k <;> simpa)
    exact ⟨r, by simp [OnlineReachSetAnalyzer.Formula.sat, hs, hs', hr], hrv⟩
  | or φ ψ ih ih' =>
    obtain ⟨s, hs, hsv⟩ := ih
    obtain ⟨s', hs', hsv'⟩ := ih'
    -- the disjunction of two valid operands is valid
    obtain ⟨r, hr, hrv, -⟩ := FourValuedSignal.at_or ![s, s'] (by
      intro k; fin_cases k <;> simpa)
    exact ⟨r, by simp [OnlineReachSetAnalyzer.Formula.sat, hs, hs', hr], hrv⟩
  | «until» I φ ψ ih ih' =>
    obtain ⟨s, hs, hsv⟩ := ih
    obtain ⟨s', hs', hsv'⟩ := ih'
    obtain ⟨r, hr, hrv, -⟩ := FourValuedSignal.until_spec s s' hsv hsv' I
    exact ⟨r, by simp [OnlineReachSetAnalyzer.Formula.sat, hs, hs', hr], hrv⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
