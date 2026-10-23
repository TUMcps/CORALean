module

public import CORALean.Specification.FourValuedSignal.Theorems.UntilSpec
public import CORALean.Specification.FourValuedSignal.Theorems.IsRefinedByIff
public import CORALean.Specification.KleeneSignal.Theorems.UntilMono
public import CORALean.Specification.Kleene.Theorems.Basic

@[expose] public section

/-!
# The until of four-valued signals respects refinement

If the Kleene signals `Λ₁`, `Λ₂` refine the four-valued `Λ̃₁`, `Λ̃₂`, then
`Λ₁ U_I Λ₂ ≺ Λ̃₁ U_I Λ̃₂`: the step of the induction in [1, Thm. 2] for `U_I`. It is the reason
[1, Sec. 4.3 (operators)] defines the operator through [1, Lemma 3]: where the untils of `⌊Λ̃⌋`
and `⌈Λ̃⌉` agree, they bound that of every refinement between them (`KleeneSignal.until_mono`),
which is then their common value.

## Inputs
* `l` – left four-valued signal
* `r` – right four-valued signal
* `kl` – left three-valued signal
* `kr` – right three-valued signal
* `U` – time interval

## Hypotheses
* `hl` – the left four-valued signal is valid
* `hr` – the right four-valued signal is valid
* `hkl` – the left three-valued signal is valid
* `hkr` – the right three-valued signal is valid
* `h₁` – the left three-valued signal refines the left signal
* `h₂` – the right three-valued signal refines the right signal

## Conclusion
* the until is valid and refined by the three-valued until

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


-- =======================================  MAIN THEOREM  ======================================= --

theorem FourValuedSignal.until_isRefinedBy (l r : FourValuedSignal ℝ) (kl kr : KleeneSignal ℝ)
    (hl : l.IsValid) (hr : r.IsValid) (hkl : kl.IsValid) (hkr : kr.IsValid)
    (h₁ : l.IsRefinedBy kl) (h₂ : r.IsRefinedBy kr) (U : STLInterval ℝ) : -- --- CONCL ---
    ∃ s, l.until U r = some s ∧ s.IsValid ∧ s.IsRefinedBy (kl.until U kr) := by -- --- PROOF ---
  obtain ⟨s, hs, hvs, hc⟩ := FourValuedSignal.until_spec l r hl hr U
  refine ⟨s, hs, hvs, fun t ht => ?_⟩
  obtain ⟨c1, c2, -⟩ := hc t ht
  -- the underapproximations and overapproximations bound the refinements
  rw [FourValuedSignal.isRefinedBy_iff l hl] at h₁
  rw [FourValuedSignal.isRefinedBy_iff r hr] at h₂
  have f₁ := (l.toKleeneSignal_spec hl Kleene.ff).1
  have f₂ := (r.toKleeneSignal_spec hr Kleene.ff).1
  have c₁ := (l.toKleeneSignal_spec hl Kleene.tt).1
  have c₂ := (r.toKleeneSignal_spec hr Kleene.tt).1
  have lo := KleeneSignal.until_mono _ _ _ _ f₁ hkl f₂ hkr U (fun x hx => (h₁ x hx).1)
    (fun x hx => (h₂ x hx).1) t ht
  have hi := KleeneSignal.until_mono _ _ _ _ hkl c₁ hkr c₂ U (fun x hx => (h₁ x hx).2)
    (fun x hx => (h₂ x hx).2) t ht
  -- if the result is conclusive, the two bounds agree, and squeeze the refinement
  intro hne
  have heq := not_not.1 (mt c1.2 hne)
  have hi' : (kl.until U kr).at t ≤ ((l.toKleeneSignal Kleene.ff).until U
      (r.toKleeneSignal Kleene.ff)).at t := by
    rw [heq]
    exact hi
  have hmid := le_antisymm hi' lo
  rw [hmid]
  exact (c2 heq).symm

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
