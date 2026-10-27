module

public import CORALean.ContSet.PolyZonotope.Real.Operations.RelaxExpEven

@[expose] public section

/-!
# [1, Thm. 1]'s printed center shift `+ξ_E/2` does not enclose

[1, Thm. 1] recenters the relaxed polynomial zonotope by `+ξ_E/2` of the dropped generator
`g_i` where `relaxExpEven` shifts by `-ξ_E/2`. Under the orientation `E_{k₀,j} ≤ E_{k₀,i}`
that `Alg. 2`'s edges have, both exponents even, the drift `α^{E_i} - α^{E_j}` is
non-positive, so the printed sign moves the set off the drift. One dimension is enough:
one factor `α`, `g_i = 1` at exponent `2` and `g_j = 0` at exponent `0`, so the set is
`α² ∈ [0, 1]` and `ξ_E = 1`. The printed relaxation is `½ + 1 + β/2 ∈ [1, 2]`, which
misses `0 = 0²`. Every hypothesis `relaxExpEven_outer` asks for holds, so the sign is the
only fault.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* the printed center shift does not enclose in general

## References

* [1] [T. Ladner and M. Althoff. "Exponent Relaxation of Polynomial Zonotopes and Its Applications
      in Formal Neural Network Verification". Proceedings of the AAAI Conference on Artificial
      Intelligence, 2024.](../../../../../../references/2024/ladner-aaai-exponent-relaxation.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Thm. 1] as printed: the relaxation recentered by `+ξ_E/2` does not enclose, even
with the evenness of `E_{k₀,j}` and the orientation `E_{k₀,j} ≤ E_{k₀,i}` supplied. -/
theorem PolyZonotope.relaxExpEven_printed_counterexample : -- --- CONCL ---
    ¬ ∀ (pZ : PolyZonotope ℝ) (d : ℕ) (part : Split (Fin pZ.h) into (Fin d) ⊕ (Fin 2))
      (k₀ : Fin pZ.p),
      (∀ k, k ≠ k₀ → pZ.E k (part.right 0) = pZ.E k (part.right 1)) →
      (∀ k, Even (pZ.E k (part.right 0))) → Even (pZ.E k₀ (part.right 1)) →
      pZ.E k₀ (part.right 1) ≤ pZ.E k₀ (part.right 0) →
      pZ.construct ⊆ { pZ.relaxExpEven part k₀ with
        c := pZ.c + ((pZ.relaxWidth part k₀ : ℝ) / 2) • pZ.G (part.right 0)
      }.construct := by -- --- PROOF ---
  intro h
  -- `0 = 0²` is in the set, with `α = 0`
  have hsub := h ⟨1, 2, 0, 0, ![1, 0], fun _ => ![2, 0], fun j => j.elim0⟩ 0
    (Partition.split 0 2) 0 (fun k hk => absurd (Subsingleton.elim _ _) hk)
    (fun k => ⟨1, rfl⟩) ⟨0, rfl⟩ (by decide)
    (show (0 : ℝ) ∈ _ from ⟨fun _ => 0, fun j => j.elim0, fun _ => by simp, fun j => j.elim0, by
      simp [PolyZonotope.monomial, Fin.sum_univ_succ]⟩)
  -- the printed relaxation is `½ + 1 + β/2 ≥ 1` at every coefficient
  obtain ⟨a, β, ha, hβ, hx⟩ := hsub
  have hr0 : (Partition.split 0 2).right 0 = (0 : Fin 2) := rfl
  have hr1 : (Partition.split 0 2).right 1 = (1 : Fin 2) := rfl
  simp [PolyZonotope.monomial, PolyZonotope.relaxExpEven, PolyZonotope.relaxWidth,
    PolyZonotope.eDiffTight, hr0, hr1, Fin.append, Fin.addCases] at hx
  have hb := abs_le.mp (hβ (Fin.last 0))
  have hx' : (0 : ℝ) = 2⁻¹ + 1 + β (Fin.last 0) * 2⁻¹ := hx
  linarith [hb.1]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
