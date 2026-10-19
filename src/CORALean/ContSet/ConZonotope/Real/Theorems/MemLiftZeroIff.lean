module

public import CORALean.ContSet.ConZonotope.Real.Operations.Lift
public import CORALean.ContSet.ConZonotope.Real.Operations.MemOfMatIff

@[expose] public section

/-!
# The lifted zonotope at the trivial partition

[1, Prop. 3] at `m₂ = 0`: the constraint of `Z⁺ = {[G; A], [c; −b]}` is empty, so `Z⁺` is the
zonotope its generators span, and membership is a zonotope's.

## References

* [1] J. K. Scott, D. M. Raimondo, G. R. Marseglia and R. D. Braatz. "Constrained zonotopes:
      A new tool for set-based estimation and fault detection". Automatica, 69:126-136,
      2016.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Prop. 3] at the trivial partition, `m₂ = 0`: `Z⁺ = {[G; A], [c; −b]}` is a zonotope. -/
theorem ConZonotope.mem_lift_zero_iff {n m h : ℕ} (c : Vec ℝ n) (G : Fin h → Vec ℝ n)
    (A : Mat ℝ (m + 0) h) (b : Vec ℝ (m + 0)) (x : Vec ℝ (n + m)) : -- --- CONCL ---
    x ∈ (ConZonotope.lift (m₂ := 0) c G A b).construct ↔
      ∃ β : Fin h → ℝ, (∀ j, |β j| ≤ 1) ∧
        x = Fin.append c (-fun i => b (Fin.castAdd 0 i))
          + ∑ j, β j • Fin.append (G j) fun i => A (Fin.castAdd 0 i) j := by -- --- PROOF ---
  unfold ConZonotope.lift
  rw [ConZonotope.mem_ofMat_iff]
  -- the empty constraint block holds of every `β`
  exact ⟨fun ⟨β, hβ, _, hx⟩ => ⟨β, hβ, hx⟩, fun ⟨β, hβ, hx⟩ => ⟨β, hβ, fun i => i.elim0, hx⟩⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
