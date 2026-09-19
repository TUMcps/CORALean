import CORALean.ContSet.Zonotope.Real.AutoTuneSetOrder
import CORALean.ContSet.Zonotope.Real.Theorems.ReduceBoxErrorEqZero

/-!
# `Alg. 2` lines 19-22 always land

The third sentence of [1, Thm. 1]'s proof, as a theorem about the sweep this tree
computes: "the reduction error `Δε^r_k(ρ_k)` can be set to `0` by simply omitting the
reduction, which trivially satisfies any bound `ε^{r,τ}_k`". Omitting the reduction is
the sweep's *last* candidate, `ρ = Z.h + 1`, where `reduce` drops no generator and
`Δε^r_k` reads `0`; so a non-negative admissible share is the whole hypothesis.

The check must be complete here, `a ≤ b → le a b = true`, which is the converse of what
a soundness statement about the same sweep would ask: a check that gives up early is
sound but need never report anything.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of
      Linear Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE
      Transactions on Automatic Control, vol. 68, no. 12, 2023, pp. 7771–7786.
-/

-- Authors:       Tobias Ladner
-- Written:       19-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The sweep reports as soon as its fuel reaches an order coarse enough to drop no
generator, and every earlier candidate it accepts reports too. -/
theorem aux_autoTuneSetOrder_exists {le : ℝ → ℝ → Bool}
    (hle : ∀ a b : ℝ, a ≤ b → le a b = true) (Z : Zonotope (Vec ℝ n)) {εrτ : ℝ}
    (hεrτ : 0 ≤ εrτ) :
    ∀ (m ρ : ℕ), Z.h ≤ (ρ + 1 + m) * n →
      ∃ ρ', Zonotope.autoTuneSetOrder le Z εrτ ρ (m + 1) = some ρ' := by -- --- PROOF ---
  intro m
  induction m with
  | zero =>
    intro ρ h
    have hzero : Z.reduceBoxError (ρ + 1) = 0 :=
      Zonotope.reduceBoxError_eq_zero Z (by simpa using h)
    have hchk : le (Z.reduceBoxError (ρ + 1)) εrτ = true := by
      rw [hzero]; exact hle 0 εrτ hεrτ
    refine ⟨ρ + 1, ?_⟩
    rw [Zonotope.autoTuneSetOrder]
    simp only [hchk, if_true]
  | succ m ih =>
    intro ρ h
    rw [Zonotope.autoTuneSetOrder]
    split
    · exact ⟨ρ + 1, rfl⟩
    -- this candidate was refused, so the sweep moves one order up with the rest of the fuel
    · refine ih (ρ + 1) ?_
      have hidx : ρ + 1 + 1 + m = ρ + 1 + (m + 1) := by omega
      rw [hidx]; exact h


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Alg. 2] lines 19-22: the order sweep is not vacuous. A non-negative admissible
share `ε^{r,τ}_k` is enough for it to report one, the `Z.h + 1` candidates always
reaching an order that reduces nothing. -/
theorem Zonotope.exists_autoTuneSetOrder {le : ℝ → ℝ → Bool}
    (hle : ∀ a b : ℝ, a ≤ b → le a b = true) (Z : Zonotope (Vec ℝ n)) {εrτ : ℝ}
    (hn : 0 < n) (hεrτ : 0 ≤ εrτ) :
    ∃ ρ, Zonotope.autoTuneSetOrder le Z εrτ 0 (Z.h + 1) = some ρ :=
  aux_autoTuneSetOrder_exists hle Z hεrτ Z.h 0
    (calc Z.h ≤ 0 + 1 + Z.h := by omega
      _ ≤ (0 + 1 + Z.h) * n := Nat.le_mul_of_pos_right _ hn)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
