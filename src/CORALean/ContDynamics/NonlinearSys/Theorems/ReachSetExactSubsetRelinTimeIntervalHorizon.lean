module

public import CORALean.ContDynamics.NonlinearSys.Theorems.ReachSetExactSubsetRelinTimeInterval
public import CORALean.ContDynamics.LinearSys.MatExp.Definitions.InputRemainderSet

@[expose] public section

/-!
# The horizon, as the union of what the loop computes on each step

`reachSetExact_subset_relinTimeInterval` covers one step; this covers `[0, NΔt]` at once, the line
`Rᵘⁿⁱᵒⁿ = Rᵘⁿⁱᵒⁿ ∪ R(τₛ)` of [1, Alg. 1] and the `R([0, t_f])` it returns. Nothing new is
computed: the union is over the sets the per-step theorem already places the run in. The work is
the covering, where `0 < Δt` and `0 < N` are spent: every `t` of the horizon sits in some step's
window, `⌊t/Δt⌋` naming it except at the right end, where the last step covers `t`. A horizon of
no steps encloses nothing. The union is over `i < N`, so a caller reads a membership off
`Set.mem_iUnion₂`.

## Inputs
* `sys` – system
* `T` – time set
* `R₀` – initial set
* `U` – input set
* `steps` – linearization steps
* `Δt` – step size
* `N` – number of steps
* `q` – Taylor terms minus two
* `o` – maximum order
* `t` – time

## Hypotheses
* `hΔt` – step size positive
* `hN` – step count positive
* `hT` – horizon inside time set
* `hR` – reachable set inside certified regions
* `hε` – step norm small enough
* `hconv` – widened input convex
* `hclosed` – widened input closed
* `hbdd` – widened input bounded
* `h0` – zero in widened input
* `hRconv` – remainder input convex
* `hRclosed` – remainder input closed
* `hRbdd` – remainder input bounded
* `ho` – order positive
* `ht` – time within the horizon

## Conclusion
* the exact reachable set at the time lies in the union of step enclosures

## References

* [1] N. Kochdumper and M. Althoff. "Sparse Polynomial Zonotopes: A Novel Set
      Representation for Reachability Analysis". IEEE Transactions on Automatic
      Control, 2021.
-/

-- Authors:       Claude Opus 5
-- Written:       13-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar NormedSpace Plus Mtimes OfInterval

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n m : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)]
variable [∀ n, LinComb (S n) (Vec ℝ n)]
variable [Mtimes (Mat ℝ) S] [OfInterval S] [Mtimes ℐ S]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Every time of `[0, NΔt]` is in the window of some step below `N`. -/
theorem aux_exists_step {Δt : ℝ} (hΔt : 0 < Δt) {N : ℕ} (hN : 0 < N) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) ((N : ℝ) * Δt)) : -- --- CONCL ---
    ∃ i < N, t ∈ Set.Icc ((i : ℝ) * Δt) (((i : ℝ) + 1) * Δt) := by -- --- PROOF ---
  have hN1 : 1 ≤ N := hN
  by_cases h : ((N : ℝ) - 1) * Δt ≤ t
  -- the right end, where `⌊t/Δt⌋` is `N` itself: the last step covers it
  · have hcast : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
      rw [Nat.cast_sub hN1, Nat.cast_one]
    refine ⟨N - 1, Nat.sub_lt hN one_pos, ?_, ?_⟩
    · rw [hcast]; exact h
    · rw [hcast]; nlinarith [ht.2]
  -- everywhere else, the floor names the step, and stays below `N - 1`
  · have h' : t < ((N : ℝ) - 1) * Δt := not_le.mp h
    have hfl : ((⌊t / Δt⌋₊ : ℕ) : ℝ) ≤ t / Δt := Nat.floor_le (div_nonneg ht.1 hΔt.le)
    have hlo : ((⌊t / Δt⌋₊ : ℕ) : ℝ) * Δt ≤ t := (le_div_iff₀ hΔt).mp hfl
    have hhi : t ≤ (((⌊t / Δt⌋₊ : ℕ) : ℝ) + 1) * Δt :=
      (div_le_iff₀ hΔt).mp (Nat.lt_floor_add_one (t / Δt)).le
    have hltR : ((⌊t / Δt⌋₊ : ℕ) : ℝ) < (N : ℝ) := by nlinarith
    exact ⟨⌊t / Δt⌋₊, by exact_mod_cast hltR, hlo, hhi⟩


-- =======================================  MAIN THEOREM  ======================================= --

/-- The reachable set at every time of `[0, NΔt]` lies in the union of the `N`
sets the loop computes, one per step. -/
theorem NonlinearSys.reachSetExact_subset_relinTimeInterval_horizon (sys : NonlinearSys n m)
    {T : Set ℝ} (R₀ : S n) (U : S m) {steps : ℕ → sys.LinStep U} {Δt : ℝ} {N : ℕ}
    (hΔt : 0 < Δt) (hN : 0 < N) (hT : Set.Icc 0 ((N : ℝ) * Δt) ⊆ T)
    (hR : ∀ i < N, ∀ t ∈ Set.Icc ((i : ℝ) * Δt) (((i : ℝ) + 1) * Δt),
      sys.reachSetExact T R₀ U t ⊆ (steps i).R)
    (q : ℕ) (hε : ∀ i < N, ‖Δt • (steps i).A‖ / (((q + 2 : ℕ) : ℝ) + 2) < 1)
    (hconv : ∀ i < N, Convex ℝ (construct (steps i).linInput))
    (hclosed : ∀ i < N, IsClosed (construct (steps i).linInput))
    (hbdd : ∀ i < N, Bornology.IsBounded (construct (steps i).linInput))
    (h0 : ∀ i < N, (0 : Vec ℝ n) ∈ construct (steps i).linInput)
    (hRconv : ∀ i < N, Convex ℝ (MatExp.inputRemainderSet (steps i).A Δt (q + 2) (steps
      i).linInput))
    (hRclosed : ∀ i < N, IsClosed (MatExp.inputRemainderSet (steps i).A Δt (q + 2) (steps
      i).linInput))
    (hRbdd : ∀ i < N, Bornology.IsBounded (MatExp.inputRemainderSet (steps i).A Δt (q + 2) (steps
      i).linInput))
    {o : ℕ} (ho : 0 < o) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) ((N : ℝ) * Δt)) : -- --- CONCL ---
    sys.reachSetExact T R₀ U t ⊆ ⋃ i < N, construct (sys.relinTimeInterval o ho Δt (q + 2) steps
      (fun i => (NonlinearSys.linearize (steps i).A).inputSolution Δt (q + 2)
        (steps i).linInput) R₀ i) := by -- --- PROOF ---
  -- the step whose window holds `t`, and then that step's own enclosure
  obtain ⟨i, hi, hti⟩ := aux_exists_step hΔt hN ht
  intro y hy
  exact Set.mem_iUnion₂.mpr ⟨i, hi, sys.reachSetExact_subset_relinTimeInterval R₀ U hΔt hT hR q hε
    hconv hclosed hbdd h0 hRconv hRclosed hRbdd ho i hi hti hy⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
