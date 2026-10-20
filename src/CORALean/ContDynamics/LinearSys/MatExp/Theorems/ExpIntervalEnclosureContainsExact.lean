module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpIntervalEnclosure
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpIntervalEnclosureExact
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpIntervalTaylor
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpIntervalWAttained

@[expose] public section

/-!
# The exact-second-order enclosure is inside the uniform one

What [1, Thm. 3.2] buys over [1, Sec. 3.3.1] as `expIntervalEnclosure` writes it: the same
remainder, the same orders from three on, and orders one and two narrower, so the sharper
enclosure is contained in the cruder one and never the other way. The comparison is where
*exactness* pays off rather than soundness: each bound of `expIntervalW` is a value `W(t)` really
takes, and `expIntervalTaylor` is sound, so that value lies in the cruder box. Soundness of
`expIntervalW` alone would say nothing about which of the two is narrower.

## Inputs
* `A` – interval matrix
* `t` – time
* `κ` – Taylor order

## Hypotheses
* `ht` – time nonzero
* `hA` – box nonempty
* `hκ` – order at least two

## Conclusion
* the exact-second-order enclosure lies inside the uniform one

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Claude Opus 5
-- Written:       12-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Above order two the two recursions peel the same term, so the uniform
truncation is the order-two one plus the tail the exact truncation reuses. -/
theorem aux_taylor_split (B : Interval (Mat ℝ n n)) (m : ℕ) (i j : Fin n) : -- --- CONCL ---
    (MatExp.expIntervalTaylor B (m + 2)).inf i j
        = (MatExp.expIntervalTaylor B 2).inf i j
          + (MatExp.expIntervalTaylorTail B (m + 2)).inf i j
      ∧ (MatExp.expIntervalTaylor B (m + 2)).sup i j
        = (MatExp.expIntervalTaylor B 2).sup i j
          + (MatExp.expIntervalTaylorTail B (m + 2)).sup i j := by -- --- PROOF ---
  induction m with
  | zero =>
    -- at order two the tail is `point 0`, so nothing is added
    constructor <;>
      simp only [MatExp.expIntervalTaylorTail, Interval.point, Matrix.zero_apply, add_zero]
  | succ p ih =>
    -- both recursions are `plus` of the same top order onto their own predecessor
    have h1 : MatExp.expIntervalTaylor B (p + 3)
        = Interval.plus (Interval.smul ((Nat.factorial (p + 3) : ℝ)⁻¹)
            (Interval.matPow B (p + 3))) (MatExp.expIntervalTaylor B (p + 2)) := rfl
    have h2 : MatExp.expIntervalTaylorTail B (p + 3)
        = Interval.plus (Interval.smul ((Nat.factorial (p + 3) : ℝ)⁻¹)
            (Interval.matPow B (p + 3))) (MatExp.expIntervalTaylorTail B (p + 2)) := rfl
    refine ⟨?_, ?_⟩
    · show (MatExp.expIntervalTaylor B (p + 3)).inf i j
          = (MatExp.expIntervalTaylor B 2).inf i j
            + (MatExp.expIntervalTaylorTail B (p + 3)).inf i j
      rw [h1, h2]
      simp only [Interval.plus, Matrix.add_apply]
      rw [ih.1]; ring
    · show (MatExp.expIntervalTaylor B (p + 3)).sup i j
          = (MatExp.expIntervalTaylor B 2).sup i j
            + (MatExp.expIntervalTaylorTail B (p + 3)).sup i j
      rw [h1, h2]
      simp only [Interval.plus, Matrix.add_apply]
      rw [ih.2]; ring


-- =======================================  MAIN THEOREM  ======================================= --

/-- The cruder enclosure of [1, Sec. 3.3.1] contains the sharper one of
[1, Thm. 3.2], entry by entry and at every order from two up. -/
theorem MatExp.expIntervalEnclosure_contains_exact (A : Interval (Mat ℝ n n)) {t : ℝ}
    (ht : t ≠ 0) (hA : ∀ p q, A.inf p q ≤ A.sup p q) {κ : ℕ} (hκ : 2 ≤ κ) : -- --- CONCL ---
    (MatExp.expIntervalEnclosureExact A t κ).construct
      ⊆ (MatExp.expIntervalEnclosure (Interval.smul t A) κ).construct := by -- --- PROOF ---
  obtain ⟨m, rfl⟩ : ∃ m, κ = m + 2 := ⟨κ - 2, by omega⟩
  intro X hX
  refine Interval.mem_mat_iff.mpr fun i j => ?_
  have hx := Interval.mem_mat_iff.mp hX i j
  -- orders zero to two of the uniform truncation, against `I + W(t)`
  have hlow : (MatExp.expIntervalTaylor (Interval.smul t A) 2).inf i j
      ≤ (1 : Mat ℝ n n) i j + (MatExp.expIntervalW A t).inf i j := by
    obtain ⟨N, hN, hNeq⟩ := (MatExp.expIntervalW_attained A ht hA i j).1
    have h := Interval.mem_mat_iff.mp (MatExp.expTaylor_mem_expIntervalTaylor
      (Interval.smul t A) (Interval.smul_outer t A hN) 2) i j
    rw [MatExp.expTaylor_two, Matrix.add_apply] at h
    rw [← hNeq]
    exact h.1
  have hhigh : (1 : Mat ℝ n n) i j + (MatExp.expIntervalW A t).sup i j
      ≤ (MatExp.expIntervalTaylor (Interval.smul t A) 2).sup i j := by
    obtain ⟨N, hN, hNeq⟩ := (MatExp.expIntervalW_attained A ht hA i j).2
    have h := Interval.mem_mat_iff.mp (MatExp.expTaylor_mem_expIntervalTaylor
      (Interval.smul t A) (Interval.smul_outer t A hN) 2) i j
    rw [MatExp.expTaylor_two, Matrix.add_apply] at h
    rw [← hNeq]
    exact h.2
  -- the exact truncation, read as its three summands
  have hExactInf : (MatExp.expIntervalTaylorExact A t (m + 2)).inf i j
      = (1 : Mat ℝ n n) i j + (MatExp.expIntervalW A t).inf i j
        + (MatExp.expIntervalTaylorTail (Interval.smul t A) (m + 2)).inf i j := by
    simp only [MatExp.expIntervalTaylorExact, Interval.plus, Interval.point, Matrix.add_apply]
  have hExactSup : (MatExp.expIntervalTaylorExact A t (m + 2)).sup i j
      = (1 : Mat ℝ n n) i j + (MatExp.expIntervalW A t).sup i j
        + (MatExp.expIntervalTaylorTail (Interval.smul t A) (m + 2)).sup i j := by
    simp only [MatExp.expIntervalTaylorExact, Interval.plus, Interval.point, Matrix.add_apply]
  have hsplit := aux_taylor_split (Interval.smul t A) m i j
  -- the remainders cancel, so only the truncations are compared
  refine ⟨?_, ?_⟩
  · show (MatExp.expIntervalTaylor (Interval.smul t A) (m + 2)).inf i j
        - MatExp.expRemainderBound (Interval.smul t A).absMax (m + 2) ≤ X i j
    have hx1 : (MatExp.expIntervalTaylorExact A t (m + 2)).inf i j
        - MatExp.expRemainderBound (Interval.smul t A).absMax (m + 2) ≤ X i j := hx.1
    -- the tail summand is shared and drops out of the comparison
    rw [hsplit.1]
    rw [hExactInf] at hx1
    linarith
  · show X i j ≤ (MatExp.expIntervalTaylor (Interval.smul t A) (m + 2)).sup i j
        + MatExp.expRemainderBound (Interval.smul t A).absMax (m + 2)
    have hx2 : X i j ≤ (MatExp.expIntervalTaylorExact A t (m + 2)).sup i j
        + MatExp.expRemainderBound (Interval.smul t A).absMax (m + 2) := hx.2
    rw [hsplit.2]
    rw [hExactSup] at hx2
    linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
