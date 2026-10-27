module

public import CORALean.Specification.Definitions.VerifyAnswer
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.List.FinRange

@[expose] public section

/-!
# `verifyHalfspacePrinted`, `[1, Alg. 2]` as printed

The control flow of the listing over given bound tables `bndUp`, `bndLo` per round `r`
(`Δt = t_end / 2 ^ r`), step `k` and direction `i`: one direction after the other (line 1), a
`repeat` that halves `Δt` until `verified` (lines 3-14), and in it a sweep over the steps whose
falsification test (line 9) is the `else if` of the safety test (line 7). `fuel` bounds each
`repeat`; running out answers `undecided`. `verifyHalfspace` is the repaired order.

# The printed `Alg. 2` never falsifies

Line 9 is reached only when line 7's upper bound is at most `f(i)`, so wherever every lower bound
is at most its upper bound (the bounds of one set) it never fires: the listing never returns
`unsafe`, and the `Sec. 5.1 (termination)` claim fails on every unsafe instance.

## Inputs
* `ι` – index type of the directions
* `bndUp` – upper bounds per round, step and direction
* `bndLo` – lower bounds per round, step and direction
* `d` – offsets `f`
* `fuel` – rounds each `repeat` may take

## Hypotheses
* `hle` – every lower bound at most the upper bound of its round, step and direction

## Conclusion
* the printed listing never answers `unsafe`, for any list of directions

## References

* [1] [M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Reachability Analysis with Support Functions". Proceedings of the 26th ACM
      International Conference on Hybrid Systems: Computation and Control,
      2023.](../../../../references/2023/wetzlinger-hscc-support-functions.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       27-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped Classical in
/-- `[1, Alg. 2]`, lines 5-12 at one round and direction: the sweep over the steps `ks`, `none`
for line 10's `return unsafe`, else `some` of the flag `verified`. -/
noncomputable def verifyHalfspacePrintedSweep {κ : Type} (up lo : κ → ℝ) (f : ℝ) :
    List κ → Bool → Option Bool
  -- 12. the loop has run through every step
  | [], verified => some verified
  | k :: ks, verified =>
      -- 6. `ρ(R̂(τₖ), ℓᵢ), ρ(Ř(τₖ), ℓᵢ) ← Alg. 1 with Δt`
      let ρhat := up k
      let ρcheck := lo k
      -- 7. `if ρ(R̂(τₖ), ℓᵢ) > f(i)`: 8. `verified ← false`
      if f < ρhat then verifyHalfspacePrintedSweep up lo f ks false
      -- 9. `else if ρ(Ř(τₖ), ℓᵢ) > f(i)`: 10. `return unsafe`
      else if f < ρcheck then none
      else verifyHalfspacePrintedSweep up lo f ks verified

/-- `[1, Alg. 2]`, lines 3-14 for the direction `i` from round `r`: `violated` for line 10,
`safe` once `verified` holds, `undecided` when `fuel` runs out. -/
noncomputable def verifyHalfspacePrintedRepeat {ι : Type}
    (bndUp bndLo : (r : ℕ) → Fin (2 ^ r) → ι → ℝ) (d : ι → ℝ) (i : ι) : ℕ → ℕ → VerifyAnswer
  | r, 0 =>
      -- 4. `verified ← true`, 5-12. the sweep over `k ← 0 to t_end/Δt − 1`
      let sweep := verifyHalfspacePrintedSweep (bndUp r · i) (bndLo r · i) (d i)
        (List.finRange (2 ^ r)) true
      match sweep with
      -- 10. `return unsafe`
      | none => .violated
      -- 14. `until verified = true`
      | some verified => if verified then .safe else .undecided
  | r, fuel + 1 =>
      -- 4. `verified ← true`, 5-12. the sweep over `k ← 0 to t_end/Δt − 1`
      let sweep := verifyHalfspacePrintedSweep (bndUp r · i) (bndLo r · i) (d i)
        (List.finRange (2 ^ r)) true
      match sweep with
      -- 10. `return unsafe`
      | none => .violated
      -- 14. `until verified = true`, else 13. `Δt ← 0.5 Δt`
      | some verified =>
          if verified then .safe else verifyHalfspacePrintedRepeat bndUp bndLo d i (r + 1) fuel

/-- `[1, Alg. 2]` as printed: each direction of `dirs` in turn from `Δt = t_end` (lines 1-2),
the next one once its `repeat` verifies, `safe` after the last (line 16). -/
noncomputable def verifyHalfspacePrinted {ι : Type}
    (bndUp bndLo : (r : ℕ) → Fin (2 ^ r) → ι → ℝ) (d : ι → ℝ) (fuel : ℕ) :
    List ι → VerifyAnswer
  -- 16. `return safe`
  | [] => .safe
  | i :: is =>
      -- 2. `ℓᵢ ← H(i,·)ᵀ`, `Δt ← t_end`: round `0`; 3-14. the `repeat`
      let answer := verifyHalfspacePrintedRepeat bndUp bndLo d i 0 fuel
      -- 15. the next direction once this one is verified
      match answer with
      | .safe => verifyHalfspacePrinted bndUp bndLo d fuel is
      | a => a


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- With every lower bound at most its upper bound, the sweep never takes line 10. -/
private theorem aux_sweep_ne_none {κ : Type} {up lo : κ → ℝ} {f : ℝ} (hle : ∀ k, lo k ≤ up k) :
    ∀ (ks : List κ) (v : Bool), verifyHalfspacePrintedSweep up lo f ks v ≠ none
  | [], v => by simp [verifyHalfspacePrintedSweep]
  | k :: ks, v => by
      simp only [verifyHalfspacePrintedSweep]
      split_ifs with h1 h2
      · exact aux_sweep_ne_none hle ks false
      · exact absurd (lt_of_lt_of_le h2 (hle k)) h1
      · exact aux_sweep_ne_none hle ks v

/-- A sweep that has cleared `verified` never sets it again. -/
private theorem aux_sweep_false {κ : Type} {up lo : κ → ℝ} {f : ℝ} :
    ∀ ks : List κ, verifyHalfspacePrintedSweep up lo f ks false ≠ some true
  | [] => by simp [verifyHalfspacePrintedSweep]
  | k :: ks => by
      simp only [verifyHalfspacePrintedSweep]
      split_ifs
      · exact aux_sweep_false ks
      · simp
      · exact aux_sweep_false ks

/-- Once a step's upper bound exceeds the offset, the sweep's flag is `false` or it returned. -/
private theorem aux_sweep_ne_some_true {κ : Type} {up lo : κ → ℝ} {f : ℝ} :
    ∀ (ks : List κ) (v : Bool), (∃ k ∈ ks, f < up k) →
      verifyHalfspacePrintedSweep up lo f ks v ≠ some true
  | [], _, ⟨_, hk, _⟩ => by simp at hk
  | k :: ks, v, ⟨k', hk', hlt⟩ => by
      simp only [verifyHalfspacePrintedSweep]
      split_ifs with h1 h2
      · exact aux_sweep_false ks
      · simp
      · rcases List.mem_cons.mp hk' with rfl | hk'
        · exact absurd hlt h1
        · exact aux_sweep_ne_some_true ks v ⟨k', hk', hlt⟩

/-- Line 10 never fires, so a `repeat` answers `safe` or `undecided`. -/
private theorem aux_repeat_ne_violated {ι : Type} {bndUp bndLo : (r : ℕ) → Fin (2 ^ r) → ι → ℝ}
    {d : ι → ℝ} (hle : ∀ r k i, bndLo r k i ≤ bndUp r k i) (i : ι) :
    ∀ (r fuel : ℕ), verifyHalfspacePrintedRepeat bndUp bndLo d i r fuel ≠ .violated
  | r, 0 => by
      have h := aux_sweep_ne_none (f := d i) (fun k => hle r k i) (List.finRange (2 ^ r)) true
      simp only [verifyHalfspacePrintedRepeat]
      split
      · contradiction
      · split_ifs <;> simp
  | r, fuel + 1 => by
      have h := aux_sweep_ne_none (f := d i) (fun k => hle r k i) (List.finRange (2 ^ r)) true
      simp only [verifyHalfspacePrintedRepeat]
      split
      · contradiction
      · split_ifs
        · simp
        · exact aux_repeat_ne_violated hle i (r + 1) fuel

/-- A direction whose every round has an upper bound above its offset never verifies: its
`repeat` answers `undecided`. -/
private theorem aux_repeat_eq_undecided {ι : Type} {bndUp bndLo : (r : ℕ) → Fin (2 ^ r) → ι → ℝ}
    {d : ι → ℝ} (hle : ∀ r k i, bndLo r k i ≤ bndUp r k i) {i : ι}
    (hup : ∀ r, ∃ k, d i < bndUp r k i) :
    ∀ (r fuel : ℕ), verifyHalfspacePrintedRepeat bndUp bndLo d i r fuel = .undecided
  | r, 0 => by
      have h := aux_sweep_ne_none (f := d i) (fun k => hle r k i) (List.finRange (2 ^ r)) true
      obtain ⟨k, hk⟩ := hup r
      have h' := aux_sweep_ne_some_true (up := (bndUp r · i)) (lo := (bndLo r · i)) (f := d i)
        (List.finRange (2 ^ r)) true ⟨k, List.mem_finRange k, hk⟩
      simp only [verifyHalfspacePrintedRepeat]
      split
      · contradiction
      · split_ifs with hv
        · subst hv; contradiction
        · rfl
  | r, fuel + 1 => by
      have h := aux_sweep_ne_none (f := d i) (fun k => hle r k i) (List.finRange (2 ^ r)) true
      obtain ⟨k, hk⟩ := hup r
      have h' := aux_sweep_ne_some_true (up := (bndUp r · i)) (lo := (bndLo r · i)) (f := d i)
        (List.finRange (2 ^ r)) true ⟨k, List.mem_finRange k, hk⟩
      simp only [verifyHalfspacePrintedRepeat]
      split
      · contradiction
      · split_ifs with hv
        · subst hv; contradiction
        · exact aux_repeat_eq_undecided hle hup (r + 1) fuel


-- =======================================  MAIN THEOREM  ======================================= --

/-- `[1, Sec. 5.1 (termination)]`: `[1, Alg. 2]` as printed never answers `unsafe` when every lower
bound is at most its upper bound. -/
theorem verifyHalfspacePrinted_ne_violated {ι : Type}
    {bndUp bndLo : (r : ℕ) → Fin (2 ^ r) → ι → ℝ} {d : ι → ℝ}
    (hle : ∀ r k i, bndLo r k i ≤ bndUp r k i) (fuel : ℕ) :
    ∀ dirs : List ι, verifyHalfspacePrinted bndUp bndLo d fuel dirs ≠ .violated
  | [] => by simp [verifyHalfspacePrinted]
  | i :: is => by
      have h := aux_repeat_ne_violated (d := d) hle i 0 fuel
      simp only [verifyHalfspacePrinted]
      split
      · exact verifyHalfspacePrinted_ne_violated hle fuel is
      · assumption

/-- `[1, Sec. 5.1 (termination)]`: with a direction of `dirs` whose upper bounds exceed its offset
at some step of every round, `[1, Alg. 2]` as printed answers `undecided` for every `fuel`. -/
theorem verifyHalfspacePrinted_eq_undecided {ι : Type}
    {bndUp bndLo : (r : ℕ) → Fin (2 ^ r) → ι → ℝ} {d : ι → ℝ}
    (hle : ∀ r k i, bndLo r k i ≤ bndUp r k i) {i : ι} (hup : ∀ r, ∃ k, d i < bndUp r k i)
    (fuel : ℕ) : -- --- CONCL ---
    ∀ dirs : List ι, i ∈ dirs →
      verifyHalfspacePrinted bndUp bndLo d fuel dirs = .undecided := by -- --- PROOF ---
  intro dirs hi
  induction dirs with
  | nil => simp at hi
  | cons j js ih =>
    have hne := aux_repeat_ne_violated (d := d) hle j 0 fuel
    rcases List.mem_cons.mp hi with rfl | hi'
    · simp only [verifyHalfspacePrinted, aux_repeat_eq_undecided hle hup 0 fuel]
    · cases h : verifyHalfspacePrintedRepeat bndUp bndLo d j 0 fuel with
      | safe => simp only [verifyHalfspacePrinted, h]; exact ih hi'
      | violated => exact absurd h hne
      | undecided => simp only [verifyHalfspacePrinted, h]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
