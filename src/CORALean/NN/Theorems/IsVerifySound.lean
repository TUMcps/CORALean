module

public import CORALean.NN.Operations.Verify
public import CORALean.NN.Theorems.EncloseUnsafeInputsOuter
public import CORALean.ContSet.ConZonotope.Real.Theorems.FourierMotzkinIterOuter
public import CORALean.ContSet.Zonotope.Real.Theorems.InterIneqsEqEmptyOfRow
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# The set-based verification is sound

[1, Alg. 1] (`SetBasedNet.verify`): a `VERIFIED` means no input of any queued set is unsafe, a
`FALSIFIED(x̃)` that `x̃` lies in a queued set and `Φ(x̃) ∈ U`. A set dropped by (8) has
`Φ(X) ⊆ Y` and `Y ∩ U = ∅`; a refined set loses no unsafe input, which lies in `X|_{C≤d}`
([1, Prop. 2]), in a piece of the split (the pieces cover the box) and in that piece's bounds
([1, Prop. 3]); every piece lies in its set. This is what [1, Cor. 1] says for one refinement,
carried over the queue. It holds for any split covering the box and any number of passes.

## Inputs
* `N` – set-based network
* `Φ` – the function it encloses
* `A` – unsafe-set matrix
* `b` – unsafe-set offset
* `split` – the split constraints of each input set
* `iterFM` – passes of Prop. 3 per piece
* `fuel` – budget of input sets
* `Q` – queue of input sets

## Hypotheses
* `hN` – `N` relaxes `Φ` with pointwise approximation errors
* `hsplit` – the split pieces of every set cover its unit box of factors

## Conclusion
* `VERIFIED` proves every queued set safe, `FALSIFIED(x̃)` gives an unsafe input of one

## References

* [1] [L. Koller, T. Ladner and M. Althoff. "Out of the Shadows: Exploring a Latent Space for Neural
      Network Verification". International Conference on Learning Representations,
      2026.](../../../../references/2026/koller-iclr-latent-space.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       21-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n k p : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The passes of Prop. 3 from the unit box stay inside it. -/
private theorem aux_iter_subset_unit {r q : ℕ} (C : Mat ℝ r q) (d : Vec ℝ r) (m : ℕ)
    (j : Fin q) : -- --- CONCL ---
    -1 ≤ (ConZonotope.fourierMotzkinIter C d m).inf j ∧
      (ConZonotope.fourierMotzkinIter C d m).sup j ≤ 1 := by -- --- PROOF ---
  simp only [ConZonotope.fourierMotzkinIter]
  induction m with
  | zero => exact ⟨le_rfl, le_rfl⟩
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    simp only [ConZonotope.fourierMotzkinBounds]
    exact ⟨ih.1.trans ((Finset.le_fold_max _).2 (Or.inl le_rfl)),
      ((Finset.fold_min_le _).2 (Or.inl le_rfl)).trans ih.2⟩

/-- A point of a zonotope whose factors lie in `[β̲, β̄]` is a point of the rescaled zonotope. -/
private theorem aux_mem_rescale (X : Zonotope (Vec ℝ n)) (lo hi β : Fin X.h → ℝ)
    (hβ : ∀ j, lo j ≤ β j ∧ β j ≤ hi j) : -- --- CONCL ---
    X.c + ∑ j, β j • X.G j ∈ (⟨X.h, X.c + ∑ j, ((lo j + hi j) / 2) • X.G j,
      fun j => ((hi j - lo j) / 2) • X.G j⟩ : Zonotope (Vec ℝ n)).construct := by -- --- PROOF ---
  -- `β = β_c + β_r t` with `t ∈ [-1, 1]`
  refine ⟨fun j => if hi j - lo j = 0 then 0 else (β j - (lo j + hi j) / 2) / ((hi j - lo j) / 2),
    fun j => ?_, ?_⟩
  · -- `|t(j)| ≤ 1`, from `β̲(j) ≤ β(j) ≤ β̄(j)`
    dsimp only
    split_ifs with h0
    · simp
    · have hr : 0 < (hi j - lo j) / 2 := by
        have := hβ j
        rcases lt_or_eq_of_le (sub_nonneg.2 (this.1.trans this.2)) with h | h
        · linarith
        · exact absurd h.symm h0
      rw [abs_div, abs_of_pos hr, div_le_one hr, abs_le]
      constructor <;> linarith [hβ j]
  · -- `β(j) = β_c(j) + t(j) β_r(j)`, generator by generator
    rw [add_assoc, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_smul, ← add_smul]
    congr 1
    dsimp only
    split_ifs with h0
    · have := hβ j
      linarith
    · field_simp
      ring

/-- The factors of the falsification candidate lie in the unit box. -/
private theorem aux_abs_zonotackFactors_le {k : ℕ} (Y : Zonotope (Vec ℝ k)) (a : Vec ℝ k)
    (j : Fin Y.h) : -- --- CONCL ---
    |Y.zonotackFactors a j| ≤ 1 := by -- --- PROOF ---
  simp only [Zonotope.zonotackFactors, abs_neg]
  rcases lt_trichotomy (a ⬝ᵥ Y.G j) 0 with h | h | h
  · simp [sign_neg h]
  · simp [h]
  · simp [sign_pos h]

/-- A point of a piece lies in its input set: the factor box is inside `[-1, 1]`. -/
private theorem aux_piece_subset (X : Zonotope (Vec ℝ n)) (Cd : Mat ℝ p X.h × Vec ℝ p)
    (s : Σ r : ℕ, Mat ℝ r X.h × Vec ℝ r) (iterFM : ℕ) (P : Zonotope (Vec ℝ n))
    (hP : aux_piece X Cd s iterFM = some P) : -- --- CONCL ---
    P.construct ⊆ X.construct := by -- --- PROOF ---
  simp only [aux_piece] at hP
  split_ifs at hP with hempty
  cases hP
  have hu := fun j => aux_iter_subset_unit (Fin.append Cd.1 s.2.1) (Fin.append Cd.2 s.2.2) iterFM j
  push Not at hempty
  generalize ConZonotope.fourierMotzkinIter (Fin.append Cd.1 s.2.1) (Fin.append Cd.2 s.2.2)
    iterFM = Bβ at hu hempty ⊢
  intro x hx
  obtain ⟨t, ht, rfl⟩ : ∃ t : Fin X.h → ℝ, (∀ j, |t j| ≤ 1) ∧
      x = (X.c + ∑ j, ((Bβ.inf j + Bβ.sup j) / 2) • X.G j) +
        ∑ j, t j • (((Bβ.sup j - Bβ.inf j) / 2) • X.G j) := hx
  -- the factor `β_c + β_r t` lies in `[β̲, β̄] ⊆ [-1, 1]`
  refine ⟨fun j => (Bβ.inf j + Bβ.sup j) / 2 + t j * ((Bβ.sup j - Bβ.inf j) / 2),
    fun j => ?_, ?_⟩
  · have hle := hempty j
    have htj := abs_le.1 (ht j)
    have hr : 0 ≤ (Bβ.sup j - Bβ.inf j) / 2 := by linarith
    have hu1 := (hu j).1
    have hu2 := (hu j).2
    rw [abs_le]
    constructor <;> nlinarith
  · simp only [add_smul, Finset.sum_add_distrib, smul_smul, add_assoc]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Alg. 1] is sound: `VERIFIED` proves the queue safe, `FALSIFIED(x̃)` an unsafe input. -/
theorem SetBasedNet.verify_sound {N : SetBasedNet n k} {Φ : Vec ℝ n → Vec ℝ k}
    (hN : N.IsRelaxationOf Φ) (A : Mat ℝ p k) (b : Vec ℝ p)
    (split : (X : Zonotope (Vec ℝ n)) → List (Σ r : ℕ, Mat ℝ r X.h × Vec ℝ r)) (iterFM : ℕ)
    (hsplit : ∀ (X : Zonotope (Vec ℝ n)) (β : Fin X.h → ℝ), (∀ j, |β j| ≤ 1) →
      ∃ s ∈ split X, ∀ i, (s.2.1 *ᵥ β) i ≤ s.2.2 i)
    (fuel : ℕ) (Q : List (Zonotope (Vec ℝ n))) : -- --- CONCL ---
    (N.verify Φ A b split iterFM fuel Q = .verified →
        ∀ X ∈ Q, ∀ x ∈ X.construct, Φ x ∉ (HPolytope.ineqs A b).construct) ∧
      ∀ x, N.verify Φ A b split iterFM fuel Q = .falsified x →
        (∃ X ∈ Q, x ∈ X.construct) ∧ Φ x ∈ (HPolytope.ineqs A b).construct := by -- --- PROOF ---
  induction fuel generalizing Q with
  | zero =>
    cases Q with
    | nil => exact ⟨fun _ X hX => absurd hX List.not_mem_nil, fun x h => by cases h⟩
    | cons Xi Q =>
      exact ⟨fun h => by simp [SetBasedNet.verify] at h,
        fun x h => by simp [SetBasedNet.verify] at h⟩
  | succ fuel ih =>
    cases Q with
    | nil => exact ⟨fun _ X hX => absurd hX List.not_mem_nil, fun x h => by cases h⟩
    | cons Xi Q =>
      obtain ⟨hQv, hQf⟩ := ih Q
      by_cases hchk : ∃ i, b i < (A *ᵥ (N.forward Xi).c) i - ∑ j, |(A *ᵥ (N.forward Xi).G j) i|
      · -- (8) verifies `X_i`: `Φ(X_i) ⊆ Y_i` and `Y_i ∩ U = ∅`
        have hv : N.verify Φ A b split iterFM (fuel + 1) (Xi :: Q) =
            N.verify Φ A b split iterFM fuel Q := by
          simp only [SetBasedNet.verify, if_pos hchk]
        rw [hv]
        refine ⟨fun h X hX x hx hU => ?_, fun x h => ?_⟩
        · rcases List.mem_cons.1 hX with rfl | hX
          · obtain ⟨β, hβ, rfl⟩ := hx
            obtain ⟨β', hβ', -, hy⟩ := N.forward_latent hN X β hβ
            have hempty := Zonotope.inter_ineqs_eq_empty_of_row _ A b hchk
            exact (Set.eq_empty_iff_forall_notMem.1 hempty) _ ⟨⟨β', hβ', hy⟩, hU⟩
          · exact hQv h X hX x hx hU
        · obtain ⟨⟨X, hX, hx⟩, hU⟩ := hQf x h
          exact ⟨⟨X, List.mem_cons_of_mem _ hX, hx⟩, hU⟩
      · cases hfind : (List.ofFn fun i : Fin p => Xi.c + ∑ j,
            (N.forward Xi).zonotackFactors (A i) (Fin.castLE (N.le_forward_h Xi) j) • Xi.G j).find?
            (fun x => decide (∀ i, (A *ᵥ Φ x) i ≤ b i)) with
        | some x' =>
          -- (9) found an unsafe vertex `x̃ ∈ X_i`
          have hv : N.verify Φ A b split iterFM (fuel + 1) (Xi :: Q) = .falsified x' := by
            simp only [SetBasedNet.verify, if_neg hchk, hfind]
          rw [hv]
          refine ⟨fun h => (by cases h), fun x h => ?_⟩
          cases h
          obtain ⟨i, rfl⟩ := List.mem_ofFn.1 (List.mem_of_find?_eq_some hfind)
          refine ⟨⟨Xi, List.mem_cons_self .., _, fun j => aux_abs_zonotackFactors_le _ _ _, rfl⟩,
            (HPolytope.mem_ineqs_iff).2 ?_⟩
          simpa using List.find?_some hfind
        | none =>
          -- refinement (Prop. 2) and splitting: the pieces join the queue
          have hv : N.verify Φ A b split iterFM (fuel + 1) (Xi :: Q) =
              N.verify Φ A b split iterFM fuel (Q ++ (split Xi).filterMap fun s =>
                aux_piece Xi (N.unsafeInputConstraints Xi A b) s iterFM) := by
            simp only [SetBasedNet.verify, if_neg hchk, hfind]
          rw [hv]
          obtain ⟨hv', hf'⟩ := ih (Q ++ (split Xi).filterMap fun s =>
            aux_piece Xi (N.unsafeInputConstraints Xi A b) s iterFM)
          refine ⟨fun h X hX x hx hU => ?_, fun x h => ?_⟩
          · rcases List.mem_cons.1 hX with rfl | hX
            · -- an unsafe `x ∈ X_i` is in `X_i|_{C≤d}` (Prop. 2), in a piece, in its box (Prop. 3)
              obtain ⟨β, hβ, hP, rfl⟩ : ∃ β : Fin X.h → ℝ, (∀ j, |β j| ≤ 1) ∧
                  β ∈ (HPolytope.ineqs (N.unsafeInputConstraints X A b).1
                    (N.unsafeInputConstraints X A b).2).construct ∧
                  x = X.c + ∑ j, β j • X.G j :=
                (N.encloseUnsafeInputs_outer hN X A b).1 ⟨hx, hU⟩
              obtain ⟨s, hs, hsβ⟩ := hsplit X β hβ
              -- the refinement and the split constraints hold together at `β`
              set Call := Fin.append (N.unsafeInputConstraints X A b).1 s.2.1 with hCall
              set dall := Fin.append (N.unsafeInputConstraints X A b).2 s.2.2 with hdall
              have hall : β ∈ (HPolytope.ineqs Call dall).construct := by
                refine (HPolytope.mem_ineqs_iff).2 fun i => ?_
                refine Fin.addCases (fun i => ?_) (fun i => ?_) i
                · simpa [hCall, hdall, mulVec, Fin.append_left] using
                    (HPolytope.mem_ineqs_iff).1 hP i
                · simpa [hCall, hdall, mulVec, Fin.append_right] using hsβ i
              -- so `β` is in the piece's bounds (Prop. 3), which are not empty
              set Bβ := ConZonotope.fourierMotzkinIter Call dall iterFM with hBβ
              have hbox : ∀ j, Bβ.inf j ≤ β j ∧ β j ≤ Bβ.sup j :=
                ConZonotope.fourierMotzkinIter_outer _ _ iterFM β hβ hall
              have hpiece : aux_piece X (N.unsafeInputConstraints X A b) s iterFM = some
                  ⟨X.h, X.c + ∑ j, ((Bβ.inf j + Bβ.sup j) / 2) • X.G j,
                    fun j => ((Bβ.sup j - Bβ.inf j) / 2) • X.G j⟩ := by
                simp only [aux_piece]
                rw [← hCall, ← hdall, ← hBβ,
                  if_neg (not_exists.2 fun j => not_lt.2 ((hbox j).1.trans (hbox j).2))]
              exact hv' h _ (List.mem_append_right _ (List.mem_filterMap.2 ⟨s, hs, hpiece⟩)) _
                (aux_mem_rescale X _ _ β hbox) hU
            · exact hv' h X (List.mem_append_left _ hX) x hx hU
          · obtain ⟨⟨X, hX, hx⟩, hU⟩ := hf' x h
            rcases List.mem_append.1 hX with hX | hX
            · exact ⟨⟨X, List.mem_cons_of_mem _ hX, hx⟩, hU⟩
            · -- a piece lies in its set
              obtain ⟨s, -, hs⟩ := List.mem_filterMap.1 hX
              exact ⟨⟨Xi, List.mem_cons_self .., aux_piece_subset Xi _ s iterFM X hs hx⟩, hU⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
