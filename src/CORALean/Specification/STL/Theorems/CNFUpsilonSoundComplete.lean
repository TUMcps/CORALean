import CORALean.Specification.STL.Theorems.CNFSatToFormula
import CORALean.Specification.STL.Theorems.CNFSatUpsilon
import CORALean.Specification.STL.Theorems.BlocksDisjoint
import CORALean.Specification.STL.Theorems.FinRepConstOnBlock
import CORALean.Specification.STL.Theorems.ForallExistsIffExistsForall
import CORALean.Specification.STL.Theorems.ForallFinalsOrGlobalsIff
import CORALean.Specification.STL.Theorems.ForallTraceSetSatIff

/-!
# `Υ` is sound and complete for c-divisible reach sequences

[1, Lemma 2]: `R ⊨ᵣ Υ(φ) ⇔ C(R) ⊨ₜ φ` for `φ = ⋀ᵢ ⋁ⱼ X_c^j (φᵢⱼ ∨ ϱᵢⱼ)` and every finitely
represented `R` with breakpoints in `ℕc`. Three conditions the paper leaves implicit: every `R t`
is non-empty, `c > 0`, and the `j` of the branches of a clause are distinct, for `X_c^j φ ∨ X_c^j ψ`
is not `X_c^j (φ ∨ ψ)` at the level of `Υ`.

## References

* [1] H. Roehm, J. Oehlerking, T. Heinz and M. Althoff. "STL Model Checking of Continuous and
      Hybrid Systems". ATVA, LNCS 9938, pp. 412-427, 2016.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped NNReal

variable {X : Type}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The window part of a branch holds of every trace iff the set `S` does, by the interval lemma. -/
theorem STL.aux_forall_window {c : ℝ≥0} (hc : 0 < c) {T : Finset ℝ≥0} {R : ℝ≥0 → Set X}
    (hne : ∀ t, (R t).Nonempty) (hT : ReachSequence.FinRep T R)
    (hdiv : ReachSequence.CDivisible c T) (b : STL.Branch X) :
    (∀ ξ ∈ ReachSequence.traceSet R,
      (∃ ϱ ∈ b.K, ∃ t, 0 < t ∧ t < c ∧ ϱ.Sat (ξ (t + b.j * c))) ∨
        ∃ ϱ ∈ b.L, ∀ t, 0 < t → t < c → ϱ.Sat (ξ (t + b.j * c))) ↔
      (∀ r ∈ R (c / 2 + b.j * c), (Pform.bigOr b.K).Sat r) ∨
        ∃ ϱ ∈ b.L, ∀ r ∈ R (c / 2 + b.j * c), (ϱ.or (Pform.bigOr b.K)).Sat r := by -- --- PROOF ---
  refine ReachSequence.forall_finals_or_globals_iff hne hc (fun x hx₁ hx₂ => ?_) b.K b.L
  -- the midpoint of the window and `x` lie in the same open block
  refine ReachSequence.eq_of_cDivisible hT hdiv b.j ⟨hx₁, hx₂⟩ ⟨?_, ?_⟩
  · exact lt_add_of_pos_left _ (half_pos hc)
  · rw [add_comm (c / 2) _]; exact add_lt_add_of_le_of_lt le_rfl (half_lt_self hc)

/-- One clause: some branch holds of every trace iff some branch holds outright. -/
theorem STL.aux_clause {c : ℝ≥0} (hc : 0 < c) {T : Finset ℝ≥0} {R : ℝ≥0 → Set X}
    (hne : ∀ t, (R t).Nonempty) (hT : ReachSequence.FinRep T R)
    (hdiv : ReachSequence.CDivisible c T) (clause : STL.Clause X)
    (hnd : (clause.map STL.Branch.j).Nodup) :
    (∀ ξ ∈ ReachSequence.traceSet R, ∃ b ∈ clause,
      ((∃ ϱ ∈ b.K, ∃ t, 0 < t ∧ t < c ∧ ϱ.Sat (ξ (t + b.j * c))) ∨
        ∃ ϱ ∈ b.L, ∀ t, 0 < t → t < c → ϱ.Sat (ξ (t + b.j * c))) ∨ b.ϱ.Sat (ξ (b.j * c))) ↔
    ∃ b ∈ clause, ((∀ r ∈ R (c / 2 + b.j * c), (Pform.bigOr b.K).Sat r) ∨
        ∃ ϱ ∈ b.L, ∀ r ∈ R (c / 2 + b.j * c), (ϱ.or (Pform.bigOr b.K)).Sat r) ∨
      ∀ r ∈ R (b.j * c), b.ϱ.Sat r := by -- --- PROOF ---
  classical
  refine ⟨fun h => ?_, ?_⟩
  · -- index every branch twice: by its window `(jc, jc + c)` and by its point `jc`
    let Tm : STL.Branch X × Bool → Set ℝ≥0 := fun p =>
      if p.2 then Set.Ioo (p.1.j * c) (p.1.j * c + c) else {p.1.j * c}
    let P : STL.Branch X × Bool → (ℝ≥0 → X) → Prop := fun p ξ =>
      if p.2 then (∃ ϱ ∈ p.1.K, ∃ t, 0 < t ∧ t < c ∧ ϱ.Sat (ξ (t + p.1.j * c))) ∨
        ∃ ϱ ∈ p.1.L, ∀ t, 0 < t → t < c → ϱ.Sat (ξ (t + p.1.j * c))
      else p.1.ϱ.Sat (ξ (p.1.j * c))
    -- every `Tm p` lies in the block `[jc, jc + c)`
    have hsub : ∀ p, Tm p ⊆ Set.Ico (p.1.j * c) (p.1.j * c + c) := by
      rintro ⟨b, i⟩ x hx
      cases i
      · obtain rfl : x = b.j * c := hx
        exact ⟨le_rfl, lt_add_of_pos_right _ hc⟩
      · exact Set.Ioo_subset_Ico_self hx
    have hpair : {p : STL.Branch X × Bool | p.1 ∈ clause}.Pairwise
        fun p q => Disjoint (Tm p) (Tm q) := by
      rintro ⟨b, i⟩ hb ⟨b', i'⟩ hb' hpq
      by_cases hj : b.j = b'.j
      · -- one branch, so the two Booleans differ
        obtain rfl : b = b' := List.inj_on_of_nodup_map hnd hb hb' hj
        cases i <;> cases i'
        · exact absurd rfl hpq
        · exact Set.disjoint_singleton_left.2 (fun hx => lt_irrefl _ hx.1)
        · exact Set.disjoint_singleton_right.2 (fun hx => lt_irrefl _ hx.1)
        · exact absurd rfl hpq
      · exact (ReachSequence.disjoint_blocks hj c).mono (hsub _) (hsub _)
    -- each part reads the trace only inside its own times
    have hloc : ∀ p ξ ξ', (∀ x ∈ Tm p, ξ x = ξ' x) → (P p ξ ↔ P p ξ') := by
      rintro ⟨b, i⟩ ξ ξ' hx
      cases i
      · have := hx (b.j * c) rfl
        simp only [P, Bool.false_eq_true, if_false]
        rw [this]
      · -- the window part reads the trace at the times `t + jc` with `0 < t < c`
        have hw : ∀ t, 0 < t → t < c → ξ (t + b.j * c) = ξ' (t + b.j * c) := fun t h₀ h₁ =>
          hx _ ⟨lt_add_of_pos_left _ h₀, by
            rw [add_comm (b.j * c) c]; exact add_lt_add_of_lt_of_le h₁ le_rfl⟩
        simp only [P, if_true]
        constructor
        · rintro (⟨ϱ, hϱ, t, h₀, h₁, hs⟩ | ⟨ϱ, hϱ, hall⟩)
          · exact Or.inl ⟨ϱ, hϱ, t, h₀, h₁, by rwa [← hw t h₀ h₁]⟩
          · exact Or.inr ⟨ϱ, hϱ, fun t h₀ h₁ => by rw [← hw t h₀ h₁]; exact hall t h₀ h₁⟩
        · rintro (⟨ϱ, hϱ, t, h₀, h₁, hs⟩ | ⟨ϱ, hϱ, hall⟩)
          · exact Or.inl ⟨ϱ, hϱ, t, h₀, h₁, by rwa [hw t h₀ h₁]⟩
          · exact Or.inr ⟨ϱ, hϱ, fun t h₀ h₁ => by rw [hw t h₀ h₁]; exact hall t h₀ h₁⟩
    -- a branch holds of each trace, so one of its two parts does
    have h' : ∀ ξ ∈ ReachSequence.traceSet R, ∃ p ∈ {p : STL.Branch X × Bool | p.1 ∈ clause},
        P p ξ := by
      intro ξ hξ
      obtain ⟨b, hb, hW | hQ⟩ := h ξ hξ
      · exact ⟨(b, true), hb, by simpa [P] using hW⟩
      · exact ⟨(b, false), hb, by simpa [P] using hQ⟩
    -- glue the counterexamples: one part holds of every trace
    obtain ⟨⟨b, i⟩, hb, hall⟩ := (ReachSequence.forall_exists_iff_exists_forall hne hpair hloc).1 h'
    cases i
    · refine ⟨b, hb, Or.inr ((ReachSequence.forall_traceSet_sat_iff hne _ b.ϱ).1 ?_)⟩
      simpa [P] using hall
    · exact ⟨b, hb, Or.inl ((STL.aux_forall_window hc hne hT hdiv b).1 (by simpa [P] using hall))⟩
  · rintro ⟨b, hb, hR | hR⟩ ξ hξ
    · exact ⟨b, hb, Or.inl ((STL.aux_forall_window hc hne hT hdiv b).2 hR ξ hξ)⟩
    · exact ⟨b, hb, Or.inr ((ReachSequence.forall_traceSet_sat_iff hne _ b.ϱ).2 hR ξ hξ)⟩


-- =======================================  MAIN THEOREM  ======================================= --

theorem STL.CNF.upsilon_sound_complete {c : ℝ≥0} (hc : 0 < c) {T : Finset ℝ≥0} {R : ℝ≥0 → Set X}
    (hne : ∀ t, (R t).Nonempty) (hT : ReachSequence.FinRep T R)
    (hdiv : ReachSequence.CDivisible c T) (cnf : STL.CNF X)
    (hnd : ∀ clause ∈ cnf, (clause.map STL.Branch.j).Nodup) :
    (cnf.upsilon c).Sat R ↔
      (cnf.toFormula c).HoldsOn (ReachSequence.traceSet R) := by -- --- PROOF ---
  rw [STL.CNF.sat_upsilon c cnf R (hne 0) fun _ _ _ _ => hne _]
  simp only [STL.Formula.HoldsOn, STL.CNF.sat_toFormula]
  -- the traces and the clauses can be quantified in either order
  refine ⟨fun h ξ hξ clause hcl => ?_, fun h clause hcl => ?_⟩
  · exact (STL.aux_clause hc hne hT hdiv clause (hnd clause hcl)).2 (h clause hcl) ξ hξ
  · exact (STL.aux_clause hc hne hT hdiv clause (hnd clause hcl)).1 fun ξ hξ => h ξ hξ clause hcl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
