module

public import CORALean.Specification.STL.Operations.FactorCheck
public import CORALean.Specification.STL.Theorems.FactorStepMem

@[expose] public section

/-!
# [1, Alg. 2] is sound: factors outside `L` satisfy the formula

Let `ξ j α` be the state at time `jΔt/2` of the trajectory with factors `α ∈ box`, in
`R̃(jΔt/2)` (`hR`), and in the unsafe factors of every `P_hjkl` it enters (`hU`, [1, Prop. 2]). If
`α` is in no polytope of `STL.factorCheck`, then for every `h` some `(j, k)` has `ξ j α` outside
all `P_hjkl`, which is `⋀_h ⋁_j ⋁_k (ξ ∉ ⋃_l P_hjkl)`: the trajectory satisfies [1, Eq. (12)]. The
claim of [1, Sec. 5] that `L = []` verifies the specification is the case where no `α` is in a
polytope, and of [1, Sec. 7.4] that the polytopes of `L` for `¬φ` hold the factors of all legal
behaviours, the contrapositive. Only the pairs of `STL.factorMeet` give this; see its zip reading.

## References

* [1] N. Kochdumper and S. Bak. "Fully Automated Verification of Linear Time-Invariant Systems
      against Signal Temporal Logic Specifications via Reachability Analysis". Nonlinear Analysis:
      Hybrid Systems, vol. 53, 2024, 101491.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {S X : Type}


-- =======================================  MAIN THEOREM  ======================================= --

theorem STL.factorCheck_sound (H J K : ℕ) (box : Set X) (R : ℕ → Set S)
    (P : ℕ → ℕ → ℕ → List (Set S)) (unsafeSet : ℕ → Set S → Set X)
    (meets : Set S → Set S → Bool) (isEmpty : Set X → Bool) (ξ : ℕ → X → S)
    (hR : ∀ j α, ξ j α ∈ R j) (hU : ∀ j α Pl, ξ j α ∈ Pl → α ∈ unsafeSet j Pl)
    (hmeets : ∀ A B, meets A B = false → A ∩ B = ∅) (hempty : ∀ v, isEmpty v = true → v = ∅)
    (α : X) (hα : α ∈ box)
    (hL : ∀ v ∈ STL.factorCheck H J K box R P unsafeSet meets isEmpty, α ∉ v) :
    ∀ h ≤ H, ∃ j ≤ J, ∃ k ≤ K, ∀ Pl ∈ P h j k, ξ j α ∉ Pl := by -- --- PROOF ---
  intro h hh
  by_contra hcon
  -- otherwise every `(j, k)` has a polytope that the trajectory enters
  have hcon' : ∀ j ≤ J, ∀ k ≤ K, ∃ Pl ∈ P h j k, ξ j α ∈ Pl := by
    intro j hj k hk
    by_contra hn
    exact hcon ⟨j, hj, k, hk, fun Pl hPl hin => hn ⟨Pl, hPl, hin⟩⟩
  let jk := (List.range (J + 1)).flatMap fun j => (List.range (K + 1)).map fun k => (j, k)
  -- `α` stays in a polytope along the loop over `(j, k)`
  have gen : ∀ (l : List (ℕ × ℕ)), (∀ q ∈ l, q.1 ≤ J ∧ q.2 ≤ K) → ∀ V : List (Set X),
      (∃ v ∈ V, α ∈ v) → ∃ v ∈ l.foldl (fun V (q : ℕ × ℕ) =>
        STL.factorStep (R q.1) (P h q.1 q.2) (unsafeSet q.1) meets isEmpty V) V, α ∈ v := by
    intro l
    induction l with
    | nil => intro _ V hV; exact hV
    | cons a t ih =>
      intro hl V hV
      refine ih (fun q hq => hl q (List.mem_cons_of_mem _ hq)) _ ?_
      obtain ⟨hj, hk⟩ := hl a (List.mem_cons_self ..)
      exact STL.exists_mem_factorStep _ _ _ meets isEmpty V α (ξ a.1 α) (hR _ _) (hU a.1 α)
        hmeets hempty (hcon' a.1 hj a.2 hk) hV
  have hjk : ∀ q ∈ jk, q.1 ≤ J ∧ q.2 ≤ K := by
    intro q hq
    simp only [jk, List.mem_flatMap, List.mem_map, List.mem_range] at hq
    obtain ⟨j, hj, k, hk, rfl⟩ := hq
    exact ⟨Nat.lt_succ_iff.mp hj, Nat.lt_succ_iff.mp hk⟩
  -- and the polytope of conjunction `h` is appended to `L`, which then holds `α`
  have fold : ∀ (l : List ℕ) (L : List (Set X)),
      (∃ v ∈ L, α ∈ v) ∨ (∃ h ∈ l, ∃ v ∈ jk.foldl (fun V (q : ℕ × ℕ) =>
        STL.factorStep (R q.1) (P h q.1 q.2) (unsafeSet q.1) meets isEmpty V) [box], α ∈ v) →
      ∃ v ∈ l.foldl (fun L h => L ++ jk.foldl (fun V (q : ℕ × ℕ) =>
        STL.factorStep (R q.1) (P h q.1 q.2) (unsafeSet q.1) meets isEmpty V) [box]) L, α ∈ v := by
    intro l
    induction l with
    | nil => intro L hL'; rcases hL' with hL' | ⟨h, hh, _⟩; exact hL'; simp at hh
    | cons a t ih =>
      intro L hL'
      -- the first conjunction's polytopes are appended, then the rest are by induction
      refine ih _ ?_
      rcases hL' with ⟨v, hv, hαv⟩ | ⟨h', hh', hex⟩
      · exact Or.inl ⟨v, List.mem_append_left _ hv, hαv⟩
      · rcases List.mem_cons.mp hh' with rfl | hh''
        · obtain ⟨v, hv, hαv⟩ := hex
          exact Or.inl ⟨v, List.mem_append_right _ hv, hαv⟩
        · exact Or.inr ⟨h', hh'', hex⟩
  obtain ⟨v, hv, hαv⟩ := fold (List.range (H + 1)) [] (Or.inr ⟨h, List.mem_range.mpr
    (Nat.lt_succ_of_le hh), gen jk hjk [box] ⟨box, List.mem_singleton_self _, hα⟩⟩)
  exact hL v hv hαv

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
