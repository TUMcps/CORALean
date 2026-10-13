module

public import CORALean.ContSet.Conversion.Float.PolyZonotope_to_Interval
public import CORALean.ContSet.PolyZonotope.Float.Operations.ContainsSetApprox
public import CORALean.ContSet.PolyZonotope.Float.Theorems.IndepFactorsPointMem
public import CORALean.ContSet.PolyZonotope.Float.Theorems.InnerGeneralSubsetImage
public import CORALean.ContSet.PolyZonotope.Float.Theorems.SplitLongestGenAllCover

@[expose] public section

/-!
# `containsSetApprox` proves containment

Through every round, each point of `S` lies in `pZ` or in a piece still on the list: a piece
dropped was proved inside `pZ` (its interval enclosure, `interval_contains`, is in the image of
the unit box under `indepFactors`' point map, `innerGeneral_subset_image`, which stays in the
nominal set, `indepFactors_point_mem`, and the error box holds `0`), and a piece split is
covered by its pieces (`splitLongestGenAll_cover`). `true` means the list
ended empty.
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.containsSetApprox_sound (pZ S : PolyZonotope (Vec 𝕋 n))
    (guess : Interval (Vec 𝕋 n) → Interval (Vec 𝕋 (pZ.p + pZ.q)))
    (inv : {k : ℕ} → Mat 𝕋 k k → Mat 𝕋 k k) (iter fuel : ℕ)
    (h : PolyZonotope.containsSetApprox pZ S guess inv iter fuel = true) :
    S.construct ⊆ pZ.construct := by -- --- PROOF ---
  unfold PolyZonotope.containsSetApprox at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨herr, -⟩, hit⟩ := h
  -- `0` is in the error box
  have h0 : ∀ i, toReal (pZ.err.inf i) ≤ 0 ∧ 0 ≤ toReal (pZ.err.sup i) := fun i => by
    have h := List.all_eq_true.mp herr i (List.mem_finRange i)
    simp only [Bool.and_eq_true] at h
    exact ⟨le_of_le_of_eq (toReal_le_of_le h.1) toReal_zero,
      le_of_eq_of_le toReal_zero.symm (toReal_le_of_le h.2)⟩
  -- a piece the test accepts is inside `pZ`
  have hproven : ∀ T : PolyZonotope (Vec 𝕋 n), PolyZonotope.innerGeneral pZ.indepFactors
      ⟨fun _ => neg one, fun _ => one⟩ (guess T.interval) T.interval inv iter = true →
        T.construct ⊆ pZ.construct := by
    intro T hT x hx
    obtain ⟨a, ha, hpt⟩ := PolyZonotope.innerGeneral_subset_image _ _ _ _ inv iter hT
      (PolyZonotope.interval_contains T hx)
    have hab : ∀ k, |a k| ≤ 1 := fun k => by
      have h1 : toReal (neg one : 𝕋) ≤ a k := (ha k).1
      have h2 : a k ≤ toReal (one : 𝕋) := (ha k).2
      rw [toReal_neg, toReal_one] at h1
      rw [toReal_one] at h2
      exact abs_le.mpr ⟨h1, h2⟩
    have hm := PolyZonotope.indepFactors_point_mem pZ hab
    rw [hpt] at hm
    exact ⟨x, hm, 0, h0, add_zero _⟩
  -- every point of `S` is in `pZ` or in a piece still listed, and `true` ends the list empty
  revert hit
  refine (Function.Iterate.rec
    (fun s : List (PolyZonotope (Vec 𝕋 n)) × ℕ × ℕ × Option Bool =>
      (∀ x ∈ S.construct, x ∈ pZ.construct ∨ ∃ T ∈ s.1, x ∈ T.construct) ∧
        (s.2.2.2 = some true → S.construct ⊆ pZ.construct))
    (⟨fun x hx => Or.inr ⟨S, List.mem_singleton_self S, hx⟩, fun h => by cases h⟩) ?_ fuel).2
  · rintro ⟨L, cnt, splits, st⟩ ⟨hcov, hdone⟩
    cases st with
    | some r => exact ⟨hcov, hdone⟩
    | none =>
      -- the new list still covers what the old one did
      have hcov' : ∀ x ∈ S.construct, x ∈ pZ.construct ∨
          ∃ T ∈ L.flatMap (fun T => if PolyZonotope.innerGeneral pZ.indepFactors
            ⟨fun _ => neg one, fun _ => one⟩ (guess T.interval) T.interval inv iter then []
            else T.splitLongestGenAll), x ∈ T.construct := by
        intro x hx
        rcases hcov x hx with h | ⟨T, hT, hxT⟩
        · exact Or.inl h
        · by_cases hp : PolyZonotope.innerGeneral pZ.indepFactors
              ⟨fun _ => neg one, fun _ => one⟩ (guess T.interval) T.interval inv iter = true
          · exact Or.inl (hproven T hp hxT)
          · obtain ⟨T', hT', hx'⟩ := PolyZonotope.splitLongestGenAll_cover T hxT
            exact Or.inr ⟨T', List.mem_flatMap.mpr ⟨T, hT, by rw [if_neg hp]; exact hT'⟩, hx'⟩
      -- the answer, once given, is whether that list is empty
      dsimp only
      split_ifs <;> refine ⟨hcov', fun h x hx => ?_⟩ <;>
        first
        | cases h
        | (simp only [Option.some.injEq, List.isEmpty_iff] at h
           rcases hcov' x hx with h' | ⟨T, hT, -⟩
           · exact h'
           · exact absurd hT (List.eq_nil_iff_forall_not_mem.mp h T))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
