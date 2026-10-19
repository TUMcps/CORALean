module

public import CORALean.NN.Layers.Operations.FindRegionLoop
public import CORALean.NN.Layers.Theorems.FindRegionLeftFits
public import CORALean.NN.Layers.Theorems.FindRegionRightFits

@[expose] public section

/-!
# The loop leaves nothing uncovered
The invariant of CORA's `while l < u`: every point outside `(l, u)` lies in a region already
found, or in the fixed outer regions `ext` (CORA's start and end polynomials). A left region
`[l, l']` moves `l` to `l'` and a right region `[u', u]` moves `u` to `u'`; the loop ends at
`u ≤ l`, where every point is outside, and each region it adds encloses `σ` with error at most
the tolerance. The new regions are in front of the old, which stay.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A region `[l, b]` found next to the covered part `t ≤ l` extends it to `t ≤ b`. -/
theorem aux_cover_left {σ : ℝ → ℝ} {tol b l u : 𝕋} {r : RegionPoly 𝕋}
    (hr : r.Fits σ tol l b) (ext acc : List (RegionPoly 𝕋))
    (h : ∀ t, (t ≤ toReal l ∨ toReal u ≤ t) → ∃ q ∈ ext ++ acc, q.covers t) :
    ∀ t, (t ≤ toReal b ∨ toReal u ≤ t) → ∃ q ∈ ext ++ r :: acc, q.covers t := by -- --- PROOF ---
  intro t ht
  have hmono : ∀ q ∈ ext ++ acc, q ∈ ext ++ r :: acc := fun q hq => by
    simp only [List.mem_append, List.mem_cons] at hq ⊢
    tauto
  by_cases hl : t ≤ toReal l
  · obtain ⟨q, hq, hc⟩ := h t (Or.inl hl)
    exact ⟨q, hmono q hq, hc⟩
  · rcases ht with hb | hu
    · refine ⟨r, by simp, ?_, ?_⟩
      · intro x hx
        rw [hr.1] at hx
        obtain rfl := Option.some.inj hx
        exact (not_le.mp hl).le
      · intro x hx
        rw [hr.2.1] at hx
        obtain rfl := Option.some.inj hx
        exact hb
    · obtain ⟨q, hq, hc⟩ := h t (Or.inr hu)
      exact ⟨q, hmono q hq, hc⟩

/-- A region `[a, u]` found next to the covered part `u ≤ t` extends it to `a ≤ t`. -/
theorem aux_cover_right {σ : ℝ → ℝ} {tol a l u : 𝕋} {r : RegionPoly 𝕋}
    (hr : r.Fits σ tol a u) (ext acc : List (RegionPoly 𝕋))
    (h : ∀ t, (t ≤ toReal l ∨ toReal u ≤ t) → ∃ q ∈ ext ++ acc, q.covers t) :
    ∀ t, (t ≤ toReal l ∨ toReal a ≤ t) → ∃ q ∈ ext ++ r :: acc, q.covers t := by -- --- PROOF ---
  intro t ht
  have hmono : ∀ q ∈ ext ++ acc, q ∈ ext ++ r :: acc := fun q hq => by
    simp only [List.mem_append, List.mem_cons] at hq ⊢
    tauto
  by_cases hu : toReal u ≤ t
  · obtain ⟨q, hq, hc⟩ := h t (Or.inr hu)
    exact ⟨q, hmono q hq, hc⟩
  · rcases ht with hl | ha
    · obtain ⟨q, hq, hc⟩ := h t (Or.inl hl)
      exact ⟨q, hmono q hq, hc⟩
    · refine ⟨r, by simp, ?_, ?_⟩
      · intro x hx
        rw [hr.1] at hx
        obtain rfl := Option.some.inj hx
        exact ha
      · intro x hx
        rw [hr.2.1] at hx
        obtain rfl := Option.some.inj hx
        exact (not_le.mp hu).le


-- =======================================  MAIN THEOREM  ======================================= --

/-- The regions the loop returns enclose `σ` within the tolerance, keep the old ones and, with
`ext`, cover the line. -/
theorem findRegionLoop_cover {σ : ℝ → ℝ} {F : (o : ℕ) → PolyRelaxation 𝕋 o}
    (hF : ∀ o, (F o).Sound σ) (order : ℕ) (tol : 𝕋) (ext : List (RegionPoly 𝕋)) : -- --- CONCL ---
    ∀ (fuel : ℕ) (l u : 𝕋) (acc res : List (RegionPoly 𝕋)),
      (∀ r ∈ acc, r.Encloses σ ∧ toReal r.err ≤ toReal tol) →
      (∀ t, (t ≤ toReal l ∨ toReal u ≤ t) → ∃ r ∈ ext ++ acc, r.covers t) →
      findRegionLoop F order tol fuel l u acc = some res →
      (∀ r ∈ res, r.Encloses σ ∧ toReal r.err ≤ toReal tol) ∧ (∀ r ∈ acc, r ∈ res) ∧
        (∀ t, ∃ r ∈ ext ++ res, r.covers t) := by -- --- PROOF ---
  intro fuel
  induction fuel with
  | zero =>
      intro l u acc res hacc hcov h
      simp only [findRegionLoop] at h
      split_ifs at h with hle
      obtain rfl := Option.some.inj h
      have hul := toReal_le_of_le hle
      refine ⟨hacc, fun r hr => hr, fun t => ?_⟩
      refine hcov t ?_
      by_cases ht : t ≤ toReal l
      exacts [Or.inl ht, Or.inr (hul.trans (not_le.mp ht).le)]
  | succ fuel ih =>
      intro l u acc res hacc hcov h
      -- the loop ends at once, or finds a left region first
      unfold findRegionLoop at h
      split_ifs at h with hle
      · obtain rfl := Option.some.inj h
        have hul := toReal_le_of_le hle
        refine ⟨hacc, fun r hr => hr, fun t => ?_⟩
        refine hcov t ?_
        by_cases ht : t ≤ toReal l
        exacts [Or.inl ht, Or.inr (hul.trans (not_le.mp ht).le)]
      · -- a left region `[l, l']` extends the covered part to `l'`
        cases hL : findRegionLeft F order tol l (fuel + 1) u with
        | none => rw [hL] at h; simp at h
        | some p =>
            obtain ⟨rL, l'⟩ := p
            rw [hL] at h
            dsimp only at h
            have hfL := findRegionLeft_fits hF order tol l _ _ _ _ hL
            have haccL : ∀ r ∈ rL :: acc, r.Encloses σ ∧ toReal r.err ≤ toReal tol := by
              intro r hr
              rcases List.mem_cons.mp hr with rfl | hr
              · exact ⟨hfL.2.2.1, hfL.2.2.2⟩
              · exact hacc r hr
            have hcovL := aux_cover_left hfL ext acc hcov
            -- either `l'` reached `u`, or a right region follows
            split_ifs at h with hle'
            · obtain rfl := Option.some.inj h
              have hul := toReal_le_of_le hle'
              refine ⟨haccL, fun r hr => List.mem_cons_of_mem _ hr, fun t => hcovL t ?_⟩
              by_cases ht : t ≤ toReal l'
              exacts [Or.inl ht, Or.inr (hul.trans (not_le.mp ht).le)]
            · -- the right region `[u', u]` extends it to `u'`, and `ih` runs on the rest
              cases hR : findRegionRight F order tol u (fuel + 1) l' with
              | none => rw [hR] at h; simp at h
              | some q =>
                  obtain ⟨rR, u'⟩ := q
                  rw [hR] at h
                  dsimp only at h
                  have hfR := findRegionRight_fits hF order tol u _ _ _ _ hR
                  have haccR : ∀ r ∈ rR :: rL :: acc,
                      r.Encloses σ ∧ toReal r.err ≤ toReal tol := by
                    intro r hr
                    rcases List.mem_cons.mp hr with rfl | hr
                    · exact ⟨hfR.2.2.1, hfR.2.2.2⟩
                    · exact haccL r hr
                  have hcovR := aux_cover_right hfR ext (rL :: acc) hcovL
                  obtain ⟨h1, h2, h3⟩ := ih l' u' (rR :: rL :: acc) res haccR
                    (fun t ht => by
                      have := hcovR t ht
                      simpa [List.append_assoc] using this) h
                  exact ⟨h1, fun r hr => h2 r (by simp [hr]), h3⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
