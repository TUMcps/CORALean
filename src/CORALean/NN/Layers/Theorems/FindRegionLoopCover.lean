module

public import CORALean.NN.Layers.Operations.FindRegionLoop

@[expose] public section

/-!
# The loop leaves nothing uncovered
The invariant of CORA's `while l < u`: every point outside `(l, u)` lies in a region already
found, or in the fixed outer regions `ext` (CORA's start and end polynomials). A left region
`[l, l']` moves `l` to `l'` and a right region `[u', u]` moves `u` to `u'`; the loop ends at
`u ≤ l`, where every point is outside, and each region it adds encloses `σ` with error at most
the tolerance. The new regions are in front of the old, which stay.

## Inputs
* `σ` – activation function
* `F` – polynomial relaxations by order
* `order` – polynomial order
* `tol` – error tolerance
* `ext` – regions already covering the outside

## Hypotheses
* `hF` – every relaxation is sound for the activation

## Conclusion
* the loop's regions enclose the activation and cover the line
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

section
variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋]

/-- The relaxation's region on `[l, u]` fits, given its error is at most the tolerance's. -/
private theorem RegionPoly.aux_ofRelaxation_fits {σ : ℝ → ℝ} {m : ℕ} {R : PolyRelaxation 𝕋 m}
    (hR : R.Encloses σ) {tol l u : 𝕋} (h : toReal (R.error l u) ≤ toReal tol) :
    (RegionPoly.step_ofRelaxation R l u).Fits σ tol l u :=
  ⟨rfl, rfl, fun _ ht => hR.sound (ht.1 l rfl) (ht.2 u rfl), h⟩

end


/-- The loop's result fits `[l, u]` if the fit it starts from does. -/
private theorem aux_lowerRegionOrder_fits {σ : ℝ → ℝ} {F : (o : ℕ) → PolyRelaxation 𝕋 o}
    (hF : ∀ o, (F o).Encloses σ) (tol l u : 𝕋) : -- --- CONCL ---
    ∀ (k : ℕ) (cur : RegionPoly 𝕋), cur.Fits σ tol l u →
      (step_lowerRegionOrder F tol l u k cur).Fits σ tol l u := by -- --- PROOF ---
  intro k
  induction k with
  | zero => exact fun _ h => h
  | succ k ih =>
      intro cur hcur
      unfold step_lowerRegionOrder
      split_ifs with h
      · exact ih _ (RegionPoly.aux_ofRelaxation_fits (hF k)
          (le_of_lt (toReal_lt_of_ltStrict h)))
      · exact hcur


/-- A returned left region fits `[l, u']`. -/
private theorem aux_findRegionLeft_fits {σ : ℝ → ℝ} {F : (o : ℕ) → PolyRelaxation 𝕋 o}
    (hF : ∀ o, (F o).Encloses σ) (order : ℕ) (tol l : 𝕋) : -- --- CONCL ---
    ∀ (fuel : ℕ) (ui : 𝕋) (r : RegionPoly 𝕋) (u' : 𝕋),
      step_findRegionLeft F order tol l fuel ui = some ⟨r, u'⟩ → r.Fits σ tol l u'
        := by -- --- PROOF ---
  intro fuel
  induction fuel with
  | zero => intro _ _ _ h; simp [step_findRegionLeft] at h
  | succ fuel ih =>
      intro ui r u' h
      unfold step_findRegionLeft at h
      dsimp only at h
      split_ifs at h with hle hlt
      · obtain ⟨rfl, rfl⟩ := RegionPoly.Found.mk.inj (Option.some.inj h)
        exact aux_lowerRegionOrder_fits hF tol l ui order _
          (RegionPoly.aux_ofRelaxation_fits (hF order) (SoundFloatArithmetic.toReal_le_of_le hle))
      · exact ih _ r u' h


/-- A returned right region fits `[l', u]`. -/
private theorem aux_findRegionRight_fits {σ : ℝ → ℝ} {F : (o : ℕ) → PolyRelaxation 𝕋 o}
    (hF : ∀ o, (F o).Encloses σ) (order : ℕ) (tol u : 𝕋) : -- --- CONCL ---
    ∀ (fuel : ℕ) (li : 𝕋) (r : RegionPoly 𝕋) (l' : 𝕋),
      step_findRegionRight F order tol u fuel li = some ⟨r, l'⟩ →
        r.Fits σ tol l' u := by -- --- PROOF ---
  intro fuel
  induction fuel with
  | zero => intro _ _ _ h; simp [step_findRegionRight] at h
  | succ fuel ih =>
      intro li r l' h
      unfold step_findRegionRight at h
      dsimp only at h
      split_ifs at h with hle hlt
      · obtain ⟨rfl, rfl⟩ := RegionPoly.Found.mk.inj (Option.some.inj h)
        exact RegionPoly.aux_ofRelaxation_fits (hF order) (SoundFloatArithmetic.toReal_le_of_le hle)
      · exact ih _ r l' h


/-- A region `[l, b]` found next to the covered part `t ≤ l` extends it to `t ≤ b`. -/
private theorem aux_cover_left {σ : ℝ → ℝ} {tol b l u : 𝕋} {r : RegionPoly 𝕋}
    (hr : r.Fits σ tol l b) (ext acc : List (RegionPoly 𝕋))
    (h : ∀ t, (t ≤ toReal l ∨ toReal u ≤ t) → ∃ q ∈ ext ++ acc, q.covers t) : -- --- CONCL ---
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
private theorem aux_cover_right {σ : ℝ → ℝ} {tol a l u : 𝕋} {r : RegionPoly 𝕋}
    (hr : r.Fits σ tol a u) (ext acc : List (RegionPoly 𝕋))
    (h : ∀ t, (t ≤ toReal l ∨ toReal u ≤ t) → ∃ q ∈ ext ++ acc, q.covers t) : -- --- CONCL ---
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
    (hF : ∀ o, (F o).Encloses σ) (order : ℕ) (tol : 𝕋)
    (ext : List (RegionPoly 𝕋)) : -- --- CONCL ---
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
        cases hL : step_findRegionLeft F order tol l (fuel + 1) u with
        | none => rw [hL] at h; simp at h
        | some p =>
            obtain ⟨rL, l'⟩ := p
            rw [hL] at h
            dsimp only at h
            have hfL := aux_findRegionLeft_fits hF order tol l _ _ _ _ hL
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
              cases hR : step_findRegionRight F order tol u (fuel + 1) l' with
              | none => rw [hR] at h; simp at h
              | some q =>
                  obtain ⟨rR, u'⟩ := q
                  rw [hR] at h
                  dsimp only at h
                  have hfR := aux_findRegionRight_fits hF order tol u _ _ _ _ hR
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
