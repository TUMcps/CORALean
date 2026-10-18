module

public import CORALean.ContSet.Interval.Float.Theorems.LeSound
public import CORALean.ContSet.Interval.Float.Theorems.MemPoint
public import CORALean.ContSet.Interval.Float.Theorems.MinusOuter
public import CORALean.ContSet.Interval.Float.Theorems.MtimesOuter
public import CORALean.ContSet.PolyZonotope.Float.Operations.InnerTest
public import CORALean.ContSet.PolyZonotope.Float.Theorems.InnerStepSubsetImage
public import CORALean.ContSet.PolyZonotope.Float.Theorems.PointBoxOuter
public import CORALean.ContSet.PolyZonotope.Float.Theorems.PrecondRegularInjective

@[expose] public section

/-!
# `innerTest` proves an inner box

When `innerTest` returns `true`, every point of `Y` is the dependent point at some factor vector
of `X`. The loop's answer is `true` only at a pass whose `innerStep` was accepted with
`u1_ ∈ U1_ ⊆ U1`, which `innerStep_subset_image` turns into the inclusion; what that needs of the
set-up is that `C` is injective (`precondRegular_injective`), that `x_` lies in `X` and `X_` off
`ind`, and that `b` holds `C(y - f(x_))` (`pointBox_outer`, `mtimes_outer`, `minus_outer`).
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

theorem PolyZonotope.innerTest_subset_image (pZ : PolyZonotope (Vec 𝕋 n))
    (X X₀ : Interval (Vec 𝕋 pZ.p)) (Y : Interval (Vec 𝕋 n)) (ind : Fin n ↪ Fin pZ.p)
    (M C : Mat 𝕋 n n) (iter : ℕ) (h : PolyZonotope.innerTest pZ X X₀ Y ind M C iter = true) :
    Y.construct ⊆ (PolyZonotope.nominal pZ).point '' X.construct := by -- --- PROOF ---
  unfold PolyZonotope.innerTest at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨hC, hsel⟩, hit⟩ := h
  -- `x_` in `X` and `X_` off `ind`
  have hxc : ∀ k, (∀ i, ind i ≠ k) → (toReal (X.inf k) ≤ toReal (Interval.center X₀ k) ∧
      toReal (Interval.center X₀ k) ≤ toReal (X.sup k)) ∧
      (toReal (X₀.inf k) ≤ toReal (Interval.center X₀ k) ∧
      toReal (Interval.center X₀ k) ≤ toReal (X₀.sup k)) := by
    intro k hk
    have h := List.all_eq_true.mp hsel k (List.mem_finRange k)
    have hany : ((List.finRange n).any fun i => decide (ind i = k)) = false :=
      List.any_eq_false.mpr fun i _ hi => hk i (of_decide_eq_true hi)
    simp only [hany, Bool.false_or, Bool.and_eq_true] at h
    exact ⟨⟨toReal_le_of_le h.1.1.1, toReal_le_of_le h.1.1.2⟩,
      ⟨toReal_le_of_le h.1.2, toReal_le_of_le h.2⟩⟩
  -- `C(y - f(x_))` in `b`
  have hb : ∀ y ∈ Y.construct, Matrix.mulVec (toRealMat C)
      (y - (PolyZonotope.nominal pZ).point (toRealVec (Interval.center X₀))) ∈
        ((Interval.mtimes C Y).minus (Interval.mtimes C (PolyZonotope.pointBox pZ
          (Interval.point (Interval.center X₀))))).materialise.construct := by
    intro y hy
    rw [Interval.materialise_eq]
    have hCy := Interval.mtimes_outer C Y ⟨y, hy, rfl⟩
    have hCf := Interval.mtimes_outer C _ ⟨_, PolyZonotope.pointBox_outer pZ _
      (Interval.mem_point (Interval.center X₀)), rfl⟩
    rw [Matrix.mulVec_sub]
    exact Interval.minus_outer _ _ (Set.sub_mem_sub hCy hCf)
  -- the answer stays unknown, or `false`, until a pass accepts
  refine Function.Iterate.rec
    (fun s : Interval (Vec 𝕋 n) × Option 𝕋 × Option 𝕋 × Option Bool => s.2.2.2 = some true →
      Y.construct ⊆ (PolyZonotope.nominal pZ).point '' X.construct)
    (fun h0 => by cases h0) ?_ iter hit
  clear hit
  intro s ih hst
  obtain ⟨U, d₁, d₂, st⟩ := s
  cases st with
  | some r => exact ih hst
  | none =>
    -- the contraction test reduced, the guard is an `if` on `U1_ ⊆ U1`
    cases d₁ <;> cases d₂ <;> dsimp only at hst <;> split at hst <;> (try cases hst) <;>
      rename_i hguard <;> split at hst <;> (try cases hst) <;> rename_i t ht <;>
      split at hst <;> (try cases hst) <;>
      exact PolyZonotope.innerStep_subset_image pZ X X₀ Y ind C
        (PolyZonotope.precondRegular_injective hC) _ hxc _ hb U
        (Interval.le_subset hguard.2) (Option.some.inj hst) _ ht (by assumption)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
