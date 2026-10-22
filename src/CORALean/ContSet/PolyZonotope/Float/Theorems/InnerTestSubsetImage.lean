module

public import CORALean.ContSet.Interval.Float.Theorems.LeSound
public import CORALean.ContSet.Interval.Float.Theorems.MemPoint
public import CORALean.ContSet.Interval.Float.Theorems.MinusOuter
public import CORALean.ContSet.Interval.Float.Theorems.MtimesOuter
public import CORALean.ContSet.PolyZonotope.Float.Operations.InnerTest
public import CORALean.ContSet.PolyZonotope.Float.Theorems.InnerStepSubsetImage
public import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
public import CORALean.ContSet.PolyZonotope.Float.Operations.PointBox
public import CORALean.ContSet.PolyZonotope.Float.Theorems.MonoBoxOuter
public import CORALean.ContSet.PolyZonotope.Real.Operations.Point
public import CORALean.Global.Float.SoundFloatArithmetic
public import CORALean.Global.MulVecInjectiveOfResidual
public import CORALean.ContSet.PolyZonotope.Float.Theorems.PointBoxOuter

@[expose] public section

/-!
# `innerTest` proves an inner box

When `innerTest` returns `true`, every point of `Y` is the dependent point at some factor vector
of `X`. The loop's answer is `true` only at a pass whose `innerStep` was accepted with
`u1_ ∈ U1_ ⊆ U1`, which `innerStep_subset_image` turns into the inclusion; what that needs of the
set-up is that `C` is injective (`aux_precondRegular_injective`), that `x_` lies in `X` and `X_` off
`ind`, and that `b` holds `C(y - f(x_))` (`pointBox_outer`, `mtimes_outer`, `minus_outer`).

## Inputs
* `pZ` – polynomial zonotope
* `X` – factor box
* `X₀` – inner factor box
* `Y` – target box
* `ind` – selected factor indices
* `M` – midpoint Jacobian
* `C` – approximate inverse Jacobian
* `iter` – number of iterations

## Hypotheses
* `h` – the test returns true

## Conclusion
* the target box lies in the image of the factor box
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `aux_precondRegular` certifies an injective preconditioner. -/
theorem PolyZonotope.aux_precondRegular_injective {M C : Mat 𝕋 n n}
    (h : PolyZonotope.aux_precondRegular M C = true) : -- --- CONCL ---
    Function.Injective (toRealMat C).mulVec := by -- --- PROOF ---
  refine mulVec_injective_of_residual (toRealMat M) (toRealMat C) fun i => ?_
  have hi := List.all_eq_true.mp h i (List.mem_finRange i)
  refine lt_of_le_of_lt ?_ (lt_of_lt_of_eq (toReal_lt_of_ltStrict hi) (toReal_one (𝕋 := 𝕋)))
  refine le_trans (Finset.sum_le_sum fun j _ => ?_) (sum_le_sumUp _)
  -- the entry of `M C` between its roundings, and `1ᵢⱼ` read exactly
  have hlo : toReal (matMulDown M C i j) ≤ (toRealMat M * toRealMat C) i j := dotDown_le _ _
  have hhi : (toRealMat M * toRealMat C) i j ≤ toReal (matMulUp M C i j) := le_dotUp _ _
  have hδ : toReal (if i = j then (one : 𝕋) else zero) = (1 : Matrix (Fin n) (Fin n) ℝ) i j := by
    by_cases hij : i = j
    · rw [if_pos hij, hij, Matrix.one_apply_eq, toReal_one]
    · rw [if_neg hij, Matrix.one_apply_ne hij, toReal_zero]
  rw [toReal_maximum, toReal_absolute, toReal_absolute, Matrix.sub_apply]
  refine abs_le_max_abs_abs ?_ ?_
  · exact le_trans (subDown_le_sub _ _) (by rw [hδ]; linarith)
  · exact le_trans (by rw [hδ]; linarith) (sub_le_subUp _ _)


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.innerTest_subset_image (pZ : PolyZonotope (Vec 𝕋 n))
    (X X₀ : Interval (Vec 𝕋 pZ.p)) (Y : Interval (Vec 𝕋 n)) (ind : Fin n ↪ Fin pZ.p)
    (M C : Mat 𝕋 n n) (iter : ℕ)
    (h : PolyZonotope.innerTest pZ X X₀ Y ind M C iter = true) : -- --- CONCL ---
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
        (PolyZonotope.aux_precondRegular_injective hC) _ hxc _ hb U
        (Interval.le_subset hguard.2) (Option.some.inj hst) _ ht (by assumption)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
