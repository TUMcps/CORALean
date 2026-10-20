module

public import CORALean.Global.JacobiSlice
public import CORALean.Global.Float.SoundFloatArithmetic
public import CORALean.ContSet.PolyZonotope.Float.Operations.SliceBox

@[expose] public section

/-!
# The slice through a point lies in `sliceBox`

For `v` in `U`, `jacobiSlice xc ind v` reads `v` at the coordinates `ind` and `xc` elsewhere,
so it lies in `sliceBox X₀ ind U` once `ind` is injective and `xc` lies in `X₀` at the other
coordinates.

## Inputs
* `X₀` – factor box
* `ind` – selected factor indices
* `U` – replacement box
* `xc` – center point
* `v` – point of the replacement box

## Hypotheses
* `hind` – the indices are injective
* `hv` – point lies in the replacement box
* `hxc` – center lies in the box outside the selected factors

## Conclusion
* the slice through the point lies in the slice box
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n p : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.jacobiSlice_mem_sliceBox (X₀ : Interval (Vec 𝕋 p)) {ind : Fin n → Fin p}
    (hind : Function.Injective ind) (U : Interval (Vec 𝕋 n)) {xc : Vec ℝ p} {v : Vec ℝ n}
    (hv : v ∈ U.construct)
    (hxc : ∀ k, (∀ i, ind i ≠ k) → toReal (X₀.inf k) ≤ xc k ∧ xc k ≤ toReal (X₀.sup k))
    : -- --- CONCL ---
    jacobiSlice xc ind v ∈ (PolyZonotope.sliceBox X₀ ind U).construct := by -- --- PROOF ---
  intro k
  show toReal ((PolyZonotope.sliceBox X₀ ind U).inf k) ≤ jacobiSlice xc ind v k ∧
    jacobiSlice xc ind v k ≤ toReal ((PolyZonotope.sliceBox X₀ ind U).sup k)
  simp only [PolyZonotope.sliceBox]
  cases h : (List.finRange n).find? fun i => decide (ind i = k) with
  | some i =>
    -- `k` is `ind i`, where the slice reads `v`
    have hik : ind i = k := of_decide_eq_true (List.find?_some (p := fun i => decide (ind i = k)) h)
    rw [← hik, jacobiSlice_apply_ind xc hind v i]
    exact hv i
  | none =>
    -- no coordinate of `U` sits at `k`, so the slice reads `xc`
    have hk : ∀ i, ind i ≠ k := fun i hi =>
      absurd (decide_eq_true hi) (List.find?_eq_none.mp h i (List.mem_finRange i))
    rw [jacobiSlice_apply_of_ne xc v hk]
    exact hxc k hk

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
