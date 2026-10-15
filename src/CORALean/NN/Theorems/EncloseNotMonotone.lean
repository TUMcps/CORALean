module

public import CORALean.ContSet.Conversion.Float.Instances
public import CORALean.ContSet.Interval.Real.Instances
public import CORALean.Global.Float.Instances.Real.Theorems.Basic
public import CORALean.NN.Layers.Operations.Activation

@[expose] public section

/-!
# `Layer.enclose` is not monotone in its input set

`Relaxation` lets `slope` depend on the box however it likes — deliberately, since
`Relaxation.tighter` [1] picks per box and `Relaxation.ofDeriv`'s `lam` is free inside its bracket.
That freedom also lets a relaxation be sloppy on a narrow box and exact on a wide one, so a small
set's loose enclosure can escape a large set's tight one: `enclose` is not monotone in its input
set. The witness relaxes the zero function, slope `1` below width `2` and `0` at or above it;
enclosing `[0, 1]` reaches `1`, enclosing the containing `[0, 3]` only `0`.

This is not a defect to fix, but it costs a proof strategy: a network reduced at several layers
cannot be reached by composing single-layer containments through `enclose`, the way
`NeuronMergingNetworkOuter.lean` does for one layer. Each of #69's Alg. 2/Thm. 1 and #68's Prop. 2
needs its own induction over the network instead.

`enclose_outer` is unaffected: every layer's `enclose` still contains the exact image of every
point in its input set. That is soundness at each point, which is a different property from
monotonicity in the set, and only the latter fails.

## References

* [1] `CORALean.Relaxation.tighter`.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet
open scoped CORALean.Real


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The zero function: cheap to relax at any slope, which is the freedom the
counterexample exploits. -/
def aux_encloseNotMonotone_sigma : ℝ → ℝ := fun _ => 0

/-- Slope `1` below width `2`, slope `0` at or above it. -/
noncomputable def aux_encloseNotMonotone_R : Relaxation ℝ where
  slope l u := if u - l < 2 then 1 else 0
  offset l u := if u - l < 2 then -(l + u) / 2 else 0
  error l u := if u - l < 2 then (u - l) / 2 else 0

/-- Both branches are sound: the deviation from the chosen line never exceeds half the box's
width. -/
theorem aux_encloseNotMonotone_R_sound :
    aux_encloseNotMonotone_R.Sound aux_encloseNotMonotone_sigma := by -- --- PROOF ---
  refine ⟨fun {l u t} hl hu => ?_⟩
  show |0 - ((if u - l < 2 then (1 : ℝ) else 0) * t + (if u - l < 2 then -(l + u) / 2 else 0))|
    ≤ (if u - l < 2 then (u - l) / 2 else 0)
  simp only [CORALean.Float.toReal_real] at hl hu
  split_ifs with h
  · -- narrow branch: `σ` is zero, so this is a midpoint-distance bound
    rw [abs_le]
    constructor <;> linarith
  · -- wide branch: slope, offset and error are all `0`, and so is `σ`
    simp

/-- The narrow box `[0, 1]`. -/
def aux_encloseNotMonotone_s : Real.Interval (Vec ℝ 1) := ⟨fun _ => 0, fun _ => 1⟩

/-- The wide box `[0, 3]`, which contains `aux_encloseNotMonotone_s`. -/
def aux_encloseNotMonotone_t : Real.Interval (Vec ℝ 1) := ⟨fun _ => 0, fun _ => 3⟩

theorem aux_encloseNotMonotone_subset :
    construct aux_encloseNotMonotone_s ⊆ construct aux_encloseNotMonotone_t := by
  intro x hx i
  have h1 : (0 : ℝ) ≤ x i := (hx i).1
  have h2 : x i ≤ (1 : ℝ) := (hx i).2
  exact ⟨h1, by show x i ≤ (3 : ℝ); linarith⟩

/-- At `ℝ`, the activation layer's propagation of a box is the box `mtimes` makes of the
diagonal slopes, plus the relaxation's box, rounded nowhere. -/
theorem aux_encloseNotMonotone_enclose (I : Real.Interval (Vec ℝ 1)) :
    (Layer.activation (S := ℐ𝒱) aux_encloseNotMonotone_R).enclose I
      = (Real.Interval.mtimes (Float.diagonalBlock fun i =>
          aux_encloseNotMonotone_R.slope (I.inf i) (I.sup i)) I).plus
          ⟨fun i => aux_encloseNotMonotone_R.offset (I.inf i) (I.sup i)
              - aux_encloseNotMonotone_R.error (I.inf i) (I.sup i),
            fun i => aux_encloseNotMonotone_R.offset (I.inf i) (I.sup i)
              + aux_encloseNotMonotone_R.error (I.inf i) (I.sup i)⟩ := by -- --- PROOF ---
  -- every rounding at `ℝ` is the exact operation, and both conversions are the identity
  show Real.Interval.plus _ ⟨fun i => _ + -_, fun i => _ + _⟩ = _
  simp only [sub_eq_add_neg]
  rfl

/-- The constant `1` vector lies in the narrow box's own propagation, `[-1, 1]`. -/
theorem aux_encloseNotMonotone_mem_s :
    (fun _ : Fin 1 => (1 : ℝ)) ∈ construct
      ((Layer.activation (S := ℐ𝒱)
        aux_encloseNotMonotone_R).enclose aux_encloseNotMonotone_s) := by -- --- PROOF ---
  rw [aux_encloseNotMonotone_enclose]
  intro i
  fin_cases i
  -- width `1`: slope `1`, offset `-1/2`, error `1/2`, so the coordinate spans `[-1, 1]`
  norm_num [Real.Interval.plus, Real.Interval.mtimes, Float.diagonalBlock,
    aux_encloseNotMonotone_R, aux_encloseNotMonotone_s, Entrywise.entry]

/-- The wide box's own propagation is the single point `0`: slope `0` drops every
dependence on the input, so nothing at `1` survives. -/
theorem aux_encloseNotMonotone_not_mem_t :
    (fun _ : Fin 1 => (1 : ℝ)) ∉ construct
      ((Layer.activation (S := ℐ𝒱)
        aux_encloseNotMonotone_R).enclose aux_encloseNotMonotone_t) := by -- --- PROOF ---
  rw [aux_encloseNotMonotone_enclose]
  intro hmem
  have h0 := hmem (0 : Fin 1)
  -- width `3`: slope, offset and error are all `0`, so the coordinate is the point `0`
  norm_num [Real.Interval.plus, Real.Interval.mtimes, Float.diagonalBlock,
    aux_encloseNotMonotone_R, aux_encloseNotMonotone_t, Entrywise.entry] at h0


-- =======================================  MAIN THEOREM  ======================================= --

/-- The zero-function relaxation above witnesses that no such law holds: `[0, 1]`
encloses past `1`, while its superset `[0, 3]` encloses only to `0`. -/
theorem Layer.enclose_not_monotone :
    ¬ ∀ {σ : ℝ → ℝ} (R : Relaxation ℝ), R.Sound σ → ∀ (s t : Real.Interval (Vec ℝ 1)),
        construct s ⊆ construct t →
          construct ((Layer.activation (S := ℐ𝒱) R).enclose s)
            ⊆ construct ((Layer.activation (S := ℐ𝒱)
              R).enclose t) := by -- --- PROOF ---
  intro h
  exact aux_encloseNotMonotone_not_mem_t
    (h aux_encloseNotMonotone_R aux_encloseNotMonotone_R_sound aux_encloseNotMonotone_s
      aux_encloseNotMonotone_t aux_encloseNotMonotone_subset aux_encloseNotMonotone_mem_s)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
