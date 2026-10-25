module

public import CORALean.ContSet.Interval.Real.Interval
public import Mathlib.Data.Matrix.Basis
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Finset.Fold
public import Mathlib.Order.Lattice

@[expose] public section

/-!
# `ConZonotope.fourierMotzkinBounds`

[1, Prop. 3]: bounds of the constrained hypercube `P = ⟨C, d⟩_H ∩ [β̲₀, β̄₀]` without a linear
program, after Fourier-Motzkin elimination. Row `i` isolates the factor `j`,
`C(i,j) β(j) ≤ d(i) - C(i,·) Σ_{∖{j}} β`, the rest bounded below over the box; a negative
`C(i,j)` gives a lower bound, a positive one an upper bound, and the tightest of each, with the
box's own, are the result. `C⁻` is `½(C - |C|)`, the entries `≤ 0`, which the proof's
`min_{β̃ ∈ [β̲₀, β̄₀]} C(i,·) Σ_{∖{j}} β̃ = C⁺(i,·) Σ_{∖{j}} β̲₀ + C⁻(i,·) Σ_{∖{j}} β̄₀` needs; [1]
writes `A⁻ ∈ ℝ_{≥0}`. CORA: `aux_fourierMotzkinApproximation` in
`conZonotope/approximateBoundsWithGPU`.

## Inputs
* `C` – constraint matrix
* `d` – constraint offset
* `B` – initial bounds `[β̲₀, β̄₀]`

## Output
* the bounds `[β̲, β̄]` of `P`

## References

* [1] L. Koller, T. Ladner and M. Althoff. "Out of the Shadows: Exploring a Latent Space for Neural
      Network Verification". International Conference on Learning Representations, 2026.
-/

-- Authors:       Claude Opus 5.5
-- Written:       21-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {p q : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Prop. 3]: `β̲(j) = max ({C̲(i,j) | C(i,j) < 0} ∪ {β̲₀(j)})`, `β̄(j)` the `min` over
`C(i,j) > 0`, with `C̲(i,j) := (d(i) - C⁺(i,·) Σ_{∖{j}} β̲₀ - C⁻(i,·) Σ_{∖{j}} β̄₀) / C(i,j)`. -/
noncomputable def ConZonotope.fourierMotzkinBounds (C : Mat ℝ p q) (d : Vec ℝ p)
    (B : Interval (Vec ℝ q)) : Interval (Vec ℝ q) :=
  -- 1. `C⁺ = ½(C + |C|)` and `C⁻ = ½(C - |C|)`
  let Cplus : Mat ℝ p q := fun i j => (C i j + |C i j|) / 2
  let Cminus : Mat ℝ p q := fun i j => (C i j - |C i j|) / 2
  -- 2. `Σ_{∖{j}} := I_q - e_j e_jᵀ`
  let excl : Fin q → Mat ℝ q q := fun j => 1 - Matrix.single j j 1
  -- 3. `C̲(i,j) := (d(i) - C⁺(i,·) Σ_{∖{j}} β̲₀ - C⁻(i,·) Σ_{∖{j}} β̄₀) / C(i,j)`
  let Clow : Mat ℝ p q := fun i j =>
    (d i - ((Cplus * excl j) *ᵥ B.inf) i - ((Cminus * excl j) *ᵥ B.sup) i) / C i j
  -- 4. `β̲(j) = max ({C̲(i,j) | i ∈ [p] : C(i,j) < 0} ∪ {β̲₀(j)})`
  let βlo : Vec ℝ q := fun j =>
    (Finset.univ.filter fun i => C i j < 0).fold max (B.inf j) fun i => Clow i j
  -- 5. `β̄(j) = min ({C̲(i,j) | i ∈ [p] : C(i,j) > 0} ∪ {β̄₀(j)})`
  let βhi : Vec ℝ q := fun j =>
    (Finset.univ.filter fun i => 0 < C i j).fold min (B.sup j) fun i => Clow i j
  ⟨βlo, βhi⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
