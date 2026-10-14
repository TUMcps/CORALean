module

public import CORALean.ContSet.Interval.Real.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval
public import CORALean.ContSet.ContSet.ContSet

@[expose] public section

/-!
# `Zonotope.minkDiffOuterScalingCora`, CORA's `minkDiff(Z, I, 'outer:scaling')`

CORA's `@zonotope/minkDiff.m` with method `'outer:scaling'` and an interval subtrahend `I`: the
subtrahend is turned into `zonotope(I)` (l. 104), and for a full-dimensional minuend outside
`n = 2` (where l. 120 forces `'exact'`) l. 148-150 call `aux_minkDiffOuterInterval` (l. 311-326).
That scales the minuend about its own centre by `1 - radSub ./ radMin` through `enlarge`
(`@contSet/enlarge.m`: `S - c`, `.* factor`, `+ c`) and never subtracts the subtrahend's centre.
One `let` per line of the source; the `representsa_` guard (l. 314) only throws.

# CORA's `minkDiff(Z, I, 'outer:scaling')` is not an outer approximation

For the unit cube `Z = zonotope(zeros(3,1), eye(3))` and `I = interval(zeros(3,1), ones(3,1))`,
`Z ⊖ I = [-1, 0]³`. `'outer:scaling'` (`Zonotope.minkDiffOuterScalingCora`) scales `Z` by
`1 - 0.5/1 = 0.5` about its centre `0` and returns `[-0.5, 0.5]³`, ignoring `I`'s centre `0.5`:
the point `(-1, -1, -1)` of the difference is missing. `n = 3`, as at `n = 2` CORA forces
`'exact'`; `Z` is full-dimensional and `I` has generators, so no earlier branch returns.

## References

* [1] `contSet/@zonotope/minkDiff.m`, CORA, ll. 99-104, 117-120, 148-150, 311-326.
* [2] `contSet/@contSet/enlarge.m`, CORA.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- The model: CORA's code as printed, kept only to be refuted.
/-- [1]'s `'outer:scaling'` at an interval subtrahend: the minuend scaled coordinatewise about its
own centre by `1 - radSub ./ radMin`. -/
noncomputable def Zonotope.minkDiffOuterScalingCora (minuend : Zonotope (Vec ℝ n))
    (I : Interval (Vec ℝ n)) : Zonotope (Vec ℝ n) :=
  -- l. 104: `subtrahend = zonotope(subtrahend)`
  let subtrahend : Zonotope (Vec ℝ n) := I.zonotope
  -- l. 321: `radMin = rad(interval(minuend))`
  let radMin : Vec ℝ n := minuend.interval.radius
  -- l. 322: `radSub = rad(interval(subtrahend))`
  let radSub : Vec ℝ n := subtrahend.interval.radius
  -- l. 323: `scale = 1 - radSub./radMin`
  let scale : Vec ℝ n := fun i => 1 - radSub i / radMin i
  -- l. 324, `enlarge(minuend, scale)` [2]: `c = center(S)`
  let c : Vec ℝ n := minuend.c
  -- [2]: `S = S - c`
  let S₁ : Zonotope (Vec ℝ n) := ⟨minuend.h, minuend.c - c, minuend.G⟩
  -- [2]: `S = S .* factor`, i.e. `diag(factor) * S`
  let S₂ : Zonotope (Vec ℝ n) :=
    ⟨S₁.h, fun i => scale i * S₁.c i, fun j i => scale i * S₁.G j i⟩
  -- [2]: `S = S + c`
  ⟨S₂.h, S₂.c + c, S₂.G⟩

end CORALean.Real

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.minkDiffOuterScalingCora_not_outer :
    let Z : Zonotope (Vec ℝ 3) := ⟨3, 0, fun j i => if i = j then 1 else 0⟩
    let I : Interval (Vec ℝ 3) := ⟨0, 1⟩
    ¬ minkowskiDiff Z.construct I.construct ⊆
      (Z.minkDiffOuterScalingCora I).construct := by -- --- PROOF ---
  intro Z I h
  -- `(-1, -1, -1) + y ∈ Z` for every `y ∈ [0, 1]³`: coefficients `y - 1`
  have hmem : (fun _ => -1 : Vec ℝ 3) ∈ minkowskiDiff Z.construct I.construct := by
    intro y hy
    refine ⟨fun j => -1 + y j, fun j => ?_, ?_⟩
    · have hj : 0 ≤ y j ∧ y j ≤ 1 := hy j
      rw [abs_le]
      constructor <;> linarith [hj.1, hj.2]
    · funext i
      fin_cases i <;> simp [Z, Fin.sum_univ_three]
  -- the result is `[-0.5, 0.5]³`: coordinate `0` is `β₀ / 2 ≠ -1`
  obtain ⟨β, hβ, hx⟩ := h hmem
  have hof : ∀ f : Fin 3 → ℝ, (Entrywise.ofEntry f : Vec ℝ 3) = f := fun _ => rfl
  have hent : ∀ (f : Fin 3 → ℝ) (i : Fin 3), Entrywise.entry (f : Vec ℝ 3) i = f i :=
    fun _ _ => rfl
  have h0 := congrFun hx 0
  simp [Zonotope.minkDiffOuterScalingCora, Zonotope.interval, Interval.radius,
    Interval.zonotope, Fin.sum_univ_three, Z, I, hof, hent] at h0
  have hb := abs_le.mp (hβ (by exact (0 : Fin 3)))
  norm_num at h0
  linarith [hb.1, hb.2]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
