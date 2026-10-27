module

public import CORALean.ContSet.Conversion.Real.Operations.PolyZonotope_to_Zonotope
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FinCases
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.Linarith
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-!
# `PolyZonotope.containsExactCora1D`

`contains(pZ, p, 'exact')` of CORA's `@polyZonotope/contains_.m` for a point `p` and a
one-dimensional `pZ` with a generator (so the center-only branch, l. 172, is not taken). The
`'exact'` method returns at once into `aux_exactContainment` (ll. 100-102), which asks
`representsa_(pZ,'zonotope',1e-12)` (l. 184). For `n = 1` that answers `true` whatever `pZ`
is (`@polyZonotope/representsa_.m` l. 128: `res = n == 1 || aux_isZonotope(pZ,tol)`), with
`S = zonotope(pZ)` (`zonotopeEven`, which agrees with CORA here: no exponent column is zero), an
outer enclosure only, and `contains_` of that zonotope decides (l. 186).

# CORA's exact `contains` for a 1-D polynomial zonotope uses its zonotope enclosure

`pZ = polyZonotope(0, [1 1], [], [1 2])` is `{α + α² : |α| ≤ 1} = [-1/4, 2]`, while
`zonotope(pZ)` is `0.5 + [-1,1] + [-0.5,0.5] = [-1, 2]`. `contains(pZ, -0.5, 'exact')`
returns `true`, yet `-0.5 ∉ pZ`, since `α² + α + 1/2 = (α + 1/2)² + 1/4 > 0`.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* CORA's exact test accepts a point outside the set
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- The model: CORA's code as printed, kept only to be refuted.
/-- The verdict of `contains(pZ, p, 'exact')` for `n = 1`. -/
noncomputable def PolyZonotope.containsExactCora1D (pZ : PolyZonotope (Vec ℝ 1))
    (p : Vec ℝ 1) : Prop :=
  let Z := pZ.zonotopeEven        -- 184. [isZonotope, Z] = representsa_(pZ,'zonotope',1e-12)
  p ∈ Z.construct                 -- 186. contains_(Z,S,method,tol,0,false,false)


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.containsExactCora1D_counterexample : -- --- CONCL ---
    let PZ : PolyZonotope (Vec ℝ 1) := ⟨1, 2, 0, 0, ![![1], ![1]], ![![1, 2]], Fin.elim0⟩
    PolyZonotope.containsExactCora1D PZ ![-1 / 2] ∧
      (![-1 / 2] : Vec ℝ 1) ∉ PZ.construct := by -- --- PROOF ---
  intro PZ
  constructor
  · -- the enclosure is `1/2 + β₀ + β₁/2`: take `β = (-1, 0)`
    refine ⟨![-1, 0], ?_, ?_⟩
    · intro j
      fin_cases j
      · show |(-1 : ℝ)| ≤ 1
        norm_num
      · show |(0 : ℝ)| ≤ 1
        norm_num
    · simp [PZ, PolyZonotope.zonotopeEven, PolyZonotope.evenWeight, Fin.sum_univ_succ,
        Fin.append, Fin.addCases]
      erw [Fin.sum_univ_two]
      simp
      funext i
      fin_cases i
      norm_num
  · rintro ⟨a, β, ha, -, hx⟩
    have h := congrFun hx 0
    simp [PZ, PolyZonotope.monomial, Fin.sum_univ_two] at h
    nlinarith [sq_nonneg (a 0 + 1 / 2)]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
