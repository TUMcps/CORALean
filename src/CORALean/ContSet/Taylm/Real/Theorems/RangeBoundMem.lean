module

public import CORALean.ContSet.Taylm.Real.Operations.RangeBound
public import CORALean.ContSet.Taylm.Real.Theorems.BoundsMem
public import CORALean.ContSet.Taylm.Real.Theorems.CodeEvalEncloses
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfCons
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfNil
public import CORALean.ContSet.Conversion.Real.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Theorems.IntervalTaylmContains
public import CORALean.ContSet.Conversion.Real.Theorems.IntervalTaylmOuter

@[expose] public section

/-!
# Range bounding encloses the range

[1, Alg. 1]'s output: whenever it returns a bound, `f` takes its values over `D` inside it. A
point of the box is `mid + rad·t` for some `t` in the normalized box (`taylm_contains`), the
identity models enclose that map, [1, Thm. 2] carries the enclosure through the code list, and
`bounds` contains every value of an enclosed function.

## Inputs
* `m` – number of variables
* `e` – code list
* `D` – domain box
* `N` – expansion order
* `x` – point

## Hypotheses
* `hx` – point lies in the domain box

## Conclusion
* the range enclosure contains the code list's value at the point

## References

* [1] K. Makino and M. Berz. "Taylor Models and Other Validated Functional Inclusion Methods".
      International Journal of Pure and Applied Mathematics, 2003.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.rangeBound_mem {m : ℕ} {e : Taylm.CodeList ℝ m} {D : Interval (Vec ℝ m)} {N : ℕ}
    {x : Vec ℝ m} (hx : x ∈ D.construct) : -- --- CONCL ---
    ∀ b ∈ Taylm.rangeBound e D N,
      b.inf ≤ e.eval x ∧ e.eval x ≤ b.sup := by -- --- PROOF ---
  intro b (hb : Taylm.rangeBound e D N = some b)
  simp only [Taylm.rangeBound, Option.map_eq_some_iff] at hb
  obtain ⟨T, hT, rfl⟩ := hb
  have hE := Taylm.codeEval_encloses (fun i => Interval.taylm_outer D N i) e hT
  -- the point is the identity models' value at some `t` in the normalized box
  obtain ⟨t, ht, hxt⟩ := Interval.taylm_contains D N hx
  have hxi : (fun i => (D.inf i + D.sup i) / 2 + (D.sup i - D.inf i) / 2 * t i) = x := by
    funext i
    have := hxt i
    simp only [Interval.taylm, Taylm.poly, Taylm.polyOf_cons, Taylm.polyOf_nil,
      Taylm.monomial_zero, Taylm.monomial_single] at this
    linarith [this.1, this.2]
  have := Taylm.bounds_mem hE ht
  rwa [hxi] at this

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
