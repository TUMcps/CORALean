module

public import CORALean.ContSet.StarSet.Real.Instances
public import CORALean.ContSet.HPolytope.Real.Operations.Ineqs
public import CORALean.ContSet.HPolytope.Real.Operations.Intersection
public import CORALean.ContSet.HPolytope.Real.Operations.Lift
public import CORALean.ContSet.Interval.Real.Operations.Basic
public import CORALean.ContSet.Interval.Real.Interval

@[expose] public section

/-!
# One ReLU neuron on a star set

CORA's `nnReLULayer/evaluateConZonotopeNeuron` after the bounds `l`, `u` of the neuron are
known: nothing to do if `0 ≤ l`; the neuron's row cleared if `u ≤ 0`; otherwise the triangle
relaxation, with the neuron's value replaced by a new factor `β` bounded by three constraints
`-β ≤ 0`, `c_j + G_j α - β ≤ 0` and `β ≤ u/(u-l) (c_j + G_j α - l)`, which are the rows
`[0 -1]`, `[G_j -1]` and `[-u/(u-l) G_j 1]` against `0`, `-c_j` and `u/(u-l) (c_j - l)` of CORA's
`C` and `d`. The new factor's box `[0, u]` is appended to the coefficient box. The predicate is
built by `HPolytope`'s own operations (#174): `lift_` gives the old rows a zero in the new column
and `intersection` adds the three rows, `HPolytope.ineqs`.
The rows use the center and generators before the neuron's row is cleared, as CORA's do.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def StarSet.reluNeuron {n : ℕ} (s : StarSet ℋ𝒫 n) (j : Fin n)
    (b : Interval ℝ) : StarSet ℋ𝒫 n :=
  let l := b.inf
  let u := b.sup
  if 0 ≤ l then s
  else if u ≤ 0 then
    { s with c := Function.update s.c j 0, G := Function.update s.G j 0 }
  else
    { m := s.m + 1
      c := Function.update s.c j 0
      G := fun i => Fin.snoc (α := fun _ => ℝ) (if i = j then 0 else s.G i)
        (if i = j then 1 else 0)
      dom := s.dom.append ⟨fun _ => 0, fun _ => u⟩
      pred := (s.pred.lift_ Fin.castSucc).intersection (HPolytope.ineqs
        ![Fin.snoc (α := fun _ => ℝ) 0 (-1), Fin.snoc (α := fun _ => ℝ) (s.G j) (-1),
          Fin.snoc (α := fun _ => ℝ) (fun k => -(u / (u - l)) * s.G j k) 1]
        ![0, -s.c j, u / (u - l) * (s.c j - l)]) }

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
