module

public import CORALean.ContSet.StarSet.Real.Instances
public import CORALean.ContSet.StarSet.Real.Operations.Basic
public import CORALean.ContSet.Interval.Real.Interval

@[expose] public section

/-!
# One ReLU neuron on a star set

CORA's `nnReLULayer/evaluateConZonotopeNeuron` after the bounds `l`, `u` of the neuron are
known: nothing to do if `0 ≤ l`; the neuron's row cleared if `u ≤ 0`; otherwise the triangle
relaxation, with the neuron's value replaced by a new factor `β` bounded by three constraints
`-β ≤ 0`, `c_j + G_j α - β ≤ 0` and `β ≤ u/(u-l) (c_j + G_j α - l)`, which are the rows
`[0 -1]`, `[G_j -1]` and `[-u/(u-l) G_j 1]` against `0`, `-c_j` and `u/(u-l) (c_j - l)` of CORA's
`C` and `d`. The new factor is bounded by `[0, u]`. The old rows gain a zero in the new column.
The predicate is built by its own operations (#174): `LinPred.snoc` adds the factor and
`LinPred.addRows` the three rows (`StarSet.LinPred.mem_snoc_iff`,
`StarSet.LinPred.mem_addRows_iff`).
The rows use the center and generators before the neuron's row is cleared, as CORA's do.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def StarSet.reluNeuron {n : ℕ} (s : StarSet StarSet.LinPred n) (j : Fin n)
    (b : Interval ℝ) : StarSet StarSet.LinPred n :=
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
      pred := (s.pred.snoc 0 u).addRows
        [(Fin.snoc (α := fun _ => ℝ) 0 (-1), 0),
         (Fin.snoc (α := fun _ => ℝ) (s.G j) (-1), -s.c j),
         (Fin.snoc (α := fun _ => ℝ) (fun k => -(u / (u - l)) * s.G j k) 1,
          u / (u - l) * (s.c j - l))] }

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
