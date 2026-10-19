module

public import CORALean.ContSet.Interval.Float.Interval
public import CORALean.ContSet.StarSet.Float.Operations.Basic
public import CORALean.Global.Float.SoundFloatArithmetic
public import CORALean.NN.Layers.Operations.StarSetFloatChordGuard
public import CORALean.NN.Layers.Operations.StarSetFloatChordRow

@[expose] public section

/-!
# One ReLU neuron on a float star set

`Real.StarSet.reluNeuron` after the bounds `b = (l, u)` of the neuron are known. Nothing to do if
`0 ≤ l`; the row cleared if `u ≤ 0`; otherwise the neuron's value is replaced by a new factor
`β` in `[0, max(u, 0)]` under `-β ≤ 0`, `c_j + G_j α - β ≤ 0` and, when `StarSet.chordGuard`
certifies it, the chord row `StarSet.chordRow`. The comparisons are the scalar's `le`,
which certifies `≤` only, so a bound that is not known to be on one side takes the last branch,
whose rows hold wherever the bounds do. The bounds are those of the nominal part, as
`StarSet.rowBounds` gives them; the error box is made symmetric at `j` by `StarSet.aux_reluError`
in every branch, the ReLU being `1`-Lipschitz. The predicate is built by its own operations
(#174), `LinPred.snoc` for the factor and `LinPred.addRows` for the rows, as in the exact layer,
which the float `snoc` reads as (`StarSet.LinPred.nominal_snoc`).
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       12-October-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Float Float.FloatOps

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The error box with coordinate `j` made symmetric about `0`. -/
def StarSet.aux_reluError (e : Interval (Vec 𝕋 n)) (j : Fin n) : Interval (Vec 𝕋 n) :=
  let r := maximum (neg (e.inf j)) (e.sup j)
  ⟨Function.update e.inf j (neg r), Function.update e.sup j r⟩


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The ReLU step on neuron `j` of a float star set, given its bounds. -/
def StarSet.reluNeuron (s : StarSet 𝕋 n) (j : Fin n) (b : Interval 𝕋) :
    StarSet 𝕋 n :=
  let e := StarSet.aux_reluError s.I_error j
  if le zero b.inf then { s with I_error := e }
  else if le b.sup zero then
    { s with c := Function.update s.c j zero, G := Function.update s.G j (fun _ => zero),
             I_error := e }
  else
    { m := s.m + 1
      c := Function.update s.c j zero
      G := fun i => Fin.snoc (α := fun _ => 𝕋) (if i = j then (fun _ => zero) else s.G i)
        (if i = j then one else zero)
      pred := (s.pred.snoc zero (maximum b.sup zero)).addRows
        ([(Fin.snoc (α := fun _ => 𝕋) (fun _ => zero) (neg one), zero),
          (Fin.snoc (α := fun _ => 𝕋) (s.G j) (neg one), neg (s.c j))] ++
          (if StarSet.chordGuard b then [s.chordRow j b] else []))
      I_error := e }

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
