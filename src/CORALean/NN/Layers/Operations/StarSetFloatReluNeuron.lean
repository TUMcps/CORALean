module

public import CORALean.ContSet.Interval.Float.Interval
public import CORALean.ContSet.HPolytope.Float.Operations.Ineqs
public import CORALean.ContSet.HPolytope.Float.Operations.Lift
public import CORALean.ContSet.HPolytope.Float.Operations.StackRows
public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.StarSet.Float.StarSet
public import CORALean.Global.Float.SoundFloatArithmetic
public import CORALean.NN.Layers.Operations.StarSetFloatChordGuard
public import CORALean.NN.Layers.Operations.StarSetFloatChordRow
public import CORALean.Global.StepOf

@[expose] public section

/-!
# One ReLU neuron on a float star set

`Real.StarSet.reluNeuron` after the bounds `b = (l, u)` of the neuron are known. Nothing to do if `0
≤ l`; the row cleared if `u ≤ 0`; otherwise the neuron's value is replaced by a new factor `β` in
`[0, max(u, 0)]` under `-β ≤ 0`, `c_j + G_j α - β ≤ 0` and, when `StarSet.chordGuard` certifies it,
the chord row `StarSet.chordRow`. The comparisons are the scalar's `le`, which certifies `≤` only,
so a bound not known to be on one side takes the last branch, whose rows hold wherever the bounds
do. The error box is made symmetric at `j` by `StarSet.step_reluError` in every branch; the
predicate is built by `HPolytope`'s own operations (#174), as in the exact layer.

## Inputs
* `s` – float star set
* `j` – neuron index
* `b` – bounds of the neuron

## Output
* star set after the ReLU step on the neuron
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       12-October-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Float Float.FloatOps

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋] {n : ℕ}


-- ------------------------------------------  STEPS  ------------------------------------------- --

/-- The error box with coordinate `j` made symmetric about `0`. -/
@[step_of StarSet.reluNeuron]
def StarSet.step_reluError (e : Interval (Vec 𝕋 n)) (j : Fin n) : Interval (Vec 𝕋 n) :=
  let r := maximum (neg (e.inf j)) (e.sup j)
  ⟨Function.update e.inf j (neg r), Function.update e.sup j r⟩


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The ReLU step on neuron `j` of a float star set, given its bounds. -/
def StarSet.reluNeuron (s : StarSet 𝕋 n) (j : Fin n) (b : Interval 𝕋) :
    StarSet 𝕋 n :=
  let e := StarSet.step_reluError s.I_error j
  if le zero b.inf then { s with I_error := e }
  else if le b.sup zero then
    { s with c := Function.update s.c j zero, G := Function.update s.G j (fun _ => zero),
             I_error := e }
  else
    { m := s.m + 1
      c := Function.update s.c j zero
      G := fun i => Fin.snoc (α := fun _ => 𝕋) (if i = j then (fun _ => zero) else s.G i)
        (if i = j then one else zero)
      dom := s.dom.append ⟨fun _ => zero, fun _ => maximum b.sup zero⟩
      -- the old rows on the old factors, `-β ≤ 0`, `c_j + G_j α - β ≤ 0`, the chord if certified
      pred :=
        let base := (s.pred.lift_ Fin.castSucc).stackRows (HPolytope.ineqs
          ![Fin.snoc (α := fun _ => 𝕋) (fun _ => zero) (neg one),
            Fin.snoc (α := fun _ => 𝕋) (s.G j) (neg one)] ![zero, neg (s.c j)])
        if StarSet.chordGuard b then
          base.stackRows (HPolytope.ineqs ![(s.chordRow j b).1] ![(s.chordRow j b).2])
        else base
      I_error := e }

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
