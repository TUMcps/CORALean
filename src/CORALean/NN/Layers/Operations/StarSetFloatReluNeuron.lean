import CORALean.NN.Layers.Operations.StarSetFloatChordGuard
import CORALean.NN.Layers.Operations.StarSetFloatChordRow

/-!
# One ReLU neuron on a float star set

`StarSet.reluNeuron` after the bounds `b = (l, u)` of the neuron are known. Nothing to do if
`0 ≤ l`; the row cleared if `u ≤ 0`; otherwise the neuron's value is replaced by a new factor
`β` in `[0, max(u, 0)]` under `-β ≤ 0`, `c_j + G_j α - β ≤ 0` and, when `StarSetFloat.chordGuard`
certifies it, the chord row `StarSetFloat.chordRow`. The comparisons are the scalar's `le`,
which certifies `≤` only, so a bound that is not known to be on one side takes the last branch,
whose rows hold wherever the bounds do.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The ReLU step on neuron `j` of a float star set, given its bounds. -/
def StarSetFloat.reluNeuron (s : StarSetFloat 𝕋 n) (j : Fin n) (b : 𝕋 × 𝕋) :
    StarSetFloat 𝕋 n :=
  if le zero b.1 then s
  else if le b.2 zero then
    { s with c := Function.update s.c j zero, G := Function.update s.G j (fun _ => zero) }
  else
    { m := s.m + 1
      c := Function.update s.c j zero
      G := fun i => Fin.snoc (α := fun _ => 𝕋) (if i = j then (fun _ => zero) else s.G i)
        (if i = j then one else zero)
      cons := s.cons.map (fun r => (Fin.snoc (α := fun _ => 𝕋) r.1 zero, r.2)) ++
        [(Fin.snoc (α := fun _ => 𝕋) (fun _ => zero) (neg one), zero),
         (Fin.snoc (α := fun _ => 𝕋) (s.G j) (neg one), neg (s.c j))] ++
        (if StarSetFloat.chordGuard b then [s.chordRow j b] else [])
      l := Fin.snoc (α := fun _ => 𝕋) s.l zero
      u := Fin.snoc (α := fun _ => 𝕋) s.u (maximum b.2 zero) }

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
