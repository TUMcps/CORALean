module

public import CORALean.ContDynamics.LinearSys.Operations.VerifyBoxOutFloat
public import CORALean.Global.StepOf

@[expose] public section

/-!
# `LinearSys.verifyGirardReduceFloat`, CORA's reduction of the input's solution

CORA's `aux_reduce` in `priv_reach_adaptive`: the new generators `e^{At_k} PU` that are aligned
with an axis (Girard's metric `Σᵢ |gᵢ| - maxᵢ |gᵢ|` is `0`) join the box, the others are appended.
Then the generators in increasing order of the metric (stable) join the box while `2 ‖Σ ĝ‖₂`, `ĝ`
the magnitude with its largest entry set to `0`, stays within the budget; here compared squared,
`4 ‖Σ ĝ‖₂² ≤ budget²`, so no square root is taken. The choice is tuning; whichever generators move,
the box encloses them (`LinearSys.verifyBoxOutFloat`).

## Inputs
* `P` – float generators so far
* `new` – float new generators
* `b` – float radius of the box
* `budget` – float budget of the reduction

## Output
* the generators that stay and the box
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- ------------------------------------------  STEPS  ------------------------------------------- --

/-- Girard's metric `Σᵢ |gᵢ| - maxᵢ |gᵢ|`, the sum from the first entry. -/
@[step_of LinearSys.verifyGirardReduceFloat]
def LinearSys.step_verifyGirardFloat (g : Vec 𝕋 n) : 𝕋 :=
  subUp ((List.finRange n).foldl (fun acc i => addUp acc (absolute (g i))) zero)
    ((List.finRange n).foldl (fun acc i => maximum acc (absolute (g i))) zero)

/-- `|g|` with its first largest entry set to `0`. -/
@[step_of LinearSys.verifyGirardReduceFloat]
def LinearSys.step_verifyGirardHatFloat (g : Vec 𝕋 n) : Vec 𝕋 n :=
  let idx := (List.finRange n).foldl (fun (k : Option (Fin n)) i => match k with
    | none => some i
    | some k => if le (absolute (g i)) (absolute (g k)) then some k else some i) none
  fun i => if idx = some i then zero else absolute (g i)

/-- How many of the generators, in the given order, join the box: the longest prefix whose
`4 ‖Σ ĝ‖₂²` is at most `budget²`. -/
@[step_of LinearSys.verifyGirardReduceFloat]
def LinearSys.step_verifyGirardCountFloat (budget : 𝕋) :
    List (Vec 𝕋 n) → Vec 𝕋 n → ℕ → ℕ
  | [], _, k => k
  | g :: gs, S, k =>
    let S' := (Interval.point fun i =>
      addUp (S i) (LinearSys.step_verifyGirardHatFloat g i)).materialise.sup
    let ω := mulUp (nsmulUp 4 one) (sumUp fun i => mulUp (S' i) (S' i))   -- 4 ‖Σ ĝ‖₂²
    if le ω (mulUp budget budget) then LinearSys.step_verifyGirardCountFloat budget gs S' (k + 1)
    else k


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The axis-aligned new generators into the box, the others appended, then those of smallest
metric into the box within the budget. -/
def LinearSys.verifyGirardReduceFloat (P new : List (Vec 𝕋 n)) (b : Vec 𝕋 n) (budget : 𝕋) :
    List (Vec 𝕋 n) × Vec 𝕋 n :=
  let axis := LinearSys.verifyBoxOutFloat                              -- metric 0: into the box
    (new.map fun g => (g, !le (LinearSys.step_verifyGirardFloat g) zero)) b
  let P₁ := P ++ axis.1
  let gir := P₁.map LinearSys.step_verifyGirardFloat
  let order := (List.range P₁.length).mergeSort fun i j =>             -- by the metric, stable
    le (gir.getD i zero) (gir.getD j zero)
  let k := LinearSys.step_verifyGirardCountFloat budget
    (order.filterMap fun i => P₁[i]?) (fun _ => zero) 0
  let out := order.take k
  LinearSys.verifyBoxOutFloat (P₁.zipIdx.map fun g => (g.1, !out.contains g.2)) axis.2

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
