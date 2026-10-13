import CORALean.ContDynamics.LinearSysDT.Operations.Reach
import CORALean.ContSet.Zonotope.Float.Instances
import CORALean.Examples.Bench.Config
import CORALean.Examples.Bench.Rational

/-!
# The spiral system and its rollout, at a chosen scalar

`dtdemo` needs a discrete-time matrix, and the verified continuous-time
discretization (`headline-a`/`headline-b`) is not landed yet, so `buildSystem`
takes it directly: `A_d := I + dt A`, first-order Euler, computed *exactly* in
`ExactDyadic` from the config's rationals and read into the target scalar
*unchecked* (`Rational.lean`'s module docstring says why). This is a
placeholder for demonstrating the harness end to end, not a sound enclosure of
the flow -- `headline-a` and `headline-b` are what replace it.

`rollout` mirrors `LinearSysDT.reach`'s own recursion equation
(`reach (k+1) = reduce (plus (mtimes sys.A (reach k)) U) o`) unrolled into an
accumulator, so the harness pays for one step each rather than replaying every
prefix, the way a table indexed by `k` would. The two agree by that equation;
it is not reproved here, since this is harness code, not the verified library.
-/

-- Authors:       Tobias Ladner
-- Written:       25-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Bench

open CORALean CORALean.Float ContSet Plus Reduce Mtimes

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]

/-- What one run needs, once every config field has been checked and read into
`𝕋`: the discretized system, the initial set, and the (empty, since the
headline system carries no input) input set `reach` still asks for. -/
structure System (𝕋 : Type) where
  sys : LinearSysDT 𝕋 2
  X0 : Zonotope (Vec 𝕋 2)
  U : Zonotope (Vec 𝕋 2)


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A row of the config's `x0.generators`, read into `𝕋` -- one generator `X0.G j`
once `buildX0` reads it in. -/
def aux_readVec (field : String) (inst : String → ExactDyadic → Except String 𝕋)
    (row : Array String) : Except String (Array 𝕋) :=
  row.mapM fun s => do inst field (← parseExact s)

/-- The zero-input zonotope `reach` still takes: a single point at the origin,
no generators, no error. -/
def aux_zeroInput (z0 : 𝕋) : Zonotope (Vec 𝕋 2) :=
  { h := 0, c := fun _ => z0, G := fun j => j.elim0, E := ⟨fun _ => z0, fun _ => z0⟩ }

/-- `X0` from the config's center and generator rows, all read into `𝕋` through
`inst` -- shared with `ContRollout.buildContSystem`, so not `aux_`-named despite
living beside the auxiliaries it is built from. -/
def buildX0 (cfg : HeadlineConfig) (inst : String → ExactDyadic → Except String 𝕋)
    (z0 : 𝕋) : Except String (Zonotope (Vec 𝕋 2)) := do
  if cfg.x0Center.size ≠ 2 then throw "config `x0.center` must have exactly 2 entries" else
  let cArr ← aux_readVec "x0.center" inst cfg.x0Center
  let h := cfg.x0Generators.size
  for row in cfg.x0Generators do
    if row.size ≠ 2 then throw "config `x0.generators` rows must each have exactly 2 entries"
  let gRows ← cfg.x0Generators.mapM (aux_readVec "x0.generators" inst)
  pure
    { h := h
      c := fun i => cArr.getD i.val z0
      G := fun j i => (gRows.getD j.val #[]).getD i.val z0
      E := ⟨fun _ => z0, fun _ => z0⟩ }


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Reads the config into a `System 𝕋`: `A_d := I + dt A` computed exactly and
read through `instUnchecked`, `X0` from the center/generators through `inst`
(which rejects one that does not fit `𝕋`'s precision), `U` empty. -/
def buildSystem (cfg : HeadlineConfig) (inst : String → ExactDyadic → Except String 𝕋)
    (instUnchecked : ExactDyadic → 𝕋) : Except String (System 𝕋) := do
  let a ← parseExact cfg.a
  let b ← parseExact cfg.b
  let dt ← parseExact cfg.dt
  let dtA00 := dt.mul a
  let dtA01 := dt.mul b
  let dtA10 := dt.mul b.neg
  let dtA11 := dt.mul a
  let a00 := instUnchecked (ExactDyadic.one.add dtA00)
  let a01 := instUnchecked dtA01
  let a10 := instUnchecked dtA10
  let a11 := instUnchecked (ExactDyadic.one.add dtA11)
  let z0 ← inst "0" ExactDyadic.zero
  let Ad : Mat 𝕋 2 2 := Matrix.of ![![a00, a01], ![a10, a11]]
  let X0 ← buildX0 cfg inst z0
  pure ⟨⟨Ad⟩, X0, aux_zeroInput z0⟩

/-- One step of `LinearSysDT.reach`'s own recursion, exposed so `rollout` and
the theorem it mirrors read the same equation. -/
def step (sys : LinearSysDT 𝕋 2) (o : ℕ) (U Z : Zonotope (Vec 𝕋 2)) : Zonotope (Vec 𝕋 2) :=
  reduce (plus (mtimes (S := fun k => Zonotope (Vec 𝕋 k)) sys.A Z) U) o

/-- `#[reach 0, reach 1, ..., reach N]`, computed in one accumulating pass. See
the module docstring for why this equals repeated calls to `LinearSysDT.reach`
without their `O(N²)` cost. -/
def rollout (S : System 𝕋) (o N : ℕ) : Array (Zonotope (Vec 𝕋 2)) := Id.run do
  let mut Z := S.X0
  let mut acc := #[Z]
  for _ in [0:N] do
    Z := step S.sys o S.U Z
    acc := acc.push Z
  pure acc

end CORALean.Bench


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
