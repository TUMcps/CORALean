# specification/@specification

CORA methods of `specification/@specification/` (a class of `specification/` or `specification/signals/`; a single-file class lists its public methods, constructor included), one row each, and where CORALean answers them. Conventions, states and the out-of-scope reasons are in [../README.md](../README.md).

**CORALean counterpart:** `Specification` (the structure, with the kinds `safeSet`, `unsafeSet`, `invariant`; `custom` is a plain `Set`) and `Specification.check`. `'logic'` specifications (signal temporal logic) are the `stl` class; their checking is not here.

| Method | State | In CORALean | Note |
|---|---|---|---|
| `add` | — | — |  |
| `check` | float | [`Specification.check`](../../../src/CORALean/Specification/Operations/Check.lean), [`Specification.check_sound`](../../../src/CORALean/Specification/Theorems/CheckSound.lean) | route b — generic over the representation of the specification's set and of the checked set (the `Contains` and `IsDisjoint` instances), computable; a `true` implies the specification on the set (`check_sound`), `false` claims nothing; safe sets, unsafe sets and invariants, not `'logic'`. cora-issue — CORA's `specification/@specification/check.m`, `aux_checkCustom` (l. 319-333), runs through a cell `S` with `res = func(S{i}); if res, return` and so returns `true` as soon as any piece passes `func`; Formalized for one row and an untimed specification (`Specification.checkReachRowCora`, `none` the error; a row with time intervals is checked) (run in MATLAB, see Details) ([`Specification.checkCustomCora`](../../../src/CORALean/Specification/Counterexamples/CheckCustomCora.lean), [`Specification.checkCustomCora_any_counterexample`](../../../src/CORALean/Specification/Counterexamples/CheckCustomCora.lean), [`Specification.checkReachRowCora`](../../../src/CORALean/Specification/Counterexamples/CheckReachSetCora.lean), [`Specification.checkReachRowCora_crash`](../../../src/CORALean/Specification/Counterexamples/CheckReachSetCora.lean)). Details below. |
| `eq` | out-of-scope | n/a — matlab-runtime | compares MATLAB objects field by field |
| `inverse` | — | — |  |
| `isempty` | — | — |  |
| `isequal` | out-of-scope | n/a — matlab-runtime | compares MATLAB objects field by field. cora-issue — CORA's `@specification/isequal.m` compares the type with `'costum'` (l. 129), so two custom specifications with different functions are equal, and compares parallel locations by `all(a,b)`, a dimension (l. 106), so `{1,2}` and `{1,3}` are equal (no Lean witness: a function handle is outside the model). Details below. |
| `ne` | out-of-scope | n/a — matlab-runtime | compares MATLAB objects field by field |
| `plot` | out-of-scope | n/a — plotting/display |  |
| `plotOverTime` | out-of-scope | n/a — plotting/display |  |
| `printSpec` | out-of-scope | n/a — plotting/display |  |
| `project` | — | — |  |
| `robustness` | — | — | definition only, no theorem: [`Specification.distancePolyPointCora`](../../../src/CORALean/Specification/Counterexamples/DistancePolyPointCora.lean) models `aux_distancePolyPoint` as printed, not the whole method. cora-issue — CORA's `specification/@specification/robustness.m`, `aux_distancePolyPoint` (l. 189-224, comment "compute the norm 1 distance"), values a point outside a safe or unsafe set (halfspace directions normalized) in three ways by the number of violated rows `ind`: one row gives `halfspaceVals(ind(1))`, the Euclidean distance to that hyperplane ([`Specification.distancePolyPointCora_norm_counterexample`](../../../src/CORALean/Specification/Counterexamples/DistancePolyPointCora.lean)). Details below. cora-issue — CORA's `robustness.m` ignores `Ae, be` of the polytope, so a point off a set of lower dimension gets `0` as on the boundary (no Lean witness: the model stops at `aux_distancePolyPoint`). Details below. |
| `specification` | float | [`Specification`](../../../src/CORALean/Specification/Specification.lean), [`Specification.holds_of_outer`](../../../src/CORALean/Specification/Theorems/HoldsOfOuter.lean), [`Specification.holds_safeSet_of_bounds`](../../../src/CORALean/Specification/Theorems/Containment.lean) | route b (scalar-free) — the structure holds a set of any representation and a kind, no scalar of its own, and is computable. `holds_of_outer` is stated for every representation: the structure (a set in any representation and a kind: `safeSet`, `unsafeSet`, `invariant`) and its denotation `Specification.Holds`, with the theorem that a verdict on an outer approximation carries over to the exact set (`holds_of_outer`). `custom` is a plain `Set`, `logic` (STL) is not a `Specification` (see the `stl` table); the argument parsing, the `time` and `location` fields and the `'logic'` type are not modelled |
| `splitLogic` | — | — |  |

## Details

**`check` — the pieces.** `check` takes `func` to say that a set satisfies the specification (it
returns `res` and reports a violation when `~res`, l. 259-266), and its siblings `aux_checkSafeSet`
and `aux_checkUnsafeSet` (l. 278-317) exit on the first failing piece, so every piece must pass. A
cell is what `reach` hands `check` when a step has parallel sets (`@contDynamics/reach.m` l. 152,
197, `check(spec, Rnext.ti, ...)`; a split set is a cell), so a custom specification that one set
violates is reported satisfied whenever another passes (run in MATLAB, see Details). The header
says `res - true/false whether set satisfies the specification` and gives no other meaning to
`func`. The coverage row is `specification/check` in `references/coverage/specification/`.

**`check` — the model of the cell.** Formalized as the loop as printed and the cell `{S_ok, S_bad}`
for a `func` true on `S_ok` only.

**`check` — the `reachSet` branch.** CORA's `specification/@specification/check.m`, the `reachSet`
branch (l. 126-168), reads `timeInterval = S(k).timeInterval;` and loops
`for j = 1:length(timeInterval.set)`. `reachSet(timePoint)` leaves `timeInterval = []` (`reachSet.m`
l. 44, `aux_parseInputArgs` l. 114), and `linearSysDT/reach.m` (l. 133, 157) and
`nonlinearSysDT/reach.m` (l. 90, 99) return exactly that, so `check(spec, R)` for the result of a
discrete-time `reach` evaluates `[].set` and stops with a MATLAB error for every specification
without a time (with a time, `find(S,'time',..)` comes first and the loop is the same). The
`timePoint` sets are there and not checked. A MATLAB error, not a wrong value.

**`check` — MATLAB run.** MATLAB R2024b, CORA v2026.1.0 (904a444): check(specification(@(S) ...,'custom'),{Sok,Sbad}) returns 1 where func(Sok)=1, func(Sbad)=0 and check(spec,Sbad) returns 0. check(specification(interval([0;0],[5;5]),'safeSet'),reachSet(tp)) for two `timePoint` sets and an empty `timeInterval` errors in check line 192: Dot indexing is not supported for variables of this type (confirmed).

**`isequal` — cora-issue account.** `@specification/isequal.m` ends with two guards that are meant
to refuse the types it cannot compare: `'logic'` (throws) and `'costum'` (l. 129, throws). The type
is spelled `'custom'` everywhere else, so the second guard never fires and the function returns the
`true` it has reached by then: two custom specifications with different functions are equal. The
locations of a parallel automaton (a cell) are compared with `all(spec1.location{i},spec2.location{i})`
(l. 106), the dimension form `all(A,dim)` and not `all(a == b)`: `all(1,3)` is true, so the cells
`{1,2}` and `{1,3}` are equal.

**`isequal` — MATLAB run.** MATLAB R2024b, CORA v2026.1.0 (904a444): isequal(specification(@(S) true,'custom'),specification(@(S) false,'custom')) = 1. isequal(specification(interval(0,1),'safeSet',{1,2}),specification(interval(0,1),'safeSet',{1,3})) = 1 (confirmed).

**`robustness` — the other branches.** Exactly `n` rows give `sqrt(sum((v-p).^2))` for the vertex
`v = linsolve(C(ind,:),d(ind))`, the Euclidean distance to `v`. Any other count solves the linear
program `min ‖p-x‖₁ s.t. C x ≤ d`, the norm 1 distance.

**`robustness` — the metric mismatch.** The rest of `robustness.m` is Euclidean (`abs(C*p-d)` over
unit rows is the distance to the facet hyperplane), so the magnitude is not one metric and not
monotone: for the unit cube `[0,1]³` as a safe set, `p = (2,2,½)` violates two rows and gets `2`,
whereas `p' = (2,2,2)`, further out, violates `n = 3` rows and gets `√3 < 2`. The point `(1,1,½)` of
the cube is at Euclidean distance `√2 < 2` from `p`. Every branch returns a positive number for a
point outside (`ind` nonempty, `v ≠ p`), and `robustness` negates it for a safe set, so the sign is
right: a wrong answer, not unsound (run in MATLAB, see Details). The `n`-row vertex also need not
lie in the set or be its nearest point.

**`robustness` — the Lean model.** Formalized as the function as printed
(`Specification.distancePolyPointCora`, `linsolve` as a solution of the square system and the
program as the infimum of `‖p-x‖₁`) and the cube example.


**`robustness` — the equality constraints.** `robustness.m` takes `A = P.A, b = P.b` of the set's polytope
and ignores `Ae, be`. For the safe set `0 <= x1 <= 1, x2 = 0` a point off the line `x2 = 0` violates no
row of `A x <= b`, so it gets `0` as a point on the boundary does; the distance to the set, `1` for
`(0.5, 1)`, is not seen. The sign is wrong (a violation reads as the boundary), where the metric
mismatch above is a wrong magnitude.

**`robustness` — MATLAB run.** MATLAB R2024b, CORA v2026.1.0 (904a444): robustness(specification(unit cube [0,1]^3,'safeSet'),`[2;2;0.5]`) = -2 and at `[2;2;2]` = -1.73205. robustness of the safe set 0<=x1<=1, x2=0 (a polytope with `Ae = [0 1]`) at (0.5, 1) = -0, where the distance to the set is 1 (confirmed).
