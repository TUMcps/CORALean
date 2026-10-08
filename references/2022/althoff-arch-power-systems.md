# Benchmarks for the Formal Verification of Power Systems

M. Althoff. "Benchmarks for the Formal Verification of Power Systems". In Proc. of the 9th International Workshop on Applied Verification of Continuous and Hybrid Systems (ARCH22), EPiC Series in Computing, vol. 90, pp. 26-43, 2022.

**Source:** https://mediatum.ub.tum.de/doc/1696138/1696138.pdf (the published EPiC paper as deposited in TUM's repository mediaTUM, 18 pages, read in full; text extracted with `pypdf`); also at https://easychair.org/publications/paper/8Tcg. CORA cites it as "Formal Verification of Power Systems", submitted to ARCH 2022, in `models/Cora/infiniteBus.m`, `models/Cora/infiniteBus_polynomialized.m` and the two region-of-attraction examples built on them.  
**Inventory:** confirmed (against the published paper: Equations 1-7, Table 1 and Figures 1-8; no numbered definitions, theorems or algorithms, the verification problems being defined in the prose of Sec. 3.1; Sec. 4 is the benchmarks' solutions)

A benchmark proposal: the generator and power-flow model behind CORA's `powerSystem2cora`, the
three verification problems (transient stability, region of attraction, robustness), and one
solved instance of each. Its mathematics is a handful of identities and one verification
criterion. The rewriting of the generator power (Eq. 2) and the single-machine-infinite-bus
system of Sec. 4.4 (its field from Eqs. 1-2, its equilibrium, and that CORA's `infiniteBus`
is it at Table 1's values) are formalized, the latter in the frequency deviation `ω - ω_s`
rather than Eq. 6's `ω`. The region-of-attraction criterion of
Sec. 3.1.2, `∃ t > 0 : R(t) ⊆ S`, does not place `R(0)` in the region of attraction `D` as the
paper defines it, by a limit, since a solution may circle inside `S` without converging; it
gives that every solution is in `S` from `t` on, and `R(0) ⊆ D` where the limits exist.

## Results

| Result | What it says | In CORALean | Class |
|---|---|---|---|
| `Sec. 1` | The state of the art: simulating the `2^{n+m+o}` extreme initial states, inputs and parameters does not bound all solutions, power systems not being monotone (after Angeli and Sontag); reachability of nonlinear DAEs is undecidable (after Platzer and Clarke); direct methods need Lyapunov functions. | n/a — a survey | `not-a-claim` |
| `Eq. 1` | The generator model `δ̇ = ω - ω_s`, `ω̇ = -(D/M)(ω - ω_s) + P_m/M - P_g/M`, `Ṗ_m = -(ω - ω_s)/(T_SV R_D) - P_m/T_SV + P_c/T_SV`, after Chen and Domínguez-García with power for torque. | n/a — the paper's model; its use in Sec. 4.4 is checked under that row | `not-a-claim` |
| `Table 1` | Default generator parameters: `M = 1/(15π)`, `D = 0.04`, `\|Y_g\| = 5`, `Ψ_g = -π/2`, `T_SV = 1`, `R_D = 6π`, `ω_s = 120π`. | n/a — data; at these values the field of Sec. 4.4 is CORA's `infiniteBus` | `not-a-claim` |
| `Eq. 2` | The generator's power `P_g = E V\|Y_g\| cos(-Ψ_g - δ + Θ) - V²\|Y_g\| cos(-Ψ_g)`, `Q_g = E V\|Y_g\| sin(-Ψ_g - δ + Θ) - V²\|Y_g\| sin(-Ψ_g)` (after Schavemaker and van der Sluis, Eq. 5.10) becomes, by `cos(-α) = cos α` and `sin(-α) = -sin α`, `P_g = E V\|Y_g\| cos(Ψ_g + δ - Θ) - V²\|Y_g\| cos Ψ_g`, `Q_g = -E V\|Y_g\| sin(Ψ_g + δ - Θ) + V²\|Y_g\| sin Ψ_g`. | [`GeneratorPowerRewrite.lean`](../../src/CORALean/Global/GeneratorPowerRewrite.lean) — the two forms are equal | `correct` |
| `Eq. 3` | The power-flow equations `P_i = Σ_j V_iV_j\|Y_ij\| cos(Ψ_ij + Θ_j - Θ_i)`, `Q_i = -Σ_j V_iV_j\|Y_ij\| sin(Ψ_ij + Θ_j - Θ_i)` at each bus. | n/a — restated from P. Schavemaker and L. van der Sluis, *Electrical Power System Essentials* (Wiley, 2008), a textbook with no page here | `restated` |
| `Sec. 2.3` | A power dropout sets `P_g = Q_g = 0` and replaces `E_i` by `V_i`, the bus becoming a load bus. | n/a — modelling | `not-a-claim` |
| `Eq. 4` | The time-invariant, semi-explicit, index-1 DAE `ẋ = f(x, y, u)`, `0 = g(x, y, u)`. | n/a — restated; tracked as `Eq. 1` on [Althoff, Krogh 2014](../2014/althoff-tac-nonlinear-dae.md) | `restated` |
| `Eq. 5` | The algebraic variables: generator voltages, load-bus voltages, the phases of all buses but the slack bus. | n/a — the numbering of variables | `not-a-claim` |
| `Eq. 6` | The differential variables: generator phases, angular velocities, mechanical powers. | n/a — the numbering of variables | `not-a-claim` |
| `Eq. 7` | The inputs: commanded powers, injected active and reactive powers, and voltages and phases at cut transmission lines. | n/a — the numbering of variables | `not-a-claim` |
| `Sec. 3.1` | Consistent initial states `g(x(0), y(0), u(0)) = 0`, the unique solution `γ(t, x(0), y(0), u(·))` assumed for piecewise continuous inputs, the exact reachable set `Rᵉ(t_i)` and `R([t_i, t_{i+1}]) = ⋃_t R(t)`. | n/a — restated; tracked as `Eq. 1` on [Althoff, Krogh 2014](../2014/althoff-tac-nonlinear-dae.md) | `restated` |
| `Sec. 3.1.1` | Transient stability, read strictly: with `R(0) ⊇ R(t_o)`, stability for the contingency is shown by `∃ t > t_c : R(t) ⊆ R(0)`. | n/a — the benchmark's definition of transient stability, which the criterion is | `not-a-claim` |
| `Sec. 3.1.2` | A robust positively invariant set `S` (after Blanchini, Def. 2.2), `∀ t > 0, ∀ u(·), ∀ [x(0); y(0)] ∈ S : γ(t, x(0), y(0), u(·)) ∈ S`; the region of attraction `D = {[x(0); y(0)] \| ∀ u(·) : lim_{t→∞} γ(t, x(0), y(0), u(·)) ∈ S}`, which unlike a steady state covers limit cycles; and "to verify the region of attraction, we have to show that for `R(0) = D`, it holds that `∃ t > 0 : R(t) ⊆ S`". | [`RobustInvariant.lean`](../../src/CORALean/Global/RobustInvariant.lean), [`RegionOfAttraction.lean`](../../src/CORALean/Global/RegionOfAttraction.lean), [`MemOfReachSubset.lean`](../../src/CORALean/Global/MemOfReachSubset.lean), [`SubsetRegionOfAttraction.lean`](../../src/CORALean/Global/SubsetRegionOfAttraction.lean), [`RegionOfAttractionCounterexample.lean`](../../src/CORALean/Global/RegionOfAttractionCounterexample.lean) — over the solution map `γ` with the time-invariance and unique solutions of Sec. 3.1 as hypotheses: from `R(t) ⊆ S` every solution from `R(0)` is in `S` at every later time, and `R(0) ⊆ D` when `S` is closed and every such solution converges; and the counterexample **Counterexample:** `regionOfAttraction_counterexample` | `fixed` — `D` asks for a limit, which the criterion does not give: the harmonic oscillator with `S` the closed unit disc satisfies it for `R(0) = S`, and `(cos t, -sin t)` from `(1, 0)` has no limit; true with "the limit, where it exists", or with `D` read as "in `S` from some time on"; see Findings |
| `Sec. 3.1.3` | Robustness against uncertain demand and production: `R([0, t_f]) ⊂ X`. | n/a — the specification of the benchmark | `not-a-claim` |
| `Sec. 3.2` | The case format (Fig. 2): buses, generator parameters, demands, voltages, admittance matrix. | n/a — a data structure | `not-a-claim` |
| `Sec. 3.3` | The specification format (Fig. 3): `t_c`, `t_f`, `t_o`, `R0`, `S`, `U`, `X`. | n/a — a data structure | `not-a-claim` |
| `Sec. 4.1` | Loading cases from PSS/E RAW and MATPOWER files into the case format (`loadPowerSystemCase`). | n/a — conversion of file formats | `not-a-claim` |
| `Sec. 4.2` | Generating the DAE of Eq. 4 symbolically (`powerSystem2cora`) and exporting to SpaceEx (`cora2spaceex`). | n/a — tool support; the abstractions it hands on are [Althoff, Krogh 2014](../2014/althoff-tac-nonlinear-dae.md)'s | `not-a-claim` |
| `Sec. 4.3` | Transient stability of `TSA:IEEE30-1:MA2014-30-1` verified in 405 s (Figs. 4, 5). | n/a — an experiment | `not-a-claim` |
| `Sec. 4.4` | The single-machine-infinite-bus system: neglecting the torque dynamics of Eq. 1 and inserting `Θ_i = 0`, `Ψ_g,i = -π/2` in Eq. 2 gives `ẋ₁ = x₂`, `ẋ₂ = (P_m - E V\|Y_g\| sin x₁ - D x₂)/M`; with `P_m = E = V = 1` the equilibrium is `x₀ = [arcsin(1/\|Y_g\|), 0]ᵀ`; the region of attraction `RoA:SMIB-1:MA2022-1-1` is verified in 6.9 s (Fig. 6). | [`InfiniteBusField.lean`](../../src/CORALean/Global/InfiniteBusField.lean), [`InfiniteBusEquilibrium.lean`](../../src/CORALean/Global/InfiniteBusEquilibrium.lean) — the field from both lines of Eq. 1 with Eq. 2's `P_g`, and the equilibrium for `\|Y_g\| ≥ 1`, which Table 1's `5` meets and `arcsin` needs; at Table 1 the field is CORA's `infiniteBus`, `[x₂; 15π(1 - 5 sin x₁ - 0.04 x₂)]`; the verification run is an experiment | `underspecified` — `x₂` has to be `ω - ω_s`, the deviation from the grid frequency, for `ẋ₁ = x₂` and the equilibrium `[·, 0]ᵀ`; Eq. 6 numbers the state as `ω` itself; see Findings |
| `Sec. 4.5` | Robustness of `Rob:IEEE14-2:MA2014-14-2` verified in 207 s (Figs. 7, 8). | n/a — an experiment | `not-a-claim` |

## Findings

**`Sec. 3.1.2` — the criterion gives "in `S` from `t` on", not a limit in `S`.** The region of
attraction is printed as `D = {[x(0); y(0)] | ∀ u(·) : lim_{t→∞} γ(t, x(0), y(0), u(·)) ∈ S}`,
and the paragraph before it names limit cycles among what an invariant `S` lets it cover; a
solution on a limit cycle has no limit. The criterion `∃ t > 0 : R(t) ⊆ S` with `S` invariant
shows that every solution from `R(0)` stays in `S` from `t` on
([`MemOfReachSubset.lean`](../../src/CORALean/Global/MemOfReachSubset.lean)), and nothing about
convergence. The harmonic oscillator `ẋ₁ = x₂`, `ẋ₂ = -x₁`, no input, with `S` the closed unit
disc, is invariant and satisfies the criterion for `R(0) = S` at `t = 1`, yet the solution
`(cos t, -sin t)` from `(1, 0) ∈ S` does not converge, so `(1, 0) ∉ D`
([`RegionOfAttractionCounterexample.lean`](../../src/CORALean/Global/RegionOfAttractionCounterexample.lean)).
Where the solutions converge, `S` being closed puts the limits in `S` and `R(0) ⊆ D`
([`SubsetRegionOfAttraction.lean`](../../src/CORALean/Global/SubsetRegionOfAttraction.lean)).

**`Sec. 4.4` — the second coordinate is the frequency deviation.** Eq. 6 assigns the differential
variables `x_{N_g+i} = ω_i`, the angular velocity. The single-machine-infinite-bus field is printed
as `ẋ₁ = x₂`, `ẋ₂ = (P_m - E V|Y_g| sin x₁ - D x₂)/M`, with equilibrium `[arcsin(1/|Y_g|), 0]ᵀ`;
from Eq. 1, `δ̇ = ω - ω_s`, both hold only with `x₂ = ω - ω_s`, the coordinate in which CORA's
`infiniteBus` is written too. Read so, the field and the equilibrium are right
([`InfiniteBusField.lean`](../../src/CORALean/Global/InfiniteBusField.lean),
[`InfiniteBusEquilibrium.lean`](../../src/CORALean/Global/InfiniteBusEquilibrium.lean)).
