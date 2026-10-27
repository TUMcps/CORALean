# Adaptive Parameter Tuning for Reachability Analysis of Nonlinear Systems

```bibtex
@inproceedings{wetzlinger2021adaptive,
  author = {Wetzlinger, M. and Kulmburg, A. and Althoff, M.},
  title = {Adaptive Parameter Tuning for Reachability Analysis of Nonlinear Systems},
  booktitle = {Proceedings of the 24th International Conference on Hybrid Systems: Computation and Control},
  year = {2021}
}
```

**Source:** https://mediatum.ub.tum.de/doc/1725668/document.pdf — Wetzlinger's thesis, Appendix A.5 (pp. 109–120), a verbatim reprint of the ACM version, read with `pypdf` (poppler is not installed here, so the Read tool's PDF-page mode is unavailable, and the ACM version at https://doi.org/10.1145/3447928.3456643 is paywalled; the paper has no arXiv preprint).  
**Inventory:** confirmed

The nonlinear counterpart of the [CDC 2020 tuning paper](../2020/wetzlinger-cdc-adaptive-tuning.md):
the time step size chosen by scalar optimization of an estimated reachable-set size
over a finite horizon, and the Taylor abstraction order switched whenever the
abstraction error moves by more than a fixed threshold. Its `Thm. 3.2` is the
Hausdorff bound between a zonotope and its box over-approximation that
`reduceBoxOrder` needs, in the form the [NAHS 2022 paper](../2022/wetzlinger-nahs-abstraction-error.md)
later sharpened into three bounds — the same file now carries both papers'
citations. `Lemma 3.1` is the minimax inequality the paper's own proof of
`Thm. 3.2` leans on; the formalization of `Thm. 3.2` takes a more direct route
and does not call it, so `Lemma 3.1` is formalized on its own, standalone terms.
`Prop. 1` is the special case of the NAHS 2022 paper's `Thm. 2` at a constant `A`
and `Ψ`, which is how this paper — not yet having re-linearized within a step —
states it; the same file cites both papers.

Both algorithms are here, and both stand beside the later paper's rather than share with it.
`Alg. 1` linearizes at the plain center of R(t_s) where the later paper carries that center half
a step along f, and numbers the same loop in 17 lines against that paper's 18. `Alg. 2` is the
tuning of the time step size on its own, and from its line 10 on it *is* the later paper's: (31)
minimized over (30), and (29) solved for the gain, are shared unchanged under other equation
numbers. New here is the first step, which has no previous gain to rescale a horizon from and
shrinks one by ζ_δ until (32) is met instead.

Its numbering runs on two schemes at once: `Def. 1` and `Prop. 1` are numbered
sequentially, `Lemma 3.1` and `Thm. 3.2` by section. The rows use the numbers as
printed.

## Results

| Result | What it says | In CORALean | Class |
|---|---|---|---|
| `Def. 1` | (Zonotopes) [cites [27, Def. 1]] Z := {x \| x = c + Σ_{i=1}^γ α_i g^(i), -1≤α_i≤1}, with order ρ := γ/n and shorthand ⟨c,G⟩_Z. | n/a — restated from Girard 2005, which this formalization does not draw on directly | `restated` |
| `Lemma 3.1` | For continuous f: C1×C2→I and g: C1→I on compact C1,C2⊂R^n and a compact interval I⊂R^n: if min_{y∈C2} f(x,y) ≤ g(x) for every x∈C1, then max_{x∈C1} min_{y∈C2} f(x,y) ≤ max_{x∈C1} g(x). | [`CORALean.minimax_le`](../../src/CORALean/Global/Minimax.lean) | `underspecified` — typo: codomain `I ⊂ ℝⁿ` printed, `I ⊂ ℝ` meant |
| `Thm. 3.2` | For a zonotope Z=⟨c,G⟩_Z and its box over-approximation Z_B := box(Z)=⟨c,G_B⟩_Z ⊇ Z, the Hausdorff distance d_H(Z,Z_B) = max_{x_B∈Z_B} min_{x∈Z} ‖x_B-x‖_2 is over-approximated by ω(Z) := 2‖Σ_{k=1}^γ ĝ^(k)‖_2, where ĝ^(k) is \|g^(k)\| with the entry at the (first) index i* attaining ‖g^(k)‖_∞ set to zero. | [`Zonotope.hausdorffDist₂_interval_le_max`](../../src/CORALean/ContSet/Zonotope/Real/Theorems/HausdorffDist2IntervalLeMax.lean) | `underspecified` — typo in eq. (15): compares the generator index `k` with `i*`; `i ≠ i*` is meant |
| `Prop. 1` | Scaling Δt by ζ_δ∈(0,1) shrinks the i-th entry of the diameter of box(R_abs) by ζ_δ^{λ_i} with λ_i∈N as Δt→0: lim_{Δt→0} d_i(box(R_abs(ζ_δΔt)))/d_i(box(R_abs(Δt))) = ζ_δ^{λ_i}, where λ_i = j+1 for the first non-negative j with (A^j Ψ)_i ≠ {0}. | [`CORALean.gainDim_tendsto_pow_const`](../../src/CORALean/ContDynamics/NonlinearSys/Theorems/GainDimTendstoPowConst.lean) — `j` read off the generator row of `A^jΨ` alone, the center not widening a box | `proof-gap` — proof substitutes the truncated (6) while `λᵢ` ignores `η_abs`; formalized at the untruncated series |
| `Alg. 1` | "Reachability analysis of nonlinear systems using state-space abstraction": per step, linearize at z*(t_s) = center(R(t_s)), compute R_lin by `linReach`, enlarge the estimated abstraction error Ψ̄ until Ψ ⊆ Ψ̄, add the resulting R_abs to both the time-point and time-interval solution, and reduce the set representation size. | [`CenterAbstrReach.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Operations/CenterAbstrReach.lean) — one `let` per printed line, for the ordinary differential equations of (1). Lines 7-10 are [`AbstrErrLoop.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Operations/AbstrErrLoop.lean), which the [NAHS 2022 paper](../2022/wetzlinger-nahs-abstraction-error.md) numbers 8-11, and line 11's `abstrSol` is `LinearSys.inputSolution` at Ψ, (6) being that operation's formula up to the uniform remainder box `inputRemainder` this tree writes for `E(Δt,η_abs)`. Line 5 adds the particular solution outside the convex hull, where (8) prints it inside — the same departure the [NAHS 2022 paper](../2022/wetzlinger-nahs-abstraction-error.md)'s `Alg. 1` row records for its (12), and it is recorded rather than discharged here too. What the loop guarantees is [`AbstrErrLoopFixed.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Theorems/AbstrErrLoopFixed.lean) and what line 17 collects is [`SubsetCenterAbstrReach.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Theorems/SubsetCenterAbstrReach.lean). See the Findings. | `underspecified` — line 3 names no input expansion point; lines 5 and 13 index `τ` one step ahead |
| `Alg. 2` | "Tuning of the time step size Δt": maintains the finite horizon Δ and the gain φ_1 across steps, computes R_abs(Δ) and its scalar counterpart r_abs,1, and returns the optimal time step size Δt* by Eq. (31) — initializing by shrinking Δ with ζ_δ until φ_1 ≥ ζ_Δ in the first step. | [`TuneDeltat.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Operations/TuneDeltat.lean) — both branches, one `let` per printed line. Lines 10-13 are the [NAHS 2022 paper](../2022/wetzlinger-nahs-abstraction-error.md)'s `Alg. 2` lines 1, 9, 10 and 16 under other equation numbers, so (30) and (31) are [`OptDeltat.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Operations/OptDeltat.lean) and (29) is [`EstimateGain.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Operations/EstimateGain.lean), held to [`OptDeltatDescent.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Theorems/OptDeltatDescent.lean) and [`EstimateGainBracket.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Theorems/EstimateGainBracket.lean) unchanged. New here is the `s = 1` branch, lines 2-8: (25)'s gain is [`TuneDeltatInit.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Operations/TuneDeltatInit.lean) over two supplied box diameters, the shrink loop carries explicit fuel and returns an `Option` where the source loops forever, and what it buys is [`TuneDeltatInitGain.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Theorems/TuneDeltatInitGain.lean). `d(box(R_abs(Δt)))` and `r(R_abs(Δt))` are the caller's, as `aux_tuneAbstrOrder`'s diameters are; see the findings below | `underspecified` — first-step loop tests a gain it has not computed and scales an uninitialized variable; eq. (32) prints `min` for `max` |

## Findings

**`Lemma 3.1`.** The shared codomain is printed as "a compact interval `I⊂R^n`". A
compact interval of `R^n` would make `f` and `g` vector-valued, leaving `min`/`max`
without an order to run in. `Thm. 3.2`'s proof applies the lemma at `f(x_B,x) =
‖x_B-x‖_2`, a scalar, and `g` constant at `2‖ẑ‖_2`, another scalar — real-valued
throughout — so `I⊂R^n` is a misprint for a compact interval `I⊂R`. Formalized
that way; `I` itself never enters the statement, since boundedness follows from
continuity on a compact domain regardless of a named enclosing interval.

**Eq. (15), in `Thm. 3.2`.** The entries of ĝ^(k) are selected by `if k ≠ i*`, comparing
the *generator* index k with i*, which the same theorem defines as a *component* index —
"the (first) index for which g^(k)_{i*} = ‖g^(k)‖_∞". The condition meant is `i ≠ i*`: the
proof zeroes the largest component of each generator, writing v^(k)_i ∈ [-2\|g^(k)_i\|,
2\|g^(k)_i\|] "if i ≠ i*, 0 otherwise" and then "rewrit[ing] using (15)". The
[NAHS 2022 paper](../2022/wetzlinger-nahs-abstraction-error.md) prints the same definition
correctly as `i ≠ i*` in its Eq. (18). The bound is right as intended.

**`Prop. 1`.** Formalized as the [NAHS 2022 paper](../2022/wetzlinger-nahs-abstraction-error.md)'s
`Thm. 2` at a constant `A` and `Ψ` — `R_abs(Δt)` read, as that paper's own `abstrSolInf` already
is, as the un-truncated series `[1, (8)]` would sum rather than this paper's truncated `(6)`. At
constant `A`, `Ψ` the specialization is proved outright, not inherited with a hypothesis: `Thm. 2`
assumes its expansion's leading term because passing a limit inside an infinite series needs
uniform control over the index that a moving `A(h)`, `Ψ(h)` does not supply. Here every summand
is already independent of `Δt`, so the same expansion is elementary and is proved here rather
than assumed.

The paper's own proof of `Prop. 1` instead substitutes its `(6)` — `Rabs` truncated at a *fixed*
`η_abs` plus a remainder of order `O(Δt^{η_abs+1})` — and the printed formula for `λ_i` never
mentions `η_abs`. It is only the value obtained when the first `j` with `(A^jΨ)_i ≠ {0}` sits at
or below `η_abs`: should every term up to `η_abs` vanish in dimension `i` while some later `AʲΨ`
does not, the remainder (which is not shaped by `Aʲ`'s individual sparsity, only by `η_abs`) sets
the true leading order at `η_abs+1` rather than `j+1`. `η_abs` is itself chosen per step by a
separate, `Δt`-dependent criterion, `(11)`, so a proof that holds it fixed across the whole
`Δt→0` limit implicitly needs the truncation to already reach the order that decides the limit.
The claim proved here is about the un-truncated `Rabs`, where the difficulty does not arise.

**`Alg. 1` — line 3 names no input expansion point, and a definition of its own is why.** §2.2
expands the dynamics in the *extended* vector z = [xᵀ uᵀ]ᵀ, so line 4's `taylor` needs a point
for u as well; line 3 gives only `center(R(t_s))`, the state half. The [NAHS 2022 paper](../2022/wetzlinger-nahs-abstraction-error.md)'s (6) prints both
halves and CORA takes `center(U)` for the input one, which is what the formalization takes. The
state half is the real difference between the two papers' `Alg. 1`: here the plain center of
R(t_s), there that center carried half a step along f. Sharing one Lean definition between them
was rejected for a second reason as well — the [NAHS 2022 paper](../2022/wetzlinger-nahs-abstraction-error.md) splits `taylor` and `linSys` across its lines
4-5 where this paper's line 4 does both, so this algorithm runs to 17 lines and that one to 18
and every line number from 5 on differs by one. The trailing line numbers are what make an `Alg.
N` definition readable against its printed original, and one body cannot carry two numberings,
so `CenterAbstrReach.lean` is written out beside `AbstrReach.lean` rather than parameterized out
of it. `abstrErrLoop` *is* shared: its four lines are identical in both papers and only the
numbers move, which one sentence in its docstring records.
[`CenterAbstrReach.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Operations/CenterAbstrReach.lean)

**`Alg. 1` — lines 5 and 13 index the time interval one step ahead of §2.2.** §2.2 divides the
horizon into `τ_s = [t_s, t_{s+1}]`, so the interval a step out of `t_s` covers is `τ_s`; lines
5 and 13 call it `τ_{s+1}`. Line 17 then unions `⋃_{j=0}^{K-1} R(τ_j)`, which under the lines'
own labelling collects an `R(τ_0)` no iteration ever computes and drops the last iteration's
`R(τ_K)`. Eqs. (7) and (8) use §2.2's indexing — `R_abs(τ_s)` is what the step out of `t_s` adds
— so it is lines 5 and 13 that are off by one, not the union. Nothing rides on it: the
formalization indexes by the iteration, `centerAbstrReach` unioning the first `K` iterations'
time-interval sets, which is what both readings agree the algorithm returns. The same labelling
is printed in the [NAHS 2022 paper](../2022/wetzlinger-nahs-abstraction-error.md)'s `Alg. 1`.
[`CenterAbstrReach.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Operations/CenterAbstrReach.lean)

**`Alg. 2` — the first step's loop tests a gain it has not computed, and shrinks a variable it has
not initialized.** Two defects in lines 2-7, both in the `s = 1` branch and both settled by the
prose. First, line 3's `while φ₁ < ζ_Δ` is a pre-test, but `φ₁` is produced by line 6 inside the
body and the algorithm's own input list supplies it only "if s > 1". On entry there is no `φ₁` to
compare. §3.4 describes the loop the other way round ("we first decrease an arbitrarily initialized
Δt (Line 2) until the condition in (32) is met, yielding Δ ... as well as φ₁ in the process (Lines
3-7)"), i.e. a `repeat … until`, which is the only reading under which the first step has a gain to
test; formalized that way, so `tuneDeltatInit` always shrinks at least once. Second, line 2
initializes `Δt` while line 4 scales `Δ` — the variable initialized is never read and the variable
scaled is never initialized, and line 4's own note reads "⊲ Decrease Δt". (32) settles that too: it
is the finite horizon `Δ` that is shrunk until `φ₁(Δ) ≥ ζ_Δ`, so the two are one variable and line
2's arbitrary value is `Δinit` here. (Line 3 and line 10 also read `ζ_Δ`, which the `Input:` list
omits though it lists `ζ_Z`, `ζ_P` and `ζ_δ`; Table 1 fixes it globally.)
[`TuneDeltat.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Operations/TuneDeltat.lean)

**Eq. (32) — the minimum is a maximum.** (32) sets `Δ = min τ such that φ₁(τ) ≥ ζ_Δ`. By `Prop.
1` and the two properties drawn from it, `φ(Δt) < ζ_δ` at every finite step size and `lim_{Δt→0}
φ(Δt) = ζ_δ`, so `φ` *rises* as the span shrinks and `{τ : φ₁(τ) ≥ ζ_Δ}` is an interval `(0,
τ*]`: its infimum is 0, it is not attained, and a minimum would name no horizon at all. The
maximum is `τ*`, and it is what `Alg. 2` lines 3-7 compute — they walk down the grid `ζ_δ^j Δ`
and stop at the *first* value that clears the condition, hence the longest one that does. That
is also what §3.4 wants: the linear interpolation (26) of `φ` is to be checked over as long a
horizon as it will bear, not over a vanishing one. `tuneDeltatInit_gain` states exactly what the
loop buys — the horizon reported meets (32)'s condition and is `ζ_δ^{j+1}` times the arbitrary
initialization — and claims no minimality.
[`TuneDeltatInitGain.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Theorems/TuneDeltatInitGain.lean)

**`Alg. 2` — lines 12-13 are in the order the later paper's `Alg. 2` line 10 gets wrong.** (31)
is minimized over `k'` through (30), which reads the gain `φ₁`; this algorithm evaluates it at
line 12 and only updates `φ₁` at line 13, and its `Input:` line says in so many words that the
`φ₁` it is given is "of previous step". So the gain line 12 uses is the last step's,
deliberately and consistently. The later paper reprints the same two steps as its lines 10 and
16 but subscripts line 10's gain `φ⁽¹⁾_k`, the value line 16 has not computed yet — the finding
recorded on the [NAHS 2022 paper](../2022/wetzlinger-nahs-abstraction-error.md)'s page. Nothing to fix here; it is the cross-check that settles which of the
two readings was meant, and `optDeltat` is passed the previous gain in both.
[`TuneDeltat.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Operations/TuneDeltat.lean)

**`Alg. 1` — lines 4-5 and the float step.** Lines 4-5 are the caller's, nothing here
differentiating `f`, which is why the certificate sits on the theorems. A definition of its own
rather than a share of that paper's `AbstrReach.lean`: line 3 differs, and so does every line number
from 5 on — see the finding below. In floats the step is
[`CenterAbstrStepFloat.lean`](../../src/CORALean/ContDynamics/NonlinearSys/Operations/CenterAbstrStepFloat.lean),
linearizing at the stored center of the start set and checking a region where lines 7-10 enlarge an
error.
