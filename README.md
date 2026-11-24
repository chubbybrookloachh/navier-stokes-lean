# navier-stokes-lean

*A small notebook of formalised notes on the 3D periodic Navier–Stokes equations, in Lean 4 and
Mathlib.*

Hello, and thank you for stopping by.

This repository is a modest attempt to write down, as carefully as I can, what I have been
learning about the 3D incompressible Navier–Stokes equations, and in particular about the
conditions that any finite-time blow-up would have to satisfy. I find the way vortices stretch,
fold and interact very beautiful, and writing things out in Lean has been a patient teacher: it
does not let me skip a step, and it shows me quickly where my understanding is incomplete.

I am sharing these notes in the hope of learning from people who know far more than I do. If you
find a mistake, an unclear definition, or a better way to say something, I would be very
grateful to hear about it. Issues and pull requests are warmly welcome.

> **Please note.** This work does **not** solve the Navier–Stokes Millennium Prize Problem, and
> it does not claim to. Every statement that is still open is written explicitly as a `Prop` and
> labelled **OPEN ASSUMPTION** or **OPEN CONJECTURE**, and none of them is ever used as if it had
> been proved. The theorem `clay_problem_D_of_blowupConjecture` is only an **implication**
> (`NSBlowupConjecture → ClayMillenniumProblemD`), not a solution of problem (D).

## At a glance

| | |
|---|---|
| Lean code | about 5 300 lines, in 5 libraries |
| Theorems and lemmas | about 270 |
| Core theorems checked by `scripts/check_axioms.sh` | 29 |
| `sorry` / `admit` | 0 |
| User-declared `axiom`s | 0 |
| Axioms used by the core theorems | only `propext`, `Classical.choice`, `Quot.sound` (Lean's three standard axioms) |
| Toolchain | Lean `v4.37.0-rc1`, Mathlib `v4.37.0-rc1` |
| CI | `.github/workflows/lean.yml`: `lake build`, then `scripts/check_axioms.sh` |

## What the notes contain

1. **Analysis on 𝕋³ for classical solutions** (Stage 1): the energy equality and the enstrophy
   balance for unforced periodic solutions.
2. **Quantitative constraints on any blow-up scenario** (G1–G5), under two classical
   inequalities (Gagliardo–Nirenberg and Poincaré): a blow-up would need large data **at every
   time**, at least a Leray-type rate, and a lifespan bounded from below.
3. **Two small obstructions, with proofs** (H1–H2):
   - with `f = 0` there are no unstable equilibria, because every periodic steady state is
     constant;
   - a Riccati mechanism requires a uniform margin of vortex stretching,
     `S/‖ω‖⁴ ≥ ν/‖u₀‖² + c/2`.
4. **Uniqueness of classical solutions**, `nsUnique` (H3), fully proved. From it, the
   mirror-symmetric class `OddSymmetrySpace` is shown to be invariant under the flow.
5. **A concrete initial datum**, `toroidalDipoleInit` (H4): a mirror-symmetric pair of toroidal
   vortex rings around `(½, ½, ½)`, shown to be C^∞, divergence-free, of zero mean, in
   `OddSymmetrySpace`, and non-zero.
6. **A formal statement of Clay problem (D)** (H5), compared with the printed text, together with
   the bridge theorem from `NSBlowupConjecture`.

## Files

| File | Lines | Contents |
|---|---|---|
| `NavierStokesLemmas.lean` | 1167 | The original file: a **conditional** regularity chain on ℝ³ |
| `KingExileConjecture.lean` | 92 | The "king's exile" conjecture (a `Prop`) and two immediate consequences |
| `NavierStokesTorus.lean` | 1307 | Stage 1: analysis on 𝕋³, `NSPeriodicData`, energy, enstrophy |
| `NavierStokesBlowup.lean` | 2508 | G1–G5, H0, H3–H5 |
| `NavierStokesObstructions.lean` | 273 | H1–H2 |
| `scripts/AxiomCheck.lean`, `scripts/check_axioms.sh` | | Automatic axiom check |

All comments and docstrings are in English.

## Map of the theorems

### Original file: `NavierStokesLemmas.lean` (namespace `NavierStokes`)
- `lemma1_near_far_depletion`, `lemma1_geometric_depletion`, `lemma2_enstrophy_bound`,
  `lemma3_bkm`, `conditional_regularity`. This is **conditional** regularity, under the
  hypotheses `AgmonInequality`, `BKMContinuation`, `Lemma1AnalyticInput` and
  `H2Bound`/`H2Propagation`, which are passed in as parameters rather than declared as axioms.
- A small caveat: the field `enstrophy_balance` of `NSClassicalSolution` uses the operator norm
  for the palinstrophy. On 𝕋³ the notes use the Frobenius norm (`palinstrophyT`), which is the
  one that genuine solutions satisfy.

### Stage 1: analysis on 𝕋³ (`NavierStokes.Torus`)
| Tag | Theorem | Content |
|---|---|---|
| A4 | `integral_cubeQ_fderiv_eq_zero` | `∫_Q ∂ⱼg = 0` for periodic `g` (via the divergence theorem) |
| A5 | `integral_cubeQ_fderiv_mul_eq_neg` | Integration by parts |
| A6 | `integral_cubeQ_inner_lap`, `integral_cubeQ_inner_gradient` | `∫u·Δv = −∫∇u:∇v`; `∫u·∇p = −∫p div u` |
| A7 | `integral_cubeQ_gradDot_self` | `∫∇u:∇u = ∫‖curl u‖² + ∫(div u)²` (uses Schwarz) |
| A8 | `integral_cubeQ_inner_convective_eq_zero` | The convective term vanishes |
| B | `NSPeriodicData`, `NSPeriodicData.zero` | Periodic classical solutions; the structure is non-empty |
| C | `energy_cont`, `enstrophy_cont` | Continuity in time |
| D | **`energy_equality`**, `energy_ineq` | `‖u(t)‖² + 2ν∫₀ᵗ‖ω‖² = ‖u(0)‖²` |
| E | `divergence_curl`, `integral_cubeQ_inner_curl_comm`, **`enstrophy_balance`** | `d/dt‖ω‖² = −2ν∫∇ω:∇ω + 2∫ω·(∇u)ω` |

### G: constraints on blow-up (`NavierStokes.Blowup`)
| Tag | Theorems |
|---|---|
| G1 | `riccati_blowup_time`, `lifespan_le_of_riccati` |
| G2 | `cubic_bound`, `leray_rate`, `blowup_time_lower_bound`, `leray_rate_NS` |
| G3 | `young_quartic`, `cubicBound_of_GN`, `leray_rate_NS_of_GN` |
| G4 | `small_data_enstrophy_bound(_from)`, `blowup_requires_large_data(_at)`, `enstrophy_pos_of_blowup` |
| G5 | `BKMBlowup`, `BKMBlowup.not_bounded`, `not_BKMBlowup_zero`, `blowup_witness_constraints`, `NSBlowupConjecture.witness_constraints` |

### H: obstructions, symmetry, self-similarity, concrete data, the Clay statement
| Tag | Theorems |
|---|---|
| H0 | `eq_zero_of_integral_cubeQ_eq_zero`, `volume_real_cubeQ` |
| H1 | `NSSteadyState.exists_const`, `NSSteadyState.eq_zero`, **`NSSteadyState.no_unstable_mode`** |
| H2 | `integral_inner_sq_le`, `enstrophy_sq_le`, `riccati_requires_stretching_margin` |
| H3a–b | `refl`, `MirrorSymmetric`, `OddSymmetrySpace`, `reflectSol` (Navier–Stokes is equivariant under the reflection) |
| H3c | **`nsUnique`**, `mirror_invariant`, `integral_inner_const_eq`, `mean_zero_invariant`, **`oddSymmetry_invariant`** |
| H3d–f | `bkmBlowup_of_typeI`, `typeI_of_ansatz`, `NSBlowupConjecture_of_leray` |
| H3g–h | `lintegral_inv_sq_eq_top`, `vortLinf_ge_of_modulated`, `NSBlowupConjecture_of_scenario`, `NSBlowupConjecture_of_eulerType` |
| H4 | **`toroidalDipoleInit_mem`**, `toroidalDipoleInit_smooth`, `toroidalDipoleInit_ne_zero`, `mirror_curl_of_anti`, `integral_cubeQ_curl_eq_zero` |
| H5 | `ClayMillenniumProblemD` (statement), `ClaySmoothSolution.rescale`, **`ClaySmoothSolution.exists_periodic_pressure`** (normalising the pressure by a Galilean change of frame), `nsPeriodicDataOfClay`, `not_BKMBlowup_of_extension`, **`clay_problem_D_of_blowupConjecture`** |

- **Structural note:** The reduction pipeline above establishes a one-way implication (`NSBlowupConjecture → ClayMillenniumProblemD`), not an equivalence; realising a trajectory along an unstable manifold, if one exists (H1 rules this out near steady states with `f = 0`), would require a closed-loop feedback policy rather than an open-loop static initial condition.

## What is still open

I have tried to be completely transparent about this part, since it is where the real
difficulty lies.

**Open assumptions and conjectures.** Nobody knows whether these are true, and they are never
used as if they had been proved:

| Statement | Meaning |
|---|---|
| `NSBlowupConjecture` | There is a periodic solution with C^∞ data such that `∫₀^T ‖ω‖_∞ = ∞` |
| `TypeIIOddScenario` | **Type II dynamics** (scenario A): a supercritical scale `ℓ = o(√(T − t))` and a modulated vortex profile around `(½, ½, ½)`. The modulation estimate is stated as a *consequence* of a spectral gap, because Mathlib does not yet have a spectral theory for the linearised Stokes operator. At Leray amplitude the viscosity does not disappear, and the expected obstruction is of Liouville type. |
| `EulerTypeOddScenario` | Euler-type dynamics (scenario B), where the effective viscosity `ν(T − t)/ℓ²` tends to 0 |
| `LeraySelfSimilarOddScenario` | A local type I (Leray) self-similar scenario. Global Leray profiles are already excluded by Nečas–Růžička–Šverák and Tsai. |
| `RiccatiLowerBound` | A Riccati lower bound for the enstrophy |
| `KingExileConjecture(Strong)` | The "king's exile" conjecture |
| `ClayMillenniumProblemD` | Clay problem (D), **only stated** |

Each of the three scenarios implies `NSBlowupConjecture`, and those three implications *are*
proved. But whether any of the scenarios actually happens is entirely open.

**Classical assumptions.** These are true in the literature, but Mathlib does not yet have the
infrastructure to prove them here: `GNStretchingIneq`, `PoincareIneq`,
`EnstrophyBlowupCriterion`, and the hypotheses of the original file.

## Specification audit

Because a formal statement is only useful if it says what it is meant to say, I tried to check
the Lean statement of problem (D) word by word against Professor Charles Fefferman's original
text:

> C. L. Fefferman, "Existence and Smoothness of the Navier–Stokes Equation", in J. Carlson,
> A. Jaffe, A. Wiles (eds.), *The Millennium Prize Problems*, Clay Mathematics Institute /
> American Mathematical Society, 2006, pp. 57–67.

**What this comparison is based on, and what is still pending.** To be clear about the source:
the comparison described in this section was made against the **official PDF of the volume
published on the website of the Clay Mathematics Institute**. I have **not yet** checked the
printed book. The British Library's physical copy (shelfmark `YK.2007.b.4238`) is kept in an
off-site store outside London, so I have ordered it in, which takes about 48 hours. The final
side-by-side comparison in the Reading Room is booked for 28 November 2026. Until then, the
`[VERIFIED: …]` tags below mean "checked against the official CMI PDF", not "checked against the printed volume". I will update this section after that visit,
including any difference I find.

Equations (1), (2), (3) are on p. 57; conditions (8)–(11) and statement (D) are on p. 58. Each of
the 12 fields of `ClayInitialData`, `ClayForce` and `ClaySmoothSolution` carries the tag
`-- [VERIFIED: Clay Monograph 2006, pp. 57–67]`, together with the number of the equation it
corresponds to.

The comparison helped me find, and correct, two places where an earlier draft did not match the
original. Both had made the earlier statement *weaker* than Fefferman's:

1. **The energy condition (7) is not part of (D).** It belongs to the problems on ℝ³. The
   condition `ClayBoundedEnergy` has been removed.
2. **Condition (10) only asks for `u` to be periodic, not `p`.** The field `periodic_p` has been
   removed. As a result, `p` may contain a linear part `⟪a(t), x⟫`, and solutions are only unique
   up to a Galilean change of frame. The theorem `ClaySmoothSolution.exists_periodic_pressure`
   deals with this: the change of frame `ũ(x,t) = u(x + X(t), t) + Y(t)`, with `Y' = a`,
   `X' = −Y` and `X(0) = Y(0) = 0`, gives another solution of (D) with the same initial datum and
   a periodic pressure.

Some formulations are **equivalent** to the printed text without being identical to it symbol
for symbol. I mention them here so that readers can judge for themselves:
- C^∞(ℝ³ × [0,∞)) is expressed with `ContDiffOn` on the closed domain.
- Condition (9) is expressed with the norm of the full derivative of order `|α| + m`.
- Equation (1) is written with the time derivative taken within `[0, ∞)`.
- "Take ν > 0" is read as "for every ν > 0", which is the stronger reading.

If you see a place where my reading of the text is mistaken, I would be especially grateful to
know.

## Reproducing the checks

You will need [elan](https://github.com/leanprover/elan).

```bash
lake exe cache get        # download the prebuilt Mathlib
lake build                # build every library
./scripts/check_axioms.sh # no new axioms; every core theorem uses only the 3 standard axioms
```

To check any single theorem:

```lean
import NavierStokesBlowup
#print axioms NavierStokes.Blowup.clay_problem_D_of_blowupConjecture
-- [propext, Classical.choice, Quot.sound]
```

## Things I would like to learn next

- Formalising the classical assumptions: Gagliardo–Nirenberg and Poincaré on 𝕋³ through Fourier
  series, and Leray's enstrophy criterion.
- Local existence for the data `toroidalDipoleInit`.
- Numerical experiments, and perhaps computer-assisted checks, for the scenarios of H3g–H3h.

## Thanks

These notes would not exist without the Lean 4 and Mathlib communities. Their library, their
documentation and their generosity in answering questions make it possible for a beginner to try
things like this at all. My heartfelt thanks to everyone who builds and maintains them.

## About the author

These notes are written under the name `chubbybrookloachh`. For now I prefer to keep my real
identity private, so that the notes can be read on their own merits. `authorship/PROOF_OF_AUTHORSHIP.txt`
explains how authorship can be confirmed later if needed.

**PGP Fingerprint:** 96FC 4E0E 82B7 CF5D AEED A309 A315 0C5D 5E33 D350 ([public-key.asc](./public-key.asc))

## Notes on Further Exploration & Support

This repository is released as a self-contained formalisation of the reduction framework (`NSBlowupConjecture → ClayMillenniumProblemD`) and its symmetric initial data (`toroidalDipoleInit`). Notice that the constructions in `H3–H4` are calibrated specifically around the invariant geometry of `OddSymmetrySpace`; whether these constraints admit dynamic trajectories depends entirely on how one frames the initial state.

If you find this verified benchmark useful for formal mathematics or AI theorem-proving research and wish to support independent study, optional sponsorship links are available in [`.github/FUNDING.yml`](./.github/FUNDING.yml) (or via `chubbybrookloachh@proton.me`). For a quieter, non-technical reflection on these notes, see [A Little Note](./docs/index.html).
