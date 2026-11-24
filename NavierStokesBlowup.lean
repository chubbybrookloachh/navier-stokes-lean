/-
  NavierStokesBlowup.lean — Toward blow-up: ODE tools, with every OPEN assumption named
  ====================================================================================

  ⚠️ PLEASE READ BEFORE CITING
  ----------------------------
  Finite-time blow-up from smooth data on `𝕋³` is the still-OPEN half of the Millennium
  Problem. This file does NOT prove it. What it contains is modest:
  * pure ODE lemmas (fully proved);
  * consequences for `NSPeriodicData` solutions, where every step that is not known to be
    true is stated as an explicit, named ASSUMPTION whose docstring says that it is OPEN.

  STATUS
  ------
  * G1: `riccati_blowup_time` — `Y' ≥ cY²`, `Y(0) > 0` ⇒ `T ≤ 1/(cY(0))`.
  * G1': `RiccatiLowerBound` (OPEN ASSUMPTION) and `lifespan_le_of_riccati`.
  * G2: `cubic_monotone`, `cubic_bound`, `leray_rate` (`Y → ∞` at `T` ⇒
    `1 ≤ 2K(T−s)Y(s)²`), `blowup_time_lower_bound` (`T ≥ 1/(2KY(0)²)`).
  * G2': `EnstrophyCubicBound` (CLASSICAL ASSUMPTION, true; derived in G3) and
    `leray_rate_NS` — a NECESSARY condition for any blow-up scenario.
  * G3: `GNStretchingIneq` (CLASSICAL ASSUMPTION about vector fields, true),
    `young_quartic`, `cubicBound_of_GN` (GN ⇒ `EnstrophyCubicBound` with
    `K = 27C⁴/(128ν³)`), `leray_rate_NS_of_GN`.
  * G4: `PoincareIneq` (CLASSICAL ASSUMPTION, true with `Λ = 4π²`),
    `small_data_dissipation`, `enstrophy_deriv_le_of_small`,
    `small_data_enstrophy_bound_from` (`16C⁴‖ω(t₀)‖⁴ < ν⁴Λ` ⇒ `‖ω(t)‖² ≤ ‖ω(t₀)‖²` for
    `t ≥ t₀`), `small_data_enstrophy_bound` (`t₀ = 0`), `blowup_requires_large_data`,
    `blowup_requires_large_data_at` (the data are large at EVERY time), `enstrophy_pos_of_blowup`.
  * G5 (STATEMENTS ONLY): `vortLinfT`, `BKMBlowup` (`∫₀^T ‖ω‖_∞ = ∞`),
    `BKMBlowup.not_bounded`, `not_BKMBlowup_zero` (a non-triviality check),
    `NSBlowupConjecture` (OPEN CONJECTURE, not proved, never used as a hypothesis),
    `EnstrophyBlowupCriterion` (CLASSICAL ASSUMPTION), `BlowupConstraints`,
    `blowup_witness_constraints`, `NSBlowupConjecture.witness_constraints`
    (IF the conjecture holds, its witness satisfies every constraint of G3–G4).
  * H0: `eq_zero_of_integral_cubeQ_eq_zero` (continuous, non-negative, periodic, `∫_Q = 0` ⇒
    identically 0), `volume_real_cubeQ`.
  * H3a: `refl` (`x₃ ↦ −x₃`), `MirrorSymmetric`, `OddSymmetrySpace` (C³, periodic,
    `div = 0`, mirror-symmetric, `∫_Q v = 0`), `OddSymmetrySpace.zero`.
  * H3b: equivariance lemmas (`fderiv`, `lap`, convection, `gradient`, `divergence`) and
    `reflectSol` — the reflection of a solution is again a solution.
  * H3c: `nsUnique` (UNIQUENESS of classical solutions, fully proved: energy of the
    difference + `e^{−2Ms}D(s)` is non-increasing), `mirror_invariant`, `integral_inner_const_eq`
    (conservation of momentum), `mean_zero_invariant`, `oddSymmetry_invariant` (the space is
    invariant under the flow).
  * H3d: `ofReal_norm_le_eLpNorm_top`, `lintegral_div_sub_eq_top`, `bkmBlowup_of_typeI`
    (`‖ω‖_∞ ≥ c/(T − t)` ⇒ `BKMBlowup`).
  * H3e: `lerayScale`, `lerayField`, `curl_lerayField`, `LerayAnsatzNear` (a local ansatz),
    `typeI_of_ansatz`.
  * H3f: `LeraySelfSimilarOddScenario` (OPEN ASSUMPTION, type I) and `NSBlowupConjecture_of_leray`.
  * H3g (type II): `TypeIIScale` (`ℓ²/(T − t) → 0`), `lintegral_inv_sq_eq_top`
    (`∫₀ᵀ ℓ⁻² = ∞`, derived rather than assumed), `ModulatedVortexProfile` (the modulation
    consequence of a spectral gap), `vortLinf_ge_of_modulated`, `bkmBlowup_of_scale`,
    `TypeIIOddScenario` (OPEN ASSUMPTION, scenario A) and `NSBlowupConjecture_of_scenario`.
  * H3h (Euler type): `EulerTypeScale` (`ν(T − t)/ℓ² → 0`), `EulerTypeOddScenario` (OPEN
    ASSUMPTION, scenario B) and `NSBlowupConjecture_of_eulerType`.
  * H4: `toroidalDipoleInit κ = curl A`, `A = h(x₃)(−s₂, s₁, 0)` (a mirror-symmetric pair of
    toroidal vortex rings around `(½, ½, ½)`, axisymmetric to first order). Fully proved:
    `toroidalDipoleInit_smooth` (C^∞), `_periodic`, `_div_free`, `_mean_zero`, `_mirror`,
    `toroidalDipoleInit_mem` (∈ `OddSymmetrySpace`), `toroidalDipoleInit_testPoint`
    (`u₀₃(½, ½, ¼) = 4π(1 − κ)`), `toroidalDipoleInit_ne_zero` (`κ ≠ 1`). General lemmas:
    `mirror_curl_of_anti`, `integral_cubeQ_curl_eq_zero`.
  * H5 (Clay problem (D)): `ClayInitialData`, `ClayForce`, `ClaySmoothSolution`,
    `ClayMillenniumProblemD` (STATEMENT, compared with the printed text: `[VERIFIED: …]` tags),
    `clayForce_zero`, `ClaySmoothSolution.rescale` (scaling `ν ↦ ν/c`),
    `ClaySmoothSolution.exists_periodic_pressure` (normalising the pressure by a Galilean
    change of frame), `nsPeriodicDataOfClay`, `not_BKMBlowup_of_extension` (the easy direction
    of BKM) and `clay_problem_D_of_blowupConjecture`
    (`NSBlowupConjecture ⇒ ClayMillenniumProblemD`: an IMPLICATION, not a solution).
  * No `sorry`, no `axiom`.
-/

import NavierStokesTorus

noncomputable section

open MeasureTheory Set Filter Topology
open scoped RealInnerProductSpace

namespace NavierStokes.Blowup

open NavierStokes.Torus

/-! ## G1. Riccati comparison (pure ODE) -/

/-- **G1.** If `Y` is continuous on `[0, T)`, differentiable on `(0, T)` with `Y' ≥ cY²`
(`c > 0`) and `Y(0) > 0`, then `T ≤ 1/(cY(0))`. In other words, a solution of the Riccati
inequality cannot live beyond time `1/(cY(0))`.
Proof: `Y' ≥ 0`, so `Y ≥ Y(0) > 0`; then `g = 1/Y + ct` has `g' = −Y'/Y² + c ≤ 0`,
hence `0 < 1/Y(t) ≤ 1/Y(0) − ct`, i.e. `t < 1/(cY(0))` for every `t ∈ [0, T)`. -/
theorem riccati_blowup_time {Y Y' : ℝ → ℝ} {c T : ℝ} (hc : 0 < c) (hY0 : 0 < Y 0)
    (hcont : ContinuousOn Y (Ico 0 T))
    (hderiv : ∀ t ∈ Ioo 0 T, HasDerivAt Y (Y' t) t)
    (hineq : ∀ t ∈ Ioo 0 T, c * Y t ^ 2 ≤ Y' t) :
    T ≤ 1 / (c * Y 0) := by
  have hb : 0 < 1 / (c * Y 0) := by positivity
  rcases le_or_gt T 0 with hT | hT
  · exact hT.trans hb.le
  have hint : interior (Ico (0 : ℝ) T) = Ioo 0 T := interior_Ico
  have h0 : (0 : ℝ) ∈ Ico 0 T := ⟨le_rfl, hT⟩
  -- Step 1: `Y` is non-decreasing, so `Y ≥ Y(0) > 0`
  have hmono : MonotoneOn Y (Ico 0 T) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ico 0 T) hcont ?_ ?_
    · rw [hint]
      exact fun t ht => (hderiv t ht).differentiableAt.differentiableWithinAt
    · rw [hint]
      intro t ht
      rw [(hderiv t ht).deriv]
      exact le_trans (by positivity) (hineq t ht)
  have hpos : ∀ t ∈ Ico 0 T, 0 < Y t := fun t ht =>
    lt_of_lt_of_le hY0 (hmono h0 ht ht.1)
  -- Step 2: `g = 1/Y + ct` is non-increasing
  set g : ℝ → ℝ := fun t => (Y t)⁻¹ + c * t with hg
  have hgd : ∀ t ∈ Ioo 0 T, HasDerivAt g (-(Y' t) / Y t ^ 2 + c) t := fun t ht => by
    have h1 := (hderiv t ht).inv (hpos t (Ioo_subset_Ico_self ht)).ne'
    have h2 : HasDerivAt (fun y => c * y) c t := by
      simpa using (hasDerivAt_id t).const_mul c
    exact h1.add h2
  have hanti : AntitoneOn g (Ico 0 T) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ico 0 T) ?_ ?_ ?_
    · exact (hcont.inv₀ fun t ht => (hpos t ht).ne').add
        (continuousOn_const.mul continuousOn_id)
    · rw [hint]
      exact fun t ht => (hgd t ht).differentiableAt.differentiableWithinAt
    · rw [hint]
      intro t ht
      rw [(hgd t ht).deriv]
      have hY2 : 0 < Y t ^ 2 := by have := hpos t (Ioo_subset_Ico_self ht); positivity
      have : c ≤ Y' t / Y t ^ 2 := by rw [le_div_iff₀ hY2]; exact hineq t ht
      rw [neg_div]
      linarith
  -- Step 3: every `t ∈ [0, T)` is smaller than `1/(cY(0))`
  have hlt : ∀ t ∈ Ico 0 T, t < 1 / (c * Y 0) := by
    intro t ht
    have hgt := hanti h0 ht ht.1
    simp only [hg, mul_zero, add_zero] at hgt
    have hinv : 0 < (Y t)⁻¹ := inv_pos.2 (hpos t ht)
    have hct : c * t < (Y 0)⁻¹ := by linarith
    rw [one_div, mul_inv, ← div_eq_inv_mul, lt_div_iff₀ hc]
    linarith
  -- Step 4: conclusion
  by_contra hcon
  exact lt_irrefl _ (hlt _ ⟨hb.le, not_le.1 hcon⟩)

/-! ## G1'. Consequences for Navier–Stokes on `𝕋³` (under an OPEN ASSUMPTION) -/

/-- **OPEN ASSUMPTION — NOT known to be true.** A Riccati lower bound for the growth of
the enstrophy of a solution `F` on the whole interval `(0, T)`:
`c ‖ω‖⁴ ≤ −2ν ∫∇ω:∇ω + 2∫ω·(∇u)ω` (the right-hand side is exactly `d/dt ‖ω‖²` by
`enstrophy_balance`).

Status: what is known is only an UPPER bound of the form `d/dt‖ω‖² ≤ C‖ω‖⁶/ν³`; the vortex
stretching term may be negative and has no lower bound in terms of `‖ω‖`. For small data the
solution is global (Fujita–Kato), so this assumption cannot hold for all data. Finding a
solution that satisfies it on a long enough interval is itself the open problem. -/
def RiccatiLowerBound (F : NSPeriodicData) (c : ℝ) : Prop :=
  ∀ t ∈ Ioo 0 F.T,
    c * enstrophyT F.u t ^ 2 ≤ -2 * F.ν * palinstrophyT F.u t + 2 * stretchingT F.u t

/-- **G1' (conditional).** If a solution `F` satisfies `RiccatiLowerBound F c` (OPEN
ASSUMPTION) and `‖ω(0)‖ > 0`, then its lifespan is bounded: `T ≤ 1/(c‖ω(0)‖²)`. The link
between the assumption and the ODE (the derivative of the enstrophy) is the proved theorem
`enstrophy_balance`, not an assumption. -/
theorem lifespan_le_of_riccati (F : NSPeriodicData) {c : ℝ} (hc : 0 < c)
    (hY0 : 0 < enstrophyT F.u 0) (hR : RiccatiLowerBound F c) :
    F.T ≤ 1 / (c * enstrophyT F.u 0) :=
  riccati_blowup_time hc hY0 F.enstrophy_cont (fun _ ht => F.enstrophy_balance ht) hR

/-! ## G2. A cubic upper bound: lower bound on the lifespan and Leray-type blow-up rate -/

/-- **G2a.** If `Y > 0` is continuous on `[0, T)` and `Y' ≤ KY³` on `(0, T)`, then
`h(t) = 1/Y(t)² + 2Kt` is non-decreasing on `[0, T)` (since `h' = −2Y'/Y³ + 2K ≥ 0`). -/
lemma cubic_monotone {Y Y' : ℝ → ℝ} {K T : ℝ}
    (hpos : ∀ t ∈ Ico 0 T, 0 < Y t) (hcont : ContinuousOn Y (Ico 0 T))
    (hderiv : ∀ t ∈ Ioo 0 T, HasDerivAt Y (Y' t) t)
    (hineq : ∀ t ∈ Ioo 0 T, Y' t ≤ K * Y t ^ 3) :
    MonotoneOn (fun t => (Y t ^ 2)⁻¹ + 2 * K * t) (Ico 0 T) := by
  have hint : interior (Ico (0 : ℝ) T) = Ioo 0 T := interior_Ico
  have hhd : ∀ t ∈ Ioo 0 T, HasDerivAt (fun t => (Y t ^ 2)⁻¹ + 2 * K * t)
      (-(2 * Y t * Y' t) / (Y t ^ 2) ^ 2 + 2 * K) t := fun t ht => by
    have hYt := hpos t (Ioo_subset_Ico_self ht)
    have h1 := ((hderiv t ht).pow 2).inv (pow_ne_zero 2 hYt.ne')
    have h2 : HasDerivAt (fun y => 2 * K * y) (2 * K) t := by
      simpa using (hasDerivAt_id t).const_mul (2 * K)
    convert h1.add h2 using 1
    simp only [Pi.pow_apply, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
  refine monotoneOn_of_deriv_nonneg (convex_Ico 0 T) ?_ ?_ ?_
  · exact ((hcont.pow 2).inv₀ fun t ht => pow_ne_zero 2 (hpos t ht).ne').add
      (continuousOn_const.mul continuousOn_id)
  · rw [hint]
    exact fun t ht => (hhd t ht).differentiableAt.differentiableWithinAt
  · rw [hint]
    intro t ht
    rw [(hhd t ht).deriv]
    have hYt := hpos t (Ioo_subset_Ico_self ht)
    have hY4 : 0 < (Y t ^ 2) ^ 2 := by positivity
    have key : 2 * Y t * Y' t ≤ 2 * K * (Y t ^ 2) ^ 2 :=
      calc 2 * Y t * Y' t ≤ 2 * Y t * (K * Y t ^ 3) :=
            mul_le_mul_of_nonneg_left (hineq t ht) (by positivity)
        _ = 2 * K * (Y t ^ 2) ^ 2 := by ring
    have : 2 * Y t * Y' t / (Y t ^ 2) ^ 2 ≤ 2 * K := by rw [div_le_iff₀ hY4]; exact key
    rw [neg_div]
    linarith

/-- **G2b (explicit upper bound).** Under the hypotheses of G2a: `1/Y(t)² ≥ 1/Y(0)² − 2Kt`
on `[0, T)`. In particular `Y` stays bounded as long as `2KY(0)² t < 1`. -/
theorem cubic_bound {Y Y' : ℝ → ℝ} {K T : ℝ} (hT : 0 < T)
    (hpos : ∀ t ∈ Ico 0 T, 0 < Y t) (hcont : ContinuousOn Y (Ico 0 T))
    (hderiv : ∀ t ∈ Ioo 0 T, HasDerivAt Y (Y' t) t)
    (hineq : ∀ t ∈ Ioo 0 T, Y' t ≤ K * Y t ^ 3) :
    ∀ t ∈ Ico 0 T, (Y 0 ^ 2)⁻¹ - 2 * K * t ≤ (Y t ^ 2)⁻¹ := by
  intro t ht
  have h := cubic_monotone hpos hcont hderiv hineq ⟨le_rfl, hT⟩ ht ht.1
  simp only [mul_zero, add_zero] at h
  linarith

/-- **G2c (Leray-type blow-up rate).** Under the hypotheses of G2a, if `Y(t) → ∞` as
`t → T⁻`, then `Y(s)² ≥ 1/(2K(T − s))`, i.e. `1 ≤ 2K(T − s) Y(s)²`, for every `s ∈ [0, T)`.
Proof: for `s < t < T`, `1/Y(s)² ≤ 1/Y(t)² + 2K(t − s)`; let `t → T⁻`, so `1/Y(t)² → 0`. -/
theorem leray_rate {Y Y' : ℝ → ℝ} {K T : ℝ}
    (hpos : ∀ t ∈ Ico 0 T, 0 < Y t) (hcont : ContinuousOn Y (Ico 0 T))
    (hderiv : ∀ t ∈ Ioo 0 T, HasDerivAt Y (Y' t) t)
    (hineq : ∀ t ∈ Ioo 0 T, Y' t ≤ K * Y t ^ 3)
    (hblow : Tendsto Y (𝓝[<] T) atTop) :
    ∀ s ∈ Ico 0 T, 1 ≤ 2 * K * (T - s) * Y s ^ 2 := by
  intro s hs
  have hmono := cubic_monotone hpos hcont hderiv hineq
  have h1 : Tendsto (fun t => (Y t ^ 2)⁻¹) (𝓝[<] T) (𝓝 0) :=
    tendsto_inv_atTop_zero.comp ((tendsto_pow_atTop two_ne_zero).comp hblow)
  have h2 : Tendsto (fun t => 2 * K * (t - s)) (𝓝[<] T) (𝓝 (2 * K * (T - s))) :=
    ((continuous_const.mul (continuous_id.sub continuous_const)).tendsto T).mono_left
      nhdsWithin_le_nhds
  have hlim := h1.add h2
  rw [zero_add] at hlim
  have hev : ∀ᶠ t in 𝓝[<] T, (Y s ^ 2)⁻¹ ≤ (Y t ^ 2)⁻¹ + 2 * K * (t - s) := by
    filter_upwards [Ioo_mem_nhdsLT hs.2] with t ht
    have := hmono hs ⟨hs.1.trans ht.1.le, ht.2⟩ ht.1.le
    simp only at this
    linarith
  have hle := ge_of_tendsto hlim hev
  have hY2 : 0 < Y s ^ 2 := by have := hpos s hs; positivity
  have hm := mul_le_mul_of_nonneg_left hle hY2.le
  rw [mul_inv_cancel₀ hY2.ne'] at hm
  linarith [hm, show Y s ^ 2 * (2 * K * (T - s)) = 2 * K * (T - s) * Y s ^ 2 by ring]

/-- **G2d (lower bound on the lifespan).** Under the hypotheses of G2c, the blow-up time
satisfies `1 ≤ 2K T Y(0)²`, i.e. `T ≥ 1/(2KY(0)²)`: the solution cannot blow up earlier. -/
theorem blowup_time_lower_bound {Y Y' : ℝ → ℝ} {K T : ℝ} (hT : 0 < T)
    (hpos : ∀ t ∈ Ico 0 T, 0 < Y t) (hcont : ContinuousOn Y (Ico 0 T))
    (hderiv : ∀ t ∈ Ioo 0 T, HasDerivAt Y (Y' t) t)
    (hineq : ∀ t ∈ Ioo 0 T, Y' t ≤ K * Y t ^ 3)
    (hblow : Tendsto Y (𝓝[<] T) atTop) :
    1 ≤ 2 * K * T * Y 0 ^ 2 := by
  simpa using leray_rate hpos hcont hderiv hineq hblow 0 ⟨le_rfl, hT⟩

/-! ## G2'. Consequences for Navier–Stokes on `𝕋³` -/

/-- **CLASSICAL ASSUMPTION (true, but not formalised here).** A cubic upper bound for the
growth of the enstrophy: `d/dt ‖ω‖² ≤ K ‖ω‖⁶`. In the literature this follows from the estimate
`|∫ω·(∇u)ω| ≤ C‖ω‖^{3/2}‖∇ω‖^{3/2}` (Gagliardo–Nirenberg/Sobolev on `𝕋³`) together with Young,
with `K = C'/ν³`. Stage G3 derives it from a named Gagliardo–Nirenberg assumption.
DIFFERENT from `RiccatiLowerBound`: this is known to be true, not an open assumption. -/
def EnstrophyCubicBound (F : NSPeriodicData) (K : ℝ) : Prop :=
  ∀ t ∈ Ioo 0 F.T,
    -2 * F.ν * palinstrophyT F.u t + 2 * stretchingT F.u t ≤ K * enstrophyT F.u t ^ 3

/-- **G2' (Leray blow-up rate for Navier–Stokes).** If `F` satisfies
`EnstrophyCubicBound F K`, `‖ω‖ > 0` on `[0, T)` and `‖ω(t)‖² → ∞` as `t → T⁻`, then
`‖ω(s)‖⁴ ≥ 1/(2K(T − s))` for every `s ∈ [0, T)`, and `T ≥ 1/(2K‖ω(0)‖⁴)`.
These are NECESSARY CONDITIONS that every blow-up scenario must satisfy. -/
theorem leray_rate_NS (F : NSPeriodicData) {K : ℝ}
    (hpos : ∀ t ∈ Ico 0 F.T, 0 < enstrophyT F.u t) (hB : EnstrophyCubicBound F K)
    (hblow : Tendsto (enstrophyT F.u) (𝓝[<] F.T) atTop) :
    (∀ s ∈ Ico 0 F.T, 1 ≤ 2 * K * (F.T - s) * enstrophyT F.u s ^ 2) ∧
      1 ≤ 2 * K * F.T * enstrophyT F.u 0 ^ 2 :=
  ⟨leray_rate hpos F.enstrophy_cont (fun _ ht => F.enstrophy_balance ht) hB hblow,
    blowup_time_lower_bound F.T_pos hpos F.enstrophy_cont
      (fun _ ht => F.enstrophy_balance ht) hB hblow⟩

/-! ## G3. From a Gagliardo–Nirenberg estimate to the cubic bound -/

/-- **CLASSICAL ASSUMPTION (true; Mathlib does not yet have the infrastructure): a
Gagliardo–Nirenberg-type vortex stretching estimate on `𝕋³`.** For every C³, periodic,
divergence-free field `v` with `ω = curl v`:
`|∫_Q ω·(∇v)ω| ≤ C ‖ω‖^{3/2}_{L²} ‖∇ω‖^{3/2}_{L²}`,
written as `C (∫|ω|²)^{3/4} (∫∇ω:∇ω)^{3/4}`.
In the literature: Hölder `|∫ω·(∇v)ω| ≤ ‖ω‖²_{L³}‖∇v‖_{L³}`, Calderón–Zygmund
`‖∇v‖_{L³} ≲ ‖ω‖_{L³}`, then Gagliardo–Nirenberg `‖ω‖_{L³} ≲ ‖ω‖^{1/2}‖∇ω‖^{1/2}` for
mean-zero fields (`ω = curl v` has mean zero by A4).
It is a purely functional inequality about vector fields and does not mention Navier–Stokes
(of the same kind as `AgmonInequality` in the original file). -/
def GNStretchingIneq (C : ℝ) : Prop :=
  ∀ v : E3 → E3, ContDiff ℝ 3 v → IsPeriodic3 v → (∀ x, divergence v x = 0) →
    |∫ x in cubeQ, ⟪curl v x, fderiv ℝ v x (curl v x)⟫|
      ≤ C * (∫ x in cubeQ, ‖curl v x‖ ^ 2) ^ (3 / 4 : ℝ)
        * (∫ x in cubeQ, gradDot (curl v) (curl v) x) ^ (3 / 4 : ℝ)

/-- **G3b (quartic Young).** `−2νy⁴ + 2ay³ ≤ 27a⁴/(128ν³)` for all real `a, y` and `ν > 0`.
Proof: `27a⁴ − 256ab³ + 256b⁴ = (4b − 3a)²((4b + a)² + 2a²) ≥ 0` with `b = νy`.
The constant is optimal (equality at `νy = 3a/4`). -/
lemma young_quartic {ν : ℝ} (hν : 0 < ν) (a y : ℝ) :
    -2 * ν * y ^ 4 + 2 * a * y ^ 3 ≤ 27 * a ^ 4 / (128 * ν ^ 3) := by
  rw [le_div_iff₀ (by positivity)]
  have hq : 0 ≤ 16 * (ν * y) ^ 2 + 8 * a * (ν * y) + 3 * a ^ 2 := by
    nlinarith [sq_nonneg (4 * (ν * y) + a), sq_nonneg a]
  nlinarith [mul_nonneg (sq_nonneg (4 * (ν * y) - 3 * a)) hq]

/-- **G3c.** The Gagliardo–Nirenberg estimate (CLASSICAL ASSUMPTION) implies the cubic bound
`d/dt ‖ω‖² ≤ (27C⁴/(128ν³)) ‖ω‖⁶` for every `NSPeriodicData` solution. -/
theorem cubicBound_of_GN {C : ℝ} (hGN : GNStretchingIneq C) (F : NSPeriodicData) :
    EnstrophyCubicBound F (27 * C ^ 4 / (128 * F.ν ^ 3)) := by
  intro t ht
  have ht' := Ioo_subset_Ico_self ht
  set Y := enstrophyT F.u t with hYdef
  set P := palinstrophyT F.u t with hPdef
  set S := stretchingT F.u t with hSdef
  have hY : 0 ≤ Y := enstrophyT_nonneg _ _
  have hP : 0 ≤ P := palinstrophyT_nonneg _ _
  -- apply GN to `v = u(t)`
  have hS : |S| ≤ C * Y ^ (3 / 4 : ℝ) * P ^ (3 / 4 : ℝ) := by
    have h := hGN (F.u t) (F.regular ht') (F.u_periodic t ht') (F.div_free t ht')
    rw [hYdef, enstrophyT_eq]
    exact h
  -- change of variables `y = P^{1/4}`, `a = C Y^{3/4}`
  set y := P ^ (1 / 4 : ℝ) with hy
  set a := C * Y ^ (3 / 4 : ℝ) with ha
  have hy4 : y ^ 4 = P := by rw [hy, ← Real.rpow_natCast, ← Real.rpow_mul hP]; norm_num
  have hy3 : y ^ 3 = P ^ (3 / 4 : ℝ) := by
    rw [hy, ← Real.rpow_natCast, ← Real.rpow_mul hP]; norm_num
  have ha4 : a ^ 4 = C ^ 4 * Y ^ 3 := by
    rw [ha, mul_pow, ← Real.rpow_natCast (Y ^ (3 / 4 : ℝ)), ← Real.rpow_mul hY]
    norm_num
  have hSle : S ≤ a * y ^ 3 := by
    rw [hy3, ha]
    exact (le_abs_self S).trans hS
  have hyoung := young_quartic F.ν_pos a y
  rw [hy4, ha4] at hyoung
  calc -2 * F.ν * P + 2 * S ≤ -2 * F.ν * P + 2 * (a * y ^ 3) := by linarith
    _ ≤ 27 * (C ^ 4 * Y ^ 3) / (128 * F.ν ^ 3) := by linarith
    _ = 27 * C ^ 4 / (128 * F.ν ^ 3) * Y ^ 3 := by ring

/-- **G3d (Leray blow-up rate, under the Gagliardo–Nirenberg assumption only).** If
`GNStretchingIneq C` holds, `‖ω‖ > 0` on `[0, T)` and `‖ω(t)‖² → ∞` as `t → T⁻`, then
`‖ω(s)‖⁴ ≥ 64ν³ / (27C⁴(T − s))` for every `s`, and `T ≥ 64ν³ / (27C⁴‖ω(0)‖⁴)`
(written without division: `1 ≤ 2K(T − s)‖ω(s)‖⁴` with `K = 27C⁴/(128ν³)`). -/
theorem leray_rate_NS_of_GN {C : ℝ} (hGN : GNStretchingIneq C) (F : NSPeriodicData)
    (hpos : ∀ t ∈ Ico 0 F.T, 0 < enstrophyT F.u t)
    (hblow : Tendsto (enstrophyT F.u) (𝓝[<] F.T) atTop) :
    (∀ s ∈ Ico 0 F.T,
        1 ≤ 2 * (27 * C ^ 4 / (128 * F.ν ^ 3)) * (F.T - s) * enstrophyT F.u s ^ 2) ∧
      1 ≤ 2 * (27 * C ^ 4 / (128 * F.ν ^ 3)) * F.T * enstrophyT F.u 0 ^ 2 :=
  leray_rate_NS F hpos (cubicBound_of_GN hGN F) hblow

/-! ## G4. Small data: the enstrophy does not grow (blow-up must come from large data) -/

/-- **CLASSICAL ASSUMPTION (true with `Λ = 4π²`; Mathlib does not yet have the
infrastructure): a Poincaré inequality for the vorticity on `𝕋³`.** For every C³, periodic,
divergence-free field `v`:
`Λ ∫_Q |curl v|² ≤ ∫_Q ∇(curl v) : ∇(curl v)`.
In the literature: `ω = curl v` has mean zero (by A4), so Poincaré–Wirtinger (via Fourier
series) gives `Λ = 4π²` on the unit torus. -/
def PoincareIneq (Λ : ℝ) : Prop :=
  ∀ v : E3 → E3, ContDiff ℝ 3 v → IsPeriodic3 v → (∀ x, divergence v x = 0) →
    Λ * ∫ x in cubeQ, ‖curl v x‖ ^ 2 ≤ ∫ x in cubeQ, gradDot (curl v) (curl v) x

/-- **G4b (algebra).** If `ΛY ≤ P`, `|S| ≤ C Y^{3/4} P^{3/4}` and `16C⁴Y² ≤ ν⁴Λ`, then the
viscous term absorbs half of the stretching term: `−2νP + 2S ≤ −νP`.
Proof: with `z = Y^{1/4}, y = P^{1/4}`, `(2Cz³y³)⁴ = 16C⁴Y² · Y y¹² ≤ ν⁴ ΛY y¹² ≤ (νy⁴)⁴`. -/
lemma small_data_dissipation {ν Λ C Y P S : ℝ} (hν : 0 < ν) (hC : 0 ≤ C) (hY : 0 ≤ Y)
    (hP : 0 ≤ P) (hPo : Λ * Y ≤ P) (hS : |S| ≤ C * Y ^ (3 / 4 : ℝ) * P ^ (3 / 4 : ℝ))
    (hsmall : 16 * C ^ 4 * Y ^ 2 ≤ ν ^ 4 * Λ) :
    -2 * ν * P + 2 * S ≤ -ν * P := by
  obtain ⟨z, hz⟩ : ∃ z, z = Y ^ (1 / 4 : ℝ) := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y, y = P ^ (1 / 4 : ℝ) := ⟨_, rfl⟩
  have hz0 : 0 ≤ z := hz ▸ Real.rpow_nonneg hY _
  have hy0 : 0 ≤ y := hy ▸ Real.rpow_nonneg hP _
  have hz4 : z ^ 4 = Y := by rw [hz, ← Real.rpow_natCast, ← Real.rpow_mul hY]; norm_num
  have hy4 : y ^ 4 = P := by rw [hy, ← Real.rpow_natCast, ← Real.rpow_mul hP]; norm_num
  have hz3 : z ^ 3 = Y ^ (3 / 4 : ℝ) := by
    rw [hz, ← Real.rpow_natCast, ← Real.rpow_mul hY]; norm_num
  have hy3 : y ^ 3 = P ^ (3 / 4 : ℝ) := by
    rw [hy, ← Real.rpow_natCast, ← Real.rpow_mul hP]; norm_num
  have key : (2 * C * z ^ 3 * y ^ 3) ^ 4 ≤ (ν * y ^ 4) ^ 4 := by
    have e1 : (2 * C * z ^ 3 * y ^ 3) ^ 4 = (16 * C ^ 4 * Y ^ 2) * (Y * y ^ 12) := by
      rw [← hz4]; ring
    have e2 : (ν * y ^ 4) ^ 4 = ν ^ 4 * (P * y ^ 12) := by rw [← hy4]; ring
    rw [e1, e2]
    calc (16 * C ^ 4 * Y ^ 2) * (Y * y ^ 12) ≤ (ν ^ 4 * Λ) * (Y * y ^ 12) :=
          mul_le_mul_of_nonneg_right hsmall (by positivity)
      _ = ν ^ 4 * ((Λ * Y) * y ^ 12) := by ring
      _ ≤ ν ^ 4 * (P * y ^ 12) := by gcongr
  have h2 := (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num)).1 key
  have hSle : S ≤ C * z ^ 3 * y ^ 3 := by
    rw [hz3, hy3]
    exact (le_abs_self S).trans hS
  rw [← hy4]
  nlinarith [h2, hSle]

/-- Under GN and Poincaré, at a time `s` with `16C⁴‖ω(s)‖⁴ ≤ ν⁴Λ`:
`d/dt ‖ω‖² ≤ −νΛ ‖ω‖²`. -/
lemma enstrophy_deriv_le_of_small (F : NSPeriodicData) {C Λ : ℝ} (hC : 0 ≤ C)
    (hGN : GNStretchingIneq C) (hPo : PoincareIneq Λ) {s : ℝ} (hs : s ∈ Ioo 0 F.T)
    (hsm : 16 * C ^ 4 * enstrophyT F.u s ^ 2 ≤ F.ν ^ 4 * Λ) :
    -2 * F.ν * palinstrophyT F.u s + 2 * stretchingT F.u s
      ≤ -(F.ν * Λ) * enstrophyT F.u s := by
  have hs' := Ioo_subset_Ico_self hs
  have hPo' : Λ * enstrophyT F.u s ≤ palinstrophyT F.u s := by
    have h := hPo (F.u s) (F.regular hs') (F.u_periodic s hs') (F.div_free s hs')
    rw [enstrophyT_eq]
    exact h
  have hGN' : |stretchingT F.u s|
      ≤ C * enstrophyT F.u s ^ (3 / 4 : ℝ) * palinstrophyT F.u s ^ (3 / 4 : ℝ) := by
    have h := hGN (F.u s) (F.regular hs') (F.u_periodic s hs') (F.div_free s hs')
    rw [enstrophyT_eq]
    exact h
  have h := small_data_dissipation F.ν_pos hC (enstrophyT_nonneg _ _)
    (palinstrophyT_nonneg _ _) hPo' hGN' hsm
  have hm := mul_le_mul_of_nonneg_left hPo' F.ν_pos.le
  linarith

/-- **G4c (small data, from an arbitrary time).** Under `GNStretchingIneq C` and
`PoincareIneq Λ` (CLASSICAL ASSUMPTIONS), if `16C⁴‖ω(t₀)‖⁴ < ν⁴Λ` at some `t₀ ∈ [0, T)`, then
`‖ω(t)‖² ≤ ‖ω(t₀)‖²` for every `t ∈ [t₀, T)`, independently of the lifespan `T`.
Proof: a barrier `B ≡ ‖ω(t₀)‖² + η` on `[e, t]` with `t₀ < e` close to `t₀`; at a touching
point the smallness condition still holds, so `d/dt ‖ω‖² ≤ −νΛ(‖ω(t₀)‖² + η) < 0`; then let
`η → 0⁺`. -/
theorem small_data_enstrophy_bound_from {C Λ : ℝ} (hC : 0 ≤ C) (hΛ : 0 < Λ)
    (hGN : GNStretchingIneq C) (hPo : PoincareIneq Λ) (F : NSPeriodicData)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ico 0 F.T)
    (hsmall : 16 * C ^ 4 * enstrophyT F.u t₀ ^ 2 < F.ν ^ 4 * Λ) :
    ∀ t ∈ Ico t₀ F.T, enstrophyT F.u t ≤ enstrophyT F.u t₀ := by
  intro t ht
  rcases eq_or_lt_of_le ht.1 with h0 | htpos
  · rw [← h0]
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  -- choose `η ∈ (0, ε)` so that the smallness condition still holds at `‖ω(t₀)‖² + η`
  have hcη : Tendsto (fun η : ℝ => 16 * C ^ 4 * (enstrophyT F.u t₀ + η) ^ 2) (𝓝[>] 0)
      (𝓝 (16 * C ^ 4 * (enstrophyT F.u t₀ + 0) ^ 2)) :=
    ((continuous_const.mul ((continuous_const.add continuous_id).pow 2)).tendsto 0).mono_left
      nhdsWithin_le_nhds
  rw [add_zero] at hcη
  obtain ⟨η, ⟨hηsm, hηε⟩, hηpos⟩ := (((hcη.eventually_lt_const hsmall).and
    (Ioo_mem_nhdsGT hε)).and self_mem_nhdsWithin).exists
  have hηpos : 0 < η := hηpos
  -- choose `e ∈ (t₀, t)` with `‖ω(e)‖² < ‖ω(t₀)‖² + η` (right continuity at `t₀`)
  have hIco : Ico 0 F.T ∈ 𝓝[>] t₀ :=
    mem_of_superset (Ioo_mem_nhdsGT ht₀.2) fun x hx => ⟨ht₀.1.trans hx.1.le, hx.2⟩
  have hY : Tendsto (enstrophyT F.u) (𝓝[>] t₀) (𝓝 (enstrophyT F.u t₀)) :=
    (F.enstrophy_cont t₀ ht₀).tendsto.mono_left (nhdsWithin_le_of_mem hIco)
  obtain ⟨e, hey, he⟩ := ((hY.eventually_lt_const (lt_add_of_pos_right _ hηpos)).and
    (Ioo_mem_nhdsGT htpos)).exists
  have he0 : 0 < e := lt_of_le_of_lt ht₀.1 he.1
  -- the barrier on `[e, t]`
  have hsubI : Icc e t ⊆ Ico 0 F.T := fun x hx => ⟨he0.le.trans hx.1, hx.2.trans_lt ht.2⟩
  have hbar := image_le_of_deriv_right_lt_deriv_boundary' (f := enstrophyT F.u)
    (f' := fun s => -2 * F.ν * palinstrophyT F.u s + 2 * stretchingT F.u s)
    (B := fun _ => enstrophyT F.u t₀ + η) (B' := fun _ => 0)
    (F.enstrophy_cont.mono hsubI)
    (fun x hx => (F.enstrophy_balance ⟨he0.trans_le hx.1, hx.2.trans ht.2⟩).hasDerivWithinAt)
    hey.le continuousOn_const (fun x _ => hasDerivWithinAt_const _ _ _)
    (fun x hx hxB => by
      have hxs : x ∈ Ioo 0 F.T := ⟨he0.trans_le hx.1, hx.2.trans ht.2⟩
      have hsm : 16 * C ^ 4 * enstrophyT F.u x ^ 2 ≤ F.ν ^ 4 * Λ := by
        rw [hxB]; exact hηsm.le
      have hd := enstrophy_deriv_le_of_small F hC hGN hPo hxs hsm
      have hY0 : 0 ≤ enstrophyT F.u t₀ := enstrophyT_nonneg _ _
      have hpos : 0 < F.ν * Λ * enstrophyT F.u x := by
        rw [hxB]; have := F.ν_pos; positivity
      linarith)
    ⟨he.2.le, le_rfl⟩
  linarith

/-- **G4c (small data).** The case `t₀ = 0` of `small_data_enstrophy_bound_from`: if
`16C⁴‖ω(0)‖⁴ < ν⁴Λ`, then `‖ω(t)‖² ≤ ‖ω(0)‖²` for every `t ∈ [0, T)`. -/
theorem small_data_enstrophy_bound {C Λ : ℝ} (hC : 0 ≤ C) (hΛ : 0 < Λ)
    (hGN : GNStretchingIneq C) (hPo : PoincareIneq Λ) (F : NSPeriodicData)
    (hsmall : 16 * C ^ 4 * enstrophyT F.u 0 ^ 2 < F.ν ^ 4 * Λ) :
    ∀ t ∈ Ico 0 F.T, enstrophyT F.u t ≤ enstrophyT F.u 0 :=
  small_data_enstrophy_bound_from hC hΛ hGN hPo F ⟨le_rfl, F.T_pos⟩ hsmall

/-- **G4d (blow-up must come from large data).** Under GN and Poincaré (CLASSICAL
ASSUMPTIONS), if `‖ω(t)‖² → ∞` as `t → T⁻`, then `ν⁴Λ ≤ 16C⁴‖ω(0)‖⁴`. -/
theorem blowup_requires_large_data {C Λ : ℝ} (hC : 0 ≤ C) (hΛ : 0 < Λ)
    (hGN : GNStretchingIneq C) (hPo : PoincareIneq Λ) (F : NSPeriodicData)
    (hblow : Tendsto (enstrophyT F.u) (𝓝[<] F.T) atTop) :
    F.ν ^ 4 * Λ ≤ 16 * C ^ 4 * enstrophyT F.u 0 ^ 2 := by
  by_contra h
  have hb := small_data_enstrophy_bound hC hΛ hGN hPo F (not_le.1 h)
  obtain ⟨s, hs1, hs2⟩ := ((hblow.eventually_gt_atTop (enstrophyT F.u 0)).and
    (Ioo_mem_nhdsLT F.T_pos)).exists
  exact absurd (hb s ⟨hs2.1.le, hs2.2⟩) (not_le.2 hs1)

/-- **G4e (the data stay large before blow-up).** Under GN and Poincaré, if `‖ω(t)‖² → ∞`
as `t → T⁻`, then `ν⁴Λ ≤ 16C⁴‖ω(s)‖⁴` at EVERY `s ∈ [0, T)`. Otherwise
`small_data_enstrophy_bound_from`, restarted at `s`, would keep `‖ω‖²` bounded on `[s, T)`. -/
theorem blowup_requires_large_data_at {C Λ : ℝ} (hC : 0 ≤ C) (hΛ : 0 < Λ)
    (hGN : GNStretchingIneq C) (hPo : PoincareIneq Λ) (F : NSPeriodicData)
    (hblow : Tendsto (enstrophyT F.u) (𝓝[<] F.T) atTop) :
    ∀ s ∈ Ico 0 F.T, F.ν ^ 4 * Λ ≤ 16 * C ^ 4 * enstrophyT F.u s ^ 2 := by
  intro s hs
  by_contra h
  have hb := small_data_enstrophy_bound_from hC hΛ hGN hPo F hs (not_le.1 h)
  obtain ⟨r, hr1, hr2⟩ := ((hblow.eventually_gt_atTop (enstrophyT F.u s)).and
    (Ioo_mem_nhdsLT hs.2)).exists
  exact absurd (hb r ⟨hr2.1.le, hr2.2⟩) (not_le.2 hr1)

/-- A consequence of G4e: before blow-up, `‖ω(s)‖ > 0` at every `s ∈ [0, T)`. So the
hypothesis `hpos` of G2'/G3d is satisfied automatically. -/
lemma enstrophy_pos_of_blowup {C Λ : ℝ} (hC : 0 ≤ C) (hΛ : 0 < Λ)
    (hGN : GNStretchingIneq C) (hPo : PoincareIneq Λ) (F : NSPeriodicData)
    (hblow : Tendsto (enstrophyT F.u) (𝓝[<] F.T) atTop) :
    ∀ s ∈ Ico 0 F.T, 0 < enstrophyT F.u s := by
  intro s hs
  have h := blowup_requires_large_data_at hC hΛ hGN hPo F hblow s hs
  rcases (enstrophyT_nonneg F.u s).lt_or_eq with h' | h'
  · exact h'
  · exfalso
    rw [← h'] at h
    have : 0 < F.ν ^ 4 * Λ := by have := F.ν_pos; positivity
    norm_num at h
    linarith

/-! ## G5. The blow-up conjecture: STATED ONLY, NOT PROVED -/

section G5

open scoped ENNReal ContDiff

/-- `‖ω(t)‖_{L^∞(𝕋³)}` with values in `ℝ≥0∞`: the essential supremum over `Q`. By
periodicity it equals the essential supremum over `ℝ³`. Values are taken in `ℝ≥0∞` so that the
statement `∫₀^T ‖ω‖_∞ = ∞` makes sense directly, without passing through `toReal`. -/
def vortLinfT (u : ℝ → E3 → E3) (t : ℝ) : ℝ≥0∞ :=
  eLpNorm (vort u t) ⊤ (volume.restrict cubeQ)

/-- **The BKM integral diverges at `T`:** `∫₀^T ‖ω(t)‖_{L^∞} dt = ∞`.
For each `t < T`, `ω(t)` is continuous on the compact `Q`, so `‖ω(t)‖_∞ < ∞`. Hence this
statement says that there is a genuine singularity at `T`: `‖ω‖_∞` is unbounded near `T` (see
`BKMBlowup.not_bounded`), and `F` cannot be continued as a classical solution past `T`. -/
def BKMBlowup (F : NSPeriodicData) : Prop :=
  ∫⁻ t in Ioo 0 F.T, vortLinfT F.u t = ⊤

/-- **G5a.** `BKMBlowup F` implies that `‖ω(t)‖_∞` is not bounded by any finite constant on
`(0, T)`. -/
theorem BKMBlowup.not_bounded {F : NSPeriodicData} (h : BKMBlowup F) (M : ℝ≥0∞)
    (hM : M < ⊤) : ¬ ∀ t ∈ Ioo 0 F.T, vortLinfT F.u t ≤ M := by
  intro hb
  have h1 : ∫⁻ t in Ioo 0 F.T, vortLinfT F.u t ≤ ∫⁻ _ in Ioo 0 F.T, M :=
    setLIntegral_mono measurable_const hb
  rw [setLIntegral_const, Real.volume_Ioo, h] at h1
  exact not_le.2 (ENNReal.mul_lt_top hM ENNReal.ofReal_lt_top) h1

/-- **G5b (non-triviality check).** The zero solution `NSPeriodicData.zero` does NOT satisfy
`BKMBlowup`. So `BKMBlowup` is not a vacuous condition. -/
theorem not_BKMBlowup_zero : ¬ BKMBlowup NSPeriodicData.zero := by
  have h : ∀ t, vortLinfT NSPeriodicData.zero.u t = 0 := by
    intro t
    have hv : vort NSPeriodicData.zero.u t = 0 := by
      funext x
      show curl (fun _ : E3 => (0 : E3)) x = 0
      simp [curl, pd]
    rw [vortLinfT, hv, eLpNorm_zero]
  simp [BKMBlowup, h]

/-- **OPEN CONJECTURE: not proved, and never used as a hypothesis anywhere.**

A blow-up statement for the 3D periodic Navier–Stokes equations without external force. There is
a classical solution `F : NSPeriodicData` on `𝕋³ = ℝ³/ℤ³` such that:
* the initial datum `u(0)` is `C^∞`, periodic and divergence-free (the last two properties are
  built into `NSPeriodicData`);
* the Beale–Kato–Majda integral diverges at the finite time `T* = F.T`, i.e.
  `∫₀^{T*} ‖ω(t)‖_{L^∞} dt = ∞`.

Relation to the Millennium Problem (Fefferman, statement (D), "breakdown on `ℝ³/ℤ³`"): (D)
also allows one to choose an external force `f`. Here `f = 0`, so this statement is STRONGER
than (D). All `ν > 0` are equivalent by scaling, so `ν` is existentially quantified together
with `F`.

Status: OPEN. This file only contains NECESSARY CONDITIONS that a witness would have to satisfy
(`blowup_witness_constraints`). -/
def NSBlowupConjecture : Prop :=
  ∃ F : NSPeriodicData, ContDiff ℝ ∞ (F.u 0) ∧ BKMBlowup F

/-- **CLASSICAL ASSUMPTION (true, not yet formalised): the enstrophy blow-up criterion.**
If the BKM integral diverges at `T`, then `‖ω(t)‖²_{L²} → ∞` as `t → T⁻`.
In the literature:
* a classical solution coincides with the unique strong solution starting from `u(0) ∈ H¹`;
* the strong solution is smooth for `t > 0`, so `T` is also the singular time of the strong
  solution;
* Leray (1934) gives `‖∇u(t)‖_{L²} ≥ c (T − t)^{-1/4}`;
* `‖∇u‖_{L²} = ‖ω‖_{L²}` when `div u = 0` (A7).

DIFFERENT from `NSBlowupConjecture`: this is known to be true, not an open conjecture. -/
def EnstrophyBlowupCriterion : Prop :=
  ∀ F : NSPeriodicData, BKMBlowup F → Tendsto (enstrophyT F.u) (𝓝[<] F.T) atTop

/-- The three constraints of G3–G4 for a solution `F`, with `K = 27C⁴/(128ν³)`:
1. `‖ω(t)‖² → ∞` as `t → T⁻`;
2. the data stay large: `ν⁴Λ ≤ 16C⁴‖ω(s)‖⁴` for every `s`;
3. the Leray rate `1 ≤ 2K(T − s)‖ω(s)‖⁴` and the lifespan bound `1 ≤ 2KT‖ω(0)‖⁴`. -/
def BlowupConstraints (C Λ : ℝ) (F : NSPeriodicData) : Prop :=
  Tendsto (enstrophyT F.u) (𝓝[<] F.T) atTop ∧
    (∀ s ∈ Ico 0 F.T, F.ν ^ 4 * Λ ≤ 16 * C ^ 4 * enstrophyT F.u s ^ 2) ∧
    (∀ s ∈ Ico 0 F.T,
        1 ≤ 2 * (27 * C ^ 4 / (128 * F.ν ^ 3)) * (F.T - s) * enstrophyT F.u s ^ 2) ∧
    1 ≤ 2 * (27 * C ^ 4 / (128 * F.ν ^ 3)) * F.T * enstrophyT F.u 0 ^ 2

/-- **G5c (necessary conditions for a blow-up witness).** Assume the three CLASSICAL
ASSUMPTIONS `GNStretchingIneq C`, `PoincareIneq Λ` and `EnstrophyBlowupCriterion`. Then every
solution `F` whose BKM integral diverges satisfies `BlowupConstraints C Λ F`.
The hypothesis `‖ω‖ > 0` of G3d is no longer needed, since it follows from G4e. -/
theorem blowup_witness_constraints {C Λ : ℝ} (hC : 0 ≤ C) (hΛ : 0 < Λ)
    (hGN : GNStretchingIneq C) (hPo : PoincareIneq Λ) (hcrit : EnstrophyBlowupCriterion)
    (F : NSPeriodicData) (hF : BKMBlowup F) : BlowupConstraints C Λ F := by
  have hblow := hcrit F hF
  exact ⟨hblow, blowup_requires_large_data_at hC hΛ hGN hPo F hblow,
    leray_rate_NS_of_GN hGN F (enstrophy_pos_of_blowup hC hΛ hGN hPo F hblow) hblow⟩

/-- **G5d.** IF `NSBlowupConjecture` holds (which is still OPEN), then its witness must
satisfy every constraint of G3–G4. This theorem is only a bridge and says nothing about whether
the conjecture is true or false. -/
theorem NSBlowupConjecture.witness_constraints {C Λ : ℝ} (hC : 0 ≤ C) (hΛ : 0 < Λ)
    (hGN : GNStretchingIneq C) (hPo : PoincareIneq Λ) (hcrit : EnstrophyBlowupCriterion)
    (h : NSBlowupConjecture) :
    ∃ F : NSPeriodicData, ContDiff ℝ ∞ (F.u 0) ∧ BKMBlowup F ∧ BlowupConstraints C Λ F := by
  obtain ⟨F, hs, hF⟩ := h
  exact ⟨F, hs, hF, blowup_witness_constraints hC hΛ hGN hPo hcrit F hF⟩

end G5

/-! ## H0. Periodic functions with zero integral over `Q` -/

/-- Translation by an integer multiple of `e_j`: `f (x − n e_j) = f x`. -/
lemma periodicIn_sub_int_smul {F : Type*} {f : E3 → F} {j : Fin 3} (h : PeriodicIn j f)
    (n : ℤ) (x : E3) : f (x - (n : ℝ) • basisVec j) = f x := by
  have hp : Function.Periodic (fun s : ℝ => f (x + s • basisVec j)) 1 := fun s => by
    simp only [add_smul, one_smul, ← add_assoc]
    exact h _
  have h' := hp.sub_int_mul_eq (x := 0) n
  simpa [sub_eq_add_neg, neg_smul] using h'

/-- Every point of `E3` can be translated by an integer vector into `Q` (take `Int.fract`
of each coordinate). -/
lemma exists_mem_cubeQ_of_periodic {F : Type*} {f : E3 → F} (hf : IsPeriodic3 f) (x : E3) :
    ∃ y ∈ cubeQ, f x = f y := by
  set y : E3 := x - ∑ j, ((⌊x j⌋ : ℤ) : ℝ) • basisVec j with hy
  have hc : ∀ i, y i = Int.fract (x i) := fun i => by
    rw [Int.fract]
    fin_cases i <;> simp [hy, basisVec, Fin.sum_univ_three]
  refine ⟨y, ?_, ?_⟩
  · refine ⟨fun i => ?_, fun i => ?_⟩
    · show (0 : ℝ) ≤ y i
      rw [hc]; exact Int.fract_nonneg _
    · show y i ≤ 1
      rw [hc]; exact (Int.fract_lt_one _).le
  · rw [hy, Fin.sum_univ_three, sub_add_eq_sub_sub, sub_add_eq_sub_sub,
      periodicIn_sub_int_smul (hf 2), periodicIn_sub_int_smul (hf 1),
      periodicIn_sub_int_smul (hf 0)]

/-- **H0.** A continuous, non-negative, periodic function `f` with `∫_Q f = 0` vanishes
identically on `E3`.
Proof: `f = 0` a.e. on `Q`, hence `f = 0` on the open cube `(0,1)³` (open sets have positive
measure); by closure `f = 0` on `Q`; then translate by integer vectors. -/
lemma eq_zero_of_integral_cubeQ_eq_zero {f : E3 → ℝ} (hf : Continuous f) (h0 : ∀ x, 0 ≤ f x)
    (hp : IsPeriodic3 f) (hI : ∫ x in cubeQ, f x = 0) : ∀ x, f x = 0 := by
  have hae : f =ᵐ[volume.restrict cubeQ] 0 :=
    (setIntegral_eq_zero_iff_of_nonneg_ae (Eventually.of_forall h0)
      (integrableOn_cubeQ hf)).1 hI
  set S : Set E3 := WithLp.ofLp ⁻¹' (univ.pi fun _ : Fin 3 => Ioo (0 : ℝ) 1) with hSdef
  have hSo : IsOpen S :=
    (isOpen_set_pi finite_univ fun _ _ => isOpen_Ioo).preimage (PiLp.continuous_ofLp 2 _)
  have hSQ : S ⊆ cubeQ := fun x hx => by
    rw [cubeQ, mem_preimage, ← pi_univ_Icc]
    exact fun i _ => Ioo_subset_Icc_self (hx i trivial)
  have hS : EqOn f 0 S :=
    Measure.eqOn_open_of_ae_eq (μ := volume) (ae_restrict_of_ae_restrict_of_subset hSQ hae)
      hSo hf.continuousOn continuousOn_const
  have hcl : cubeQ ⊆ closure S := by
    have h := (EuclideanSpace.equiv (Fin 3) ℝ).toHomeomorph.preimage_closure
      (univ.pi fun _ : Fin 3 => Ioo (0 : ℝ) 1)
    rw [closure_pi_set] at h
    simp only [closure_Ioo (zero_ne_one' ℝ), pi_univ_Icc] at h
    intro x hx
    have hx' : x ∈ (EuclideanSpace.equiv (Fin 3) ℝ).toHomeomorph ⁻¹'
        Icc (fun _ => (0 : ℝ)) fun _ => 1 := hx
    rw [h] at hx'
    exact hx'
  have hQ : EqOn f 0 cubeQ := fun x hx => (hS.closure hf continuous_const) (hcl hx)
  intro x
  obtain ⟨y, hy, hxy⟩ := exists_mem_cubeQ_of_periodic hp x
  rw [hxy]
  exact hQ hy

/-- The volume of `Q` is 1. -/
lemma volume_real_cubeQ : volume.real cubeQ = 1 := by
  rw [measureReal_def, cubeQ,
    (PiLp.volume_preserving_ofLp (Fin 3)).measure_preimage measurableSet_Icc.nullMeasurableSet,
    Real.volume_Icc_pi]
  simp

/-! ## H3a. The mirror reflection `x₃ ↦ −x₃` and the odd-symmetry space -/

/-- Sign of the reflection on axis `i`: `−1` on the `x₃` axis (index `2`), `+1` on the other
two. -/
def rsgn (i : Fin 3) : ℝ := if i = 2 then -1 else 1

lemma rsgn_mul_self (i : Fin 3) : rsgn i * rsgn i = 1 := by
  unfold rsgn; split_ifs <;> norm_num

/-- The mirror reflection `σ(x₁, x₂, x₃) = (x₁, x₂, −x₃)`: `σx = x − 2x₃ e₃`. -/
def refl : E3 →L[ℝ] E3 :=
  ContinuousLinearMap.id ℝ E3
    - (2 : ℝ) • (EuclideanSpace.proj (2 : Fin 3) : E3 →L[ℝ] ℝ).smulRight (basisVec 2)

lemma refl_apply_coord (x : E3) (i : Fin 3) : refl x i = rsgn i * x i := by
  fin_cases i <;> simp [refl, rsgn, basisVec]
  ring

lemma refl_refl (x : E3) : refl (refl x) = x := by
  ext i
  rw [refl_apply_coord, refl_apply_coord, ← mul_assoc, rsgn_mul_self, one_mul]

lemma refl_basisVec (j : Fin 3) : refl (basisVec j) = rsgn j • basisVec j := by
  ext i
  rw [refl_apply_coord]
  by_cases h : i = j <;> simp [basisVec, h]

/-- `σ` is self-adjoint: `⟪σa, b⟫ = ⟪a, σb⟫`. -/
lemma inner_refl (a b : E3) : ⟪refl a, b⟫ = ⟪a, refl b⟫ := by
  rw [inner_eq_sum, inner_eq_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [refl_apply_coord, refl_apply_coord]; ring

/-- The reflected field `(Rv)(x) = σ v(σx)`. -/
def reflF (v : E3 → E3) : E3 → E3 := fun x => refl (v (refl x))

/-- **Mirror symmetry across the plane `x₃ = 0`:** `v(σx) = σ v(x)`, i.e. `v₁, v₂` are even
and `v₃` is odd in `x₃`. -/
def MirrorSymmetric (v : E3 → E3) : Prop := ∀ x, v (refl x) = refl (v x)

lemma reflF_eq_self_iff {v : E3 → E3} : reflF v = v ↔ MirrorSymmetric v := by
  constructor
  · intro h x
    have := congrFun h x
    rw [reflF] at this
    rw [← this, refl_refl]
  · intro h
    funext x
    rw [reflF, h, refl_refl]

/-- **The odd-symmetry space** `OddSymmetrySpace`: C³, periodic, divergence-free fields that
are mirror-symmetric across `x₃ = 0` and have total momentum `∫_Q v = 0`. -/
structure OddSymmetrySpace (v : E3 → E3) : Prop where
  smooth : ContDiff ℝ 3 v
  periodic : IsPeriodic3 v
  div_free : ∀ x, divergence v x = 0
  mirror : MirrorSymmetric v
  mean_zero : ∫ x in cubeQ, v x = 0

/-- The field `0` belongs to `OddSymmetrySpace` (the space is non-empty). -/
lemma OddSymmetrySpace.zero : OddSymmetrySpace (fun _ => 0) where
  smooth := contDiff_const
  periodic := fun _ _ => rfl
  div_free := fun x => by simp [divergence, pd]
  mirror := fun x => by simp
  mean_zero := by simp

/-! ## H3b. Navier–Stokes is equivariant under the reflection -/

lemma hasFDerivAt_reflF {v : E3 → E3} {x : E3} (hv : DifferentiableAt ℝ v (refl x)) :
    HasFDerivAt (reflF v) (refl.comp ((fderiv ℝ v (refl x)).comp refl)) x :=
  refl.hasFDerivAt.comp x (hv.hasFDerivAt.comp x refl.hasFDerivAt)

lemma fderiv_reflF_apply {v : E3 → E3} {x : E3} (hv : DifferentiableAt ℝ v (refl x)) (w : E3) :
    fderiv ℝ (reflF v) x w = refl (fderiv ℝ v (refl x) (refl w)) := by
  rw [(hasFDerivAt_reflF hv).fderiv]
  rfl

lemma fderiv_reflF {v : E3 → E3} {x : E3} (hv : DifferentiableAt ℝ v (refl x)) :
    fderiv ℝ (reflF v) x = refl.comp ((fderiv ℝ v (refl x)).comp refl) :=
  (hasFDerivAt_reflF hv).fderiv

lemma differentiable_reflF {v : E3 → E3} (hv : Differentiable ℝ v) :
    Differentiable ℝ (reflF v) := fun _ => (hasFDerivAt_reflF (hv _)).differentiableAt

lemma contDiff_reflF {v : E3 → E3} {n : WithTop ℕ∞} (hv : ContDiff ℝ n v) :
    ContDiff ℝ n (reflF v) :=
  refl.contDiff.comp (hv.comp refl.contDiff)

lemma fderiv_comp_refl_apply {p : E3 → ℝ} {x : E3} (hp : DifferentiableAt ℝ p (refl x))
    (w : E3) : fderiv ℝ (fun y => p (refl y)) x w = fderiv ℝ p (refl x) (refl w) := by
  show fderiv ℝ (p ∘ refl) x w = _
  rw [(hp.hasFDerivAt.comp x refl.hasFDerivAt).fderiv]
  rfl

lemma pd_reflF {v : E3 → E3} {x : E3} (hv : DifferentiableAt ℝ v (refl x)) (j i : Fin 3) :
    pd (reflF v) j i x = rsgn i * rsgn j * pd v j i (refl x) := by
  show (fderiv ℝ (reflF v) x (basisVec j)) i = _
  rw [fderiv_reflF_apply hv, refl_apply_coord, refl_basisVec, map_smul]
  show rsgn i * (rsgn j * (fderiv ℝ v (refl x) (basisVec j)) i) = _
  rw [← mul_assoc]
  rfl

lemma divergence_reflF {v : E3 → E3} (hv : Differentiable ℝ v) (x : E3) :
    divergence (reflF v) x = divergence v (refl x) := by
  unfold divergence
  exact Finset.sum_congr rfl fun i _ => by rw [pd_reflF (hv _), rsgn_mul_self, one_mul]

lemma conv_reflF {v : E3 → E3} {x : E3} (hv : DifferentiableAt ℝ v (refl x)) :
    fderiv ℝ (reflF v) x (reflF v x) = refl (fderiv ℝ v (refl x) (v (refl x))) := by
  rw [fderiv_reflF_apply hv, reflF, refl_refl]

lemma lap_reflF {v : E3 → E3} (hv : ContDiff ℝ 2 v) (x : E3) :
    lap (reflF v) x = refl (lap v (refl x)) := by
  have hv1 : Differentiable ℝ v := hv.differentiable (by norm_num)
  have hG : ∀ j, Differentiable ℝ (fun z => fderiv ℝ v z (basisVec j)) := fun j =>
    ((hv.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const).differentiable
      (by norm_num)
  have hin : ∀ j, (fun y => fderiv ℝ (reflF v) y (basisVec j))
      = rsgn j • reflF (fun z => fderiv ℝ v z (basisVec j)) := fun j => by
    funext y
    rw [fderiv_reflF_apply (hv1 _), refl_basisVec, map_smul, map_smul]
    rfl
  simp only [lap, hin]
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [fderiv_const_smul ((differentiable_reflF (hG j)) x), smul_apply,
    fderiv_reflF_apply (hG j _), refl_basisVec, map_smul, map_smul, smul_smul, rsgn_mul_self,
    one_smul]

lemma gradient_comp_refl {p : E3 → ℝ} {x : E3} (hp : DifferentiableAt ℝ p (refl x)) :
    gradient (fun y => p (refl y)) x = refl (gradient p (refl x)) := by
  refine ext_inner_right ℝ fun w => ?_
  rw [inner_gradient_left, fderiv_comp_refl_apply hp, inner_refl, inner_gradient_left]

lemma periodicIn_sub {F : Type*} {j : Fin 3} {f : E3 → F} (h : PeriodicIn j f) (x : E3) :
    f (x - basisVec j) = f x := by
  have := h (x - basisVec j)
  rw [sub_add_cancel] at this
  exact this.symm

lemma periodic_comp_refl {F : Type*} {f : E3 → F} (hf : IsPeriodic3 f) :
    IsPeriodic3 (fun x => f (refl x)) := fun j x => by
  show f (refl (x + basisVec j)) = f (refl x)
  rw [map_add, refl_basisVec]
  unfold rsgn
  split_ifs
  · rw [neg_one_smul, ← sub_eq_add_neg, periodicIn_sub (hf j)]
  · rw [one_smul, hf j]

lemma periodic_reflF {v : E3 → E3} (hv : IsPeriodic3 v) : IsPeriodic3 (reflF v) := fun j =>
  (periodic_comp_refl hv j).comp refl

/-- **H3b. The reflected solution.** If `(u, p)` is a solution, so is `(σ∘u∘σ, p∘σ)`, with
the same `ν` and `T`. This is the equivariance of the unforced Navier–Stokes equations under the
mirror reflection. -/
def reflectSol (F : NSPeriodicData) : NSPeriodicData where
  T := F.T
  T_pos := F.T_pos
  ν := F.ν
  ν_pos := F.ν_pos
  u := fun t => reflF (F.u t)
  p := fun t y => F.p t (refl y)
  u_periodic := fun t ht => periodic_reflF (F.u_periodic t ht)
  p_periodic := fun t ht => periodic_comp_refl (F.p_periodic t ht)
  smooth := by
    have hm : ContDiff ℝ 3 (fun z : ℝ × E3 => (z.1, refl z.2)) :=
      contDiff_fst.prodMk (refl.contDiff.comp contDiff_snd)
    exact refl.contDiff.comp_contDiffOn
      (F.smooth.comp hm.contDiffOn fun z hz => ⟨hz.1, mem_univ _⟩)
  regular0 := contDiff_reflF F.regular0
  cont_u := by
    have hm : Continuous (fun z : ℝ × E3 => (z.1, refl z.2)) :=
      continuous_fst.prodMk (refl.continuous.comp continuous_snd)
    exact refl.continuous.comp_continuousOn
      (F.cont_u.comp hm.continuousOn fun z hz => ⟨hz.1, mem_univ _⟩)
  cont_grad := by
    have hm : Continuous (fun z : ℝ × E3 => (z.1, refl z.2)) :=
      continuous_fst.prodMk (refl.continuous.comp continuous_snd)
    have h := F.cont_grad.comp hm.continuousOn
      fun z (hz : z ∈ Ico 0 F.T ×ˢ (univ : Set E3)) =>
        (⟨hz.1, mem_univ _⟩ : (z.1, refl z.2) ∈ Ico 0 F.T ×ˢ (univ : Set E3))
    exact (continuousOn_const.clm_comp (h.clm_comp continuousOn_const)).congr
      fun z (hz : z ∈ Ico 0 F.T ×ˢ (univ : Set E3)) =>
        fderiv_reflF (((F.regular hz.1).differentiable (by norm_num)) _)
  p_regular := fun t ht => (F.p_regular t ht).comp refl.contDiff
  div_free := fun t ht x => by
    rw [divergence_reflF ((F.regular ht).differentiable (by norm_num))]
    exact F.div_free t ht _
  momentum := fun t ht x => by
    have hu2 : ContDiff ℝ 2 (F.u t) := (F.regular (Ioo_subset_Ico_self ht)).of_le (by norm_num)
    have hu1 : Differentiable ℝ (F.u t) := hu2.differentiable (by norm_num)
    have hp1 : Differentiable ℝ (F.p t) := (F.p_regular t ht).differentiable (by norm_num)
    have h := refl.hasFDerivAt.comp_hasDerivAt t (F.momentum t ht (refl x))
    refine h.congr_deriv ?_
    rw [lap_reflF hu2, conv_reflF (hu1 _), gradient_comp_refl (hp1 _), map_sub, map_sub,
      map_smul]

@[simp] lemma reflectSol_T (F : NSPeriodicData) : (reflectSol F).T = F.T := rfl
@[simp] lemma reflectSol_ν (F : NSPeriodicData) : (reflectSol F).ν = F.ν := rfl
lemma reflectSol_u (F : NSPeriodicData) (t : ℝ) : (reflectSol F).u t = reflF (F.u t) := rfl

/-! ## H3c. Uniqueness of solutions (an energy estimate for the difference) -/

lemma pd_sub_field {u v : E3 → E3} {x : E3} (hu : DifferentiableAt ℝ u x)
    (hv : DifferentiableAt ℝ v x) (j i : Fin 3) :
    pd (fun y => u y - v y) j i x = pd u j i x - pd v j i x := by
  simp [pd, fderiv_fun_sub hu hv]

lemma divergence_sub_field {u v : E3 → E3} {x : E3} (hu : DifferentiableAt ℝ u x)
    (hv : DifferentiableAt ℝ v x) :
    divergence (fun y => u y - v y) x = divergence u x - divergence v x := by
  unfold divergence
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => pd_sub_field hu hv i i

lemma gradDot_sub_right (w : E3 → E3) {u v : E3 → E3} {x : E3} (hu : DifferentiableAt ℝ u x)
    (hv : DifferentiableAt ℝ v x) :
    gradDot w u x - gradDot w v x = gradDot w (fun y => u y - v y) x := by
  unfold gradDot
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by rw [pd_sub_field hu hv]; ring

lemma continuous_gradDot {u v : E3 → E3} (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 1 v) :
    Continuous (gradDot u v) := by
  unfold gradDot
  exact continuous_finsetSum _ fun j _ => continuous_finsetSum _ fun i _ =>
    (contDiff_pd (m := 0) hu (by norm_num) j i).continuous.mul
      (contDiff_pd (m := 0) hv (by norm_num) j i).continuous

/-- **H3c-1 (energy estimate for the difference).** With `W = u_F − u_G` at time `t`, if
`‖∇u_G(t, x)‖ ≤ M` on `Q`, then `∫_Q 2⟪W, ∂ₜW⟫ ≤ 2M ∫_Q |W|²`.
Proof: viscosity gives `−2ν∫∇W:∇W ≤ 0` (A6a); `∫⟪W, (u_F·∇)W⟫ = 0` (A8); the pressure term
vanishes (A6b, `div W = 0`); the remaining term satisfies `−∫⟪W, (W·∇)u_G⟫ ≤ M∫|W|²`. -/
lemma diff_energy_deriv_le (F G : NSPeriodicData) (hν : F.ν = G.ν) {t M : ℝ}
    (htF : t ∈ Ioo 0 F.T) (htG : t ∈ Ioo 0 G.T)
    (hM : ∀ x ∈ cubeQ, ‖fderiv ℝ (G.u t) x‖ ≤ M) :
    ∫ x in cubeQ, 2 * ⟪F.u t x - G.u t x, F.dtu t x - G.dtu t x⟫
      ≤ 2 * M * ∫ x in cubeQ, ⟪F.u t x - G.u t x, F.u t x - G.u t x⟫ := by
  have htF' := Ioo_subset_Ico_self htF
  have htG' := Ioo_subset_Ico_self htG
  set u := F.u t with hu
  set v := G.u t with hv
  set p := F.p t with hp
  set q := G.p t with hq
  set W : E3 → E3 := fun x => u x - v x with hW
  have hu3 : ContDiff ℝ 3 u := F.regular htF'
  have hv3 : ContDiff ℝ 3 v := G.regular htG'
  have hu2 : ContDiff ℝ 2 u := hu3.of_le (by norm_num)
  have hv2 : ContDiff ℝ 2 v := hv3.of_le (by norm_num)
  have hu1 : ContDiff ℝ 1 u := hu3.of_le (by norm_num)
  have hv1 : ContDiff ℝ 1 v := hv3.of_le (by norm_num)
  have hW1 : ContDiff ℝ 1 W := hu1.sub hv1
  have hud : Differentiable ℝ u := hu1.differentiable (by norm_num)
  have hvd : Differentiable ℝ v := hv1.differentiable (by norm_num)
  have hp1 : ContDiff ℝ 1 p := (F.p_regular t htF).of_le (by norm_num)
  have hq1 : ContDiff ℝ 1 q := (G.p_regular t htG).of_le (by norm_num)
  have hup : IsPeriodic3 u := F.u_periodic t htF'
  have hvp : IsPeriodic3 v := G.u_periodic t htG'
  have hWp : IsPeriodic3 W := fun j x => by
    show u (x + basisVec j) - v (x + basisVec j) = u x - v x
    rw [hup j x, hvp j x]
  have hpp : IsPeriodic3 p := F.p_periodic t htF
  have hqp : IsPeriodic3 q := G.p_periodic t htG
  have hdu : ∀ x, divergence u x = 0 := F.div_free t htF'
  have hdW : ∀ x, divergence W x = 0 := fun x => by
    rw [divergence_sub_field (hud x) (hvd x), hdu x, G.div_free t htG' x, sub_zero]
  have hfW : ∀ x, fderiv ℝ W x = fderiv ℝ u x - fderiv ℝ v x := fun x =>
    fderiv_fun_sub (hud x) (hvd x)
  -- continuous functions
  have cW := hW1.continuous
  have ca1 : Continuous fun x => ⟪W x, lap u x⟫ := cW.inner (continuous_lap hu2)
  have ca2 : Continuous fun x => ⟪W x, lap v x⟫ := cW.inner (continuous_lap hv2)
  have cb : Continuous fun x => ⟪W x, fderiv ℝ W x (u x)⟫ :=
    cW.inner ((hW1.continuous_fderiv (by norm_num)).clm_apply hu1.continuous)
  have cc : Continuous fun x => ⟪W x, fderiv ℝ v x (W x)⟫ :=
    cW.inner ((hv1.continuous_fderiv (by norm_num)).clm_apply cW)
  have hgr : ∀ (r : E3 → ℝ) x, ⟪W x, gradient r x⟫ = fderiv ℝ r x (W x) := fun r x => by
    rw [real_inner_comm, inner_gradient_left]
  have cd1 : Continuous fun x => ⟪W x, gradient p x⟫ := by
    simp_rw [hgr p]; exact (hp1.continuous_fderiv (by norm_num)).clm_apply cW
  have cd2 : Continuous fun x => ⟪W x, gradient q x⟫ := by
    simp_rw [hgr q]; exact (hq1.continuous_fderiv (by norm_num)).clm_apply cW
  -- pointwise identity
  have hpt : ∀ x, ⟪u x - v x, F.dtu t x - G.dtu t x⟫
      = (F.ν * (⟪W x, lap u x⟫ - ⟪W x, lap v x⟫) - ⟪W x, fderiv ℝ W x (u x)⟫
          - (⟪W x, gradient p x⟫ - ⟪W x, gradient q x⟫)) - ⟪W x, fderiv ℝ v x (W x)⟫ :=
    fun x => by
      rw [F.dtu_eq htF x, G.dtu_eq htG x, ← hν, ← hu, ← hv, ← hp, ← hq, hfW x]
      simp only [hW, sub_apply, map_sub, inner_sub_right, inner_smul_right]
      ring
  simp_rw [hpt]
  -- integrate term by term
  have i1 : ∫ x in cubeQ, ⟪W x, lap u x⟫ - ⟪W x, lap v x⟫
      = -∫ x in cubeQ, gradDot W W x := by
    rw [integral_sub (integrableOn_cubeQ ca1) (integrableOn_cubeQ ca2),
      integral_cubeQ_inner_lap hW1 hu2 hWp hup, integral_cubeQ_inner_lap hW1 hv2 hWp hvp,
      neg_sub_neg, ← integral_sub (integrableOn_cubeQ (continuous_gradDot hW1 hv1))
        (integrableOn_cubeQ (continuous_gradDot hW1 hu1))]
    rw [← integral_neg]
    refine setIntegral_congr_fun measurableSet_cubeQ fun x _ => ?_
    rw [← gradDot_sub_right W (hud x) (hvd x)]
    ring
  have i2 : ∫ x in cubeQ, ⟪W x, fderiv ℝ W x (u x)⟫ = 0 :=
    integral_cubeQ_inner_convective_eq_zero hu1 hW1 hup hWp hdu
  have i3 : ∫ x in cubeQ, ⟪W x, gradient p x⟫ - ⟪W x, gradient q x⟫ = 0 := by
    rw [integral_sub (integrableOn_cubeQ cd1) (integrableOn_cubeQ cd2),
      integral_cubeQ_inner_gradient hW1 hp1 hWp hpp, integral_cubeQ_inner_gradient hW1 hq1 hWp hqp]
    simp [hdW]
  have cE : Continuous fun x => F.ν * (⟪W x, lap u x⟫ - ⟪W x, lap v x⟫)
      - ⟪W x, fderiv ℝ W x (u x)⟫ - (⟪W x, gradient p x⟫ - ⟪W x, gradient q x⟫) :=
    ((continuous_const.mul (ca1.sub ca2)).sub cb).sub (cd1.sub cd2)
  have iE : ∫ x in cubeQ, (F.ν * (⟪W x, lap u x⟫ - ⟪W x, lap v x⟫)
      - ⟪W x, fderiv ℝ W x (u x)⟫ - (⟪W x, gradient p x⟫ - ⟪W x, gradient q x⟫))
      = -(F.ν * ∫ x in cubeQ, gradDot W W x) := by
    rw [integral_sub (f := fun x => F.ν * (⟪W x, lap u x⟫ - ⟪W x, lap v x⟫)
        - ⟪W x, fderiv ℝ W x (u x)⟫)
        (g := fun x => ⟪W x, gradient p x⟫ - ⟪W x, gradient q x⟫)
        (integrableOn_cubeQ ((continuous_const.mul (ca1.sub ca2)).sub cb))
        (integrableOn_cubeQ (cd1.sub cd2)),
      integral_sub (f := fun x => F.ν * (⟪W x, lap u x⟫ - ⟪W x, lap v x⟫))
        (integrableOn_cubeQ (continuous_const.mul (ca1.sub ca2))) (integrableOn_cubeQ cb),
      integral_const_mul, i1, i2, i3]
    ring
  -- bound the term `(W·∇)v`
  have iC : -∫ x in cubeQ, ⟪W x, fderiv ℝ v x (W x)⟫
      ≤ M * ∫ x in cubeQ, ⟪W x, W x⟫ := by
    rw [← integral_neg, ← integral_const_mul]
    refine setIntegral_mono_on (integrableOn_cubeQ cc.neg)
      (integrableOn_cubeQ (continuous_const.mul (cW.inner cW))) measurableSet_cubeQ
      fun x hx => ?_
    have h1 : -⟪W x, fderiv ℝ v x (W x)⟫ ≤ ‖W x‖ * ‖fderiv ℝ v x (W x)‖ :=
      (neg_le_abs _).trans (abs_real_inner_le_norm _ _)
    have h2 : ‖fderiv ℝ v x (W x)‖ ≤ M * ‖W x‖ :=
      ((fderiv ℝ v x).le_opNorm (W x)).trans
        (mul_le_mul_of_nonneg_right (hM x hx) (norm_nonneg _))
    rw [real_inner_self_eq_norm_sq]
    calc -⟪W x, fderiv ℝ v x (W x)⟫ ≤ ‖W x‖ * ‖fderiv ℝ v x (W x)‖ := h1
      _ ≤ ‖W x‖ * (M * ‖W x‖) := mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
      _ = M * ‖W x‖ ^ 2 := by ring
  have hP : 0 ≤ ∫ x in cubeQ, gradDot W W x :=
    setIntegral_nonneg measurableSet_cubeQ fun x _ => gradDot_self_nonneg _ x
  rw [integral_const_mul, integral_sub (integrableOn_cubeQ cE) (integrableOn_cubeQ cc), iE]
  have hν0 := F.ν_pos
  have : 0 ≤ F.ν * ∫ x in cubeQ, gradDot W W x := mul_nonneg hν0.le hP
  show 2 * (-(F.ν * ∫ x in cubeQ, gradDot W W x) - ∫ x in cubeQ, ⟪W x, fderiv ℝ v x (W x)⟫)
    ≤ 2 * M * ∫ x in cubeQ, ⟪W x, W x⟫
  nlinarith [iC]

/-- **H3c-2. Uniqueness of classical solutions.** Two solutions `F, G` with the same `ν` and
the same initial datum coincide on `[0, min T_F T_G)`.
Proof: `D(s) = ∫_Q |u_F − u_G|²` has `D(0) = 0`, `D ≥ 0`, `D' ≤ 2M D` on `(0, t)` (H3c-1,
with `M` bounding `‖∇u_G‖` on the compact `[0, t] × Q`); so `e^{−2Ms} D(s)` is
non-increasing, hence `D(t) = 0`; then H0. -/
theorem nsUnique (F G : NSPeriodicData) (hν : F.ν = G.ν) (h0 : F.u 0 = G.u 0) :
    ∀ t ∈ Ico 0 (min F.T G.T), F.u t = G.u t := by
  have hTF : min F.T G.T ≤ F.T := min_le_left _ _
  have hTG : min F.T G.T ≤ G.T := min_le_right _ _
  have hIcoF : Ico 0 (min F.T G.T) ⊆ Ico 0 F.T := Ico_subset_Ico_right hTF
  have hIcoG : Ico 0 (min F.T G.T) ⊆ Ico 0 G.T := Ico_subset_Ico_right hTG
  set D : ℝ → ℝ := fun s => ∫ x in cubeQ, ⟪F.u s x - G.u s x, F.u s x - G.u s x⟫ with hD
  have hWc : ContinuousOn (fun z : ℝ × E3 => F.u z.1 z.2 - G.u z.1 z.2)
      (Ico 0 (min F.T G.T) ×ˢ univ) :=
    (F.cont_u.mono (prod_mono hIcoF subset_rfl)).sub (G.cont_u.mono (prod_mono hIcoG subset_rfl))
  have hDc : ContinuousOn D (Ico 0 (min F.T G.T)) :=
    continuousOn_integral_cubeQ (G := fun s x => ⟪F.u s x - G.u s x, F.u s x - G.u s x⟫)
      (hWc.inner hWc)
  have hDd : ∀ s ∈ Ioo 0 (min F.T G.T), HasDerivAt D
      (∫ x in cubeQ, 2 * ⟪F.u s x - G.u s x, F.dtu s x - G.dtu s x⟫) s := fun s hs =>
    hasDerivAt_integral_inner_self_of (T := min F.T G.T) hs
      (W := fun s x => F.u s x - G.u s x) (W' := fun s x => F.dtu s x - G.dtu s x)
      (hWc.mono (prod_mono Ioo_subset_Ico_self subset_rfl))
      ((F.cont_dtu.mono (prod_mono (Ioo_subset_Ioo_right hTF) subset_rfl)).sub
        (G.cont_dtu.mono (prod_mono (Ioo_subset_Ioo_right hTG) subset_rfl)))
      (fun r hr x => (F.hasDerivAt_u_time ⟨hr.1, hr.2.trans_le hTF⟩ x).sub
        (G.hasDerivAt_u_time ⟨hr.1, hr.2.trans_le hTG⟩ x))
  have hD0 : D 0 = 0 := by simp [hD, h0]
  have hDnn : ∀ s, 0 ≤ D s := fun s =>
    setIntegral_nonneg measurableSet_cubeQ fun x _ => real_inner_self_nonneg
  intro t ht
  rcases eq_or_lt_of_le ht.1 with h | htpos
  · rw [← h]; exact h0
  -- a bound `M` for `‖∇u_G‖` on `[0, t] × Q`
  have hK : IsCompact (Icc 0 t ×ˢ cubeQ) := isCompact_Icc.prod isCompact_cubeQ
  have hsubK : Icc 0 t ×ˢ cubeQ ⊆ Ico 0 G.T ×ˢ univ := fun z hz =>
    ⟨⟨hz.1.1, hz.1.2.trans_lt (ht.2.trans_le hTG)⟩, mem_univ _⟩
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (G.cont_grad.mono hsubK)
  -- `g(s) = e^{−2Ms} D(s)` is non-increasing on `[0, t]`
  set g : ℝ → ℝ := fun s => Real.exp (-(2 * M) * s) * D s with hg
  have hsub : Icc 0 t ⊆ Ico 0 (min F.T G.T) := fun s hs => ⟨hs.1, hs.2.trans_lt ht.2⟩
  have hgd : ∀ s ∈ Ioo 0 t, HasDerivAt g
      (Real.exp (-(2 * M) * s) * (-(2 * M)) * D s + Real.exp (-(2 * M) * s)
        * ∫ x in cubeQ, 2 * ⟪F.u s x - G.u s x, F.dtu s x - G.dtu s x⟫) s := fun s hs => by
    have he : HasDerivAt (fun r => Real.exp (-(2 * M) * r))
        (Real.exp (-(2 * M) * s) * (-(2 * M))) s := by
      have := ((hasDerivAt_id s).const_mul (-(2 * M))).exp
      simpa using this
    exact he.mul (hDd s ⟨hs.1, hs.2.trans ht.2⟩)
  have hanti : AntitoneOn g (Icc 0 t) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc 0 t) ?_ ?_ ?_
    · exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.mul
        (hDc.mono hsub)
    · rw [interior_Icc]
      exact fun s hs => (hgd s hs).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro s hs
      rw [(hgd s hs).deriv]
      have hsT : s < min F.T G.T := hs.2.trans ht.2
      have hb := diff_energy_deriv_le F G hν ⟨hs.1, hsT.trans_le hTF⟩ ⟨hs.1, hsT.trans_le hTG⟩
        (fun x hx => by simpa using hM (s, x) ⟨⟨hs.1.le, hs.2.le⟩, hx⟩)
      have he := Real.exp_pos (-(2 * M) * s)
      have : Real.exp (-(2 * M) * s) * (∫ x in cubeQ, 2 * ⟪F.u s x - G.u s x,
          F.dtu s x - G.dtu s x⟫) ≤ Real.exp (-(2 * M) * s) * (2 * M * D s) :=
        mul_le_mul_of_nonneg_left hb he.le
      nlinarith
  have hgt : g t ≤ g 0 := hanti ⟨le_rfl, htpos.le⟩ ⟨htpos.le, le_rfl⟩ htpos.le
  have hDt : D t = 0 := by
    have he := Real.exp_pos (-(2 * M) * t)
    have h1 : Real.exp (-(2 * M) * t) * D t ≤ 0 := by simpa [hg, hD0] using hgt
    exact le_antisymm (nonpos_of_mul_nonpos_right (by linarith) he) (hDnn t)
  have htF := hIcoF ht
  have htG := hIcoG ht
  have hcW : Continuous fun x => F.u t x - G.u t x :=
    (F.regular htF).continuous.sub (G.regular htG).continuous
  have hz := eq_zero_of_integral_cubeQ_eq_zero
    (f := fun x => ⟪F.u t x - G.u t x, F.u t x - G.u t x⟫) (hcW.inner hcW)
    (fun x => real_inner_self_nonneg)
    (fun j x => by
      show ⟪F.u t (x + basisVec j) - G.u t (x + basisVec j),
        F.u t (x + basisVec j) - G.u t (x + basisVec j)⟫ = _
      rw [F.u_periodic t htF j x, G.u_periodic t htG j x]) hDt
  funext x
  have := hz x
  rw [inner_self_eq_zero, sub_eq_zero] at this
  exact this

/-- **H3c-3 (mirror symmetry is preserved by the flow).** If `u(0)` is mirror-symmetric,
then so is `u(t)` for every `t ∈ [0, T)`. Proof: `reflectSol F` is a solution (H3b) with the
same `ν` and the same initial datum as `F`, so it coincides with `F` (H3c-2). -/
theorem mirror_invariant (F : NSPeriodicData) (h0 : MirrorSymmetric (F.u 0)) :
    ∀ t ∈ Ico 0 F.T, MirrorSymmetric (F.u t) := by
  intro t ht
  have h := nsUnique F (reflectSol F) rfl
    (by rw [reflectSol_u, reflF_eq_self_iff.2 h0]) t (by rw [reflectSol_T, min_self]; exact ht)
  rw [reflectSol_u] at h
  exact reflF_eq_self_iff.1 h.symm

/-- `∫_Q ⟪c, ∂ₜu⟫ = 0` for every constant vector `c`: the viscous term (A6a, `∇c = 0`), the
convective term (`⟪c, (u·∇)u⟫ = u·∇⟪c, u⟫`, A6b, `div u = 0`) and the pressure term (A6b,
`div c = 0`) all vanish. -/
lemma integral_inner_const_dtu (F : NSPeriodicData) {t : ℝ} (ht : t ∈ Ioo 0 F.T) (c : E3) :
    ∫ x in cubeQ, ⟪c, F.dtu t x⟫ = 0 := by
  have ht' := Ioo_subset_Ico_self ht
  set u := F.u t with hu
  set p := F.p t with hp
  have hu2 : ContDiff ℝ 2 u := (F.regular ht').of_le (by norm_num)
  have hu1 : ContDiff ℝ 1 u := (F.regular ht').of_le (by norm_num)
  have hud : Differentiable ℝ u := hu1.differentiable (by norm_num)
  have hp1 : ContDiff ℝ 1 p := (F.p_regular t ht).of_le (by norm_num)
  have hup : IsPeriodic3 u := F.u_periodic t ht'
  have hpp : IsPeriodic3 p := F.p_periodic t ht
  have hdu : ∀ x, divergence u x = 0 := F.div_free t ht'
  have hcp : IsPeriodic3 (fun _ : E3 => c) := fun _ _ => rfl
  have hdc : ∀ x, divergence (fun _ : E3 => c) x = 0 := fun x => by simp [divergence, pd]
  set φ : E3 → ℝ := fun x => ⟪c, u x⟫ with hφ
  have hφ1 : ContDiff ℝ 1 φ := contDiff_const.inner ℝ hu1
  have hφp : IsPeriodic3 φ := fun j x => by
    show ⟪c, u (x + basisVec j)⟫ = ⟪c, u x⟫
    rw [hup j x]
  have hφd : ∀ x, fderiv ℝ φ x (u x) = ⟪c, fderiv ℝ u x (u x)⟫ := fun x => by
    rw [fderiv_inner_apply ℝ (differentiableAt_const c) (hud x)]
    simp
  have hpt : ∀ x, ⟪c, F.dtu t x⟫
      = F.ν * ⟪c, lap u x⟫ - ⟪u x, gradient φ x⟫ - ⟪c, gradient p x⟫ := fun x => by
    rw [F.dtu_eq ht x, ← hu, ← hp, inner_sub_right, inner_sub_right, inner_smul_right,
      real_inner_comm (gradient φ x) (u x), inner_gradient_left, hφd]
  have c1 : Continuous fun x => ⟪c, lap u x⟫ := continuous_const.inner (continuous_lap hu2)
  have hgr : ∀ (r : E3 → ℝ) (w : E3 → E3) x, ⟪w x, gradient r x⟫ = fderiv ℝ r x (w x) :=
    fun r w x => by rw [real_inner_comm, inner_gradient_left]
  have c2 : Continuous fun x => ⟪u x, gradient φ x⟫ := by
    simp_rw [hgr φ u]
    exact (hφ1.continuous_fderiv (by norm_num)).clm_apply hu1.continuous
  have c3 : Continuous fun x => ⟪c, gradient p x⟫ := by
    simp_rw [hgr p (fun _ => c)]
    exact (hp1.continuous_fderiv (by norm_num)).clm_apply continuous_const
  simp_rw [hpt]
  rw [integral_sub (f := fun x => F.ν * ⟪c, lap u x⟫ - ⟪u x, gradient φ x⟫)
      (g := fun x => ⟪c, gradient p x⟫)
      (integrableOn_cubeQ ((continuous_const.mul c1).sub c2)) (integrableOn_cubeQ c3),
    integral_sub (f := fun x => F.ν * ⟪c, lap u x⟫) (g := fun x => ⟪u x, gradient φ x⟫)
      (integrableOn_cubeQ (continuous_const.mul c1)) (integrableOn_cubeQ c2),
    integral_const_mul,
    integral_cubeQ_inner_lap (u := fun _ => c) contDiff_const hu2 hcp hup,
    integral_cubeQ_inner_gradient hu1 hφ1 hup hφp,
    integral_cubeQ_inner_gradient (u := fun _ => c) contDiff_const hp1 hcp hpp]
  simp [hdu, hdc, gradDot, pd]

/-- **H3c-4 (conservation of momentum).** `t ↦ ∫_Q ⟪c, u(t)⟫` is constant on `[0, T)` for
every `c`.
Proof: `2∫⟪c, u⟫ = ∫|u + c|² − ∫|u|² − ∫|c|²`; differentiating the first two terms (E2) gives
`2∫⟪c, ∂ₜu⟫ = 0`; then monotonicity in both directions on `[0, t]`. -/
theorem integral_inner_const_eq (F : NSPeriodicData) (c : E3) :
    ∀ t ∈ Ico 0 F.T, ∫ x in cubeQ, ⟪c, F.u t x⟫ = ∫ x in cubeQ, ⟪c, F.u 0 x⟫ := by
  set h : ℝ → ℝ := fun s => ∫ x in cubeQ, ⟪c, F.u s x⟫ with hh
  have hcont : ContinuousOn h (Ico 0 F.T) :=
    continuousOn_integral_cubeQ (G := fun s x => ⟪c, F.u s x⟫) (continuousOn_const.inner F.cont_u)
  -- express `h` through two energy integrals
  have hrep : ∀ s ∈ Ico 0 F.T, h s = ((∫ x in cubeQ, ⟪F.u s x + c, F.u s x + c⟫)
      - (∫ x in cubeQ, ⟪F.u s x, F.u s x⟫) - ∫ x in cubeQ, ⟪c, c⟫) / 2 := fun s hs => by
    have hc := (F.regular hs).continuous
    rw [← integral_sub (integrableOn_cubeQ ((hc.add continuous_const).inner
        (hc.add continuous_const))) (integrableOn_cubeQ (hc.inner hc)),
      ← integral_sub (integrableOn_cubeQ (((hc.add continuous_const).inner
        (hc.add continuous_const)).sub (hc.inner hc))) (integrableOn_cubeQ continuous_const)]
    rw [eq_div_iff (two_ne_zero), hh, ← integral_mul_const]
    refine setIntegral_congr_fun measurableSet_cubeQ fun x _ => ?_
    simp only [inner_add_left, inner_add_right, real_inner_comm (F.u s x) c]
    ring
  have hderiv : ∀ s ∈ Ioo 0 F.T, HasDerivAt h 0 s := fun s hs => by
    have hA := hasDerivAt_integral_inner_self_of hs (W := fun r x => F.u r x + c)
      (W' := F.dtu) ((F.cont_u.mono (prod_mono Ioo_subset_Ico_self subset_rfl)).add
        continuousOn_const) F.cont_dtu
      (fun r hr x => (F.hasDerivAt_u_time hr x).add_const c)
    have hB := F.hasDerivAt_integral_inner_self hs
    have hAB := ((hA.sub hB).sub_const (∫ x in cubeQ, ⟪c, c⟫)).div_const 2
    have hval : ((∫ x in cubeQ, 2 * ⟪F.u s x + c, F.dtu s x⟫)
        - ∫ x in cubeQ, 2 * ⟪F.u s x, F.dtu s x⟫) / 2 = 0 := by
      have hc := (F.regular (Ioo_subset_Ico_self hs)).continuous
      have hd : Continuous (F.dtu s) := continuous_slice F.cont_dtu hs
      have i1 : IntegrableOn (fun x => 2 * ⟪F.u s x + c, F.dtu s x⟫) cubeQ :=
        integrableOn_cubeQ (continuous_const.mul ((hc.add continuous_const).inner hd))
      have i2 : IntegrableOn (fun x => 2 * ⟪F.u s x, F.dtu s x⟫) cubeQ :=
        integrableOn_cubeQ (continuous_const.mul (hc.inner hd))
      rw [← integral_sub i1 i2]
      have : ∀ x, 2 * ⟪F.u s x + c, F.dtu s x⟫ - 2 * ⟪F.u s x, F.dtu s x⟫
          = 2 * ⟪c, F.dtu s x⟫ := fun x => by rw [inner_add_left]; ring
      simp_rw [this]
      rw [integral_const_mul, integral_inner_const_dtu F hs c]
      simp
    rw [hval] at hAB
    refine hAB.congr_of_eventuallyEq ?_
    filter_upwards [isOpen_Ioo.mem_nhds hs] with r hr
    exact hrep r (Ioo_subset_Ico_self hr)
  intro t ht
  rcases eq_or_lt_of_le ht.1 with h0 | htpos
  · rw [← h0]
  have hsub : Icc 0 t ⊆ Ico 0 F.T := fun s hs => ⟨hs.1, hs.2.trans_lt ht.2⟩
  have hd' : ∀ s ∈ interior (Icc 0 t), HasDerivAt h 0 s := fun s hs => by
    rw [interior_Icc] at hs
    exact hderiv s ⟨hs.1, hs.2.trans ht.2⟩
  have hm := monotoneOn_of_deriv_nonneg (convex_Icc 0 t) (hcont.mono hsub)
    (fun s hs => (hd' s hs).differentiableAt.differentiableWithinAt)
    (fun s hs => by rw [(hd' s hs).deriv])
  have ha := antitoneOn_of_deriv_nonpos (convex_Icc 0 t) (hcont.mono hsub)
    (fun s hs => (hd' s hs).differentiableAt.differentiableWithinAt)
    (fun s hs => by rw [(hd' s hs).deriv])
  have h0t : (0 : ℝ) ∈ Icc 0 t := ⟨le_rfl, htpos.le⟩
  have htt : t ∈ Icc 0 t := ⟨htpos.le, le_rfl⟩
  exact le_antisymm (ha h0t htt htpos.le) (hm h0t htt htpos.le)

/-- Consequence: `∫_Q u(0) = 0` ⇒ `∫_Q u(t) = 0` for every `t ∈ [0, T)`. -/
theorem mean_zero_invariant (F : NSPeriodicData) (h0 : ∫ x in cubeQ, F.u 0 x = 0) :
    ∀ t ∈ Ico 0 F.T, ∫ x in cubeQ, F.u t x = 0 := by
  intro t ht
  have hi : ∀ s ∈ Ico 0 F.T, Integrable (F.u s) (volume.restrict cubeQ) := fun s hs =>
    integrableOn_cubeQ (F.regular hs).continuous
  set m := ∫ x in cubeQ, F.u t x
  have h := integral_inner_const_eq F m t ht
  rw [integral_inner (hi t ht), integral_inner (hi 0 ⟨le_rfl, F.T_pos⟩), h0, inner_zero_right]
    at h
  exact inner_self_eq_zero.1 h

/-- **H3c (invariance of `OddSymmetrySpace`).** If `u(0) ∈ OddSymmetrySpace`, then
`u(t) ∈ OddSymmetrySpace` for every `t ∈ [0, T)`. No assumption is used beyond the structure of
a solution. -/
theorem oddSymmetry_invariant (F : NSPeriodicData) (h0 : OddSymmetrySpace (F.u 0)) :
    ∀ t ∈ Ico 0 F.T, OddSymmetrySpace (F.u t) := fun t ht =>
  { smooth := F.regular ht
    periodic := F.u_periodic t ht
    div_free := F.div_free t ht
    mirror := mirror_invariant F h0.mirror t ht
    mean_zero := mean_zero_invariant F h0.mean_zero t ht }

/-! ## H3d. Bounding the `L^∞(𝕋³)` norm from below by a point value -/

/-- The open cube `(0,1)³ ⊆ Q`. -/
def openCubeQ : Set E3 := WithLp.ofLp ⁻¹' (univ.pi fun _ : Fin 3 => Ioo (0 : ℝ) 1)

lemma isOpen_openCubeQ : IsOpen openCubeQ :=
  (isOpen_set_pi finite_univ fun _ _ => isOpen_Ioo).preimage (PiLp.continuous_ofLp 2 _)

lemma openCubeQ_subset : openCubeQ ⊆ cubeQ := fun x hx => by
  rw [cubeQ, mem_preimage, ← pi_univ_Icc]
  exact fun i _ => Ioo_subset_Icc_self (hx i trivial)

/-- For continuous `f` and `x` in the open cube: `|f(x)| ≤ ‖f‖_{L^∞(Q)}`. -/
lemma ofReal_norm_le_eLpNorm_top {G : Type*} [NormedAddCommGroup G] {f : E3 → G}
    (hf : Continuous f) {x : E3} (hx : x ∈ openCubeQ) :
    ENNReal.ofReal ‖f x‖ ≤ eLpNorm f ⊤ (volume.restrict cubeQ) := by
  rw [eLpNorm_exponent_top hf.aestronglyMeasurable]
  by_contra hlt
  rw [not_le] at hlt
  set M := eLpNormEssSup f (volume.restrict cubeQ)
  set U : Set E3 := {y | M < ‖f y‖ₑ} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const (continuous_eNorm.comp hf)
  have hnull : volume.restrict cubeQ U = 0 := by
    have h := ae_le_eLpNormEssSup (μ := volume.restrict cubeQ) (f := f)
    rw [ae_iff] at h
    simpa [hU, not_le] using h
  rw [Measure.restrict_apply hUo.measurableSet] at hnull
  have hxU : x ∈ U := by
    show M < ‖f x‖ₑ
    rw [← ofReal_norm]
    exact hlt
  have hpos : 0 < volume (U ∩ openCubeQ) :=
    (hUo.inter isOpen_openCubeQ).measure_pos volume ⟨x, hxU, hx⟩
  exact hpos.ne' (measure_mono_null (inter_subset_inter_right _ openCubeQ_subset) hnull)

/-- `∫_{T−δ}^T c/(T − t) dt = ∞` (in `lintegral` form). -/
lemma lintegral_div_sub_eq_top {T δ c : ℝ} (hc : 0 < c) (hδ : 0 < δ) :
    ∫⁻ t in Ioo (T - δ) T, ENNReal.ofReal (c / (T - t)) = ⊤ := by
  by_contra hne
  have hlt := lt_top_iff_ne_top.2 hne
  have hcont : ContinuousOn (fun t => c / (T - t)) (Ioo (T - δ) T) := fun t ht =>
    (continuousAt_const.div (continuousAt_const.sub continuousAt_id)
      (sub_ne_zero.2 ht.2.ne')).continuousWithinAt
  have hint : IntegrableOn (fun t => c / (T - t)) (Ioo (T - δ) T) :=
    ⟨hcont.aestronglyMeasurable measurableSet_Ioo,
      (hasFiniteIntegral_iff_ofReal ((ae_restrict_iff' measurableSet_Ioo).2
        (Eventually.of_forall fun t ht => (div_pos hc (sub_pos.2 ht.2)).le))).2 hlt⟩
  have hii : IntervalIntegrable (fun t => c / (T - t)) volume (T - δ) T :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (by linarith)).2 hint
  have heq : (fun t => -c⁻¹ * (c / (T - t))) = fun t => (t - T)⁻¹ := by
    funext t
    by_cases ht : t = T
    · simp [ht]
    · have : T - t ≠ 0 := sub_ne_zero.2 (Ne.symm ht)
      have : t - T ≠ 0 := sub_ne_zero.2 ht
      field_simp
      ring
  have h2 : IntervalIntegrable (fun t => (t - T)⁻¹) volume (T - δ) T := by
    rw [← heq]; exact hii.const_mul _
  rcases intervalIntegrable_sub_inv_iff.1 h2 with h | h
  · linarith
  · exact h right_mem_uIcc

/-- **H3d (a type I rate ⇒ the BKM integral diverges).** If `‖ω(t)‖_∞ ≥ c/(T − t)` on
`(T − δ, T)`, then `BKMBlowup F`. -/
theorem bkmBlowup_of_typeI (F : NSPeriodicData) {c δ : ℝ} (hc : 0 < c) (hδ : 0 < δ)
    (hδT : δ ≤ F.T)
    (hlow : ∀ t ∈ Ioo (F.T - δ) F.T, ENNReal.ofReal (c / (F.T - t)) ≤ vortLinfT F.u t) :
    BKMBlowup F := by
  unfold BKMBlowup
  refine eq_top_iff.2 ?_
  calc ⊤ = ∫⁻ t in Ioo (F.T - δ) F.T, ENNReal.ofReal (c / (F.T - t)) :=
        (lintegral_div_sub_eq_top hc hδ).symm
    _ ≤ ∫⁻ t in Ioo (F.T - δ) F.T, vortLinfT F.u t :=
        lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ioo).2 (Eventually.of_forall hlow))
    _ ≤ ∫⁻ t in Ioo 0 F.T, vortLinfT F.u t :=
        lintegral_mono_set (Ioo_subset_Ioo_left (by linarith))

/-! ## H3e. A local Leray self-similar frame -/

/-- The Leray scale `λ(t) = √(2a(T − t))`. -/
def lerayScale (a T t : ℝ) : ℝ := Real.sqrt (2 * a * (T - t))

/-- The Leray rescaled field `x ↦ λ⁻¹ W(λ⁻¹(x − x₀))`. Substituting into NS gives the
profile equation `−νΔW + aW + a(y·∇)W + (W·∇)W + ∇P = 0`: every term has the same order
`λ⁻³`, so viscosity balances the nonlinearity directly (only at the Leray exponent `1/2`). -/
def lerayField (x₀ : E3) (l : ℝ) (W : E3 → E3) : E3 → E3 := fun x => l⁻¹ • W (l⁻¹ • (x - x₀))

lemma fderiv_lerayField {x₀ : E3} {l : ℝ} {W : E3 → E3} (hW : Differentiable ℝ W)
    (x w : E3) :
    fderiv ℝ (lerayField x₀ l W) x w = (l⁻¹ * l⁻¹) • fderiv ℝ W (l⁻¹ • (x - x₀)) w := by
  have hin : HasFDerivAt (fun x => l⁻¹ • (x - x₀)) (l⁻¹ • ContinuousLinearMap.id ℝ E3) x :=
    ((hasFDerivAt_id x).sub_const x₀).const_smul l⁻¹
  have h := ((hW _).hasFDerivAt.comp x hin).const_smul l⁻¹
  rw [show lerayField x₀ l W = l⁻¹ • (W ∘ fun x => l⁻¹ • (x - x₀)) from rfl, h.fderiv]
  simp [smul_smul]

lemma pd_lerayField {x₀ : E3} {l : ℝ} {W : E3 → E3} (hW : Differentiable ℝ W) (x : E3)
    (j i : Fin 3) :
    pd (lerayField x₀ l W) j i x = (l⁻¹ * l⁻¹) * pd W j i (l⁻¹ • (x - x₀)) := by
  show (fderiv ℝ (lerayField x₀ l W) x (basisVec j)) i = _
  rw [fderiv_lerayField hW, PiLp.smul_apply, smul_eq_mul]
  rfl

lemma curl_lerayField {x₀ : E3} {l : ℝ} {W : E3 → E3} (hW : Differentiable ℝ W) (x : E3) :
    curl (lerayField x₀ l W) x = (l⁻¹ * l⁻¹) • curl W (l⁻¹ • (x - x₀)) := by
  ext i
  rw [curl_apply, PiLp.smul_apply, curl_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by rw [pd_lerayField hW]; ring

lemma curl_congr_of_fderiv {u v : E3 → E3} {x : E3} (h : fderiv ℝ u x = fderiv ℝ v x) :
    curl u x = curl v x := by
  simp only [curl, pd, h]

/-- **A LOCAL Leray self-similar ansatz around `x₀`.** On `(T − δ, T)` and inside the
shrinking ball `‖x − x₀‖ < Rλ(t)`: `u(t, x) = λ⁻¹ W((x − x₀)/λ)`, with a profile `W` that is
non-zero in the sense that `curl W(y₀) ≠ 0` at some point `‖y₀‖ < R`.

Remark (why only local): a GLOBAL Leray profile `W ∈ L³(ℝ³)` is excluded by
Nečas–Růžička–Šverák (1996); Tsai (1998) excludes `W ∈ L^p` (`3 < p < ∞`) and `W` satisfying a
local energy estimate. This is also type I blow-up (`|u| ~ (T − t)^{−1/2}`), which has been
excluded in the axisymmetric case (Koch–Nadirashvili–Seregin–Šverák 2009; Chen–Strain–Tsai–Yau). -/
structure LerayAnsatzNear (F : NSPeriodicData) (x₀ : E3) (a R δ : ℝ) (W : E3 → E3) : Prop where
  a_pos : 0 < a
  R_pos : 0 < R
  δ_pos : 0 < δ
  δ_le : δ ≤ F.T
  center_mem : x₀ ∈ openCubeQ
  profile_smooth : ContDiff ℝ 1 W
  profile_nontrivial : ∃ y, ‖y‖ < R ∧ curl W y ≠ 0
  ansatz : ∀ t ∈ Ioo (F.T - δ) F.T,
    EqOn (F.u t) (lerayField x₀ (lerayScale a F.T t) W) (Metric.ball x₀ (R * lerayScale a F.T t))

/-- **H3e (ansatz ⇒ type I rate).** The local Leray ansatz gives `‖ω(t)‖_∞ ≥ c/(T − t)` near
`T`, with `c = |curl W(y₀)|/(2a)`: at `x(t) = x₀ + λ(t)y₀` one has `ω = λ⁻² curl W(y₀)`. -/
theorem typeI_of_ansatz {F : NSPeriodicData} {x₀ : E3} {a R δ : ℝ} {W : E3 → E3}
    (hA : LerayAnsatzNear F x₀ a R δ W) :
    ∃ c > 0, ∃ δ' > 0, δ' ≤ F.T ∧
      ∀ t ∈ Ioo (F.T - δ') F.T, ENNReal.ofReal (c / (F.T - t)) ≤ vortLinfT F.u t := by
  obtain ⟨y₀, hy₀R, hy₀c⟩ := hA.profile_nontrivial
  have ha := hA.a_pos
  have hWd : Differentiable ℝ W := hA.profile_smooth.differentiable (by norm_num)
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 isOpen_openCubeQ x₀ hA.center_mem
  set N := ‖y₀‖ + 1 with hN
  have hNpos : 0 < N := by positivity
  set ρ := (r / N) ^ 2 / (2 * a) with hρ
  have hρpos : 0 < ρ := by positivity
  refine ⟨‖curl W y₀‖ / (2 * a), div_pos (norm_pos_iff.2 hy₀c) (by positivity),
    min δ ρ, lt_min hA.δ_pos hρpos, (min_le_left _ _).trans hA.δ_le, fun t ht => ?_⟩
  have htδ : t ∈ Ioo (F.T - δ) F.T := ⟨by linarith [min_le_left δ ρ, ht.1], ht.2⟩
  have hTt : 0 < F.T - t := sub_pos.2 ht.2
  set l := lerayScale a F.T t with hl
  have hl2 : l ^ 2 = 2 * a * (F.T - t) := Real.sq_sqrt (by positivity)
  have hlpos : 0 < l := Real.sqrt_pos.2 (by positivity)
  have hlr : l * N < r := by
    have h1 : l ^ 2 < (r / N) ^ 2 := by
      rw [hl2]
      have : F.T - t < ρ := by linarith [min_le_right δ ρ, ht.1]
      calc 2 * a * (F.T - t) < 2 * a * ρ := by gcongr
        _ = (r / N) ^ 2 := by rw [hρ]; field_simp
    have h2 := lt_of_pow_lt_pow_left₀ 2 (by positivity) h1
    rwa [lt_div_iff₀ hNpos] at h2
  set x := x₀ + l • y₀ with hx
  have hdist : ‖x - x₀‖ = l * ‖y₀‖ := by
    rw [hx, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hlpos.le]
  have hxB : x ∈ Metric.ball x₀ (R * l) := by
    rw [Metric.mem_ball, dist_eq_norm, hdist]
    nlinarith
  have hxS : x ∈ openCubeQ := hball (by
    rw [Metric.mem_ball, dist_eq_norm, hdist]
    nlinarith)
  have htI : t ∈ Ico 0 F.T := ⟨by linarith [hA.δ_le, htδ.1], ht.2⟩
  -- `ω(t, x) = λ⁻² curl W(y₀)`
  have hfd : fderiv ℝ (F.u t) x = fderiv ℝ (lerayField x₀ l W) x :=
    (eventuallyEq_of_mem (Metric.isOpen_ball.mem_nhds hxB) (hA.ansatz t htδ)).fderiv_eq
  have hω : vort F.u t x = (l⁻¹ * l⁻¹) • curl W y₀ := by
    rw [vort, curl_congr_of_fderiv hfd, curl_lerayField hWd, hx, add_sub_cancel_left,
      smul_smul, inv_mul_cancel₀ hlpos.ne', one_smul]
  have hnorm : ‖vort F.u t x‖ = ‖curl W y₀‖ / (2 * a) / (F.T - t) := by
    rw [hω, norm_smul, Real.norm_of_nonneg (by positivity), ← mul_inv, ← sq, hl2]
    field_simp
  have hcont : Continuous (vort F.u t) :=
    (contDiff_curl (m := 0) (F.regular htI) (by norm_num)).continuous
  rw [← hnorm]
  exact ofReal_norm_le_eLpNorm_top hcont hxS

/-! ## H3f. An odd-symmetric self-similar scenario ⇒ `NSBlowupConjecture` -/

section H3f

open scoped ContDiff

/-- **OPEN ASSUMPTION — an odd-symmetric LERAY (type I) self-similar scenario (f = 0).**
There is a solution `F` with `C^∞` data in `OddSymmetrySpace` (mirror-symmetric across
`x₃ = 0`, total momentum 0), and a local Leray ansatz around a centre `x₀` on the second plane of
symmetry `x₃ = 1/2` (the mirror across `x₃ = 0` plus periodicity gives a mirror across
`x₃ = 1/2`, and this plane lies inside `Q`).
By `oddSymmetry_invariant`, the solution stays in the symmetry class on all of `[0, T)`.
All the real difficulty of the problem lies in finding `F` and `W` satisfying this statement. -/
def LeraySelfSimilarOddScenario : Prop :=
  ∃ F : NSPeriodicData, ContDiff ℝ ∞ (F.u 0) ∧ OddSymmetrySpace (F.u 0) ∧
    ∃ (x₀ : E3) (a R δ : ℝ) (W : E3 → E3), x₀ 2 = 1 / 2 ∧ LerayAnsatzNear F x₀ a R δ W

/-- **H3f (bridge theorem, type I).** `LeraySelfSimilarOddScenario ⇒ NSBlowupConjecture`
(`f = 0`). Chain: ansatz ⇒ `‖ω(t)‖_∞ ≥ c/(T − t)` (H3e) ⇒ `∫₀^T ‖ω‖_∞ = ∞` (H3d). -/
theorem NSBlowupConjecture_of_leray (h : LeraySelfSimilarOddScenario) : NSBlowupConjecture := by
  obtain ⟨F, hs, -, x₀, a, R, δ, W, -, hA⟩ := h
  obtain ⟨c, hc, δ', hδ', hδ'T, hlow⟩ := typeI_of_ansatz hA
  exact ⟨F, hs, bkmBlowup_of_typeI F hc hδ' hδ'T hlow⟩

end H3f

/-! ## H3g. A type II scenario: a supercritical scale + a modulated profile (spectral gap)

A PHYSICAL REMARK (dimensions checked). With Leray amplitude `ω ~ ℓ⁻²` (`u ~ ℓ⁻¹`), the
Navier–Stokes equations are scale invariant, so the ratio of viscosity to nonlinearity is a
CONSTANT, even when `ℓ = o(√(T − t))`. The blow-up limit is then a stationary or ancient solution
of NS on `ℝ³`; the obstruction in this regime is the Liouville theorems
(Koch–Nadirashvili–Seregin–Šverák 2009, axisymmetric without swirl), no longer
Nečas–Růžička–Šverák/Tsai. The regime in which the effective viscosity really tends to `0` is the
Euler type (section H3h). -/

/-- The mirror centre `x₀ = (½, ½, ½)`, on the symmetry plane `x₃ = ½` and inside `Q`. -/
def mirrorCenter : E3 := WithLp.toLp 2 (fun _ : Fin 3 => (1 / 2 : ℝ))

lemma mirrorCenter_mem : mirrorCenter ∈ openCubeQ := fun i _ => by
  show (1 / 2 : ℝ) ∈ Ioo 0 1
  constructor <;> norm_num

/-- **Type II scale (supercritical).** `ℓ > 0` on `[0, T)` and `ℓ(t)²/(T − t) → 0` as
`t → T⁻`, i.e. `ℓ = o(√(T − t))`. -/
structure TypeIIScale (T : ℝ) (ℓ : ℝ → ℝ) : Prop where
  pos : ∀ t ∈ Ico 0 T, 0 < ℓ t
  supercritical : Tendsto (fun t => ℓ t ^ 2 / (T - t)) (𝓝[<] T) (𝓝 0)

/-- **T2.** A type II scale gives `∫₀ᵀ ℓ⁻² = ∞`: this is DERIVED, not assumed.
Near `T` one has `ℓ² < T − t`, so `ℓ⁻² > 1/(T − t)`; then use `lintegral_div_sub_eq_top`. -/
lemma lintegral_inv_sq_eq_top {T : ℝ} {ℓ : ℝ → ℝ} (hT : 0 < T) (h : TypeIIScale T ℓ) :
    ∫⁻ t in Ioo 0 T, ENNReal.ofReal ((ℓ t ^ 2)⁻¹) = ⊤ := by
  have hev : ∀ᶠ t in 𝓝[<] T, ℓ t ^ 2 / (T - t) < 1 :=
    h.supercritical.eventually (gt_mem_nhds one_pos)
  obtain ⟨l, hl, hsub⟩ := mem_nhdsLT_iff_exists_Ioo_subset.1 hev
  have hl' : l < T := hl
  set δ := min (T - l) T with hδdef
  have hδ : 0 < δ := lt_min (sub_pos.2 hl') hT
  have hδ1 := min_le_left (T - l) T
  have hδ2 := min_le_right (T - l) T
  refine eq_top_iff.2 ?_
  calc ⊤ = ∫⁻ t in Ioo (T - δ) T, ENNReal.ofReal (1 / (T - t)) :=
        (lintegral_div_sub_eq_top one_pos hδ).symm
    _ ≤ ∫⁻ t in Ioo (T - δ) T, ENNReal.ofReal ((ℓ t ^ 2)⁻¹) := by
        refine lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ioo).2
          (Eventually.of_forall fun t ht => ENNReal.ofReal_le_ofReal ?_))
        have htl : t ∈ Ioo l T := ⟨by linarith [ht.1], ht.2⟩
        have h1 : ℓ t ^ 2 / (T - t) < 1 := hsub htl
        have h2 : ℓ t ^ 2 < T - t := (div_lt_one (sub_pos.2 ht.2)).1 h1
        have hpos : 0 < ℓ t := h.pos t ⟨by linarith [ht.1], ht.2⟩
        rw [one_div]
        exact inv_anti₀ (pow_pos hpos 2) h2.le
    _ ≤ ∫⁻ t in Ioo 0 T, ENNReal.ofReal ((ℓ t ^ 2)⁻¹) :=
        lintegral_mono_set (Ioo_subset_Ioo_left (by linarith))

/-- **T5.** If `‖ω(t)‖_∞ ≥ c ℓ(t)⁻²` on `(0, T)` and `∫₀ᵀ ℓ⁻² = ∞`, then `BKMBlowup F`. -/
theorem bkmBlowup_of_scale (F : NSPeriodicData) {ℓ : ℝ → ℝ} {c : ℝ} (hc : 0 < c)
    (hℓ : ∫⁻ t in Ioo 0 F.T, ENNReal.ofReal ((ℓ t ^ 2)⁻¹) = ⊤)
    (hlow : ∀ t ∈ Ioo 0 F.T, ENNReal.ofReal (c * (ℓ t ^ 2)⁻¹) ≤ vortLinfT F.u t) :
    BKMBlowup F := by
  unfold BKMBlowup
  refine eq_top_iff.2 ?_
  calc ⊤ = ENNReal.ofReal c * ∫⁻ t in Ioo 0 F.T, ENNReal.ofReal ((ℓ t ^ 2)⁻¹) := by
        rw [hℓ, ENNReal.mul_top (ENNReal.ofReal_pos.2 hc).ne']
    _ = ∫⁻ t in Ioo 0 F.T, ENNReal.ofReal (c * (ℓ t ^ 2)⁻¹) := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        congr 1
        funext t
        rw [ENNReal.ofReal_mul hc.le]
    _ ≤ ∫⁻ t in Ioo 0 F.T, vortLinfT F.u t :=
        lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ioo).2 (Eventually.of_forall hlow))

/-- **T3. A modulated vortex profile — a CONSEQUENCE of a spectral gap (not the spectral
statement itself).** Around the centre `x₀`, with scale `ℓ(t)`, amplitude `A(t)` and rescaled
time `τ(t)`:
`‖A(t)⁻¹ ω(x₀ + ℓ(t)y, t) − Ω(y)‖ ≤ C e^{−γτ(t)}` on `‖y‖ ≤ R`.
A spectral gap `γ > 0` of the operator linearised around `Ω` in `OddSymmetrySpace` (together
with a standard modulation argument) would give an estimate of this form; Mathlib does not yet
have a spectral theory for the Stokes operator, so we state the consequence directly.
`profile_odd`: `Ω(σy) = −σΩ(y)` (the vorticity of a mirror-symmetric field is anti-symmetric), so
at the centre `Ω(0)` is vertical (`center_vertical`). The bridge theorem only uses
`C < ‖Ω(0)‖`; `γ` plays no logical role. -/
structure ModulatedVortexProfile (F : NSPeriodicData) (x₀ : E3) (ℓ A τ : ℝ → ℝ) (Ω : E3 → E3)
    (γ C R : ℝ) : Prop where
  γ_pos : 0 < γ
  R_pos : 0 < R
  C_nonneg : 0 ≤ C
  small : C < ‖Ω 0‖
  profile_cont : Continuous Ω
  profile_odd : ∀ y, Ω (refl y) = -refl (Ω y)
  modulation : ∀ t ∈ Ioo 0 F.T, ∀ y, ‖y‖ ≤ R →
    ‖(A t)⁻¹ • vort F.u t (x₀ + ℓ t • y) - Ω y‖ ≤ C * Real.exp (-γ * τ t)

/-- At the centre the profile is vertical: `Ω(0)₁ = Ω(0)₂ = 0`. -/
lemma ModulatedVortexProfile.center_vertical {F : NSPeriodicData} {x₀ : E3} {ℓ A τ : ℝ → ℝ}
    {Ω : E3 → E3} {γ C R : ℝ} (hM : ModulatedVortexProfile F x₀ ℓ A τ Ω γ C R) :
    Ω 0 0 = 0 ∧ Ω 0 1 = 0 := by
  have h := hM.profile_odd 0
  rw [map_zero] at h
  have h0 := congrArg (fun w : E3 => w 0) h
  have h1 := congrArg (fun w : E3 => w 1) h
  simp only [PiLp.neg_apply, refl_apply_coord, rsgn] at h0 h1
  norm_num at h0 h1
  constructor <;> linarith

/-- **T4.** From the modulated profile: `‖ω(t)‖_∞ ≥ (‖Ω(0)‖ − C) A(t)` on `(0, T)` (take
`y = 0` and use `e^{−γτ} ≤ 1` when `τ ≥ 0`). -/
theorem vortLinf_ge_of_modulated {F : NSPeriodicData} {x₀ : E3} {ℓ A τ : ℝ → ℝ} {Ω : E3 → E3}
    {γ C R : ℝ} (hM : ModulatedVortexProfile F x₀ ℓ A τ Ω γ C R) (hx₀ : x₀ ∈ openCubeQ)
    (hA : ∀ t ∈ Ioo 0 F.T, 0 < A t) (hτ : ∀ t ∈ Ioo 0 F.T, 0 ≤ τ t) :
    ∀ t ∈ Ioo 0 F.T, ENNReal.ofReal ((‖Ω 0‖ - C) * A t) ≤ vortLinfT F.u t := by
  intro t ht
  have h := hM.modulation t ht 0 (by rw [norm_zero]; exact hM.R_pos.le)
  rw [smul_zero, add_zero] at h
  have hexp : Real.exp (-γ * τ t) ≤ 1 :=
    Real.exp_le_one_iff.2 (by nlinarith [hM.γ_pos, hτ t ht])
  have hC : C * Real.exp (-γ * τ t) ≤ C := by
    nlinarith [hM.C_nonneg, Real.exp_pos (-γ * τ t)]
  have hAt := hA t ht
  have h2 : ‖Ω 0‖ - ‖(A t)⁻¹ • vort F.u t x₀‖ ≤ C := by
    have := norm_sub_norm_le (Ω 0) ((A t)⁻¹ • vort F.u t x₀)
    rw [norm_sub_rev] at this
    linarith
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hAt.le)] at h2
  have h3 : (‖Ω 0‖ - C) * A t ≤ ‖vort F.u t x₀‖ := by
    have h4 : ‖Ω 0‖ - C ≤ (A t)⁻¹ * ‖vort F.u t x₀‖ := by linarith
    calc (‖Ω 0‖ - C) * A t ≤ (A t)⁻¹ * ‖vort F.u t x₀‖ * A t :=
          mul_le_mul_of_nonneg_right h4 hAt.le
      _ = ‖vort F.u t x₀‖ := by field_simp
  have hcont : Continuous (vort F.u t) :=
    (contDiff_curl (m := 0) (F.regular (Ioo_subset_Ico_self ht)) (by norm_num)).continuous
  exact (ENNReal.ofReal_le_ofReal h3).trans (ofReal_norm_le_eLpNorm_top hcont hx₀)

section H3g

open scoped ContDiff

/-- **OPEN ASSUMPTION — scenario A: type II, Leray amplitude, odd symmetry (f = 0).**
There is a solution `F` with `C^∞` data in `OddSymmetrySpace`, a type II scale
`ℓ = o(√(T − t))`, and a vortex profile `Ω` (for instance nested toroidal vortices) such that
around `x₀ = (½, ½, ½)`, with amplitude `A = ℓ⁻²` and rescaled time `τ(t) = ∫₀ᵗ ℓ⁻²`:
`‖ℓ(t)² ω(x₀ + ℓ(t)y, t) − Ω(y)‖ ≤ C e^{−γτ(t)}`.
Note: at Leray amplitude the viscosity does NOT disappear (see the beginning of H3g); the
obstruction is of Liouville type. -/
def TypeIIOddScenario : Prop :=
  ∃ F : NSPeriodicData, ContDiff ℝ ∞ (F.u 0) ∧ OddSymmetrySpace (F.u 0) ∧
    ∃ (ℓ : ℝ → ℝ) (Ω : E3 → E3) (γ C R : ℝ), TypeIIScale F.T ℓ ∧
      ModulatedVortexProfile F mirrorCenter ℓ (fun t => (ℓ t ^ 2)⁻¹)
        (fun t => ∫ s in (0 : ℝ)..t, (ℓ s ^ 2)⁻¹) Ω γ C R

/-- **H3g (bridge theorem).** `TypeIIOddScenario ⇒ NSBlowupConjecture` (`f = 0`).
Chain: modulated profile ⇒ `‖ω(t)‖_∞ ≥ (‖Ω(0)‖ − C) ℓ(t)⁻²` (T4); type II scale ⇒
`∫₀ᵀ ℓ⁻² = ∞` (T2); hence `∫₀ᵀ ‖ω‖_∞ = ∞` (T5). -/
theorem NSBlowupConjecture_of_scenario (h : TypeIIOddScenario) : NSBlowupConjecture := by
  obtain ⟨F, hs, -, ℓ, Ω, γ, C, R, hS, hM⟩ := h
  have hlow := vortLinf_ge_of_modulated hM mirrorCenter_mem
    (fun t ht => inv_pos.2 (pow_pos (hS.pos t (Ioo_subset_Ico_self ht)) 2))
    (fun t ht => intervalIntegral.integral_nonneg ht.1.le fun s _ => inv_nonneg.2 (sq_nonneg _))
  exact ⟨F, hs, bkmBlowup_of_scale F (sub_pos.2 hM.small)
    (lintegral_inv_sq_eq_top F.T_pos hS) hlow⟩

/-! ## H3h. Scenario B: Euler type (the effective viscosity really tends to 0) -/

/-- **Euler-type scale.** `ℓ > 0` and `ν_eff(t) := (T − t)/ℓ(t)² → 0` as `t → T⁻`
(multiplied by `ν`, this is the ratio of viscosity to nonlinearity when `u ~ ℓ/(T − t)`),
i.e. `ℓ ≫ √(T − t)`. -/
structure EulerTypeScale (T : ℝ) (ℓ : ℝ → ℝ) : Prop where
  pos : ∀ t ∈ Ico 0 T, 0 < ℓ t
  viscosity_vanishes : Tendsto (fun t => (T - t) / ℓ t ^ 2) (𝓝[<] T) (𝓝 0)

/-- **OPEN ASSUMPTION — scenario B: Euler type, odd symmetry (f = 0).**
As scenario A, but with Euler-type amplitude: `u ~ ℓ/(T − t)`, `ω ~ (T − t)⁻¹`, rescaled time
`τ(t) = log(T/(T − t))`:
`‖(T − t) ω(x₀ + ℓ(t)y, t) − Ω(y)‖ ≤ C e^{−γτ(t)}`.
This is the regime in which the profile solves an Euler-type equation and viscosity is a
singular perturbation (in the same spirit as Hou's numerical scenarios for NS). It remains
OPEN. -/
def EulerTypeOddScenario : Prop :=
  ∃ F : NSPeriodicData, ContDiff ℝ ∞ (F.u 0) ∧ OddSymmetrySpace (F.u 0) ∧
    ∃ (ℓ : ℝ → ℝ) (Ω : E3 → E3) (γ C R : ℝ), EulerTypeScale F.T ℓ ∧
      ModulatedVortexProfile F mirrorCenter ℓ (fun t => (F.T - t)⁻¹)
        (fun t => Real.log (F.T / (F.T - t))) Ω γ C R

/-- **H3h (bridge theorem).** `EulerTypeOddScenario ⇒ NSBlowupConjecture` (`f = 0`).
Chain: T4 gives `‖ω(t)‖_∞ ≥ (‖Ω(0)‖ − C)/(T − t)`, then `bkmBlowup_of_typeI` (H3d). -/
theorem NSBlowupConjecture_of_eulerType (h : EulerTypeOddScenario) : NSBlowupConjecture := by
  obtain ⟨F, hs, -, ℓ, Ω, γ, C, R, -, hM⟩ := h
  have hlow := vortLinf_ge_of_modulated hM mirrorCenter_mem
    (fun t ht => inv_pos.2 (sub_pos.2 ht.2))
    (fun t ht => Real.log_nonneg ((le_div_iff₀ (sub_pos.2 ht.2)).2 (by linarith [ht.1])))
  refine ⟨F, hs, bkmBlowup_of_typeI F (sub_pos.2 hM.small) F.T_pos le_rfl fun t ht => ?_⟩
  rw [sub_self] at ht
  rw [div_eq_mul_inv]
  exact hlow t ht

end H3g

/-! ## H4. Concrete initial data: a mirror-symmetric pair of toroidal vortex rings,
`toroidalDipoleInit`

We build `u₀ = curl A` from a smooth, periodic, trigonometric vector potential
`A = h(x₃) · (−s₂, s₁, 0)`, where `sᵢ = sin 2π(xᵢ − ½)` and
`h(x₃) = sin 2πx₃ + κ sin 6πx₃` (a vortex sub-layer of strength `κ`).
* This is the form `A = φ·(−Y, X, 0)` of a stream function `ψ = rφ` (the factor `r` removes the
  polar-coordinate singularity), with `X, Y` replaced by `s₁/2π, s₂/2π` for periodicity. So the
  field is only AXISYMMETRIC TO FIRST ORDER near `x₀`, not exactly (an exactly axisymmetric field
  cannot be periodic).
* `u₀ = (−s₁h′, −s₂h′, 2πh(c₁ + c₂))`: a poloidal flow with azimuthal vorticity. `h` is odd
  across `x₃ = 0` and `x₃ = ½`, so there are two rings on either side of the plane `x₃ = ½`,
  rotating in opposite directions.
-/

/-- `sᵢ(x) = sin 2π(xᵢ − ½)`. -/
def sTrig (i : Fin 3) (x : E3) : ℝ := Real.sin (2 * Real.pi * (x i - 1 / 2))

/-- The profile in `x₃`: `h(x₃) = sin 2πx₃ + κ sin 6πx₃`. -/
def hLayer (κ : ℝ) (x : E3) : ℝ :=
  Real.sin (2 * Real.pi * x 2) + κ * Real.sin (6 * Real.pi * x 2)

/-- The vector potential `A = h · (−s₂, s₁, 0)`. -/
def dipolePotential (κ : ℝ) (x : E3) : E3 :=
  (-(sTrig 1 x * hLayer κ x)) • basisVec 0 + (sTrig 0 x * hLayer κ x) • basisVec 1

/-- **Initial data: a mirror-symmetric pair of toroidal vortex rings** `u₀ = curl A`. -/
def toroidalDipoleInit (κ : ℝ) : E3 → E3 := curl (dipolePotential κ)

lemma basisVec_apply (j i : Fin 3) : basisVec j i = if i = j then 1 else 0 := by
  by_cases h : i = j <;> simp [basisVec, h]

lemma coord_add_basisVec (x : E3) (i j : Fin 3) :
    (x + basisVec j) i = x i + if i = j then 1 else 0 := by
  rw [PiLp.add_apply, basisVec_apply]

lemma contDiff_coord {n : WithTop ℕ∞} (i : Fin 3) : ContDiff ℝ n (fun x : E3 => x i) :=
  (EuclideanSpace.proj i : E3 →L[ℝ] ℝ).contDiff

lemma contDiff_sTrig {n : WithTop ℕ∞} (i : Fin 3) : ContDiff ℝ n (sTrig i) :=
  Real.contDiff_sin.comp (contDiff_const.mul ((contDiff_coord i).sub contDiff_const))

lemma contDiff_hLayer {n : WithTop ℕ∞} (κ : ℝ) : ContDiff ℝ n (hLayer κ) :=
  (Real.contDiff_sin.comp (contDiff_const.mul (contDiff_coord 2))).add
    (contDiff_const.mul (Real.contDiff_sin.comp (contDiff_const.mul (contDiff_coord 2))))

lemma contDiff_dipolePotential {n : WithTop ℕ∞} (κ : ℝ) : ContDiff ℝ n (dipolePotential κ) :=
  ((((contDiff_sTrig 1).mul (contDiff_hLayer κ)).neg).smul contDiff_const).add
    (((contDiff_sTrig 0).mul (contDiff_hLayer κ)).smul contDiff_const)

lemma sTrig_periodic (i j : Fin 3) (x : E3) : sTrig i (x + basisVec j) = sTrig i x := by
  unfold sTrig
  rw [coord_add_basisVec]
  split_ifs
  · rw [show 2 * Real.pi * (x i + 1 - 1 / 2) = 2 * Real.pi * (x i - 1 / 2) + 2 * Real.pi by ring,
      Real.sin_add_two_pi]
  · rw [add_zero]

lemma hLayer_periodic (κ : ℝ) (j : Fin 3) (x : E3) : hLayer κ (x + basisVec j) = hLayer κ x := by
  unfold hLayer
  rw [coord_add_basisVec]
  split_ifs
  · rw [show 2 * Real.pi * (x 2 + 1) = 2 * Real.pi * x 2 + 2 * Real.pi by ring,
      show 6 * Real.pi * (x 2 + 1) = 6 * Real.pi * x 2 + ((3 : ℕ) : ℝ) * (2 * Real.pi) by
        push_cast; ring,
      Real.sin_add_two_pi, Real.sin_add_nat_mul_two_pi]
  · rw [add_zero]

lemma dipolePotential_periodic (κ : ℝ) : IsPeriodic3 (dipolePotential κ) := fun j x => by
  simp only [dipolePotential, sTrig_periodic, hLayer_periodic]

lemma sTrig_refl (i : Fin 3) (hi : i ≠ 2) (x : E3) : sTrig i (refl x) = sTrig i x := by
  simp [sTrig, refl_apply_coord, rsgn, hi]

lemma hLayer_refl (κ : ℝ) (x : E3) : hLayer κ (refl x) = -hLayer κ x := by
  simp only [hLayer, refl_apply_coord, rsgn, ↓reduceIte]
  rw [show 2 * Real.pi * (-1 * x 2) = -(2 * Real.pi * x 2) by ring,
    show 6 * Real.pi * (-1 * x 2) = -(6 * Real.pi * x 2) by ring, Real.sin_neg, Real.sin_neg]
  ring

/-- `A` is mirror-antisymmetric: `A(σx) = −σA(x)`. -/
lemma dipolePotential_anti (κ : ℝ) (x : E3) :
    dipolePotential κ (refl x) = -refl (dipolePotential κ x) := by
  have h0 : sTrig 0 (refl x) = sTrig 0 x := sTrig_refl 0 (by decide) x
  have h1 : sTrig 1 (refl x) = sTrig 1 x := sTrig_refl 1 (by decide) x
  simp only [dipolePotential, h0, h1, hLayer_refl, map_add, map_smul, refl_basisVec, rsgn]
  norm_num
  abel

/-! ### H4b. Two general lemmas about `curl` -/

lemma eps_rsgn (i j k : Fin 3) : eps i j k * (-(rsgn j * rsgn k)) = rsgn i * eps i j k := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp [eps, rsgn]

lemma pd_neg_field (A : E3 → E3) (j i : Fin 3) (x : E3) :
    pd (fun y => -A y) j i x = -pd A j i x := by
  simp [pd, fderiv_fun_neg]

/-- **The curl of a mirror-antisymmetric field is mirror-symmetric:** if `A(σx) = −σA(x)`,
then `curl A (σx) = σ curl A(x)`. -/
theorem mirror_curl_of_anti {A : E3 → E3} (hA : Differentiable ℝ A)
    (h : ∀ x, A (refl x) = -refl (A x)) : MirrorSymmetric (curl A) := by
  have hR : reflF A = fun y => -A y := funext fun y => by
    rw [reflF, h, map_neg, refl_refl]
  have hpd : ∀ x j i, pd A j i (refl x) = -(rsgn i * rsgn j) * pd A j i x := fun x j i => by
    have h1 := pd_reflF (v := A) (x := x) (hA _) j i
    rw [hR, pd_neg_field] at h1
    have h2 := rsgn_mul_self i
    have h3 := rsgn_mul_self j
    calc pd A j i (refl x)
        = (rsgn i * rsgn i) * (rsgn j * rsgn j) * pd A j i (refl x) := by rw [h2, h3]; ring
      _ = rsgn i * rsgn j * (rsgn i * rsgn j * pd A j i (refl x)) := by ring
      _ = -(rsgn i * rsgn j) * pd A j i x := by rw [← h1]; ring
  intro x
  ext i
  rw [curl_apply, refl_apply_coord, curl_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hpd x j k]
  linear_combination (pd A j k x) * eps_rsgn i j k

/-- **`∫_Q curl A = 0`** for a C¹ periodic `A` (each `∫_Q ∂ⱼAₖ = 0` by A4). -/
theorem integral_cubeQ_curl_eq_zero {A : E3 → E3} (hA : ContDiff ℝ 1 A) (hp : IsPeriodic3 A) :
    ∫ x in cubeQ, curl A x = 0 := by
  have hAd : Differentiable ℝ A := hA.differentiable (by norm_num)
  have hpdc : ∀ j k, Continuous (pd A j k) := fun j k =>
    (contDiff_pd (m := 0) hA (by norm_num) j k).continuous
  have hcont : Continuous (curl A) := (contDiff_curl (m := 0) hA (by norm_num)).continuous
  have hpd0 : ∀ j k, ∫ x in cubeQ, pd A j k x = 0 := fun j k => by
    have hg : ContDiff ℝ 1 (fun y => A y k) := (contDiff_coord k).comp hA
    rw [← integral_cubeQ_fderiv_eq_zero hg j ((hp j).comp fun z => z k)]
    exact setIntegral_congr_fun measurableSet_cubeQ fun x _ =>
      pd_eq_fderiv_component (hAd x) j k
  ext i
  have hL : (∫ x in cubeQ, curl A x) i = ∫ x in cubeQ, curl A x i :=
    ((EuclideanSpace.proj i : E3 →L[ℝ] ℝ).integral_comp_comm (integrableOn_cubeQ hcont)).symm
  rw [hL]
  simp_rw [curl_apply]
  rw [integral_finsetSum (f := fun j x => ∑ k, eps i j k * pd A j k x) _ fun j _ => by
    exact integrableOn_cubeQ (continuous_finsetSum _ fun k _ => continuous_const.mul (hpdc j k))]
  rw [Finset.sum_eq_zero fun j _ => by
    rw [integral_finsetSum (f := fun k x => eps i j k * pd A j k x) _ fun k _ => by
      exact integrableOn_cubeQ (continuous_const.mul (hpdc j k))]
    exact Finset.sum_eq_zero fun k _ => by rw [integral_const_mul, hpd0, mul_zero]]
  simp

/-! ### H4c. `toroidalDipoleInit` belongs to `OddSymmetrySpace` and is `C^∞` -/

section H4

open scoped ContDiff

/-- `u₀` is `C^∞`. -/
theorem toroidalDipoleInit_smooth (κ : ℝ) : ContDiff ℝ ∞ (toroidalDipoleInit κ) :=
  contDiff_curl (m := ∞) (n := ω) (contDiff_dipolePotential κ) le_top

theorem toroidalDipoleInit_periodic (κ : ℝ) : IsPeriodic3 (toroidalDipoleInit κ) :=
  (dipolePotential_periodic κ).curl

theorem toroidalDipoleInit_div_free (κ : ℝ) (x : E3) : divergence (toroidalDipoleInit κ) x = 0 :=
  divergence_curl (contDiff_dipolePotential κ) x

theorem toroidalDipoleInit_mean_zero (κ : ℝ) : ∫ x in cubeQ, toroidalDipoleInit κ x = 0 :=
  integral_cubeQ_curl_eq_zero (contDiff_dipolePotential κ) (dipolePotential_periodic κ)

theorem toroidalDipoleInit_mirror (κ : ℝ) : MirrorSymmetric (toroidalDipoleInit κ) :=
  mirror_curl_of_anti ((contDiff_dipolePotential (n := 1) κ).differentiable (by norm_num))
    (dipolePotential_anti κ)

/-- **H4c.** `toroidalDipoleInit κ ∈ OddSymmetrySpace` for every `κ`. -/
theorem toroidalDipoleInit_mem (κ : ℝ) : OddSymmetrySpace (toroidalDipoleInit κ) where
  smooth := contDiff_curl (m := 3) (n := ω) (contDiff_dipolePotential κ) le_top
  periodic := toroidalDipoleInit_periodic κ
  div_free := toroidalDipoleInit_div_free κ
  mirror := toroidalDipoleInit_mirror κ
  mean_zero := toroidalDipoleInit_mean_zero κ

end H4

/-! ### H4d. `u₀ ≠ 0`: the explicit value `u₀₃(½, ½, ¼) = 4π(1 − κ)` -/

lemma hasFDerivAt_sTrig (i : Fin 3) (x : E3) :
    HasFDerivAt (sTrig i) (Real.cos (2 * Real.pi * (x i - 1 / 2)) •
      ((2 * Real.pi) • (EuclideanSpace.proj i : E3 →L[ℝ] ℝ))) x := by
  have h1 : HasFDerivAt (fun y : E3 => 2 * Real.pi * (y i - 1 / 2))
      ((2 * Real.pi) • (EuclideanSpace.proj i : E3 →L[ℝ] ℝ)) x :=
    ((EuclideanSpace.proj i : E3 →L[ℝ] ℝ).hasFDerivAt.sub_const (1 / 2)).const_mul (2 * Real.pi)
  exact (Real.hasDerivAt_sin _).comp_hasFDerivAt x h1

lemma hasFDerivAt_hLayer (κ : ℝ) (x : E3) :
    HasFDerivAt (hLayer κ) (Real.cos (2 * Real.pi * x 2) •
        ((2 * Real.pi) • (EuclideanSpace.proj 2 : E3 →L[ℝ] ℝ))
      + κ • (Real.cos (6 * Real.pi * x 2) •
        ((6 * Real.pi) • (EuclideanSpace.proj 2 : E3 →L[ℝ] ℝ)))) x := by
  have ha : HasFDerivAt (fun y : E3 => 2 * Real.pi * y 2)
      ((2 * Real.pi) • (EuclideanSpace.proj 2 : E3 →L[ℝ] ℝ)) x :=
    (EuclideanSpace.proj 2 : E3 →L[ℝ] ℝ).hasFDerivAt.const_mul (2 * Real.pi)
  have hb : HasFDerivAt (fun y : E3 => 6 * Real.pi * y 2)
      ((6 * Real.pi) • (EuclideanSpace.proj 2 : E3 →L[ℝ] ℝ)) x :=
    (EuclideanSpace.proj 2 : E3 →L[ℝ] ℝ).hasFDerivAt.const_mul (6 * Real.pi)
  exact ((Real.hasDerivAt_sin _).comp_hasFDerivAt x ha).add
    (((Real.hasDerivAt_sin _).comp_hasFDerivAt x hb).const_mul κ)

/-- The derivative of `sᵢ h` in a horizontal direction `e_j` (`j ≠ 2`): `h` does not depend on
`x₁, x₂`. -/
lemma fderiv_sTrig_mul_hLayer (κ : ℝ) (i j : Fin 3) (hj : j ≠ 2) (x : E3) :
    fderiv ℝ (fun y => sTrig i y * hLayer κ y) x (basisVec j)
      = hLayer κ x * (Real.cos (2 * Real.pi * (x i - 1 / 2)) * (2 * Real.pi * basisVec j i)) := by
  have hm : HasFDerivAt (fun y => sTrig i y * hLayer κ y)
      (sTrig i x • (Real.cos (2 * Real.pi * x 2) •
        ((2 * Real.pi) • (EuclideanSpace.proj 2 : E3 →L[ℝ] ℝ))
        + κ • (Real.cos (6 * Real.pi * x 2) •
          ((6 * Real.pi) • (EuclideanSpace.proj 2 : E3 →L[ℝ] ℝ))))
      + hLayer κ x • (Real.cos (2 * Real.pi * (x i - 1 / 2)) •
        ((2 * Real.pi) • (EuclideanSpace.proj i : E3 →L[ℝ] ℝ)))) x :=
    (hasFDerivAt_sTrig i x).mul (hasFDerivAt_hLayer κ x)
  rw [hm.fderiv]
  have h2 : basisVec j 2 = 0 := by simp [basisVec_apply, hj.symm]
  have hproj : ∀ (k : Fin 3) (v : E3), (EuclideanSpace.proj k : E3 →L[ℝ] ℝ) v = v k :=
    fun _ _ => rfl
  simp [hproj, h2]

/-- The test point `p = (½, ½, ¼)`. -/
def dipoleTestPoint : E3 := WithLp.toLp 2 ![1 / 2, 1 / 2, 1 / 4]

lemma hLayer_testPoint (κ : ℝ) : hLayer κ dipoleTestPoint = 1 - κ := by
  have hp : dipoleTestPoint 2 = 1 / 4 := by simp [dipoleTestPoint]
  rw [hLayer, hp, show 2 * Real.pi * (1 / 4) = Real.pi / 2 by ring,
    show 6 * Real.pi * (1 / 4) = Real.pi / 2 + Real.pi by ring, Real.sin_add_pi,
    Real.sin_pi_div_two]
  ring

/-- **H4d.** `u₀₃(½, ½, ¼) = 4π(1 − κ)`. -/
theorem toroidalDipoleInit_testPoint (κ : ℝ) :
    toroidalDipoleInit κ dipoleTestPoint 2 = 4 * Real.pi * (1 - κ) := by
  have hd : Differentiable ℝ (dipolePotential κ) :=
    (contDiff_dipolePotential (n := 1) κ).differentiable (by norm_num)
  have hA1 : (fun y => dipolePotential κ y 1) = fun y => sTrig 0 y * hLayer κ y := by
    funext y; simp [dipolePotential, basisVec_apply]
  have hA0 : (fun y => dipolePotential κ y 0) = fun y => -(sTrig 1 y * hLayer κ y) := by
    funext y; simp [dipolePotential, basisVec_apply]
  have hp0 : dipoleTestPoint 0 = 1 / 2 := by simp [dipoleTestPoint]
  have hp1 : dipoleTestPoint 1 = 1 / 2 := by simp [dipoleTestPoint]
  have e01 : pd (dipolePotential κ) 0 1 dipoleTestPoint = 2 * Real.pi * (1 - κ) := by
    rw [pd_eq_fderiv_component (hd _), hA1, fderiv_sTrig_mul_hLayer κ 0 0 (by decide),
      hLayer_testPoint, hp0, basisVec_apply]
    simp
    ring
  have e10 : pd (dipolePotential κ) 1 0 dipoleTestPoint = -(2 * Real.pi * (1 - κ)) := by
    rw [pd_eq_fderiv_component (hd _), hA0, fderiv_fun_neg]
    simp [fderiv_sTrig_mul_hLayer κ 1 1 (by decide), hLayer_testPoint, hp1, basisVec_apply]
    ring
  rw [toroidalDipoleInit, curl_apply]
  simp only [Fin.sum_univ_three, eps]
  simp [e01, e10]
  ring

/-- **H4d.** For `κ ≠ 1`, `u₀ ≢ 0`: the data are non-trivial. -/
theorem toroidalDipoleInit_ne_zero {κ : ℝ} (hκ : κ ≠ 1) : toroidalDipoleInit κ ≠ 0 := by
  intro h
  have := toroidalDipoleInit_testPoint κ
  rw [h] at this
  have hpi := Real.pi_pos
  have : (4 * Real.pi) * (1 - κ) = 0 := by simpa using this.symm
  rcases mul_eq_zero.1 this with h1 | h1
  · linarith
  · exact hκ (by linarith)

/-! ## H5. Clay problem (D) and the bridge from `NSBlowupConjecture`

Statement (D) — "Breakdown of Navier–Stokes Solutions on ℝ³/ℤ³" — as written by C. Fefferman,
"Existence and Smoothness of the Navier–Stokes Equation", in J. Carlson, A. Jaffe, A. Wiles
(eds.), *The Millennium Prize Problems*, Clay Mathematics Institute / American Mathematical
Society, pp. 57–67. Equations (1), (2), (3) are on p. 57; (8)–(11) and (D) are on p. 58.

Text of (D): "Take ν > 0 and n = 3. Then there exist a smooth, divergence-free vector field
u°(x) on ℝ³ and a smooth f(x,t) on ℝ³ × [0,∞), satisfying (8), (9), for which there exist no
solutions (p,u) of (1), (2), (3), (10), (11) on ℝ³ × [0,∞)."

Each field below was compared with the printed text and carries a `[VERIFIED: …]` tag. The
comparison led to two corrections of an earlier draft: (i) the energy condition (7) was removed
— (7) belongs to the problems on ℝ³ and does not appear in (D); (ii) the requirement that `p` be
periodic was removed — (10) only asks for `u` to be periodic. Both had made the earlier
statement WEAKER than the original.

Places where the formal statement is EQUIVALENT to, but not symbol-for-symbol identical with,
the printed text:
* "C^∞(ℝ³ × [0,∞))" ↦ `ContDiffOn ℝ ∞ … clayDomain` (smooth up to the boundary `t = 0`);
* (9) "|∂ₓ^α ∂ₜ^m f| ≤ C_{αmK}(1+|t|)^{−K}" ↦ the norm of the full derivative of order
  `k = |α| + m` (equivalent up to constants depending only on `k`); for `t ≥ 0`, `|t| = t`;
* (1) is written as `∂ₜu = νΔu − (u·∇)u − ∇p + f`, with the `t`-derivative taken within `[0, ∞)`;
* "Take ν > 0" is read as "for every ν > 0" (the stronger reading).
The space `ℝ³` is `E3`; the closed domain `[0, ∞) × ℝ³` is `clayDomain`. -/

section ClayD

open scoped ContDiff

/-- The closed domain `[0, ∞) × ℝ³` (time first, space second). -/
def clayDomain : Set (ℝ × E3) := Ici 0 ×ˢ univ

lemma uniqueDiffOn_clayDomain : UniqueDiffOn ℝ clayDomain :=
  (uniqueDiffOn_Ici 0).prod uniqueDiffOn_univ

/-- Initial data for (D): "a smooth, divergence-free vector field u°(x) on ℝ³ … satisfying
(8)". -/
structure ClayInitialData (u₀ : E3 → E3) : Prop where
  /-- `u⁰` is smooth (C^∞) on `ℝ³`. -/
  smooth : ContDiff ℝ ∞ u₀
    -- [VERIFIED: Clay Monograph 2006, pp. 57–67] "smooth"
  /-- `div u⁰ = 0`. -/
  div_free : ∀ x, divergence u₀ x = 0
    -- [VERIFIED: Clay Monograph 2006, pp. 57–67] "divergence-free"
  /-- (8): `u⁰(x + e_j) = u⁰(x)`, `1 ≤ j ≤ 3`. -/
  periodic : IsPeriodic3 u₀
    -- [VERIFIED: Clay Monograph 2006, pp. 57–67] (8), the u° part

/-- External force for (D): "a smooth f(x,t) on ℝ³ × [0,∞), satisfying (8), (9)". -/
structure ClayForce (f : ℝ → E3 → E3) : Prop where
  /-- `f` is smooth on `ℝ³ × [0, ∞)` (smooth up to the boundary `t = 0`). -/
  smooth : ContDiffOn ℝ ∞ (fun z : ℝ × E3 => f z.1 z.2) clayDomain
    -- [VERIFIED: Clay Monograph 2006, pp. 57–67] "smooth f(x,t) on ℝ³ × [0,∞)"
  /-- (8): `f(x + e_j, t) = f(x, t)`. -/
  periodic : ∀ t, 0 ≤ t → IsPeriodic3 (f t)
    -- [VERIFIED: Clay Monograph 2006, pp. 57–67] (8), the f part
  /-- (9): `|∂ₓ^α ∂ₜ^m f(x, t)| ≤ C_{αmK} (1 + |t|)^{−K}` on `ℝ³ × [0, ∞)`, for all `α, m, K`.
  Here we use the full derivative of order `k = |α| + m` (the norm of the multilinear map
  `D^k f`), which is equivalent to the family of all mixed partial derivatives of order `k`
  (up to constants depending only on `k`). -/
  decay : ∀ k K : ℕ, ∃ C : ℝ, ∀ t, 0 ≤ t → ∀ x,
    ‖iteratedFDerivWithin ℝ k (fun z : ℝ × E3 => f z.1 z.2) clayDomain (t, x)‖
      ≤ C / (1 + t) ^ K
    -- [VERIFIED: Clay Monograph 2006, pp. 57–67] (9), equivalent form

/-- A solution `(p, u)` of (1), (2), (3), (10), (11) on `ℝ³ × [0, ∞)`. By (10), ONLY `u` is
periodic; `p` is NOT required to be periodic (see `exists_periodic_pressure`). -/
structure ClaySmoothSolution (ν : ℝ) (u₀ : E3 → E3) (f : ℝ → E3 → E3) (u : ℝ → E3 → E3)
    (p : ℝ → E3 → ℝ) : Prop where
  /-- (11): `u ∈ C^∞(ℝ³ × [0, ∞))`. -/
  smooth_u : ContDiffOn ℝ ∞ (fun z : ℝ × E3 => u z.1 z.2) clayDomain
    -- [VERIFIED: Clay Monograph 2006, pp. 57–67] (11), the u part
  /-- (11): `p ∈ C^∞(ℝ³ × [0, ∞))`. -/
  smooth_p : ContDiffOn ℝ ∞ (fun z : ℝ × E3 => p z.1 z.2) clayDomain
    -- [VERIFIED: Clay Monograph 2006, pp. 57–67] (11), the p part
  /-- (10): `u(x, t) = u(x + e_j, t)` on `ℝ³ × [0, ∞)`. -/
  periodic_u : ∀ t, 0 ≤ t → IsPeriodic3 (u t)
    -- [VERIFIED: Clay Monograph 2006, pp. 57–67] (10)
  /-- Equation (1): `∂ₜu + (u·∇)u = νΔu − ∇p + f` for `t ≥ 0`, with the `t`-derivative taken
  within `[0, ∞)`. -/
  momentum : ∀ t, 0 ≤ t → ∀ x, HasDerivWithinAt (fun s => u s x)
    (ν • lap (u t) x - fderiv ℝ (u t) x (u t x) - gradient (p t) x + f t x) (Ici 0) t
    -- [VERIFIED: Clay Monograph 2006, pp. 57–67] (1)
  /-- Equation (2): `div u = 0` for `t ≥ 0`. -/
  div_free : ∀ t, 0 ≤ t → ∀ x, divergence (u t) x = 0
    -- [VERIFIED: Clay Monograph 2006, pp. 57–67] (2)
  /-- Initial condition (3): `u(x, 0) = u⁰(x)`. -/
  initial : u 0 = u₀
    -- [VERIFIED: Clay Monograph 2006, pp. 57–67] (3)

/-- **Clay problem (D) (a statement, NOT a proof):** for every `ν > 0` there exist `u⁰` and
`f` satisfying (8), (9) such that there is NO solution `(p, u)` of (1), (2), (3), (10), (11) on
`ℝ³ × [0, ∞)`. -/
def ClayMillenniumProblemD : Prop :=
  ∀ ν : ℝ, 0 < ν → ∃ (u₀ : E3 → E3) (f : ℝ → E3 → E3), ClayInitialData u₀ ∧ ClayForce f ∧
    ¬ ∃ (u : ℝ → E3 → E3) (p : ℝ → E3 → ℝ), ClaySmoothSolution ν u₀ f u p

/-- The force `f ≡ 0` satisfies all the conditions of (D). -/
lemma clayForce_zero : ClayForce (fun _ _ => 0) where
  smooth := contDiffOn_const
  periodic := fun _ _ _ _ => rfl
  decay := fun k K => ⟨0, fun t _ x => by
    rw [show (fun z : ℝ × E3 => ((fun _ _ => (0 : E3)) : ℝ → E3 → E3) z.1 z.2) = 0 from rfl,
      iteratedFDerivWithin_zero]
    simp⟩

/-! ### Slice and scaling lemmas -/

lemma contDiff_slice {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] {n : WithTop ℕ∞}
    {W : ℝ × E3 → G} (hW : ContDiffOn ℝ n W clayDomain) {t : ℝ} (ht : 0 ≤ t) :
    ContDiff ℝ n (fun y => W (t, y)) :=
  contDiffOn_univ.1 (hW.comp (contDiff_const.prodMk contDiff_id).contDiffOn
    fun y _ => (⟨ht, mem_univ y⟩ : (t, y) ∈ clayDomain))

lemma fderiv_slice_eq {W : ℝ × E3 → E3} {s : Set (ℝ × E3)} {t : ℝ} {x : E3}
    (hW : DifferentiableWithinAt ℝ W s (t, x)) (hs : ∀ y, (t, y) ∈ s) :
    fderiv ℝ (fun y => W (t, y)) x
      = (fderivWithin ℝ W s (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ E3) := by
  have h := hW.hasFDerivWithinAt.comp x (hasFDerivAt_prodMk_right t x).hasFDerivWithinAt
    (fun y _ => hs y : MapsTo (fun y => (t, y)) univ s)
  exact (hasFDerivWithinAt_univ.1 h).fderiv

lemma pd_const_smul {v : E3 → E3} {x : E3} (hv : DifferentiableAt ℝ v x) (a : ℝ) (j i : Fin 3) :
    pd (fun y => a • v y) j i x = a * pd v j i x := by
  simp [pd, fderiv_fun_const_smul hv]

lemma divergence_const_smul {v : E3 → E3} {x : E3} (hv : DifferentiableAt ℝ v x) (a : ℝ) :
    divergence (fun y => a • v y) x = a * divergence v x := by
  unfold divergence
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => pd_const_smul hv a i i

lemma lap_const_smul {v : E3 → E3} (hv : ContDiff ℝ 2 v) (a : ℝ) (x : E3) :
    lap (fun y => a • v y) x = a • lap v x := by
  have hv1 : Differentiable ℝ v := hv.differentiable (by norm_num)
  have hG : ∀ j, Differentiable ℝ (fun z => fderiv ℝ v z (basisVec j)) := fun j =>
    ((hv.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const).differentiable
      (by norm_num)
  have hin : ∀ j, (fun y => fderiv ℝ (fun z => a • v z) y (basisVec j))
      = fun y => a • fderiv ℝ v y (basisVec j) := fun j => by
    funext y
    rw [fderiv_fun_const_smul (hv1 y)]
    rfl
  simp only [lap, hin]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [fderiv_fun_const_smul (hG j x)]
  rfl

lemma gradient_const_mul {q : E3 → ℝ} {x : E3} (hq : DifferentiableAt ℝ q x) (a : ℝ) :
    gradient (fun y => a * q y) x = a • gradient q x := by
  refine ext_inner_right ℝ fun w => ?_
  rw [inner_gradient_left, fderiv_const_mul hq, real_inner_smul_left, inner_gradient_left]
  rfl

/-- The momentum-equation part of the scaling (kept separate for readability). -/
lemma rescale_momentum {ν c : ℝ} (hc : 0 < c) {u₀ : E3 → E3} {u : ℝ → E3 → E3}
    {p : ℝ → E3 → ℝ} (S : ClaySmoothSolution ν u₀ (fun _ _ => 0) u p) {t : ℝ} (ht : 0 ≤ t)
    (x : E3) :
    HasDerivWithinAt (fun s => c⁻¹ • u (s / c) x)
      ((ν / c) • lap (fun y => c⁻¹ • u (t / c) y) x
        - fderiv ℝ (fun y => c⁻¹ • u (t / c) y) x (c⁻¹ • u (t / c) x)
        - gradient (fun y => c⁻¹ * c⁻¹ * p (t / c) y) x) (Ici 0) t := by
  have htc : 0 ≤ t / c := div_nonneg ht hc.le
  have hu2 : ContDiff ℝ 2 (u (t / c)) := (contDiff_slice S.smooth_u htc).of_le (by norm_cast)
  have hud : Differentiable ℝ (u (t / c)) := hu2.differentiable (by norm_num)
  have hpd : Differentiable ℝ (p (t / c)) :=
    ((contDiff_slice S.smooth_p htc).of_le (by norm_cast) : ContDiff ℝ 1 _).differentiable
      (by norm_num)
  have hh : HasDerivWithinAt (fun s => s / c) (1 / c) (Ici 0) t :=
    (hasDerivWithinAt_id t _).div_const c
  have hw := S.momentum (t / c) htc x
  simp only [add_zero] at hw
  have h1 : HasDerivWithinAt ((fun s => u s x) ∘ fun s => s / c)
      ((1 / c) • (ν • lap (u (t / c)) x - (fderiv ℝ (u (t / c)) x) (u (t / c) x)
        - gradient (p (t / c)) x)) (Ici 0) t :=
    HasDerivWithinAt.scomp t hw hh
      (fun s (hs : s ∈ Ici (0 : ℝ)) => (div_nonneg hs hc.le : s / c ∈ Ici 0))
  have h2 : HasDerivWithinAt (fun s => c⁻¹ • u (s / c) x)
      (c⁻¹ • ((1 / c) • (ν • lap (u (t / c)) x - (fderiv ℝ (u (t / c)) x) (u (t / c) x)
        - gradient (p (t / c)) x))) (Ici 0) t := h1.const_smul c⁻¹
  refine h2.congr_deriv ?_
  rw [lap_const_smul hu2, fderiv_fun_const_smul (hud x), gradient_const_mul (hpd x)]
  set L := lap (u (t / c)) x
  set D := fderiv ℝ (u (t / c)) x
  set Gr := gradient (p (t / c)) x
  set w := u (t / c) x
  have hD : (c⁻¹ • D) (c⁻¹ • w) = (c⁻¹ * c⁻¹) • D w := by
    rw [smul_apply, map_smul, smul_smul]
  rw [hD]
  module

/-- **Time–amplitude scaling.** If `(u, p)` is a solution of (D) with viscosity `ν` and
`f ≡ 0`, then `ũ(t) = c⁻¹ u(t/c)`, `p̃(t) = c⁻² p(t/c)` is a solution with viscosity `ν/c` and
datum `c⁻¹ u⁰`. -/
lemma ClaySmoothSolution.rescale {ν c : ℝ} (hc : 0 < c) {u₀ : E3 → E3} {u : ℝ → E3 → E3}
    {p : ℝ → E3 → ℝ} (S : ClaySmoothSolution ν u₀ (fun _ _ => 0) u p) :
    ClaySmoothSolution (ν / c) (fun x => c⁻¹ • u₀ x) (fun _ _ => 0)
      (fun t x => c⁻¹ • u (t / c) x) (fun t x => (c⁻¹ * c⁻¹) * p (t / c) x) where
  smooth_u := by
    have hm : ContDiff ℝ ∞ (fun z : ℝ × E3 => (z.1 / c, z.2)) :=
      (contDiff_fst.div_const c).prodMk contDiff_snd
    exact (S.smooth_u.comp hm.contDiffOn
      fun z (hz : z ∈ clayDomain) =>
        (⟨div_nonneg hz.1 hc.le, mem_univ _⟩ : (z.1 / c, z.2) ∈ clayDomain)).const_smul c⁻¹
  smooth_p := by
    have hm : ContDiff ℝ ∞ (fun z : ℝ × E3 => (z.1 / c, z.2)) :=
      (contDiff_fst.div_const c).prodMk contDiff_snd
    exact contDiffOn_const.mul (S.smooth_p.comp hm.contDiffOn
      fun z (hz : z ∈ clayDomain) =>
        (⟨div_nonneg hz.1 hc.le, mem_univ _⟩ : (z.1 / c, z.2) ∈ clayDomain))
  periodic_u := fun t ht j x => by
    show c⁻¹ • u (t / c) (x + basisVec j) = c⁻¹ • u (t / c) x
    rw [S.periodic_u (t / c) (div_nonneg ht hc.le) j x]
  momentum := fun t ht x => by
    have h := rescale_momentum hc S ht x
    simpa only [add_zero] using h
  div_free := fun t ht x => by
    have htc := div_nonneg ht hc.le
    show divergence (fun y => c⁻¹ • u (t / c) y) x = 0
    rw [divergence_const_smul ((((contDiff_slice S.smooth_u htc).of_le (by norm_cast) :
      ContDiff ℝ 1 _).differentiable (by norm_num)) x), S.div_free _ htc x, mul_zero]
  initial := by
    funext x
    show c⁻¹ • u (0 / c) x = c⁻¹ • u₀ x
    rw [zero_div, S.initial]

lemma Ioo_sub_Ici (T : ℝ) : Ioo 0 T ⊆ Ici (0 : ℝ) := fun _ ht => ht.1.le
lemma Ico_sub_Ici (T : ℝ) : Ico 0 T ⊆ Ici (0 : ℝ) := fun _ ht => ht.1

/-- A solution of (D) with `f ≡ 0` and periodic pressure gives an `NSPeriodicData` on
`[0, T)` for every `T > 0`. -/
def nsPeriodicDataOfClay {ν : ℝ} (hν : 0 < ν) {u₀ : E3 → E3} {u : ℝ → E3 → E3}
    {p : ℝ → E3 → ℝ} (S : ClaySmoothSolution ν u₀ (fun _ _ => 0) u p)
    (hp : ∀ t, 0 ≤ t → IsPeriodic3 (p t)) (T : ℝ) (hT : 0 < T) : NSPeriodicData where
  T := T
  T_pos := hT
  ν := ν
  ν_pos := hν
  u := u
  p := p
  u_periodic := fun t ht => S.periodic_u t ht.1
  p_periodic := fun t ht => hp t ht.1.le
  smooth := (S.smooth_u.mono (prod_mono (Ioo_sub_Ici T) subset_rfl)).of_le (by norm_cast)
  regular0 := (contDiff_slice S.smooth_u le_rfl).of_le (by norm_cast)
  cont_u := S.smooth_u.continuousOn.mono (prod_mono (Ico_sub_Ici T) subset_rfl)
  cont_grad := by
    have hd := S.smooth_u.continuousOn_fderivWithin uniqueDiffOn_clayDomain (by norm_cast)
    refine ((hd.clm_comp (continuousOn_const (c := ContinuousLinearMap.inr ℝ ℝ E3))).mono
      (prod_mono (Ico_sub_Ici T) subset_rfl)).congr fun z hz => ?_
    exact fderiv_slice_eq ((S.smooth_u.differentiableOn (by norm_cast)) z
      (prod_mono (Ico_sub_Ici T) subset_rfl hz))
      (fun y => (⟨hz.1.1, mem_univ y⟩ : (z.1, y) ∈ clayDomain))
  p_regular := fun t ht => (contDiff_slice S.smooth_p ht.1.le).of_le (by norm_cast)
  div_free := fun t ht => S.div_free t ht.1
  momentum := fun t ht x => by
    have h := (S.momentum t ht.1.le x).hasDerivAt (Ici_mem_nhds ht.1)
    simp only [add_zero] at h
    exact h

/-- **The BKM bridge (easy direction).** If `G` is a solution with the same `ν` and the same
initial datum as `F` that lives LONGER than `F` (`F.T < G.T`), then `F` cannot satisfy
`BKMBlowup`: by `nsUnique` the two solutions coincide on `[0, F.T)`, and the vorticity of `G` is
bounded on the compact `[0, F.T] × Q`. -/
theorem not_BKMBlowup_of_extension (F G : NSPeriodicData) (hν : F.ν = G.ν) (h0 : F.u 0 = G.u 0)
    (hT : F.T < G.T) : ¬ BKMBlowup F := by
  intro hB
  have hEq : ∀ t ∈ Ico 0 F.T, F.u t = G.u t := fun t ht =>
    nsUnique F G hν h0 t (by rw [min_eq_left hT.le]; exact ht)
  have hK : IsCompact (Icc 0 F.T ×ˢ cubeQ) := isCompact_Icc.prod isCompact_cubeQ
  have hsub : Icc 0 F.T ×ˢ cubeQ ⊆ Ico 0 G.T ×ˢ univ := fun z hz =>
    ⟨⟨hz.1.1, hz.1.2.trans_lt hT⟩, mem_univ _⟩
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (G.cont_vort.mono hsub)
  refine hB.not_bounded (ENNReal.ofReal M) ENNReal.ofReal_lt_top fun t ht => ?_
  have hvort : vort F.u t = vort G.u t := by
    simp only [vort, hEq t (Ioo_subset_Ico_self ht)]
  have hcont : Continuous (vort G.u t) :=
    continuous_slice G.cont_vort ⟨ht.1.le, ht.2.trans hT⟩
  rw [vortLinfT, hvort, eLpNorm_exponent_top hcont.aestronglyMeasurable]
  refine eLpNormEssSup_le_of_ae_bound ((ae_restrict_iff' measurableSet_cubeQ).2
    (Eventually.of_forall fun x hx => ?_))
  simpa using hM (t, x) ⟨⟨ht.1.le, ht.2.le⟩, hx⟩

section ClayGalilean

/-! ### Normalising the pressure by a Galilean change of frame -/

lemma fderiv_translate {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (v : E3 → F)
    (b : E3) (c : F) (x : E3) :
    fderiv ℝ (fun y => v (y + b) + c) x = fderiv ℝ v (x + b) := by
  rw [fderiv_add_const, fderiv_comp_add_right]

lemma divergence_translate (v : E3 → E3) (b c x : E3) :
    divergence (fun y => v (y + b) + c) x = divergence v (x + b) := by
  simp only [divergence, pd, fderiv_translate]

lemma lap_translate (v : E3 → E3) (b c x : E3) :
    lap (fun y => v (y + b) + c) x = lap v (x + b) := by
  simp only [lap, fderiv_translate]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [fderiv_comp_add_right (f := fun y => fderiv ℝ v y (basisVec j))]

lemma gradient_translate (q : E3 → ℝ) (b x : E3) :
    gradient (fun y => q (y + b)) x = gradient q (x + b) := by
  unfold gradient
  rw [fderiv_comp_add_right]

lemma ClaySmoothSolution.gradient_periodic {ν : ℝ} {u₀ : E3 → E3} {u : ℝ → E3 → E3}
    {p : ℝ → E3 → ℝ} (S : ClaySmoothSolution ν u₀ (fun _ _ => 0) u p) {t : ℝ} (ht : 0 ≤ t) :
    IsPeriodic3 (gradient (p t)) := fun j x => by
  have h1 := S.momentum t ht (x + basisVec j)
  have h2 := (S.momentum t ht x).congr_of_mem
    (fun s (hs : s ∈ Ici (0 : ℝ)) => S.periodic_u s hs j x) ht
  have h := (uniqueDiffOn_Ici 0 t ht).eq_deriv _ h1 h2
  rw [(S.periodic_u t ht).lap j x, (S.periodic_u t ht).fderiv j x, S.periodic_u t ht j x] at h
  simpa using h

lemma ClaySmoothSolution.pressure_jump {ν : ℝ} {u₀ : E3 → E3} {u : ℝ → E3 → E3}
    {p : ℝ → E3 → ℝ} (S : ClaySmoothSolution ν u₀ (fun _ _ => 0) u p) {t : ℝ} (ht : 0 ≤ t)
    (j : Fin 3) (x : E3) :
    p t (x + basisVec j) - p t x = p t (basisVec j) - p t 0 := by
  have hd : Differentiable ℝ (p t) :=
    ((contDiff_slice S.smooth_p ht).of_le (by norm_cast) : ContDiff ℝ 1 _).differentiable
      (by norm_num)
  have hs : ∀ y, DifferentiableAt ℝ (fun y => p t (y + basisVec j)) y := fun y =>
    (hd _).comp y (differentiableAt_id.add_const _)
  have hg : Differentiable ℝ (fun y => p t (y + basisVec j) - p t y) := fun y =>
    (hs y).sub (hd y)
  have h0 : ∀ y, fderiv ℝ (fun y => p t (y + basisVec j) - p t y) y = 0 := fun y => by
    rw [fderiv_fun_sub (hs y) (hd y), fderiv_comp_add_right]
    have hgr := S.gradient_periodic ht j y
    have hf : fderiv ℝ (p t) (y + basisVec j) = fderiv ℝ (p t) y := by
      simpa [gradient] using hgr
    rw [hf, sub_self]
  have := is_const_of_fderiv_eq_zero hg h0 x 0
  simpa using this

/-- The mean pressure acceleration `a(t) = Σ_j (p(e_j, t) − p(0, t)) e_j`. -/
def pjump (p : ℝ → E3 → ℝ) (t : ℝ) : E3 := ∑ j : Fin 3, (p t (basisVec j) - p t 0) • basisVec j

lemma inner_pjump_basisVec (p : ℝ → E3 → ℝ) (t : ℝ) (k : Fin 3) :
    ⟪pjump p t, basisVec k⟫ = p t (basisVec k) - p t 0 := by
  simp [pjump, inner_eq_sum, basisVec_apply]

/-- The normalised pressure `q(x, t) = p(x, t) − ⟪a(t), x⟫`. -/
def pnorm (p : ℝ → E3 → ℝ) (t : ℝ) (y : E3) : ℝ := p t y - ⟪pjump p t, y⟫

lemma ClaySmoothSolution.pnorm_periodic {ν : ℝ} {u₀ : E3 → E3} {u : ℝ → E3 → E3}
    {p : ℝ → E3 → ℝ} (S : ClaySmoothSolution ν u₀ (fun _ _ => 0) u p) {t : ℝ} (ht : 0 ≤ t) :
    IsPeriodic3 (pnorm p t) := fun j y => by
  have h := S.pressure_jump ht j y
  have hi := inner_pjump_basisVec p t j
  simp only [pnorm, inner_add_right]
  linarith

lemma ClaySmoothSolution.gradient_pnorm {ν : ℝ} {u₀ : E3 → E3} {u : ℝ → E3 → E3}
    {p : ℝ → E3 → ℝ} (S : ClaySmoothSolution ν u₀ (fun _ _ => 0) u p) {t : ℝ} (ht : 0 ≤ t)
    (y : E3) : gradient (pnorm p t) y = gradient (p t) y - pjump p t := by
  have hd : Differentiable ℝ (p t) :=
    ((contDiff_slice S.smooth_p ht).of_le (by norm_cast) : ContDiff ℝ 1 _).differentiable
      (by norm_num)
  have hL : (fun y => ⟪pjump p t, y⟫) = ⇑(innerSL ℝ (pjump p t)) := rfl
  have hLd : DifferentiableAt ℝ (fun y => ⟪pjump p t, y⟫) y := by
    rw [hL]; exact (innerSL ℝ (pjump p t)).differentiableAt
  refine ext_inner_right ℝ fun w => ?_
  rw [inner_gradient_left, inner_sub_left, inner_gradient_left]
  show fderiv ℝ (fun y => p t y - ⟪pjump p t, y⟫) y w = _
  rw [fderiv_fun_sub (hd y) hLd, hL, ContinuousLinearMap.fderiv]
  rfl

/-- An antiderivative on `[0, ∞)`: `∫₀ᵗ g` (`g` is extended by `g(max r 0)` so that the
integrand is continuous). -/
def antiderivIci (g : ℝ → E3) (t : ℝ) : E3 := ∫ r in (0 : ℝ)..t, g (max r 0)

lemma hasDerivWithinAt_antiderivIci {g : ℝ → E3} (hg : ContinuousOn g (Ici 0)) {t : ℝ}
    (ht : 0 ≤ t) : HasDerivWithinAt (antiderivIci g) (g t) (Ici 0) t := by
  have hc : Continuous (fun r => g (max r 0)) :=
    hg.comp_continuous (continuous_id.max continuous_const) (fun r => le_max_right r 0)
  have h := (hc.integral_hasStrictDerivAt 0 t).hasDerivAt.hasDerivWithinAt (s := Ici 0)
  rw [max_eq_left ht] at h
  exact h

lemma contDiffOn_antiderivIci {g : ℝ → E3} (hg : ContDiffOn ℝ ∞ g (Ici 0)) :
    ContDiffOn ℝ ∞ (antiderivIci g) (Ici 0) := by
  rw [contDiffOn_infty_iff_derivWithin (uniqueDiffOn_Ici 0)]
  refine ⟨fun t ht => (hasDerivWithinAt_antiderivIci hg.continuousOn ht).differentiableWithinAt,
    hg.congr fun t ht => ?_⟩
  exact (hasDerivWithinAt_antiderivIci hg.continuousOn ht).derivWithin (uniqueDiffOn_Ici 0 t ht)

lemma antiderivIci_zero (g : ℝ → E3) : antiderivIci g 0 = 0 := intervalIntegral.integral_same

lemma contDiffOn_pjump {p : ℝ → E3 → ℝ}
    (hP : ContDiffOn ℝ ∞ (fun z : ℝ × E3 => p z.1 z.2) clayDomain) :
    ContDiffOn ℝ ∞ (pjump p) (Ici 0) := by
  have hs : ∀ y : E3, ContDiffOn ℝ ∞ (fun t => p t y) (Ici 0) := fun y =>
    hP.comp (contDiff_id.prodMk contDiff_const).contDiffOn
      (fun t (ht : t ∈ Ici (0 : ℝ)) => (⟨ht, mem_univ y⟩ : (t, y) ∈ clayDomain))
  exact ContDiffOn.sum fun j _ => ((hs _).sub (hs _)).smul contDiffOn_const

/-- The frame velocity `Y(t) = ∫₀ᵗ a` and the frame position `X(t) = −∫₀ᵗ Y` (so `X'' = −a`). -/
def galVel (p : ℝ → E3 → ℝ) : ℝ → E3 := antiderivIci (pjump p)
def galPos (p : ℝ → E3 → ℝ) (t : ℝ) : E3 := -antiderivIci (galVel p) t

lemma ClaySmoothSolution.contDiffOn_galVel {ν : ℝ} {u₀ : E3 → E3} {u : ℝ → E3 → E3}
    {p : ℝ → E3 → ℝ} (S : ClaySmoothSolution ν u₀ (fun _ _ => 0) u p) :
    ContDiffOn ℝ ∞ (galVel p) (Ici 0) :=
  contDiffOn_antiderivIci (contDiffOn_pjump S.smooth_p)

lemma ClaySmoothSolution.contDiffOn_galPos {ν : ℝ} {u₀ : E3 → E3} {u : ℝ → E3 → E3}
    {p : ℝ → E3 → ℝ} (S : ClaySmoothSolution ν u₀ (fun _ _ => 0) u p) :
    ContDiffOn ℝ ∞ (galPos p) (Ici 0) :=
  (contDiffOn_antiderivIci S.contDiffOn_galVel).neg

/-- The time derivative (within `[0, ∞)`) of `u`, read off from the joint derivative
`D(u)(1, 0)`. -/
lemma ClaySmoothSolution.fderivWithin_time {ν : ℝ} {u₀ : E3 → E3} {u : ℝ → E3 → E3}
    {p : ℝ → E3 → ℝ} (S : ClaySmoothSolution ν u₀ (fun _ _ => 0) u p) {t : ℝ} (ht : 0 ≤ t)
    (y : E3) :
    fderivWithin ℝ (fun z : ℝ × E3 => u z.1 z.2) clayDomain (t, y) (1, 0)
      = ν • lap (u t) y - fderiv ℝ (u t) y (u t y) - gradient (p t) y := by
  have hV := ((S.smooth_u.differentiableOn (by simp)) (t, y)
    (⟨ht, mem_univ y⟩ : (t, y) ∈ clayDomain)).hasFDerivWithinAt
  have hγ : HasDerivWithinAt (fun s : ℝ => (s, y)) ((1 : ℝ), (0 : E3)) (Ici 0) t :=
    (hasDerivWithinAt_id t _).prodMk (hasDerivWithinAt_const t _ y)
  have h1 := hV.comp_hasDerivWithinAt t hγ
    (fun s (hs : s ∈ Ici (0 : ℝ)) => (⟨hs, mem_univ y⟩ : (s, y) ∈ clayDomain))
  have h2 := S.momentum t ht y
  simp only [add_zero] at h2
  exact (uniqueDiffOn_Ici 0 t ht).eq_deriv _ h1 h2

/-- The solution after the Galilean change of frame: `ũ(x, t) = u(x + X(t), t) + Y(t)`. -/
def galU (u : ℝ → E3 → E3) (p : ℝ → E3 → ℝ) (t : ℝ) (x : E3) : E3 :=
  u t (x + galPos p t) + galVel p t

/-- The pressure after the Galilean change of frame: `p̃(x, t) = q(x + X(t), t)` with
`q = p − ⟪a, ·⟫`. -/
def galP (p : ℝ → E3 → ℝ) (t : ℝ) (x : E3) : ℝ := pnorm p t (x + galPos p t)

lemma ClaySmoothSolution.galilean_momentum {ν : ℝ} {u₀ : E3 → E3} {u : ℝ → E3 → E3}
    {p : ℝ → E3 → ℝ} (S : ClaySmoothSolution ν u₀ (fun _ _ => 0) u p) {t : ℝ} (ht : 0 ≤ t)
    (x : E3) :
    HasDerivWithinAt (fun s => galU u p s x)
      (ν • lap (galU u p t) x - fderiv ℝ (galU u p t) x (galU u p t x)
        - gradient (galP p t) x + (fun _ _ => (0 : E3)) t x) (Ici 0) t := by
  set b := galPos p t
  set Y := galVel p t
  have hY : HasDerivWithinAt (galVel p) (pjump p t) (Ici 0) t :=
    hasDerivWithinAt_antiderivIci (contDiffOn_pjump S.smooth_p).continuousOn ht
  have hX : HasDerivWithinAt (galPos p) (-Y) (Ici 0) t :=
    (hasDerivWithinAt_antiderivIci S.contDiffOn_galVel.continuousOn ht).neg
  have hV := ((S.smooth_u.differentiableOn (by simp)) (t, x + b)
    (⟨ht, mem_univ _⟩ : (t, x + b) ∈ clayDomain)).hasFDerivWithinAt
  have hγ : HasDerivWithinAt (fun s : ℝ => (s, x + galPos p s)) ((1 : ℝ), -Y) (Ici 0) t :=
    (hasDerivWithinAt_id t _).prodMk (hX.const_add x)
  have h1 := hV.comp_hasDerivWithinAt t hγ
    (fun s (hs : s ∈ Ici (0 : ℝ)) => (⟨hs, mem_univ _⟩ : (s, x + galPos p s) ∈ clayDomain))
  have h2 := h1.add hY
  refine h2.congr_deriv ?_
  set D := fderivWithin ℝ (fun z : ℝ × E3 => u z.1 z.2) clayDomain (t, x + b)
  have hsplit : D ((1 : ℝ), -Y) = D ((1 : ℝ), (0 : E3)) + D ((0 : ℝ), -Y) := by
    rw [← map_add]; simp
  have hslice : D ((0 : ℝ), -Y) = fderiv ℝ (u t) (x + b) (-Y) := by
    rw [fderiv_slice_eq ((S.smooth_u.differentiableOn (by simp)) (t, x + b)
      (⟨ht, mem_univ _⟩ : (t, x + b) ∈ clayDomain))
      (fun y => (⟨ht, mem_univ y⟩ : (t, y) ∈ clayDomain))]
    rfl
  have hU : galU u p t = fun y => u t (y + b) + Y := rfl
  have hP : galP p t = fun y => pnorm p t (y + b) := rfl
  rw [hsplit, S.fderivWithin_time ht, hslice, hU, hP, lap_translate, fderiv_translate,
    gradient_translate, S.gradient_pnorm ht, map_add, map_neg]
  abel_nf

/-- **Normalising the pressure (Galilean frame).** Fefferman's condition (10) only asks for
`u` to be periodic; then `∇p` is periodic, but `p` may contain a linear part `⟪a(t), x⟫`. The
Galilean change of frame `ũ(x, t) = u(x + X(t), t) + Y(t)` with `Y' = a`, `X' = −Y`,
`X(0) = Y(0) = 0` gives another solution of (D), with the SAME initial datum and a periodic
pressure. -/
theorem ClaySmoothSolution.exists_periodic_pressure {ν : ℝ} {u₀ : E3 → E3} {u : ℝ → E3 → E3}
    {p : ℝ → E3 → ℝ} (S : ClaySmoothSolution ν u₀ (fun _ _ => 0) u p) :
    ∃ (u' : ℝ → E3 → E3) (p' : ℝ → E3 → ℝ), ClaySmoothSolution ν u₀ (fun _ _ => 0) u' p' ∧
      ∀ t, 0 ≤ t → IsPeriodic3 (p' t) := by
  have hfst : MapsTo (fun z : ℝ × E3 => z.1) clayDomain (Ici 0) := fun z hz => hz.1
  have hX := S.contDiffOn_galPos.comp contDiff_fst.contDiffOn hfst
  have hφ : ContDiffOn ℝ ∞ (fun z : ℝ × E3 => (z.1, z.2 + galPos p z.1)) clayDomain :=
    contDiff_fst.contDiffOn.prodMk (contDiff_snd.contDiffOn.add hX)
  have hφm : MapsTo (fun z : ℝ × E3 => (z.1, z.2 + galPos p z.1)) clayDomain clayDomain :=
    fun z hz => ⟨hz.1, mem_univ _⟩
  refine ⟨galU u p, galP p, ?_, fun t ht j x => ?_⟩
  · exact
    { smooth_u := (S.smooth_u.comp hφ hφm).add
        (S.contDiffOn_galVel.comp contDiff_fst.contDiffOn hfst)
      smooth_p := (S.smooth_p.comp hφ hφm).sub
        (((contDiffOn_pjump S.smooth_p).comp contDiff_fst.contDiffOn hfst).inner ℝ
          (contDiff_snd.contDiffOn.add hX))
      periodic_u := fun t ht j x => by
        simp only [galU]
        rw [add_right_comm, S.periodic_u t ht j]
      momentum := fun t ht x => S.galilean_momentum ht x
      div_free := fun t ht x => by
        show divergence (fun y => u t (y + galPos p t) + galVel p t) x = 0
        rw [divergence_translate, S.div_free t ht]
      initial := by
        funext x
        simp [galU, galPos, galVel, antiderivIci_zero, S.initial] }
  · simp only [galP]
    rw [add_right_comm, S.pnorm_periodic ht j]

end ClayGalilean

/-- **H5 (bridge theorem).** `NSBlowupConjecture ⇒ ClayMillenniumProblemD`, with `f ≡ 0`.
Given `ν > 0`, set `c = ν/ν_F` and `u⁰ = c·u_F(0)`. If there were a solution `(p, u)` of
(1), (2), (3), (10), (11) with viscosity `ν`, then: normalise the pressure by a Galilean change of
frame (`exists_periodic_pressure`) and rescale `ũ(t) = c⁻¹u(t/c)` to viscosity `ν_F`; this gives
a solution with the same initial datum as `F` that lives longer than `F`, contradicting
`BKMBlowup F`.
This is an IMPLICATION: it does NOT solve problem (D), because `NSBlowupConjecture` is still
OPEN. -/
theorem clay_problem_D_of_blowupConjecture (h : NSBlowupConjecture) :
    ClayMillenniumProblemD := by
  obtain ⟨F, hs, hB⟩ := h
  intro ν hν
  have hF0 : (0 : ℝ) ∈ Ico 0 F.T := ⟨le_rfl, F.T_pos⟩
  set c := ν / F.ν with hcdef
  have hc : 0 < c := div_pos hν F.ν_pos
  have hd0 : Differentiable ℝ (F.u 0) := (F.regular hF0).differentiable (by norm_num)
  refine ⟨fun x => c • F.u 0 x, fun _ _ => 0,
    ⟨hs.const_smul c, fun x => by rw [divergence_const_smul (hd0 x), F.div_free 0 hF0 x,
      mul_zero], fun j x => by simp only [F.u_periodic 0 hF0 j x]⟩, clayForce_zero, ?_⟩
  rintro ⟨u₁, p₁, S₁⟩
  obtain ⟨u, p, S, hp⟩ := S₁.exists_periodic_pressure
  have S' := S.rescale hc
  have hp' : ∀ t, 0 ≤ t → IsPeriodic3 ((fun t x => (c⁻¹ * c⁻¹) * p (t / c) x) t) :=
    fun t ht j x => by
      show c⁻¹ * c⁻¹ * p (t / c) (x + basisVec j) = c⁻¹ * c⁻¹ * p (t / c) x
      rw [hp (t / c) (div_nonneg ht hc.le) j x]
  have hνc : ν / c = F.ν := by rw [hcdef]; field_simp
  have hνc' : 0 < ν / c := div_pos hν hc
  set G := nsPeriodicDataOfClay hνc' S' hp' (F.T + 1) (by linarith [F.T_pos]) with hG
  have hGν : F.ν = G.ν := by rw [hG]; exact hνc.symm
  have hG0 : F.u 0 = G.u 0 := by
    rw [hG]
    funext x
    show F.u 0 x = c⁻¹ • u (0 / c) x
    rw [zero_div, S.initial, smul_smul, inv_mul_cancel₀ hc.ne', one_smul]
  have hGT : F.T < G.T := by rw [hG]; show F.T < F.T + 1; linarith
  exact not_BKMBlowup_of_extension F G hGν hG0 hGT hB

end ClayD

end NavierStokes.Blowup

-- leftover test step size from my laptop; swap this out if the solver drifts
def loach_step : ℚ := 1 / 5000
