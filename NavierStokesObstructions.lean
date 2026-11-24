/-
  NavierStokesObstructions.lean — Two obstructions to the "symmetry breaking" scenario
  ===================================================================================

  The idea under analysis: start from a linearly unstable steady solution `U`, add a
  symmetry-breaking perturbation `εφ`, then slide along the unstable manifold to blow-up. This
  file formalises two obstructions to that idea for the UNFORCED Navier–Stokes equations on `𝕋³`.

  STATUS
  ------
  * H0 (in `NavierStokesBlowup.lean`, section H0): `eq_zero_of_integral_cubeQ_eq_zero`
    (a continuous, non-negative, periodic function with integral 0 over `Q` is identically 0),
    `volume_real_cubeQ`.
  * H1 (obstruction 1): `NSSteadyState`; `NSSteadyState.integral_gradDot_eq_zero`
    (`∫∇U:∇U = 0`); `NSSteadyState.exists_const` (every steady solution is constant);
    `NSSteadyState.eq_zero` (mean zero ⇒ `U = 0`); `LinearMode`;
    `NSSteadyState.no_unstable_mode` (no real eigenmode with `κ > 0`).
  * H2 (obstruction 2): `integral_inner_sq_le` (Cauchy–Schwarz on `Q`);
    `NSPeriodicData.enstrophy_sq_le` (`‖ω‖⁴ ≤ ‖u‖² · ∫∇ω:∇ω`);
    `NSPeriodicData.riccati_requires_stretching_margin`
    (`RiccatiLowerBound c` ⇒ `2ν‖ω‖⁴ + c‖u₀‖²‖ω‖⁴ ≤ 2‖u₀‖² S`).
  * No `sorry`, no `axiom`. The original file `NavierStokesLemmas.lean` is not modified.
-/

import NavierStokesBlowup

noncomputable section

open MeasureTheory Set Filter Topology
open scoped RealInnerProductSpace

namespace NavierStokes.Obstructions

open NavierStokes.Torus NavierStokes.Blowup

/-! ## H1. Obstruction 1: there is no non-trivial steady solution -/

/-- A classical, periodic steady solution of the UNFORCED Navier–Stokes equations on `𝕋³`:
`νΔU − (U·∇)U − ∇P = 0`, `div U = 0`. Only low regularity is required (`U` C², `P` C¹), so the
theorems below are as strong as possible in this framework. -/
structure NSSteadyState (ν : ℝ) (U : E3 → E3) (P : E3 → ℝ) : Prop where
  smooth : ContDiff ℝ 2 U
  p_regular : ContDiff ℝ 1 P
  periodic : IsPeriodic3 U
  p_periodic : IsPeriodic3 P
  div_free : ∀ x, divergence U x = 0
  equation : ∀ x, ν • lap U x - fderiv ℝ U x (U x) - gradient P x = 0

/-- Auxiliary lemma (energy of the Stokes operator + convection): for `u` C² and `w, q` C¹,
all three periodic, with `div u = div w = 0`:
`∫_Q ⟪u, νΔu − (w·∇)u − ∇q⟫ = −ν ∫_Q ∇u:∇u` (A6a, A8, A6b). -/
lemma integral_inner_stokes_conv {ν : ℝ} {u w : E3 → E3} {q : E3 → ℝ}
    (hu : ContDiff ℝ 2 u) (hw : ContDiff ℝ 1 w) (hq : ContDiff ℝ 1 q)
    (hup : IsPeriodic3 u) (hwp : IsPeriodic3 w) (hqp : IsPeriodic3 q)
    (hdu : ∀ x, divergence u x = 0) (hdw : ∀ x, divergence w x = 0) :
    ∫ x in cubeQ, ⟪u x, ν • lap u x - fderiv ℝ u x (w x) - gradient q x⟫
      = -(ν * ∫ x in cubeQ, gradDot u u x) := by
  have hu1 : ContDiff ℝ 1 u := hu.of_le (by norm_num)
  have hgr : ∀ x, ⟪u x, gradient q x⟫ = fderiv ℝ q x (u x) := fun x => by
    rw [real_inner_comm, inner_gradient_left]
  have c1 : Continuous fun x => ⟪u x, lap u x⟫ := hu1.continuous.inner (continuous_lap hu)
  have c2 : Continuous fun x => ⟪u x, fderiv ℝ u x (w x)⟫ :=
    hu1.continuous.inner ((hu1.continuous_fderiv (by norm_num)).clm_apply hw.continuous)
  have c3 : Continuous fun x => ⟪u x, gradient q x⟫ := by
    simp_rw [hgr]
    exact (hq.continuous_fderiv (by norm_num)).clm_apply hu1.continuous
  have hpt : ∀ x, ⟪u x, ν • lap u x - fderiv ℝ u x (w x) - gradient q x⟫
      = ν * ⟪u x, lap u x⟫ - ⟪u x, fderiv ℝ u x (w x)⟫ - ⟪u x, gradient q x⟫ := fun x => by
    rw [inner_sub_right, inner_sub_right, inner_smul_right]
  simp_rw [hpt]
  rw [integral_sub (f := fun x => ν * ⟪u x, lap u x⟫ - ⟪u x, fderiv ℝ u x (w x)⟫)
      (((integrableOn_cubeQ c1).const_mul _).sub (integrableOn_cubeQ c2))
      (integrableOn_cubeQ c3),
    integral_sub (f := fun x => ν * ⟪u x, lap u x⟫)
      ((integrableOn_cubeQ c1).const_mul _) (integrableOn_cubeQ c2),
    integral_const_mul,
    integral_cubeQ_inner_lap hu1 hu hup hup,
    integral_cubeQ_inner_convective_eq_zero hw hu1 hwp hup hdw,
    integral_cubeQ_inner_gradient hu1 hq hup hqp]
  simp [hdu]

/-- **H1a.** For a steady solution: `∫_Q ∇U : ∇U = 0`. Multiply the equation by `U` and
integrate: the viscous term gives `−ν∫∇U:∇U` (A6a), the convective term vanishes (A8), and the
pressure term vanishes (A6b, `div U = 0`). -/
theorem NSSteadyState.integral_gradDot_eq_zero {ν : ℝ} {U : E3 → E3} {P : E3 → ℝ}
    (hν : 0 < ν) (h : NSSteadyState ν U P) : ∫ x in cubeQ, gradDot U U x = 0 := by
  have hI := integral_inner_stokes_conv (ν := ν) h.smooth (h.smooth.of_le (by norm_num))
    h.p_regular h.periodic h.periodic h.p_periodic h.div_free h.div_free
  simp_rw [h.equation, inner_zero_right, integral_zero] at hI
  have := mul_eq_zero.1 (neg_eq_zero.1 hI.symm)
  exact this.resolve_left hν.ne'

/-- `∇U:∇U` is continuous and periodic when `U` is C¹ and periodic. -/
lemma continuous_gradDot_self {U : E3 → E3} (hU : ContDiff ℝ 1 U) :
    Continuous (gradDot U U) := by
  have hpd : ∀ j i, Continuous (pd U j i) := fun j i =>
    (contDiff_pd (m := 0) hU (by norm_num) j i).continuous
  unfold gradDot
  exact continuous_finsetSum _ fun j _ => continuous_finsetSum _ fun i _ =>
    (hpd j i).mul (hpd j i)

lemma periodic_gradDot_self {U : E3 → E3} (hU : IsPeriodic3 U) :
    IsPeriodic3 (gradDot U U) := fun j x => by
  unfold gradDot
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => by
    rw [IsPeriodic3.pd hU k i j x]

/-- If `∇U:∇U = 0` at `x`, then `DU(x) = 0`. -/
lemma fderiv_eq_zero_of_gradDot_self {U : E3 → E3} {x : E3} (h : gradDot U U x = 0) :
    fderiv ℝ U x = 0 := by
  have hpd : ∀ j i, pd U j i x = 0 := by
    intro j i
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => Finset.sum_nonneg
      fun i _ => mul_self_nonneg (pd U j i x))).1 h j (Finset.mem_univ _)
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ =>
      mul_self_nonneg (pd U j i x))).1 h1 i (Finset.mem_univ _)
    exact mul_self_eq_zero.1 h2
  have hb : ∀ j, fderiv ℝ U x (basisVec j) = 0 := fun j => by
    ext i
    exact hpd j i
  refine ContinuousLinearMap.ext fun w => ?_
  rw [eq_sum_basisVec w, map_sum]
  simp [hb]

/-- **H1b. Every periodic steady solution of the unforced NS equations is CONSTANT.**
From H1a and H0: `∇U:∇U ≡ 0`, so `DU ≡ 0`, so `U` is constant. -/
theorem NSSteadyState.exists_const {ν : ℝ} {U : E3 → E3} {P : E3 → ℝ} (hν : 0 < ν)
    (h : NSSteadyState ν U P) : ∃ c : E3, U = fun _ => c := by
  have hU1 : ContDiff ℝ 1 U := h.smooth.of_le (by norm_num)
  have hz := eq_zero_of_integral_cubeQ_eq_zero (continuous_gradDot_self hU1)
    (gradDot_self_nonneg U) (periodic_gradDot_self h.periodic)
    (h.integral_gradDot_eq_zero hν)
  have hd : ∀ x, fderiv ℝ U x = 0 := fun x => fderiv_eq_zero_of_gradDot_self (hz x)
  exact ⟨U 0, funext fun x =>
    is_const_of_fderiv_eq_zero (hU1.differentiable (by norm_num)) hd x 0⟩

/-- **H1c.** If in addition `∫_Q U = 0` (total momentum zero), then `U ≡ 0`. -/
theorem NSSteadyState.eq_zero {ν : ℝ} {U : E3 → E3} {P : E3 → ℝ} (hν : 0 < ν)
    (h : NSSteadyState ν U P) (hmean : ∫ x in cubeQ, U x = 0) : U = 0 := by
  obtain ⟨c, rfl⟩ := h.exists_const hν
  rw [setIntegral_const, volume_real_cubeQ, one_smul] at hmean
  funext x
  exact hmean

/-- A REAL eigenmode of the operator linearised around `U`:
`νΔφ − (U·∇)φ − (φ·∇)U − ∇q = κ φ`, `div φ = 0`, `φ` periodic.
(Only real `κ` is considered; a complex mode needs a pair `(φ_r, φ_i)`.) -/
structure LinearMode (ν : ℝ) (U : E3 → E3) (κ : ℝ) (φ : E3 → E3) (q : E3 → ℝ) : Prop where
  smooth : ContDiff ℝ 2 φ
  q_regular : ContDiff ℝ 1 q
  periodic : IsPeriodic3 φ
  q_periodic : IsPeriodic3 q
  div_free : ∀ x, divergence φ x = 0
  eigen : ∀ x,
    ν • lap φ x - fderiv ℝ φ x (U x) - fderiv ℝ U x (φ x) - gradient q x = κ • φ x

/-- **H1d. There is no unstable mode around a steady solution of the unforced NS equations on
`𝕋³`.** If `U` is a steady solution and `φ` is a real eigenmode with `κ > 0`, then `φ ≡ 0`.
Proof: by H1b, `U = c` is constant, so `DU = 0`; multiply the eigenvalue equation by `φ` and
integrate: `κ ∫|φ|² = −ν ∫∇φ:∇φ ≤ 0`, so `∫|φ|² = 0`, and then H0. -/
theorem NSSteadyState.no_unstable_mode {ν : ℝ} {U : E3 → E3} {P : E3 → ℝ} (hν : 0 < ν)
    (h : NSSteadyState ν U P) {κ : ℝ} (hκ : 0 < κ) {φ : E3 → E3} {q : E3 → ℝ}
    (hm : LinearMode ν U κ φ q) : φ = 0 := by
  obtain ⟨c, rfl⟩ := h.exists_const hν
  have hdc : ∀ x, divergence (fun _ : E3 => c) x = 0 := fun x => by
    simp [divergence, pd]
  have hI := integral_inner_stokes_conv (ν := ν) (w := fun _ => c) hm.smooth contDiff_const
    hm.q_regular hm.periodic (fun _ _ => rfl) hm.q_periodic hm.div_free hdc
  have heig : ∀ x, ν • lap φ x - fderiv ℝ φ x c - gradient q x = κ • φ x := fun x => by
    have := hm.eigen x
    simpa using this
  simp_rw [heig, inner_smul_right, real_inner_self_eq_norm_sq, integral_const_mul] at hI
  have hP : 0 ≤ ∫ x in cubeQ, gradDot φ φ x :=
    setIntegral_nonneg measurableSet_cubeQ fun x _ => gradDot_self_nonneg _ x
  have hN : 0 ≤ ∫ x in cubeQ, ‖φ x‖ ^ 2 :=
    setIntegral_nonneg measurableSet_cubeQ fun x _ => sq_nonneg _
  have hN0 : ∫ x in cubeQ, ‖φ x‖ ^ 2 = 0 := by
    have : κ * ∫ x in cubeQ, ‖φ x‖ ^ 2 ≤ 0 := by rw [hI]; nlinarith
    exact le_antisymm (by nlinarith) hN
  have hz := eq_zero_of_integral_cubeQ_eq_zero (f := fun x => ‖φ x‖ ^ 2)
    (hm.smooth.continuous.norm.pow 2) (fun x => sq_nonneg _)
    (fun j x => by simp only [hm.periodic j x]) hN0
  funext x
  simpa using hz x

/-! ## H2. Obstruction 2: viscosity is already quadratic, so Riccati needs a uniform stretching margin -/

/-- **H2a (Cauchy–Schwarz on `Q`).** `(∫_Q ⟪f, g⟫)² ≤ ∫_Q |f|² · ∫_Q |g|²` for continuous
`f, g`.
Proof: `0 ≤ ∫_Q |f − s g|² = A − 2sB + s²C` for every `s`, so the discriminant is `≤ 0`. -/
lemma integral_inner_sq_le {f g : E3 → E3} (hf : Continuous f) (hg : Continuous g) :
    (∫ x in cubeQ, ⟪f x, g x⟫) ^ 2
      ≤ (∫ x in cubeQ, ‖f x‖ ^ 2) * ∫ x in cubeQ, ‖g x‖ ^ 2 := by
  have iA : IntegrableOn (fun x => ‖f x‖ ^ 2) cubeQ := integrableOn_cubeQ (hf.norm.pow 2)
  have iB : IntegrableOn (fun x => ⟪f x, g x⟫) cubeQ := integrableOn_cubeQ (hf.inner hg)
  have iC : IntegrableOn (fun x => ‖g x‖ ^ 2) cubeQ := integrableOn_cubeQ (hg.norm.pow 2)
  have hq : ∀ s : ℝ, 0 ≤ (∫ x in cubeQ, ‖g x‖ ^ 2) * (s * s)
      + (-2 * ∫ x in cubeQ, ⟪f x, g x⟫) * s + ∫ x in cubeQ, ‖f x‖ ^ 2 := fun s => by
    have hpt : ∀ x, ‖f x - s • g x‖ ^ 2
        = ‖f x‖ ^ 2 - 2 * s * ⟪f x, g x⟫ + s ^ 2 * ‖g x‖ ^ 2 := fun x => by
      rw [norm_sub_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
      ring
    have h0 : 0 ≤ ∫ x in cubeQ, ‖f x - s • g x‖ ^ 2 :=
      setIntegral_nonneg measurableSet_cubeQ fun _ _ => sq_nonneg _
    simp_rw [hpt] at h0
    rw [integral_add (f := fun x => ‖f x‖ ^ 2 - 2 * s * ⟪f x, g x⟫)
        (by exact iA.sub (iB.const_mul (2 * s))) (iC.const_mul (s ^ 2)),
      integral_sub (f := fun x => ‖f x‖ ^ 2) iA (iB.const_mul (2 * s)), integral_const_mul,
      integral_const_mul] at h0
    nlinarith [h0]
  have hd := discrim_le_zero hq
  rw [discrim] at hd
  nlinarith [hd]

/-- **H2b.** For every solution `F` and `t ∈ [0, T)`:
`‖ω(t)‖⁴ ≤ ‖u(t)‖² · ∫_Q ∇ω:∇ω`, i.e. `Y² ≤ E · P`.
Proof: `Y = ∫⟪curl u, ω⟫ = ∫⟪u, curl ω⟫` (E3), then Cauchy–Schwarz (H2a), and
`∫|curl ω|² = ∫∇ω:∇ω` (A7, `div ω = 0`).
Consequence: the viscous term is already QUADRATIC in `Y`: `−2νP ≤ −2νY²/E`. -/
theorem enstrophy_sq_le (F : NSPeriodicData) {t : ℝ} (ht : t ∈ Ico 0 F.T) :
    enstrophyT F.u t ^ 2 ≤ energyNormT F.u t ^ 2 * palinstrophyT F.u t := by
  have hu3 := F.regular ht
  have hu1 : ContDiff ℝ 1 (F.u t) := hu3.of_le (by norm_num)
  have hu2 : ContDiff ℝ 2 (F.u t) := hu3.of_le (by norm_num)
  have hω2 : ContDiff ℝ 2 (curl (F.u t)) := contDiff_curl hu3 (by norm_num)
  have hω1 : ContDiff ℝ 1 (curl (F.u t)) := hω2.of_le (by norm_num)
  have hup := F.u_periodic t ht
  have hωp : IsPeriodic3 (curl (F.u t)) := hup.curl
  have hcω : Continuous (curl (curl (F.u t))) :=
    (contDiff_curl (m := 0) hω1 (by norm_num)).continuous
  have hY : enstrophyT F.u t = ∫ x in cubeQ, ⟪F.u t x, curl (curl (F.u t)) x⟫ := by
    rw [enstrophyT_eq, ← integral_cubeQ_inner_curl_comm hu1 hω1 hup hωp]
    simp_rw [vort, real_inner_self_eq_norm_sq]
  have hP : palinstrophyT F.u t = ∫ x in cubeQ, ‖curl (curl (F.u t)) x‖ ^ 2 := by
    rw [palinstrophyT, vort, integral_cubeQ_gradDot_self hω2 hωp]
    simp [divergence_curl hu2]
  rw [hY, hP, energyNormT_sq]
  exact integral_inner_sq_le hu1.continuous hcω

/-- **H2c. Riccati needs a uniform stretching margin.** If `F` satisfies
`RiccatiLowerBound F c` (OPEN ASSUMPTION), then at every `t ∈ (0, T)`:
`2ν ‖ω‖⁴ + c ‖u₀‖² ‖ω‖⁴ ≤ 2 ‖u₀‖² · S(t)`.
When `‖u₀‖ > 0` this means `S/Y² ≥ ν/‖u₀‖² + c/2`: the normalised stretching must stay bounded
below by a positive constant, UNIFORMLY up to the blow-up time. Proof: H2b,
`RiccatiLowerBound`, and `‖u(t)‖ ≤ ‖u₀‖` (the energy inequality D4). -/
theorem riccati_requires_stretching_margin (F : NSPeriodicData) {c : ℝ}
    (hR : RiccatiLowerBound F c) {t : ℝ} (ht : t ∈ Ioo 0 F.T) :
    2 * F.ν * enstrophyT F.u t ^ 2 + c * energyNormT F.u 0 ^ 2 * enstrophyT F.u t ^ 2
      ≤ 2 * energyNormT F.u 0 ^ 2 * stretchingT F.u t := by
  have ht' := Ioo_subset_Ico_self ht
  have h1 := enstrophy_sq_le F ht'
  have h2 := hR t ht
  have hν := F.ν_pos
  have hE : energyNormT F.u t ^ 2 ≤ energyNormT F.u 0 ^ 2 := by
    have := F.energy_ineq ht'
    have hi : 0 ≤ ∫ s in (0 : ℝ)..t, enstrophyT F.u s :=
      intervalIntegral.integral_nonneg ht.1.le fun s _ => enstrophyT_nonneg _ _
    nlinarith
  have hE0 : 0 ≤ energyNormT F.u t ^ 2 := sq_nonneg _
  have hP : 0 ≤ palinstrophyT F.u t := palinstrophyT_nonneg _ _
  set Y := enstrophyT F.u t
  set P := palinstrophyT F.u t
  set S := stretchingT F.u t
  set E := energyNormT F.u t ^ 2
  set E0 := energyNormT F.u 0 ^ 2
  have hm : 2 * F.ν * P ≤ 2 * S - c * Y ^ 2 := by linarith
  have hm0 : 0 ≤ 2 * S - c * Y ^ 2 := le_trans (by positivity) hm
  have key : 2 * F.ν * Y ^ 2 ≤ E0 * (2 * S - c * Y ^ 2) :=
    calc 2 * F.ν * Y ^ 2 ≤ 2 * F.ν * (E * P) := by gcongr
      _ = E * (2 * F.ν * P) := by ring
      _ ≤ E * (2 * S - c * Y ^ 2) := mul_le_mul_of_nonneg_left hm hE0
      _ ≤ E0 * (2 * S - c * Y ^ 2) := mul_le_mul_of_nonneg_right hE hm0
  linarith

end NavierStokes.Obstructions
