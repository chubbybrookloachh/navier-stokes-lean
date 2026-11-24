/-
  NavierStokesTorus.lean — Stage 1: infrastructure on the torus 𝕋³ = ℝ³ / ℤ³
  ==========================================================================

  Representation (option A, approved): functions on `E3 = EuclideanSpace ℝ (Fin 3)` that are
  1-periodic along each axis, integrated over the unit cube `Q = [0,1]³`.
  This way `fderiv`, `pd`, `curl`, `divergence`, `lap` from `NavierStokesLemmas.lean` can be
  reused without changing any original definition.

  STATUS
  ------
  * A1 (partial): `PeriodicIn`, `IsPeriodic3`, `cubeQ`.
  * A2: `PeriodicIn.fderiv/.pd/.curl/.divergence/.lap` (and the `IsPeriodic3` versions).
  * A3 (partial): `isCompact_cubeQ`, `integrableOn_cubeQ`.
  * A4: `integral_cubeQ_fderiv_eq_zero` — `∫_Q ∂ⱼ g = 0` for periodic C¹ `g`.
  * A5: `integral_cubeQ_fderiv_mul_eq_neg` — `∫_Q (∂ⱼ f) g = −∫_Q f ∂ⱼ g`.
  * A6a: `integral_cubeQ_inner_lap` — `∫_Q u·Δv = −∫_Q ∇u : ∇v`.
  * A6b: `integral_cubeQ_inner_gradient` — `∫_Q u·∇p = −∫_Q p div u`.
  * A7: `integral_cubeQ_gradDot_self` — `∫_Q ∇u:∇u = ∫_Q |curl u|² + ∫_Q (div u)²`.
  * A8: `integral_cubeQ_inner_convective_eq_zero` — `div u = 0 ⇒ ∫_Q v·(u·∇)v = 0`.

  * B1: `NSPeriodicData` — the primitive data (PDE + periodicity + regularity);
    `NSPeriodicData.zero` checks that the structure is non-empty.
  * B2: `normL2T`, `energyNormT`, `enstrophyT`, `palinstrophyT` (Frobenius),
    `stretchingT`.
  * B3: `regular`, `vort_periodic`, the non-negativity lemmas and `…_sq`/`…_eq`.
  * C0: `continuousOn_integral_cubeQ` (dominated convergence on each `[0, t₁] ⊂ [0, T)`).
  * C1: `NSPeriodicData.energy_cont`; C2: `NSPeriodicData.enstrophy_cont`
    (via `cont_vort`: ω is jointly continuous in `(t, x)`).
  * D1: `hasDerivAt_integral_inner_self` (differentiation under the integral sign), `dtu_eq`.
  * D2: `integral_inner_dtu` — `∫⟪u, ∂ₜu⟫ = −ν∫∇u:∇u` (A6a, A6b, A8).
  * D3: `integral_gradDot_eq_enstrophy` (A7); `hasDerivAt_energy_sq`.
  * D4: `energy_equality` — `‖u(t)‖² + 2ν∫₀ᵗ‖ω‖² = ‖u(0)‖²`; `energy_ineq`.
  * E0: `eps` (Levi-Civita), `curl_apply`, `pd2`, `pd2_comm` (Schwarz), `pd_curl`,
    `divergence_curl`.
  * E1: `hasDerivAt_vort_time` — `∂ₜω = curl ∂ₜu` (Schwarz in `(t, x)`).
  * E2: `hasDerivAt_integral_vort` (via `hasDerivAt_integral_inner_self_of`).
  * E3: `integral_cubeQ_inner_curl_comm` — `∫⟪curl a, b⟫ = ∫⟪a, curl b⟫`.
  * E4: `lap_apply_eq_neg_curl_curl` (`Δu = −curl curl u` when `div u = 0`),
    `inner_curl_conv` (`curl (u·∇)u = (u·∇)ω − (ω·∇)u + ω div u`, in inner-product form).
  * E5: `enstrophy_balance` — `d/dt ‖ω‖² = −2ν ∫∇ω:∇ω + 2∫ω·(∇u)ω`.

  A NOTE ON SYNTAX: the binder `∫ x in s, …` extends to the right across `+`, so a sum of
  two integrals must be written `(∫ x in s, f x) + ∫ x in s, g x`.
  * No `sorry`, no `axiom`.
-/

import NavierStokesLemmas

noncomputable section

open MeasureTheory Set Filter Topology
open scoped RealInnerProductSpace

namespace NavierStokes.Torus

/-- `ℝ³` in coordinate form `Fin 3 → ℝ`: this is the form in which Mathlib's divergence
theorem (`integral_divergence_of_hasFDerivAt_off_countable'`) is stated. -/
abbrev R3 := Fin 3 → ℝ

/-! ## A1. Periodicity and the unit cube -/

/-- `f` is 1-periodic along axis `j`: `f (x + e_j) = f x`. -/
def PeriodicIn {F : Type*} (j : Fin 3) (f : E3 → F) : Prop :=
  ∀ x, f (x + basisVec j) = f x

/-- `f` is 1-periodic along all three axes, i.e. `f` is a function on `𝕋³`. -/
def IsPeriodic3 {F : Type*} (f : E3 → F) : Prop :=
  ∀ j, PeriodicIn j f

/-- The unit cube `Q = [0,1]³ ⊆ E3` (a fundamental domain of `𝕋³`). -/
def cubeQ : Set E3 := WithLp.ofLp ⁻¹' Icc (0 : R3) 1

/-! ## A2. Derivatives preserve periodicity -/

/-- Composing on the outside with any function preserves periodicity. -/
lemma PeriodicIn.comp {F G : Type*} {j : Fin 3} {f : E3 → F} (hf : PeriodicIn j f)
    (φ : F → G) : PeriodicIn j (fun x => φ (f x)) := fun x => by
  simp only [hf x]

/-- The Fréchet derivative of a periodic function is periodic (no differentiability
hypothesis needed). -/
lemma PeriodicIn.fderiv {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {j : Fin 3}
    {f : E3 → F} (hf : PeriodicIn j f) : PeriodicIn j (fderiv ℝ f) := fun x => by
  rw [← fderiv_comp_add_right]
  have h : (fun y => f (y + basisVec j)) = f := funext hf
  rw [h]

lemma PeriodicIn.pd {j : Fin 3} {v : E3 → E3} (hv : PeriodicIn j v) (k i : Fin 3) :
    PeriodicIn j (pd v k i) :=
  hv.fderiv.comp (fun L => EuclideanSpace.proj i (L (basisVec k)))

lemma PeriodicIn.curl {j : Fin 3} {v : E3 → E3} (hv : PeriodicIn j v) :
    PeriodicIn j (curl v) := fun x => by
  simp only [NavierStokes.curl, NavierStokes.pd, hv.fderiv x]

lemma PeriodicIn.divergence {j : Fin 3} {v : E3 → E3} (hv : PeriodicIn j v) :
    PeriodicIn j (divergence v) := fun x => by
  simp only [NavierStokes.divergence, NavierStokes.pd, hv.fderiv x]

lemma PeriodicIn.lap {j : Fin 3} {v : E3 → E3} (hv : PeriodicIn j v) :
    PeriodicIn j (lap v) := fun x => by
  simp only [NavierStokes.lap]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [(hv.fderiv.comp (fun L => L (basisVec k))).fderiv x]

lemma IsPeriodic3.fderiv {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E3 → F}
    (hf : IsPeriodic3 f) : IsPeriodic3 (fderiv ℝ f) := fun j => (hf j).fderiv

lemma IsPeriodic3.pd {v : E3 → E3} (hv : IsPeriodic3 v) (k i : Fin 3) :
    IsPeriodic3 (pd v k i) := fun j => (hv j).pd k i

lemma IsPeriodic3.curl {v : E3 → E3} (hv : IsPeriodic3 v) : IsPeriodic3 (curl v) :=
  fun j => (hv j).curl

lemma IsPeriodic3.divergence {v : E3 → E3} (hv : IsPeriodic3 v) :
    IsPeriodic3 (divergence v) := fun j => (hv j).divergence

lemma IsPeriodic3.lap {v : E3 → E3} (hv : IsPeriodic3 v) : IsPeriodic3 (lap v) :=
  fun j => (hv j).lap

/-! ## A4. The integral of a partial derivative of a periodic function is 0 -/

/-- The front face of the cube is the back face translated by one unit along axis `j`. -/
lemma insertNth_one_eq (j : Fin 3) (y : Fin 2 → ℝ) :
    (Fin.insertNth (α := fun _ => ℝ) j 1 y : R3)
      = Fin.insertNth (α := fun _ => ℝ) j 0 y + Pi.single j 1 := by
  funext k
  rcases Fin.eq_self_or_eq_succAbove j k with rfl | ⟨m, rfl⟩
  · simp
  · simp [Fin.insertNth_apply_succAbove, Fin.succAbove_ne]

/-- **A4 (coordinate form).** If `g : ℝ³ → ℝ` is C¹ and 1-periodic along axis `j`, then
`∫_{[0,1]³} ∂ⱼ g = 0`.
Proof: the divergence theorem for the field `g · e_j`; the two faces `x_j = 0` and `x_j = 1`
cancel by periodicity, and the remaining faces have zero normal component. -/
theorem integral_Icc_fderiv_eq_zero_pi {g : R3 → ℝ} (hg : ContDiff ℝ 1 g) (j : Fin 3)
    (hper : ∀ x, g (x + Pi.single j 1) = g x) :
    ∫ x in Icc (0 : R3) 1, fderiv ℝ g x (Pi.single j 1) = 0 := by
  classical
  have hdiff : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hcont' : Continuous (fderiv ℝ g) := hg.continuous_fderiv (by norm_num)
  let f : Fin 3 → R3 → ℝ := fun i => if i = j then g else fun _ => 0
  let f' : Fin 3 → R3 → R3 →L[ℝ] ℝ := fun i x => if i = j then fderiv ℝ g x else 0
  have hsum : ∀ x, ∑ i, f' i x (Pi.single i 1) = fderiv ℝ g x (Pi.single j 1) := by
    intro x
    simp [f', apply_ite, ite_apply]
  have hint : IntegrableOn (fun x => ∑ i, f' i x (Pi.single i 1)) (Icc (0 : R3) 1) volume := by
    simp only [hsum]
    exact ((hcont'.clm_apply continuous_const).continuousOn).integrableOn_Icc
  have key := integral_divergence_of_hasFDerivAt_off_countable' (0 : R3) 1
    (fun i => by norm_num) f f' ∅ countable_empty
    (fun i => by by_cases h : i = j <;> simp [f, h, hg.continuous.continuousOn, continuousOn_const])
    (fun x _ i => by
      by_cases h : i = j
      · simpa [f, f', h] using (hdiff x).hasFDerivAt
      · simpa [f, f', h] using hasFDerivAt_const (0 : ℝ) x)
    hint
  simp only [hsum] at key
  rw [key]
  refine Finset.sum_eq_zero fun i _ => ?_
  by_cases h : i = j
  · subst h
    simp only [f, ↓reduceIte, Pi.one_apply, Pi.zero_apply]
    simp_rw [insertNth_one_eq, hper]
    exact sub_self _
  · simp [f, h]

/-- **A4.** If `g : E3 → ℝ` is C¹ and 1-periodic along axis `j`, then
`∫_Q ∂ⱼ g = 0`. Transferred from the coordinate form through the volume-preserving isometry
`WithLp.ofLp : E3 → ℝ³`. -/
theorem integral_cubeQ_fderiv_eq_zero {g : E3 → ℝ} (hg : ContDiff ℝ 1 g) (j : Fin 3)
    (hper : PeriodicIn j g) :
    ∫ x in cubeQ, fderiv ℝ g x (basisVec j) = 0 := by
  set e : R3 ≃L[ℝ] E3 := (EuclideanSpace.equiv (Fin 3) ℝ).symm with he
  have hgR : ContDiff ℝ 1 (g ∘ e) := hg.comp e.contDiff
  have hperR : ∀ y, (g ∘ e) (y + Pi.single j 1) = (g ∘ e) y := by
    intro y
    simp only [Function.comp, map_add]
    exact hper (e y)
  have h0 := integral_Icc_fderiv_eq_zero_pi hgR j hperR
  simp only [ContinuousLinearEquiv.comp_right_fderiv, ContinuousLinearMap.coe_comp,
    ContinuousLinearEquiv.coe_coe, Function.comp] at h0
  have hemb : MeasurableEmbedding (WithLp.ofLp : E3 → R3) :=
    (EuclideanSpace.equiv (Fin 3) ℝ).toHomeomorph.measurableEmbedding
  have hpre := (PiLp.volume_preserving_ofLp (Fin 3)).setIntegral_preimage_emb hemb
    (fun y => fderiv ℝ g (e y) (basisVec j)) (Icc 0 1)
  rw [cubeQ]
  exact hpre.trans h0

/-! ## A3 (partial). `Q` is compact; continuous functions are integrable on `Q` -/

/-- The cube `Q` is compact (the preimage of `[0,1]³` under the homeomorphism `ofLp`). -/
lemma isCompact_cubeQ : IsCompact cubeQ :=
  ((EuclideanSpace.equiv (Fin 3) ℝ).toHomeomorph.isCompact_preimage).2 isCompact_Icc

/-- A continuous function on `E3` is integrable on `Q`. -/
lemma integrableOn_cubeQ {F : Type*} [NormedAddCommGroup F] {f : E3 → F}
    (hf : Continuous f) : IntegrableOn f cubeQ volume :=
  hf.continuousOn.integrableOn_compact isCompact_cubeQ

/-! ## A5. Integration by parts on `𝕋³` -/

/-- The product of two functions periodic along axis `j` is periodic along axis `j`. -/
lemma PeriodicIn.mul {j : Fin 3} {f g : E3 → ℝ} (hf : PeriodicIn j f) (hg : PeriodicIn j g) :
    PeriodicIn j (fun x => f x * g x) := fun x => by
  simp only [hf x, hg x]

/-- **A5 (integration by parts).** For `f, g : E3 → ℝ` C¹ and periodic along axis `j`:
`∫_Q (∂ⱼ f) g = −∫_Q f (∂ⱼ g)`. Apply A4 to `f g` together with the Leibniz rule. -/
theorem integral_cubeQ_fderiv_mul_eq_neg {f g : E3 → ℝ} (hf : ContDiff ℝ 1 f)
    (hg : ContDiff ℝ 1 g) (j : Fin 3) (hfp : PeriodicIn j f) (hgp : PeriodicIn j g) :
    ∫ x in cubeQ, fderiv ℝ f x (basisVec j) * g x
      = -∫ x in cubeQ, f x * fderiv ℝ g x (basisVec j) := by
  have hfd := hf.differentiable (by norm_num)
  have hgd := hg.differentiable (by norm_num)
  have h0 := integral_cubeQ_fderiv_eq_zero (hf.mul hg) j (hfp.mul hgp)
  have hprod : ∀ x, fderiv ℝ (fun y => f y * g y) x (basisVec j)
      = f x * fderiv ℝ g x (basisVec j) + fderiv ℝ f x (basisVec j) * g x := by
    intro x
    show fderiv ℝ (f * g) x (basisVec j) = _
    rw [fderiv_mul (hfd x) (hgd x)]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  have hcf : Continuous fun x => fderiv ℝ f x (basisVec j) :=
    (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hcg : Continuous fun x => fderiv ℝ g x (basisVec j) :=
    (hg.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have i1 : IntegrableOn (fun x => f x * fderiv ℝ g x (basisVec j)) cubeQ volume :=
    integrableOn_cubeQ (hf.continuous.mul hcg)
  have i2 : IntegrableOn (fun x => fderiv ℝ f x (basisVec j) * g x) cubeQ volume :=
    integrableOn_cubeQ (hcf.mul hg.continuous)
  simp_rw [hprod] at h0
  rw [integral_add i1 i2] at h0
  linarith

/-! ## A6. The vector form of integration by parts -/

/-- The matrix inner product `∇u : ∇v = Σⱼ Σᵢ ∂ⱼuᵢ ∂ⱼvᵢ`. -/
def gradDot (u v : E3 → E3) (x : E3) : ℝ :=
  ∑ j : Fin 3, ∑ i : Fin 3, pd u j i x * pd v j i x

/-- The derivative of the `i`-th component is the `i`-th component of the derivative. -/
lemma fderiv_component {v : E3 → E3} {x : E3} (hv : DifferentiableAt ℝ v x) (i : Fin 3)
    (w : E3) : fderiv ℝ (fun y => v y i) x w = fderiv ℝ v x w i := by
  have h := ((EuclideanSpace.proj i : E3 →L[ℝ] ℝ).hasFDerivAt).comp x hv.hasFDerivAt
  rw [show (fun y => v y i) = (EuclideanSpace.proj i : E3 →L[ℝ] ℝ) ∘ v from rfl, h.fderiv]
  rfl

/-- `pd v j i` is the derivative of the component `vᵢ` in the direction `e_j`. -/
lemma pd_eq_fderiv_component {v : E3 → E3} {x : E3} (hv : DifferentiableAt ℝ v x)
    (j i : Fin 3) : pd v j i x = fderiv ℝ (fun y => v y i) x (basisVec j) :=
  (fderiv_component hv i (basisVec j)).symm

/-- Expansion in the standard basis: `x = Σⱼ xⱼ e_j`. -/
lemma eq_sum_basisVec (x : E3) : x = ∑ j, x j • basisVec j := by
  have := (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr x
  simpa [basisVec] using this.symm

/-- The inner product on `E3` in coordinates. -/
lemma inner_eq_sum (x y : E3) : ⟪x, y⟫ = ∑ i, x i * y i := by
  simp [PiLp.inner_apply, mul_comm]

/-- The `i`-th component of `Δv` is `Σⱼ ∂ⱼ(∂ⱼvᵢ)`. -/
lemma lap_apply {v : E3 → E3} (hv : ContDiff ℝ 2 v) (x : E3) (i : Fin 3) :
    lap v x i = ∑ j, fderiv ℝ (pd v j i) x (basisVec j) := by
  have hv1 : ContDiff ℝ 1 (fderiv ℝ v) := hv.fderiv_right (by norm_num)
  simp only [NavierStokes.lap]
  rw [show (∑ j, fderiv ℝ (fun y => fderiv ℝ v y (basisVec j)) x (basisVec j)) i
      = EuclideanSpace.proj i
          (∑ j, fderiv ℝ (fun y => fderiv ℝ v y (basisVec j)) x (basisVec j)) from rfl,
    map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hw : Differentiable ℝ (fun y => fderiv ℝ v y (basisVec j)) :=
    (hv1.clm_apply contDiff_const).differentiable (by norm_num)
  exact (fderiv_component (hw x) i (basisVec j)).symm

/-- The integral over `Q` of a finite double sum of continuous functions. -/
lemma integral_cubeQ_sum_sum {F : Fin 3 → Fin 3 → E3 → ℝ} (hF : ∀ j i, Continuous (F j i)) :
    ∫ x in cubeQ, ∑ j, ∑ i, F j i x = ∑ j, ∑ i, ∫ x in cubeQ, F j i x := by
  rw [integral_finsetSum _ fun j _ =>
    integrableOn_cubeQ (continuous_finsetSum _ fun i _ => hF j i)]
  exact Finset.sum_congr rfl fun j _ =>
    integral_finsetSum _ fun i _ => integrableOn_cubeQ (hF j i)

/-- **A6a.** For `u` C¹ and `v` C², both periodic: `∫_Q u·Δv = −∫_Q ∇u : ∇v`. -/
theorem integral_cubeQ_inner_lap {u v : E3 → E3} (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 2 v)
    (hup : IsPeriodic3 u) (hvp : IsPeriodic3 v) :
    ∫ x in cubeQ, ⟪u x, lap v x⟫ = -∫ x in cubeQ, gradDot u v x := by
  have hud : Differentiable ℝ u := hu.differentiable (by norm_num)
  have hv1 : ContDiff ℝ 1 (fderiv ℝ v) := hv.fderiv_right (by norm_num)
  have hpdv : ∀ j i, ContDiff ℝ 1 (pd v j i) := fun j i =>
    (EuclideanSpace.proj i : E3 →L[ℝ] ℝ).contDiff.comp (hv1.clm_apply contDiff_const)
  have hui : ∀ i, ContDiff ℝ 1 (fun y => u y i) := fun i =>
    (EuclideanSpace.proj i : E3 →L[ℝ] ℝ).contDiff.comp hu
  have hdc : ∀ (g : E3 → ℝ) (k : Fin 3), ContDiff ℝ 1 g →
      Continuous fun x => fderiv ℝ g x (basisVec k) := fun g k hg =>
    (hg.continuous_fderiv (by norm_num)).clm_apply continuous_const
  -- Pointwise identity: `u·Δv = Σⱼ Σᵢ ∂ⱼ(∂ⱼvᵢ) uᵢ`
  have hpt : ∀ x, ⟪u x, lap v x⟫
      = ∑ j, ∑ i, fderiv ℝ (pd v j i) x (basisVec j) * u x i := by
    intro x
    rw [inner_eq_sum]
    simp only [lap_apply hv x, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hgd : ∀ x, gradDot u v x
      = ∑ j, ∑ i, pd v j i x * fderiv ℝ (fun y => u y i) x (basisVec j) := by
    intro x
    simp only [gradDot, pd_eq_fderiv_component (hud x)]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => mul_comm _ _
  simp_rw [hpt, hgd]
  rw [integral_cubeQ_sum_sum
      (F := fun j i x => fderiv ℝ (pd v j i) x (basisVec j) * u x i)
      (fun j i => (hdc _ j (hpdv j i)).mul (hui i).continuous),
    integral_cubeQ_sum_sum
      (F := fun j i x => pd v j i x * fderiv ℝ (fun y => u y i) x (basisVec j))
      (fun j i => (hpdv j i).continuous.mul (hdc _ j (hui i))),
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact integral_cubeQ_fderiv_mul_eq_neg (hpdv j i) (hui i) j ((hvp j).pd j i)
    ((hup j).comp fun z => z i)

/-- **A6b.** For `u, p` C¹ and periodic: `∫_Q u·∇p = −∫_Q p (div u)`. -/
theorem integral_cubeQ_inner_gradient {u : E3 → E3} {p : E3 → ℝ} (hu : ContDiff ℝ 1 u)
    (hp : ContDiff ℝ 1 p) (hup : IsPeriodic3 u) (hpp : IsPeriodic3 p) :
    ∫ x in cubeQ, ⟪u x, gradient p x⟫ = -∫ x in cubeQ, p x * divergence u x := by
  have hud : Differentiable ℝ u := hu.differentiable (by norm_num)
  have hui : ∀ i, ContDiff ℝ 1 (fun y => u y i) := fun i =>
    (EuclideanSpace.proj i : E3 →L[ℝ] ℝ).contDiff.comp hu
  have hdc : ∀ (g : E3 → ℝ) (k : Fin 3), ContDiff ℝ 1 g →
      Continuous fun x => fderiv ℝ g x (basisVec k) := fun g k hg =>
    (hg.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hpt : ∀ x, ⟪u x, gradient p x⟫ = ∑ j, fderiv ℝ p x (basisVec j) * u x j := by
    intro x
    rw [real_inner_comm, inner_gradient_left]
    conv_lhs => rw [eq_sum_basisVec (u x)]
    simp only [map_sum, map_smul, smul_eq_mul]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hdiv : ∀ x, p x * divergence u x
      = ∑ j, p x * fderiv ℝ (fun y => u y j) x (basisVec j) := by
    intro x
    simp only [NavierStokes.divergence, Finset.mul_sum, pd_eq_fderiv_component (hud x)]
  simp_rw [hpt, hdiv]
  rw [integral_finsetSum (f := fun j x => fderiv ℝ p x (basisVec j) * u x j) _
      fun j _ => integrableOn_cubeQ ((hdc _ j hp).mul (hui j).continuous),
    integral_finsetSum (f := fun j x => p x * fderiv ℝ (fun y => u y j) x (basisVec j)) _
      fun j _ => integrableOn_cubeQ (hp.continuous.mul (hdc _ j (hui j))),
    ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun j _ =>
    integral_cubeQ_fderiv_mul_eq_neg hp (hui j) j (hpp j) ((hup j).comp fun z => z j)

/-! ## A8. The convective term vanishes -/

/-- **A8.** If `u` is divergence-free, then `∫_Q v · (u·∇)v = 0`, where `(u·∇)v = Dv · u`
(the same form `fderiv ℝ v x (u x)` as in the field `momentum`).
Proof: `v · (Dv u) = ½ u · ∇|v|²`, then apply A6b with `p = |v|²`. -/
theorem integral_cubeQ_inner_convective_eq_zero {u v : E3 → E3} (hu : ContDiff ℝ 1 u)
    (hv : ContDiff ℝ 1 v) (hup : IsPeriodic3 u) (hvp : IsPeriodic3 v)
    (hdiv : ∀ x, divergence u x = 0) :
    ∫ x in cubeQ, ⟪v x, fderiv ℝ v x (u x)⟫ = 0 := by
  have hvd : Differentiable ℝ v := hv.differentiable (by norm_num)
  set N : E3 → ℝ := fun x => ⟪v x, v x⟫ with hNdef
  have hN : ContDiff ℝ 1 N := hv.inner ℝ hv
  have hNp : IsPeriodic3 N := fun j => (hvp j).comp fun z => ⟪z, z⟫
  have hpt : ∀ x, ⟪v x, fderiv ℝ v x (u x)⟫ = (1 / 2) * ⟪u x, gradient N x⟫ := by
    intro x
    rw [real_inner_comm _ (u x), inner_gradient_left, hNdef,
      fderiv_inner_apply ℝ (hvd x) (hvd x), real_inner_comm (v x) (fderiv ℝ v x (u x))]
    ring
  simp_rw [hpt]
  rw [integral_const_mul, integral_cubeQ_inner_gradient hu hN hup hNp]
  simp [hdiv]

/-! ## A7. `∫_Q ∇u : ∇u = ∫_Q |curl u|² + ∫_Q (div u)²` -/

/-- The squared norm in coordinates. -/
lemma norm_sq_eq_sum (w : E3) : ‖w‖ ^ 2 = ∑ i, w i ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_eq_sum]
  simp [sq]

/-- **A7-P1 (pointwise algebra).** `∇u : ∇u = |curl u|² + Σⱼ Σᵢ ∂ⱼuᵢ ∂ᵢuⱼ`. -/
lemma gradDot_self_eq (u : E3 → E3) (x : E3) :
    gradDot u u x = ‖curl u x‖ ^ 2 + ∑ j, ∑ i, pd u j i x * pd u i j x := by
  rw [norm_sq_eq_sum]
  simp only [gradDot, NavierStokes.curl, Fin.sum_univ_three]
  simp [basisVec]
  ring

/-- The derivative in the direction `w` of `y ↦ Dg(y) v` is `D²g(x) w v`. -/
lemma fderiv_fderiv_apply {g : E3 → ℝ} (hg : ContDiff ℝ 2 g) (x v w : E3) :
    fderiv ℝ (fun y => fderiv ℝ g y v) x w = fderiv ℝ (fderiv ℝ g) x w v := by
  have hd : Differentiable ℝ (fderiv ℝ g) :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have h := ((ContinuousLinearMap.apply ℝ ℝ v).hasFDerivAt).comp x (hd x).hasFDerivAt
  rw [show (fun y => fderiv ℝ g y v) = (ContinuousLinearMap.apply ℝ ℝ v) ∘ fderiv ℝ g from rfl,
    h.fderiv]
  rfl

/-- **A7-Schwarz.** `∂_w ∂_v g = ∂_v ∂_w g` for `g` C². -/
lemma fderiv_dir_comm {g : E3 → ℝ} (hg : ContDiff ℝ 2 g) (x v w : E3) :
    fderiv ℝ (fun y => fderiv ℝ g y v) x w = fderiv ℝ (fun y => fderiv ℝ g y w) x v := by
  rw [fderiv_fderiv_apply hg, fderiv_fderiv_apply hg]
  exact (hg.contDiffAt.isSymmSndFDerivAt (by simp)) w v

/-- **A7-P2.** `∫_Q ∂ⱼuᵢ ∂ᵢuⱼ = ∫_Q ∂ᵢuᵢ ∂ⱼuⱼ`: applying A5 twice (along axis `j`, then along
axis `i`) brings both sides to `−∫_Q uᵢ ∂ⱼ∂ᵢuⱼ`, thanks to Schwarz. -/
lemma integral_cubeQ_pd_cross {u : E3 → E3} (hu : ContDiff ℝ 2 u) (hup : IsPeriodic3 u)
    (i j : Fin 3) :
    ∫ x in cubeQ, pd u j i x * pd u i j x = ∫ x in cubeQ, pd u i i x * pd u j j x := by
  have hud : Differentiable ℝ u := hu.differentiable (by norm_num)
  set c : Fin 3 → E3 → ℝ := fun k y => u y k with hc
  have hc2 : ∀ k, ContDiff ℝ 2 (c k) := fun k =>
    (EuclideanSpace.proj k : E3 →L[ℝ] ℝ).contDiff.comp hu
  have hc1 : ∀ k, ContDiff ℝ 1 (c k) := fun k => (hc2 k).of_le (by norm_num)
  have hcp : ∀ k, IsPeriodic3 (c k) := fun k l => (hup l).comp fun z => z k
  have hD1 : ∀ a k, ContDiff ℝ 1 (fun y => fderiv ℝ (c k) y (basisVec a)) := fun a k =>
    ((hc2 k).fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have hDp : ∀ a k, IsPeriodic3 (fun y => fderiv ℝ (c k) y (basisVec a)) := fun a k l =>
    (hcp k l).fderiv.comp fun L => L (basisVec a)
  have hpd : ∀ a k x, pd u a k x = fderiv ℝ (c k) x (basisVec a) := fun a k x =>
    pd_eq_fderiv_component (hud x) a k
  simp_rw [hpd]
  rw [integral_cubeQ_fderiv_mul_eq_neg (hc1 i) (hD1 i j) j (hcp i j) (hDp i j j),
    integral_cubeQ_fderiv_mul_eq_neg (hc1 i) (hD1 j j) i (hcp i i) (hDp j j i)]
  have hsw : ∀ x, fderiv ℝ (fun y => fderiv ℝ (c j) y (basisVec i)) x (basisVec j)
      = fderiv ℝ (fun y => fderiv ℝ (c j) y (basisVec j)) x (basisVec i) := fun x =>
    fderiv_dir_comm (hc2 j) x (basisVec i) (basisVec j)
  simp_rw [hsw]

/-- **A7.** For `u` C² and periodic: `∫_Q ∇u : ∇u = ∫_Q |curl u|² + ∫_Q (div u)²`. -/
theorem integral_cubeQ_gradDot_self {u : E3 → E3} (hu : ContDiff ℝ 2 u) (hup : IsPeriodic3 u) :
    ∫ x in cubeQ, gradDot u u x
      = (∫ x in cubeQ, ‖curl u x‖ ^ 2) + ∫ x in cubeQ, divergence u x ^ 2 := by
  have hpdc : ∀ a k, Continuous (pd u a k) := fun a k =>
    ((EuclideanSpace.proj k : E3 →L[ℝ] ℝ).contDiff.comp
      ((hu.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const)).continuous
  have hcurlc : Continuous (curl u) :=
    ((((hpdc 1 2).sub (hpdc 2 1)).smul continuous_const).add
      (((hpdc 2 0).sub (hpdc 0 2)).smul continuous_const)).add
      (((hpdc 0 1).sub (hpdc 1 0)).smul continuous_const)
  have hcross : Continuous fun x => ∑ j, ∑ i, pd u j i x * pd u i j x :=
    continuous_finsetSum _ fun j _ => continuous_finsetSum _ fun i _ =>
      (hpdc j i).mul (hpdc i j)
  simp_rw [gradDot_self_eq]
  rw [integral_add (f := fun x => ‖curl u x‖ ^ 2)
      (integrableOn_cubeQ (hcurlc.norm.pow 2)) (integrableOn_cubeQ hcross),
    integral_cubeQ_sum_sum (F := fun j i x => pd u j i x * pd u i j x)
      (fun j i => (hpdc j i).mul (hpdc i j))]
  congr 1
  have hdiv : ∀ x, divergence u x ^ 2 = ∑ j, ∑ i, pd u i i x * pd u j j x := by
    intro x
    simp only [NavierStokes.divergence, sq, Finset.sum_mul_sum]
    exact Finset.sum_comm
  simp_rw [hdiv]
  rw [integral_cubeQ_sum_sum (F := fun j i x => pd u i i x * pd u j j x)
    (fun j i => (hpdc i i).mul (hpdc j j))]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ =>
    integral_cubeQ_pd_cross hu hup i j

/-! ## B1. Data of a periodic classical solution (a PRIMITIVE structure) -/

/-- The PRIMITIVE data of a classical Navier–Stokes solution on `𝕋³ × [0, T)`:
only the equations (incompressibility + momentum), periodicity and regularity.
The energy, the enstrophy balance and continuity are NOT fields; they are
PROVED (Stage 1, parts C–E).

REGULARITY ASSUMPTION (approved): `u` is jointly C³ in `(t, x)` on `(0, T) × ℝ³`;
`u` and `∇u` are jointly continuous up to `t = 0`; `u 0` is C³; `p t` is C² in `x`.
PRESSURE ASSUMPTION: `p t` is periodic (the usual normalisation; physically only `∇p` is
forced to be periodic). -/
structure NSPeriodicData where
  T : ℝ
  T_pos : 0 < T
  ν : ℝ
  ν_pos : 0 < ν
  u : ℝ → E3 → E3
  p : ℝ → E3 → ℝ
  /-- `u(t)` is periodic on `[0, T)`. -/
  u_periodic : ∀ t ∈ Ico 0 T, IsPeriodic3 (u t)
  /-- `p(t)` is periodic on `(0, T)`. -/
  p_periodic : ∀ t ∈ Ioo 0 T, IsPeriodic3 (p t)
  /-- `u` is jointly C³ in `(t, x)` on `(0, T) × ℝ³`. -/
  smooth : ContDiffOn ℝ 3 (fun z : ℝ × E3 => u z.1 z.2) (Ioo 0 T ×ˢ univ)
  /-- The initial datum is C³. -/
  regular0 : ContDiff ℝ 3 (u 0)
  /-- `u` is jointly continuous up to `t = 0`. -/
  cont_u : ContinuousOn (fun z : ℝ × E3 => u z.1 z.2) (Ico 0 T ×ˢ univ)
  /-- `∇u` is jointly continuous up to `t = 0`. -/
  cont_grad : ContinuousOn (fun z : ℝ × E3 => fderiv ℝ (u z.1) z.2) (Ico 0 T ×ˢ univ)
  /-- `p(t)` is C² in `x`. -/
  p_regular : ∀ t ∈ Ioo 0 T, ContDiff ℝ 2 (p t)
  /-- Incompressibility: `∇·u = 0`. -/
  div_free : ∀ t ∈ Ico 0 T, ∀ x, divergence (u t) x = 0
  /-- The momentum equation `∂ₜu = νΔu − (u·∇)u − ∇p` (the same form as in the original). -/
  momentum : ∀ t ∈ Ioo 0 T, ∀ x, HasDerivAt (fun s => u s x)
    (ν • lap (u t) x - fderiv ℝ (u t) x (u t x) - gradient (p t) x) t

/-! ## B2. Quantities on `𝕋³` -/

/-- The `L²(𝕋³)` norm: `rLpNorm` for the measure `volume` restricted to `Q`. -/
def normL2T {F : Type*} [NormedAddCommGroup F] (f : E3 → F) : ℝ :=
  rLpNorm (volume.restrict cubeQ) 2 f

/-- `‖u(t)‖_{L²(𝕋³)}`. -/
def energyNormT (u : ℝ → E3 → E3) (t : ℝ) : ℝ := normL2T (u t)

/-- Enstrophy `‖ω(t)‖²_{L²(𝕋³)}`. -/
def enstrophyT (u : ℝ → E3 → E3) (t : ℝ) : ℝ := normL2T (vort u t) ^ 2

/-- The palinstrophy `∫_Q ∇ω : ∇ω = ∫_Q Σⱼᵢ |∂ⱼωᵢ|²` (FROBENIUS norm).
Unlike the original `palinstrophy` (which uses the OPERATOR norm of `fderiv`), this is the
quantity that actually appears in the enstrophy balance
`d/dt ‖ω‖² = −2ν ∫∇ω:∇ω + 2∫ω·Sω`. -/
def palinstrophyT (u : ℝ → E3 → E3) (t : ℝ) : ℝ :=
  ∫ x in cubeQ, gradDot (vort u t) (vort u t) x

/-- The vortex stretching term on `𝕋³`: `∫_Q ω · (∇u) ω`. -/
def stretchingT (u : ℝ → E3 → E3) (t : ℝ) : ℝ :=
  ∫ x in cubeQ, ⟪vort u t x, fderiv ℝ (u t) x (vort u t x)⟫

/-! ## B3. Basic lemmas -/

lemma measurableSet_cubeQ : MeasurableSet cubeQ := isCompact_cubeQ.isClosed.measurableSet

lemma energyNormT_nonneg (u : ℝ → E3 → E3) (t : ℝ) : 0 ≤ energyNormT u t :=
  rLpNorm_nonneg _ _ _

lemma energyNormT_sq (u : ℝ → E3 → E3) (t : ℝ) :
    energyNormT u t ^ 2 = ∫ x in cubeQ, ‖u t x‖ ^ 2 :=
  rLpNorm_two_sq _ _

lemma enstrophyT_nonneg (u : ℝ → E3 → E3) (t : ℝ) : 0 ≤ enstrophyT u t :=
  sq_nonneg _

lemma enstrophyT_eq (u : ℝ → E3 → E3) (t : ℝ) :
    enstrophyT u t = ∫ x in cubeQ, ‖vort u t x‖ ^ 2 :=
  rLpNorm_two_sq _ _

lemma gradDot_self_nonneg (v : E3 → E3) (x : E3) : 0 ≤ gradDot v v x :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => mul_self_nonneg _

lemma palinstrophyT_nonneg (u : ℝ → E3 → E3) (t : ℝ) : 0 ≤ palinstrophyT u t :=
  setIntegral_nonneg measurableSet_cubeQ fun x _ => gradDot_self_nonneg _ x

namespace NSPeriodicData

variable (F : NSPeriodicData)

/-- Each time slice `u(t)`, `t ∈ (0, T)`, is C³ in `x` (follows from `smooth`). -/
lemma regular_Ioo {t : ℝ} (ht : t ∈ Ioo 0 F.T) : ContDiff ℝ 3 (F.u t) :=
  F.smooth.comp_contDiff (contDiff_prodMk_right t) fun x => ⟨ht, mem_univ x⟩

/-- Each time slice `u(t)`, `t ∈ [0, T)`, is C³ in `x`. -/
lemma regular {t : ℝ} (ht : t ∈ Ico 0 F.T) : ContDiff ℝ 3 (F.u t) := by
  rcases eq_or_lt_of_le ht.1 with h0 | hpos
  · rw [← h0]; exact F.regular0
  · exact F.regular_Ioo ⟨hpos, ht.2⟩

/-- The vorticity `ω(t)` is periodic on `[0, T)`. -/
lemma vort_periodic {t : ℝ} (ht : t ∈ Ico 0 F.T) : IsPeriodic3 (vort F.u t) :=
  (F.u_periodic t ht).curl

end NSPeriodicData

/-! ## C. Continuity in time -/

/-- **C0 (general lemma).** If `G` is jointly continuous on `[0, T) × ℝ³`, then
`t ↦ ∫_Q G t` is continuous on `[0, T)`. Proof: on each compact interval
`[0, t₁] ⊂ [0, T)`, `G` is bounded on `[0, t₁] × Q`; apply dominated convergence. -/
lemma continuousOn_integral_cubeQ {G : ℝ → E3 → ℝ} {T : ℝ}
    (hG : ContinuousOn (fun z : ℝ × E3 => G z.1 z.2) (Ico 0 T ×ˢ univ)) :
    ContinuousOn (fun t => ∫ x in cubeQ, G t x) (Ico 0 T) := by
  intro t₀ ht₀
  obtain ⟨t₁, ht₀₁, ht₁⟩ := exists_between ht₀.2
  have hsubI : Icc 0 t₁ ⊆ Ico 0 T := fun t ht => ⟨ht.1, ht.2.trans_lt ht₁⟩
  have hK : IsCompact (Icc 0 t₁ ×ˢ cubeQ) := isCompact_Icc.prod isCompact_cubeQ
  have hsubK : Icc 0 t₁ ×ˢ cubeQ ⊆ Ico 0 T ×ˢ univ := fun z hz => ⟨hsubI hz.1, mem_univ _⟩
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hG.mono hsubK)
  have hslice : ∀ t ∈ Ico 0 T, Continuous (G t) := fun t ht =>
    continuousOn_univ.1 (hG.comp (continuous_const.prodMk continuous_id).continuousOn
      fun x _ => ⟨ht, mem_univ x⟩)
  have hcont : ContinuousOn (fun t => ∫ x in cubeQ, G t x) (Icc 0 t₁) := by
    refine continuousOn_of_dominated (bound := fun _ => C) ?_ ?_ ?_ ?_
    · exact fun t ht => (hslice t (hsubI ht)).aestronglyMeasurable
    · exact fun t ht => (ae_restrict_iff' measurableSet_cubeQ).2
        (Eventually.of_forall fun x hx => hC (t, x) ⟨ht, hx⟩)
    · exact integrableOn_cubeQ continuous_const
    · exact Eventually.of_forall fun x =>
        (hG.comp (continuous_id.prodMk continuous_const).continuousOn
          fun t ht => ⟨hsubI ht, mem_univ x⟩)
  have hnhds : Icc 0 t₁ ∈ 𝓝[Ico 0 T] t₀ :=
    mem_nhdsWithin.2 ⟨Iio t₁, isOpen_Iio, ht₀₁, fun y hy => ⟨hy.2.1, hy.1.le⟩⟩
  exact (hcont t₀ ⟨ht₀.1, ht₀₁.le⟩).mono_of_mem_nhdsWithin hnhds

/-- A partial derivative read off from the Jacobian matrix `L`: `(L e_j)ᵢ`. -/
def jacPd (L : E3 →L[ℝ] E3) (j i : Fin 3) : ℝ := EuclideanSpace.proj i (L (basisVec j))

/-- `curl` read off from the Jacobian matrix: `curl v x = curlOfJac (Dv x)`. -/
def curlOfJac (L : E3 →L[ℝ] E3) : E3 :=
  (jacPd L 1 2 - jacPd L 2 1) • basisVec 0
    + (jacPd L 2 0 - jacPd L 0 2) • basisVec 1
    + (jacPd L 0 1 - jacPd L 1 0) • basisVec 2

lemma curl_eq_curlOfJac (v : E3 → E3) (x : E3) : curl v x = curlOfJac (fderiv ℝ v x) := rfl

lemma continuous_jacPd (j i : Fin 3) : Continuous fun L : E3 →L[ℝ] E3 => jacPd L j i :=
  (EuclideanSpace.proj i : E3 →L[ℝ] ℝ).continuous.comp
    (continuous_id.clm_apply continuous_const)

lemma continuous_curlOfJac : Continuous curlOfJac :=
  ((((continuous_jacPd 1 2).sub (continuous_jacPd 2 1)).smul continuous_const).add
    (((continuous_jacPd 2 0).sub (continuous_jacPd 0 2)).smul continuous_const)).add
    (((continuous_jacPd 0 1).sub (continuous_jacPd 1 0)).smul continuous_const)

namespace NSPeriodicData

variable (F : NSPeriodicData)

/-- The vorticity is jointly continuous in `(t, x)` on `[0, T) × ℝ³`. -/
lemma cont_vort :
    ContinuousOn (fun z : ℝ × E3 => vort F.u z.1 z.2) (Ico 0 F.T ×ˢ univ) :=
  continuous_curlOfJac.comp_continuousOn F.cont_grad

/-- If `f` is jointly continuous on `[0, T) × ℝ³`, then `t ↦ ‖f t‖_{L²(𝕋³)}` is continuous. -/
lemma continuousOn_normL2T {f : ℝ → E3 → E3}
    (hf : ContinuousOn (fun z : ℝ × E3 => f z.1 z.2) (Ico 0 F.T ×ˢ univ)) :
    ContinuousOn (fun t => normL2T (f t)) (Ico 0 F.T) := by
  have h := continuousOn_integral_cubeQ (G := fun t x => ‖f t x‖ ^ (2 : ℝ))
    (hf.norm.rpow_const fun _ _ => Or.inr (by norm_num))
  exact h.rpow_const fun _ _ => Or.inr (by norm_num)

/-- **C1.** `t ↦ ‖u(t)‖_{L²(𝕋³)}` is continuous on `[0, T)`. -/
theorem energy_cont : ContinuousOn (energyNormT F.u) (Ico 0 F.T) :=
  F.continuousOn_normL2T F.cont_u

/-- **C2.** `t ↦ ‖ω(t)‖²_{L²(𝕋³)}` is continuous on `[0, T)`. -/
theorem enstrophy_cont : ContinuousOn (enstrophyT F.u) (Ico 0 F.T) :=
  (F.continuousOn_normL2T F.cont_vort).pow 2

end NSPeriodicData

/-! ## D. The energy equality on `𝕋³` -/

/-- `Δv` is continuous if `v` is C². -/
lemma continuous_lap {v : E3 → E3} (hv : ContDiff ℝ 2 v) : Continuous (lap v) := by
  have hv1 : ContDiff ℝ 1 (fderiv ℝ v) := hv.fderiv_right (by norm_num)
  have h : ∀ k, Continuous fun x =>
      fderiv ℝ (fun y => fderiv ℝ v y (basisVec k)) x (basisVec k) := fun k =>
    ((hv1.clm_apply contDiff_const).continuous_fderiv (by norm_num)).clm_apply continuous_const
  exact continuous_finsetSum _ fun k _ => h k

namespace NSPeriodicData

variable (F : NSPeriodicData)

/-- The time derivative `∂ₜu(s, x)`, read off from the joint derivative in `(t, x)`. -/
def dtu (s : ℝ) (x : E3) : E3 :=
  fderiv ℝ (fun z : ℝ × E3 => F.u z.1 z.2) (s, x) (1, 0)

lemma isOpen_Ioo_prod : IsOpen (Ioo (0 : ℝ) F.T ×ˢ (univ : Set E3)) :=
  isOpen_Ioo.prod isOpen_univ

/-- **D1a.** `∂ₜu` is the genuine time derivative of `s ↦ u(s, x)`. -/
lemma hasDerivAt_u_time {s : ℝ} (hs : s ∈ Ioo 0 F.T) (x : E3) :
    HasDerivAt (fun r => F.u r x) (F.dtu s x) s := by
  have hd : DifferentiableAt ℝ (fun z : ℝ × E3 => F.u z.1 z.2) (s, x) :=
    (F.smooth.contDiffAt (F.isOpen_Ioo_prod.mem_nhds ⟨hs, mem_univ x⟩)).differentiableAt
      (by norm_num)
  exact hd.hasFDerivAt.comp_hasDerivAt s ((hasDerivAt_id s).prodMk (hasDerivAt_const s x))

/-- `∂ₜu` is jointly continuous on `(0, T) × ℝ³`. -/
lemma cont_dtu : ContinuousOn (fun z : ℝ × E3 => F.dtu z.1 z.2) (Ioo 0 F.T ×ˢ univ) :=
  (F.smooth.continuousOn_fderiv_of_isOpen F.isOpen_Ioo_prod (by norm_num)).clm_apply
    continuousOn_const

/-- **D1b.** `∂ₜu` agrees with the right-hand side of the momentum equation. -/
lemma dtu_eq {s : ℝ} (hs : s ∈ Ioo 0 F.T) (x : E3) :
    F.dtu s x = F.ν • lap (F.u s) x - fderiv ℝ (F.u s) x (F.u s x) - gradient (F.p s) x :=
  (F.hasDerivAt_u_time hs x).unique (F.momentum s hs x)

/-- **D1.** `d/dt ∫_Q ⟪u, u⟫ = ∫_Q 2⟪u, ∂ₜu⟫` on `(0, T)`: differentiation under the integral
sign, with a dominating bound taken on the compact neighbourhood `[t − δ, t + δ] × Q`. -/
lemma hasDerivAt_integral_inner_self {t : ℝ} (ht : t ∈ Ioo 0 F.T) :
    HasDerivAt (fun s => ∫ x in cubeQ, ⟪F.u s x, F.u s x⟫)
      (∫ x in cubeQ, 2 * ⟪F.u t x, F.dtu t x⟫) t := by
  set δ := min (t / 2) ((F.T - t) / 2) with hδ
  have hδ1 := min_le_left (t / 2) ((F.T - t) / 2)
  have hδ2 := min_le_right (t / 2) ((F.T - t) / 2)
  have hδpos : 0 < δ := lt_min (by linarith [ht.1]) (by linarith [ht.2])
  have hsub : Icc (t - δ) (t + δ) ⊆ Ioo 0 F.T := fun s hs =>
    ⟨by linarith [hs.1, ht.1], by linarith [hs.2, ht.2]⟩
  have hK : IsCompact (Icc (t - δ) (t + δ) ×ˢ cubeQ) := isCompact_Icc.prod isCompact_cubeQ
  have hcF' : ContinuousOn (fun z : ℝ × E3 => 2 * ⟪F.u z.1 z.2, F.dtu z.1 z.2⟫)
      (Ioo 0 F.T ×ˢ univ) :=
    continuousOn_const.mul
      ((F.cont_u.mono (prod_mono Ioo_subset_Ico_self subset_rfl)).inner F.cont_dtu)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn
    (hcF'.mono fun z hz => ⟨hsub hz.1, mem_univ _⟩)
  have hslice : ∀ s ∈ Ioo 0 F.T, Continuous (F.u s) := fun s hs =>
    (F.regular (Ioo_subset_Ico_self hs)).continuous
  have hslice' : ∀ s ∈ Ioo 0 F.T, Continuous (F.dtu s) := fun s hs => by
    have h := F.cont_dtu.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun x (_ : x ∈ (univ : Set E3)) => (⟨hs, mem_univ x⟩ : (s, x) ∈ Ioo 0 F.T ×ˢ univ))
    simp only [Function.comp_def] at h
    exact continuousOn_univ.1 h
  have hball : Ioo (t - δ) (t + δ) ∈ 𝓝 t := Ioo_mem_nhds (by linarith) (by linarith)
  have hIoo : ∀ s ∈ Ioo (t - δ) (t + δ), s ∈ Ioo 0 F.T := fun s hs =>
    hsub (Ioo_subset_Icc_self hs)
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict cubeQ)
    (F := fun s x => ⟪F.u s x, F.u s x⟫) (F' := fun s x => 2 * ⟪F.u s x, F.dtu s x⟫)
    (bound := fun _ => C) hball ?_ ?_ ?_ ?_ ?_ ?_).2
  · filter_upwards [hball] with s hs
    exact ((hslice s (hIoo s hs)).inner (hslice s (hIoo s hs))).aestronglyMeasurable
  · exact integrableOn_cubeQ ((hslice t ht).inner (hslice t ht))
  · exact (continuous_const.mul ((hslice t ht).inner (hslice' t ht))).aestronglyMeasurable
  · exact (ae_restrict_iff' measurableSet_cubeQ).2 (Eventually.of_forall fun x hx s hs =>
      hC (s, x) ⟨Ioo_subset_Icc_self hs, hx⟩)
  · exact integrableOn_cubeQ continuous_const
  · refine Eventually.of_forall fun x s hs => ?_
    have h := F.hasDerivAt_u_time (hIoo s hs) x
    refine (h.inner ℝ h).congr_deriv ?_
    rw [real_inner_comm (F.u s x) (F.dtu s x)]
    ring

/-- **D2.** `∫_Q ⟪u, ∂ₜu⟫ = −ν ∫_Q ∇u : ∇u` on `(0, T)`: substitute the momentum equation,
then use A6a (viscosity), A8 (the convective term vanishes) and A6b (pressure, with
`div u = 0`). -/
lemma integral_inner_dtu {t : ℝ} (ht : t ∈ Ioo 0 F.T) :
    ∫ x in cubeQ, ⟪F.u t x, F.dtu t x⟫
      = -(F.ν * ∫ x in cubeQ, gradDot (F.u t) (F.u t) x) := by
  have ht' := Ioo_subset_Ico_self ht
  have hu3 := F.regular ht'
  have hu1 : ContDiff ℝ 1 (F.u t) := hu3.of_le (by norm_num)
  have hu2 : ContDiff ℝ 2 (F.u t) := hu3.of_le (by norm_num)
  have hp1 : ContDiff ℝ 1 (F.p t) := (F.p_regular t ht).of_le (by norm_num)
  have hup := F.u_periodic t ht'
  have hpp := F.p_periodic t ht
  have hgr : ∀ x, ⟪F.u t x, gradient (F.p t) x⟫ = fderiv ℝ (F.p t) x (F.u t x) := fun x => by
    rw [real_inner_comm, inner_gradient_left]
  have c1 : Continuous fun x => ⟪F.u t x, lap (F.u t) x⟫ :=
    hu1.continuous.inner (continuous_lap hu2)
  have c2 : Continuous fun x => ⟪F.u t x, fderiv ℝ (F.u t) x (F.u t x)⟫ :=
    hu1.continuous.inner ((hu1.continuous_fderiv (by norm_num)).clm_apply hu1.continuous)
  have c3 : Continuous fun x => ⟪F.u t x, gradient (F.p t) x⟫ := by
    simp_rw [hgr]
    exact (hp1.continuous_fderiv (by norm_num)).clm_apply hu1.continuous
  have hpt : ∀ x, ⟪F.u t x, F.dtu t x⟫ = F.ν * ⟪F.u t x, lap (F.u t) x⟫
      - ⟪F.u t x, fderiv ℝ (F.u t) x (F.u t x)⟫ - ⟪F.u t x, gradient (F.p t) x⟫ := fun x => by
    rw [F.dtu_eq ht x, inner_sub_right, inner_sub_right, inner_smul_right]
  simp_rw [hpt]
  rw [integral_sub (f := fun x => F.ν * ⟪F.u t x, lap (F.u t) x⟫
        - ⟪F.u t x, fderiv ℝ (F.u t) x (F.u t x)⟫)
      (((integrableOn_cubeQ c1).const_mul _).sub (integrableOn_cubeQ c2))
      (integrableOn_cubeQ c3),
    integral_sub (f := fun x => F.ν * ⟪F.u t x, lap (F.u t) x⟫)
      ((integrableOn_cubeQ c1).const_mul _) (integrableOn_cubeQ c2),
    integral_const_mul,
    integral_cubeQ_inner_lap hu1 hu2 hup hup,
    integral_cubeQ_inner_convective_eq_zero hu1 hu1 hup hup (F.div_free t ht'),
    integral_cubeQ_inner_gradient hu1 hp1 hup hpp]
  simp [F.div_free t ht']

/-- **D3.** `∫_Q ∇u : ∇u = ‖ω‖²_{L²(𝕋³)}` (A7 together with `div u = 0`). -/
lemma integral_gradDot_eq_enstrophy {t : ℝ} (ht : t ∈ Ico 0 F.T) :
    ∫ x in cubeQ, gradDot (F.u t) (F.u t) x = enstrophyT F.u t := by
  rw [integral_cubeQ_gradDot_self ((F.regular ht).of_le (by norm_num)) (F.u_periodic t ht),
    enstrophyT_eq]
  simp [F.div_free t ht, vort]

/-- `d/dt ‖u‖²_{L²(𝕋³)} = −2ν ‖ω‖²_{L²(𝕋³)}` on `(0, T)`. -/
theorem hasDerivAt_energy_sq {t : ℝ} (ht : t ∈ Ioo 0 F.T) :
    HasDerivAt (fun s => energyNormT F.u s ^ 2) (-2 * F.ν * enstrophyT F.u t) t := by
  have heq : (fun s => energyNormT F.u s ^ 2)
      = fun s => ∫ x in cubeQ, ⟪F.u s x, F.u s x⟫ := by
    funext s
    rw [energyNormT_sq]
    simp_rw [real_inner_self_eq_norm_sq]
  rw [heq]
  refine (F.hasDerivAt_integral_inner_self ht).congr_deriv ?_
  rw [integral_const_mul, F.integral_inner_dtu ht,
    F.integral_gradDot_eq_enstrophy (Ioo_subset_Ico_self ht)]
  ring

/-- **D4 (the energy equality).** `‖u(t)‖² + 2ν ∫₀ᵗ ‖ω‖² = ‖u(0)‖²` on `[0, T)`. -/
theorem energy_equality {t : ℝ} (ht : t ∈ Ico 0 F.T) :
    energyNormT F.u t ^ 2 + 2 * F.ν * (∫ s in (0 : ℝ)..t, enstrophyT F.u s)
      = energyNormT F.u 0 ^ 2 := by
  have hsub : Icc 0 t ⊆ Ico 0 F.T := fun s hs => ⟨hs.1, hs.2.trans_lt ht.2⟩
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1
    ((F.energy_cont.pow 2).mono hsub)
    (fun s hs => F.hasDerivAt_energy_sq ⟨hs.1, hs.2.trans ht.2⟩)
    (ContinuousOn.intervalIntegrable (by
      rw [uIcc_of_le ht.1]
      exact continuousOn_const.mul (F.enstrophy_cont.mono hsub)))
  rw [intervalIntegral.integral_const_mul] at hFTC
  simp only [Pi.pow_apply] at hFTC
  linarith

/-- **The Leray–Hopf energy inequality** (the same form as the original field `energy_ineq`). -/
theorem energy_ineq {t : ℝ} (ht : t ∈ Ico 0 F.T) :
    energyNormT F.u t ^ 2 + 2 * F.ν * (∫ s in (0 : ℝ)..t, enstrophyT F.u s)
      ≤ energyNormT F.u 0 ^ 2 :=
  (F.energy_equality ht).le

end NSPeriodicData

/-! ## E0. Coordinates: Levi-Civita, second derivatives, Schwarz -/

/-- The Levi-Civita symbol `ε_{ijk}`. -/
def eps : Fin 3 → Fin 3 → Fin 3 → ℝ :=
  ![![![0, 0, 0], ![0, 0, 1], ![0, -1, 0]],
    ![![0, 0, -1], ![0, 0, 0], ![1, 0, 0]],
    ![![0, 1, 0], ![-1, 0, 0], ![0, 0, 0]]]

/-- `curl` theo Levi-Civita: `(curl v)ᵢ = Σⱼ Σₖ ε_{ijk} ∂ⱼvₖ`. -/
lemma curl_apply (v : E3 → E3) (x : E3) (i : Fin 3) :
    curl v x i = ∑ j, ∑ k, eps i j k * pd v j k x := by
  fin_cases i <;> simp [NavierStokes.curl, basisVec, eps, Fin.sum_univ_three] <;> ring

/-- The second partial derivative `∂ₖ∂ⱼvᵢ`. -/
def pd2 (v : E3 → E3) (k j i : Fin 3) (x : E3) : ℝ := fderiv ℝ (pd v j i) x (basisVec k)

/-- `pd v j i` is C^m if `v` is C^n with `m + 1 ≤ n`. -/
lemma contDiff_pd {v : E3 → E3} {m n : WithTop ℕ∞} (hv : ContDiff ℝ n v) (hmn : m + 1 ≤ n)
    (j i : Fin 3) : ContDiff ℝ m (pd v j i) :=
  (EuclideanSpace.proj i : E3 →L[ℝ] ℝ).contDiff.comp
    ((hv.fderiv_right hmn).clm_apply contDiff_const)

/-- `curl v` is C^m if `v` is C^n with `m + 1 ≤ n`. -/
lemma contDiff_curl {v : E3 → E3} {m n : WithTop ℕ∞} (hv : ContDiff ℝ n v) (hmn : m + 1 ≤ n) :
    ContDiff ℝ m (curl v) :=
  ((((contDiff_pd hv hmn 1 2).sub (contDiff_pd hv hmn 2 1)).smul contDiff_const).add
    (((contDiff_pd hv hmn 2 0).sub (contDiff_pd hv hmn 0 2)).smul contDiff_const)).add
    (((contDiff_pd hv hmn 0 1).sub (contDiff_pd hv hmn 1 0)).smul contDiff_const)

/-- **Schwarz for vector fields.** `∂ₖ∂ⱼvᵢ = ∂ⱼ∂ₖvᵢ` for `v` C². -/
lemma pd2_comm {v : E3 → E3} (hv : ContDiff ℝ 2 v) (k j i : Fin 3) (x : E3) :
    pd2 v k j i x = pd2 v j k i x := by
  have hvd : Differentiable ℝ v := hv.differentiable (by norm_num)
  have hc : ContDiff ℝ 2 (fun y => v y i) := (EuclideanSpace.proj i : E3 →L[ℝ] ℝ).contDiff.comp hv
  have hfun : ∀ a, pd v a i = fun y => fderiv ℝ (fun z => v z i) y (basisVec a) := fun a =>
    funext fun y => pd_eq_fderiv_component (hvd y) a i
  simp only [pd2, hfun]
  exact fderiv_dir_comm hc x (basisVec j) (basisVec k)

/-- The directional derivative of a linear combination over two indices. -/
lemma fderiv_sum_sum_const_mul_apply {c : Fin 3 → Fin 3 → ℝ} {g : Fin 3 → Fin 3 → E3 → ℝ}
    {x : E3} (hg : ∀ j k, DifferentiableAt ℝ (g j k) x) (w : E3) :
    fderiv ℝ (fun y => ∑ j, ∑ k, c j k * g j k y) x w
      = ∑ j, ∑ k, c j k * fderiv ℝ (g j k) x w := by
  have h : HasFDerivAt (fun y => ∑ j, ∑ k, c j k * g j k y)
      (∑ j, ∑ k, c j k • fderiv ℝ (g j k) x) x :=
    HasFDerivAt.fun_sum fun j _ => HasFDerivAt.fun_sum fun k _ =>
      (hg j k).hasFDerivAt.const_mul (c j k)
  rw [h.fderiv]
  simp [sum_apply, smul_apply]

/-- **The derivative of curl.** `∂ₘ(curl v)ᵢ = Σⱼ Σₖ ε_{ijk} ∂ₘ∂ⱼvₖ` for `v` C². -/
lemma pd_curl {v : E3 → E3} (hv : ContDiff ℝ 2 v) (m i : Fin 3) (x : E3) :
    pd (curl v) m i x = ∑ j, ∑ k, eps i j k * pd2 v m j k x := by
  have hcd : Differentiable ℝ (curl v) :=
    (contDiff_curl (m := 1) hv (by norm_num)).differentiable (by norm_num)
  have hpdd : ∀ j k, Differentiable ℝ (pd v j k) := fun j k =>
    (contDiff_pd (m := 1) hv (by norm_num) j k).differentiable (by norm_num)
  rw [pd_eq_fderiv_component (hcd x)]
  have hfun : (fun y => curl v y i) = fun y => ∑ j, ∑ k, eps i j k * pd v j k y :=
    funext fun y => curl_apply v y i
  rw [hfun, fderiv_sum_sum_const_mul_apply fun j k => hpdd j k x]
  rfl

/-- **`div curl = 0`** for `v` C² (Schwarz). -/
lemma divergence_curl {v : E3 → E3} (hv : ContDiff ℝ 2 v) (x : E3) :
    divergence (curl v) x = 0 := by
  simp only [NavierStokes.divergence, pd_curl hv, Fin.sum_univ_three]
  simp only [eps, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, zero_mul, one_mul, neg_mul, zero_add, add_zero]
  rw [pd2_comm hv 1 0, pd2_comm hv 2 0, pd2_comm hv 2 1]
  ring

/-! ## E3. Symmetry of curl under integration by parts -/

/-- The integral over `Q` of a triple-index sum of continuous functions. -/
lemma integral_cubeQ_sum3 {G : Fin 3 → Fin 3 → Fin 3 → E3 → ℝ}
    (hG : ∀ j k i, Continuous (G j k i)) :
    ∫ x in cubeQ, ∑ j, ∑ k, ∑ i, G j k i x = ∑ j, ∑ k, ∑ i, ∫ x in cubeQ, G j k i x := by
  rw [integral_cubeQ_sum_sum (F := fun j k x => ∑ i, G j k i x)
    (fun j k => continuous_finsetSum _ fun i _ => hG j k i)]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ =>
    integral_finsetSum _ fun i _ => integrableOn_cubeQ (hG j k i)

/-- **E3.** For `a, b` C¹ and periodic: `∫_Q ⟪curl a, b⟫ = ∫_Q ⟪a, curl b⟫`.
Write both sides with Levi-Civita, then apply A5 to each term `∂ⱼaₖ · bᵢ`, using
`ε_{kji} = −ε_{ijk}`. -/
theorem integral_cubeQ_inner_curl_comm {a b : E3 → E3} (ha : ContDiff ℝ 1 a)
    (hb : ContDiff ℝ 1 b) (hap : IsPeriodic3 a) (hbp : IsPeriodic3 b) :
    ∫ x in cubeQ, ⟪curl a x, b x⟫ = ∫ x in cubeQ, ⟪a x, curl b x⟫ := by
  have had : Differentiable ℝ a := ha.differentiable (by norm_num)
  have hbd : Differentiable ℝ b := hb.differentiable (by norm_num)
  have hac : ∀ k, ContDiff ℝ 1 (fun y => a y k) := fun k =>
    (EuclideanSpace.proj k : E3 →L[ℝ] ℝ).contDiff.comp ha
  have hbc : ∀ i, ContDiff ℝ 1 (fun y => b y i) := fun i =>
    (EuclideanSpace.proj i : E3 →L[ℝ] ℝ).contDiff.comp hb
  have hdc : ∀ (g : E3 → ℝ) (m : Fin 3), ContDiff ℝ 1 g →
      Continuous fun x => fderiv ℝ g x (basisVec m) := fun g m hg =>
    (hg.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hL : ∀ x, ⟪curl a x, b x⟫ = ∑ j, ∑ k, ∑ i,
      eps i j k * (fderiv ℝ (fun y => a y k) x (basisVec j) * b x i) := by
    intro x
    simp only [inner_eq_sum, curl_apply, pd_eq_fderiv_component (had x), Fin.sum_univ_three]
    ring
  have hR : ∀ x, ⟪a x, curl b x⟫ = ∑ j, ∑ k, ∑ i,
      -eps i j k * (a x k * fderiv ℝ (fun y => b y i) x (basisVec j)) := by
    intro x
    simp only [inner_eq_sum, curl_apply, pd_eq_fderiv_component (hbd x), Fin.sum_univ_three]
    simp only [eps, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    ring
  simp_rw [hL, hR]
  rw [integral_cubeQ_sum3
      (G := fun j k i x => eps i j k * (fderiv ℝ (fun y => a y k) x (basisVec j) * b x i))
      (fun j k i => continuous_const.mul ((hdc _ j (hac k)).mul (hbc i).continuous)),
    integral_cubeQ_sum3
      (G := fun j k i x => -eps i j k * (a x k * fderiv ℝ (fun y => b y i) x (basisVec j)))
      (fun j k i => continuous_const.mul ((hac k).continuous.mul (hdc _ j (hbc i))))]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ =>
    Finset.sum_congr rfl fun i _ => ?_
  have h5 := integral_cubeQ_fderiv_mul_eq_neg (hac k) (hbc i) j
    ((hap j).comp fun z => z k) ((hbp j).comp fun z => z i)
  simp only at h5
  rw [integral_const_mul, integral_const_mul, h5]
  ring

/-! ## E4. Pointwise identities: the viscous term and the convective term -/

/-- The convective term `(v·∇)v = Dv · v`. -/
def conv (v : E3 → E3) (x : E3) : E3 := fderiv ℝ v x (v x)

/-- The components of `Dv(x) w`: `(Dv w)ₖ = Σₗ wₗ ∂ₗvₖ`. -/
lemma fderiv_apply_coord {v : E3 → E3} (x w : E3) (k : Fin 3) :
    fderiv ℝ v x w k = ∑ l, w l * pd v l k x := by
  conv_lhs => rw [eq_sum_basisVec w]
  simp [NavierStokes.pd]

/-- `(Δv)ᵢ = Σⱼ ∂ⱼ∂ⱼvᵢ`. -/
lemma lap_apply' {v : E3 → E3} (hv : ContDiff ℝ 2 v) (x : E3) (i : Fin 3) :
    lap v x i = ∑ j, pd2 v j j i x :=
  lap_apply hv x i

/-- The derivative of the convective term: `∂ⱼ(conv v)ₖ = Σₗ (∂ⱼvₗ ∂ₗvₖ + vₗ ∂ⱼ∂ₗvₖ)`. -/
lemma pd_conv {v : E3 → E3} (hv : ContDiff ℝ 2 v) (j k : Fin 3) (x : E3) :
    pd (conv v) j k x = ∑ l, (pd v j l x * pd v l k x + v x l * pd2 v j l k x) := by
  have hvd : Differentiable ℝ v := hv.differentiable (by norm_num)
  have hconv : ContDiff ℝ 1 (conv v) :=
    (hv.fderiv_right (m := 1) (by norm_num)).clm_apply (hv.of_le (by norm_num))
  have hcl : ∀ l, Differentiable ℝ (fun y => v y l) := fun l =>
    ((EuclideanSpace.proj l : E3 →L[ℝ] ℝ).contDiff.comp hv).differentiable (by norm_num)
  have hpdd : ∀ l, Differentiable ℝ (pd v l k) := fun l =>
    (contDiff_pd (m := 1) hv (by norm_num) l k).differentiable (by norm_num)
  rw [pd_eq_fderiv_component ((hconv.differentiable (by norm_num)) x)]
  have hfun : (fun y => conv v y k) = fun y => ∑ l, v y l * pd v l k y :=
    funext fun y => fderiv_apply_coord y (v y) k
  have h : HasFDerivAt (fun y => ∑ l, v y l * pd v l k y)
      (∑ l, (v x l • fderiv ℝ (pd v l k) x + pd v l k x • fderiv ℝ (fun y => v y l) x)) x :=
    HasFDerivAt.fun_sum fun l _ => ((hcl l x).hasFDerivAt.mul (hpdd l x).hasFDerivAt)
  rw [hfun, h.fderiv]
  simp only [sum_apply, add_apply, smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← pd_eq_fderiv_component (hvd x)]
  simp only [pd2]
  ring

/-- `∂ᵢ(div v) = Σₘ ∂ᵢ∂ₘvₘ`; it is 0 if `div v ≡ 0`. -/
lemma sum_pd2_div_eq_zero {v : E3 → E3} (hv : ContDiff ℝ 2 v)
    (hdiv : ∀ x, divergence v x = 0) (i : Fin 3) (x : E3) :
    ∑ m, pd2 v i m m x = 0 := by
  have hpdd : ∀ m, Differentiable ℝ (pd v m m) := fun m =>
    (contDiff_pd (m := 1) hv (by norm_num) m m).differentiable (by norm_num)
  have h : HasFDerivAt (fun y => ∑ m, pd v m m y) (∑ m, fderiv ℝ (pd v m m) x) x :=
    HasFDerivAt.fun_sum fun m _ => (hpdd m x).hasFDerivAt
  have hz : (fun y => ∑ m, pd v m m y) = fun _ => (0 : ℝ) := funext hdiv
  have h0 := h.fderiv
  rw [hz, fderiv_const_apply] at h0
  have h1 := congrArg (fun L : E3 →L[ℝ] ℝ => L (basisVec i)) h0
  simp only [zero_apply, sum_apply] at h1
  exact h1.symm

/-- **E4a (viscosity).** For `div v ≡ 0` and `v` C³: `(Δv)ᵢ = −(curl curl v)ᵢ`. -/
lemma lap_apply_eq_neg_curl_curl {v : E3 → E3} (hv : ContDiff ℝ 3 v)
    (hdiv : ∀ x, divergence v x = 0) (x : E3) (i : Fin 3) :
    lap v x i = -(curl (curl v) x i) := by
  have hv2 : ContDiff ℝ 2 v := hv.of_le (by norm_num)
  have hdi := sum_pd2_div_eq_zero hv2 hdiv i x
  rw [lap_apply' hv2, curl_apply]
  simp only [pd_curl hv2]
  fin_cases i <;>
  · simp only [Fin.sum_univ_three, eps, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.zero_eta, Fin.mk_one,
      Fin.reduceFinMk] at hdi ⊢
    simp only [pd2_comm hv2 1 0, pd2_comm hv2 2 0, pd2_comm hv2 2 1] at hdi ⊢
    linarith

/-- **E4b (convection).** For `v` C² and `ω = curl v`:
`⟪ω, curl (v·∇)v⟫ = ⟪ω, (v·∇)ω⟫ − ⟪ω, (ω·∇)v⟫ + |ω|² div v`. -/
lemma inner_curl_conv {v : E3 → E3} (hv : ContDiff ℝ 2 v) (x : E3) :
    ⟪curl v x, curl (conv v) x⟫
      = ⟪curl v x, fderiv ℝ (curl v) x (v x)⟫ - ⟪curl v x, fderiv ℝ v x (curl v x)⟫
        + (∑ i, curl v x i ^ 2) * divergence v x := by
  simp only [inner_eq_sum, fderiv_apply_coord, curl_apply (conv v), pd_conv hv, pd_curl hv]
  simp only [curl_apply v, NavierStokes.divergence, Fin.sum_univ_three, eps,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  simp only [pd2_comm hv 1 0, pd2_comm hv 2 0, pd2_comm hv 2 1]
  ring

/-! ## E1–E2. The time derivative of the vorticity -/

/-- A slice of a jointly continuous function is continuous. -/
lemma continuous_slice {S : Set ℝ} {W : ℝ → E3 → E3}
    (hW : ContinuousOn (fun z : ℝ × E3 => W z.1 z.2) (S ×ˢ univ)) {s : ℝ} (hs : s ∈ S) :
    Continuous (W s) := by
  have h := hW.comp (continuous_const.prodMk continuous_id).continuousOn
    (fun x (_ : x ∈ (univ : Set E3)) => (⟨hs, mem_univ x⟩ : (s, x) ∈ S ×ˢ univ))
  simp only [Function.comp_def] at h
  exact continuousOn_univ.1 h

/-- **Differentiation under the integral sign (general form).** If `W, W'` are jointly
continuous on `(0, T) × ℝ³` and `∂ₜW = W'`, then `d/dt ∫_Q ⟪W, W⟫ = ∫_Q 2⟪W, W'⟫`. -/
lemma hasDerivAt_integral_inner_self_of {T t : ℝ} (ht : t ∈ Ioo 0 T) {W W' : ℝ → E3 → E3}
    (hW : ContinuousOn (fun z : ℝ × E3 => W z.1 z.2) (Ioo 0 T ×ˢ univ))
    (hW' : ContinuousOn (fun z : ℝ × E3 => W' z.1 z.2) (Ioo 0 T ×ˢ univ))
    (hd : ∀ s ∈ Ioo 0 T, ∀ x, HasDerivAt (fun r => W r x) (W' s x) s) :
    HasDerivAt (fun s => ∫ x in cubeQ, ⟪W s x, W s x⟫)
      (∫ x in cubeQ, 2 * ⟪W t x, W' t x⟫) t := by
  set δ := min (t / 2) ((T - t) / 2) with hδ
  have hδ1 := min_le_left (t / 2) ((T - t) / 2)
  have hδ2 := min_le_right (t / 2) ((T - t) / 2)
  have hδpos : 0 < δ := lt_min (by linarith [ht.1]) (by linarith [ht.2])
  have hsub : Icc (t - δ) (t + δ) ⊆ Ioo 0 T := fun s hs =>
    ⟨by linarith [hs.1, ht.1], by linarith [hs.2, ht.2]⟩
  have hK : IsCompact (Icc (t - δ) (t + δ) ×ˢ cubeQ) := isCompact_Icc.prod isCompact_cubeQ
  have hcF' : ContinuousOn (fun z : ℝ × E3 => 2 * ⟪W z.1 z.2, W' z.1 z.2⟫)
      (Ioo 0 T ×ˢ univ) := continuousOn_const.mul (hW.inner hW')
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn
    (hcF'.mono fun z hz => ⟨hsub hz.1, mem_univ _⟩)
  have hball : Ioo (t - δ) (t + δ) ∈ 𝓝 t := Ioo_mem_nhds (by linarith) (by linarith)
  have hIoo : ∀ s ∈ Ioo (t - δ) (t + δ), s ∈ Ioo 0 T := fun s hs =>
    hsub (Ioo_subset_Icc_self hs)
  have hsl : ∀ s ∈ Ioo 0 T, Continuous (W s) := fun s hs => continuous_slice hW hs
  have hsl' : ∀ s ∈ Ioo 0 T, Continuous (W' s) := fun s hs => continuous_slice hW' hs
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict cubeQ)
    (F := fun s x => ⟪W s x, W s x⟫) (F' := fun s x => 2 * ⟪W s x, W' s x⟫)
    (bound := fun _ => C) hball ?_ ?_ ?_ ?_ ?_ ?_).2
  · filter_upwards [hball] with s hs
    exact ((hsl s (hIoo s hs)).inner (hsl s (hIoo s hs))).aestronglyMeasurable
  · exact integrableOn_cubeQ ((hsl t ht).inner (hsl t ht))
  · exact (continuous_const.mul ((hsl t ht).inner (hsl' t ht))).aestronglyMeasurable
  · exact (ae_restrict_iff' measurableSet_cubeQ).2 (Eventually.of_forall fun x hx s hs =>
      hC (s, x) ⟨Ioo_subset_Icc_self hs, hx⟩)
  · exact integrableOn_cubeQ continuous_const
  · refine Eventually.of_forall fun x s hs => ?_
    have h := hd s (hIoo s hs) x
    refine (h.inner ℝ h).congr_deriv ?_
    rw [real_inner_comm (W s x) (W' s x)]
    ring

namespace NSPeriodicData

variable (F : NSPeriodicData)

/-- The joint function `U(t, x) = u(t, x)` on `ℝ × E3`. -/
abbrev U : ℝ × E3 → E3 := fun z => F.u z.1 z.2

lemma U_contDiffAt {s : ℝ} (hs : s ∈ Ioo 0 F.T) (x : E3) : ContDiffAt ℝ 3 F.U (s, x) :=
  F.smooth.contDiffAt (F.isOpen_Ioo_prod.mem_nhds ⟨hs, mem_univ x⟩)

lemma fderivU_contDiffOn : ContDiffOn ℝ 2 (fderiv ℝ F.U) (Ioo 0 F.T ×ˢ univ) :=
  F.smooth.fderiv_of_isOpen F.isOpen_Ioo_prod (by norm_num)

lemma fderivU_differentiableAt {s : ℝ} (hs : s ∈ Ioo 0 F.T) (x : E3) :
    DifferentiableAt ℝ (fderiv ℝ F.U) (s, x) :=
  (F.fderivU_contDiffOn.differentiableOn (by norm_num)).differentiableAt
    (F.isOpen_Ioo_prod.mem_nhds ⟨hs, mem_univ x⟩)

/-- The spatial derivative read off from `DU`: `Du(r)(y) w = DU(r, y)(0, w)`. -/
lemma fderiv_u_eq {r : ℝ} (hr : r ∈ Ioo 0 F.T) (y w : E3) :
    fderiv ℝ (F.u r) y w = fderiv ℝ F.U (r, y) (0, w) := by
  have hd : DifferentiableAt ℝ F.U (r, y) :=
    (F.U_contDiffAt hr y).differentiableAt (by norm_num)
  have hinc : HasFDerivAt (fun z : E3 => (r, z))
      ((0 : E3 →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ E3)) y :=
    (hasFDerivAt_const r y).prodMk (hasFDerivAt_id y)
  have h := hd.hasFDerivAt.comp y hinc
  rw [show F.u r = F.U ∘ fun z : E3 => (r, z) from rfl, h.fderiv]
  simp

/-- `D(∂ₜu)(s)(x) w = D²U(s, x)(0, w)(1, 0)`. -/
lemma fderiv_dtu_eq {s : ℝ} (hs : s ∈ Ioo 0 F.T) (x w : E3) :
    fderiv ℝ (F.dtu s) x w = fderiv ℝ (fderiv ℝ F.U) (s, x) (0, w) (1, 0) := by
  have hinc : HasFDerivAt (fun z : E3 => (s, z))
      ((0 : E3 →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ E3)) x :=
    (hasFDerivAt_const s x).prodMk (hasFDerivAt_id x)
  have h1 := (F.fderivU_differentiableAt hs x).hasFDerivAt.comp x hinc
  have h2 := (ContinuousLinearMap.apply ℝ E3 ((1 : ℝ), (0 : E3))).hasFDerivAt.comp x h1
  rw [show F.dtu s = (ContinuousLinearMap.apply ℝ E3 ((1 : ℝ), (0 : E3)))
      ∘ (fderiv ℝ F.U ∘ fun z : E3 => (s, z)) from rfl, h2.fderiv]
  simp

/-- The time derivative of `∂ⱼuᵢ(·, x)`, read off from `D²U`. -/
lemma hasDerivAt_pd_time_aux {s : ℝ} (hs : s ∈ Ioo 0 F.T) (x : E3) (j i : Fin 3) :
    HasDerivAt (fun r => pd (F.u r) j i x)
      (EuclideanSpace.proj i (fderiv ℝ (fderiv ℝ F.U) (s, x) (1, 0) (0, basisVec j))) s := by
  have hcurve : HasDerivAt (fun r => fderiv ℝ F.U (r, x))
      (fderiv ℝ (fderiv ℝ F.U) (s, x) (1, 0)) s :=
    (F.fderivU_differentiableAt hs x).hasFDerivAt.comp_hasDerivAt s
      ((hasDerivAt_id s).prodMk (hasDerivAt_const s x))
  have happ := hcurve.clm_apply (hasDerivAt_const s ((0 : ℝ), basisVec j))
  have hproj := (EuclideanSpace.proj i : E3 →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt s happ
  have hev : (fun r => pd (F.u r) j i x) =ᶠ[𝓝 s]
      fun r => EuclideanSpace.proj i (fderiv ℝ F.U (r, x) (0, basisVec j)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hs] with r hr
    simp only [NavierStokes.pd, F.fderiv_u_eq hr]
  refine (hproj.congr_of_eventuallyEq hev).congr_deriv ?_
  simp

/-- **E1a (Schwarz theo `(t, x)`).** `∂ₜ(∂ⱼuᵢ) = ∂ⱼ(∂ₜuᵢ)`. -/
lemma hasDerivAt_pd_time {s : ℝ} (hs : s ∈ Ioo 0 F.T) (x : E3) (j i : Fin 3) :
    HasDerivAt (fun r => pd (F.u r) j i x) (pd (F.dtu s) j i x) s := by
  refine (F.hasDerivAt_pd_time_aux hs x j i).congr_deriv ?_
  show _ = EuclideanSpace.proj i (fderiv ℝ (F.dtu s) x (basisVec j))
  rw [F.fderiv_dtu_eq hs, (F.U_contDiffAt hs x).isSymmSndFDerivAt
    (by simp only [minSmoothness_of_isRCLikeNormedField]; norm_num)
    ((1 : ℝ), (0 : E3)) ((0 : ℝ), basisVec j)]

/-- **E1.** `∂ₜω = curl (∂ₜu)` on `(0, T)`. -/
lemma hasDerivAt_vort_time {s : ℝ} (hs : s ∈ Ioo 0 F.T) (x : E3) :
    HasDerivAt (fun r => vort F.u r x) (curl (F.dtu s) x) s := by
  have h := fun j i => F.hasDerivAt_pd_time hs x j i
  exact ((((h 1 2).sub (h 2 1)).smul_const (basisVec 0)).add
    (((h 2 0).sub (h 0 2)).smul_const (basisVec 1))).add
    (((h 0 1).sub (h 1 0)).smul_const (basisVec 2))

/-- `∂ₜu(s)` is C² in `x`. -/
lemma dtu_contDiff {s : ℝ} (hs : s ∈ Ioo 0 F.T) : ContDiff ℝ 2 (F.dtu s) := by
  have h := (F.fderivU_contDiffOn.comp_contDiff (contDiff_prodMk_right s)
    fun x => ⟨hs, mem_univ x⟩).clm_apply (contDiff_const (c := ((1 : ℝ), (0 : E3))))
  rw [show F.dtu s = fun x => fderiv ℝ F.U (s, x) (1, 0) from rfl]
  simpa [Function.comp_def] using h

/-- `∂ₜu(s)` is periodic. -/
lemma dtu_periodic {s : ℝ} (hs : s ∈ Ioo 0 F.T) : IsPeriodic3 (F.dtu s) := fun j x => by
  have h1 := F.hasDerivAt_u_time hs (x + basisVec j)
  have hev : (fun r => F.u r (x + basisVec j)) =ᶠ[𝓝 s] fun r => F.u r x := by
    filter_upwards [isOpen_Ioo.mem_nhds hs] with r hr
    exact F.u_periodic r (Ioo_subset_Ico_self hr) j x
  exact (h1.congr_of_eventuallyEq hev.symm).unique (F.hasDerivAt_u_time hs x)

/-- `curl (∂ₜu)` is jointly continuous on `(0, T) × ℝ³`. -/
lemma cont_curl_dtu :
    ContinuousOn (fun z : ℝ × E3 => curl (F.dtu z.1) z.2) (Ioo 0 F.T ×ˢ univ) := by
  have hD2 : ContinuousOn (fderiv ℝ (fderiv ℝ F.U)) (Ioo 0 F.T ×ˢ univ) :=
    F.fderivU_contDiffOn.continuousOn_fderiv_of_isOpen F.isOpen_Ioo_prod (by norm_num)
  have hpd : ∀ j i, ContinuousOn (fun z : ℝ × E3 => pd (F.dtu z.1) j i z.2)
      (Ioo 0 F.T ×ˢ univ) := by
    intro j i
    have h : ContinuousOn (fun z : ℝ × E3 => EuclideanSpace.proj i
        (fderiv ℝ (fderiv ℝ F.U) z ((0 : ℝ), basisVec j) ((1 : ℝ), (0 : E3))))
        (Ioo 0 F.T ×ˢ univ) :=
      (EuclideanSpace.proj i : E3 →L[ℝ] ℝ).continuous.comp_continuousOn
        ((hD2.clm_apply continuousOn_const).clm_apply continuousOn_const)
    refine h.congr fun z hz => ?_
    simp only [NavierStokes.pd, F.fderiv_dtu_eq hz.1, Prod.mk.eta]
  exact ((((hpd 1 2).sub (hpd 2 1)).smul continuousOn_const).add
    (((hpd 2 0).sub (hpd 0 2)).smul continuousOn_const)).add
    (((hpd 0 1).sub (hpd 1 0)).smul continuousOn_const)

/-- **E2.** `d/dt ∫_Q ⟪ω, ω⟫ = ∫_Q 2⟪ω, curl ∂ₜu⟫` on `(0, T)`. -/
lemma hasDerivAt_integral_vort {t : ℝ} (ht : t ∈ Ioo 0 F.T) :
    HasDerivAt (fun s => ∫ x in cubeQ, ⟪vort F.u s x, vort F.u s x⟫)
      (∫ x in cubeQ, 2 * ⟪vort F.u t x, curl (F.dtu t) x⟫) t :=
  hasDerivAt_integral_inner_self_of (W' := fun s x => curl (F.dtu s) x) ht
    (F.cont_vort.mono (prod_mono Ioo_subset_Ico_self subset_rfl)) F.cont_curl_dtu
    fun _ hs x => F.hasDerivAt_vort_time hs x

/-- **E5 (the enstrophy balance on `𝕋³`, Frobenius norm).** On `(0, T)`:
`d/dt ‖ω‖² = −2ν ∫_Q ∇ω : ∇ω + 2 ∫_Q ω · (∇u) ω`.
Proof: E2, then E3 (`∫⟪ω, curl ∂ₜu⟫ = ∫⟪curl ω, ∂ₜu⟫`), and substitute the momentum equation:
the viscous term via E4a + A7 (`div ω = 0`), the convective term via E3 + E4b + A8, and the
pressure term via A6b (`div curl ω = 0`). -/
theorem enstrophy_balance {t : ℝ} (ht : t ∈ Ioo 0 F.T) :
    HasDerivAt (enstrophyT F.u)
      (-2 * F.ν * palinstrophyT F.u t + 2 * stretchingT F.u t) t := by
  have ht' := Ioo_subset_Ico_self ht
  set u := F.u t with hu_def
  have hu3 : ContDiff ℝ 3 u := F.regular ht'
  have hu2 : ContDiff ℝ 2 u := hu3.of_le (by norm_num)
  have hu1 : ContDiff ℝ 1 u := hu3.of_le (by norm_num)
  have hup : IsPeriodic3 u := F.u_periodic t ht'
  have hdiv : ∀ x, divergence u x = 0 := F.div_free t ht'
  set ω := curl u with hω_def
  have hω2 : ContDiff ℝ 2 ω := contDiff_curl hu3 (by norm_num)
  have hω1 : ContDiff ℝ 1 ω := hω2.of_le (by norm_num)
  have hωp : IsPeriodic3 ω := hup.curl
  have hcω1 : ContDiff ℝ 1 (curl ω) := contDiff_curl hω2 (by norm_num)
  have hcωp : IsPeriodic3 (curl ω) := hωp.curl
  have hdivω : ∀ x, divergence ω x = 0 := fun x => divergence_curl hu2 x
  have hdivcω : ∀ x, divergence (curl ω) x = 0 := fun x => divergence_curl hω2 x
  have hdt1 : ContDiff ℝ 1 (F.dtu t) := (F.dtu_contDiff ht).of_le (by norm_num)
  have hdtp := F.dtu_periodic ht
  have hp1 : ContDiff ℝ 1 (F.p t) := (F.p_regular t ht).of_le (by norm_num)
  have hpp := F.p_periodic t ht
  have hconv1 : ContDiff ℝ 1 (conv u) :=
    (hu2.fderiv_right (m := 1) (by norm_num)).clm_apply hu1
  have hconvp : IsPeriodic3 (conv u) := fun j x => by
    simp only [conv, (hup j).fderiv x, hup j x]
  -- (0) `‖ω‖² = ∫⟪ω, ω⟫`, then E2
  have heq : enstrophyT F.u = fun s => ∫ x in cubeQ, ⟪vort F.u s x, vort F.u s x⟫ := by
    funext s
    rw [enstrophyT_eq]
    simp_rw [real_inner_self_eq_norm_sq]
  rw [heq]
  refine (F.hasDerivAt_integral_vort ht).congr_deriv ?_
  show ∫ x in cubeQ, 2 * ⟪ω x, curl (F.dtu t) x⟫ = _
  -- (1) E3
  have h1 : ∫ x in cubeQ, ⟪ω x, curl (F.dtu t) x⟫ = ∫ x in cubeQ, ⟪curl ω x, F.dtu t x⟫ :=
    (integral_cubeQ_inner_curl_comm hω1 hdt1 hωp hdtp).symm
  -- (2) substitute the momentum equation and split the integral
  have hgr : ∀ x, ⟪curl ω x, gradient (F.p t) x⟫ = fderiv ℝ (F.p t) x (curl ω x) := fun x => by
    rw [real_inner_comm, inner_gradient_left]
  have c1 : Continuous fun x => ⟪curl ω x, lap u x⟫ :=
    hcω1.continuous.inner (continuous_lap hu2)
  have c2 : Continuous fun x => ⟪curl ω x, conv u x⟫ :=
    hcω1.continuous.inner hconv1.continuous
  have c3 : Continuous fun x => ⟪curl ω x, gradient (F.p t) x⟫ := by
    simp_rw [hgr]
    exact (hp1.continuous_fderiv (by norm_num)).clm_apply hcω1.continuous
  have hpt : ∀ x, ⟪curl ω x, F.dtu t x⟫ = F.ν * ⟪curl ω x, lap u x⟫
      - ⟪curl ω x, conv u x⟫ - ⟪curl ω x, gradient (F.p t) x⟫ := fun x => by
    rw [F.dtu_eq ht x, inner_sub_right, inner_sub_right, inner_smul_right]
    rfl
  have h2 : ∫ x in cubeQ, ⟪curl ω x, F.dtu t x⟫
      = F.ν * (∫ x in cubeQ, ⟪curl ω x, lap u x⟫) - (∫ x in cubeQ, ⟪curl ω x, conv u x⟫)
        - ∫ x in cubeQ, ⟪curl ω x, gradient (F.p t) x⟫ := by
    simp_rw [hpt]
    rw [integral_sub (f := fun x => F.ν * ⟪curl ω x, lap u x⟫ - ⟪curl ω x, conv u x⟫)
        (((integrableOn_cubeQ c1).const_mul _).sub (integrableOn_cubeQ c2))
        (integrableOn_cubeQ c3),
      integral_sub (f := fun x => F.ν * ⟪curl ω x, lap u x⟫)
        ((integrableOn_cubeQ c1).const_mul _) (integrableOn_cubeQ c2),
      integral_const_mul]
  -- (3) the viscous term: `∫⟪curl ω, Δu⟫ = −∫∇ω:∇ω`
  have hvisc : ∫ x in cubeQ, ⟪curl ω x, lap u x⟫ = -palinstrophyT F.u t := by
    have hpt' : ∀ x, ⟪curl ω x, lap u x⟫ = -‖curl ω x‖ ^ 2 := by
      intro x
      rw [← real_inner_self_eq_norm_sq, inner_eq_sum, inner_eq_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [lap_apply_eq_neg_curl_curl hu3 hdiv x i]
      ring
    simp_rw [hpt']
    rw [integral_neg]
    have hA7 := integral_cubeQ_gradDot_self hω2 hωp
    simp only [hdivω, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      integral_zero, add_zero] at hA7
    show -(∫ x in cubeQ, ‖curl ω x‖ ^ 2) = -(∫ x in cubeQ, gradDot ω ω x)
    rw [hA7]
  -- (4) the convective term: `∫⟪curl ω, (u·∇)u⟫ = −∫ω·(∇u)ω`
  have hconvI : ∫ x in cubeQ, ⟪curl ω x, conv u x⟫ = -stretchingT F.u t := by
    rw [integral_cubeQ_inner_curl_comm hω1 hconv1 hωp hconvp]
    have hpt' : ∀ x, ⟪ω x, curl (conv u) x⟫
        = ⟪ω x, fderiv ℝ ω x (u x)⟫ - ⟪ω x, fderiv ℝ u x (ω x)⟫ := fun x => by
      rw [inner_curl_conv hu2 x, hdiv x, mul_zero, add_zero]
    have d1 : Continuous fun x => ⟪ω x, fderiv ℝ ω x (u x)⟫ :=
      hω1.continuous.inner ((hω1.continuous_fderiv (by norm_num)).clm_apply hu1.continuous)
    have d2 : Continuous fun x => ⟪ω x, fderiv ℝ u x (ω x)⟫ :=
      hω1.continuous.inner ((hu1.continuous_fderiv (by norm_num)).clm_apply hω1.continuous)
    simp_rw [hpt']
    rw [integral_sub (integrableOn_cubeQ d1) (integrableOn_cubeQ d2),
      integral_cubeQ_inner_convective_eq_zero hu1 hω1 hup hωp hdiv, zero_sub]
    rfl
  -- (5) the pressure term: `∫⟪curl ω, ∇p⟫ = −∫p div(curl ω) = 0`
  have hpres : ∫ x in cubeQ, ⟪curl ω x, gradient (F.p t) x⟫ = 0 := by
    rw [integral_cubeQ_inner_gradient hcω1 hp1 hcωp hpp]
    simp [hdivcω]
  rw [integral_const_mul, h1, h2, hvisc, hconvI, hpres]
  ring

end NSPeriodicData

/-- **Non-emptiness check.** The trivial solution `u = 0, p = 0` satisfies `NSPeriodicData`,
so the fields are not contradictory. -/
def NSPeriodicData.zero : NSPeriodicData where
  T := 1
  T_pos := one_pos
  ν := 1
  ν_pos := one_pos
  u := fun _ _ => 0
  p := fun _ _ => 0
  u_periodic := fun _ _ _ _ => rfl
  p_periodic := fun _ _ _ _ => rfl
  smooth := contDiffOn_const
  regular0 := contDiff_const
  cont_u := continuousOn_const
  cont_grad := by simpa using continuousOn_const
  p_regular := fun _ _ => contDiff_const
  div_free := fun _ _ _ => by simp [NavierStokes.divergence, NavierStokes.pd]
  momentum := fun t _ x => by
    simpa [NavierStokes.lap] using hasDerivAt_const t (0 : E3)

end NavierStokes.Torus
