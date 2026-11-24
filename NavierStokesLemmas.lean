/-
  NavierStokesLemmas.lean  (version 4: no `sorry` left)
  =====================================================

  A CONDITIONAL chain of deductions for the unforced 3D Navier–Stokes equations:

      (analytic data `Lemma1AnalyticInput`) ──Lemma 1──▶ (vortex stretching inequality)
         ──Lemma 2──▶ (enstrophy bound) ──Lemma 3──▶ (finite BKM integral)
         ──BKM──▶ (the solution extends past T)

  STATUS
  ------
  * No `sorry`, no `axiom`. `#print axioms` for every main theorem shows only
    `propext`, `Classical.choice`, `Quot.sound`.
  * Lemma 1: proved through the abstract framework `NSFieldData` (§3) and four sub-lemmas
    1A/1B/1C-1/1C-2, and connected to genuine solutions through `Lemma1AnalyticInput` (§7).
  * Lemma 2: Young (twice) → continuity → Grönwall with a variable coefficient. Complete.
  * Lemma 3: Agmon at each time → AM–GM → integration, under the assumption
    `H2Propagation` (§8).

  THE ASSUMPTIONS (read carefully before citing)
  ----------------------------------------------
  The final theorem `conditional_regularity` rests on the following explicit assumptions.
  (a)–(d) are known classical theorems that Mathlib does not have yet; (e)–(f) are the OPEN part:
    (a) the fields of `NSClassicalSolution` (the equations, the energy inequality, the
        enstrophy balance, continuity);
    (b) `AgmonInequality CAg`;
    (c) `BKMContinuation` (the Beale–Kato–Majda theorem, 1984);
    (d) `H2Propagation F` (bounded enstrophy ⇒ an H² bound);
    (e) `Lemma1AnalyticInput` — a Constantin–Fefferman-type alignment condition together with
        a far-field estimate; it does NOT force `T_ρ` to be the genuine Biot–Savart operator,
        so in effect it assumes the vortex stretching inequality;
    (f) `hΛ`: the coherence scale ρ(t) does not collapse too fast.
  This is NOT a solution of the Millennium Problem.

  Versions v2/v3 were compiled on live.lean-lang.org (Lean v4.37.0-rc1, latest Mathlib).

  DESIGN PRINCIPLES (kept from version 1)
  ---------------------------------------
  1. No global `axiom`: every postulate is a field of a structure / a `Prop`.
  2. The Bochner integral of a non-integrable function is `0`, so the norm `rLpNorm`
     (defined through the integral) is only meaningful together with an integrability
     hypothesis. For this reason the field `CalderonZygmundBound.bound` has been given an
     integrability hypothesis (the original version quantified over EVERY function `f`, which
     could easily make the structure empty).
-/

import Mathlib

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal RealInnerProductSpace

namespace NavierStokes

/-! ## §0. Real `L^p` norms, Young, Hölder (fully proved) -/

/-- The real-valued `L^p` norm `(∫ ‖f‖^p dμ)^{1/p}` (via the Bochner integral). -/
def rLpNorm {X V : Type*} [MeasurableSpace X] [NormedAddCommGroup V]
    (μ : Measure X) (p : ℝ) (f : X → V) : ℝ :=
  (∫ x, ‖f x‖ ^ p ∂μ) ^ (1 / p)

lemma rLpNorm_nonneg {X V : Type*} [MeasurableSpace X] [NormedAddCommGroup V]
    (μ : Measure X) (p : ℝ) (f : X → V) : 0 ≤ rLpNorm μ p f :=
  Real.rpow_nonneg (integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg (f x)) p) (1 / p)

lemma rLpNorm_rpow_eq {X V : Type*} [MeasurableSpace X] [NormedAddCommGroup V]
    (μ : Measure X) {p : ℝ} (hp : 0 < p) (f : X → V) :
    (rLpNorm μ p f) ^ p = ∫ x, ‖f x‖ ^ p ∂μ := by
  unfold rLpNorm
  have hnn : 0 ≤ ∫ x, ‖f x‖ ^ p ∂μ :=
    integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg (f x)) p
  rw [← Real.rpow_mul hnn, one_div_mul_cancel hp.ne', Real.rpow_one]

lemma rLpNorm_two_sq {X V : Type*} [MeasurableSpace X] [NormedAddCommGroup V]
    (μ : Measure X) (f : X → V) :
    (rLpNorm μ 2 f) ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  rw [← Real.rpow_two, rLpNorm_rpow_eq μ (p := 2) (by norm_num) f]
  simp_rw [Real.rpow_two]

/-- The classical Young inequality `ab ≤ a^p/p + b^q/q`, derived from weighted AM–GM. -/
lemma young_ab {a b p q : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hp : 1 < p) (hq : 1 < q) (hpq : 1 / p + 1 / q = 1) :
    a * b ≤ a ^ p / p + b ^ q / q := by
  have hp0 : 0 < p := by linarith
  have hq0 : 0 < q := by linarith
  have h := Real.geom_mean_le_arith_mean2_weighted
    (w₁ := 1 / p) (w₂ := 1 / q) (p₁ := a ^ p) (p₂ := b ^ q)
    (by positivity) (by positivity)
    (Real.rpow_nonneg ha p) (Real.rpow_nonneg hb q) hpq
  rw [← Real.rpow_mul ha, mul_one_div_cancel hp0.ne', Real.rpow_one] at h
  rw [← Real.rpow_mul hb, mul_one_div_cancel hq0.ne', Real.rpow_one] at h
  linarith [show 1 / p * a ^ p = a ^ p / p by ring,
            show 1 / q * b ^ q = b ^ q / q by ring]

/-- The integral Hölder inequality for non-negative real functions. -/
lemma holder_integral_nonneg {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {f g : X → ℝ} {p q : ℝ}
    (hp : 1 < p) (hq : 1 < q) (hpq : 1 / p + 1 / q = 1)
    (hf_nn : ∀ x, 0 ≤ f x) (hg_nn : ∀ x, 0 ≤ g x)
    (hfp : Integrable (fun x => (f x) ^ p) μ)
    (hgq : Integrable (fun x => (g x) ^ q) μ)
    (hfg : Integrable (fun x => f x * g x) μ) :
    ∫ x, f x * g x ∂μ ≤
      (∫ x, (f x) ^ p ∂μ) ^ (1 / p) * (∫ x, (g x) ^ q ∂μ) ^ (1 / q) := by
  have hp0 : 0 < p := by linarith
  have hq0 : 0 < q := by linarith
  set A := ∫ x, (f x) ^ p ∂μ with hA_def
  set B := ∫ x, (g x) ^ q ∂μ with hB_def
  have hA_nn : 0 ≤ A := integral_nonneg fun x => Real.rpow_nonneg (hf_nn x) p
  have hB_nn : 0 ≤ B := integral_nonneg fun x => Real.rpow_nonneg (hg_nn x) q
  rcases eq_or_lt_of_le hA_nn with hA0 | hA_pos
  · have h_ae : (fun x => (f x) ^ p) =ᵐ[μ] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun x => Real.rpow_nonneg (hf_nn x) p) hfp).mp hA0.symm
    have hfg_ae : (fun x => f x * g x) =ᵐ[μ] 0 := by
      filter_upwards [h_ae] with x hx
      simp only [Pi.zero_apply] at hx ⊢
      have hfx : f x = 0 := by
        by_contra hne
        exact (Real.rpow_pos_of_pos (lt_of_le_of_ne (hf_nn x) (Ne.symm hne)) p).ne' hx
      rw [hfx, zero_mul]
    rw [integral_eq_zero_of_ae hfg_ae]
    exact mul_nonneg (Real.rpow_nonneg hA_nn _) (Real.rpow_nonneg hB_nn _)
  · rcases eq_or_lt_of_le hB_nn with hB0 | hB_pos
    · have h_ae : (fun x => (g x) ^ q) =ᵐ[μ] 0 :=
        (integral_eq_zero_iff_of_nonneg (fun x => Real.rpow_nonneg (hg_nn x) q) hgq).mp hB0.symm
      have hfg_ae : (fun x => f x * g x) =ᵐ[μ] 0 := by
        filter_upwards [h_ae] with x hx
        simp only [Pi.zero_apply] at hx ⊢
        have hgx : g x = 0 := by
          by_contra hne
          exact (Real.rpow_pos_of_pos (lt_of_le_of_ne (hg_nn x) (Ne.symm hne)) q).ne' hx
        rw [hgx, mul_zero]
      rw [integral_eq_zero_of_ae hfg_ae]
      exact mul_nonneg (Real.rpow_nonneg hA_nn _) (Real.rpow_nonneg hB_nn _)
    · set Ip := A ^ (1 / p)
      set Iq := B ^ (1 / q)
      have hIp : 0 < Ip := Real.rpow_pos_of_pos hA_pos (1 / p)
      have hIq : 0 < Iq := Real.rpow_pos_of_pos hB_pos (1 / q)
      have hIp_p : Ip ^ p = A := by
        dsimp only [Ip]
        rw [← Real.rpow_mul hA_nn, one_div_mul_cancel hp0.ne', Real.rpow_one]
      have hIq_q : Iq ^ q = B := by
        dsimp only [Iq]
        rw [← Real.rpow_mul hB_nn, one_div_mul_cancel hq0.ne', Real.rpow_one]
      have h_pt : ∀ x, (Ip * Iq)⁻¹ * (f x * g x) ≤
          (1 / (p * A)) * (f x) ^ p + (1 / (q * B)) * (g x) ^ q := by
        intro x
        have hY := young_ab
          (a := f x / Ip) (b := g x / Iq)
          (div_nonneg (hf_nn x) hIp.le) (div_nonneg (hg_nn x) hIq.le) hp hq hpq
        rw [Real.div_rpow (hf_nn x) hIp.le p, hIp_p,
            Real.div_rpow (hg_nn x) hIq.le q, hIq_q] at hY
        have hL : (Ip * Iq)⁻¹ * (f x * g x) = (f x / Ip) * (g x / Iq) := by
          rw [mul_inv]; ring
        have hR1 : (1 / (p * A)) * (f x) ^ p = (f x) ^ p / A / p := by
          rw [one_div, mul_inv]; ring
        have hR2 : (1 / (q * B)) * (g x) ^ q = (g x) ^ q / B / q := by
          rw [one_div, mul_inv]; ring
        linarith
      have hsum : Integrable
          (fun x => (1 / (p * A)) * (f x) ^ p + (1 / (q * B)) * (g x) ^ q) μ :=
        (hfp.const_mul _).add (hgq.const_mul _)
      have h_int := integral_mono (hfg.const_mul (Ip * Iq)⁻¹) hsum h_pt
      rw [integral_const_mul, integral_add (hfp.const_mul _) (hgq.const_mul _),
          integral_const_mul, integral_const_mul, ← hA_def, ← hB_def] at h_int
      have h_rhs : (1 / (p * A)) * A + (1 / (q * B)) * B = 1 := by
        have h1 : (1 / (p * A)) * A = 1 / p := by
          rw [one_div, mul_inv]
          calc p⁻¹ * A⁻¹ * A = (1 / p) * (A / A) := by ring
            _ = (1 / p) * 1 := by rw [div_self hA_pos.ne']
            _ = 1 / p := mul_one _
        have h2 : (1 / (q * B)) * B = 1 / q := by
          rw [one_div, mul_inv]
          calc q⁻¹ * B⁻¹ * B = (1 / q) * (B / B) := by ring
            _ = (1 / q) * 1 := by rw [div_self hB_pos.ne']
            _ = 1 / q := mul_one _
        linarith
      rw [h_rhs] at h_int
      have h_mul := mul_le_mul_of_nonneg_left h_int (mul_pos hIp hIq).le
      calc ∫ x, f x * g x ∂μ
          = (Ip * Iq) * ((Ip * Iq)⁻¹ * ∫ x, f x * g x ∂μ) := by
            rw [← mul_assoc, mul_inv_cancel₀ (mul_pos hIp hIq).ne', one_mul]
        _ ≤ (Ip * Iq) * 1 := h_mul
        _ = Ip * Iq := mul_one _

/-- `(x²)^a = x^{2a}` for `x ≥ 0`. -/
lemma sq_rpow_eq {x : ℝ} (hx : 0 ≤ x) (a : ℝ) : (x ^ 2) ^ a = x ^ (2 * a) := by
  rw [← Real.rpow_two, ← Real.rpow_mul hx]

/-! ## §1. Basic objects: ℝ³, velocity, vorticity, norms -/

/-- Euclidean space ℝ³. -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- The standard basis vector `e_j`. -/
def basisVec (j : Fin 3) : E3 := EuclideanSpace.single j (1 : ℝ)

/-- The partial derivative `∂_j v_i (x)`. -/
def pd (v : E3 → E3) (j i : Fin 3) (x : E3) : ℝ :=
  EuclideanSpace.proj i (fderiv ℝ v x (basisVec j))

/-- The curl operator: `curl v = (∂₁v₂ − ∂₂v₁, ∂₂v₀ − ∂₀v₂, ∂₀v₁ − ∂₁v₀)`. -/
def curl (v : E3 → E3) (x : E3) : E3 :=
  (pd v 1 2 x - pd v 2 1 x) • basisVec 0
    + (pd v 2 0 x - pd v 0 2 x) • basisVec 1
    + (pd v 0 1 x - pd v 1 0 x) • basisVec 2

/-- Divergence `∇·v`. -/
def divergence (v : E3 → E3) (x : E3) : ℝ := ∑ i : Fin 3, pd v i i x

/-- The vector Laplacian `Δv = Σ_j ∂_j ∂_j v`. -/
def lap (v : E3 → E3) (x : E3) : E3 :=
  ∑ j : Fin 3, fderiv ℝ (fun y => fderiv ℝ v y (basisVec j)) x (basisVec j)

/-- The `L²` norm on ℝ³. It uses the SAME definition `rLpNorm` as the Lemma 1 framework, so
that the bridge in §6 does not have to convert between `eLpNorm` and the Bochner integral. Only
meaningful together with a hypothesis `MemLp _ 2`. -/
def normL2 {F : Type*} [NormedAddCommGroup F] (f : E3 → F) : ℝ := rLpNorm volume 2 f

/-- The `L^∞` norm (real-valued; only meaningful when the function is essentially bounded). -/
def normLinf {F : Type*} [NormedAddCommGroup F] (f : E3 → F) : ℝ :=
  (eLpNorm f ⊤ volume).toReal

/-- The vorticity `ω(t) = ∇ × u(t)`. -/
def vort (u : ℝ → E3 → E3) (t : ℝ) : E3 → E3 := curl (u t)

/-- `‖u(t)‖_{L²}`. -/
def energyNorm (u : ℝ → E3 → E3) (t : ℝ) : ℝ := normL2 (u t)

/-- Enstrophy `Y(t) = ‖ω(t)‖²_{L²}`. -/
def enstrophy (u : ℝ → E3 → E3) (t : ℝ) : ℝ := normL2 (vort u t) ^ 2

/-- Palinstrophy `D(t) = ‖∇ω(t)‖²_{L²}`. -/
def palinstrophy (u : ℝ → E3 → E3) (t : ℝ) : ℝ := normL2 (fderiv ℝ (vort u t)) ^ 2

/-- The vortex stretching term `∫ ω · (∇u) ω dx = ∫ ω · S ω dx`. -/
def stretching (u : ℝ → E3 → E3) (t : ℝ) : ℝ :=
  ∫ x, ⟪vort u t x, fderiv ℝ (u t) x (vort u t x)⟫

/-- The Beale–Kato–Majda integrand: `‖ω(t)‖_{L^∞}`. -/
def bkmIntegrand (u : ℝ → E3 → E3) (t : ℝ) : ℝ := normLinf (vort u t)

/-! ## §2. Abstract structures for solutions (instead of axioms) -/

/-- A divergence-free velocity field, smooth enough on `[0, T)`. -/
structure DivFreeH3Field where
  T : ℝ
  T_pos : 0 < T
  u : ℝ → E3 → E3
  regular : ∀ t ∈ Ico 0 T, ContDiff ℝ 3 (u t)
  div_free : ∀ t ∈ Ico 0 T, ∀ x, divergence (u t) x = 0
  memL2_u : ∀ t ∈ Ico 0 T, MemLp (u t) 2 volume
  memL2_vort : ∀ t ∈ Ico 0 T, MemLp (vort u t) 2 volume
  memL2_grad_vort : ∀ t ∈ Ico 0 T, MemLp (fderiv ℝ (vort u t)) 2 volume
  memL2_hess_vort : ∀ t ∈ Ico 0 T,
    MemLp (fun x => iteratedFDeriv ℝ 2 (vort u t) x) 2 volume

/-- A classical solution of the 3D incompressible Navier–Stokes equations on `ℝ³ × [0, T)`. -/
structure NSClassicalSolution extends DivFreeH3Field where
  ν : ℝ
  ν_pos : 0 < ν
  p : ℝ → E3 → ℝ
  /-- `∂ₜu = νΔu − (u·∇)u − ∇p`. -/
  momentum : ∀ t ∈ Ioo 0 T, ∀ x, HasDerivAt (fun s => u s x)
    (ν • lap (u t) x - fderiv ℝ (u t) x (u t x) - gradient (p t) x) t
  /-- The Leray–Hopf energy inequality. -/
  energy_ineq : ∀ t ∈ Ico 0 T,
    energyNorm u t ^ 2 + 2 * ν * (∫ s in (0:ℝ)..t, enstrophy u s) ≤ energyNorm u 0 ^ 2
  enstrophy_cont : ContinuousOn (enstrophy u) (Ico 0 T)
  energy_cont : ContinuousOn (energyNorm u) (Ico 0 T)
  /-- The enstrophy balance: `d/dt ‖ω‖² = −2ν‖∇ω‖² + 2∫ ω·Sω`. -/
  enstrophy_balance : ∀ t ∈ Ioo 0 T,
    HasDerivAt (enstrophy u) (-2 * ν * palinstrophy u t + 2 * stretching u t) t

/-- The 3D Agmon inequality `‖f‖_∞ ≤ C ‖∇f‖^{1/2} ‖∇²f‖^{1/2}` (as a `Prop`). -/
def AgmonInequality (C : ℝ) : Prop :=
  ∀ f : E3 → E3, ContDiff ℝ 2 f → MemLp f 2 volume → MemLp (fderiv ℝ f) 2 volume →
    MemLp (fun x => iteratedFDeriv ℝ 2 f x) 2 volume →
    normLinf f ≤ C * normL2 (fderiv ℝ f) ^ (1/2 : ℝ)
      * normL2 (fun x => iteratedFDeriv ℝ 2 f x) ^ (1/2 : ℝ)

/-- The Beale–Kato–Majda continuation criterion (1984), as a `Prop`. -/
def BKMContinuation : Prop :=
  ∀ F : NSClassicalSolution,
    (∃ B : ℝ, ∀ t ∈ Ico 0 F.T,
      IntervalIntegrable (bkmIntegrand F.u) volume 0 t ∧
        ∫ s in (0:ℝ)..t, bkmIntegrand F.u s ≤ B) →
    ∃ G : NSClassicalSolution, G.ν = F.ν ∧ F.T < G.T ∧ ∀ t ∈ Ico 0 F.T, G.u t = F.u t

/-! ## §3. Lemma 1 — the abstract framework at one time slice -/

/-- The data of a time slice at time `t`, together with the truncation operator `T_ρ`. -/
structure NSFieldData (X V W M3 : Type*) [MeasurableSpace X]
    [NormedAddCommGroup V] [NormedAddCommGroup W] [NormedAddCommGroup M3]
    (μ : Measure X) where
  u : X → V
  ω : X → V
  gradω : X → W
  M : ℝ
  ρ : ℝ
  β : ℝ
  ν : ℝ
  hM : 0 < M
  hρ : 0 < ρ
  hβ_lo : (1 : ℝ) / 2 ≤ β
  hβ_hi : β ≤ 1
  hν : 0 < ν
  /-- The truncated singular integral operator `T_ρ` (near field). -/
  T_ρ : (X → V) → (X → M3)
  T_ρ_add : ∀ f g x, T_ρ (f + g) x = T_ρ f x + T_ρ g x
  /-- The local stretching density `F(x, A) = ω(x)ᵀ A ω(x)`. -/
  F : X → M3 → ℝ
  F_add : ∀ x A B, F x (A + B) = F x A + F x B
  F_bound : ∀ x A, |F x A| ≤ ‖ω x‖ ^ 2 * ‖A‖
  /-- The total stretching term and its far-field part. -/
  S_total : ℝ
  S_far : ℝ
  S_split : S_total = S_far + ∫ x, F x (T_ρ ω x) ∂μ
  /-- The Riesz potential `R_β(ω)`. -/
  R_β : ℝ
  hR_β_nn : 0 ≤ R_β
  hΩ_meas : MeasurableSet {x : X | M < ‖ω x‖}
  hInt_near : Integrable (fun x => F x (T_ρ ω x)) μ
  hInt_I1 : Integrable (fun x => F x (T_ρ ({y | M < ‖ω y‖}.indicator ω) x))
    (μ.restrict {x | M < ‖ω x‖})
  hInt_I2 : Integrable (fun x => F x (T_ρ ({y | M < ‖ω y‖}ᶜ.indicator ω) x))
    (μ.restrict {x | M < ‖ω x‖})
  hInt_ω2 : Integrable (fun x => ‖ω x‖ ^ (2 : ℝ)) μ
  hInt_ω83 : Integrable (fun x => (‖ω x‖ ^ 2) ^ (4 / 3 : ℝ)) μ
  hInt_ωlo4 : Integrable (fun x => ‖({y | M < ‖ω y‖}ᶜ.indicator ω) x‖ ^ (4 : ℝ)) μ
  hInt_Tωlo4 : Integrable (fun x => ‖T_ρ ({y | M < ‖ω y‖}ᶜ.indicator ω) x‖ ^ (4 : ℝ)) μ
  hInt_Tω2 : Integrable (fun x => ‖T_ρ ω x‖ ^ (2 : ℝ)) μ
  hInt_HL_prod : Integrable (fun x => ‖ω x‖ ^ 2 * ‖T_ρ ({y | M < ‖ω y‖}ᶜ.indicator ω) x‖) μ
  hInt_L_prod : Integrable (fun x => ‖ω x‖ * ‖T_ρ ω x‖) μ

section Lemma1Abstract

variable {X V W M3 : Type*} [MeasurableSpace X]
  [NormedAddCommGroup V] [NormedAddCommGroup W] [NormedAddCommGroup M3]
  {μ : Measure X}

/-- The high-vorticity region `Ω_M = {x : |ω(x)| > M}`. -/
def Ω_M (d : NSFieldData X V W M3 μ) : Set X := {x | d.M < ‖d.ω x‖}

/-- `ω_> = ω 𝟙_{Ω_M}`. -/
def ω_hi (d : NSFieldData X V W M3 μ) : X → V := (Ω_M d).indicator d.ω

/-- `ω_≤ = ω 𝟙_{Ω_Mᶜ}`. -/
def ω_lo (d : NSFieldData X V W M3 μ) : X → V := (Ω_M d)ᶜ.indicator d.ω

/-- The three near-field pieces `I₁` (High–High), `I₂` (High–Low), `I₃` (Low). -/
def I₁ (d : NSFieldData X V W M3 μ) : ℝ := ∫ x in Ω_M d, d.F x (d.T_ρ (ω_hi d) x) ∂μ
def I₂ (d : NSFieldData X V W M3 μ) : ℝ := ∫ x in Ω_M d, d.F x (d.T_ρ (ω_lo d) x) ∂μ
def I₃ (d : NSFieldData X V W M3 μ) : ℝ := ∫ x in (Ω_M d)ᶜ, d.F x (d.T_ρ d.ω x) ∂μ

/-- Package 1 (ASSUMPTION): a bound on the far-field kernel after integration by parts. -/
structure FarFieldKernelBound (d : NSFieldData X V W M3 μ) where
  K₃ : ℝ
  gradK_L2 : ℝ
  hK₃_nn : 0 ≤ K₃
  hgradK_nn : 0 ≤ gradK_L2
  hgradK_bound : gradK_L2 ≤ K₃ * d.ρ ^ (-(5 : ℝ) / 2)
  hS_far_cs : |d.S_far| ≤ ∫ x, ‖d.ω x‖ ^ 2 * (gradK_L2 * rLpNorm μ 2 d.u) ∂μ

/-- Package 2 (ASSUMPTION): Calderón–Zygmund, bounded uniformly in `ρ` on `L^p`.
An integrability hypothesis `‖f‖^p ∈ L¹` has been added compared with the original version. -/
structure CalderonZygmundBound (d : NSFieldData X V W M3 μ) where
  C_CZ : ℝ → ℝ
  hC_CZ_nn : ∀ p, 1 < p → 0 ≤ C_CZ p
  bound : ∀ p, 1 < p → ∀ f : X → V, Integrable (fun x => ‖f x‖ ^ p) μ →
    rLpNorm μ p (d.T_ρ f) ≤ C_CZ p * rLpNorm μ p f

/-- Package 3 (ASSUMPTION): Hardy–Littlewood–Sobolev for `R_β`. -/
structure HLSBound (d : NSFieldData X V W M3 μ) where
  C_HLS : ℝ
  hC_HLS_nn : 0 ≤ C_HLS
  bound : ∀ p q : ℝ, 1 < p → 1 < q → 1 / p + 1 / q + (3 - d.β) / 3 = 2 →
    p = q / 2 → d.R_β ≤ C_HLS * (rLpNorm μ q d.ω) ^ 3

/-- Package 4 (ASSUMPTION): 3D Gagliardo–Nirenberg. -/
structure GagliardoNirenberg3D (d : NSFieldData X V W M3 μ) where
  C_GN : ℝ → ℝ
  hC_GN_nn : ∀ r, 2 < r → r < 6 → 0 ≤ C_GN r
  bound : ∀ r θ : ℝ, 2 < r → r < 6 → θ = 3 * (1 / 2 - 1 / r) →
    rLpNorm μ r d.ω ≤ C_GN r * (rLpNorm μ 2 d.ω) ^ (1 - θ) * (rLpNorm μ 2 d.gradω) ^ θ

/-- Package 5 (ASSUMPTION): control of the vorticity direction angle, `A(t) < ∞`
(Constantin–Fefferman).
Note: `A_sup` is an arbitrary number, not yet defined from the actual angle of `ω`; the real
content lies in `hI₁_kernel`. -/
structure VorticityAlignmentHyp (d : NSFieldData X V W M3 μ) where
  C₀ : ℝ
  hC₀_nn : 0 ≤ C₀
  A_sup : ℝ≥0∞
  hA_fin : A_sup < ⊤
  hA_scale : A_sup.toReal ≤ C₀ * d.ρ ^ (-d.β)
  hI₁_kernel : |I₁ d| ≤ (3 / (4 * Real.pi)) * A_sup.toReal * d.R_β

/-- The High–High near-field constant. -/
def nearHHConst (d : NSFieldData X V W M3 μ) (hAlign : VorticityAlignmentHyp d)
    (hHLS : HLSBound d) (hGN : GagliardoNirenberg3D d) : ℝ :=
  (3 / (4 * Real.pi)) * hAlign.C₀ * hHLS.C_HLS * (hGN.C_GN (9 / (3 + d.β))) ^ 3

/-- The High–Low near-field constant. -/
def nearHLConst (d : NSFieldData X V W M3 μ) (hCZ : CalderonZygmundBound d)
    (hGN : GagliardoNirenberg3D d) : ℝ :=
  hCZ.C_CZ 4 * (hGN.C_GN (8 / 3)) ^ 2

lemma ω_hi_add_ω_lo (d : NSFieldData X V W M3 μ) : ω_hi d + ω_lo d = d.ω :=
  Set.indicator_self_add_compl _ _

/-- Splitting the near field into `I₁ + I₂ + I₃`. -/
lemma near_field_domain_split (d : NSFieldData X V W M3 μ) :
    ∫ x, d.F x (d.T_ρ d.ω x) ∂μ = I₁ d + I₂ d + I₃ d := by
  have hmeas : MeasurableSet (Ω_M d) := d.hΩ_meas
  have h_compl := integral_add_compl hmeas d.hInt_near
  have hI1 : Integrable (fun x => d.F x (d.T_ρ (ω_hi d) x)) (μ.restrict (Ω_M d)) :=
    d.hInt_I1
  have hI2 : Integrable (fun x => d.F x (d.T_ρ (ω_lo d) x)) (μ.restrict (Ω_M d)) :=
    d.hInt_I2
  have h_eq : (fun x => d.F x (d.T_ρ d.ω x)) =
      fun x => d.F x (d.T_ρ (ω_hi d) x) + d.F x (d.T_ρ (ω_lo d) x) := by
    funext x
    rw [← d.F_add, ← d.T_ρ_add, ω_hi_add_ω_lo]
  have h_hi : ∫ x in Ω_M d, d.F x (d.T_ρ d.ω x) ∂μ = I₁ d + I₂ d := by
    rw [h_eq, integral_add hI1 hI2, I₁, I₂]
  rw [← h_compl, h_hi, I₃]

lemma norm_ω_lo_le_M (d : NSFieldData X V W M3 μ) (x : X) : ‖ω_lo d x‖ ≤ d.M := by
  classical
  unfold ω_lo
  rw [Set.indicator_apply]
  split_ifs with hx
  · have hx' : ¬ (d.M < ‖d.ω x‖) := hx
    exact not_lt.mp hx'
  · rw [norm_zero]; exact d.hM.le

lemma norm_ω_lo_le_norm (d : NSFieldData X V W M3 μ) (x : X) : ‖ω_lo d x‖ ≤ ‖d.ω x‖ := by
  classical
  unfold ω_lo
  rw [Set.indicator_apply]
  split_ifs
  · exact le_rfl
  · rw [norm_zero]; exact norm_nonneg _

/-- `‖ω_≤(x)‖⁴ ≤ M² ‖ω(x)‖²`. -/
lemma norm_ω_lo_pow_four_le (d : NSFieldData X V W M3 μ) (x : X) :
    ‖ω_lo d x‖ ^ (4 : ℝ) ≤ d.M ^ (2 : ℝ) * ‖d.ω x‖ ^ (2 : ℝ) := by
  have h1 := norm_ω_lo_le_M d x
  have h2 := norm_ω_lo_le_norm d x
  have h0 := norm_nonneg (ω_lo d x)
  rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
    Real.rpow_two, Real.rpow_two]
  have ha : ‖ω_lo d x‖ ^ 2 ≤ d.M ^ 2 := pow_le_pow_left₀ h0 h1 2
  have hb : ‖ω_lo d x‖ ^ 2 ≤ ‖d.ω x‖ ^ 2 := pow_le_pow_left₀ h0 h2 2
  calc ‖ω_lo d x‖ ^ 4 = ‖ω_lo d x‖ ^ 2 * ‖ω_lo d x‖ ^ 2 := by ring
    _ ≤ d.M ^ 2 * ‖d.ω x‖ ^ 2 := mul_le_mul ha hb (sq_nonneg _) (sq_nonneg _)

/-- `‖ω_≤‖_{L⁴} ≤ M^{1/2} ‖ω‖_{L²}^{1/2}`. -/
lemma rLpNorm_four_ω_lo_le (d : NSFieldData X V W M3 μ) :
    rLpNorm μ 4 (ω_lo d) ≤ d.M ^ ((1 : ℝ) / 2) * (rLpNorm μ 2 d.ω) ^ ((1 : ℝ) / 2) := by
  have h_int : ∫ x, ‖ω_lo d x‖ ^ (4 : ℝ) ∂μ ≤ d.M ^ (2 : ℝ) * ∫ x, ‖d.ω x‖ ^ (2 : ℝ) ∂μ := by
    calc ∫ x, ‖ω_lo d x‖ ^ (4 : ℝ) ∂μ
        ≤ ∫ x, d.M ^ (2 : ℝ) * ‖d.ω x‖ ^ (2 : ℝ) ∂μ :=
          integral_mono d.hInt_ωlo4 (d.hInt_ω2.const_mul (d.M ^ (2 : ℝ)))
            (norm_ω_lo_pow_four_le d)
      _ = d.M ^ (2 : ℝ) * ∫ x, ‖d.ω x‖ ^ (2 : ℝ) ∂μ := integral_const_mul _ _
  have hI_nn : 0 ≤ ∫ x, ‖d.ω x‖ ^ (2 : ℝ) ∂μ :=
    integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _
  have h_rpow := Real.rpow_le_rpow
    (integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _) h_int
    (by norm_num : (0 : ℝ) ≤ 1 / 4)
  unfold rLpNorm
  calc (∫ x, ‖ω_lo d x‖ ^ (4 : ℝ) ∂μ) ^ ((1 : ℝ) / 4)
      ≤ (d.M ^ (2 : ℝ) * ∫ x, ‖d.ω x‖ ^ (2 : ℝ) ∂μ) ^ ((1 : ℝ) / 4) := h_rpow
    _ = (d.M ^ (2 : ℝ)) ^ ((1 : ℝ) / 4) * (∫ x, ‖d.ω x‖ ^ (2 : ℝ) ∂μ) ^ ((1 : ℝ) / 4) :=
        Real.mul_rpow (Real.rpow_nonneg d.hM.le _) hI_nn
    _ = d.M ^ ((1 : ℝ) / 2) * ((∫ x, ‖d.ω x‖ ^ (2 : ℝ) ∂μ) ^ ((1 : ℝ) / 2)) ^ ((1 : ℝ) / 2) := by
        rw [← Real.rpow_mul d.hM.le, ← Real.rpow_mul hI_nn]
        norm_num

/-- **Sub-lemma 1A (far field):** `|S_far| ≤ K₃ ρ^{-5/2} ‖u‖ ‖ω‖²`. -/
lemma sublemma_1A_far_field (d : NSFieldData X V W M3 μ) (hFar : FarFieldKernelBound d) :
    |d.S_far| ≤ hFar.K₃ * d.ρ ^ (-(5 : ℝ) / 2) * rLpNorm μ 2 d.u * (rLpNorm μ 2 d.ω) ^ 2 := by
  have h_pull :
      ∫ x, ‖d.ω x‖ ^ 2 * (hFar.gradK_L2 * rLpNorm μ 2 d.u) ∂μ =
      (rLpNorm μ 2 d.ω) ^ 2 * (hFar.gradK_L2 * rLpNorm μ 2 d.u) := by
    rw [integral_mul_const, rLpNorm_two_sq]
  have h1 : |d.S_far| ≤ hFar.gradK_L2 * rLpNorm μ 2 d.u * (rLpNorm μ 2 d.ω) ^ 2 := by
    linarith [hFar.hS_far_cs, h_pull]
  have h_nn : 0 ≤ rLpNorm μ 2 d.u * (rLpNorm μ 2 d.ω) ^ 2 :=
    mul_nonneg (rLpNorm_nonneg μ 2 d.u) (sq_nonneg _)
  have h2 := mul_le_mul_of_nonneg_right hFar.hgradK_bound h_nn
  linarith

/-- **Sub-lemma 1B (High–High):**
`|I₁| ≤ K₁ ρ^{-β} ‖ω‖^{3/2+β} ‖∇ω‖^{3/2−β}`, with `r = 9/(3+β)` (HLS) and
`θ = (3−2β)/6` (GN). -/
lemma sublemma_1B_near_HH (d : NSFieldData X V W M3 μ)
    (hAlign : VorticityAlignmentHyp d) (hHLS : HLSBound d) (hGN : GagliardoNirenberg3D d) :
    |I₁ d| ≤ nearHHConst d hAlign hHLS hGN * d.ρ ^ (-d.β) *
      (rLpNorm μ 2 d.ω) ^ (3 / 2 + d.β) * (rLpNorm μ 2 d.gradω) ^ (3 / 2 - d.β) := by
  have h3β_pos : 0 < 3 + d.β := by linarith [d.hβ_lo]
  have hr_gt2 : 2 < 9 / (3 + d.β) := by rw [lt_div_iff₀ h3β_pos]; linarith [d.hβ_hi]
  have hr_lt6 : 9 / (3 + d.β) < 6 := by rw [div_lt_iff₀ h3β_pos]; linarith [d.hβ_lo]
  have hp_gt1 : 1 < 9 / (3 + d.β) / 2 := by linarith
  have hq_gt1 : 1 < 9 / (3 + d.β) := by linarith
  have h_hls_exp : 1 / (9 / (3 + d.β) / 2) + 1 / (9 / (3 + d.β)) + (3 - d.β) / 3 = 2 := by
    rw [div_div, one_div_div, one_div_div]; ring
  have hR_bound : d.R_β ≤ hHLS.C_HLS * (rLpNorm μ (9 / (3 + d.β)) d.ω) ^ 3 :=
    hHLS.bound _ _ hp_gt1 hq_gt1 h_hls_exp rfl
  have hθ_eq : (3 - 2 * d.β) / 6 = 3 * (1 / 2 - 1 / (9 / (3 + d.β))) := by
    rw [one_div_div]; ring
  have hGN_r := hGN.bound (9 / (3 + d.β)) ((3 - 2 * d.β) / 6) hr_gt2 hr_lt6 hθ_eq
  have hW2_nn : 0 ≤ rLpNorm μ 2 d.ω := rLpNorm_nonneg μ 2 d.ω
  have hG2_nn : 0 ≤ rLpNorm μ 2 d.gradω := rLpNorm_nonneg μ 2 d.gradω
  have hGN_cube : (rLpNorm μ (9 / (3 + d.β)) d.ω) ^ 3 ≤
      (hGN.C_GN (9 / (3 + d.β))) ^ 3 * (rLpNorm μ 2 d.ω) ^ (3 / 2 + d.β) *
        (rLpNorm μ 2 d.gradω) ^ (3 / 2 - d.β) := by
    have h_pow3 := pow_le_pow_left₀ (rLpNorm_nonneg μ _ d.ω) hGN_r 3
    have h1 : ((rLpNorm μ 2 d.ω) ^ (1 - (3 - 2 * d.β) / 6)) ^ (3 : ℕ) =
        (rLpNorm μ 2 d.ω) ^ (3 / 2 + d.β) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hW2_nn]
      congr 1; push_cast; ring
    have h2 : ((rLpNorm μ 2 d.gradω) ^ ((3 - 2 * d.β) / 6)) ^ (3 : ℕ) =
        (rLpNorm μ 2 d.gradω) ^ (3 / 2 - d.β) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hG2_nn]
      congr 1; push_cast; ring
    rw [mul_pow, mul_pow, h1, h2] at h_pow3
    exact h_pow3
  have h3pi_nn : 0 ≤ 3 / (4 * Real.pi) := by positivity
  have hρβ : 0 ≤ d.ρ ^ (-d.β) := Real.rpow_nonneg d.hρ.le _
  have h_step1 : |I₁ d| ≤ (3 / (4 * Real.pi)) * (hAlign.C₀ * d.ρ ^ (-d.β)) * d.R_β :=
    hAlign.hI₁_kernel.trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hAlign.hA_scale h3pi_nn)
        d.hR_β_nn)
  have h_pref_nn : 0 ≤ (3 / (4 * Real.pi)) * (hAlign.C₀ * d.ρ ^ (-d.β)) :=
    mul_nonneg h3pi_nn (mul_nonneg hAlign.hC₀_nn hρβ)
  have h_step2 : d.R_β ≤ hHLS.C_HLS * ((hGN.C_GN (9 / (3 + d.β))) ^ 3 *
      (rLpNorm μ 2 d.ω) ^ (3 / 2 + d.β) * (rLpNorm μ 2 d.gradω) ^ (3 / 2 - d.β)) :=
    hR_bound.trans (mul_le_mul_of_nonneg_left hGN_cube hHLS.hC_HLS_nn)
  have h_step3 := mul_le_mul_of_nonneg_left h_step2 h_pref_nn
  have h_rearr :
      (3 / (4 * Real.pi)) * (hAlign.C₀ * d.ρ ^ (-d.β)) *
        (hHLS.C_HLS * ((hGN.C_GN (9 / (3 + d.β))) ^ 3 * (rLpNorm μ 2 d.ω) ^ (3 / 2 + d.β) *
          (rLpNorm μ 2 d.gradω) ^ (3 / 2 - d.β))) =
      nearHHConst d hAlign hHLS hGN * d.ρ ^ (-d.β) * (rLpNorm μ 2 d.ω) ^ (3 / 2 + d.β) *
        (rLpNorm μ 2 d.gradω) ^ (3 / 2 - d.β) := by
    unfold nearHHConst; ring
  linarith

/-- **Sub-lemma 1C-1 (High–Low):** `|I₂| ≤ K₂ M^{1/2} ‖ω‖^{7/4} ‖∇ω‖^{3/4}`
(Hölder `(4/3, 4)` + CZ at `p = 4` + GN at `r = 8/3`). -/
lemma sublemma_1C_near_HL (d : NSFieldData X V W M3 μ)
    (hCZ : CalderonZygmundBound d) (hGN : GagliardoNirenberg3D d) :
    |I₂ d| ≤ nearHLConst d hCZ hGN * d.M ^ ((1 : ℝ) / 2) *
      (rLpNorm μ 2 d.ω) ^ ((7 : ℝ) / 4) * (rLpNorm μ 2 d.gradω) ^ ((3 : ℝ) / 4) := by
  -- Step 1: move the absolute value inside and extend to the whole space
  have h_abs : |I₂ d| ≤ ∫ x, ‖d.ω x‖ ^ 2 * ‖d.T_ρ (ω_lo d) x‖ ∂μ := by
    have h1 : |I₂ d| ≤ ∫ x in Ω_M d, |d.F x (d.T_ρ (ω_lo d) x)| ∂μ :=
      abs_integral_le_integral_abs
    have h2 : ∫ x in Ω_M d, |d.F x (d.T_ρ (ω_lo d) x)| ∂μ ≤
        ∫ x in Ω_M d, ‖d.ω x‖ ^ 2 * ‖d.T_ρ (ω_lo d) x‖ ∂μ :=
      integral_mono d.hInt_I2.abs d.hInt_HL_prod.integrableOn
        (fun x => d.F_bound x (d.T_ρ (ω_lo d) x))
    have h3 : ∫ x in Ω_M d, ‖d.ω x‖ ^ 2 * ‖d.T_ρ (ω_lo d) x‖ ∂μ ≤
        ∫ x, ‖d.ω x‖ ^ 2 * ‖d.T_ρ (ω_lo d) x‖ ∂μ :=
      setIntegral_le_integral d.hInt_HL_prod
        (Filter.Eventually.of_forall fun x => mul_nonneg (sq_nonneg _) (norm_nonneg _))
    linarith
  -- Step 2: Hölder (4/3, 4)
  have h_holder := holder_integral_nonneg μ
    (f := fun x => ‖d.ω x‖ ^ 2) (g := fun x => ‖d.T_ρ (ω_lo d) x‖)
    (p := 4 / 3) (q := 4)
    (by norm_num) (by norm_num) (by norm_num)
    (fun x => sq_nonneg _) (fun x => norm_nonneg _)
    d.hInt_ω83 d.hInt_Tωlo4 d.hInt_HL_prod
  have h_first_factor :
      (∫ x, (‖d.ω x‖ ^ 2) ^ (4 / 3 : ℝ) ∂μ) ^ (1 / (4 / 3 : ℝ)) =
      (rLpNorm μ (8 / 3) d.ω) ^ 2 := by
    have h_integrand : (fun x => (‖d.ω x‖ ^ 2) ^ (4 / 3 : ℝ)) =
        fun x => ‖d.ω x‖ ^ (8 / 3 : ℝ) := by
      funext x
      rw [← Real.rpow_two, ← Real.rpow_mul (norm_nonneg _)]
      norm_num
    rw [h_integrand]
    unfold rLpNorm
    have hI_nn : 0 ≤ ∫ x, ‖d.ω x‖ ^ (8 / 3 : ℝ) ∂μ :=
      integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _
    rw [← Real.rpow_two, ← Real.rpow_mul hI_nn]
    norm_num
  have h_after_holder :
      |I₂ d| ≤ (rLpNorm μ (8 / 3) d.ω) ^ 2 * rLpNorm μ 4 (d.T_ρ (ω_lo d)) := by
    rw [h_first_factor] at h_holder
    exact h_abs.trans h_holder
  -- Step 3: Calderón–Zygmund (p = 4) + L⁴ interpolation of ω_≤
  have h_CZ4 : rLpNorm μ 4 (d.T_ρ (ω_lo d)) ≤
      hCZ.C_CZ 4 * (d.M ^ ((1 : ℝ) / 2) * (rLpNorm μ 2 d.ω) ^ ((1 : ℝ) / 2)) :=
    (hCZ.bound 4 (by norm_num) (ω_lo d) d.hInt_ωlo4).trans
      (mul_le_mul_of_nonneg_left (rLpNorm_four_ω_lo_le d) (hCZ.hC_CZ_nn 4 (by norm_num)))
  -- Step 4: Gagliardo–Nirenberg at r = 8/3, θ = 3/8, then square
  have hGN_83 : rLpNorm μ (8 / 3) d.ω ≤
      hGN.C_GN (8 / 3) * (rLpNorm μ 2 d.ω) ^ (1 - (3 : ℝ) / 8) *
        (rLpNorm μ 2 d.gradω) ^ ((3 : ℝ) / 8) :=
    hGN.bound (8 / 3) (3 / 8) (by norm_num) (by norm_num) (by norm_num)
  have hW2_nn : 0 ≤ rLpNorm μ 2 d.ω := rLpNorm_nonneg μ 2 d.ω
  have hG2_nn : 0 ≤ rLpNorm μ 2 d.gradω := rLpNorm_nonneg μ 2 d.gradω
  have hGN_sq : (rLpNorm μ (8 / 3) d.ω) ^ 2 ≤
      (hGN.C_GN (8 / 3)) ^ 2 * (rLpNorm μ 2 d.ω) ^ ((5 : ℝ) / 4) *
        (rLpNorm μ 2 d.gradω) ^ ((3 : ℝ) / 4) := by
    have h_sq := pow_le_pow_left₀ (rLpNorm_nonneg μ (8 / 3) d.ω) hGN_83 2
    have h1 : ((rLpNorm μ 2 d.ω) ^ (1 - (3 : ℝ) / 8)) ^ (2 : ℕ) =
        (rLpNorm μ 2 d.ω) ^ ((5 : ℝ) / 4) := by
      rw [← Real.rpow_two, ← Real.rpow_mul hW2_nn]; norm_num
    have h2 : ((rLpNorm μ 2 d.gradω) ^ ((3 : ℝ) / 8)) ^ (2 : ℕ) =
        (rLpNorm μ 2 d.gradω) ^ ((3 : ℝ) / 4) := by
      rw [← Real.rpow_two, ← Real.rpow_mul hG2_nn]; norm_num
    rw [mul_pow, mul_pow, h1, h2] at h_sq
    exact h_sq
  -- Step 5: combine the exponents ‖ω‖^{5/4} · ‖ω‖^{1/2} = ‖ω‖^{7/4}
  have h_comb := mul_le_mul hGN_sq h_CZ4
    (rLpNorm_nonneg μ 4 (d.T_ρ (ω_lo d))) (by positivity)
  have h_exp_add :
      (rLpNorm μ 2 d.ω) ^ ((5 : ℝ) / 4) * (rLpNorm μ 2 d.ω) ^ ((1 : ℝ) / 2) =
      (rLpNorm μ 2 d.ω) ^ ((7 : ℝ) / 4) := by
    rw [← Real.rpow_add' hW2_nn (by norm_num : (5 : ℝ) / 4 + 1 / 2 ≠ 0)]
    norm_num
  have h_final :
      (hGN.C_GN (8 / 3)) ^ 2 * (rLpNorm μ 2 d.ω) ^ ((5 : ℝ) / 4) *
        (rLpNorm μ 2 d.gradω) ^ ((3 : ℝ) / 4) *
        (hCZ.C_CZ 4 * (d.M ^ ((1 : ℝ) / 2) * (rLpNorm μ 2 d.ω) ^ ((1 : ℝ) / 2))) =
      nearHLConst d hCZ hGN * d.M ^ ((1 : ℝ) / 2) * (rLpNorm μ 2 d.ω) ^ ((7 : ℝ) / 4) *
        (rLpNorm μ 2 d.gradω) ^ ((3 : ℝ) / 4) := by
    rw [← h_exp_add]; unfold nearHLConst; ring
  linarith

/-- **Sub-lemma 1C-2 (Low):** `|I₃| ≤ C_CZ(2) M ‖ω‖²`. -/
lemma sublemma_1C_near_L (d : NSFieldData X V W M3 μ) (hCZ : CalderonZygmundBound d) :
    |I₃ d| ≤ hCZ.C_CZ 2 * d.M * (rLpNorm μ 2 d.ω) ^ 2 := by
  have h1 : |I₃ d| ≤ ∫ x in (Ω_M d)ᶜ, |d.F x (d.T_ρ d.ω x)| ∂μ :=
    abs_integral_le_integral_abs
  have hmeasc : MeasurableSet (Ω_M d)ᶜ := d.hΩ_meas.compl
  have h_ae : ∀ᵐ x ∂(μ.restrict (Ω_M d)ᶜ),
      |d.F x (d.T_ρ d.ω x)| ≤ d.M * (‖d.ω x‖ * ‖d.T_ρ d.ω x‖) := by
    rw [ae_restrict_iff' hmeasc]
    refine Filter.Eventually.of_forall fun x hx => ?_
    have hle : ‖d.ω x‖ ≤ d.M := by
      have hx' : ¬ (d.M < ‖d.ω x‖) := hx
      exact not_lt.mp hx'
    calc |d.F x (d.T_ρ d.ω x)|
        ≤ ‖d.ω x‖ ^ 2 * ‖d.T_ρ d.ω x‖ := d.F_bound x (d.T_ρ d.ω x)
      _ = ‖d.ω x‖ * (‖d.ω x‖ * ‖d.T_ρ d.ω x‖) := by ring
      _ ≤ d.M * (‖d.ω x‖ * ‖d.T_ρ d.ω x‖) :=
        mul_le_mul_of_nonneg_right hle (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have h2 : ∫ x in (Ω_M d)ᶜ, |d.F x (d.T_ρ d.ω x)| ∂μ ≤
      d.M * ∫ x, ‖d.ω x‖ * ‖d.T_ρ d.ω x‖ ∂μ := by
    calc ∫ x in (Ω_M d)ᶜ, |d.F x (d.T_ρ d.ω x)| ∂μ
        ≤ ∫ x in (Ω_M d)ᶜ, d.M * (‖d.ω x‖ * ‖d.T_ρ d.ω x‖) ∂μ :=
          integral_mono_ae d.hInt_near.abs.integrableOn
            (d.hInt_L_prod.const_mul d.M).integrableOn h_ae
      _ = d.M * ∫ x in (Ω_M d)ᶜ, ‖d.ω x‖ * ‖d.T_ρ d.ω x‖ ∂μ := integral_const_mul _ _
      _ ≤ d.M * ∫ x, ‖d.ω x‖ * ‖d.T_ρ d.ω x‖ ∂μ :=
        mul_le_mul_of_nonneg_left
          (setIntegral_le_integral d.hInt_L_prod
            (Filter.Eventually.of_forall fun x => mul_nonneg (norm_nonneg _) (norm_nonneg _)))
          d.hM.le
  have h_cs := holder_integral_nonneg μ
    (f := fun x => ‖d.ω x‖) (g := fun x => ‖d.T_ρ d.ω x‖)
    (p := 2) (q := 2)
    (by norm_num) (by norm_num) (by norm_num)
    (fun x => norm_nonneg _) (fun x => norm_nonneg _)
    d.hInt_ω2 d.hInt_Tω2 d.hInt_L_prod
  have h_cz2 : rLpNorm μ 2 (d.T_ρ d.ω) ≤ hCZ.C_CZ 2 * rLpNorm μ 2 d.ω :=
    hCZ.bound 2 (by norm_num) d.ω d.hInt_ω2
  have h3 : ∫ x, ‖d.ω x‖ * ‖d.T_ρ d.ω x‖ ∂μ ≤ hCZ.C_CZ 2 * (rLpNorm μ 2 d.ω) ^ 2 := by
    calc ∫ x, ‖d.ω x‖ * ‖d.T_ρ d.ω x‖ ∂μ
        ≤ rLpNorm μ 2 d.ω * rLpNorm μ 2 (d.T_ρ d.ω) := h_cs
      _ ≤ rLpNorm μ 2 d.ω * (hCZ.C_CZ 2 * rLpNorm μ 2 d.ω) :=
        mul_le_mul_of_nonneg_left h_cz2 (rLpNorm_nonneg μ 2 d.ω)
      _ = hCZ.C_CZ 2 * (rLpNorm μ 2 d.ω) ^ 2 := by ring
  have h4 := mul_le_mul_of_nonneg_left h3 d.hM.le
  linarith

/-- **Lemma 1 (abstract form, no `sorry`):** split `Ω_M / Ω_Mᶜ` + the 4 sub-lemmas. -/
theorem lemma1_near_far_depletion (d : NSFieldData X V W M3 μ)
    (hFar : FarFieldKernelBound d) (hAlign : VorticityAlignmentHyp d)
    (hCZ : CalderonZygmundBound d) (hHLS : HLSBound d) (hGN : GagliardoNirenberg3D d) :
    |d.S_total| ≤
      nearHHConst d hAlign hHLS hGN * d.ρ ^ (-d.β) * (rLpNorm μ 2 d.ω) ^ (3 / 2 + d.β) *
        (rLpNorm μ 2 d.gradω) ^ (3 / 2 - d.β) +
      nearHLConst d hCZ hGN * d.M ^ ((1 : ℝ) / 2) * (rLpNorm μ 2 d.ω) ^ ((7 : ℝ) / 4) *
        (rLpNorm μ 2 d.gradω) ^ ((3 : ℝ) / 4) +
      hCZ.C_CZ 2 * d.M * (rLpNorm μ 2 d.ω) ^ 2 +
      hFar.K₃ * d.ρ ^ (-(5 : ℝ) / 2) * rLpNorm μ 2 d.u * (rLpNorm μ 2 d.ω) ^ 2 := by
  have h_decomp : d.S_total = d.S_far + (I₁ d + I₂ d + I₃ d) := by
    rw [d.S_split, near_field_domain_split d]
  have h_tri : |d.S_total| ≤ |d.S_far| + |I₁ d| + |I₂ d| + |I₃ d| := by
    rw [h_decomp]
    have e1 := abs_add_le d.S_far (I₁ d + I₂ d + I₃ d)
    have e2 := abs_add_le (I₁ d + I₂ d) (I₃ d)
    have e3 := abs_add_le (I₁ d) (I₂ d)
    linarith
  have h1A := sublemma_1A_far_field d hFar
  have h1B := sublemma_1B_near_HH d hAlign hHLS hGN
  have h1C1 := sublemma_1C_near_HL d hCZ hGN
  have h1C2 := sublemma_1C_near_L d hCZ
  linarith

end Lemma1Abstract

/-! ## §4. Exponents, the right-hand side of Lemma 1, the Grönwall coefficient -/

/-- The exponent of `D = ‖∇ω‖²` in the High–High term: `θ = (3 − 2β)/4`. -/
def thetaD (β : ℝ) : ℝ := (3 - 2 * β) / 4

/-- The exponent of `Y = ‖ω‖²` in the High–High term: `γ = (3 + 2β)/4`. -/
def gammaY (β : ℝ) : ℝ := (3 + 2 * β) / 4

/-- The conjugate exponent after Young: `q = (1 − θ)⁻¹ = 4/(1 + 2β)`. -/
def qExp (β : ℝ) : ℝ := 4 / (1 + 2 * β)

/-- The constant in the Young inequality `c·D^θ ≤ εD + C_Y(θ,ε) c^{1/(1−θ)}`. -/
def youngConst (θ ε : ℝ) : ℝ := (1 - θ) * (θ / ε) ^ (θ / (1 - θ))

/-- The right-hand side of Lemma 1 in terms of `Y = ‖ω‖²`, `D = ‖∇ω‖²`, `N = ‖u‖`:
`K₁ρ^{-β}Y^γD^θ + K₂M^{1/2}Y^{7/8}D^{3/8} + (K₂'M + K₃ρ^{-5/2}N)·Y`.
(Four terms: High–High, High–Low, Low, far field — exactly as in `lemma1_near_far_depletion`.) -/
def stretchingBound (K₁ K₂ K₂' K₃ M β : ℝ) (ρ Y D N : ℝ → ℝ) : ℝ → ℝ := fun t =>
  K₁ * ρ t ^ (-β) * Y t ^ gammaY β * D t ^ thetaD β
    + K₂ * M ^ ((1 : ℝ) / 2) * Y t ^ ((7 : ℝ) / 8) * D t ^ ((3 : ℝ) / 8)
    + (K₂' * M + K₃ * ρ t ^ (-(5 : ℝ) / 2) * N t) * Y t

/-- The Grönwall coefficient `a(t)` after two applications of Young (each with `ε = ν`):
`C_Y(θ,ν)(2K₁ρ^{-β})^q Y^{q/2} + C_Y(3/8,ν)(2K₂M^{1/2})^{8/5} Y^{2/5}
 + 2(K₂'M + K₃ρ^{-5/2}N)`. -/
def growthRate (ν β K₁ K₂ K₂' K₃ M : ℝ) (ρ Y N : ℝ → ℝ) : ℝ → ℝ := fun t =>
  youngConst (thetaD β) ν * (2 * K₁ * ρ t ^ (-β)) ^ qExp β * Y t ^ (qExp β / 2)
    + youngConst ((3 : ℝ) / 8) ν * (2 * K₂ * M ^ ((1 : ℝ) / 2)) ^ ((8 : ℝ) / 5)
        * Y t ^ ((2 : ℝ) / 5)
    + 2 * (K₂' * M + K₃ * ρ t ^ (-(5 : ℝ) / 2) * N t)

/-- Sanity check: at the critical threshold `β = 1/2` we have `q = 2`. -/
example : qExp (1/2) = 2 := by unfold qExp; norm_num

/-! ## §5. Tools for Lemma 2 (fully proved) -/

/-- **Young, absorbing form.** `c·D^θ ≤ ε·D + C_Y(θ,ε)·c^{1/(1−θ)}`. -/
theorem young_absorb {θ ε c D : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hε : 0 < ε)
    (hc : 0 ≤ c) (hD : 0 ≤ D) :
    c * D ^ θ ≤ ε * D + youngConst θ ε * c ^ (1 - θ)⁻¹ := by
  have h1θ : 0 < 1 - θ := sub_pos.mpr hθ1
  have h1θ' : (1 : ℝ) - θ ≠ 0 := h1θ.ne'
  have hθ' : θ ≠ 0 := hθ0.ne'
  have hε' : ε ≠ 0 := hε.ne'
  have hθε : 0 ≤ θ / ε := div_nonneg hθ0.le hε.le
  have hεθ : 0 ≤ ε / θ := div_nonneg hε.le hθ0.le
  have hA0 : 0 ≤ (θ / ε) ^ (θ / (1 - θ)) := Real.rpow_nonneg hθε _
  have hcq : 0 ≤ c ^ (1 - θ)⁻¹ := Real.rpow_nonneg hc _
  have key := Real.geom_mean_le_arith_mean2_weighted hθ0.le h1θ.le
    (mul_nonneg hεθ hD) (mul_nonneg hA0 hcq) (by ring : θ + (1 - θ) = 1)
  have e1 : (ε / θ * D) ^ θ = (ε / θ) ^ θ * D ^ θ := Real.mul_rpow hεθ hD
  have h3 : θ / (1 - θ) * (1 - θ) = θ := by
    rw [div_mul_eq_mul_div, mul_div_assoc, div_self h1θ', mul_one]
  have e2 : ((θ / ε) ^ (θ / (1 - θ)) * c ^ (1 - θ)⁻¹) ^ (1 - θ) = (θ / ε) ^ θ * c := by
    rw [Real.mul_rpow hA0 hcq, ← Real.rpow_mul hθε, ← Real.rpow_mul hc, h3,
      inv_mul_cancel₀ h1θ', Real.rpow_one]
  have hmul : ε / θ * (θ / ε) = 1 := by
    rw [div_mul_div_comm, mul_comm ε θ, div_self (mul_ne_zero hθ' hε')]
  have e3 : (ε / θ) ^ θ * (θ / ε) ^ θ = 1 := by
    rw [← Real.mul_rpow hεθ hθε, hmul, Real.one_rpow]
  have lhs : (ε / θ * D) ^ θ * ((θ / ε) ^ (θ / (1 - θ)) * c ^ (1 - θ)⁻¹) ^ (1 - θ)
      = c * D ^ θ := by
    rw [e1, e2]
    calc (ε / θ) ^ θ * D ^ θ * ((θ / ε) ^ θ * c)
        = ((ε / θ) ^ θ * (θ / ε) ^ θ) * (c * D ^ θ) := by ring
      _ = c * D ^ θ := by rw [e3, one_mul]
  have hθε1 : θ * (ε / θ) = ε := by
    rw [mul_div_assoc', mul_comm θ ε, mul_div_assoc, div_self hθ', mul_one]
  have hfirst : θ * (ε / θ * D) = ε * D := by rw [← mul_assoc, hθε1]
  have rhs : θ * (ε / θ * D) + (1 - θ) * ((θ / ε) ^ (θ / (1 - θ)) * c ^ (1 - θ)⁻¹)
      = ε * D + youngConst θ ε * c ^ (1 - θ)⁻¹ := by
    rw [hfirst, youngConst]; ring
  exact (lhs.symm.le.trans key).trans rhs.le

/-- **Grönwall with a variable coefficient (integrating factor).** -/
theorem gronwall_integrating_factor {Y A a : ℝ → ℝ} {T : ℝ}
    (hYc : ContinuousOn Y (Ico 0 T))
    (hAc : ∀ s ∈ Ico 0 T, ContinuousOn A (Icc 0 s))
    (hA0 : A 0 = 0)
    (hA' : ∀ t ∈ Ioo 0 T, HasDerivAt A (a t) t)
    {Y' : ℝ → ℝ} (hY' : ∀ t ∈ Ioo 0 T, HasDerivAt Y (Y' t) t)
    (hbound : ∀ t ∈ Ioo 0 T, Y' t ≤ a t * Y t) :
    ∀ t ∈ Ico 0 T, Y t ≤ Y 0 * Real.exp (A t) := by
  intro s hs
  have hZd : ∀ t ∈ Ioo 0 T, HasDerivAt (fun y => Y y * Real.exp (-A y))
      (Y' t * Real.exp (-A t) + Y t * (Real.exp (-A t) * -a t)) t := by
    intro t ht
    exact (hY' t ht).mul ((hA' t ht).neg.exp)
  have hZneg : ∀ t ∈ Ioo 0 T,
      Y' t * Real.exp (-A t) + Y t * (Real.exp (-A t) * -a t) ≤ 0 := by
    intro t ht
    have he := Real.exp_pos (-A t)
    have h0 : 0 ≤ Real.exp (-A t) * (a t * Y t - Y' t) :=
      mul_nonneg he.le (sub_nonneg.mpr (hbound t ht))
    nlinarith [h0]
  have hsub : Icc 0 s ⊆ Ico 0 T := fun x hx => ⟨hx.1, hx.2.trans_lt hs.2⟩
  have hZc : ContinuousOn (fun y => Y y * Real.exp (-A y)) (Icc 0 s) :=
    (hYc.mono hsub).mul (hAc s hs).neg.rexp
  have hanti : AntitoneOn (fun y => Y y * Real.exp (-A y)) (Icc 0 s) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 s) hZc
    · intro x hx
      rw [interior_Icc] at hx
      exact (hZd x ⟨hx.1, hx.2.trans hs.2⟩).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have hx' : x ∈ Ioo 0 T := ⟨hx.1, hx.2.trans hs.2⟩
      rw [(hZd x hx').deriv]
      exact hZneg x hx'
  have hZs : Y s * Real.exp (-A s) ≤ Y 0 * Real.exp (-A 0) :=
    hanti ⟨le_rfl, hs.1⟩ ⟨hs.1, le_rfl⟩ hs.1
  rw [hA0, neg_zero, Real.exp_zero, mul_one] at hZs
  calc Y s = Y s * Real.exp (-A s) * Real.exp (A s) := by
          rw [mul_assoc, ← Real.exp_add]; simp
    _ ≤ Y 0 * Real.exp (A s) := mul_le_mul_of_nonneg_right hZs (Real.exp_pos _).le

/-- The fundamental theorem of calculus for `A(t) = ∫₀ᵗ a`, with `a` continuous on `[0,T)`. -/
theorem primitive_props {a : ℝ → ℝ} {T : ℝ} (ha : ContinuousOn a (Ico 0 T)) :
    (∀ s ∈ Ico 0 T, ContinuousOn (fun t => ∫ x in (0:ℝ)..t, a x) (Icc 0 s)) ∧
    (∀ t ∈ Ioo 0 T, HasDerivAt (fun t => ∫ x in (0:ℝ)..t, a x) (a t) t) := by
  constructor
  · intro s hs
    have hsub : Icc 0 s ⊆ Ico 0 T := fun x hx => ⟨hx.1, hx.2.trans_lt hs.2⟩
    have hint : IntegrableOn a (uIcc 0 s) := by
      rw [uIcc_of_le hs.1]; exact (ha.mono hsub).integrableOn_Icc
    have h := intervalIntegral.continuousOn_primitive_interval hint
    rwa [uIcc_of_le hs.1] at h
  · intro t ht
    have hsub : uIcc 0 t ⊆ Ico 0 T := by
      rw [uIcc_of_le ht.1.le]
      intro x hx
      exact ⟨hx.1, hx.2.trans_lt ht.2⟩
    exact intervalIntegral.integral_hasDerivAt_right (ha.mono hsub).intervalIntegrable
      ((ha.mono Ioo_subset_Ico_self).stronglyMeasurableAtFilter isOpen_Ioo t ht)
      (ha.continuousAt (Ico_mem_nhds ht.1 ht.2))

/-! ## §6. Lemma 2 — scalar form (fully proved, in 3 steps as before) -/

theorem enstrophy_closure_scalar
    {ν β M K₁ K₂ K₂' K₃ T Λ : ℝ} {Y Y' D N ρ : ℝ → ℝ}
    (hν : 0 < ν) (hβ : β ∈ Icc (1/2 : ℝ) 1) (hM : 0 ≤ M)
    (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂)
    (hY0 : ∀ t, 0 ≤ Y t) (hD0 : ∀ t, 0 ≤ D t)
    (hρ : ∀ t ∈ Ico 0 T, 0 < ρ t)
    (hYc : ContinuousOn Y (Ico 0 T)) (hρc : ContinuousOn ρ (Ico 0 T))
    (hNc : ContinuousOn N (Ico 0 T))
    (hY' : ∀ t ∈ Ioo 0 T, HasDerivAt Y (Y' t) t)
    (hbal : ∀ t ∈ Ioo 0 T,
      Y' t ≤ -2 * ν * D t + 2 * stretchingBound K₁ K₂ K₂' K₃ M β ρ Y D N t)
    (hΛ : ∀ t ∈ Ico 0 T, ∫ s in (0:ℝ)..t, growthRate ν β K₁ K₂ K₂' K₃ M ρ Y N s ≤ Λ) :
    ∀ t ∈ Ico 0 T, Y t ≤ Y 0 * Real.exp Λ := by
  /- Step 0: exponents. -/
  have hθ0 : 0 < thetaD β := by unfold thetaD; linarith [hβ.2]
  have hθ1 : thetaD β < 1 := by unfold thetaD; linarith [hβ.1]
  have h1θ : (1 : ℝ) - thetaD β ≠ 0 := (sub_pos.mpr hθ1).ne'
  have hβpos : 0 < 1 + 2 * β := by linarith [hβ.1]
  have hq : 0 < qExp β := by unfold qExp; exact div_pos (by norm_num) hβpos
  have hqinv : (1 - thetaD β)⁻¹ = qExp β := by
    unfold thetaD qExp
    rw [show (1 : ℝ) - (3 - 2 * β) / 4 = (1 + 2 * β) / 4 by ring, inv_div]
  have hγ : gammaY β = 1/2 + (1 - thetaD β) := by unfold gammaY thetaD; ring
  have hγq : gammaY β * qExp β = 1 + qExp β / 2 := by
    rw [hγ, ← hqinv, add_mul, mul_inv_cancel₀ h1θ]; ring
  have h85 : (1 - (3 : ℝ) / 8)⁻¹ = 8 / 5 := by norm_num
  /- Step 1: Young (twice, each with ε = ν) + collecting terms ⇒ `Y' ≤ a(t) · Y`. -/
  have hbound : ∀ t ∈ Ioo 0 T,
      Y' t ≤ growthRate ν β K₁ K₂ K₂' K₃ M ρ Y N t * Y t := by
    intro t ht
    have hρt : 0 < ρ t := hρ t (Ioo_subset_Ico_self ht)
    have hYt : 0 ≤ Y t := hY0 t
    have hA : 0 ≤ 2 * K₁ * ρ t ^ (-β) :=
      mul_nonneg (mul_nonneg (by norm_num) hK₁) (Real.rpow_nonneg hρt.le _)
    have hYγ : 0 ≤ Y t ^ gammaY β := Real.rpow_nonneg hYt _
    have hB : 0 ≤ 2 * K₂ * M ^ ((1 : ℝ) / 2) :=
      mul_nonneg (mul_nonneg (by norm_num) hK₂) (Real.rpow_nonneg hM _)
    have hY78 : 0 ≤ Y t ^ ((7 : ℝ) / 8) := Real.rpow_nonneg hYt _
    -- Young 1: the High–High term, exponent θ = (3 − 2β)/4
    have hy1 := young_absorb hθ0 hθ1 hν (mul_nonneg hA hYγ) (hD0 t)
    rw [hqinv] at hy1
    -- Young 2: the High–Low term, exponent 3/8
    have hy2 := young_absorb (θ := (3 : ℝ) / 8) (by norm_num) (by norm_num) hν
      (mul_nonneg hB hY78) (hD0 t)
    rw [h85] at hy2
    -- (2K₁ρ^{-β} Y^γ)^q = (2K₁ρ^{-β})^q · Y^{q/2} · Y
    have hcq1 : (2 * K₁ * ρ t ^ (-β) * Y t ^ gammaY β) ^ qExp β
        = (2 * K₁ * ρ t ^ (-β)) ^ qExp β * Y t ^ (qExp β / 2) * Y t := by
      rw [Real.mul_rpow hA hYγ, ← Real.rpow_mul hYt, hγq,
        Real.rpow_add' hYt (by linarith : (0:ℝ) < 1 + qExp β / 2).ne', Real.rpow_one]
      ring
    -- (2K₂M^{1/2} Y^{7/8})^{8/5} = (2K₂M^{1/2})^{8/5} · Y^{2/5} · Y
    have hcq2 : (2 * K₂ * M ^ ((1 : ℝ) / 2) * Y t ^ ((7 : ℝ) / 8)) ^ ((8 : ℝ) / 5)
        = (2 * K₂ * M ^ ((1 : ℝ) / 2)) ^ ((8 : ℝ) / 5) * Y t ^ ((2 : ℝ) / 5) * Y t := by
      rw [Real.mul_rpow hB hY78, ← Real.rpow_mul hYt,
        show (7 : ℝ) / 8 * (8 / 5) = 1 + 2 / 5 by norm_num,
        Real.rpow_add' hYt (by norm_num : (1 : ℝ) + 2 / 5 ≠ 0), Real.rpow_one]
      ring
    have hb := hbal t ht
    simp only [stretchingBound] at hb
    have hexp : growthRate ν β K₁ K₂ K₂' K₃ M ρ Y N t * Y t
        = youngConst (thetaD β) ν * (2 * K₁ * ρ t ^ (-β) * Y t ^ gammaY β) ^ qExp β
          + youngConst ((3 : ℝ) / 8) ν
              * (2 * K₂ * M ^ ((1 : ℝ) / 2) * Y t ^ ((7 : ℝ) / 8)) ^ ((8 : ℝ) / 5)
          + 2 * (K₂' * M + K₃ * ρ t ^ (-(5 : ℝ) / 2) * N t) * Y t := by
      rw [hcq1, hcq2]; simp only [growthRate]; ring
    rw [hexp]
    linarith [hy1, hy2, hb]
  /- Step 2: continuity of the coefficient `a` on `[0,T)`. -/
  have hac : ContinuousOn (growthRate ν β K₁ K₂ K₂' K₃ M ρ Y N) (Ico 0 T) := by
    have h1 : ContinuousOn (fun t => ρ t ^ (-β)) (Ico 0 T) :=
      hρc.rpow_const (fun t ht => Or.inl (hρ t ht).ne')
    have h2 : ContinuousOn (fun t => (2 * K₁ * ρ t ^ (-β)) ^ qExp β) (Ico 0 T) :=
      (continuousOn_const.mul h1).rpow_const (fun _ _ => Or.inr hq.le)
    have h3 : ContinuousOn (fun t => Y t ^ (qExp β / 2)) (Ico 0 T) :=
      hYc.rpow_const (fun _ _ => Or.inr (by linarith))
    have h4 : ContinuousOn (fun t => ρ t ^ (-(5 : ℝ) / 2)) (Ico 0 T) :=
      hρc.rpow_const (fun t ht => Or.inl (hρ t ht).ne')
    have h6 : ContinuousOn (fun t => Y t ^ ((2 : ℝ) / 5)) (Ico 0 T) :=
      hYc.rpow_const (fun _ _ => Or.inr (by norm_num))
    have h5 : ContinuousOn (fun t =>
        youngConst (thetaD β) ν * (2 * K₁ * ρ t ^ (-β)) ^ qExp β * Y t ^ (qExp β / 2)
          + youngConst ((3 : ℝ) / 8) ν * (2 * K₂ * M ^ ((1 : ℝ) / 2)) ^ ((8 : ℝ) / 5)
              * Y t ^ ((2 : ℝ) / 5)
          + 2 * (K₂' * M + K₃ * ρ t ^ (-(5 : ℝ) / 2) * N t)) (Ico 0 T) :=
      (((continuousOn_const.mul h2).mul h3).add (continuousOn_const.mul h6)).add
        (continuousOn_const.mul (continuousOn_const.add ((continuousOn_const.mul h4).mul hNc)))
    exact h5
  /- Step 3: Grönwall with `A(t) = ∫₀ᵗ a`. -/
  obtain ⟨hAc, hA'⟩ := primitive_props hac
  have hG := gronwall_integrating_factor hYc hAc (by simp) hA' hY' hbound
  intro t ht
  calc Y t ≤ Y 0 * Real.exp (∫ s in (0:ℝ)..t, growthRate ν β K₁ K₂ K₂' K₃ M ρ Y N s) :=
        hG t ht
    _ ≤ Y 0 * Real.exp Λ :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (hΛ t ht)) (hY0 0)

/-! ## §7. The bridge: abstract framework ⇒ genuine solutions -/

/-- The analytic data that Lemma 1 needs, uniformly in time: at each `t < T` there is a
slice `NSFieldData` attached to `V.u t`, together with the 5 tool packages, with constants
bounded by `K₁, K₂, K₂', K₃` independently of `t`.

THIS IS AN ASSUMPTION. Note that it does not force `T_ρ` to be the near-field part of the
genuine Biot–Savart operator: it only asks for the existence of SOME splitting satisfying the
estimates. -/
structure Lemma1AnalyticInput (V : DivFreeH3Field) (M β : ℝ) (ρ : ℝ → ℝ) where
  K₁ : ℝ
  K₂ : ℝ
  K₂' : ℝ
  K₃ : ℝ
  hK : 0 ≤ K₁ ∧ 0 ≤ K₂ ∧ 0 ≤ K₂' ∧ 0 ≤ K₃
  slice : ∀ t ∈ Ico 0 V.T,
    ∃ d : NSFieldData E3 E3 (E3 →L[ℝ] E3) (E3 →L[ℝ] E3) volume,
    ∃ (hFar : FarFieldKernelBound d) (hAlign : VorticityAlignmentHyp d)
      (hCZ : CalderonZygmundBound d) (hHLS : HLSBound d) (hGN : GagliardoNirenberg3D d),
      d.u = V.u t ∧ d.ω = vort V.u t ∧ d.gradω = fderiv ℝ (vort V.u t) ∧
      d.M = M ∧ d.ρ = ρ t ∧ d.β = β ∧ d.S_total = stretching V.u t ∧
      nearHHConst d hAlign hHLS hGN ≤ K₁ ∧ nearHLConst d hCZ hGN ≤ K₂ ∧
      hCZ.C_CZ 2 ≤ K₂' ∧ hFar.K₃ ≤ K₃

/-- Turn `(w²)^γ, (g²)^θ, …` into `w^{3/2+β}, g^{3/2−β}, …`. -/
lemma bound_shape (K₁ K₂ K₂' K₃ M β r s w g U : ℝ) (hw : 0 ≤ w) (hg : 0 ≤ g) :
    K₁ * r * (w ^ 2) ^ gammaY β * (g ^ 2) ^ thetaD β
      + K₂ * M ^ ((1 : ℝ) / 2) * (w ^ 2) ^ ((7 : ℝ) / 8) * (g ^ 2) ^ ((3 : ℝ) / 8)
      + (K₂' * M + K₃ * s * U) * w ^ 2
    = K₁ * r * w ^ (3 / 2 + β) * g ^ (3 / 2 - β)
      + K₂ * M ^ ((1 : ℝ) / 2) * w ^ ((7 : ℝ) / 4) * g ^ ((3 : ℝ) / 4)
      + (K₂' * M + K₃ * s * U) * w ^ 2 := by
  rw [sq_rpow_eq hw, sq_rpow_eq hg, sq_rpow_eq hw, sq_rpow_eq hg,
    show 2 * gammaY β = 3 / 2 + β by unfold gammaY; ring,
    show 2 * thetaD β = 3 / 2 - β by unfold thetaD; ring,
    show (2 : ℝ) * (7 / 8) = 7 / 4 by norm_num,
    show (2 : ℝ) * (3 / 8) = 3 / 4 by norm_num]

/-- **Lemma 1 (for genuine solutions, NO `sorry`, conditional on `Lemma1AnalyticInput`).** -/
theorem lemma1_geometric_depletion (V : DivFreeH3Field) {M β : ℝ} {ρ : ℝ → ℝ}
    (I : Lemma1AnalyticInput V M β ρ) :
    ∀ t ∈ Ico 0 V.T, stretching V.u t ≤
      stretchingBound I.K₁ I.K₂ I.K₂' I.K₃ M β ρ (enstrophy V.u) (palinstrophy V.u)
        (energyNorm V.u) t := by
  intro t ht
  obtain ⟨d, hFar, hAlign, hCZ, hHLS, hGN, hu, hω, hg, hM, hρ, hβ, hS,
    hc1, hc2, hc3, hc4⟩ := I.slice t ht
  have hρt : 0 < ρ t := by rw [← hρ]; exact d.hρ
  have hMpos : 0 < M := by rw [← hM]; exact d.hM
  have hL := lemma1_near_far_depletion d hFar hAlign hCZ hHLS hGN
  rw [hu, hω, hg, hM, hρ, hβ, hS] at hL
  have hw0 : 0 ≤ rLpNorm volume 2 (vort V.u t) := rLpNorm_nonneg _ _ _
  have hg0 : 0 ≤ rLpNorm volume 2 (fderiv ℝ (vort V.u t)) := rLpNorm_nonneg _ _ _
  have hU0 : 0 ≤ rLpNorm volume 2 (V.u t) := rLpNorm_nonneg _ _ _
  have hX1 : 0 ≤ ρ t ^ (-β) * rLpNorm volume 2 (vort V.u t) ^ (3 / 2 + β)
      * rLpNorm volume 2 (fderiv ℝ (vort V.u t)) ^ (3 / 2 - β) := by positivity
  have hX2 : 0 ≤ M ^ ((1 : ℝ) / 2) * rLpNorm volume 2 (vort V.u t) ^ ((7 : ℝ) / 4)
      * rLpNorm volume 2 (fderiv ℝ (vort V.u t)) ^ ((3 : ℝ) / 4) := by positivity
  have hX3 : 0 ≤ M * rLpNorm volume 2 (vort V.u t) ^ 2 := by positivity
  have hX4 : 0 ≤ ρ t ^ (-(5 : ℝ) / 2) * rLpNorm volume 2 (V.u t)
      * rLpNorm volume 2 (vort V.u t) ^ 2 := by positivity
  have e1 := mul_le_mul_of_nonneg_right hc1 hX1
  have e2 := mul_le_mul_of_nonneg_right hc2 hX2
  have e3 := mul_le_mul_of_nonneg_right hc3 hX3
  have e4 := mul_le_mul_of_nonneg_right hc4 hX4
  have hshape := bound_shape I.K₁ I.K₂ I.K₂' I.K₃ M β (ρ t ^ (-β)) (ρ t ^ (-(5 : ℝ) / 2))
    (rLpNorm volume 2 (vort V.u t)) (rLpNorm volume 2 (fderiv ℝ (vort V.u t)))
    (rLpNorm volume 2 (V.u t)) hw0 hg0
  simp only [stretchingBound, enstrophy, palinstrophy, energyNorm, normL2]
  rw [hshape]
  linarith [le_abs_self (stretching V.u t), hL, e1, e2, e3, e4]

/-! ## §8. Lemma 2, Lemma 3 and the conditional regularity chain -/

/-- **Lemma 2 (closing the enstrophy inequality).** Fully proved. -/
theorem lemma2_enstrophy_bound (F : NSClassicalSolution)
    {β M K₁ K₂ K₂' K₃ Λ : ℝ} {ρ : ℝ → ℝ}
    (hβ : β ∈ Icc (1/2 : ℝ) 1) (hM : 0 ≤ M) (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂)
    (hρ : ∀ t ∈ Ico 0 F.T, 0 < ρ t) (hρc : ContinuousOn ρ (Ico 0 F.T))
    (hL1 : ∀ t ∈ Ico 0 F.T, stretching F.u t ≤
      stretchingBound K₁ K₂ K₂' K₃ M β ρ (enstrophy F.u) (palinstrophy F.u)
        (energyNorm F.u) t)
    (hΛ : ∀ t ∈ Ico 0 F.T, ∫ s in (0:ℝ)..t,
      growthRate F.ν β K₁ K₂ K₂' K₃ M ρ (enstrophy F.u) (energyNorm F.u) s ≤ Λ) :
    ∀ t ∈ Ico 0 F.T, enstrophy F.u t ≤ enstrophy F.u 0 * Real.exp Λ :=
  enstrophy_closure_scalar
    (Y := enstrophy F.u) (D := palinstrophy F.u) (N := energyNorm F.u)
    (Y' := fun t => -2 * F.ν * palinstrophy F.u t + 2 * stretching F.u t)
    F.ν_pos hβ hM hK₁ hK₂
    (fun t => by simp only [enstrophy]; positivity)
    (fun t => by simp only [palinstrophy]; positivity)
    hρ F.enstrophy_cont hρc F.energy_cont F.enstrophy_balance
    (fun t ht => by
      have h := hL1 t (Ioo_subset_Ico_self ht)
      show -2 * F.ν * palinstrophy F.u t + 2 * stretching F.u t ≤ _
      linarith)
    hΛ

/-! ### Lemma 3: tools and assumptions -/

/-- `‖∇²ω(t)‖²_{L²}`. -/
def hessSq (u : ℝ → E3 → E3) (t : ℝ) : ℝ :=
  normL2 (fun x => iteratedFDeriv ℝ 2 (vort u t) x) ^ 2

/-- AM–GM: `x^{1/4} ≤ x/4 + 3/4` for `x ≥ 0`. -/
lemma rpow_quarter_le (x : ℝ) (hx : 0 ≤ x) : x ^ (1/4 : ℝ) ≤ x / 4 + 3 / 4 := by
  have h := Real.geom_mean_le_arith_mean2_weighted (w₁ := 1/4) (w₂ := 3/4) (p₁ := x) (p₂ := 1)
    (by norm_num) (by norm_num) hx (by norm_num) (by norm_num)
  rw [Real.one_rpow, mul_one] at h
  linarith

/-- An `H²`-level bound for the vorticity (ASSUMPTION): the palinstrophy is bounded,
`ν∫‖∇²ω‖²` is bounded, together with the continuity/smoothness properties that classical
solutions have. -/
structure H2Bound (F : NSClassicalSolution) (E₂ : ℝ) : Prop where
  E₂_nonneg : 0 ≤ E₂
  pal_le : ∀ t ∈ Ico 0 F.T, palinstrophy F.u t ≤ E₂
  hess_cont : ContinuousOn (hessSq F.u) (Ico 0 F.T)
  hess_int_le : ∀ t ∈ Ico 0 F.T, F.ν * (∫ s in (0:ℝ)..t, hessSq F.u s) ≤ E₂
  bkm_cont : ContinuousOn (bkmIntegrand F.u) (Ico 0 F.T)
  vort_C2 : ∀ t ∈ Ico 0 F.T, ContDiff ℝ 2 (vort F.u t)

/-- Propagation of regularity (an ASSUMPTION; a classical theorem for classical solutions):
if the enstrophy is bounded on `[0,T)`, then there is an `H²`-level bound. This is a
higher-order energy estimate, for which Mathlib does not yet have the infrastructure. -/
def H2Propagation (F : NSClassicalSolution) : Prop :=
  ∀ E₁ : ℝ, (∀ t ∈ Ico 0 F.T, enstrophy F.u t ≤ E₁) → ∃ E₂ : ℝ, H2Bound F E₂

/-- **Lemma 3 (upgrading regularity → BKM).** NO `sorry`, conditional on `H2Propagation`.
Agmon at each time, then AM–GM `b^{1/2} = (b²)^{1/4} ≤ b²/4 + 3/4`, then integrate:
`∫₀ᵗ ‖ω‖_∞ ≤ C_Ag E₂^{1/4} (E₂/(4ν) + 3T/4)`. -/
theorem lemma3_bkm (F : NSClassicalSolution) {CAg E₁ : ℝ} (hCAg : 0 ≤ CAg)
    (hAg : AgmonInequality CAg) (hProp : H2Propagation F)
    (hE : ∀ t ∈ Ico 0 F.T, enstrophy F.u t ≤ E₁) :
    ∃ E₂ : ℝ, (∀ t ∈ Ico 0 F.T, palinstrophy F.u t ≤ E₂) ∧
      ∀ t ∈ Ico 0 F.T, IntervalIntegrable (bkmIntegrand F.u) volume 0 t ∧
        ∫ s in (0:ℝ)..t, bkmIntegrand F.u s
          ≤ CAg * E₂ ^ (1/4 : ℝ) * (E₂ / (4 * F.ν) + 3 * F.T / 4) := by
  obtain ⟨E₂, hP⟩ := hProp E₁ hE
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = CAg * E₂ ^ (1/4 : ℝ) := ⟨_, rfl⟩
  have hE' : 0 ≤ E₂ ^ (1/4 : ℝ) := Real.rpow_nonneg hP.E₂_nonneg _
  have hc0 : 0 ≤ c := by rw [hc]; exact mul_nonneg hCAg hE'
  -- Step 1: the pointwise-in-time bound ‖ω(s)‖_∞ ≤ c/4 · ‖∇²ω(s)‖² + 3c/4
  have hpt : ∀ s ∈ Ico 0 F.T,
      bkmIntegrand F.u s ≤ c / 4 * hessSq F.u s + 3 * c / 4 := by
    intro s hs
    have hA := hAg (vort F.u s) (hP.vort_C2 s hs) (F.memL2_vort s hs)
      (F.memL2_grad_vort s hs) (F.memL2_hess_vort s hs)
    have ha0 : 0 ≤ normL2 (fderiv ℝ (vort F.u s)) := rLpNorm_nonneg _ _ _
    have hb0 : 0 ≤ normL2 (fun x => iteratedFDeriv ℝ 2 (vort F.u s) x) :=
      rLpNorm_nonneg _ _ _
    have ha : normL2 (fderiv ℝ (vort F.u s)) ^ (1/2 : ℝ) ≤ E₂ ^ (1/4 : ℝ) := by
      have h1 : normL2 (fderiv ℝ (vort F.u s)) ^ (1/2 : ℝ)
          = (normL2 (fderiv ℝ (vort F.u s)) ^ 2) ^ (1/4 : ℝ) := by
        rw [sq_rpow_eq ha0]; norm_num
      rw [h1]
      exact Real.rpow_le_rpow (sq_nonneg _) (hP.pal_le s hs) (by norm_num)
    have hb : normL2 (fun x => iteratedFDeriv ℝ 2 (vort F.u s) x) ^ (1/2 : ℝ)
        ≤ hessSq F.u s / 4 + 3 / 4 := by
      have h1 : normL2 (fun x => iteratedFDeriv ℝ 2 (vort F.u s) x) ^ (1/2 : ℝ)
          = (normL2 (fun x => iteratedFDeriv ℝ 2 (vort F.u s) x) ^ 2) ^ (1/4 : ℝ) := by
        rw [sq_rpow_eq hb0]; norm_num
      rw [h1]
      exact rpow_quarter_le _ (sq_nonneg _)
    have hb' : 0 ≤ normL2 (fun x => iteratedFDeriv ℝ 2 (vort F.u s) x) ^ (1/2 : ℝ) :=
      Real.rpow_nonneg hb0 _
    calc bkmIntegrand F.u s
        ≤ CAg * normL2 (fderiv ℝ (vort F.u s)) ^ (1/2 : ℝ)
            * normL2 (fun x => iteratedFDeriv ℝ 2 (vort F.u s) x) ^ (1/2 : ℝ) := hA
      _ ≤ CAg * E₂ ^ (1/4 : ℝ)
            * normL2 (fun x => iteratedFDeriv ℝ 2 (vort F.u s) x) ^ (1/2 : ℝ) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ha hCAg) hb'
      _ ≤ CAg * E₂ ^ (1/4 : ℝ) * (hessSq F.u s / 4 + 3 / 4) :=
          mul_le_mul_of_nonneg_left hb (mul_nonneg hCAg hE')
      _ = c / 4 * hessSq F.u s + 3 * c / 4 := by rw [hc]; ring
  refine ⟨E₂, hP.pal_le, fun t ht => ?_⟩
  -- Step 2: integrability on [0, t] (t < T)
  have hsub : Icc 0 t ⊆ Ico 0 F.T := fun x hx => ⟨hx.1, hx.2.trans_lt ht.2⟩
  have hsubu : uIcc 0 t ⊆ Ico 0 F.T := by rw [uIcc_of_le ht.1]; exact hsub
  have hbkm_int : IntervalIntegrable (bkmIntegrand F.u) volume 0 t :=
    (hP.bkm_cont.mono hsubu).intervalIntegrable
  have hH_int : IntervalIntegrable (hessSq F.u) volume 0 t :=
    (hP.hess_cont.mono hsubu).intervalIntegrable
  have hcH : IntervalIntegrable (fun s => c / 4 * hessSq F.u s) volume 0 t :=
    hH_int.const_mul _
  have hconst : IntervalIntegrable (fun _ : ℝ => 3 * c / 4) volume 0 t :=
    intervalIntegrable_const
  have hg_int : IntervalIntegrable (fun s => c / 4 * hessSq F.u s + 3 * c / 4) volume 0 t :=
    hcH.add hconst
  refine ⟨hbkm_int, ?_⟩
  -- Step 3: integrate and bound
  have hmono := intervalIntegral.integral_mono_on ht.1 hbkm_int hg_int
    (fun s hs => hpt s (hsub hs))
  rw [intervalIntegral.integral_add hcH hconst, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const, smul_eq_mul, sub_zero] at hmono
  have hI : ∫ s in (0:ℝ)..t, hessSq F.u s ≤ E₂ / F.ν := by
    rw [le_div_iff₀ F.ν_pos]; linarith [hP.hess_int_le t ht]
  have h1 := mul_le_mul_of_nonneg_left hI (div_nonneg hc0 (by norm_num : (0:ℝ) ≤ 4))
  have h2 := mul_le_mul_of_nonneg_right ht.2.le
    (div_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 3) hc0) (by norm_num : (0:ℝ) ≤ 4))
  have hdiv : E₂ / (4 * F.ν) = E₂ / F.ν / 4 := by rw [div_div, mul_comm (4:ℝ) F.ν]
  rw [← hc, hdiv]
  linarith [hmono, h1, h2]

/-- **CONDITIONAL regularity (no `sorry`).** If there are analytic data `I` for Lemma 1,
`Λ_β(T) < ∞` with the constants of `I`, the Agmon inequality, `H²` propagation of regularity
and the BKM theorem, then the solution extends past `T`.
This is NOT a solution of the Millennium Problem: the hard part lies in `I` and `hΛ`. -/
theorem conditional_regularity (hBKM : BKMContinuation) {CAg : ℝ} (hCAg : 0 ≤ CAg)
    (hAg : AgmonInequality CAg) (F : NSClassicalSolution) (hProp : H2Propagation F)
    {β M : ℝ} {ρ : ℝ → ℝ}
    (hβ : β ∈ Icc (1/2 : ℝ) 1) (hM : 0 ≤ M)
    (hρ : ∀ t ∈ Ico 0 F.T, 0 < ρ t) (hρc : ContinuousOn ρ (Ico 0 F.T))
    (I : Lemma1AnalyticInput F.toDivFreeH3Field M β ρ)
    (hΛ : ∃ Λ : ℝ, ∀ t ∈ Ico 0 F.T, ∫ s in (0:ℝ)..t,
      growthRate F.ν β I.K₁ I.K₂ I.K₂' I.K₃ M ρ (enstrophy F.u) (energyNorm F.u) s ≤ Λ) :
    ∃ G : NSClassicalSolution, G.ν = F.ν ∧ F.T < G.T ∧ ∀ t ∈ Ico 0 F.T, G.u t = F.u t := by
  obtain ⟨hK₁, hK₂, -, -⟩ := I.hK
  obtain ⟨Λ, hΛ'⟩ := hΛ
  have hE := lemma2_enstrophy_bound F hβ hM hK₁ hK₂ hρ hρc
    (lemma1_geometric_depletion F.toDivFreeH3Field I) hΛ'
  obtain ⟨E₂, -, hbkm⟩ := lemma3_bkm F hCAg hAg hProp hE
  exact hBKM F ⟨_, hbkm⟩

end NavierStokes
