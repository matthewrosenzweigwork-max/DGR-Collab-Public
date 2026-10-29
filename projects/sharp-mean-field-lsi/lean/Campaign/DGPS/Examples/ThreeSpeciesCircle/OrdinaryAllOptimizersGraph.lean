import DGPS.Examples.ThreeSpeciesCircle.OrdinaryGlobalLocalization

/-!
# Every ordinary optimizer lies on the STR026 graph (packet STR028a)

For an ordinary optimizer `ρ` at parameter `h`, written in the chart of STR026 as
`ρ = rho α y` with `y = ((a, b, h, γ), w)` and `1 + γ = λ / (4π²)` (`λ` the optimal quotient):

* the weak Euler equation together with the bootstrap ODE gives the strong equation
  `u_tt + r u - 3h sin 3t u_t + ½ u_t² = r L` (`eul` is constant, `r = 1 + γ`);
* the multiplier identity `∫ ρ E = -κ/2` (integration by parts of the periodic flux `ρ u_t`)
  gives `κ = -2 r L`, hence `resid = 0` and `rangeMap α y = 0` (`sgv_single`);
* along `h_j → 0` with `γ_j → 0` (an explicit hypothesis `hγ`), the localization chart points
  (with their `γ`-coordinate reset to `γ_j`, which does not change `ρ`) enter the STR026
  neighbourhood and, by uniqueness there, satisfy `w_j = ψ (p_j)`
  (`ordinaryOptimizer_on_rangeGraph`).
-/

open MeasureTheory Filter Topology Function
open scoped ENNReal
open DGPS DGPS.Analysis.PeriodicHolder DGPS.Analysis.ComplementaryElliptic

namespace DGPS.Examples.ThreeSpeciesCircle

theorem sg_ode_real {h c lam Lz : ℝ} {u u1 u2 W A : ℝ → ℝ}
    (hu : ∀ t, HasDerivAt u (u1 t) t) (hu1 : ∀ t, HasDerivAt u1 (u2 t) t)
    (hW : ∀ t, 0 < W t)
    (hlog : ∀ t, Real.log (W t ^ 2) = h * Real.cos (6 * Real.pi * t) + u t - Lz)
    (hWd : ∀ t, HasDerivAt W ((A t + W t * sg0 h t) / 2) t)
    (hAd : ∀ t, HasDerivAt A (-(A t * sg0 h t) / 2 - lam *
      (W t * (fF W t - ellF h c t))) t) (t : ℝ) :
    u2 t + sg0 h t * u1 t + u1 t ^ 2 / 2 + lam * (u t - (Lz - c)) = 0 := by
  have hf := hasDerivAt_fF hWd hW t
  have hfe : fF W = fun t => ellF h c t + u t - (Lz - c) := by
    funext s
    simp only [fF, hlog s, ellF]; ring
  have hf2 : HasDerivAt (fun t => ellF h c t + u t - (Lz - c)) (sg0 h t + u1 t) t :=
    ((hasDerivAt_ellF h c t).add (hu t)).sub_const _
  rw [hfe] at hf
  have hv : vF A W t = u1 t := by
    have := hf.unique hf2
    linarith
  have hA : ∀ s, A s = W s * u1 s := by
    intro s
    have h1 : vF A W s = u1 s := by
      have hf' := hasDerivAt_fF hWd hW s
      rw [hfe] at hf'
      have := hf'.unique (((hasDerivAt_ellF h c s).add (hu s)).sub_const _)
      linarith
    unfold vF at h1
    have := (hW s).ne'
    field_simp at h1
    linarith
  have hAfun : A = fun s => W s * u1 s := funext hA
  have hd : HasDerivAt (fun s => W s * u1 s)
      ((A t + W t * sg0 h t) / 2 * u1 t + W t * u2 t) t := (hWd t).mul (hu1 t)
  rw [← hAfun] at hd
  have hq := hd.unique (hAd t)
  have hfl : fF W t - ellF h c t = u t - (Lz - c) := by
    rw [hfe]; ring
  rw [hfl, hA t] at hq
  have hWt := (hW t).ne'
  have : W t * (u2 t + sg0 h t * u1 t + u1 t ^ 2 / 2 + lam * (u t - (Lz - c))) = 0 := by
    linear_combination hq
  rcases mul_eq_zero.1 this with h0 | h0
  · exact absurd h0 hWt
  · exact h0

section Eval
variable {α : ℝ} [HolderExponent α]

theorem sgv_phi (y : Par × Wsp α) (s : ℝ) :
    (phiCLM y).val s = y.1 2 * Real.cos (6 * Real.pi * s) + (uCLM y).val s := by
  simp only [phiCLM, add_apply, ContinuousLinearMap.smulRight_apply, pc_apply,
    u0CLM, ContinuousLinearMap.comp_apply, PH.val_add, PH.val_smul, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, incl2_val, cos3, PH.val_trig, trigFun]
  push_cast
  ring_nf

theorem sgv_Du (y : Par × Wsp α) (s : ℝ) :
    (DuCLM y).val s = (2 * Real.pi)⁻¹ * deriv (uCLM y).val s := by
  simp [DuCLM]

theorem sgv_D2u (y : Par × Wsp α) (s : ℝ) :
    (D2uCLM y).val s = kappa⁻¹ * deriv (deriv (uCLM y).val) s := by
  simp [D2uCLM]

theorem sgv_u0 (y : Par × Wsp α) (s : ℝ) : (u0CLM y).val s = (uCLM y).val s := rfl

theorem sgv_sin3 (s : ℝ) : (sin3 (α := α)).val s = Real.sin (6 * Real.pi * s) := by
  simp only [sin3, PH.val_trig, trigFun]
  push_cast
  ring_nf

theorem sgv_rho (y : Par × Wsp α) (s : ℝ) :
    (rho α y).val s = (∫ x in (0 : ℝ)..1, Real.exp ((phiCLM y).val x))⁻¹ *
      Real.exp ((phiCLM y).val s) := by
  unfold rho PH.normMap
  rw [PH.val_smul, Pi.smul_apply, smul_eq_mul, PH.integral_apply]
  simp only [PH.expMap_val]

theorem sgv_Z_pos (y : Par × Wsp α) : 0 < ∫ x in (0 : ℝ)..1, Real.exp ((phiCLM y).val x) := by
  have := PH.integral_expMap_pos (phiCLM y)
  rw [PH.integral_apply] at this
  simpa [PH.expMap_val] using this

theorem sgv_rho_pos (y : Par × Wsp α) (s : ℝ) : 0 < (rho α y).val s := by
  rw [sgv_rho]; exact mul_pos (inv_pos.2 (sgv_Z_pos y)) (Real.exp_pos _)

theorem sgv_eul (y : Par × Wsp α) (s : ℝ) :
    (eul α y).val s = kappa⁻¹ * (deriv (deriv (uCLM y).val) s +
      sg0 (y.1 2) s * deriv (uCLM y).val s + deriv (uCLM y).val s ^ 2 / 2) +
      (1 + y.1 3) * (uCLM y).val s := by
  simp only [eul, PH.val_add, PH.val_sub, PH.val_smul, PH.val_mul, Pi.add_apply, Pi.sub_apply,
    Pi.smul_apply, Pi.mul_apply, smul_eq_mul, sgv_D2u, sgv_Du, sgv_u0, sgv_sin3, sg0, kappa]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

theorem sgv_integral_rho (y : Par × Wsp α) : ∫ s in (0 : ℝ)..1, (rho α y).val s = 1 := by
  simp only [sgv_rho]
  rw [intervalIntegral.integral_const_mul]
  exact inv_mul_cancel₀ (sgv_Z_pos y).ne'

/-- The multiplier identity: `∫ρ E = -κ/2`. -/
theorem sgv_multiplier (y : Par × Wsp α) :
    ∫ s in (0 : ℝ)..1, (rho α y).val s * (eul α y).val s = -(kap α y) / 2 := by
  have hpu : IsPH α 2 (uCLM y).val := (uCLM y).isPH
  set u := (uCLM y).val with hu
  have hu1 : ∀ s, HasDerivAt u (deriv u s) s := fun s => (hpu.2.1 s).hasDerivAt
  have hu2 : ∀ s, HasDerivAt (deriv u) (deriv (deriv u) s) s :=
    fun s => (hpu.2.2.2.1 s).hasDerivAt
  have hcu : Continuous u := hpu.continuous
  have hcu1 : Continuous (deriv u) := hpu.2.2.continuous
  have hcu2 : Continuous (deriv (deriv u)) := (isPH_deriv_deriv hpu).continuous
  have hcρ : Continuous (rho α y).val := (rho α y).isPH.continuous
  have hσc : Continuous (sg0 (y.1 2)) := by unfold sg0; fun_prop
  have hρd : ∀ s, HasDerivAt (rho α y).val
      ((rho α y).val s * (sg0 (y.1 2) s + deriv u s)) s := by
    intro s
    have h1 : HasDerivAt (fun x => ellF (y.1 2) 0 x + u x) (sg0 (y.1 2) s + deriv u s) s :=
      (hasDerivAt_ellF (y.1 2) 0 s).add (hu1 s)
    have h2 := (h1.exp).const_mul (∫ x in (0 : ℝ)..1, Real.exp ((phiCLM y).val x))⁻¹
    have e : (rho α y).val = fun x => (∫ x in (0 : ℝ)..1, Real.exp ((phiCLM y).val x))⁻¹ *
        Real.exp (ellF (y.1 2) 0 x + u x) := by
      funext x; rw [sgv_rho, sgv_phi]; simp [ellF, hu]
    rw [e]
    refine h2.congr_deriv ?_
    rw [← e]
    rw [sgv_rho, sgv_phi]
    simp [ellF, hu]
    ring
  set D : ℝ → ℝ := fun s => (rho α y).val s * deriv u s with hD
  set D' : ℝ → ℝ := fun s => (rho α y).val s * (sg0 (y.1 2) s + deriv u s) * deriv u s +
    (rho α y).val s * deriv (deriv u) s with hD'
  have hDd : ∀ s, HasDerivAt D (D' s) s := fun s =>
    ((hρd s).mul (hu2 s)).congr_deriv (by simp [hD'])
  have hcD' : Continuous D' := by
    simp only [hD']
    exact ((hcρ.mul (hσc.add hcu1)).mul hcu1).add (hcρ.mul hcu2)
  have hper : D 1 = D 0 := by
    have h1 := (rho α y).isPH.periodic 0
    have h2 := hpu.2.2.1 0
    simp only [zero_add] at h1 h2
    simp only [hD, h1, h2]
  have hI0 : ∫ s in (0 : ℝ)..1, D' s = 0 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hDd s)
      (hcD'.intervalIntegrable _ _), hper, sub_self]
  set γ1 : ℝ := 1 + y.1 3 with hγ1
  have hpt : ∀ s, (rho α y).val s * (eul α y).val s =
      kappa⁻¹ * D' s + (-(kappa⁻¹ / 2)) * ((rho α y).val s * deriv u s ^ 2) +
        γ1 * ((rho α y).val s * u s) := by
    intro s
    rw [sgv_eul]
    simp only [hD']
    ring
  have hc1 : Continuous fun s => (rho α y).val s * deriv u s ^ 2 := hcρ.mul (hcu1.pow 2)
  have hc2 : Continuous fun s => (rho α y).val s * u s := hcρ.mul hcu
  have hA1 : Continuous (fun s => kappa⁻¹ * D' s) := continuous_const.mul hcD'
  have hA2 : Continuous (fun s => (-(kappa⁻¹ / 2)) * ((rho α y).val s * deriv u s ^ 2)) :=
    continuous_const.mul hc1
  have hA3 : Continuous (fun s => γ1 * ((rho α y).val s * u s)) := continuous_const.mul hc2
  have hint : ∫ s in (0 : ℝ)..1, (rho α y).val s * (eul α y).val s =
      kappa⁻¹ * (∫ s in (0 : ℝ)..1, D' s) + (-(kappa⁻¹ / 2)) *
        (∫ s in (0 : ℝ)..1, (rho α y).val s * deriv u s ^ 2) +
        γ1 * (∫ s in (0 : ℝ)..1, (rho α y).val s * u s) := by
    simp only [hpt]
    have hI12 : IntervalIntegrable (fun s => kappa⁻¹ * D' s + (-(kappa⁻¹ / 2)) * ((rho α y).val s * deriv u s ^ 2)) MeasureTheory.volume 0 1 := (hA1.add hA2).intervalIntegrable 0 1
    rw [intervalIntegral.integral_add hI12 (hA3.intervalIntegrable 0 1),
      intervalIntegral.integral_add (hA1.intervalIntegrable 0 1) (hA2.intervalIntegrable 0 1),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
  rw [hint, hI0]
  have hk : kap α y = kappa⁻¹ * (∫ s in (0 : ℝ)..1, (rho α y).val s * deriv u s ^ 2) -
      2 * γ1 * (∫ s in (0 : ℝ)..1, (rho α y).val s * u s) := by
    have e1 : ∫ x in (0 : ℝ)..1, (rho α y * (DuCLM y * DuCLM y)).val x =
        kappa⁻¹ * ∫ s in (0 : ℝ)..1, (rho α y).val s * deriv u s ^ 2 := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr (fun s _ => ?_)
      simp only [PH.val_mul, Pi.mul_apply, sgv_Du, kappa]
      have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
      field_simp
      rfl
    have e2 : ∫ x in (0 : ℝ)..1, (rho α y * u0CLM y).val x =
        ∫ s in (0 : ℝ)..1, (rho α y).val s * u s := by
      refine intervalIntegral.integral_congr (fun s _ => ?_)
      simp only [PH.val_mul, Pi.mul_apply, sgv_u0]
      rfl
    unfold kap
    rw [PH.integral_apply, PH.integral_apply, e1, e2]
  rw [hk]
  ring

theorem sgv_torus_lift {g : ℝ → ℝ} (hc : Continuous g) (hp : Periodic g 1) :
    ∃ G : Torus 1 → ℝ, Continuous G ∧ ∀ s, G (pt s) = g s := by
  let F : UnitAddCircle → ℝ := hp.lift
  have hF : Continuous F := by
    have := (QuotientAddGroup.isQuotientMap_mk (AddSubgroup.zmultiples (1:ℝ))).continuous_iff
      (g := F)
    refine this.2 ?_
    have e : F ∘ (QuotientAddGroup.mk : ℝ → ℝ ⧸ AddSubgroup.zmultiples (1:ℝ)) = g := by
      funext s; exact hp.lift_coe s
    rw [e]; exact hc
  exact ⟨fun x => F (x 0), hF.comp (continuous_apply 0), fun s => hp.lift_coe s⟩

theorem sgv_abs_sqrt_sub_one {g : ℝ} (hg : 0 ≤ g) : |Real.sqrt g - 1| ≤ |g - 1| := by
  have h1 : g - 1 = (Real.sqrt g - 1) * (Real.sqrt g + 1) := by
    nlinarith [Real.sq_sqrt hg]
  have h2 : 1 ≤ Real.sqrt g + 1 := by linarith [Real.sqrt_nonneg g]
  rw [h1, abs_mul, abs_of_nonneg (by linarith : 0 ≤ Real.sqrt g + 1)]
  nlinarith [abs_nonneg (Real.sqrt g - 1)]

/-- A chart point whose density is an ordinary optimizer solves the strong equation:
the Euler expression is constant, `κ = -2 r L`, the residual vanishes and `rangeMap = 0`. -/
theorem sgv_single (h : ℝ) (ρ : AbsoluteDensity 1) (hpos : 0 < ordinaryEntropy h ρ)
    (hmin : ∀ ρ' : AbsoluteDensity 1, 0 < ordinaryEntropy h ρ' →
      str025_quot h ρ ≤ str025_quot h ρ')
    (y : Par × Wsp α) (hy2 : y.1 2 = h)
    (hlam : 1 + y.1 3 = (str025_quot h ρ).toReal / (4 * Real.pi ^ 2))
    (hae : ∀ᵐ x ∂haar 1, ∀ s : ℝ, torusLift (fun _ => s) = x → ρ.density x = (rho α y).val s)
    (hsmall : ∀ s, |(rho α y).val s - 1| ≤ 1 / 2) (hS1 : 6 * Real.pi * |h| ≤ 1) :
    ∃ L : ℝ, eul α y = ((1 + y.1 3) * L) • (1 : PH α 0) ∧
      kap α y = -2 * ((1 + y.1 3) * L) ∧ resid α y = 0 ∧ rangeMap α y = 0 := by
  obtain ⟨G, hGc, hG⟩ := sgv_torus_lift (rho α y).isPH.continuous (rho α y).isPH.periodic
  have hGb : ∀ x, |G x - 1| ≤ 1 / 2 := fun x => by
    obtain ⟨t, rfl⟩ := bs_exists_pt x
    rw [hG]; exact hsmall t
  have hGnn : ∀ x, 0 ≤ G x := fun x => by
    have := hGb x
    rw [abs_le] at this; linarith
  have hGpos : ∀ x, 0 < G x := fun x => by
    have := hGb x
    rw [abs_le] at this; linarith
  have hWc : Continuous (fun z => Real.sqrt (G z)) := Real.continuous_sqrt.comp hGc
  have hae' : (fun z => Real.sqrt (G z)) =ᵐ[haar 1] ρ.sqrt := by
    filter_upwards [hae, ρ.sqrt_nonneg] with x hx hnn
    obtain ⟨t, rfl⟩ := bs_exists_pt x
    have h1 := hx t rfl
    have hnn' : 0 ≤ ρ.sqrt (pt t) := hnn
    show Real.sqrt (G (pt t)) = ρ.sqrt (pt t)
    rw [hG, ← h1]
    exact Real.sqrt_sq hnn'
  have hδ : ∀ x, |Real.sqrt (G x) - 1| ≤ 1 / 2 := fun x =>
    (sgv_abs_sqrt_sub_one (hGnn x)).trans (hGb x)
  obtain ⟨Ac, hAc, hWd, hAd, -⟩ := bootstrap_single h ρ hpos hmin hWc hae' le_rfl hδ hS1
  have hWsq : ∀ s, Real.sqrt (G (pt s)) ^ 2 = (rho α y).val s := fun s => by
    rw [Real.sq_sqrt (hGnn _), hG]
  have hpu : IsPH α 2 (uCLM y).val := (uCLM y).isPH
  have hu1 : ∀ s, HasDerivAt (uCLM y).val (deriv (uCLM y).val s) s :=
    fun s => (hpu.2.1 s).hasDerivAt
  have hu2 : ∀ s, HasDerivAt (deriv (uCLM y).val) (deriv (deriv (uCLM y).val) s) s :=
    fun s => (hpu.2.2.2.1 s).hasDerivAt
  set Z : ℝ := ∫ x in (0 : ℝ)..1, Real.exp ((phiCLM y).val x) with hZ
  have hlog : ∀ t, Real.log (Real.sqrt (G (pt t)) ^ 2) =
      h * Real.cos (6 * Real.pi * t) + (uCLM y).val t - Real.log Z := fun t => by
    rw [hWsq, sgv_rho, sgv_phi, hy2, Real.log_mul (inv_ne_zero (sgv_Z_pos y).ne')
      (Real.exp_pos _).ne', Real.log_inv, Real.log_exp]
    ring
  have hode := fun t => sg_ode_real (h := h) (c := Real.log (besselI 0 h))
    (lam := (str025_quot h ρ).toReal) (Lz := Real.log Z) (u := (uCLM y).val)
    (u1 := deriv (uCLM y).val) (u2 := deriv (deriv (uCLM y).val))
    (W := fun s => Real.sqrt (G (pt s))) (A := fun s => Ac (pt s)) hu1 hu2
    (fun s => Real.sqrt_pos.2 (hGpos _)) hlog hWd hAd t
  have hl : (str025_quot h ρ).toReal = 4 * Real.pi ^ 2 * (1 + y.1 3) := by
    rw [hlam]; field_simp
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  refine ⟨Real.log Z - Real.log (besselI 0 h), ?_⟩
  have heul : ∀ s, (eul α y).val s =
      (1 + y.1 3) * (Real.log Z - Real.log (besselI 0 h)) := fun s => by
    rw [sgv_eul, hy2]
    have h1 := hode s
    rw [hl] at h1
    have e : deriv (deriv (uCLM y).val) s + sg0 h s * deriv (uCLM y).val s +
        deriv (uCLM y).val s ^ 2 / 2 = -(4 * Real.pi ^ 2 * (1 + y.1 3) *
          ((uCLM y).val s - (Real.log Z - Real.log (besselI 0 h)))) := by linarith
    rw [e]
    simp only [kappa]
    field_simp
    ring
  have heulPH : eul α y = ((1 + y.1 3) * (Real.log Z - Real.log (besselI 0 h))) •
      (1 : PH α 0) := by
    refine PH.ext (funext fun s => ?_)
    simp only [PH.val_smul, Pi.smul_apply, PH.val_one, Pi.one_apply, smul_eq_mul, mul_one]
    exact heul s
  have hmul := sgv_multiplier y
  have hint : ∫ s in (0 : ℝ)..1, (rho α y).val s * (eul α y).val s =
      (1 + y.1 3) * (Real.log Z - Real.log (besselI 0 h)) := by
    simp only [heul]
    rw [intervalIntegral.integral_mul_const, sgv_integral_rho, one_mul]
  have hk : kap α y = -2 * ((1 + y.1 3) * (Real.log Z - Real.log (besselI 0 h))) := by
    rw [hint] at hmul; linarith
  have hres : resid α y = 0 := by
    refine PH.ext (funext fun s => ?_)
    simp only [resid, PH.val_add, PH.val_smul, Pi.add_apply, Pi.smul_apply, PH.val_one,
      Pi.one_apply, smul_eq_mul, mul_one, PH.val_zero, Pi.zero_apply]
    rw [heul, hk]; ring
  refine ⟨heulPH, hk, hres, ?_⟩
  unfold rangeMap
  rw [hres, mul_zero, map_zero, smul_zero]

theorem sgv_rho_update (p : Par) (g : ℝ) (w : Wsp α) :
    rho α (Function.update p 3 g, w) = rho α (p, w) := by
  have h1 : phiCLM (Function.update p 3 g, w) = phiCLM (p, w) := by
    simp only [phiCLM, uCLM, u0CLM, pc, add_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd']
    simp
  unfold rho
  rw [h1]

theorem sgv_abs_le_norm (f : PH α 0) (s : ℝ) : |f.val s| ≤ ‖f‖ :=
  (f.isPH.bdd.abs_le_supNorm s).trans (supNorm_le_phNorm 0 f.val)

/-- **Every ordinary optimizer lies on the STR026 graph.**  For optimizers `ρ_j` of the ordinary
quotient at `h_j → 0`, whose multipliers satisfy `γ_j = λ_j / (4π²) - 1 → 0` (hypothesis `hγ`),
there are chart points `x_j → 0` representing `ρ_j` (with `r = 1 + γ_j`), such that eventually
`x_j` solves the strong equation (`eul` constant, `resid = 0`), `rangeMap x_j = 0`,
`x_j` lies in the STR026 neighbourhood, and `w_j = ψ (p_j)`. -/
theorem ordinaryOptimizer_on_rangeGraph (h : ℕ → ℝ) (hh : Tendsto h atTop (𝓝 0))
    (ρ : ℕ → AbsoluteDensity 1)
    (hpos : ∀ j, 0 < ordinaryEntropy (h j) (ρ j))
    (hmin : ∀ j, ∀ ρ' : AbsoluteDensity 1, 0 < ordinaryEntropy (h j) ρ' →
      ordinaryFisher (h j) (ρ j) / (2 * ordinaryEntropy (h j) (ρ j)) ≤
        ordinaryFisher (h j) ρ' / (2 * ordinaryEntropy (h j) ρ'))
    (hγ : Tendsto (fun j => (str025_quot (h j) (ρ j)).toReal / (4 * Real.pi ^ 2) - 1)
      atTop (𝓝 0))
    (α : ℝ) [HolderExponent α] (k : ℕ) (hk : 1 ≤ k) :
    ∃ (U : Set Par) (Wn : Set (Wsp α)) (ψ : Par → Wsp α) (x : ℕ → Par × Wsp α),
      IsOpen U ∧ (0 : Par) ∈ U ∧ IsOpen Wn ∧ (0 : Wsp α) ∈ Wn ∧ ψ 0 = 0 ∧ ContDiffOn ℝ k ψ U ∧
      (∀ p ∈ U, ψ p ∈ Wn ∧ rangeMap α (p, ψ p) = 0) ∧
      (∀ p ∈ U, ∀ w ∈ Wn, rangeMap α (p, w) = 0 → w = ψ p) ∧
      Tendsto x atTop (𝓝 0) ∧
      (∀ j, (x j).1 2 = h j ∧ 1 + (x j).1 3 = (str025_quot (h j) (ρ j)).toReal / (4 * Real.pi ^ 2)) ∧
      (∀ᶠ j in atTop, ∀ᵐ y ∂haar 1, ∀ s : ℝ, torusLift (fun _ => s) = y →
        (ρ j).density y = (rho α (x j)).val s) ∧
      ∀ᶠ j in atTop, (x j).1 ∈ U ∧ (x j).2 ∈ Wn ∧
        (∃ L : ℝ, eul α (x j) = ((1 + (x j).1 3) * L) • (1 : PH α 0)) ∧
        resid α (x j) = 0 ∧ rangeMap α (x j) = 0 ∧ (x j).2 = ψ (x j).1 := by
  obtain ⟨-, hloc⟩ := ordinaryOptimizer_globalLocalization h hh ρ hpos hmin
  obtain ⟨x, hx0, hxh, hxae⟩ := hloc α
  obtain ⟨-, -, -, -, hex⟩ := threefold_range_equation_invertible (α := α)
  obtain ⟨U, hU, h0U, Wn, hWn, h0W, ψ, hψ0, hψmem, huniq, hcd, -⟩ := hex k hk
  set γ : ℕ → ℝ := fun j => (str025_quot (h j) (ρ j)).toReal / (4 * Real.pi ^ 2) - 1 with hγdef
  set x' : ℕ → Par × Wsp α := fun j => (Function.update (x j).1 3 (γ j), (x j).2) with hx'
  have hx1 : Tendsto (fun j => (x j).1) atTop (𝓝 0) := (continuous_fst.tendsto _).comp hx0
  have hx2 : Tendsto (fun j => (x j).2) atTop (𝓝 0) := (continuous_snd.tendsto _).comp hx0
  have hp' : Tendsto (fun j => Function.update (x j).1 3 (γ j)) atTop (𝓝 0) := by
    rw [tendsto_pi_nhds]
    intro i
    by_cases hi : i = 3
    · subst hi
      simpa using hγ
    · simp only [Function.update_of_ne hi]
      exact (tendsto_pi_nhds.1 hx1) i
  have hx'0 : Tendsto x' atTop (𝓝 0) := by
    exact hp'.prodMk_nhds hx2
  have hrho : Tendsto (fun j => rho α (x' j)) atTop (𝓝 1) := by
    have := ((contDiff_rho (α := α) 0).continuous.tendsto 0).comp hx'0
    rwa [rho_zero] at this
  have hsm : ∀ᶠ j in atTop, ∀ s, |(rho α (x' j)).val s - 1| ≤ 1 / 2 := by
    filter_upwards [Metric.tendsto_nhds.1 hrho (1 / 2) (by norm_num)] with j hj s
    have h1 := sgv_abs_le_norm (rho α (x' j) - 1) s
    rw [dist_eq_norm] at hj
    simpa using h1.trans hj.le
  have hS : ∀ᶠ j in atTop, 6 * Real.pi * |h j| ≤ 1 := by
    have h1 : Tendsto (fun j => 6 * Real.pi * |h j|) atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds (x := 6 * Real.pi)).mul hh.abs
    exact (tendsto_order.1 h1).2 1 one_pos |>.mono fun j hj => hj.le
  have hmem : ∀ᶠ j in atTop, x' j ∈ U ×ˢ Wn :=
    hx'0 ((hU.prod hWn).mem_nhds ⟨h0U, h0W⟩)
  have hy2 : ∀ j, (x' j).1 2 = h j := fun j => by
    simp only [hx', Function.update_of_ne (show (2 : Fin 4) ≠ 3 by decide)]
    exact (hxh j).1
  have hlam : ∀ j, 1 + (x' j).1 3 = (str025_quot (h j) (ρ j)).toReal / (4 * Real.pi ^ 2) :=
    fun j => by simp [hx', hγdef]
  have hae : ∀ᶠ j in atTop, ∀ᵐ y ∂haar 1, ∀ s : ℝ, torusLift (fun _ => s) = y →
      (ρ j).density y = (rho α (x' j)).val s := by
    filter_upwards [hxae] with j hj
    have e : rho α (x' j) = rho α (x j) := by
      have := sgv_rho_update (α := α) (x j).1 (γ j) (x j).2
      simpa [hx'] using this
    rw [e]; exact hj
  have hfin : ∀ᶠ j in atTop, ∃ L : ℝ, eul α (x' j) = ((1 + (x' j).1 3) * L) • (1 : PH α 0) ∧
      resid α (x' j) = 0 ∧ rangeMap α (x' j) = 0 := by
    filter_upwards [hae, hsm, hS] with j hj1 hj2 hj3
    obtain ⟨L, h1, -, h3, h4⟩ := sgv_single (h j) (ρ j) (hpos j)
      (fun ρ' hρ' => hmin j ρ' hρ') (x' j) (hy2 j) (hlam j) hj1 hj2 hj3
    exact ⟨L, h1, h3, h4⟩
  refine ⟨U, Wn, ψ, x', hU, h0U, hWn, h0W, hψ0, hcd, hψmem, huniq, hx'0,
    fun j => ⟨hy2 j, hlam j⟩, hae, ?_⟩
  filter_upwards [hmem, hfin] with j hj1 ⟨L, hL1, hL2, hL3⟩
  exact ⟨hj1.1, hj1.2, ⟨L, hL1⟩, hL2, hL3, huniq _ hj1.1 _ hj1.2 hL3⟩

end Eval
end DGPS.Examples.ThreeSpeciesCircle
