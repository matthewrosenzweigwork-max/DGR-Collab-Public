import DGPS.Examples.ThreeSpeciesCircle.OrdinaryGammaLower
import DGPS.Examples.ThreeSpeciesCircle.OrdinaryJetExpansion

/-!
# STR028-b3: all-optimizer scaling and the three minima

Final stage of packet STR028.  For ordinary optimizers `ρ_j` at `h_j → 0` (a sequence of positive
entropy global minimizers of the ordinary quotient), represented in the STR026 chart by points
`x_j = ((a_j, b_j, h_j, γ_j), w_j) → 0`:

* `sgv_single_phi_STR028b3`: the explicit Euler constant `L = log Z - log I₀(h)` gives
  `Phi x_j = 0` (with `Z₀(h) = I₀(h)`), in addition to `resid = 0`, `rangeMap = 0`;
* `chart_radius_pos_STR028b3`: `R0 > 0` (the zero-amplitude chart point is the reference
  measure, which has zero entropy);
* the reduced identity: transfer from `Xp p` to `(p, ψ p)` (`transfer_STR028b1`,
  `nu4_le_STR028b1`) and the jet expansion `phi_jet_expansion_STR028b2` give
  `-γ/2 - (9/20)h² - h q/12 + R0²/48 + E = 0` with the remainder class of `allOptimizers_core`;
* `TrialState.allOptimizers_trial` (which wraps `allOptimizers_core` and the explicit trial
  state) then gives `|γ| + R0² ≤ 192 h²`, `|h|/2 < R0` and the three-minima alternative.
-/

open MeasureTheory Filter Topology
open scoped ENNReal
open DGPS DGPS.Analysis.PeriodicHolder DGPS.Analysis.ComplementaryElliptic

namespace DGPS.Examples.ThreeSpeciesCircle

section Main
variable {α : ℝ} [HolderExponent α]

theorem integral_exp_cos_STR028b3 (h : ℝ) :
    ∫ x in (0 : ℝ)..1, Real.exp (h * Real.cos (6 * Real.pi * x)) = besselI 0 h := by
  rw [← integral_unit_threePeriods 0 h]
  refine intervalIntegral.integral_congr (fun x _ => ?_)
  have e : 2 * Real.pi * 3 * x = 6 * Real.pi * x := by ring
  simp only [Nat.cast_zero, mul_zero, zero_mul, Real.cos_zero, mul_one, e]

theorem Z0_eq_bessel_STR028b3 (h : ℝ) : Z0_STR028b1 (α := α) h = besselI 0 h := by
  rw [Z0_eq_STR028b2, integral_exp_cos_STR028b3]

theorem ZV_eq_STR028b3 (y : Par × Wsp α) :
    ZV_STR028b1 y = ∫ x in (0 : ℝ)..1, Real.exp ((phiCLM y).val x) := by
  unfold ZV_STR028b1 eV_STR028b1
  rw [PH.integral_apply]
  simp only [PH.expMap_val]

/-- A chart point whose density is an ordinary optimizer solves the strong equation with the
explicit Euler constant `L = log Z - log I₀(h)`: `κ = -2 r L`, hence `Phi = 0`, the residual
vanishes and `rangeMap = 0`.  (This repeats the proof of `sgv_single`, whose existential `L` does
not record the value of the constant.) -/
theorem sgv_single_phi_STR028b3 (h : ℝ) (ρ : AbsoluteDensity 1) (hpos : 0 < ordinaryEntropy h ρ)
    (hmin : ∀ ρ' : AbsoluteDensity 1, 0 < ordinaryEntropy h ρ' →
      str025_quot h ρ ≤ str025_quot h ρ')
    (y : Par × Wsp α) (hy2 : y.1 2 = h)
    (hlam : 1 + y.1 3 = (str025_quot h ρ).toReal / (4 * Real.pi ^ 2))
    (hae : ∀ᵐ x ∂haar 1, ∀ s : ℝ, torusLift (fun _ => s) = x → ρ.density x = (rho α y).val s)
    (hsmall : ∀ s, |(rho α y).val s - 1| ≤ 1 / 2) (hS1 : 6 * Real.pi * |h| ≤ 1) :
    Phi_STR028b1 y = 0 ∧ resid α y = 0 ∧ rangeMap α y = 0 := by
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
  have hPhi : Phi_STR028b1 y = 0 := by
    unfold Phi_STR028b1
    rw [hk, ZV_eq_STR028b3, ← hZ, hy2, Z0_eq_bessel_STR028b3]
    ring
  refine ⟨hPhi, hres, ?_⟩
  unfold rangeMap
  rw [hres, mul_zero, map_zero, smul_zero]

/-- The zero-amplitude chart point represents the reference measure, which has zero entropy. -/
theorem entropy_zero_of_ab_zero_STR028b3 (h : ℝ) (ρ : AbsoluteDensity 1) (y : Par × Wsp α)
    (hy2 : y.1 2 = h) (h0 : y.1 0 = 0) (h1 : y.1 1 = 0) (hw : y.2 = 0)
    (hae : ∀ᵐ x ∂haar 1, ∀ s : ℝ, torusLift (fun _ => s) = x → ρ.density x = (rho α y).val s) :
    ordinaryEntropy h ρ = 0 := by
  obtain ⟨p, w⟩ := y
  simp only at hy2 h0 h1 hw
  subst hw
  have hu : uCLM ((p, (0 : Wsp α)) : Par × Wsp α) = 0 := uCLM_ab_zero_STR028b1 p h0 h1
  have hphi : ∀ s, (phiCLM ((p, (0 : Wsp α)) : Par × Wsp α)).val s =
      h * Real.cos (6 * Real.pi * s) := fun s => by
    rw [sgv_phi, hu]; simp [hy2]
  have hrho : ∀ s, (rho α ((p, (0 : Wsp α)) : Par × Wsp α)).val s =
      (besselI 0 h)⁻¹ * Real.exp (h * Real.cos (6 * Real.pi * s)) := fun s => by
    rw [sgv_rho]
    simp only [hphi]
    rw [integral_exp_cos_STR028b3]
  have hmeas : (densityMeasure ρ : Measure (Torus 1)) = threefoldReference h := by
    rw [densityMeasure_coe]
    unfold threefoldReference
    refine withDensity_congr_ae ?_
    filter_upwards [hae] with x hx
    obtain ⟨t, rfl⟩ := bs_exists_pt x
    have h2 := hx t rfl
    have e : ρ.sqrt (pt t) ^ 2 = referenceDensity h (pt t) := by
      have h3 : ρ.density (pt t) = ρ.sqrt (pt t) ^ 2 := rfl
      rw [← h3, h2, hrho]
      unfold referenceDensity
      have e3 : 2 * Real.pi * ((3 : ℕ) : ℝ) * t = 6 * Real.pi * t := by push_cast; ring
      rw [cosHarm_pt, e3, div_eq_inv_mul]
    rw [e]
  unfold ordinaryEntropy
  rw [hmeas]
  exact relativeEntropy_self _

/-- **Transfer of the jet expansion to the optimizer value.**  If `Φ(p, ψ p) = 0` and `R0² > 0`,
the reduced identity of `allOptimizers_core` holds with a remainder of the same class
(`K = |K_jet| + 128 |C_transfer|`), uniformly for `‖p‖ < r`. -/
theorem reduced_identity_STR028b3 (ψ : Par → Wsp α) (hψ : ContDiffAt ℝ 3 ψ 0) (h0 : ψ 0 = 0)
    (hF : ∀ᶠ p in 𝓝 (0 : Par), rangeMap α (p, ψ p) = 0) :
    ∃ r : ℝ, 0 < r ∧ ∃ K : ℝ, 0 ≤ K ∧ ∀ p : Par, ‖p‖ < r → 0 < p 0 ^ 2 + p 1 ^ 2 →
      Phi_STR028b1 ((p, ψ p) : Par × Wsp α) = 0 →
      ∃ E : ℝ,
        -p 3 / 2 - 9 / 20 * p 2 ^ 2 -
            p 2 * ((p 0 ^ 3 - 3 * p 0 * p 1 ^ 2) / (p 0 ^ 2 + p 1 ^ 2)) / 12 +
            (p 0 ^ 2 + p 1 ^ 2) / 48 + E = 0 ∧
        |E| ≤ K * ((|p 2| + Real.sqrt (p 0 ^ 2 + p 1 ^ 2)) ^ 3 +
          |p 3| * (|p 2| + Real.sqrt (p 0 ^ 2 + p 1 ^ 2)) + p 3 ^ 2) := by
  obtain ⟨r1, hr1, C, hC⟩ := transfer_STR028b1 ψ hψ h0 hF
  obtain ⟨r2, hr2, K, E, hE⟩ := phi_jet_expansion_STR028b2 (α := α)
  refine ⟨min (min r1 r2) (1 / 3), lt_min (lt_min hr1 hr2) (by norm_num), |K| + 128 * |C|,
    by positivity, fun p hp hS hΦ => ?_⟩
  have hp1 : ‖p‖ < r1 := lt_of_lt_of_le hp ((min_le_left _ _).trans (min_le_left _ _))
  have hp2 : ‖p‖ < r2 := lt_of_lt_of_le hp ((min_le_left _ _).trans (min_le_right _ _))
  have hp3 : ‖p‖ ≤ 1 / 3 := (lt_of_lt_of_le hp (min_le_right _ _)).le
  have hT := hC p hp1
  obtain ⟨hexp, hEb⟩ := hE p hp2
  have hn4 := nu4_le_STR028b1 p hp3
  have hR2 := R0_sq_STR028b1 p
  have hFred : Fred_STR028b1 ψ p = 0 := hΦ
  rw [hFred] at hT
  have hR4 : R0_STR028b1 p ^ 4 = (p 0 ^ 2 + p 1 ^ 2) ^ 2 := by rw [← hR2]; ring
  rw [hR4, hR2] at hexp
  rw [hR2] at hT
  have hRdef : R0_STR028b1 p = Real.sqrt (p 0 ^ 2 + p 1 ^ 2) := rfl
  rw [hRdef] at hEb hn4
  set S : ℝ := (|p 2| + Real.sqrt (p 0 ^ 2 + p 1 ^ 2)) ^ 3 +
    |p 3| * (|p 2| + Real.sqrt (p 0 ^ 2 + p 1 ^ 2)) + p 3 ^ 2 with hSdef
  set S2 : ℝ := p 0 ^ 2 + p 1 ^ 2 with hS2
  set PX : ℝ := Phi_STR028b1 (Xp (α := α) p) with hPX
  have hnu4 : 0 ≤ nu p ^ 4 := by positivity
  have hTb : |PX| / S2 ≤ 128 * |C| * S := by
    rw [div_le_iff₀ hS]
    have h1 : |0 - PX| ≤ |C| * S2 * nu p ^ 4 := by
      refine hT.trans ?_
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self C) hS.le) hnu4
    rw [zero_sub, abs_neg] at h1
    refine h1.trans ?_
    have h2 : nu p ^ 4 ≤ 128 * S := hn4
    calc |C| * S2 * nu p ^ 4 ≤ |C| * S2 * (128 * S) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = 128 * |C| * S * S2 := by ring
  refine ⟨E p + (-PX) / S2, ?_, ?_⟩
  · have hS0 : S2 ≠ 0 := hS.ne'
    have hq : p 2 * ((p 0 ^ 3 - 3 * p 0 * p 1 ^ 2) / S2) / 12 =
        p 2 * (p 0 ^ 3 - 3 * p 0 * p 1 ^ 2) / 12 / S2 := by
      field_simp
    have hPXeq : PX = -p 3 * S2 / 2 - 9 / 20 * p 2 ^ 2 * S2 -
        p 2 * (p 0 ^ 3 - 3 * p 0 * p 1 ^ 2) / 12 + S2 ^ 2 / 48 + S2 * E p := hexp
    rw [hq]
    have : (-p 3 / 2 - 9 / 20 * p 2 ^ 2 - p 2 * (p 0 ^ 3 - 3 * p 0 * p 1 ^ 2) / 12 / S2 + S2 / 48
        + (E p + -PX / S2)) * S2 = 0 := by
      field_simp
      rw [hPXeq]
      ring
    rcases mul_eq_zero.1 this with h | h
    · exact h
    · exact absurd h hS0
  · calc |E p + (-PX) / S2| ≤ |E p| + |(-PX) / S2| := abs_add_le _ _
      _ ≤ |K| * S + 128 * |C| * S := by
          have h1 : |E p| ≤ |K| * S := hEb.trans (mul_le_mul_of_nonneg_right (le_abs_self K)
            (by positivity))
          have h2 : |(-PX) / S2| = |PX| / S2 := by
            rw [abs_div, abs_neg, abs_of_pos hS]
          linarith
      _ = (|K| + 128 * |C|) * S := by ring

/-- The chart sequence `x_j = ((a_j, b_j, h_j, γ_j), w_j)` represents the optimizer sequence `ρ_j`:
`x_j → 0`, `h_j` and `γ_j = λ_j / (4π²) - 1` (with `λ_j` the quotient of `ρ_j`) are the third and
fourth coordinates, and eventually the density of `ρ_j` is the chart density `rho α (x_j)`. -/
def IsChartRep_STR028b3 {α : ℝ} [HolderExponent α] (h : ℕ → ℝ) (ρ : ℕ → AbsoluteDensity 1)
    (x : ℕ → Par × Wsp α) : Prop :=
  Tendsto x atTop (𝓝 0) ∧
  (∀ j, (x j).1 2 = h j ∧ 1 + (x j).1 3 = (str025_quot (h j) (ρ j)).toReal / (4 * Real.pi ^ 2)) ∧
  (∀ᶠ j in atTop, ∀ᵐ y ∂haar 1, ∀ s : ℝ, torusLift (fun _ => s) = y →
    (ρ j).density y = (rho α (x j)).val s)

theorem alt_minima_STR028b3 {a b h η : ℝ}
    (halt : (a / h - 2) ^ 2 + (b / h) ^ 2 < η ^ 2 ∨
      (a / h + 1) ^ 2 + (b / h - Real.sqrt 3) ^ 2 < η ^ 2 ∨
      (a / h + 1) ^ 2 + (b / h + Real.sqrt 3) ^ 2 < η ^ 2) :
    ∃ A B : ℝ, A ^ 2 + B ^ 2 ≠ 0 ∧ reducedQuotient A B = -16 / 15 ∧
      (a / h - A) ^ 2 + (b / h - B) ^ 2 < η ^ 2 := by
  have hs3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hsq : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  obtain ⟨-, -, -, hmin, -⟩ := reducedQuotient_exact_minimizers
  rcases halt with h1 | h1 | h1
  · have hne : (2 : ℝ) ^ 2 + 0 ^ 2 ≠ 0 := by norm_num
    refine ⟨2, 0, hne, ((hmin 2 0 hne).2.2 (Or.inl ⟨rfl, rfl⟩)), ?_⟩
    simpa using h1
  · have hne : (-1 : ℝ) ^ 2 + Real.sqrt 3 ^ 2 ≠ 0 := (by positivity : (0 : ℝ) < _).ne'
    refine ⟨-1, Real.sqrt 3, hne, ((hmin (-1) (Real.sqrt 3) hne).2.2
      (Or.inr (Or.inl ⟨rfl, rfl⟩))), ?_⟩
    simpa [sub_neg_eq_add] using h1
  · have hne : (-1 : ℝ) ^ 2 + (-Real.sqrt 3) ^ 2 ≠ 0 := (by positivity : (0 : ℝ) < _).ne'
    refine ⟨-1, -Real.sqrt 3, hne, ((hmin (-1) (-Real.sqrt 3) hne).2.2
      (Or.inr (Or.inr ⟨rfl, rfl⟩))), ?_⟩
    simpa [sub_neg_eq_add] using h1

/-- **STR028-b3, combined statement.**  For every sequence of positive-entropy ordinary optimizers
`ρ_j` at `h_j → 0` (`h_j ≠ 0` eventually) there are chart points `x_j` representing `ρ_j` in the
STR026 chart such that, with `R0 = √(a²+b²)`, eventually `R0 > 0`, `|γ| + R0² ≤ 192 h²`,
`R0 / |h| ≥ 1/2`, and `(a/h, b/h)` is within every `η` of a global minimizer of `Q`. -/
theorem allOptimizers_main_STR028b3 (h : ℕ → ℝ) (hh : Tendsto h atTop (𝓝 0))
    (hne : ∀ᶠ j in atTop, h j ≠ 0) (ρ : ℕ → AbsoluteDensity 1)
    (hpos : ∀ j, 0 < ordinaryEntropy (h j) (ρ j))
    (hmin : ∀ j, ∀ ρ' : AbsoluteDensity 1, 0 < ordinaryEntropy (h j) ρ' →
      ordinaryFisher (h j) (ρ j) / (2 * ordinaryEntropy (h j) (ρ j)) ≤
        ordinaryFisher (h j) ρ' / (2 * ordinaryEntropy (h j) ρ'))
    (α : ℝ) [HolderExponent α] :
    ∃ x : ℕ → Par × Wsp α, IsChartRep_STR028b3 h ρ x ∧
      (∀ᶠ j in atTop, 0 < R0_STR028b1 (x j).1 ∧
        |(x j).1 3| + R0_STR028b1 (x j).1 ^ 2 ≤ 192 * h j ^ 2 ∧
        1 / 2 ≤ R0_STR028b1 (x j).1 / |h j|) ∧
      ∀ η : ℝ, 0 < η → ∀ᶠ j in atTop, ∃ A B : ℝ, A ^ 2 + B ^ 2 ≠ 0 ∧
        reducedQuotient A B = -16 / 15 ∧
        ((x j).1 0 / h j - A) ^ 2 + ((x j).1 1 / h j - B) ^ 2 < η ^ 2 := by
  obtain ⟨U, Wn, ψ, x, hU, h0U, hWn, h0W, hψ0, hcd, hψmem, huniq, hx0, hxid, hae, hev⟩ :=
    OrdinaryGammaLower.ordinaryOptimizer_on_rangeGraph_unconditional h hh hne ρ hpos hmin α 3
      (by norm_num)
  have hcdAt : ContDiffAt ℝ 3 ψ 0 := hcd.contDiffAt (hU.mem_nhds h0U)
  have hF : ∀ᶠ p in 𝓝 (0 : Par), rangeMap α (p, ψ p) = 0 :=
    Filter.mem_of_superset (hU.mem_nhds h0U) (fun p hp => (hψmem p hp).2)
  obtain ⟨r, hr, K, hK0, Hid⟩ := reduced_identity_STR028b3 ψ hcdAt hψ0 hF
  have hx1 : Tendsto (fun j => (x j).1) atTop (𝓝 0) := (continuous_fst.tendsto _).comp hx0
  -- `Phi = 0` at the optimizers
  have hrho : Tendsto (fun j => rho α (x j)) atTop (𝓝 1) := by
    have := ((contDiff_rho (α := α) 0).continuous.tendsto 0).comp hx0
    rwa [rho_zero] at this
  have hsm : ∀ᶠ j in atTop, ∀ s, |(rho α (x j)).val s - 1| ≤ 1 / 2 := by
    filter_upwards [Metric.tendsto_nhds.1 hrho (1 / 2) (by norm_num)] with j hj s
    have h1 := sgv_abs_le_norm (rho α (x j) - 1) s
    rw [dist_eq_norm] at hj
    simpa using h1.trans hj.le
  have hS : ∀ᶠ j in atTop, 6 * Real.pi * |h j| ≤ 1 := by
    have h1 : Tendsto (fun j => 6 * Real.pi * |h j|) atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds (x := 6 * Real.pi)).mul hh.abs
    exact (tendsto_order.1 h1).2 1 one_pos |>.mono fun j hj => hj.le
  have hPhi : ∀ᶠ j in atTop, Phi_STR028b1 (x j) = 0 := by
    filter_upwards [hae, hsm, hS] with j hj1 hj2 hj3
    exact (sgv_single_phi_STR028b3 (h j) (ρ j) (hpos j) (fun ρ' hρ' => hmin j ρ' hρ')
      (x j) (hxid j).1 (hxid j).2 hj1 hj2 hj3).1
  -- `R0 > 0`
  have hR0 : ∀ᶠ j in atTop, 0 < (x j).1 0 ^ 2 + (x j).1 1 ^ 2 := by
    filter_upwards [hev, hae] with j hj hj7
    obtain ⟨hj1, -, -, -, -, hj6⟩ := hj
    by_contra hneg
    replace hneg := not_lt.1 hneg
    have ha : (x j).1 0 ^ 2 = 0 := by nlinarith [sq_nonneg ((x j).1 0), sq_nonneg ((x j).1 1)]
    have hb : (x j).1 1 ^ 2 = 0 := by nlinarith [sq_nonneg ((x j).1 0), sq_nonneg ((x j).1 1)]
    have h0 : (x j).1 0 = 0 := pow_eq_zero_iff (two_ne_zero) |>.1 ha
    have h1 : (x j).1 1 = 0 := pow_eq_zero_iff (two_ne_zero) |>.1 hb
    have hz := (rangeMap_ab_zero_STR028b1 (α := α) (x j).1 h0 h1).2
    have hw0 : (0 : Wsp α) = ψ (x j).1 := huniq _ hj1 0 h0W hz
    have hw : (x j).2 = 0 := hj6.trans hw0.symm
    exact (hpos j).ne' (entropy_zero_of_ab_zero_STR028b3 (h j) (ρ j) (x j) (hxid j).1 h0 h1 hw hj7)
  -- the scale and localization estimates
  have hcore : ∀ η : ℝ, 0 < η → ∀ᶠ j in atTop, 0 < R0_STR028b1 (x j).1 ∧
      |(x j).1 3| + R0_STR028b1 (x j).1 ^ 2 ≤ 192 * h j ^ 2 ∧
      |h j| / 2 < R0_STR028b1 (x j).1 ∧
      (((x j).1 0 / h j - 2) ^ 2 + ((x j).1 1 / h j) ^ 2 < η ^ 2 ∨
      ((x j).1 0 / h j + 1) ^ 2 + ((x j).1 1 / h j - Real.sqrt 3) ^ 2 < η ^ 2 ∨
      ((x j).1 0 / h j + 1) ^ 2 + ((x j).1 1 / h j + Real.sqrt 3) ^ 2 < η ^ 2) := by
    intro η hη
    obtain ⟨ε, hε, Htr⟩ := TrialState.allOptimizers_trial K hK0 η hη
    have hδ : 0 < min r (ε / 2) := lt_min hr (by positivity)
    have hsmallp : ∀ᶠ j in atTop, ‖(x j).1‖ < min r (ε / 2) :=
      (hx1.eventually (Metric.ball_mem_nhds _ hδ)).mono fun j hj => by simpa using hj
    filter_upwards [hsmallp, hPhi, hR0, hev, hne] with j hj1 hj2 hj3 hj4 hj5
    have hp_r : ‖(x j).1‖ < r := hj1.trans_le (min_le_left _ _)
    have hp_ε : ‖(x j).1‖ < ε / 2 := hj1.trans_le (min_le_right _ _)
    have hcomp : ∀ i, |(x j).1 i| < ε / 2 := fun i =>
      lt_of_le_of_lt (by simpa using norm_le_pi_norm (x j).1 i) hp_ε
    have hex : x j = ((x j).1, ψ (x j).1) := Prod.ext rfl hj4.2.2.2.2.2
    have hΦ : Phi_STR028b1 (((x j).1, ψ (x j).1) : Par × Wsp α) = 0 := by
      rw [← hex]; exact hj2
    obtain ⟨E, hE1, hE2⟩ := Hid (x j).1 hp_r hj3 hΦ
    have ha2 : (x j).1 0 ^ 2 ≤ (ε / 2) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hcomp 0).le 2
    have hb2 : (x j).1 1 ^ 2 ≤ (ε / 2) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hcomp 1).le 2
    have hγ : (x j).1 3 = (str025_quot (h j) (ρ j)).toReal / (4 * Real.pi ^ 2) - 1 := by
      linarith [(hxid j).2]
    have hh2 := (hxid j).1
    have hhε : |h j| ≤ ε := by
      have := (hcomp 2).le
      rw [hh2] at this
      linarith
    have hab : (x j).1 0 ^ 2 + (x j).1 1 ^ 2 ≤ ε ^ 2 := by nlinarith [ha2, hb2, hε]
    have hγε : |(x j).1 3| ≤ ε := by
      have := (hcomp 3).le
      linarith
    rw [hh2] at hE1 hE2
    have key := Htr ((x j).1 0) ((x j).1 1) (h j) ((x j).1 3) E (ρ j) (abs_pos.2 hj5)
      hhε hab hγε hj3 hγ (hpos j) (fun ρ' hρ' => hmin j ρ' hρ') hE1 hE2
    obtain ⟨k1, k2, k3⟩ := key
    have hR2 := R0_sq_STR028b1 (x j).1
    refine ⟨Real.sqrt_pos.2 hj3, ?_, k2, k3⟩
    rw [hR2]; exact k1
  refine ⟨x, ⟨hx0, hxid, hae⟩, ?_, ?_⟩
  · filter_upwards [hcore 1 one_pos, hne] with j hj hj5
    obtain ⟨k0, k1, k2, -⟩ := hj
    refine ⟨k0, k1, ?_⟩
    rw [le_div_iff₀ (abs_pos.2 hj5)]
    linarith
  · intro η hη
    filter_upwards [hcore η hη] with j hj
    exact alt_minima_STR028b3 hj.2.2.2


/-- **DAG output `threefold_allOptimizers_scale_h`.**  Along every sequence of positive-entropy
ordinary optimizers `ρ_j` with `h_j → 0` (`h_j ≠ 0` eventually) there are STR026 chart points
`x_j` representing `ρ_j` with, eventually, `R0 > 0`, `|γ| + R0² ≤ C h²` and `c ≤ R0 / |h|`
(with `C = 192`, `c = 1/2`). -/
theorem threefold_allOptimizers_scale_h (h : ℕ → ℝ) (hh : Tendsto h atTop (𝓝 0))
    (hne : ∀ᶠ j in atTop, h j ≠ 0) (ρ : ℕ → AbsoluteDensity 1)
    (hpos : ∀ j, 0 < ordinaryEntropy (h j) (ρ j))
    (hmin : ∀ j, ∀ ρ' : AbsoluteDensity 1, 0 < ordinaryEntropy (h j) ρ' →
      ordinaryFisher (h j) (ρ j) / (2 * ordinaryEntropy (h j) (ρ j)) ≤
        ordinaryFisher (h j) ρ' / (2 * ordinaryEntropy (h j) ρ'))
    (α : ℝ) [HolderExponent α] :
    ∃ x : ℕ → Par × Wsp α, IsChartRep_STR028b3 h ρ x ∧ ∃ C c : ℝ, 0 < c ∧
      ∀ᶠ j in atTop, 0 < R0_STR028b1 (x j).1 ∧
        |(x j).1 3| + R0_STR028b1 (x j).1 ^ 2 ≤ C * h j ^ 2 ∧
        c ≤ R0_STR028b1 (x j).1 / |h j| := by
  obtain ⟨x, hx, hs, -⟩ := allOptimizers_main_STR028b3 h hh hne ρ hpos hmin α
  exact ⟨x, hx, 192, 1 / 2, by norm_num, hs⟩

/-- **DAG output `threefold_allOptimizers_near_three_minima`.**  For the same chart points,
`(a_j/h_j, b_j/h_j)` eventually lies within any `η > 0` of a global minimizer of the reduced
quartic quotient `Q` (STR027: `reducedQuotient A B = -16/15`, `(A,B) ≠ 0`), i.e. one of the three
minima `(2,0)`, `(-1,±√3)`. -/
theorem threefold_allOptimizers_near_three_minima (h : ℕ → ℝ) (hh : Tendsto h atTop (𝓝 0))
    (hne : ∀ᶠ j in atTop, h j ≠ 0) (ρ : ℕ → AbsoluteDensity 1)
    (hpos : ∀ j, 0 < ordinaryEntropy (h j) (ρ j))
    (hmin : ∀ j, ∀ ρ' : AbsoluteDensity 1, 0 < ordinaryEntropy (h j) ρ' →
      ordinaryFisher (h j) (ρ j) / (2 * ordinaryEntropy (h j) (ρ j)) ≤
        ordinaryFisher (h j) ρ' / (2 * ordinaryEntropy (h j) ρ'))
    (α : ℝ) [HolderExponent α] :
    ∃ x : ℕ → Par × Wsp α, IsChartRep_STR028b3 h ρ x ∧
      ∀ η : ℝ, 0 < η → ∀ᶠ j in atTop, ∃ A B : ℝ, A ^ 2 + B ^ 2 ≠ 0 ∧
        reducedQuotient A B = -16 / 15 ∧
        ((x j).1 0 / h j - A) ^ 2 + ((x j).1 1 / h j - B) ^ 2 < η ^ 2 := by
  obtain ⟨x, hx, -, hm⟩ := allOptimizers_main_STR028b3 h hh hne ρ hpos hmin α
  exact ⟨x, hx, hm⟩

end Main

end DGPS.Examples.ThreeSpeciesCircle
