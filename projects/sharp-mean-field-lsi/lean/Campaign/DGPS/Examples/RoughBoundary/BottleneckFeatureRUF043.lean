import DGPS.Examples.RoughBoundary.Bottleneck
import DGPS.Examples.RoughBoundary.FreeEnergyBarrier
import DGPS.Analysis.PeriodicMollificationHolder

set_option maxHeartbeats 2000000

open MeasureTheory Metric Set Filter Topology
open scoped ContDiff

namespace DGPS.Examples.RoughBoundary.Bottleneck

open DGPS.Analysis.PeriodicMollification
open DGPS.Examples.RoughBoundary.Feature
open DGPS.Examples.RoughBoundary.FreeEnergy
open DGPS.Examples.RoughBoundary.Model
open DGPS.Examples.RoughBoundary.Particle
open DGPS.Examples.RoughBoundary.Semicontinuity
open DGPS.Examples.RoughBoundary.Landscape

/-! ### Definitions used by the fixed smooth bottleneck feature -/

/-- The remote centre `z_* = t_* / κ`. -/
noncomputable def remoteCentre_RUF043 (tstar : E2) : E2 := kappa⁻¹ • tstar

/-- The rescaled potential `Q(z) = Ψ(κ z)`. -/
noncomputable def remotePotential_RUF043 (L ε : ℝ) (z : E2) : ℝ :=
  featurePotential kappa0 (Ufeat L ε) (kappa • z)

/-- The remote level `Δ = Q(z_*)`. -/
noncomputable def remoteLevel_RUF043 (L ε : ℝ) (tstar : E2) : ℝ :=
  remotePotential_RUF043 L ε (remoteCentre_RUF043 tstar)

/-- The rough empirical feature mean `M_N(x) = N⁻¹ Σ U(x_i)`. -/
noncomputable def roughMean_RUF043 (L ε : ℝ) (N : ℕ+) (x : ParticleSpace 1 N) : E2 :=
  (N : ℝ)⁻¹ • featureSum L ε N x

/-- The smooth empirical statistic `Y_N(x) = N⁻¹ Σ Φ(x_i)`. -/
noncomputable def smoothMean_RUF043 (Φ : Torus 1 → E2) (N : ℕ+) (x : ParticleSpace 1 N) : E2 :=
  (N : ℝ)⁻¹ • ∑ i, Φ (x i)

/-- The transition annulus `S = {r ≤ |y - z_*| ≤ 2r}`. -/
def transitionAnnulus_RUF043 (zs : E2) (r : ℝ) : Set E2 :=
  {y | r ≤ ‖y - zs‖ ∧ ‖y - zs‖ ≤ 2 * r}

/-- The compact set `K_B = {|z - z_*| ≤ 9r/4}`. -/
def compactBall_RUF043 (zs : E2) (r : ℝ) : Set E2 :=
  {z | ‖z - zs‖ ≤ 9 * r / 4}

/-- The compact set `K_S = {3r/4 ≤ |z - z_*| ≤ 9r/4}`. -/
def compactAnnulus_RUF043 (zs : E2) (r : ℝ) : Set E2 :=
  {z | 3 * r / 4 ≤ ‖z - zs‖ ∧ ‖z - zs‖ ≤ 9 * r / 4}

/-! ### Uniform periodic mollification of a continuous function -/

lemma exists_mollify_close_RUF043 {g : Torus 1 → ℝ} (hg : Continuous g) {η : ℝ} (hη : 0 < η) :
    ∃ h₀ : ℝ, 0 < h₀ ∧ h₀ < 1 / 4 ∧ ∀ h : ℝ, 0 < h → h ≤ h₀ →
      ∀ y, |mollify h g y - g y| ≤ η := by
  have huc : UniformContinuous g := CompactSpace.uniformContinuous_of_continuous hg
  obtain ⟨δ, hδ, hδu⟩ := Metric.uniformContinuous_iff.1 huc η hη
  have hpt : ∀ᶠ z : ℝ in 𝓝 0, dist (pt z) 0 < δ := by
    have := continuous_pt.tendsto 0
    rw [pt_zero] at this
    exact this (Metric.ball_mem_nhds _ hδ)
  obtain ⟨ρ, hρ, hρδ⟩ := Metric.eventually_nhds_iff.1 hpt
  refine ⟨min (ρ / 2) (1 / 8), lt_min (by positivity) (by norm_num),
    lt_of_le_of_lt (min_le_right _ _) (by norm_num), fun h hh hhle y => ?_⟩
  have e : mollify h g y - g y = ∫ s, phiH h s * (g (y - pt s) - g y) := by
    have h1 : ∫ s, phiH h s * g y = g y := by
      rw [integral_mul_const, integral_phiH hh, one_mul]
    unfold mollify
    conv_lhs => rw [← h1]
    rw [← integral_sub (holder_integrable_phiH_mul hh hg y) ((integrable_phiH hh).mul_const _)]
    congr 1; funext s; ring
  rw [e]
  refine abs_integral_phiH_mul_le hh fun s hs => ?_
  have hs' := abs_phiH_support_le hh hs
  have hsρ : dist s 0 < ρ := by
    rw [Real.dist_eq, sub_zero]
    have : h ≤ ρ / 2 := hhle.trans (min_le_left _ _)
    linarith
  have hd := hρδ hsρ
  have := hδu (a := y - pt s) (b := y) (by
    rw [dist_eq_norm, sub_sub_cancel_left, norm_neg]
    simpa [dist_eq_norm] using hd)
  rw [Real.dist_eq] at this
  exact this.le

/-- A smooth periodic map `Φ : 𝕋 → ℝ²` uniformly `η`-close to a continuous periodic map. -/
lemma exists_smooth_uniform_approx_RUF043 {U : Torus 1 → E2} (hU : Continuous U) {η : ℝ}
    (hη : 0 < η) :
    ∃ Φ : Torus 1 → E2, ContDiff ℝ ∞ (Φ ∘ DGPS.torusLift) ∧ ∀ y, ‖Φ y - U y‖ ≤ η := by
  have hcoord : ∀ i : Fin 2, Continuous fun y => U y i := fun i =>
    (continuous_apply i).comp ((PiLp.continuous_ofLp 2 (fun _ : Fin 2 => ℝ)).comp hU)
  obtain ⟨a₀, ha₀, ha₁, ha⟩ := exists_mollify_close_RUF043 (hcoord 0) (half_pos hη)
  obtain ⟨b₀, hb₀, hb₁, hb⟩ := exists_mollify_close_RUF043 (hcoord 1) (half_pos hη)
  set h : ℝ := min a₀ b₀ with hhdef
  have hh : 0 < h := lt_min ha₀ hb₀
  have hha : h ≤ a₀ := min_le_left _ _
  have hhb : h ≤ b₀ := min_le_right _ _
  refine ⟨fun y => (EuclideanSpace.equiv (Fin 2) ℝ).symm
    (fun i => mollify h (fun x => U x i) y), ?_, fun y => ?_⟩
  · have hsm : ContDiff ℝ ∞ (fun x : Fin 1 → ℝ =>
        (fun i : Fin 2 => mollify h (fun x => U x i) (DGPS.torusLift x))) := by
      refine contDiff_pi.mpr fun i => ?_
      exact isSmoothPeriodic_mollify_of_continuous hh (hcoord i)
    exact (EuclideanSpace.equiv (Fin 2) ℝ).symm.contDiff.comp hsm
  · have h0 := ha h hh hha y
    have h1 := hb h hh hhb y
    rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
    refine Real.sqrt_le_iff.2 ⟨hη.le, ?_⟩
    simp only [Real.norm_eq_abs, sq_abs]
    have e0 : |mollify h (fun x => U x 0) y - U y 0| ^ 2 ≤ (η / 2) ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) h0 2
    have e1 : |mollify h (fun x => U x 1) y - U y 1| ^ 2 ≤ (η / 2) ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) h1 2
    rw [sq_abs] at e0 e1
    change (mollify h (fun x => U x 0) y - U y 0) ^ 2 +
      (mollify h (fun x => U x 1) y - U y 1) ^ 2 ≤ η ^ 2
    nlinarith [sq_nonneg η]

/-! ### A smooth radial cutoff -/

lemma exists_cutoff_RUF043 (c : E2) {r : ℝ} (hr : 0 < r) :
    ∃ χ : E2 → ℝ, ContDiff ℝ ∞ χ ∧ (∀ y, 0 ≤ χ y ∧ χ y ≤ 1) ∧
      (∀ y, ‖y - c‖ ≤ r → χ y = 1) ∧ (∀ y, 2 * r ≤ ‖y - c‖ → χ y = 0) ∧
      (∀ y, fderiv ℝ χ y ≠ 0 → r ≤ ‖y - c‖ ∧ ‖y - c‖ ≤ 2 * r) := by
  let f : ContDiffBump c := ⟨r, 2 * r, hr, by linarith⟩
  have h1 : ∀ y, ‖y - c‖ ≤ r → f y = 1 := fun y hy =>
    f.one_of_mem_closedBall (by rwa [mem_closedBall, dist_eq_norm])
  have h0 : ∀ y, 2 * r ≤ ‖y - c‖ → f y = 0 := fun y hy =>
    f.zero_of_le_dist (by rwa [dist_eq_norm])
  refine ⟨f, f.contDiff, fun y => ⟨f.nonneg, f.le_one⟩, h1, h0, fun y hy => ?_⟩
  by_contra hcon
  rw [not_and_or, not_le, not_le] at hcon
  rcases hcon with hlt | hgt
  · have hev : (f : E2 → ℝ) =ᶠ[𝓝 y] fun _ => (1 : ℝ) := by
      have : ball c r ∈ 𝓝 y := Metric.isOpen_ball.mem_nhds (by rwa [mem_ball, dist_eq_norm])
      filter_upwards [this] with z hz
      exact h1 z (by rw [mem_ball, dist_eq_norm] at hz; exact hz.le)
    apply hy
    rw [hev.fderiv_eq]
    simp
  · have hev : (f : E2 → ℝ) =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
      have : (closedBall c (2 * r))ᶜ ∈ 𝓝 y :=
        isClosed_closedBall.isOpen_compl.mem_nhds (by
          rw [mem_compl_iff, mem_closedBall, dist_eq_norm]; exact not_le.2 hgt)
      filter_upwards [this] with z hz
      exact h0 z (by
        rw [mem_compl_iff, mem_closedBall, dist_eq_norm, not_le] at hz; exact hz.le)
    apply hy
    rw [hev.fderiv_eq]
    simp

/-! ### The potential `Q` near the remote critical point -/

lemma continuous_remotePotential_RUF043 {L : ℝ} (hL : 0 < L) (ε : ℝ) :
    Continuous (remotePotential_RUF043 L ε) := by
  unfold remotePotential_RUF043
  exact (contDiff_featurePotential hL ε).continuous.comp (continuous_const_smul kappa)

lemma kappa_smul_centre_RUF043 (tstar : E2) :
    kappa • remoteCentre_RUF043 tstar = tstar := by
  unfold remoteCentre_RUF043
  rw [smul_smul, mul_inv_cancel₀ kappa_pos.ne', one_smul]

lemma norm_kappa_smul_sub_RUF043 (z tstar : E2) :
    ‖kappa • z - tstar‖ = kappa * ‖z - remoteCentre_RUF043 tstar‖ := by
  rw [← norm_smul_of_nonneg kappa_pos.le, smul_sub, kappa_smul_centre_RUF043]

/-! ### Main theorem -/

/-- RUF043.  Fixed smooth bottleneck feature and compatible neighborhoods.

Setting: the RUF029 data (the landscape certificate of `U = Ufeat L ε`, a critical point `t_*`
of `Ψ` with `D²Ψ ≥ λ I` on `B̄(t_*, r₀)` and `0 ∉ B̄(t_*, r₀)`).  With `z_* = t_*/κ`,
`Q(z) = Ψ(κ z)` and `Δ = Q(z_*)`, there are `R > 0` (with `r = R/4`), `0 < η < r/4`, a smooth
periodic `Φ : 𝕋 → ℝ²` with `‖Φ - U‖_∞ ≤ η`, and a smooth cutoff `χ ∈ [0,1]` which is `1` on
`{|y - z_*| ≤ r}`, `0` on `{|y - z_*| ≥ 2r}` and has derivative supported in
`S = {r ≤ |y - z_*| ≤ 2r}`, such that `Δ > 0`, `Q ≥ Δ` on `B̄(z_*, R)` with equality only at
`z_*`, `0 ∉ B̄(z_*, R)`, and (7.6)-(7.7) hold: for every `N` and every configuration
`|Y_N - M_N| ≤ η`, `Y_N ∈ B ⟹ M_N ∈ K_B`, `Y_N ∈ S ⟹ M_N ∈ K_S`, `Q ≥ Δ` on `K_B`, and
`b = min_{K_S} Q - Δ > 0`. -/
theorem fixed_smooth_bottleneck_feature_and_compatible_neighborhoods {L : ℝ} (hL : 0 < L)
    (ε : ℝ) (hcert : RoughLandscapeCertificate (Ufeat L ε)) (tstar : E2) (r₀ lam : ℝ)
    (hr₀ : 0 < r₀) (hlam : 0 < lam)
    (hcrit : fderiv ℝ (featurePotential kappa0 (Ufeat L ε)) tstar = 0)
    (h0 : (0 : E2) ∉ closedBall tstar r₀)
    (hH : ∀ x ∈ closedBall tstar r₀, ∀ v : E2,
      lam * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ (featurePotential kappa0 (Ufeat L ε))) x v v) :
    ∃ R : ℝ, 0 < R ∧
      0 < remoteLevel_RUF043 L ε tstar ∧
      (∀ z ∈ closedBall (remoteCentre_RUF043 tstar) R,
        remoteLevel_RUF043 L ε tstar ≤ remotePotential_RUF043 L ε z) ∧
      (∀ z ∈ closedBall (remoteCentre_RUF043 tstar) R,
        remotePotential_RUF043 L ε z = remoteLevel_RUF043 L ε tstar →
          z = remoteCentre_RUF043 tstar) ∧
      (0 : E2) ∉ closedBall (remoteCentre_RUF043 tstar) R ∧
      ∃ η : ℝ, 0 < η ∧ η < (R / 4) / 4 ∧
      ∃ Φ : Torus 1 → E2, ContDiff ℝ ∞ (Φ ∘ DGPS.torusLift) ∧
        (∀ y, ‖Φ y - Ufeat L ε y‖ ≤ η) ∧
      ∃ χ : E2 → ℝ, ContDiff ℝ ∞ χ ∧ (∀ y, 0 ≤ χ y ∧ χ y ≤ 1) ∧
        (∀ y, ‖y - remoteCentre_RUF043 tstar‖ ≤ R / 4 → χ y = 1) ∧
        (∀ y, 2 * (R / 4) ≤ ‖y - remoteCentre_RUF043 tstar‖ → χ y = 0) ∧
        Function.support (fderiv ℝ χ) ⊆
          transitionAnnulus_RUF043 (remoteCentre_RUF043 tstar) (R / 4) ∧
        (∀ y, ‖y - remoteCentre_RUF043 tstar‖ < (R / 4) / 2 →
          χ y = 1 ∧ ∀ y' ∈ transitionAnnulus_RUF043 (remoteCentre_RUF043 tstar) (R / 4),
            (R / 4) / 2 ≤ ‖y' - y‖) ∧
        (∀ N : ℕ+, ∀ x : ParticleSpace 1 N,
          ‖smoothMean_RUF043 Φ N x - roughMean_RUF043 L ε N x‖ ≤ η) ∧
        (∀ N : ℕ+, ∀ x : ParticleSpace 1 N,
          ‖smoothMean_RUF043 Φ N x - remoteCentre_RUF043 tstar‖ < 2 * (R / 4) →
            roughMean_RUF043 L ε N x ∈
              compactBall_RUF043 (remoteCentre_RUF043 tstar) (R / 4)) ∧
        (∀ N : ℕ+, ∀ x : ParticleSpace 1 N,
          smoothMean_RUF043 Φ N x ∈
              transitionAnnulus_RUF043 (remoteCentre_RUF043 tstar) (R / 4) →
            roughMean_RUF043 L ε N x ∈
              compactAnnulus_RUF043 (remoteCentre_RUF043 tstar) (R / 4)) ∧
        (∀ z ∈ compactBall_RUF043 (remoteCentre_RUF043 tstar) (R / 4),
          remoteLevel_RUF043 L ε tstar ≤ remotePotential_RUF043 L ε z) ∧
        ∃ b : ℝ, 0 < b ∧
          (∀ z ∈ compactAnnulus_RUF043 (remoteCentre_RUF043 tstar) (R / 4),
            remoteLevel_RUF043 L ε tstar + b ≤ remotePotential_RUF043 L ε z) ∧
          ∃ z ∈ compactAnnulus_RUF043 (remoteCentre_RUF043 tstar) (R / 4),
            remotePotential_RUF043 L ε z = remoteLevel_RUF043 L ε tstar + b := by
  set zs : E2 := remoteCentre_RUF043 tstar with hzs
  set Δ : ℝ := remoteLevel_RUF043 L ε tstar with hΔ
  set Q : E2 → ℝ := remotePotential_RUF043 L ε with hQ
  have hk : 0 < kappa := kappa_pos
  set R : ℝ := r₀ / kappa with hR
  have hRpos : 0 < R := div_pos hr₀ hk
  have hkR : kappa * R = r₀ := by rw [hR]; field_simp
  have htay := taylor_lower_of_hessian (featurePotential kappa0 (Ufeat L ε))
    (contDiff_featurePotential hL ε) tstar r₀ lam hcrit hH
  have hΔeq : Δ = featurePotential kappa0 (Ufeat L ε) tstar := by
    rw [hΔ]
    unfold remoteLevel_RUF043 remotePotential_RUF043
    rw [kappa_smul_centre_RUF043]
  -- the quadratic lower bound for `Q` near `z_*`
  have hQlow : ∀ z, ‖z - zs‖ ≤ R → Δ + lam / 2 * (kappa * ‖z - zs‖) ^ 2 ≤ Q z := by
    intro z hz
    have hmem : kappa • z ∈ closedBall tstar r₀ := by
      rw [mem_closedBall, dist_eq_norm, norm_kappa_smul_sub_RUF043, ← hkR]
      exact mul_le_mul_of_nonneg_left hz hk.le
    have := htay _ hmem
    rw [norm_kappa_smul_sub_RUF043, ← hΔeq] at this
    exact this
  -- `Δ > 0`
  have hts : r₀ < ‖tstar‖ := by
    by_contra hcon
    apply h0
    rw [mem_closedBall, dist_eq_norm, zero_sub, norm_neg]
    exact not_lt.1 hcon
  have hΔpos : 0 < Δ := by
    obtain ⟨-, -, hnn, hzero, -⟩ := hcert
    have h1 : 0 ≤ featurePotential kappa0 (Ufeat L ε) tstar := hnn tstar
    have h2 : featurePotential kappa0 (Ufeat L ε) tstar ≠ 0 := by
      intro h
      have := (hzero tstar).1 h
      rw [this, norm_zero] at hts
      linarith
    rw [hΔeq]
    exact lt_of_le_of_ne h1 (Ne.symm h2)
  have hzsnorm : R < ‖zs‖ := by
    have : ‖zs‖ = ‖tstar‖ / kappa := by
      rw [hzs]
      unfold remoteCentre_RUF043
      rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hk]
      field_simp
    rw [this, hR]
    exact div_lt_div_of_pos_right hts hk
  have hQge : ∀ z ∈ closedBall zs R, Δ ≤ Q z := by
    intro z hz
    rw [mem_closedBall, dist_eq_norm] at hz
    have := hQlow z hz
    nlinarith [sq_nonneg (kappa * ‖z - zs‖), hlam]
  have hQstrict : ∀ z, ‖z - zs‖ ≤ R → z ≠ zs → Δ < Q z := by
    intro z hz hne
    have hpos : 0 < ‖z - zs‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
    have := hQlow z hz
    have h2 : 0 < lam / 2 * (kappa * ‖z - zs‖) ^ 2 := by positivity
    linarith
  set r : ℝ := R / 4 with hr
  have hrpos : 0 < r := by positivity
  set η : ℝ := r / 8 with hη
  have hηpos : 0 < η := by positivity
  have hηlt : η < r / 4 := by rw [hη]; linarith
  obtain ⟨Φ, hΦs, hΦ⟩ := exists_smooth_uniform_approx_RUF043 (continuous_Ufeat hL ε) hηpos
  obtain ⟨χ, hχs, hχ01, hχ1, hχ0, hχd⟩ := exists_cutoff_RUF043 zs hrpos
  have hMY : ∀ (N : ℕ+) (x : ParticleSpace 1 N),
      ‖smoothMean_RUF043 Φ N x - roughMean_RUF043 L ε N x‖ ≤ η := by
    intro N x
    have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
    have hdiff : smoothMean_RUF043 Φ N x - roughMean_RUF043 L ε N x =
        (N : ℝ)⁻¹ • ∑ i, (Φ (x i) - Ufeat L ε (x i)) := by
      unfold smoothMean_RUF043 roughMean_RUF043 featureSum
      rw [← smul_sub, Finset.sum_sub_distrib]
    rw [hdiff, norm_smul, norm_inv, Real.norm_natCast]
    have hsum : ‖∑ i, (Φ (x i) - Ufeat L ε (x i))‖ ≤ (N : ℝ) * η := by
      refine (norm_sum_le _ _).trans ?_
      refine (Finset.sum_le_card_nsmul _ _ η fun i _ => hΦ (x i)).trans ?_
      simp
    calc (N : ℝ)⁻¹ * ‖∑ i, (Φ (x i) - Ufeat L ε (x i))‖ ≤ (N : ℝ)⁻¹ * ((N : ℝ) * η) :=
          mul_le_mul_of_nonneg_left hsum (inv_nonneg.2 hN.le)
      _ = η := by field_simp
  refine ⟨R, hRpos, hΔpos, hQge, ?_, ?_, η, hηpos, hηlt, Φ, hΦs, hΦ, χ, hχs, hχ01, hχ1, hχ0,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz hQz
    by_contra hne
    have := hQstrict z (by rwa [mem_closedBall, dist_eq_norm] at hz) hne
    linarith
  · intro hmem
    rw [mem_closedBall, dist_eq_norm, zero_sub, norm_neg] at hmem
    linarith
  · intro y hy
    exact hχd y hy
  · intro y hy
    refine ⟨hχ1 y (by linarith), fun y' hy' => ?_⟩
    have h1 : r ≤ ‖y' - zs‖ := hy'.1
    have h2 : ‖y' - zs‖ ≤ ‖y' - y‖ + ‖y - zs‖ := by
      calc ‖y' - zs‖ = ‖(y' - y) + (y - zs)‖ := by rw [sub_add_sub_cancel]
        _ ≤ _ := norm_add_le _ _
    linarith
  · exact hMY
  · intro N x hx
    have h1 := hMY N x
    have h2 := norm_sub_le_norm_sub_add_norm_sub (roughMean_RUF043 L ε N x)
      (smoothMean_RUF043 Φ N x) zs
    rw [norm_sub_rev] at h1
    show ‖roughMean_RUF043 L ε N x - zs‖ ≤ 9 * (R / 4) / 4
    linarith
  · intro N x hx
    have h1 := hMY N x
    have h2 := norm_sub_le_norm_sub_add_norm_sub (roughMean_RUF043 L ε N x)
      (smoothMean_RUF043 Φ N x) zs
    have h3 := norm_sub_le_norm_sub_add_norm_sub (smoothMean_RUF043 Φ N x)
      (roughMean_RUF043 L ε N x) zs
    have hx1 : r ≤ ‖smoothMean_RUF043 Φ N x - zs‖ := hx.1
    have hx2 : ‖smoothMean_RUF043 Φ N x - zs‖ ≤ 2 * r := hx.2
    have h1' : ‖roughMean_RUF043 L ε N x - smoothMean_RUF043 Φ N x‖ ≤ η := by
      rw [norm_sub_rev]; exact h1
    show 3 * (R / 4) / 4 ≤ ‖roughMean_RUF043 L ε N x - zs‖ ∧
      ‖roughMean_RUF043 L ε N x - zs‖ ≤ 9 * (R / 4) / 4
    constructor <;> linarith
  · intro z hz
    have hz' : ‖z - zs‖ ≤ R := by
      have : ‖z - zs‖ ≤ 9 * r / 4 := hz
      linarith
    exact hQge z (by rwa [mem_closedBall, dist_eq_norm])
  · -- the exact minimum of `Q` over `K_S`
    have hKc : IsCompact (compactAnnulus_RUF043 zs r) := by
      have hcl : IsClosed {z : E2 | 3 * r / 4 ≤ ‖z - zs‖} :=
        isClosed_le continuous_const (continuous_norm.comp (continuous_id.sub continuous_const))
      have : compactAnnulus_RUF043 zs r = closedBall zs (9 * r / 4) ∩ {z : E2 | 3 * r / 4 ≤ ‖z - zs‖} := by
        ext z
        simp only [compactAnnulus_RUF043, mem_ofPred_eq, mem_inter_iff, mem_closedBall,
          dist_eq_norm]
        tauto
      rw [this]
      exact (isCompact_closedBall zs _).inter_right hcl
    obtain ⟨v, hv⟩ := exists_norm_eq E2 hrpos.le
    have hne : (compactAnnulus_RUF043 zs r).Nonempty :=
      ⟨zs + v, by
        simp only [compactAnnulus_RUF043, mem_ofPred_eq, add_sub_cancel_left, hv]
        constructor <;> linarith⟩
    have hKR : ∀ z ∈ compactAnnulus_RUF043 zs r, ‖z - zs‖ ≤ R := fun z hz => by
      have : ‖z - zs‖ ≤ 9 * r / 4 := hz.2
      linarith
    obtain ⟨z₀, hz₀, hmin⟩ := hKc.exists_isMinOn hne
      ((continuous_remotePotential_RUF043 hL ε).continuousOn)
    have hz₀ne : z₀ ≠ zs := by
      intro h
      have : 3 * r / 4 ≤ ‖z₀ - zs‖ := hz₀.1
      rw [h, sub_self, norm_zero] at this
      linarith
    have hlt : Δ < Q z₀ := hQstrict z₀ (hKR z₀ hz₀) hz₀ne
    refine ⟨Q z₀ - Δ, by linarith, fun z hz => ?_, z₀, hz₀, by ring⟩
    have := hmin hz
    simp only [mem_ofPred_eq] at this
    linarith

end DGPS.Examples.RoughBoundary.Bottleneck
