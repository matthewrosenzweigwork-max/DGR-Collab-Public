import DGPS.FiniteN.SymmetricHarmonicTrial
import DGPS.FiniteN.Tools.RareCutoff
import DGPS.FiniteN.ScalarFoldFIN062
import DGPS.FiniteN.ScalarFoldFIN063
import DGPS.FiniteN.ScalarFoldFIN060

/-!
# FIN064: fold symmetric test and exact power row

For the scalar cosine model at the fold field `h = h_c(κ)`, `κ > 2`, fix a smooth cutoff `χ`
(`0 ≤ χ ≤ 1`, `χ = 1` on `[-1, 1]`, `χ = 0` outside `[-2, 2]`) and let
`f_N = χ (N^{1/3} (z_N - t*))`, `z_N = h_c + (κ/N) Σ_i cos 2π x_i`.  Then `f_N` is symmetric and
`Σ_i |∂_{x_i} f_N|² ≤ C N^{-1/3} 1_{S_N}`, so FIN018 applied with the FIN062/FIN063 rare-box masses
gives `λ_N ≤ C N^{-1/3}`, `r_N^sym ≤ C N^{-4/3}`; FIN060 gives the matching lower bounds, and
`r_N^all ≤ r_N^sym` finishes the three `Θ` rows.
-/

open MeasureTheory
open scoped ContDiff ENNReal

namespace DGPS.FiniteN.ScalarFoldFIN064

open DGPS DGPS.Models DGPS.FiniteN.Tools.Hubbard DGPS.FiniteN.Tools.GaussianCoupling
open DGPS.Circle.AngularNormalization DGPS.FiniteN.UnitTorusNormalization

theorem lift_secT_FIN064 {N : ℕ+} (x : ParticleSpace 1 N) :
    particleLift (fun i => SharpLSI.secT (x i)) = x := by
  funext i; simp [particleLift, torusLift, SharpLSI.liftT_secT]

theorem isSmooth_comp_FIN064 {N : ℕ+} {F : ParticleSpace 1 N → ℝ}
    (hF : IsSmoothPeriodicParticle F) {G : ℝ → ℝ} (hG : ContDiff ℝ ∞ G) :
    IsSmoothPeriodicParticle (fun x => G (F x)) := by
  unfold IsSmoothPeriodicParticle at *
  exact hG.comp hF

theorem particlePartial_comp_FIN064 {N : ℕ+} {F : ParticleSpace 1 N → ℝ}
    (hF : IsSmoothPeriodicParticle F) {G : ℝ → ℝ} (hG : ContDiff ℝ ∞ G)
    (i : Fin N) (x : ParticleSpace 1 N) :
    particlePartial i 0 (fun x => G (F x)) x = deriv G (F x) * particlePartial i 0 F x := by
  unfold particlePartial
  have hD : DifferentiableAt ℝ (F ∘ particleLift) (fun k => SharpLSI.secT (x k)) :=
    (hF.differentiable (by simp)) _
  have hGd : DifferentiableAt ℝ G ((F ∘ particleLift) (fun k => SharpLSI.secT (x k))) :=
    (hG.differentiable (by simp)) _
  have : ((fun x => G (F x)) ∘ particleLift) = G ∘ (F ∘ particleLift) := rfl
  rw [this, fderiv_comp _ hGd hD]
  simp only [ContinuousLinearMap.comp_apply, Function.comp_apply, lift_secT_FIN064]
  have key : ∀ w : ℝ, fderiv ℝ G (F x) w = deriv G (F x) * w := fun w => by
    have := (fderiv ℝ G (F x)).map_smul w (1 : ℝ)
    simp only [smul_eq_mul, mul_one] at this
    rw [this, fderiv_apply_one_eq_deriv]; ring
  rw [key]


theorem smooth_h1_FIN064 (A : InteractionData 1) (N : ℕ+) {F : ParticleSpace 1 N → ℝ}
    (hF : IsSmoothPeriodicParticle F) :
    ∃ f : ParticleH1 A N, f.1 = F ∧ particleEnergy A N f =
      ∫ x, ∑ i, (particlePartial i 0 F x) ^ 2 ∂particleLaw A N := by
  have hG := DGPS.FiniteN.PositiveRate.isParticleHaarWeakGradient_of_smooth hF
  have hGP : IsParticleWeakGradient A N F
      (fun x i => WithLp.toLp 2 fun j => particlePartial i j F x) :=
    (isParticleWeakGradient_iff A N _ _).2 hG
  have hmem : MemParticleH1 A N F := ⟨_, hGP⟩
  refine ⟨⟨F, hmem⟩, rfl, ?_⟩
  rw [particleEnergy_eq_of_isParticleWeakGradient ⟨F, hmem⟩ hGP]
  simp only [particleTangentNormSq_eq, Fin.sum_univ_one]

/-- The fixed cutoff bump `ContDiffBump` with inner radius `1` and outer radius `2`. -/
noncomputable def bumpFIN064 : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩

/-- The cutoff profile `χ`. -/
noncomputable def chiFIN064 : ℝ → ℝ := fun u => bumpFIN064 u

theorem chi_contDiff_FIN064 : ContDiff ℝ ∞ chiFIN064 := bumpFIN064.contDiff

theorem chi_nonneg_FIN064 (u : ℝ) : 0 ≤ chiFIN064 u := bumpFIN064.nonneg

theorem chi_le_one_FIN064 (u : ℝ) : chiFIN064 u ≤ 1 := bumpFIN064.le_one

theorem chi_one_FIN064 {u : ℝ} (hu : |u| ≤ 1) : chiFIN064 u = 1 := by
  apply bumpFIN064.one_of_mem_closedBall
  simpa [Metric.mem_closedBall, dist_zero_right, bumpFIN064] using hu

theorem chi_zero_FIN064 {u : ℝ} (hu : 2 < |u|) : chiFIN064 u = 0 := by
  apply bumpFIN064.zero_of_le_dist
  simp only [dist_zero_right, Real.norm_eq_abs, bumpFIN064]
  exact hu.le

theorem deriv_chi_zero_FIN064 {u : ℝ} (hu : 2 < |u|) : deriv chiFIN064 u = 0 := by
  have hopen : IsOpen {v : ℝ | 2 < |v|} := isOpen_lt continuous_const continuous_abs
  have hev : chiFIN064 =ᶠ[nhds u] fun _ => (0 : ℝ) :=
    Filter.eventually_of_mem (hopen.mem_nhds hu) fun v hv => chi_zero_FIN064 hv
  rw [hev.deriv_eq]
  simp

theorem deriv_chi_bound_FIN064 : ∃ K : ℝ, 0 ≤ K ∧ ∀ u, |deriv chiFIN064 u| ≤ K := by
  have hc : Continuous (deriv chiFIN064) := chi_contDiff_FIN064.continuous_deriv (by simp)
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Set.Icc (-2 : ℝ) 2)).exists_bound_of_continuousOn
    hc.continuousOn
  refine ⟨|C|, abs_nonneg _, fun u => ?_⟩
  by_cases hu : 2 < |u|
  · rw [deriv_chi_zero_FIN064 hu]; simp
  · have hu' : u ∈ Set.Icc (-2 : ℝ) 2 := by
      rw [not_lt, abs_le] at hu
      exact hu
    have := hC u hu'
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_abs_self C)


theorem cube_FIN064 (N : ℕ+) : ((N : ℝ) ^ (1 / 3 : ℝ)) ^ 3 = (N : ℝ) := by
  have hN : (0 : ℝ) ≤ N := by positivity
  rw [← Real.rpow_natCast, ← Real.rpow_mul hN]
  norm_num

theorem rpow_neg_third_FIN064 (N : ℕ+) :
    (N : ℝ) ^ (-(1 / 3 : ℝ)) = ((N : ℝ) ^ (1 / 3 : ℝ))⁻¹ := by
  rw [Real.rpow_neg (by positivity)]

theorem rpow_third_pos_FIN064 (N : ℕ+) : 0 < (N : ℝ) ^ (1 / 3 : ℝ) :=
  Real.rpow_pos_of_pos (by exact_mod_cast N.pos) _

noncomputable def aFIN064 (κ : ℝ) (N : ℕ+) : ℝ := (N : ℝ) ^ (1 / 3 : ℝ) * (κ / N)

noncomputable def bFIN064 (h t : ℝ) (N : ℕ+) : ℝ := (N : ℝ) ^ (1 / 3 : ℝ) * (h - t)

noncomputable def gFIN064 (a b : ℝ) : ℝ → ℝ := fun s => chiFIN064 (a * s + b)

noncomputable def testFIN064 (κ h t : ℝ) (N : ℕ+) : ParticleSpace 1 N → ℝ :=
  fun x => gFIN064 (aFIN064 κ N) (bFIN064 h t N) (harmonicTrial N x)

theorem gFIN064_contDiff (a b : ℝ) : ContDiff ℝ ∞ (gFIN064 a b) :=
  chi_contDiff_FIN064.comp ((contDiff_const.mul contDiff_id).add contDiff_const)

theorem deriv_gFIN064 (a b s : ℝ) : deriv (gFIN064 a b) s = deriv chiFIN064 (a * s + b) * a := by
  have hd : DifferentiableAt ℝ chiFIN064 (a * s + b) :=
    (chi_contDiff_FIN064.differentiable (by simp)) _
  have hin : HasDerivAt (fun s : ℝ => a * s + b) a s := by
    simpa using ((hasDerivAt_id s).const_mul a).add_const b
  exact (hd.hasDerivAt.comp s hin).deriv

theorem isSmooth_testFIN064 (κ h t : ℝ) (N : ℕ+) : IsSmoothPeriodicParticle (testFIN064 κ h t N) :=
  isSmooth_comp_FIN064 (isSmooth_harmonicTrial N) (gFIN064_contDiff _ _)

theorem particlePartial_testFIN064 (κ h t : ℝ) (N : ℕ+) (i : Fin N) (x : ParticleSpace 1 N) :
    particlePartial i 0 (testFIN064 κ h t N) x =
      deriv chiFIN064 (aFIN064 κ N * harmonicTrial N x + bFIN064 h t N) * aFIN064 κ N *
        (-(2 * Real.pi) * (mode 1 (x i)).im) := by
  have := particlePartial_comp_FIN064 (isSmooth_harmonicTrial N)
    (gFIN064_contDiff (aFIN064 κ N) (bFIN064 h t N)) i x
  unfold testFIN064
  rw [this, deriv_gFIN064, particlePartial_harmonicTrial]

theorem posteriorCenter_eq_FIN064 (κ h : ℝ) (N : ℕ+) (x : ParticleSpace 1 N) :
    posteriorCenter (ScalarFoldFIN060.dSFIN060 κ) (ScalarFoldFIN060.hSFIN060 h)
      ScalarFoldFIN060.phiSFIN060 N x 0 = h + κ / N * harmonicTrial N x := by
  simp [posteriorCenter, ScalarFoldFIN060.hSFIN060, ScalarFoldFIN060.dSFIN060, fieldSum,
    ScalarFoldFIN060.phiSFIN060, harmonicTrial, mode_apply, scalarCos,
    Finset.mul_sum, div_eq_inv_mul, mul_assoc]

theorem scaled_eq_FIN064 (κ h t : ℝ) (N : ℕ+) (x : ParticleSpace 1 N) :
    (N : ℝ) ^ (1 / 3 : ℝ) * (posteriorCenter (ScalarFoldFIN060.dSFIN060 κ)
      (ScalarFoldFIN060.hSFIN060 h) ScalarFoldFIN060.phiSFIN060 N x 0 - t) =
      aFIN064 κ N * harmonicTrial N x + bFIN064 h t N := by
  rw [posteriorCenter_eq_FIN064]; unfold aFIN064 bFIN064; ring


theorem abs_mode_im_le_FIN064 (y : Torus 1) : |(mode 1 y).im| ≤ 1 := by
  refine (Complex.abs_im_le_norm _).trans (le_of_eq ?_)
  rw [mode_apply]; simp [fourier_apply]

theorem gradSq_zero_FIN064 (κ h t : ℝ) (N : ℕ+) (x : ParticleSpace 1 N)
    (hx : 2 < |aFIN064 κ N * harmonicTrial N x + bFIN064 h t N|) :
    ∑ i, (particlePartial i 0 (testFIN064 κ h t N) x) ^ 2 = 0 := by
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [particlePartial_testFIN064, deriv_chi_zero_FIN064 hx]
  simp

theorem gradSq_le_FIN064 {K : ℝ} (hK : ∀ u, |deriv chiFIN064 u| ≤ K) (κ h t : ℝ) (N : ℕ+)
    (x : ParticleSpace 1 N) :
    ∑ i, (particlePartial i 0 (testFIN064 κ h t N) x) ^ 2 ≤
      K ^ 2 * (4 * Real.pi ^ 2) * κ ^ 2 * (N : ℝ) ^ (-(1 / 3 : ℝ)) := by
  have hs := rpow_third_pos_FIN064 N
  set s := (N : ℝ) ^ (1 / 3 : ℝ) with hsdef
  have h3 : s ^ 3 = (N : ℝ) := cube_FIN064 N
  have hNpos : (0 : ℝ) < N := by exact_mod_cast N.pos
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK 0)
  have hterm : ∀ i : Fin N, (particlePartial i 0 (testFIN064 κ h t N) x) ^ 2 ≤
      K ^ 2 * (aFIN064 κ N) ^ 2 * (4 * Real.pi ^ 2) := by
    intro i
    rw [particlePartial_testFIN064]
    have h1 : |deriv chiFIN064 (aFIN064 κ N * harmonicTrial N x + bFIN064 h t N)| ≤ K := hK _
    have h2 : (deriv chiFIN064 (aFIN064 κ N * harmonicTrial N x + bFIN064 h t N)) ^ 2 ≤ K ^ 2 := by
      have := sq_le_sq' (abs_le.1 h1).1 (abs_le.1 h1).2
      exact this
    have h4 : ((mode 1 (x i)).im) ^ 2 ≤ 1 := by
      have := abs_mode_im_le_FIN064 (x i)
      nlinarith [sq_abs ((mode 1 (x i)).im), abs_nonneg ((mode 1 (x i)).im)]
    calc _ = (deriv chiFIN064 (aFIN064 κ N * harmonicTrial N x + bFIN064 h t N)) ^ 2 *
          (aFIN064 κ N) ^ 2 * (4 * Real.pi ^ 2) * ((mode 1 (x i)).im) ^ 2 := by ring
      _ ≤ K ^ 2 * (aFIN064 κ N) ^ 2 * (4 * Real.pi ^ 2) * 1 := by
          gcongr
      _ = _ := by ring
  calc _ ≤ ∑ _i : Fin N, K ^ 2 * (aFIN064 κ N) ^ 2 * (4 * Real.pi ^ 2) :=
        Finset.sum_le_sum fun i _ => hterm i
    _ = (N : ℝ) * (K ^ 2 * (aFIN064 κ N) ^ 2 * (4 * Real.pi ^ 2)) := by
        simp
    _ = K ^ 2 * (4 * Real.pi ^ 2) * κ ^ 2 * (N : ℝ) ^ (-(1 / 3 : ℝ)) := by
        rw [rpow_neg_third_FIN064, ← hsdef]
        unfold aFIN064
        rw [← hsdef, ← h3]
        field_simp

theorem abs_le_iff_FIN064 (N : ℕ+) (y c : ℝ) :
    |y| ≤ c * (N : ℝ) ^ (-(1 / 3 : ℝ)) ↔ |(N : ℝ) ^ (1 / 3 : ℝ) * y| ≤ c := by
  have hs := rpow_third_pos_FIN064 N
  rw [rpow_neg_third_FIN064, abs_mul, abs_of_pos hs, ← div_eq_mul_inv, le_div_iff₀ hs, mul_comm]


theorem weight_angEquivN_FIN064 (κ h : ℝ) (N : ℕ+) (x : ParticleSpace 1 N) :
    particleWeight (fun _ : AngCircle => (0 : ℝ)) ScalarFoldFIN063.cosVec_FIN063
        (ScalarFoldFIN063.D_FIN063 κ) (fun _ => h) N (angEquivN N x) =
      particleWeight ScalarFoldFIN060.uSFIN060 ScalarFoldFIN060.phiSFIN060
        (ScalarFoldFIN060.dSFIN060 κ) (ScalarFoldFIN060.hSFIN060 h) N x := by
  have hf : fieldSum ScalarFoldFIN063.cosVec_FIN063 (angEquivN N x) =
      fieldSum ScalarFoldFIN060.phiSFIN060 x := by
    unfold fieldSum
    refine Finset.sum_congr rfl fun i _ => ?_
    funext j
    simp [ScalarFoldFIN063.cosVec_FIN063, ScalarFoldFIN060.phiSFIN060, angEquivN_apply,
      ScalarFoldFIN060.scalarCos_eq_angCos_FIN060]
  unfold particleWeight
  rw [hf]
  have hD : ScalarFoldFIN063.D_FIN063 κ = ScalarFoldFIN060.dSFIN060 κ := rfl
  have hh : (fun _ : Fin 1 => h) = ScalarFoldFIN060.hSFIN060 h := rfl
  rw [hD, hh]
  simp [ScalarFoldFIN060.uSFIN060]

theorem hubbard_transfer_FIN064 (κ h : ℝ) (N : ℕ+) (T : Set (Fin N → AngCircle)) :
    hubbardParticleLaw (ScalarFoldFIN063.D_FIN063 κ) (fun _ => h)
        (fun _ : AngCircle => (0 : ℝ)) ScalarFoldFIN063.cosVec_FIN063 angHaar N T =
      hubbardParticleLaw (ScalarFoldFIN060.dSFIN060 κ) (ScalarFoldFIN060.hSFIN060 h)
        ScalarFoldFIN060.uSFIN060 ScalarFoldFIN060.phiSFIN060 (haar 1) N (angEquivN N ⁻¹' T) := by
  have hmp := measurePreserving_angEquivN N
  have hemb := (angEquivN N).measurableEmbedding
  have hmass : particleMass (ScalarFoldFIN063.D_FIN063 κ) (fun _ => h)
      (fun _ : AngCircle => (0 : ℝ)) ScalarFoldFIN063.cosVec_FIN063 angHaar N =
      particleMass (ScalarFoldFIN060.dSFIN060 κ) (ScalarFoldFIN060.hSFIN060 h)
        ScalarFoldFIN060.uSFIN060 ScalarFoldFIN060.phiSFIN060 (haar 1) N := by
    unfold particleMass
    have := hmp.lintegral_comp_emb hemb
      (fun θ => ENNReal.ofReal (particleWeight (fun _ : AngCircle => (0 : ℝ))
        ScalarFoldFIN063.cosVec_FIN063 (ScalarFoldFIN063.D_FIN063 κ) (fun _ => h) N θ))
    simp only [weight_angEquivN_FIN064] at this
    exact this.symm
  unfold hubbardParticleLaw
  rw [hmass]
  simp only [Measure.smul_apply, smul_eq_mul]
  congr 1
  rw [withDensity_apply' _ T, withDensity_apply' _ (angEquivN N ⁻¹' T)]
  have := hmp.setLIntegral_comp_preimage_emb hemb
    (fun θ => ENNReal.ofReal (particleWeight (fun _ : AngCircle => (0 : ℝ))
        ScalarFoldFIN063.cosVec_FIN063 (ScalarFoldFIN063.D_FIN063 κ) (fun _ => h) N θ)) T
  simp only [weight_angEquivN_FIN064] at this
  exact this.symm


/-- The scaled box `{x : |a_N F_N(x) + b_N| ≤ c}`. -/
def boxFIN064 (κ h t : ℝ) (N : ℕ+) (c : ℝ) : Set (ParticleSpace 1 N) :=
  {x | |aFIN064 κ N * harmonicTrial N x + bFIN064 h t N| ≤ c}

theorem measurableSet_box_FIN064 (κ h t : ℝ) (N : ℕ+) (c : ℝ) :
    MeasurableSet (boxFIN064 κ h t N c) := by
  have hc : Continuous fun x : ParticleSpace 1 N =>
      |aFIN064 κ N * harmonicTrial N x + bFIN064 h t N| :=
    continuous_abs.comp ((continuous_const.mul (continuous_harmonicTrial N)).add continuous_const)
  exact measurableSet_le hc.measurable measurable_const

theorem box_eq_FIN064 (κ h t : ℝ) (N : ℕ+) (c : ℝ) :
    boxFIN064 κ h t N c = {x | |posteriorCenter (ScalarFoldFIN060.dSFIN060 κ)
      (ScalarFoldFIN060.hSFIN060 h) ScalarFoldFIN060.phiSFIN060 N x 0 - t| ≤
        c * (N : ℝ) ^ (-(1 / 3 : ℝ))} := by
  ext x
  simp only [boxFIN064, Set.mem_ofPred_eq]
  rw [abs_le_iff_FIN064, scaled_eq_FIN064]

theorem fieldSum_angEquivN_FIN064 (N : ℕ+) (x : ParticleSpace 1 N) :
    fieldSum ScalarFoldFIN063.cosVec_FIN063 (angEquivN N x) =
      fieldSum ScalarFoldFIN060.phiSFIN060 x := by
  unfold fieldSum
  refine Finset.sum_congr rfl fun i _ => ?_
  funext j
  simp [ScalarFoldFIN063.cosVec_FIN063, ScalarFoldFIN060.phiSFIN060, angEquivN_apply,
    ScalarFoldFIN060.scalarCos_eq_angCos_FIN060]

theorem posteriorCenter_angEquivN_FIN064 (κ h : ℝ) (N : ℕ+) (x : ParticleSpace 1 N) :
    posteriorCenter (ScalarFoldFIN063.D_FIN063 κ) (fun _ => h) ScalarFoldFIN063.cosVec_FIN063 N
        (angEquivN N x) =
      posteriorCenter (ScalarFoldFIN060.dSFIN060 κ) (ScalarFoldFIN060.hSFIN060 h)
        ScalarFoldFIN060.phiSFIN060 N x := by
  unfold posteriorCenter
  rw [fieldSum_angEquivN_FIN064]
  rfl

theorem masses_FIN064 (κ : ℝ) (hκ : 2 < κ) :
    ∃ Δ : ℝ, 0 < Δ ∧ ∃ c Cm : ℝ, 0 < c ∧ 0 < Cm ∧ ∃ N₀ : ℕ, ∀ N : ℕ+, N₀ ≤ (N : ℕ) →
      c * DGPS.FiniteN.RareCutoff.rareMass (1 / 6) Δ N ≤
          (particleLaw (scalarCosineFold κ) N).real
            (boxFIN064 κ (scalarFoldField κ) (-scalarFoldPoint κ) N 1) ∧
      (particleLaw (scalarCosineFold κ) N).real
          (boxFIN064 κ (scalarFoldField κ) (-scalarFoldPoint κ) N 2) ≤
        Cm * DGPS.FiniteN.RareCutoff.rareMass (1 / 6) Δ N := by
  obtain ⟨tp, Δ, htp, hmin, hΔeq, hΔ, C, hC, M0, hM0, hsup⟩ :=
    DGPS.FiniteN.fold_empirical_support_upper_by_posterior κ hκ
  obtain ⟨tp', Δ', htp', hmin', hΔeq', hΔ', c, hc, M1, hM1, hcore⟩ :=
    DGPS.FiniteN.fold_empirical_core_lower_by_conditional_variance κ hκ
  have htt : tp' = tp := by
    by_contra hne
    exact lt_asymm (hmin' tp (Ne.symm hne)) (hmin tp' hne)
  subst htt
  have hΔΔ : Δ' = Δ := hΔeq'.trans hΔeq.symm
  subst hΔΔ
  have hlaw : ∀ N : ℕ+, hubbardParticleLaw (ScalarFoldFIN060.dSFIN060 κ)
      (ScalarFoldFIN060.hSFIN060 (scalarFoldField κ)) ScalarFoldFIN060.uSFIN060
      ScalarFoldFIN060.phiSFIN060 (haar 1) N = particleLaw (scalarCosineFold κ) N :=
    fun N => ScalarFoldFIN060.hubbardParticleLaw_eq_particleLaw_FIN060
      (ScalarFoldFIN060.particleWeight_FIN060 κ (scalarFoldField κ) N)
  refine ⟨Δ', hΔ', c, C, hc, hC, ⌈max M0 M1⌉₊, fun N hN => ?_⟩
  have hNr : max M0 M1 ≤ (N : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hN)
  constructor
  · have h1 := hcore N ((le_max_right _ _).trans hNr)
    rw [hubbard_transfer_FIN064] at h1
    have hset : angEquivN N ⁻¹' {x | |posteriorCenter (ScalarFoldFIN063.D_FIN063 κ)
        (fun _ => scalarFoldField κ) ScalarFoldFIN063.cosVec_FIN063 N x 0 - -scalarFoldPoint κ| ≤
          (N : ℝ) ^ (-(1 / 3 : ℝ))} =
        boxFIN064 κ (scalarFoldField κ) (-scalarFoldPoint κ) N 1 := by
      rw [box_eq_FIN064, one_mul]
      ext x
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, posteriorCenter_angEquivN_FIN064]
    rw [hset, hlaw] at h1
    unfold DGPS.FiniteN.RareCutoff.rareMass
    rw [Measure.real, ← mul_assoc]
    exact h1
  · have h1 := hsup N ((le_max_left _ _).trans hNr)
    rw [hlaw, ← box_eq_FIN064] at h1
    have := ENNReal.toReal_le_of_le_ofReal (by positivity) h1
    unfold DGPS.FiniteN.RareCutoff.rareMass
    rw [Measure.real, ← mul_assoc]
    exact this


theorem harmonicTrial_permute_FIN064 {N : ℕ+} (σ : Equiv.Perm (Fin N)) (x : ParticleSpace 1 N) :
    harmonicTrial N (permuteParticles σ x) = harmonicTrial N x := by
  rw [harmonicTrial_eq_witness, DGPS.FiniteN.PositiveRate.witnessSum_permute]

theorem symmetric_FIN064 {A : InteractionData 1} {N : ℕ+} (f : ParticleH1 A N) (κ h t : ℝ)
    (hf : ∀ x, f x = chiFIN064 (aFIN064 κ N * harmonicTrial N x + bFIN064 h t N)) :
    IsSymmetricParticleTest f := by
  rw [isSymmetricParticleTest_iff f]
  intro σ
  refine Filter.Eventually.of_forall fun x => ?_
  show f (permuteParticles σ x) = f x
  rw [hf, hf, harmonicTrial_permute_FIN064]

theorem family_FIN064 (κ : ℝ) :
    ∃ f : (N : ℕ+) → ParticleH1 (scalarCosineFold κ) N,
      (∀ N x, f N x = chiFIN064 (aFIN064 κ N * harmonicTrial N x +
        bFIN064 (scalarFoldField κ) (-scalarFoldPoint κ) N)) ∧
      ∀ N, particleEnergy (scalarCosineFold κ) N (f N) =
        ∫ x, ∑ i, (particlePartial i 0
          (testFIN064 κ (scalarFoldField κ) (-scalarFoldPoint κ) N) x) ^ 2
          ∂particleLaw (scalarCosineFold κ) N := by
  have h : ∀ N : ℕ+, ∃ f : ParticleH1 (scalarCosineFold κ) N,
      f.1 = testFIN064 κ (scalarFoldField κ) (-scalarFoldPoint κ) N ∧
      particleEnergy (scalarCosineFold κ) N f = ∫ x, ∑ i, (particlePartial i 0
          (testFIN064 κ (scalarFoldField κ) (-scalarFoldPoint κ) N) x) ^ 2
          ∂particleLaw (scalarCosineFold κ) N := fun N => by
    obtain ⟨f, hf1, hf2⟩ := smooth_h1_FIN064 (scalarCosineFold κ) N
      (isSmooth_testFIN064 κ (scalarFoldField κ) (-scalarFoldPoint κ) N)
    exact ⟨f, hf1, hf2⟩
  choose f hf1 hf2 using h
  refine ⟨f, fun N x => ?_, hf2⟩
  show (f N).1 x = _
  rw [hf1 N]
  rfl

theorem energy_le_FIN064 {K : ℝ} (hK : ∀ u, |deriv chiFIN064 u| ≤ K) (κ h t : ℝ) (N : ℕ+)
    (A : InteractionData 1) :
    ∫ x, ∑ i, (particlePartial i 0 (testFIN064 κ h t N) x) ^ 2 ∂particleLaw A N ≤
      K ^ 2 * (4 * Real.pi ^ 2) * κ ^ 2 * (N : ℝ) ^ (-(1 / 3 : ℝ)) *
        (particleLaw A N).real (boxFIN064 κ h t N 2) := by
  have : IsProbabilityMeasure (particleLaw A N) := DGPS.Particle.particleLaw_isProbabilityMeasure' A N
  have hbox := measurableSet_box_FIN064 κ h t N 2
  have hind : Integrable ((boxFIN064 κ h t N 2).indicator fun _ =>
      K ^ 2 * (4 * Real.pi ^ 2) * κ ^ 2 * (N : ℝ) ^ (-(1 / 3 : ℝ))) (particleLaw A N) :=
    (integrable_const _).indicator hbox
  calc ∫ x, ∑ i, (particlePartial i 0 (testFIN064 κ h t N) x) ^ 2 ∂particleLaw A N
      ≤ ∫ x, (boxFIN064 κ h t N 2).indicator (fun _ =>
          K ^ 2 * (4 * Real.pi ^ 2) * κ ^ 2 * (N : ℝ) ^ (-(1 / 3 : ℝ))) x ∂particleLaw A N := by
        refine integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun x => Finset.sum_nonneg fun i _ => sq_nonneg _) hind
          (Filter.Eventually.of_forall fun x => ?_)
        by_cases hx : x ∈ boxFIN064 κ h t N 2
        · rw [Set.indicator_of_mem hx]
          exact gradSq_le_FIN064 hK κ h t N x
        · rw [Set.indicator_of_notMem hx]
          have hx2 : 2 < |aFIN064 κ N * harmonicTrial N x + bFIN064 h t N| := by
            simpa [boxFIN064] using hx
          beta_reduce
          rw [gradSq_zero_FIN064 κ h t N x hx2]
    _ = _ := by
        rw [integral_indicator_const _ hbox, smul_eq_mul, mul_comm]

theorem rates_FIN064 (κ : ℝ) (hκ : 2 < κ) :
    ∃ C'' c1 c2 : ℝ, 0 < C'' ∧ 0 < c1 ∧ 0 < c2 ∧ ∃ N₂ : ℕ, ∀ N : ℕ+, N₂ ≤ (N : ℕ) →
      (c1 * (N : ℝ) ^ (-(1 / 3 : ℝ)) ≤ (particlePoincareRate (scalarCosineFold κ) N).toReal ∧
        (particlePoincareRate (scalarCosineFold κ) N).toReal ≤ C'' * (N : ℝ) ^ (-(1 / 3 : ℝ))) ∧
      (c2 * (N : ℝ) ^ (-(4 / 3 : ℝ)) ≤ (particleRateAll (scalarCosineFold κ) N).toReal ∧
        (particleRateAll (scalarCosineFold κ) N).toReal ≤ C'' * (N : ℝ) ^ (-(4 / 3 : ℝ))) ∧
      (c2 * (N : ℝ) ^ (-(4 / 3 : ℝ)) ≤ (particleRateSym (scalarCosineFold κ) N).toReal ∧
        (particleRateSym (scalarCosineFold κ) N).toReal ≤ C'' * (N : ℝ) ^ (-(4 / 3 : ℝ))) := by
  have hκ0 : 0 < κ := by linarith
  obtain ⟨Δ, hΔ, c, Cm, hc, hCm, N₀, hmass⟩ := masses_FIN064 κ hκ
  obtain ⟨f, hfv, hfE⟩ := family_FIN064 κ
  obtain ⟨K, hK0, hK⟩ := deriv_chi_bound_FIN064
  have hK' : ∀ u, |deriv chiFIN064 u| ≤ K + 1 := fun u => (hK u).trans (by linarith)
  have hs := fun N : ℕ+ => rpow_third_pos_FIN064 N
  have hf0 : ∀ N : ℕ+, N₀ ≤ (N : ℕ) → ∀ x, 0 ≤ f N x := fun N _ x => by
    rw [hfv]; exact chi_nonneg_FIN064 _
  have hf1 : ∀ N : ℕ+, N₀ ≤ (N : ℕ) → ∀ x, f N x ≤ 1 := fun N _ x => by
    rw [hfv]; exact chi_le_one_FIN064 _
  have hfC : ∀ N : ℕ+, N₀ ≤ (N : ℕ) → ∀ x, x ∈ boxFIN064 κ (scalarFoldField κ)
      (-scalarFoldPoint κ) N 1 → f N x = 1 := fun N _ x hx => by
    rw [hfv]; exact chi_one_FIN064 hx
  have hfS : ∀ N : ℕ+, N₀ ≤ (N : ℕ) → ∀ x, x ∉ boxFIN064 κ (scalarFoldField κ)
      (-scalarFoldPoint κ) N 2 → f N x = 0 := fun N _ x hx => by
    rw [hfv]; exact chi_zero_FIN064 (not_le.1 hx)
  have hE : ∀ N : ℕ+, N₀ ≤ (N : ℕ) → particleEnergy (scalarCosineFold κ) N (f N) ≤
      ((K + 1) ^ 2 * (4 * Real.pi ^ 2) * κ ^ 2 * Cm / c) * ((N : ℕ) : ℝ) ^ (-(1 / 3 : ℝ)) *
        ∫ x, f N x ^ 2 ∂particleLaw (scalarCosineFold κ) N := by
    intro N hN
    obtain ⟨hm1, hm2⟩ := hmass N hN
    have hmem : MemLp (f N).1 2 (particleLaw (scalarCosineFold κ) N) :=
      (isParticleWeakGradient_particleWeakGradient (f N)).memLp
    have hn : c * DGPS.FiniteN.RareCutoff.rareMass (1 / 6) Δ N ≤
        ∫ x, f N x ^ 2 ∂particleLaw (scalarCosineFold κ) N :=
      hm1.trans (DGPS.FiniteN.RareCutoff.measureReal_le_integral_sq
        (measurableSet_box_FIN064 _ _ _ _ _) hmem (hfC N hN))
    rw [hfE N]
    refine (energy_le_FIN064 hK' κ _ _ N (scalarCosineFold κ)).trans ?_
    have hq : 0 ≤ (K + 1) ^ 2 * (4 * Real.pi ^ 2) * κ ^ 2 * (N : ℝ) ^ (-(1 / 3 : ℝ)) :=
      mul_nonneg (by positivity) (Real.rpow_nonneg (by positivity) _)
    have hm : DGPS.FiniteN.RareCutoff.rareMass (1 / 6) Δ N ≤
        (∫ x, f N x ^ 2 ∂particleLaw (scalarCosineFold κ) N) / c := by
      rw [le_div_iff₀ hc]; linarith
    calc (K + 1) ^ 2 * (4 * Real.pi ^ 2) * κ ^ 2 * (N : ℝ) ^ (-(1 / 3 : ℝ)) *
          (particleLaw (scalarCosineFold κ) N).real
            (boxFIN064 κ (scalarFoldField κ) (-scalarFoldPoint κ) N 2)
        ≤ (K + 1) ^ 2 * (4 * Real.pi ^ 2) * κ ^ 2 * (N : ℝ) ^ (-(1 / 3 : ℝ)) *
          (Cm * ((∫ x, f N x ^ 2 ∂particleLaw (scalarCosineFold κ) N) / c)) :=
          mul_le_mul_of_nonneg_left (hm2.trans (mul_le_mul_of_nonneg_left hm hCm.le)) hq
      _ = _ := by ring
  have hsym : ∀ N : ℕ+, N₀ ≤ (N : ℕ) → IsSymmetricParticleTest (f N) := fun N _ =>
    symmetric_FIN064 (f N) κ _ _ (hfv N)
  obtain ⟨-, h18⟩ := DGPS.FiniteN.rare_cutoff_variance_and_entropy_weights (scalarCosineFold κ) f
    (fun N => boxFIN064 κ (scalarFoldField κ) (-scalarFoldPoint κ) N 1)
    (fun N => boxFIN064 κ (scalarFoldField κ) (-scalarFoldPoint κ) N 2) (1 / 6) Δ c Cm hΔ hc N₀
    (fun N => measurableSet_box_FIN064 _ _ _ _ _) (fun N => measurableSet_box_FIN064 _ _ _ _ _)
    hf0 hf1 hfC hfS (fun N hN => (hmass N hN).1) (fun N hN => (hmass N hN).2)
  obtain ⟨C'', hC'', N₂, hN₂⟩ := h18 (1 / 3) ((K + 1) ^ 2 * (4 * Real.pi ^ 2) * κ ^ 2 * Cm / c)
    (by positivity) hE
  obtain ⟨-, ⟨c1, hc1, hlow1⟩, ⟨c2, hc2, hlow2⟩⟩ :=
    DGPS.FiniteN.fold_auxiliary_and_particle_lower_powers hκ
  have e : (-((1 : ℝ) / 3 + 1)) = -(4 / 3 : ℝ) := by norm_num
  refine ⟨C'', c1, c2, hC'', hc1, hc2, N₂, fun N hN => ?_⟩
  obtain ⟨⟨hP1, hP2⟩, hS⟩ := hN₂ N hN
  obtain ⟨hS1, hS2⟩ := hS hsym
  rw [e] at hS1 hS2
  have hPtop : particlePoincareRate (scalarCosineFold κ) N ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hP1
  have hStop : particleRateSym (scalarCosineFold κ) N ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hS1
  have hAS : particleRateAll (scalarCosineFold κ) N ≤ particleRateSym (scalarCosineFold κ) N :=
    DGPS.particleRateAll_le_sym _ N
  have hAtop : particleRateAll (scalarCosineFold κ) N ≠ ⊤ := ne_top_of_le_ne_top hStop hAS
  have hASr := ENNReal.toReal_mono hStop hAS
  have hAl : c2 * (N : ℝ) ^ (-(4 / 3 : ℝ)) ≤ (particleRateAll (scalarCosineFold κ) N).toReal :=
    (ENNReal.ofReal_le_iff_le_toReal hAtop).1 (hlow2 N)
  exact ⟨⟨(ENNReal.ofReal_le_iff_le_toReal hPtop).1 (hlow1 N), hP2⟩, ⟨hAl, hASr.trans hS2⟩,
    ⟨hAl.trans hASr, hS2⟩⟩

end DGPS.FiniteN.ScalarFoldFIN064

namespace DGPS.FiniteN

open DGPS DGPS.Models DGPS.FiniteN.Tools.Hubbard DGPS.FiniteN.Tools.GaussianCoupling
  DGPS.FiniteN.ScalarFoldFIN064

/-- **FIN064.** For every fixed `κ > 2` at the fold field `h = h_c(κ)` of the scalar cosine model:

* (test functions) there is a smooth profile `χ` (`0 ≤ χ ≤ 1`, `χ = 1` on `[-1, 1]`, `χ = 0`
  outside `[-2, 2]`) and a constant `C` such that for every `N` the test
  `f_N = χ (N^{1/3} (z_N - t*))`, `z_N = posteriorCenter ...`, `t* = -scalarFoldPoint κ`, is an
  `H¹` test function, symmetric under particle permutations, and satisfies
  `Σ_i |∂_{x_i} f_N|² ≤ C N^{-1/3} 1_{S_N}` pointwise, `S_N = {|z_N - t*| ≤ 2 N^{-1/3}}`;
* (exact power row) `λ_N = Θ(N^{-1/3})` and `r_N^all`, `r_N^sym` are `Θ(N^{-4/3})`. -/
theorem fold_symmetric_test_and_exact_power_row (κ : ℝ) (hκ : 2 < κ) :
    (∃ χ : ℝ → ℝ, ContDiff ℝ ∞ χ ∧ (∀ u, 0 ≤ χ u ∧ χ u ≤ 1) ∧ (∀ u, |u| ≤ 1 → χ u = 1) ∧
      (∀ u, 2 < |u| → χ u = 0) ∧
      ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ+, ∃ f : ParticleH1 (scalarCosineFold κ) N,
        (∀ x, f x = χ ((N : ℝ) ^ (1 / 3 : ℝ) *
          (posteriorCenter (ScalarFoldFIN060.dSFIN060 κ)
            (ScalarFoldFIN060.hSFIN060 (scalarFoldField κ)) ScalarFoldFIN060.phiSFIN060 N x 0 -
              (-scalarFoldPoint κ)))) ∧
        (∀ (σ : Equiv.Perm (Fin N)) x, f (permuteParticles σ x) = f x) ∧
        IsSymmetricParticleTest f ∧
        ∀ x, ∑ i, (particlePartial i 0 f.1 x) ^ 2 ≤
          if |posteriorCenter (ScalarFoldFIN060.dSFIN060 κ)
              (ScalarFoldFIN060.hSFIN060 (scalarFoldField κ)) ScalarFoldFIN060.phiSFIN060 N x 0 -
                (-scalarFoldPoint κ)| ≤ 2 * (N : ℝ) ^ (-(1 / 3 : ℝ))
          then C * (N : ℝ) ^ (-(1 / 3 : ℝ)) else 0) ∧
    ThetaScale (1 / 3) (fun n : ℕ => if h : 0 < n then
      (particlePoincareRate (scalarCosineFold κ) ⟨n, h⟩).toReal else 0) ∧
    ThetaScale (4 / 3) (fun n : ℕ => if h : 0 < n then
      (particleRateAll (scalarCosineFold κ) ⟨n, h⟩).toReal else 0) ∧
    ThetaScale (4 / 3) (fun n : ℕ => if h : 0 < n then
      (particleRateSym (scalarCosineFold κ) ⟨n, h⟩).toReal else 0) := by
  have hκ0 : 0 < κ := by linarith
  refine ⟨?_, ?_⟩
  · obtain ⟨f, hfv, -⟩ := family_FIN064 κ
    obtain ⟨K, hK0, hK⟩ := deriv_chi_bound_FIN064
    refine ⟨chiFIN064, chi_contDiff_FIN064, fun u => ⟨chi_nonneg_FIN064 u, chi_le_one_FIN064 u⟩,
      fun u hu => chi_one_FIN064 hu, fun u hu => chi_zero_FIN064 hu,
      (K + 1) ^ 2 * (4 * Real.pi ^ 2) * κ ^ 2, by positivity, fun N => ⟨f N, ?_, ?_, ?_, ?_⟩⟩
    · intro x
      rw [hfv, ← scaled_eq_FIN064]
    · intro σ x
      rw [hfv, hfv, harmonicTrial_permute_FIN064]
    · exact symmetric_FIN064 (f N) κ _ _ (hfv N)
    · intro x
      have hf1 : (f N).1 = testFIN064 κ (scalarFoldField κ) (-scalarFoldPoint κ) N :=
        funext fun y => hfv N y
      rw [hf1]
      split_ifs with hx
      · have hxb : x ∈ boxFIN064 κ (scalarFoldField κ) (-scalarFoldPoint κ) N 2 := by
          rw [box_eq_FIN064]; exact hx
        exact gradSq_le_FIN064 (fun u => (hK u).trans (by linarith)) κ _ _ N x
      · have hnb : x ∉ boxFIN064 κ (scalarFoldField κ) (-scalarFoldPoint κ) N 2 := by
          rw [box_eq_FIN064]; exact hx
        have hx2 : 2 < |aFIN064 κ N * harmonicTrial N x +
            bFIN064 (scalarFoldField κ) (-scalarFoldPoint κ) N| := by
          simpa [boxFIN064] using hnb
        exact (gradSq_zero_FIN064 κ _ _ N x hx2).le
  · obtain ⟨C'', c1, c2, hC'', hc1, hc2, N₂, hN₂⟩ := rates_FIN064 κ hκ
    have key : ∀ n : ℕ, max N₂ 1 ≤ n → ∃ hn0 : 0 < n,
        let N : ℕ+ := ⟨n, hn0⟩
        ((c1 * (n : ℝ) ^ (-(1 / 3 : ℝ)) ≤ (particlePoincareRate (scalarCosineFold κ) N).toReal ∧
          (particlePoincareRate (scalarCosineFold κ) N).toReal ≤ C'' * (n : ℝ) ^ (-(1 / 3 : ℝ))) ∧
        (c2 * (n : ℝ) ^ (-(4 / 3 : ℝ)) ≤ (particleRateAll (scalarCosineFold κ) N).toReal ∧
          (particleRateAll (scalarCosineFold κ) N).toReal ≤ C'' * (n : ℝ) ^ (-(4 / 3 : ℝ))) ∧
        (c2 * (n : ℝ) ^ (-(4 / 3 : ℝ)) ≤ (particleRateSym (scalarCosineFold κ) N).toReal ∧
          (particleRateSym (scalarCosineFold κ) N).toReal ≤ C'' * (n : ℝ) ^ (-(4 / 3 : ℝ)))) :=
      fun n hn => ⟨lt_of_lt_of_le one_pos ((le_max_right _ _).trans hn),
        hN₂ ⟨n, lt_of_lt_of_le one_pos ((le_max_right _ _).trans hn)⟩ ((le_max_left _ _).trans hn)⟩
    refine ⟨⟨c1, C'', hc1, hC'', max N₂ 1, le_max_right _ _, fun n hn => ?_⟩,
      ⟨c2, C'', hc2, hC'', max N₂ 1, le_max_right _ _, fun n hn => ?_⟩,
      ⟨c2, C'', hc2, hC'', max N₂ 1, le_max_right _ _, fun n hn => ?_⟩⟩
    · obtain ⟨hn0, h1, -, -⟩ := key n hn
      simp only [hn0, ↓reduceDIte]
      exact h1
    · obtain ⟨hn0, -, h2, -⟩ := key n hn
      simp only [hn0, ↓reduceDIte]
      exact h2
    · obtain ⟨hn0, -, -, h3⟩ := key n hn
      simp only [hn0, ↓reduceDIte]
      exact h3

end DGPS.FiniteN
