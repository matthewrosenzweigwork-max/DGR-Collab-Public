import DGPS.FiniteN.EmpiricalCosineCramerFIN080
import DGPS.FiniteN.FalseMinimum
import DGPS.FiniteN.ScalarCosine

/-!
# FIN081: Gibbs empirical rate and critical heights

For the scalar-cosine particle law `particleLaw (scalarCosine κ h) N` on the unit torus, the empirical
cosine `m_N = N⁻¹ ∑ cos θᵢ` obeys the closed/open large-deviation bounds with rate
`J(m) = I(m) - h m - κ m²/2 - min_u [I(u) - h u - κ u²/2]`, `I` the Cramér rate of FIN080.

The Gibbs measure is the Haar measure tilted by `exp (N (h m_N + κ m_N²/2))`; the tilt is bounded and
continuous on `[-1,1]`, so the upper bound uses the FIN080 finite cover and the lower bound uses an
open neighbourhood of a near-minimiser (a direct Laplace argument).  For `κ > 2`, `0 < h < h_c(κ)`, the
critical points of `U = I - h m - κ m²/2` correspond to those of `ψ_h` under `m = g(t)`, and the
roots of FIN076 give the zero `m_+ = g(t_+)` and the heights `G_-`, `G_- + B`.
-/

open MeasureTheory Filter Topology
open DGPS.Circle.AngularNormalization DGPS.Circle.BesselMoments DGPS.Circle.BesselMonotonicity
  DGPS.Circle.BesselConcavity
open DGPS.FiniteN.UnitTorusNormalization DGPS.FiniteN.EmpiricalCosineCramerFIN080
open DGPS.Models

namespace DGPS.FiniteN.FalseMinimumFIN081

/-- The Gibbs tilt `Φ(m) = h m + κ m²/2`. -/
noncomputable def tiltFIN081 (κ h m : ℝ) : ℝ := h * m + κ * m ^ 2 / 2

/-- The tilt weight `exp (N Φ(m_N))` on the angular torus. -/
noncomputable def weightFIN081 (κ h : ℝ) (N : ℕ+) (θ : AngParticleSpace N) : ℝ :=
  Real.exp ((N : ℝ) * tiltFIN081 κ h (empCos N θ))

/-- The tilted (unnormalised) measure. -/
noncomputable def tiltMeasFIN081 (κ h : ℝ) (N : ℕ+) : Measure (AngParticleSpace N) :=
  (angParticleHaar N).withDensity fun θ => ENNReal.ofReal (weightFIN081 κ h N θ)

/-- The empirical cosine on the unit-torus particle space. -/
noncomputable def empTorusFIN081 (N : ℕ+) (x : DGPS.ParticleSpace 1 N) : ℝ :=
  (N : ℝ)⁻¹ * ∑ i, scalarCos (x i)

theorem scalarCos_eq_angCos_FIN081 (y : DGPS.Torus 1) : scalarCos y = angCos (angEquiv y) := by
  obtain ⟨r, hr⟩ := QuotientAddGroup.mk_surjective (y 0)
  have h1 : scalarCos y = Real.cos (2 * Real.pi * r) := by
    have h : y 0 = ((r : ℝ) : UnitAddCircle) := hr.symm
    rw [scalarCos, h, fourier_coe_apply]
    have : (2 * Real.pi * Complex.I * ((1:ℤ) : ℂ) * (r : ℂ) / ((1 : ℝ) : ℂ)) = ((2 * Real.pi * r : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [this, Complex.exp_ofReal_mul_I_re]
  rw [h1, angEquiv_apply, ← hr, angRescale_mk]
  change _ = angMode 1 _
  rw [angMode_coe]; simp

theorem empCos_angEquivN_FIN081 (N : ℕ+) (x : DGPS.ParticleSpace 1 N) :
    empCos N (angEquivN N x) = empTorusFIN081 N x := by
  unfold empCos sumCos empTorusFIN081
  simp [angEquivN_apply, scalarCos_eq_angCos_FIN081]

theorem exp_neg_hamiltonian_FIN081 (κ h : ℝ) (N : ℕ+) (x : DGPS.ParticleSpace 1 N) :
    Real.exp (-DGPS.particleHamiltonian (scalarCosine κ h) N x) =
      weightFIN081 κ h N (angEquivN N x) := by
  rw [scalarCosine_hamiltonian, weightFIN081, empCos_angEquivN_FIN081]
  unfold empTorusFIN081 tiltFIN081
  congr 1
  have hN : (N : ℝ) ≠ 0 := by positivity
  field_simp
  ring

theorem continuous_tilt_FIN081 (κ h : ℝ) : Continuous (tiltFIN081 κ h) := by
  unfold tiltFIN081; fun_prop

theorem measurable_weight_FIN081 (κ h : ℝ) (N : ℕ+) : Measurable (weightFIN081 κ h N) := by
  have := continuous_tilt_FIN081 κ h
  unfold weightFIN081
  have h2 := continuous_empCos N
  fun_prop

theorem particleLaw_preimage_FIN081 (κ h : ℝ) (N : ℕ+) {T : Set (AngParticleSpace N)}
    (hT : MeasurableSet T) :
    DGPS.particleLaw (scalarCosine κ h) N (angEquivN N ⁻¹' T) =
      ENNReal.ofReal (DGPS.particlePartition (scalarCosine κ h) N)⁻¹ * tiltMeasFIN081 κ h N T := by
  rw [DGPS.particleLaw, withDensity_apply _ ((angEquivN N).measurable hT), tiltMeasFIN081,
    withDensity_apply _ hT]
  have hz : ∀ x, ENNReal.ofReal (DGPS.particleDensity (scalarCosine κ h) N x) =
      ENNReal.ofReal (DGPS.particlePartition (scalarCosine κ h) N)⁻¹ *
        ENNReal.ofReal (weightFIN081 κ h N (angEquivN N x)) := by
    intro x
    rw [DGPS.particleDensity, exp_neg_hamiltonian_FIN081,
      ENNReal.ofReal_mul (inv_nonneg.2 (DGPS.Particle.particlePartition_pos _ N).le)]
  simp_rw [hz]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  congr 1
  exact (measurePreserving_angEquivN N).setLIntegral_comp_preimage_emb
    (angEquivN N).measurableEmbedding (fun θ => ENNReal.ofReal (weightFIN081 κ h N θ)) T

theorem tiltMeas_univ_FIN081 (κ h : ℝ) (N : ℕ+) :
    ENNReal.ofReal (DGPS.particlePartition (scalarCosine κ h) N)⁻¹ * tiltMeasFIN081 κ h N Set.univ = 1 := by
  have := particleLaw_preimage_FIN081 κ h N (T := Set.univ) MeasurableSet.univ
  rw [Set.preimage_univ, measure_univ] at this
  exact this.symm

theorem particleLaw_emp_FIN081 (κ h : ℝ) (N : ℕ+) {S : Set ℝ} (hS : MeasurableSet S) :
    DGPS.particleLaw (scalarCosine κ h) N {x | empTorusFIN081 N x ∈ S} =
      (tiltMeasFIN081 κ h N Set.univ)⁻¹ * tiltMeasFIN081 κ h N {θ | empCos N θ ∈ S} := by
  have hT : MeasurableSet {θ : AngParticleSpace N | empCos N θ ∈ S} :=
    (continuous_empCos N).measurable hS
  have h1 : {x : DGPS.ParticleSpace 1 N | empTorusFIN081 N x ∈ S} =
      angEquivN N ⁻¹' {θ | empCos N θ ∈ S} := by
    ext x; simp [empCos_angEquivN_FIN081]
  rw [h1, particleLaw_preimage_FIN081 κ h N hT]
  congr 1
  exact (ENNReal.eq_inv_of_mul_eq_one_left (tiltMeas_univ_FIN081 κ h N))


/-! ### Tilt bounds -/

theorem abs_tilt_le_FIN081 (κ h : ℝ) {m : ℝ} (hm : |m| ≤ 1) : |tiltFIN081 κ h m| ≤ |h| + |κ| := by
  unfold tiltFIN081
  have h1 : |h * m| ≤ |h| := by
    rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) hm
  have h2 : |κ * m ^ 2 / 2| ≤ |κ| := by
    rw [abs_div, abs_mul, abs_pow]
    have : |m| ^ 2 ≤ 1 := pow_le_one₀ (abs_nonneg _) hm
    have h3 : |κ| * |m| ^ 2 ≤ |κ| := mul_le_of_le_one_right (abs_nonneg _) this
    have : |(2 : ℝ)| = 2 := abs_of_pos (by norm_num)
    rw [this]
    linarith [abs_nonneg κ]
  calc |h * m + κ * m ^ 2 / 2| ≤ |h * m| + |κ * m ^ 2 / 2| := abs_add_le _ _
    _ ≤ |h| + |κ| := add_le_add h1 h2

theorem abs_tilt_sub_le_FIN081 (κ h : ℝ) {x y : ℝ} (hx : |x| ≤ 1) (hy : |y| ≤ 1) :
    |tiltFIN081 κ h x - tiltFIN081 κ h y| ≤ (|h| + |κ|) * |x - y| := by
  have e : tiltFIN081 κ h x - tiltFIN081 κ h y = (x - y) * (h + κ * ((x + y) / 2)) := by
    unfold tiltFIN081; ring
  rw [e, abs_mul, mul_comm]
  apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
  have h1 : |κ * ((x + y) / 2)| ≤ |κ| := by
    rw [abs_mul]
    apply mul_le_of_le_one_right (abs_nonneg _)
    rw [abs_div]
    have : |x + y| ≤ 2 := (abs_add_le x y).trans (by linarith)
    have h2 : |(2:ℝ)| = 2 := abs_of_pos (by norm_num)
    rw [h2]
    linarith
  calc |h + κ * ((x + y) / 2)| ≤ |h| + |κ * ((x + y) / 2)| := abs_add_le _ _
    _ ≤ |h| + |κ| := by linarith

/-! ### Weighted Chernoff bound -/

theorem tilt_set_upper_FIN081 (κ h : ℝ) (N : ℕ+) {A : Set ℝ} (hA : IsOpen A) {s c : ℝ}
    (hAs : ∀ y ∈ A, tiltFIN081 κ h y + c ≤ s * y - logI0 s) :
    tiltMeasFIN081 κ h N {θ | empCos N θ ∈ A} ≤ ENNReal.ofReal (Real.exp (-((N : ℝ) * c))) := by
  have : IsProbabilityMeasure (angParticleHaar N) := by unfold angParticleHaar; infer_instance
  have hT : MeasurableSet {θ : AngParticleSpace N | empCos N θ ∈ A} :=
    (continuous_empCos N).measurable hA.measurableSet
  have hN : (0 : ℝ) < N := by positivity
  rw [tiltMeasFIN081, withDensity_apply _ hT]
  set b : ℝ := -((N : ℝ) * logI0 s) - (N : ℝ) * c with hb
  calc ∫⁻ θ in {θ : AngParticleSpace N | empCos N θ ∈ A}, ENNReal.ofReal (weightFIN081 κ h N θ)
          ∂angParticleHaar N
      ≤ ∫⁻ θ in {θ : AngParticleSpace N | empCos N θ ∈ A},
          ENNReal.ofReal (Real.exp (s * sumCos N θ + b)) ∂angParticleHaar N := by
        refine setLIntegral_mono' hT fun θ hθ => ENNReal.ofReal_le_ofReal ?_
        have h1 := hAs _ hθ
        unfold weightFIN081
        apply Real.exp_le_exp.2
        have h2 : (N : ℝ) * (tiltFIN081 κ h (empCos N θ) + c) ≤
            (N : ℝ) * (s * empCos N θ - logI0 s) := mul_le_mul_of_nonneg_left h1 hN.le
        have h3 : (N : ℝ) * (s * empCos N θ) = s * sumCos N θ := by
          rw [← N_mul_empCos]; ring
        rw [hb]
        nlinarith
    _ ≤ ∫⁻ θ, ENNReal.ofReal (Real.exp (s * sumCos N θ + b)) ∂angParticleHaar N :=
        setLIntegral_le_lintegral _ _
    _ = ENNReal.ofReal (∫ θ, Real.exp (s * sumCos N θ + b) ∂angParticleHaar N) := by
        rw [ofReal_integral_eq_lintegral_ofReal (integrable_exp_affine N s b)
          (Eventually.of_forall fun θ => (Real.exp_pos _).le)]
    _ = ENNReal.ofReal (Real.exp (-((N : ℝ) * c))) := by
        rw [integral_exp_affine, hb]
        congr 2
        ring

/-! ### Weighted cover -/

theorem tilt_cover_point_FIN081 (κ h : ℝ) {c x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1)
    (hc : ((c + tiltFIN081 κ h x : ℝ) : EReal) < cramerRate x) :
    ∃ s : ℝ, ∃ A : Set ℝ, IsOpen A ∧ x ∈ A ∧ ∀ y ∈ A, tiltFIN081 κ h y + c ≤ s * y - logI0 s := by
  obtain ⟨c1, hc1, hc2⟩ := EReal.lt_iff_exists_real_btwn.1 hc
  have hc1' : c + tiltFIN081 κ h x < c1 := EReal.coe_lt_coe_iff.1 hc1
  obtain ⟨s, A0, hA0, hs⟩ := cover_point hx hc2
  refine ⟨s, interior A0 ∩ {y | tiltFIN081 κ h y < c1 - c}, isOpen_interior.inter
    (isOpen_lt (continuous_tilt_FIN081 κ h) continuous_const), ⟨mem_interior_iff_mem_nhds.2 hA0, ?_⟩,
    fun y hy => ?_⟩
  · show tiltFIN081 κ h x < c1 - c
    linarith
  · have h1 := hs y (interior_subset hy.1)
    have h2 : tiltFIN081 κ h y < c1 - c := hy.2
    linarith

theorem tilt_upper_cover_FIN081 (κ h : ℝ) {K : Set ℝ} (hK : IsClosed K) {c : ℝ}
    (hc : ∀ x ∈ K, ((c + tiltFIN081 κ h x : ℝ) : EReal) < cramerRate x) :
    ∃ C : ℕ, ∀ N : ℕ+, tiltMeasFIN081 κ h N {θ | empCos N θ ∈ K} ≤
      (C : ENNReal) * ENNReal.ofReal (Real.exp (-((N : ℝ) * c))) := by
  have hcomp : IsCompact (K ∩ Set.Icc (-1 : ℝ) 1) := isCompact_Icc.inter_left hK
  have key : ∀ x : ℝ, ∃ (s : ℝ) (A : Set ℝ),
      x ∈ K ∩ Set.Icc (-1 : ℝ) 1 → (IsOpen A ∧ x ∈ A) ∧
        ∀ y ∈ A, tiltFIN081 κ h y + c ≤ s * y - logI0 s := by
    intro x
    by_cases hx : x ∈ K ∩ Set.Icc (-1 : ℝ) 1
    · obtain ⟨s, A, hA, hxA, h⟩ := tilt_cover_point_FIN081 κ h hx.2 (hc x hx.1)
      exact ⟨s, A, fun _ => ⟨⟨hA, hxA⟩, h⟩⟩
    · exact ⟨0, ∅, fun h => absurd h hx⟩
  choose S A hA using key
  obtain ⟨t, ht, hsub⟩ := hcomp.elim_nhds_subcover A
    (fun x hx => (hA x hx).1.1.mem_nhds (hA x hx).1.2)
  refine ⟨t.card, fun N => ?_⟩
  have h1 : {θ : AngParticleSpace N | empCos N θ ∈ K} ⊆
      ⋃ x ∈ t, {θ : AngParticleSpace N | empCos N θ ∈ A x} := by
    intro θ hθ
    have hmem : empCos N θ ∈ K ∩ Set.Icc (-1 : ℝ) 1 := ⟨hθ, abs_le.1 (abs_empCos_le N θ)⟩
    have := hsub hmem
    simpa using this
  calc tiltMeasFIN081 κ h N {θ | empCos N θ ∈ K}
      ≤ tiltMeasFIN081 κ h N (⋃ x ∈ t, {θ : AngParticleSpace N | empCos N θ ∈ A x}) :=
        measure_mono h1
    _ ≤ ∑ x ∈ t, tiltMeasFIN081 κ h N {θ : AngParticleSpace N | empCos N θ ∈ A x} :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ _x ∈ t, ENNReal.ofReal (Real.exp (-((N : ℝ) * c))) :=
        Finset.sum_le_sum fun x hx =>
          tilt_set_upper_FIN081 κ h N (hA x (ht x hx)).1.1 (hA x (ht x hx)).2
    _ = (t.card : ENNReal) * ENNReal.ofReal (Real.exp (-((N : ℝ) * c))) := by simp


/-! ### Weighted lower bound -/

theorem tilt_lower_ball_FIN081 (κ h : ℝ) {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ+ in atTop,
      ENNReal.ofReal ((1 / 2 : ℝ) * Real.exp (-((N : ℝ) *
          (rateReal x - tiltFIN081 κ h x + (|h| + |κ| + |tInv x|) * ε)))) ≤
        tiltMeasFIN081 κ h N {θ | |empCos N θ - x| < ε} := by
  filter_upwards [lower_bound_point hx hε] with N hN
  have : IsProbabilityMeasure (angParticleHaar N) := by unfold angParticleHaar; infer_instance
  have hNpos : (0 : ℝ) < N := by positivity
  have hB := measurableSet_empCos_lt N x ε
  set L : ℝ := |h| + |κ| with hL
  set c0 : ℝ := Real.exp ((N : ℝ) * (tiltFIN081 κ h x - L * ε)) with hc0
  have hx1 : |x| ≤ 1 := abs_le.2 ⟨hx.1.le, hx.2.le⟩
  rw [tiltMeasFIN081, withDensity_apply _ hB]
  calc ENNReal.ofReal ((1 / 2 : ℝ) * Real.exp (-((N : ℝ) *
          (rateReal x - tiltFIN081 κ h x + (L + |tInv x|) * ε))))
      = ENNReal.ofReal c0 * ENNReal.ofReal ((1 / 2 : ℝ) * Real.exp (-((N : ℝ) * (rateReal x + |tInv x| * ε)))) := by
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
        congr 1
        have : Real.exp ((N : ℝ) * (tiltFIN081 κ h x - L * ε)) *
            ((1 / 2 : ℝ) * Real.exp (-((N : ℝ) * (rateReal x + |tInv x| * ε)))) =
            (1 / 2 : ℝ) * (Real.exp ((N : ℝ) * (tiltFIN081 κ h x - L * ε)) *
              Real.exp (-((N : ℝ) * (rateReal x + |tInv x| * ε)))) := by ring
        rw [this, ← Real.exp_add]
        congr 2
        ring
    _ ≤ ENNReal.ofReal c0 * angParticleHaar N {θ | |empCos N θ - x| < ε} := by
        gcongr
        calc ENNReal.ofReal ((1 / 2 : ℝ) * Real.exp (-((N : ℝ) * (rateReal x + |tInv x| * ε)))) ≤
            ENNReal.ofReal ((angParticleHaar N).real {θ | |empCos N θ - x| < ε}) :=
              ENNReal.ofReal_le_ofReal hN
          _ = _ := ofReal_measureReal (measure_ne_top _ _)
    _ = ∫⁻ θ in {θ : AngParticleSpace N | |empCos N θ - x| < ε}, ENNReal.ofReal c0 ∂angParticleHaar N := by
        rw [setLIntegral_const]
    _ ≤ _ := by
        refine setLIntegral_mono' hB fun θ hθ => ENNReal.ofReal_le_ofReal ?_
        have h1 : |empCos N θ - x| < ε := hθ
        have h2 := abs_tilt_sub_le_FIN081 κ h (abs_empCos_le N θ) hx1
        have h3 : |tiltFIN081 κ h (empCos N θ) - tiltFIN081 κ h x| ≤ L * ε :=
          h2.trans (mul_le_mul_of_nonneg_left h1.le (by positivity))
        have h4 := (abs_le.1 h3).1
        unfold weightFIN081
        rw [hc0]
        apply Real.exp_le_exp.2
        exact mul_le_mul_of_nonneg_left (by linarith) hNpos.le

/-! ### From bounds to `EReal` limits -/

theorem limsup_log_le_FIN081 {p : ℕ+ → ENNReal} {q c : ℝ} (hq : 0 < q)
    (h : ∀ᶠ N : ℕ+ in atTop, p N ≤ ENNReal.ofReal (q * Real.exp (-((N : ℝ) * c)))) :
    limsup (fun N : ℕ+ => (((N : ℝ)⁻¹ : ℝ) : EReal) * ENNReal.log (p N)) atTop ≤ ((-c : ℝ) : EReal) := by
  set u : ℕ+ → ℝ := fun N => ((N : ℕ) : ℝ)⁻¹ * Real.log q - c with hu
  have hle : ∀ᶠ N : ℕ+ in atTop,
      (((N : ℝ)⁻¹ : ℝ) : EReal) * ENNReal.log (p N) ≤ ((u N : ℝ) : EReal) := by
    filter_upwards [h] with N hN
    have hNpos : (0 : ℝ) < N := by positivity
    have hq' : 0 < q * Real.exp (-((N : ℝ) * c)) := by positivity
    refine (scaled_log_le (inv_nonneg.2 hNpos.le) hq' hN).trans ?_
    apply EReal.coe_le_coe_iff.2
    rw [Real.log_mul hq.ne' (Real.exp_pos _).ne', Real.log_exp, hu]
    field_simp
    ring_nf
    rfl
  have hlim : Tendsto (fun N : ℕ+ => ((u N : ℝ) : EReal)) atTop (𝓝 ((-c : ℝ) : EReal)) := by
    have : Tendsto u atTop (𝓝 (0 * Real.log q - c)) := (tendsto_inv_N.mul_const _).sub_const c
    rw [zero_mul, zero_sub] at this
    exact (continuous_coe_real_ereal.tendsto _).comp this
  calc limsup (fun N : ℕ+ => (((N : ℝ)⁻¹ : ℝ) : EReal) * ENNReal.log (p N)) atTop
      ≤ limsup (fun N : ℕ+ => ((u N : ℝ) : EReal)) atTop := limsup_le_limsup hle
    _ = ((-c : ℝ) : EReal) := hlim.limsup_eq

theorem le_liminf_log_FIN081 {p : ℕ+ → ENNReal} {q a : ℝ} (hq : 0 < q)
    (h : ∀ᶠ N : ℕ+ in atTop, ENNReal.ofReal (q * Real.exp (-((N : ℝ) * a))) ≤ p N) :
    ((-a : ℝ) : EReal) ≤
      liminf (fun N : ℕ+ => (((N : ℝ)⁻¹ : ℝ) : EReal) * ENNReal.log (p N)) atTop := by
  set v : ℕ+ → ℝ := fun N => ((N : ℕ) : ℝ)⁻¹ * Real.log q - a with hv
  have hlim : Tendsto (fun N : ℕ+ => ((v N : ℝ) : EReal)) atTop (𝓝 ((-a : ℝ) : EReal)) := by
    have : Tendsto v atTop (𝓝 (0 * Real.log q - a)) := (tendsto_inv_N.mul_const _).sub_const a
    rw [zero_mul, zero_sub] at this
    exact (continuous_coe_real_ereal.tendsto _).comp this
  have hev : ∀ᶠ N : ℕ+ in atTop,
      ((v N : ℝ) : EReal) ≤ (((N : ℝ)⁻¹ : ℝ) : EReal) * ENNReal.log (p N) := by
    filter_upwards [h] with N hN
    have hNpos : (0 : ℝ) < N := by positivity
    have hq' : 0 < q * Real.exp (-((N : ℝ) * a)) := by positivity
    refine le_trans ?_ (le_scaled_log (inv_nonneg.2 hNpos.le) hq' hN)
    apply EReal.coe_le_coe_iff.2
    rw [Real.log_mul hq.ne' (Real.exp_pos _).ne', Real.log_exp, hv]
    field_simp
    ring_nf
    rfl
  calc ((-a : ℝ) : EReal)
      = liminf (fun N : ℕ+ => ((v N : ℝ) : EReal)) atTop := hlim.liminf_eq.symm
    _ ≤ _ := liminf_le_liminf hev

/-! ### Normalised ratios in `ENNReal` -/

theorem ratio_upper_FIN081 {Z T : ENNReal} {z t : ℝ} (hz : 0 < z) (hZ : ENNReal.ofReal z ≤ Z)
    (hT : T ≤ ENNReal.ofReal t) : Z⁻¹ * T ≤ ENNReal.ofReal (z⁻¹ * t) := by
  have h1 : Z⁻¹ ≤ ENNReal.ofReal z⁻¹ := by
    rw [ENNReal.ofReal_inv_of_pos hz]
    exact ENNReal.inv_le_inv.2 hZ
  calc Z⁻¹ * T ≤ ENNReal.ofReal z⁻¹ * ENNReal.ofReal t := mul_le_mul' h1 hT
    _ = ENNReal.ofReal (z⁻¹ * t) := (ENNReal.ofReal_mul (inv_nonneg.2 hz.le)).symm

theorem ratio_lower_FIN081 {Z T : ENNReal} {z t : ℝ} (hz : 0 < z) (hZ : Z ≤ ENNReal.ofReal z)
    (hT : ENNReal.ofReal t ≤ T) : ENNReal.ofReal (z⁻¹ * t) ≤ Z⁻¹ * T := by
  have h1 : ENNReal.ofReal z⁻¹ ≤ Z⁻¹ := by
    rw [ENNReal.ofReal_inv_of_pos hz]
    exact ENNReal.inv_le_inv.2 hZ
  calc ENNReal.ofReal (z⁻¹ * t) = ENNReal.ofReal z⁻¹ * ENNReal.ofReal t :=
        ENNReal.ofReal_mul (inv_nonneg.2 hz.le)
    _ ≤ Z⁻¹ * T := mul_le_mul' h1 hT

theorem natCast_mul_ofReal_le_FIN081 (C : ℕ) (r : ℝ) :
    (C : ENNReal) * ENNReal.ofReal r ≤ ENNReal.ofReal (((C : ℝ) + 1) * r) := by
  by_cases hr : 0 ≤ r
  · rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_add (by positivity) (by norm_num)]
    simp only [ENNReal.ofReal_natCast, ENNReal.ofReal_one]
    gcongr
    exact le_self_add
  · rw [ENNReal.ofReal_of_nonpos (not_le.1 hr).le]
    simp


/-! ### The minimum of `I - Φ` -/

/-- `inf_u [I(u) - h u - κ u²/2]` as an extended real. -/
noncomputable def gibbsInfFIN081 (κ h : ℝ) : EReal :=
  ⨅ x : ℝ, (cramerRate x - ((tiltFIN081 κ h x : ℝ) : EReal))

/-- The real number `min_u [I(u) - h u - κ u²/2]` (finite, see `gibbsInf_eq_FIN081`). -/
noncomputable def gibbsMinFIN081 (κ h : ℝ) : ℝ := (gibbsInfFIN081 κ h).toReal

/-- The Gibbs empirical rate `J(m) = I(m) - h m - κ m²/2 - min_u [I(u) - h u - κ u²/2]`. -/
noncomputable def gibbsRateFIN081 (κ h m : ℝ) : EReal :=
  cramerRate m - ((tiltFIN081 κ h m + gibbsMinFIN081 κ h : ℝ) : EReal)

/-- `N⁻¹ log P_N(m_N ∈ S)` for the scalar cosine particle law. -/
noncomputable def gibbsLogProbFIN081 (κ h : ℝ) (N : ℕ+) (S : Set ℝ) : EReal :=
  (((N : ℝ)⁻¹ : ℝ) : EReal) *
    ENNReal.log (DGPS.particleLaw (scalarCosine κ h) N {x | empTorusFIN081 N x ∈ S})

theorem coe_lt_sub_coe_FIN081 (a b : ℝ) (e : EReal) :
    ((a : ℝ) : EReal) < e - (b : EReal) ↔ ((a + b : ℝ) : EReal) < e := by
  induction e using EReal.rec with
  | bot => simp [sub_eq_add_neg]
  | top => rw [EReal.top_sub_coe]; exact ⟨fun _ => EReal.coe_lt_top _, fun _ => EReal.coe_lt_top _⟩
  | coe r =>
    rw [← EReal.coe_sub, EReal.coe_lt_coe_iff, EReal.coe_lt_coe_iff]
    constructor <;> intro h <;> linarith

theorem coe_le_sub_coe_FIN081 (a b : ℝ) (e : EReal) :
    ((a : ℝ) : EReal) ≤ e - (b : EReal) ↔ ((a + b : ℝ) : EReal) ≤ e := by
  induction e using EReal.rec with
  | bot => simp [sub_eq_add_neg]
  | top => rw [EReal.top_sub_coe]; exact ⟨fun _ => le_top, fun _ => le_top⟩
  | coe r =>
    rw [← EReal.coe_sub, EReal.coe_le_coe_iff, EReal.coe_le_coe_iff]
    constructor <;> intro h <;> linarith

theorem rateReal_zero_FIN081 : rateReal 0 = 0 := by
  have h := tInv_ratio 0
  rw [ratio_zero] at h
  simp [rateReal, h, logI0_zero]

theorem zero_mem_Ioo_FIN081 : (0 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩

theorem sub_tilt_mem_FIN081 (κ h : ℝ) {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    cramerRate x - ((tiltFIN081 κ h x : ℝ) : EReal) = ((rateReal x - tiltFIN081 κ h x : ℝ) : EReal) := by
  rw [cramerRate_of_mem hx, ← EReal.coe_sub]

theorem sub_tilt_not_mem_FIN081 (κ h : ℝ) {x : ℝ} (hx : x ∉ Set.Ioo (-1 : ℝ) 1) :
    cramerRate x - ((tiltFIN081 κ h x : ℝ) : EReal) = ⊤ := by
  rw [cramerRate_of_not_mem hx]; exact EReal.top_sub_coe _

theorem gibbsInf_le_zero_FIN081 (κ h : ℝ) : gibbsInfFIN081 κ h ≤ ((0 : ℝ) : EReal) := by
  refine iInf_le_of_le 0 ?_
  rw [sub_tilt_mem_FIN081 κ h zero_mem_Ioo_FIN081, rateReal_zero_FIN081]
  apply EReal.coe_le_coe_iff.2
  simp [tiltFIN081]

theorem neg_le_gibbsInf_FIN081 (κ h : ℝ) :
    ((-(|h| + |κ|) : ℝ) : EReal) ≤ gibbsInfFIN081 κ h := by
  refine le_iInf fun x => ?_
  by_cases hx : x ∈ Set.Ioo (-1 : ℝ) 1
  · rw [sub_tilt_mem_FIN081 κ h hx]
    apply EReal.coe_le_coe_iff.2
    have h1 := rateReal_nonneg hx
    have h2 := abs_tilt_le_FIN081 κ h (abs_le.2 ⟨hx.1.le, hx.2.le⟩)
    have h3 := (abs_le.1 h2).2
    linarith
  · rw [sub_tilt_not_mem_FIN081 κ h hx]; exact le_top

theorem gibbsInf_eq_FIN081 (κ h : ℝ) :
    gibbsInfFIN081 κ h = ((gibbsMinFIN081 κ h : ℝ) : EReal) := by
  have h1 : gibbsInfFIN081 κ h ≠ ⊤ :=
    ne_top_of_le_ne_top (EReal.coe_ne_top 0) (gibbsInf_le_zero_FIN081 κ h)
  have h2 : gibbsInfFIN081 κ h ≠ ⊥ := by
    intro hb
    have := neg_le_gibbsInf_FIN081 κ h
    rw [hb] at this
    exact absurd (le_bot_iff.1 this) (EReal.coe_ne_bot _)
  exact (EReal.coe_toReal h1 h2).symm

theorem gibbsMin_le_FIN081 (κ h : ℝ) (x : ℝ) :
    ((gibbsMinFIN081 κ h + tiltFIN081 κ h x : ℝ) : EReal) ≤ cramerRate x := by
  have h1 : gibbsInfFIN081 κ h ≤ cramerRate x - ((tiltFIN081 κ h x : ℝ) : EReal) :=
    iInf_le (fun x : ℝ => cramerRate x - ((tiltFIN081 κ h x : ℝ) : EReal)) x
  rw [gibbsInf_eq_FIN081] at h1
  exact (coe_le_sub_coe_FIN081 _ _ _).1 h1

theorem exists_near_min_FIN081 (κ h : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ x ∈ Set.Ioo (-1 : ℝ) 1, rateReal x - tiltFIN081 κ h x < gibbsMinFIN081 κ h + δ := by
  have h1 : gibbsInfFIN081 κ h < ((gibbsMinFIN081 κ h + δ : ℝ) : EReal) := by
    rw [gibbsInf_eq_FIN081]; exact EReal.coe_lt_coe_iff.2 (by linarith)
  obtain ⟨x, hx⟩ := iInf_lt_iff.1 h1
  by_cases hI : x ∈ Set.Ioo (-1 : ℝ) 1
  · rw [sub_tilt_mem_FIN081 κ h hI] at hx
    exact ⟨x, hI, EReal.coe_lt_coe_iff.1 hx⟩
  · rw [sub_tilt_not_mem_FIN081 κ h hI] at hx
    exact absurd hx (not_lt.2 le_top)

/-! ### The normaliser -/

theorem tilt_ball_eta_FIN081 (κ h : ℝ) {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) {η ε0 : ℝ} (hη : 0 < η)
    (hε0 : 0 < ε0) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ ε0 ∧ ∀ᶠ N : ℕ+ in atTop,
      ENNReal.ofReal ((1 / 2 : ℝ) * Real.exp (-((N : ℝ) *
          (rateReal x - tiltFIN081 κ h x + η)))) ≤
        tiltMeasFIN081 κ h N {θ | |empCos N θ - x| < ε} := by
  set L' : ℝ := |h| + |κ| + |tInv x| with hL'
  have hL'0 : 0 ≤ L' := by positivity
  refine ⟨min ε0 (η / (L' + 1)), lt_min hε0 (by positivity), min_le_left _ _, ?_⟩
  filter_upwards [tilt_lower_ball_FIN081 κ h hx (lt_min hε0 (by positivity : 0 < η / (L' + 1)))]
    with N hN
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) hN
  have hNpos : (0 : ℝ) < N := by positivity
  have h1 : L' * min ε0 (η / (L' + 1)) ≤ η := by
    calc L' * min ε0 (η / (L' + 1)) ≤ L' * (η / (L' + 1)) :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) hL'0
      _ ≤ η := by
          rw [mul_div_assoc', div_le_iff₀ (by positivity)]
          nlinarith
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.exp_le_exp.2
  have : (N : ℝ) * (rateReal x - tiltFIN081 κ h x + L' * min ε0 (η / (L' + 1))) ≤
      (N : ℝ) * (rateReal x - tiltFIN081 κ h x + η) :=
    mul_le_mul_of_nonneg_left (by linarith) hNpos.le
  linarith

theorem normaliser_upper_FIN081 (κ h : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℕ, ∀ N : ℕ+, tiltMeasFIN081 κ h N Set.univ ≤
      ENNReal.ofReal (((C : ℝ) + 1) * Real.exp (-((N : ℝ) * (gibbsMinFIN081 κ h - δ)))) := by
  have hc : ∀ x ∈ (Set.univ : Set ℝ),
      ((gibbsMinFIN081 κ h - δ + tiltFIN081 κ h x : ℝ) : EReal) < cramerRate x := by
    intro x _
    refine lt_of_lt_of_le ?_ (gibbsMin_le_FIN081 κ h x)
    exact EReal.coe_lt_coe_iff.2 (by linarith)
  obtain ⟨C, hC⟩ := tilt_upper_cover_FIN081 κ h isClosed_univ hc
  refine ⟨C, fun N => ?_⟩
  refine le_trans ?_ (natCast_mul_ofReal_le_FIN081 C _)
  have := hC N
  simpa using this

theorem normaliser_lower_FIN081 (κ h : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ N : ℕ+ in atTop, ENNReal.ofReal ((1 / 2 : ℝ) *
      Real.exp (-((N : ℝ) * (gibbsMinFIN081 κ h + δ)))) ≤ tiltMeasFIN081 κ h N Set.univ := by
  obtain ⟨x, hx, hxδ⟩ := exists_near_min_FIN081 κ h (half_pos hδ)
  obtain ⟨ε, hε, -, hev⟩ := tilt_ball_eta_FIN081 κ h hx (half_pos hδ) one_pos
  filter_upwards [hev] with N hN
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) (hN.trans (measure_mono (Set.subset_univ _)))
  have hNpos : (0 : ℝ) < N := by positivity
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.exp_le_exp.2
  have : (N : ℝ) * (rateReal x - tiltFIN081 κ h x + δ / 2) ≤
      (N : ℝ) * (gibbsMinFIN081 κ h + δ) :=
    mul_le_mul_of_nonneg_left (by linarith) hNpos.le
  linarith


/-! ### The large-deviation bounds -/

theorem gibbsLogProb_eq_FIN081 (κ h : ℝ) (N : ℕ+) {S : Set ℝ} (hS : MeasurableSet S) :
    gibbsLogProbFIN081 κ h N S = (((N : ℝ)⁻¹ : ℝ) : EReal) *
      ENNReal.log ((tiltMeasFIN081 κ h N Set.univ)⁻¹ * tiltMeasFIN081 κ h N {θ | empCos N θ ∈ S}) := by
  rw [gibbsLogProbFIN081, particleLaw_emp_FIN081 κ h N hS]

theorem gibbs_upper_FIN081 (κ h : ℝ) {K : Set ℝ} (hK : IsClosed K) :
    limsup (fun N : ℕ+ => gibbsLogProbFIN081 κ h N K) atTop ≤ -(⨅ x ∈ K, gibbsRateFIN081 κ h x) := by
  refine ereal_le_neg_of_forall fun c hc => ?_
  obtain ⟨c'', hc1, hc2⟩ := EReal.lt_iff_exists_real_btwn.1 hc
  have hcc : c < c'' := EReal.coe_lt_coe_iff.1 hc1
  have hcover : ∀ x ∈ K, ((gibbsMinFIN081 κ h + c'' + tiltFIN081 κ h x : ℝ) : EReal) < cramerRate x := by
    intro x hx
    have h1 : ((c'' : ℝ) : EReal) < gibbsRateFIN081 κ h x := lt_of_lt_of_le hc2 (iInf₂_le x hx)
    rw [gibbsRateFIN081, coe_lt_sub_coe_FIN081] at h1
    have : gibbsMinFIN081 κ h + c'' + tiltFIN081 κ h x = c'' + (tiltFIN081 κ h x + gibbsMinFIN081 κ h) := by
      ring
    rw [this]; exact h1
  obtain ⟨C, hC⟩ := tilt_upper_cover_FIN081 κ h hK (c := gibbsMinFIN081 κ h + c'') hcover
  have hδ : 0 < c'' - c := by linarith
  have hq : 0 < 2 * ((C : ℝ) + 1) := by positivity
  have hlow := normaliser_lower_FIN081 κ h hδ
  have key : ∀ᶠ N : ℕ+ in atTop, (tiltMeasFIN081 κ h N Set.univ)⁻¹ *
      tiltMeasFIN081 κ h N {θ | empCos N θ ∈ K} ≤
      ENNReal.ofReal (2 * ((C : ℝ) + 1) * Real.exp (-((N : ℝ) * c))) := by
    filter_upwards [hlow] with N hN
    have hz : 0 < (1 / 2 : ℝ) * Real.exp (-((N : ℝ) * (gibbsMinFIN081 κ h + (c'' - c)))) := by positivity
    have hT : tiltMeasFIN081 κ h N {θ | empCos N θ ∈ K} ≤
        ENNReal.ofReal (((C : ℝ) + 1) * Real.exp (-((N : ℝ) * (gibbsMinFIN081 κ h + c'')))) :=
      (hC N).trans (natCast_mul_ofReal_le_FIN081 C _)
    refine (ratio_upper_FIN081 hz hN hT).trans (le_of_eq ?_)
    congr 1
    set E1 := Real.exp (-((N : ℝ) * (gibbsMinFIN081 κ h + (c'' - c)))) with hE1
    set Ec := Real.exp (-((N : ℝ) * c)) with hEc
    have hE2 : Real.exp (-((N : ℝ) * (gibbsMinFIN081 κ h + c''))) = E1 * Ec := by
      rw [hE1, hEc, ← Real.exp_add]; congr 1; ring
    have hE1pos : 0 < E1 := Real.exp_pos _
    rw [hE2]
    field_simp
  have hmeas : MeasurableSet K := hK.measurableSet
  have hfun : (fun N : ℕ+ => gibbsLogProbFIN081 κ h N K) = fun N : ℕ+ =>
      (((N : ℝ)⁻¹ : ℝ) : EReal) * ENNReal.log ((tiltMeasFIN081 κ h N Set.univ)⁻¹ *
        tiltMeasFIN081 κ h N {θ | empCos N θ ∈ K}) :=
    funext fun N => gibbsLogProb_eq_FIN081 κ h N hmeas
  rw [hfun]
  exact limsup_log_le_FIN081 hq key

theorem gibbsRate_of_mem_FIN081 (κ h : ℝ) {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    gibbsRateFIN081 κ h x =
      ((rateReal x - (tiltFIN081 κ h x + gibbsMinFIN081 κ h) : ℝ) : EReal) := by
  rw [gibbsRateFIN081, cramerRate_of_mem hx, ← EReal.coe_sub]

theorem gibbsRate_of_not_mem_FIN081 (κ h : ℝ) {x : ℝ} (hx : x ∉ Set.Ioo (-1 : ℝ) 1) :
    gibbsRateFIN081 κ h x = ⊤ := by
  rw [gibbsRateFIN081, cramerRate_of_not_mem hx]; exact EReal.top_sub_coe _

theorem gibbs_lower_eta_FIN081 (κ h : ℝ) {O : Set ℝ} (hO : IsOpen O) {x : ℝ}
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1) {ε0 : ℝ} (hε0 : 0 < ε0) (hball : Metric.ball x ε0 ⊆ O)
    {η : ℝ} (hη : 0 < η) :
    ((-(rateReal x - (tiltFIN081 κ h x + gibbsMinFIN081 κ h) + η) : ℝ) : EReal) ≤
      liminf (fun N : ℕ+ => gibbsLogProbFIN081 κ h N O) atTop := by
  obtain ⟨C, hC⟩ := normaliser_upper_FIN081 κ h (half_pos hη)
  obtain ⟨ε, hε, hεε0, hev⟩ := tilt_ball_eta_FIN081 κ h hx (half_pos hη) hε0
  have hq : 0 < 1 / (2 * ((C : ℝ) + 1)) := by positivity
  have key : ∀ᶠ N : ℕ+ in atTop, ENNReal.ofReal (1 / (2 * ((C : ℝ) + 1)) *
      Real.exp (-((N : ℝ) * (rateReal x - (tiltFIN081 κ h x + gibbsMinFIN081 κ h) + η)))) ≤
      (tiltMeasFIN081 κ h N Set.univ)⁻¹ * tiltMeasFIN081 κ h N {θ | empCos N θ ∈ O} := by
    filter_upwards [hev] with N hN
    have hz : 0 < ((C : ℝ) + 1) * Real.exp (-((N : ℝ) * (gibbsMinFIN081 κ h - η / 2))) := by
      positivity
    have hsub : {θ : AngParticleSpace N | |empCos N θ - x| < ε} ⊆ {θ | empCos N θ ∈ O} := by
      intro θ hθ
      apply hball
      rw [Metric.mem_ball, Real.dist_eq]
      exact lt_of_lt_of_le hθ hεε0
    have hT := hN.trans (measure_mono hsub)
    refine le_trans (le_of_eq ?_) (ratio_lower_FIN081 hz (hC N) hT)
    congr 1
    set E1 := Real.exp (-((N : ℝ) * (gibbsMinFIN081 κ h - η / 2))) with hE1
    set Ec := Real.exp (-((N : ℝ) * (rateReal x - (tiltFIN081 κ h x + gibbsMinFIN081 κ h) + η))) with hEc
    have hE2 : Real.exp (-((N : ℝ) * (rateReal x - tiltFIN081 κ h x + η / 2))) = E1 * Ec := by
      rw [hE1, hEc, ← Real.exp_add]; congr 1; ring
    have hE1pos : 0 < E1 := Real.exp_pos _
    rw [hE2]
    field_simp
  have hmeas : MeasurableSet O := hO.measurableSet
  have hfun : (fun N : ℕ+ => gibbsLogProbFIN081 κ h N O) = fun N : ℕ+ =>
      (((N : ℝ)⁻¹ : ℝ) : EReal) * ENNReal.log ((tiltMeasFIN081 κ h N Set.univ)⁻¹ *
        tiltMeasFIN081 κ h N {θ | empCos N θ ∈ O}) :=
    funext fun N => gibbsLogProb_eq_FIN081 κ h N hmeas
  rw [hfun]
  exact le_liminf_log_FIN081 hq key

theorem gibbs_lower_point_FIN081 (κ h : ℝ) {O : Set ℝ} (hO : IsOpen O) {x : ℝ} (hxO : x ∈ O)
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    ((-(rateReal x - (tiltFIN081 κ h x + gibbsMinFIN081 κ h)) : ℝ) : EReal) ≤
      liminf (fun N : ℕ+ => gibbsLogProbFIN081 κ h N O) atTop := by
  obtain ⟨ε0, hε0, hball⟩ := Metric.isOpen_iff.1 hO x hxO
  set R : ℝ := rateReal x - (tiltFIN081 κ h x + gibbsMinFIN081 κ h) with hR
  have hlim : Tendsto (fun η : ℝ => ((-(R + η) : ℝ) : EReal)) (𝓝[>] 0) (𝓝 ((-R : ℝ) : EReal)) := by
    have h1 : Tendsto (fun η : ℝ => -(R + η)) (𝓝[>] 0) (𝓝 (-R)) := by
      have : Tendsto (fun η : ℝ => -(R + η)) (𝓝 0) (𝓝 (-(R + 0))) :=
        (continuous_const.add continuous_id).neg.tendsto 0
      rw [add_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    exact (continuous_coe_real_ereal.tendsto _).comp h1
  refine le_of_tendsto hlim ?_
  filter_upwards [self_mem_nhdsWithin] with η hη
  exact gibbs_lower_eta_FIN081 κ h hO hx hε0 hball (η := η) hη

theorem gibbs_lower_FIN081 (κ h : ℝ) {O : Set ℝ} (hO : IsOpen O) :
    -(⨅ x ∈ O, gibbsRateFIN081 κ h x) ≤
      liminf (fun N : ℕ+ => gibbsLogProbFIN081 κ h N O) atTop := by
  rw [EReal.neg_le]
  refine le_iInf₂ fun x hx => ?_
  by_cases hI : x ∈ Set.Ioo (-1 : ℝ) 1
  · rw [gibbsRate_of_mem_FIN081 κ h hI, EReal.neg_le, ← EReal.coe_neg]
    exact gibbs_lower_point_FIN081 κ h hO hx hI
  · rw [gibbsRate_of_not_mem_FIN081 κ h hI]
    exact le_top

/-! ### The critical heights -/

open DGPS.FiniteN.FalseMinimumFIN076

/-- The effective potential `U(m) = I(m) - h m - κ m²/2` on `(-1,1)`. -/
noncomputable def ufFIN081 (κ h m : ℝ) : ℝ := rateReal m - tiltFIN081 κ h m

theorem hasDerivAt_uf_FIN081 (κ h : ℝ) {m : ℝ} (hm : m ∈ Set.Ioo (-1 : ℝ) 1) :
    HasDerivAt (ufFIN081 κ h) (tInv m - (h + κ * m)) m := by
  have h1 : HasDerivAt (tiltFIN081 κ h) (h + κ * m) m := by
    have := ((hasDerivAt_id m).const_mul h).add (((hasDerivAt_id m).pow 2).const_mul κ |>.div_const 2)
    refine this.congr_deriv ?_
    simp only [id]
    ring
  exact (hasDerivAt_rateReal hm).sub h1

theorem continuousOn_uf_FIN081 (κ h : ℝ) : ContinuousOn (ufFIN081 κ h) (Set.Ioo (-1 : ℝ) 1) :=
  fun _ hx => (hasDerivAt_uf_FIN081 κ h hx).continuousAt.continuousWithinAt

theorem exists_minimizer_FIN081 (κ h : ℝ) :
    ∃ m ∈ Set.Ioo (-1 : ℝ) 1, ∀ x ∈ Set.Ioo (-1 : ℝ) 1, ufFIN081 κ h m ≤ ufFIN081 κ h x := by
  obtain ⟨δ1, hδ1, h1⟩ := exists_rate_ge_right (|h| + |κ| + 1)
  obtain ⟨δ2, hδ2, h2⟩ := exists_rate_ge_left (|h| + |κ| + 1)
  set δ := min (min δ1 δ2) (1 / 2) with hδ
  have hδ0 : 0 < δ := lt_min (lt_min hδ1 hδ2) (by norm_num)
  have hδa : δ ≤ δ1 := (min_le_left _ _).trans (min_le_left _ _)
  have hδb : δ ≤ δ2 := (min_le_left _ _).trans (min_le_right _ _)
  have hδc : δ ≤ 1 / 2 := min_le_right _ _
  have hKsub : Set.Icc (-1 + δ) (1 - δ) ⊆ Set.Ioo (-1 : ℝ) 1 := fun x hx =>
    ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hKne : (Set.Icc (-1 + δ) (1 - δ)).Nonempty := ⟨0, by constructor <;> linarith⟩
  obtain ⟨m, hmK, hmin⟩ := isCompact_Icc.exists_isMinOn hKne
    ((continuousOn_uf_FIN081 κ h).mono hKsub)
  have h0K : (0 : ℝ) ∈ Set.Icc (-1 + δ) (1 - δ) := by constructor <;> linarith
  have hm0 : ufFIN081 κ h m ≤ 0 := by
    have := hmin h0K
    simpa [ufFIN081, rateReal_zero_FIN081, tiltFIN081] using this
  refine ⟨m, hKsub hmK, fun x hx => ?_⟩
  by_cases hxK : x ∈ Set.Icc (-1 + δ) (1 - δ)
  · exact hmin hxK
  · have hbig : 1 ≤ ufFIN081 κ h x := by
      have hx1 : |x| ≤ 1 := abs_le.2 ⟨hx.1.le, hx.2.le⟩
      have ht := abs_tilt_le_FIN081 κ h hx1
      have hr : |h| + |κ| + 1 ≤ rateReal x := by
        by_cases hl : x < -1 + δ
        · exact h2 x ⟨hx.1, by linarith⟩
        · have hr' : 1 - δ < x := by
            by_contra hc
            exact hxK ⟨not_lt.1 hl, not_lt.1 hc⟩
          exact h1 x ⟨by linarith, hx.2⟩
      unfold ufFIN081
      have := le_abs_self (tiltFIN081 κ h x)
      linarith
    linarith

theorem critical_of_min_FIN081 (κ h : ℝ) {m : ℝ} (hm : m ∈ Set.Ioo (-1 : ℝ) 1)
    (hmin : ∀ x ∈ Set.Ioo (-1 : ℝ) 1, ufFIN081 κ h m ≤ ufFIN081 κ h x) :
    tInv m = h + κ * m := by
  have hloc : IsLocalMin (ufFIN081 κ h) m :=
    Filter.mem_of_superset (Ioo_mem_nhds hm.1 hm.2) fun x hx => hmin x hx
  have := hloc.hasDerivAt_eq_zero (hasDerivAt_uf_FIN081 κ h hm)
  linarith

theorem ratio_mem_FIN081 (t : ℝ) : besselRatio t ∈ Set.Ioo (-1 : ℝ) 1 :=
  ⟨neg_one_lt_ratio t, besselRatio_lt_one t⟩

theorem uf_ratio_FIN081 {κ : ℝ} (hκ : κ ≠ 0) (h : ℝ) {t : ℝ}
    (ht : DGPS.FiniteN.ScalarFoldFIN056.psiDerivFIN056 κ h t = 0) :
    ufFIN081 κ h (besselRatio t) = scalarPsi κ h t := by
  unfold DGPS.FiniteN.ScalarFoldFIN056.psiDerivFIN056 at ht
  have hg : t = h + κ * besselRatio t := by
    field_simp at ht
    linarith
  unfold ufFIN081 rateReal tiltFIN081 scalarPsi
  rw [tInv_ratio]
  unfold logI0
  generalize besselRatio t = g at hg ⊢
  subst hg
  field_simp
  ring

theorem tInv_of_ratio_FIN081 {m : ℝ} (hm : m ∈ Set.Ioo (-1 : ℝ) 1) : besselRatio (tInv m) = m :=
  ratio_tInv hm

theorem psiDeriv_zero_FIN081 {κ : ℝ} (hκ : κ ≠ 0) (h : ℝ) {t : ℝ}
    (ht : t = h + κ * besselRatio t) :
    DGPS.FiniteN.ScalarFoldFIN056.psiDerivFIN056 κ h t = 0 := by
  unfold DGPS.FiniteN.ScalarFoldFIN056.psiDerivFIN056
  have : t - h = κ * besselRatio t := by linarith
  rw [this]
  field_simp
  ring

theorem psiDeriv_zero_of_deriv_FIN081 {κ : ℝ} (hκ : 0 < κ) (h : ℝ) {t : ℝ}
    (ht : deriv (scalarPsi κ h) t = 0) :
    DGPS.FiniteN.ScalarFoldFIN056.psiDerivFIN056 κ h t = 0 := by
  rwa [DGPS.FiniteN.ScalarFoldFIN056.deriv_scalarPsi_FIN056 hκ] at ht

/-- The global minimum of `U` over `(-1,1)` is attained at `g(t_+)`, and equals `ψ(t_+)`. -/
theorem min_at_tp_FIN081 {κ h s1 s2 tp : ℝ} (hκ : 0 < κ)
    (hG : FalseMinimumGeometryFIN076 κ h s1 s2 tp) :
    ufFIN081 κ h (besselRatio tp) = scalarPsi κ h tp ∧
      ∀ x ∈ Set.Ioo (-1 : ℝ) 1, scalarPsi κ h tp ≤ ufFIN081 κ h x := by
  obtain ⟨-, -, htp, -, -, -, ⟨-, hglob⟩, -⟩ := hG
  have hpd : DGPS.FiniteN.ScalarFoldFIN056.psiDerivFIN056 κ h tp = 0 :=
    psiDeriv_zero_FIN081 hκ.ne' h htp
  have hUp : ufFIN081 κ h (besselRatio tp) = scalarPsi κ h tp := uf_ratio_FIN081 hκ.ne' h hpd
  refine ⟨hUp, ?_⟩
  obtain ⟨m, hm, hmin⟩ := exists_minimizer_FIN081 κ h
  have hcrit := critical_of_min_FIN081 κ h hm hmin
  have hgm : besselRatio (tInv m) = m := ratio_tInv hm
  have hpd' : DGPS.FiniteN.ScalarFoldFIN056.psiDerivFIN056 κ h (tInv m) = 0 := by
    refine psiDeriv_zero_FIN081 hκ.ne' h ?_
    rw [hgm]; exact hcrit
  have hUm : ufFIN081 κ h m = scalarPsi κ h (tInv m) := by
    have := uf_ratio_FIN081 hκ.ne' h hpd'
    rwa [hgm] at this
  have h1 : scalarPsi κ h tp ≤ scalarPsi κ h (tInv m) := by
    by_cases he : tInv m = tp
    · rw [he]
    · exact (hglob _ he).le
  have h2 : ufFIN081 κ h m ≤ scalarPsi κ h tp := by
    rw [← hUp]; exact hmin _ (ratio_mem_FIN081 tp)
  intro x hx
  have := hmin x hx
  linarith

/-- Every zero of `U - ψ(t_+)` on `(-1,1)` is `g(t_+)`. -/
theorem unique_min_FIN081 {κ h s1 s2 tp : ℝ} (hκ : 0 < κ)
    (hG : FalseMinimumGeometryFIN076 κ h s1 s2 tp) {m : ℝ} (hm : m ∈ Set.Ioo (-1 : ℝ) 1)
    (hUm : ufFIN081 κ h m = scalarPsi κ h tp) : m = besselRatio tp := by
  obtain ⟨-, hglob⟩ := min_at_tp_FIN081 hκ hG
  have hmin : ∀ x ∈ Set.Ioo (-1 : ℝ) 1, ufFIN081 κ h m ≤ ufFIN081 κ h x :=
    fun x hx => hUm ▸ hglob x hx
  have hcrit := critical_of_min_FIN081 κ h hm hmin
  have hgm : besselRatio (tInv m) = m := ratio_tInv hm
  have hpd' : DGPS.FiniteN.ScalarFoldFIN056.psiDerivFIN056 κ h (tInv m) = 0 := by
    refine psiDeriv_zero_FIN081 hκ.ne' h ?_
    rw [hgm]; exact hcrit
  have hUm' : ufFIN081 κ h m = scalarPsi κ h (tInv m) := by
    have := uf_ratio_FIN081 hκ.ne' h hpd'
    rwa [hgm] at this
  have hstrict := hG.2.2.2.2.2.2.1.2
  have : tInv m = tp := by
    by_contra hne
    have := hstrict _ hne
    linarith
  rw [← hgm, this]

theorem gibbsMin_eq_FIN081 {κ h s1 s2 tp : ℝ} (hκ : 0 < κ)
    (hG : FalseMinimumGeometryFIN076 κ h s1 s2 tp) :
    gibbsMinFIN081 κ h = scalarPsi κ h tp := by
  obtain ⟨hU, hglob⟩ := min_at_tp_FIN081 hκ hG
  have hinf : gibbsInfFIN081 κ h = ((scalarPsi κ h tp : ℝ) : EReal) := by
    apply le_antisymm
    · refine iInf_le_of_le (besselRatio tp) ?_
      rw [sub_tilt_mem_FIN081 κ h (ratio_mem_FIN081 tp)]
      exact EReal.coe_le_coe_iff.2 (le_of_eq (by rw [← hU]; rfl))
    · refine le_iInf fun x => ?_
      by_cases hx : x ∈ Set.Ioo (-1 : ℝ) 1
      · rw [sub_tilt_mem_FIN081 κ h hx]
        exact EReal.coe_le_coe_iff.2 (hglob x hx)
      · rw [sub_tilt_not_mem_FIN081 κ h hx]; exact le_top
  rw [gibbsInf_eq_FIN081] at hinf
  exact EReal.coe_injective hinf

theorem gibbsRate_eq_FIN081 {κ h s1 s2 tp : ℝ} (hκ : 0 < κ)
    (hG : FalseMinimumGeometryFIN076 κ h s1 s2 tp) {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    gibbsRateFIN081 κ h x = ((ufFIN081 κ h x - scalarPsi κ h tp : ℝ) : EReal) := by
  rw [gibbsRate_of_mem_FIN081 κ h hx, gibbsMin_eq_FIN081 hκ hG]
  congr 1
  unfold ufFIN081
  ring

theorem gibbsRate_nonneg_FIN081 {κ h s1 s2 tp : ℝ} (hκ : 0 < κ)
    (hG : FalseMinimumGeometryFIN076 κ h s1 s2 tp) (x : ℝ) : 0 ≤ gibbsRateFIN081 κ h x := by
  by_cases hx : x ∈ Set.Ioo (-1 : ℝ) 1
  · rw [gibbsRate_eq_FIN081 hκ hG hx]
    have := (min_at_tp_FIN081 hκ hG).2 x hx
    exact EReal.coe_nonneg.2 (by linarith)
  · rw [gibbsRate_of_not_mem_FIN081 κ h hx]; exact le_top

theorem gibbsRate_zero_iff_FIN081 {κ h s1 s2 tp : ℝ} (hκ : 0 < κ)
    (hG : FalseMinimumGeometryFIN076 κ h s1 s2 tp) {m : ℝ} :
    gibbsRateFIN081 κ h m = 0 ↔ m = besselRatio tp := by
  constructor
  · intro h0
    by_cases hm : m ∈ Set.Ioo (-1 : ℝ) 1
    · rw [gibbsRate_eq_FIN081 hκ hG hm] at h0
      have : ufFIN081 κ h m - scalarPsi κ h tp = 0 := by exact_mod_cast h0
      exact unique_min_FIN081 hκ hG hm (by linarith)
    · rw [gibbsRate_of_not_mem_FIN081 κ h hm] at h0
      exact absurd h0 (by simp)
  · intro hm
    subst hm
    rw [gibbsRate_eq_FIN081 hκ hG (ratio_mem_FIN081 tp), (min_at_tp_FIN081 hκ hG).1]
    simp

/-- The rate at `g(t)` for a critical point `t` of `ψ` is `ψ(t) - ψ(t_+)`. -/
theorem gibbsRate_critical_FIN081 {κ h s1 s2 tp : ℝ} (hκ : 0 < κ)
    (hG : FalseMinimumGeometryFIN076 κ h s1 s2 tp) {t : ℝ}
    (ht : deriv (scalarPsi κ h) t = 0) :
    gibbsRateFIN081 κ h (besselRatio t) = ((scalarPsi κ h t - scalarPsi κ h tp : ℝ) : EReal) := by
  rw [gibbsRate_eq_FIN081 hκ hG (ratio_mem_FIN081 t),
    uf_ratio_FIN081 hκ.ne' h (psiDeriv_zero_of_deriv_FIN081 hκ h ht)]

end DGPS.FiniteN.FalseMinimumFIN081

namespace DGPS.FiniteN

open DGPS.FiniteN.FalseMinimumFIN081 DGPS.FiniteN.FalseMinimumFIN076 DGPS.Models
open DGPS.FiniteN.EmpiricalCosineCramerFIN080 DGPS.FiniteN.ScalarFoldFIN056

/-- **Gibbs empirical rate and critical heights.**

Part 1 (all `κ`, `h`): for the scalar-cosine particle law `particleLaw (scalarCosine κ h) N`,
the empirical cosine `m_N = N⁻¹ ∑ cos θ_i` obeys the closed/open large-deviation bounds
with rate `J(m) = I(m) - h m - κ m²/2 - min_u [I(u) - h u - κ u²/2]`, where `I = cramerRate`
(`⊤` outside `(-1,1)`), and the minimum is a finite real number.

Part 2 (`κ > 2`, `0 < h < h_c(κ)`): with the roots `s1 < s_* < s2` and `t_+` of `FalseMinimumGeometryFIN076`
(`t_- = -s2`, `t_b = -s1`), the minimum equals `ψ(t_+)`, `J ≥ 0` with unique zero `m_+ = g(t_+)`,
`J(g(t_-)) = G_- > 0`, and `J(g(t_b)) = G_- + B` with `B > 0`. -/
theorem gibbs_empirical_rate_and_critical_heights :
    (∀ κ h : ℝ,
      ((gibbsMinFIN081 κ h : ℝ) : EReal) =
          ⨅ u : ℝ, (cramerRate u - ((tiltFIN081 κ h u : ℝ) : EReal)) ∧
      (∀ K : Set ℝ, IsClosed K →
        Filter.limsup (fun N : ℕ+ => gibbsLogProbFIN081 κ h N K) Filter.atTop ≤
          -(⨅ x ∈ K, gibbsRateFIN081 κ h x)) ∧
      (∀ O : Set ℝ, IsOpen O →
        -(⨅ x ∈ O, gibbsRateFIN081 κ h x) ≤
          Filter.liminf (fun N : ℕ+ => gibbsLogProbFIN081 κ h N O) Filter.atTop)) ∧
    (∀ κ h : ℝ, 2 < κ → 0 < h → h < scalarFoldField κ →
      ∃ s1 s2 tp : ℝ, 0 < s1 ∧ s1 < scalarFoldPoint κ ∧ scalarFoldPoint κ < s2 ∧ 0 < tp ∧
        FalseMinimumGeometryFIN076 κ h s1 s2 tp ∧
        gibbsMinFIN081 κ h = scalarPsi κ h tp ∧
        (∀ m : ℝ, 0 ≤ gibbsRateFIN081 κ h m) ∧
        gibbsRateFIN081 κ h (besselRatio tp) = 0 ∧
        (∀ m : ℝ, gibbsRateFIN081 κ h m = 0 → m = besselRatio tp) ∧
        ∃ G B : ℝ, 0 < G ∧ 0 < B ∧
          G = scalarPsi κ h (-s2) - scalarPsi κ h tp ∧
          B = scalarPsi κ h (-s1) - scalarPsi κ h (-s2) ∧
          gibbsRateFIN081 κ h (besselRatio (-s2)) = (G : EReal) ∧
          gibbsRateFIN081 κ h (besselRatio (-s1)) = ((G + B : ℝ) : EReal)) := by
  refine ⟨fun κ h => ⟨?_, fun K hK => gibbs_upper_FIN081 κ h hK,
    fun O hO => gibbs_lower_FIN081 κ h hO⟩, ?_⟩
  · rw [← gibbsInf_eq_FIN081]; rfl
  · intro κ h hκ hh0 hhc
    obtain ⟨s1, s2, tp, hs1, hs1', hs2', htp, hG⟩ := general_FIN076 κ h hκ hh0 hhc
    have hκ0 : 0 < κ := by linarith
    refine ⟨s1, s2, tp, hs1, hs1', hs2', htp, hG, gibbsMin_eq_FIN081 hκ0 hG,
      gibbsRate_nonneg_FIN081 hκ0 hG, (gibbsRate_zero_iff_FIN081 hκ0 hG).2 rfl,
      fun m hm => (gibbsRate_zero_iff_FIN081 hκ0 hG).1 hm, ?_⟩
    obtain ⟨-, -, -, hcrit, -, -, -, ⟨hB, -⟩, ⟨hGpos, -⟩⟩ := id hG
    refine ⟨scalarPsi κ h (-s2) - scalarPsi κ h tp, scalarPsi κ h (-s1) - scalarPsi κ h (-s2),
      hGpos, hB, rfl, rfl, ?_, ?_⟩
    · exact gibbsRate_critical_FIN081 hκ0 hG ((hcrit _).2 (Or.inl rfl))
    · rw [gibbsRate_critical_FIN081 hκ0 hG ((hcrit _).2 (Or.inr (Or.inl rfl)))]
      congr 1
      ring

end DGPS.FiniteN
