import DGPS.FiniteN.FalseMinimumFIN083
import DGPS.FiniteN.Tools.PositiveRate
import DGPS.FiniteN.Tools.UnitTorusNormalization

/-!
# FIN084: false-minimum symmetric quotient upper barrier

For `κ > 2`, `0 < h < h_c(κ)` and the false-minimum geometry `s1, s2, tp` of
`FalseMinimumGeometryFIN076`, with `B = ψ(-s1) - ψ(-s2) > 0`, the particle quotients built from the
cutoff test function `f_N = χ_δ (m_N)` satisfy `E_x(f_N) ≤ a₀ ‖χ_δ'‖∞² P(|m_N - m_b| ≤ δ) / N`.
Hence, for fixed `δ`, the `N⁻¹ log` limsup of the Poincare, all-LSI and symmetric-LSI rates is at
most `-(J_δ - G_-)`; then `δ ↓ 0` and `J_δ → G_- + B` give the final bound
`limsup N⁻¹ log rate_N ≤ -B` for the three rates.
-/

open MeasureTheory Filter Topology
open scoped ContDiff ENNReal
open DGPS.Circle.BesselMoments DGPS.FiniteN.EmpiricalCosineCramerFIN080 DGPS.FiniteN.FalseMinimumFIN081 DGPS.FiniteN.FalseMinimumFIN076
  DGPS.FiniteN.FalseMinimumFIN082 DGPS.FiniteN.FalseMinimumFIN083 DGPS.Models DGPS.FiniteN.ScalarFoldFIN056
  DGPS.Circle.AngularNormalization

namespace DGPS.FiniteN.FalseMinimumFIN084

/-- The coordinate function `a ↦ cos (2π a₀)` on the fundamental domain. -/
noncomputable def cosCoordFIN084 (a : Fin 1 → ℝ) : ℝ := Real.cos (2 * Real.pi * a 0)

theorem contDiff_cosCoord_FIN084 : ContDiff ℝ ∞ cosCoordFIN084 := by
  unfold cosCoordFIN084
  exact Real.contDiff_cos.comp (contDiff_const.mul (contDiff_apply ℝ ℝ 0))

theorem hasFDerivAt_cosCoord_FIN084 (t : Fin 1 → ℝ) :
    HasFDerivAt cosCoordFIN084
      (-Real.sin (2 * Real.pi * t 0) • ((2 * Real.pi) • ContinuousLinearMap.proj (R := ℝ)
        (φ := fun _ : Fin 1 => ℝ) 0)) t := by
  unfold cosCoordFIN084
  exact ((hasFDerivAt_apply (0 : Fin 1) t).const_mul (2 * Real.pi)).cos

theorem fderiv_cosCoord_apply_FIN084 (t : Fin 1 → ℝ) :
    fderiv ℝ cosCoordFIN084 t (Pi.single (0 : Fin 1) (1 : ℝ)) =
      -(2 * Real.pi) * Real.sin (2 * Real.pi * t 0) := by
  rw [(hasFDerivAt_cosCoord_FIN084 t).fderiv]
  simp only [smul_apply, ContinuousLinearMap.proj_apply, Pi.single_eq_same,
    smul_eq_mul]
  ring

theorem lift_FIN084 {N : ℕ+} (χ : ℝ → ℝ) :
    (fun x : DGPS.ParticleSpace 1 N => χ (empTorusFIN081 N x)) ∘ DGPS.particleLift =
      fun y : Fin N → Fin 1 → ℝ => χ ((N : ℝ)⁻¹ * ∑ k, cosCoordFIN084 (y k)) := by
  funext y
  simp [empTorusFIN081, DGPS.particleLift, scalarCos_lift, cosCoordFIN084]

theorem isSmooth_FIN084 {N : ℕ+} {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) :
    DGPS.IsSmoothPeriodicParticle
      (fun x : DGPS.ParticleSpace 1 N => χ (empTorusFIN081 N x)) := by
  unfold DGPS.IsSmoothPeriodicParticle
  rw [lift_FIN084]
  exact hχ.comp (contDiff_const.mul (ContDiff.sum fun k _ =>
    contDiff_cosCoord_FIN084.comp (contDiff_apply ℝ (Fin 1 → ℝ) k)))

theorem emp_secT_FIN084 {N : ℕ+} (x : DGPS.ParticleSpace 1 N) :
    (N : ℝ)⁻¹ * ∑ k, cosCoordFIN084 (SharpLSI.secT (x k)) = empTorusFIN081 N x := by
  simp [empTorusFIN081, cosCoordFIN084, ← scalarCos_lift, DGPS.torusLift, SharpLSI.liftT_secT]

theorem particlePartial_FIN084 {N : ℕ+} {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (x : DGPS.ParticleSpace 1 N) (i : Fin N) :
    DGPS.particlePartial i 0 (fun x : DGPS.ParticleSpace 1 N => χ (empTorusFIN081 N x)) x =
      deriv χ (empTorusFIN081 N x) *
        ((N : ℝ)⁻¹ * (-(2 * Real.pi) * Real.sin (2 * Real.pi * (SharpLSI.secT (x i)) 0))) := by
  set y0 : Fin N → Fin 1 → ℝ := fun k => SharpLSI.secT (x k) with hy0
  have hk : ∀ k : Fin N, HasFDerivAt (cosCoordFIN084 ∘ fun y : Fin N → Fin 1 → ℝ => y k)
      ((fderiv ℝ cosCoordFIN084 (y0 k)).comp (ContinuousLinearMap.proj k)) y0 := fun k =>
    HasFDerivAt.comp y0 ((contDiff_cosCoord_FIN084.differentiable (by simp)) (y0 k)).hasFDerivAt
      (hasFDerivAt_apply k y0)
  have hsumd : HasFDerivAt (fun y : Fin N → Fin 1 → ℝ => ∑ k, cosCoordFIN084 (y k))
      (∑ k, (fderiv ℝ cosCoordFIN084 (y0 k)).comp (ContinuousLinearMap.proj k)) y0 :=
    HasFDerivAt.fun_sum fun k _ => hk k
  have hinner := hsumd.const_mul ((N : ℝ)⁻¹)
  have hχd : HasDerivAt χ (deriv χ (empTorusFIN081 N x))
      ((N : ℝ)⁻¹ * ∑ k, cosCoordFIN084 (y0 k)) := by
    rw [hy0, emp_secT_FIN084]
    exact ((hχ.differentiable (by simp)) _).hasDerivAt
  have hcomp := hχd.comp_hasFDerivAt y0 hinner
  have key := hcomp.fderiv
  have hsum : ∑ k, (fderiv ℝ cosCoordFIN084 (y0 k))
      ((Pi.single i (Pi.single (0 : Fin 1) (1 : ℝ)) : Fin N → Fin 1 → ℝ) k) =
      fderiv ℝ cosCoordFIN084 (SharpLSI.secT (x i)) (Pi.single (0 : Fin 1) (1 : ℝ)) := by
    rw [Finset.sum_eq_single i]
    · simp [hy0]
    · intro k _ hk
      simp [hk]
    · intro h
      exact absurd (Finset.mem_univ i) h
  show fderiv ℝ ((fun x : DGPS.ParticleSpace 1 N => χ (empTorusFIN081 N x)) ∘ DGPS.particleLift) y0
      (Pi.single i (Pi.single (0 : Fin 1) (1 : ℝ))) = _
  rw [lift_FIN084]
  have key' : fderiv ℝ (fun y : Fin N → Fin 1 → ℝ => χ ((N : ℝ)⁻¹ * ∑ k, cosCoordFIN084 (y k))) y0 =
      deriv χ (empTorusFIN081 N x) •
        ((N : ℝ)⁻¹ • ∑ k, (fderiv ℝ cosCoordFIN084 (y0 k)).comp (ContinuousLinearMap.proj k)) :=
    key
  rw [key']
  simp only [smul_apply, sum_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
  rw [hsum, fderiv_cosCoord_apply_FIN084]

theorem le_of_forall_FIN084 {x : EReal} {r : ℝ}
    (h : ∀ c : ℝ, c < r → x ≤ ((-c : ℝ) : EReal)) : x ≤ ((-r : ℝ) : EReal) := by
  by_contra hx
  rw [not_le] at hx
  obtain ⟨q, h1, h2⟩ := EReal.lt_iff_exists_real_btwn.1 hx
  have hq : -q < r := by
    have := EReal.coe_lt_coe_iff.1 h1
    linarith
  have := h (-q) hq
  rw [neg_neg] at this
  exact absurd h2 (not_lt.2 this)

theorem quotient_limsup_FIN084 {P Q : ℕ+ → ℝ≥0∞} {n : ℕ+ → ℝ} {K J G : ℝ} (hK : 0 < K)
    (hG : 0 < G) (hn0 : ∀ N, 0 ≤ n N)
    (hP : limsup (fun N : ℕ+ => (((N : ℝ)⁻¹ : ℝ) : EReal) * ENNReal.log (P N)) atTop ≤
      ((-J : ℝ) : EReal))
    (hPtop : ∀ N, P N ≠ ⊤) (hQtop : ∀ᶠ N : ℕ+ in atTop, Q N ≠ ⊤)
    (hn : Tendsto (fun N : ℕ+ => ((N : ℝ)⁻¹) * Real.log (n N)) atTop (𝓝 (-G)))
    (hQ : ∀ᶠ N : ℕ+ in atTop, (Q N).toReal ≤ K * (P N).toReal / n N) :
    limsup (fun N : ℕ+ => (((N : ℝ)⁻¹ : ℝ) : EReal) * ENNReal.log (Q N)) atTop ≤
      ((-(J - G) : ℝ) : EReal) := by
  refine le_of_forall_FIN084 fun c hc => ?_
  set ε : ℝ := (J - G - c) / 2 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  have hlt : limsup (fun N : ℕ+ => (((N : ℝ)⁻¹ : ℝ) : EReal) * ENNReal.log (P N)) atTop <
      ((-J + ε : ℝ) : EReal) :=
    lt_of_le_of_lt hP (EReal.coe_lt_coe_iff.2 (by linarith))
  have hev1 := Filter.eventually_lt_of_limsup_lt hlt
  have hev2 := exp_lt_FIN083 hn0 hG hn (c := -G - ε) (by linarith)
  have hev3 := eventually_pos_FIN083 hn0 hG hn
  refine limsup_log_le_FIN081 (q := K) (c := c) hK ?_
  filter_upwards [hQ, hev1, hev2, hev3, hQtop] with N hq h1 h2 h3 hQt
  have hp := toReal_le_exp_FIN083 (hPtop N) h1
  rw [← ENNReal.ofReal_toReal hQt]
  refine ENNReal.ofReal_le_ofReal (hq.trans ?_)
  have e1 : Real.exp ((N : ℝ) * (-J + ε)) / Real.exp ((N : ℝ) * (-G - ε)) =
      Real.exp (-((N : ℝ) * c)) := by
    rw [← Real.exp_sub]; congr 1; rw [hε]; ring
  rw [← e1, mul_div_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hK.le
  exact div_le_div₀ (Real.exp_pos _).le hp (Real.exp_pos _) h2.le



theorem pointwise_FIN084 {N : ℕ+} {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) {a b C : ℝ}
    (hC : ∀ y, |deriv χ y| ≤ C) (hsupp : ∀ y, y ∉ Set.Icc a b → deriv χ y = 0)
    (x : DGPS.ParticleSpace 1 N) :
    ∑ i, ∑ j, DGPS.particlePartial i j
        (fun x : DGPS.ParticleSpace 1 N => χ (empTorusFIN081 N x)) x ^ 2 ≤
      Set.indicator {x : DGPS.ParticleSpace 1 N | empTorusFIN081 N x ∈ Set.Icc a b}
        (fun _ => a0 * C ^ 2 / (N : ℝ)) x := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast N.pos
  simp only [Fin.sum_univ_one]
  by_cases hY : empTorusFIN081 N x ∈ Set.Icc a b
  · rw [Set.indicator_of_mem (show x ∈ {x : DGPS.ParticleSpace 1 N |
      empTorusFIN081 N x ∈ Set.Icc a b} from hY)]
    have hterm : ∀ i : Fin N, DGPS.particlePartial i 0
        (fun x : DGPS.ParticleSpace 1 N => χ (empTorusFIN081 N x)) x ^ 2 ≤
          a0 * C ^ 2 / (N : ℝ) ^ 2 := by
      intro i
      rw [particlePartial_FIN084 hχ x i]
      have hd : deriv χ (empTorusFIN081 N x) ^ 2 ≤ C ^ 2 :=
        sq_le_sq' (abs_le.1 (hC _)).1 (abs_le.1 (hC _)).2
      have hs : Real.sin (2 * Real.pi * (SharpLSI.secT (x i)) 0) ^ 2 ≤ 1 := by
        have := Real.sin_sq_add_cos_sq (2 * Real.pi * (SharpLSI.secT (x i)) 0)
        nlinarith [sq_nonneg (Real.cos (2 * Real.pi * (SharpLSI.secT (x i)) 0))]
      have hpi : 0 ≤ (Real.pi) ^ 2 := sq_nonneg _
      calc (deriv χ (empTorusFIN081 N x) *
            ((N : ℝ)⁻¹ * (-(2 * Real.pi) * Real.sin (2 * Real.pi * (SharpLSI.secT (x i)) 0)))) ^ 2
          = deriv χ (empTorusFIN081 N x) ^ 2 * ((N : ℝ) ^ 2)⁻¹ * (4 * Real.pi ^ 2) *
              Real.sin (2 * Real.pi * (SharpLSI.secT (x i)) 0) ^ 2 := by
            rw [← inv_pow]; ring
        _ ≤ C ^ 2 * ((N : ℝ) ^ 2)⁻¹ * (4 * Real.pi ^ 2) * 1 := by
            gcongr
        _ = a0 * C ^ 2 / (N : ℝ) ^ 2 := by
            unfold a0; field_simp
    calc ∑ i : Fin N, DGPS.particlePartial i 0
          (fun x : DGPS.ParticleSpace 1 N => χ (empTorusFIN081 N x)) x ^ 2
        ≤ ∑ _i : Fin N, a0 * C ^ 2 / (N : ℝ) ^ 2 := Finset.sum_le_sum fun i _ => hterm i
      _ = a0 * C ^ 2 / (N : ℝ) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp
  · have hz : deriv χ (empTorusFIN081 N x) = 0 := hsupp _ hY
    have hzero : ∀ i : Fin N, DGPS.particlePartial i 0
        (fun x : DGPS.ParticleSpace 1 N => χ (empTorusFIN081 N x)) x = 0 := by
      intro i
      rw [particlePartial_FIN084 hχ x i, hz, zero_mul]
    rw [Set.indicator_of_notMem (show x ∉ {x : DGPS.ParticleSpace 1 N |
      empTorusFIN081 N x ∈ Set.Icc a b} from hY)]
    simp [hzero]

theorem symmetric_FIN084 {A : InteractionData 1} {N : ℕ+} (χ : ℝ → ℝ) :
    DGPS.IsSymmetricParticleFun A N (fun x : DGPS.ParticleSpace 1 N => χ (empTorusFIN081 N x)) :=
  DGPS.IsSymmetricParticleFun.of_forall fun σ x => by
    show χ (empTorusFIN081 N (DGPS.permuteParticles σ x)) = χ (empTorusFIN081 N x)
    unfold empTorusFIN081 DGPS.permuteParticles
    rw [Equiv.sum_comp σ (fun k => scalarCos (x k))]

theorem energy_le_FIN084 {A : InteractionData 1} {N : ℕ+} (F : DGPS.ParticleSpace 1 N → ℝ)
    (hF : DGPS.IsSmoothPeriodicParticle F) (S : Set (DGPS.ParticleSpace 1 N))
    (hS : MeasurableSet S) {c p : ℝ} (hc : 0 ≤ c) (hp : 0 ≤ p)
    (hpt : ∀ x, ∑ i, ∑ j, DGPS.particlePartial i j F x ^ 2 ≤ S.indicator (fun _ => c) x)
    (hprob : DGPS.particleLaw A N S ≤ ENNReal.ofReal p) :
    ∃ f : DGPS.ParticleH1 A N, f.1 = F ∧ DGPS.particleEnergy A N f ≤ c * p := by
  have hg := (DGPS.isParticleWeakGradient_iff A N F _).2
    (DGPS.FiniteN.PositiveRate.isParticleHaarWeakGradient_of_smooth hF)
  refine ⟨⟨F, ⟨_, hg⟩⟩, rfl, ?_⟩
  rw [DGPS.particleEnergy_eq_of_isParticleWeakGradient ⟨F, ⟨_, hg⟩⟩ hg]
  have hreal : (DGPS.particleLaw A N).real S ≤ p := by
    rw [measureReal_def]
    exact ENNReal.toReal_le_of_le_ofReal hp hprob
  refine (integral_mono_of_nonneg ?_ ((integrable_const c).indicator hS) ?_).trans ?_
  · exact Filter.Eventually.of_forall fun x => by
      simp only [DGPS.particleTangentNormSq]
      positivity
  · exact Filter.Eventually.of_forall fun x => by
      dsimp only
      rw [DGPS.particleTangentNormSq_eq]
      exact hpt x
  · rw [integral_indicator_const c hS, smul_eq_mul, mul_comm c p]
    exact mul_le_mul_of_nonneg_right hreal hc

theorem test_FIN084 (κ h : ℝ) {N : ℕ+} {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) {a b C : ℝ}
    (hC : ∀ y, |deriv χ y| ≤ C) (hsupp : ∀ y, y ∉ Set.Icc a b → deriv χ y = 0) :
    ∃ f : DGPS.ParticleH1 (scalarCosine κ h) N,
      f.1 = (fun x : DGPS.ParticleSpace 1 N => χ (empTorusFIN081 N x)) ∧
      DGPS.IsSymmetricParticleTest f ∧
      DGPS.particleEnergy (scalarCosine κ h) N f ≤
        a0 * C ^ 2 * (DGPS.particleLaw (scalarCosine κ h) N {x : DGPS.ParticleSpace 1 N |
          empTorusFIN081 N x ∈ Set.Icc a b}).toReal / (N : ℝ) := by
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast N.pos
  obtain ⟨f, hf, hE⟩ := energy_le_FIN084 (A := scalarCosine κ h) (N := N)
    (fun x : DGPS.ParticleSpace 1 N => χ (empTorusFIN081 N x)) (isSmooth_FIN084 hχ)
    {x : DGPS.ParticleSpace 1 N | empTorusFIN081 N x ∈ Set.Icc a b}
    (measurable_set_emp_FIN082 N measurableSet_Icc)
    (c := a0 * C ^ 2 / (N : ℝ)) (p := (DGPS.particleLaw (scalarCosine κ h) N
      {x : DGPS.ParticleSpace 1 N | empTorusFIN081 N x ∈ Set.Icc a b}).toReal)
    (by have := a0_pos; positivity) ENNReal.toReal_nonneg (pointwise_FIN084 hχ hC hsupp)
    (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) ENNReal.toReal_nonneg |>.2 le_rfl)
  refine ⟨f, hf, ?_, hE.trans_eq (by ring)⟩
  show DGPS.IsSymmetricParticleFun (scalarCosine κ h) N f.1
  rw [hf]
  exact symmetric_FIN084 χ

theorem cutoff_deriv_FIN084 {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) {a b : ℝ}
    (hχ1 : ∀ x, x ≤ a → χ x = 1) (hχ0 : ∀ x, b ≤ x → χ x = 0) :
    (∀ y, y ∉ Set.Icc a b → deriv χ y = 0) ∧ ∃ C : ℝ, ∀ y, |deriv χ y| ≤ C := by
  have hsupp : ∀ y, y ∉ Set.Icc a b → deriv χ y = 0 := by
    intro y hy
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hy
    rcases hy with hy | hy
    · have : χ =ᶠ[𝓝 y] fun _ => (1 : ℝ) :=
        Filter.eventually_of_mem (Iio_mem_nhds hy) fun z hz => hχ1 z (le_of_lt hz)
      rw [this.deriv_eq, deriv_const]
    · have : χ =ᶠ[𝓝 y] fun _ => (0 : ℝ) :=
        Filter.eventually_of_mem (Ioi_mem_nhds hy) fun z hz => hχ0 z (le_of_lt hz)
      rw [this.deriv_eq, deriv_const]
  refine ⟨hsupp, ?_⟩
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn
    (hχ.continuous_deriv (by simp)).continuousOn
  refine ⟨max C 0, fun y => ?_⟩
  by_cases hy : y ∈ Set.Icc a b
  · exact (hC y hy).trans (le_max_left _ _)
  · rw [hsupp y hy, abs_zero]; exact le_max_right _ _

theorem ratio_bound_FIN084 {e d p n k c0 : ℝ} (he : 0 ≤ e) (hek : e ≤ k * p)
    (hd : c0 * n ≤ d) (hc0 : 0 < c0) (hn : 0 < n) :
    e / d ≤ (k / c0) * p / n := by
  have hd0 : 0 < c0 * n := mul_pos hc0 hn
  have hd' : 0 < d := lt_of_lt_of_le hd0 hd
  calc e / d ≤ (k * p) / (c0 * n) := div_le_div₀ (he.trans hek) hek hd0 hd
    _ = (k / c0) * p / n := by field_simp

theorem eventually_lower_FIN084 {n V : ℕ+ → ℝ} {c : ℝ} (hc : c < 1)
    (hV : Tendsto (fun N => V N / n N) atTop (𝓝 1))
    (hn : ∀ᶠ N : ℕ+ in atTop, 0 < n N) :
    ∀ᶠ N : ℕ+ in atTop, c * n N < V N := by
  filter_upwards [hV.eventually (lt_mem_nhds hc), hn] with N h1 h2
  rwa [lt_div_iff₀ h2] at h1

theorem poincare_limsup_FIN084 {P : ℕ+ → ℝ≥0∞} {n E V : ℕ+ → ℝ} {k J G : ℝ} (hk : 0 ≤ k)
    (hG : 0 < G) (hn0 : ∀ N, 0 ≤ n N)
    (hP : limsup (fun N : ℕ+ => (((N : ℝ)⁻¹ : ℝ) : EReal) * ENNReal.log (P N)) atTop ≤
      ((-J : ℝ) : EReal))
    (hPtop : ∀ N, P N ≠ ⊤)
    (hn : Tendsto (fun N : ℕ+ => ((N : ℝ)⁻¹) * Real.log (n N)) atTop (𝓝 (-G)))
    (hE0 : ∀ N, 0 ≤ E N) (hE : ∀ N, E N ≤ k * (P N).toReal)
    (hV : Tendsto (fun N => V N / n N) atTop (𝓝 1)) :
    limsup (fun N : ℕ+ => (((N : ℝ)⁻¹ : ℝ) : EReal) *
      ENNReal.log (ENNReal.ofReal (E N) / ENNReal.ofReal (V N))) atTop ≤
      ((-(J - G) : ℝ) : EReal) := by
  have hnpos := eventually_pos_FIN083 hn0 hG hn
  have hVev := eventually_lower_FIN084 (c := 1 / 2) (by norm_num) hV hnpos
  refine quotient_limsup_FIN084 (K := 2 * k + 1) (by linarith) hG hn0 hP hPtop ?_ hn ?_
  · filter_upwards [hVev, hnpos] with N h1 h2
    have : 0 < V N := lt_trans (by positivity) h1
    exact ENNReal.div_ne_top ENNReal.ofReal_ne_top (by simpa using this)
  · filter_upwards [hVev, hnpos] with N h1 h2
    have hV0 : 0 < V N := lt_trans (by positivity) h1
    rw [ENNReal.toReal_div, ENNReal.toReal_ofReal (hE0 N), ENNReal.toReal_ofReal hV0.le]
    have := ratio_bound_FIN084 (hE0 N) (hE N) (d := V N) (n := n N)
      (c0 := 1 / 2) h1.le (by norm_num) h2
    refine this.trans ?_
    have hp := ENNReal.toReal_nonneg (a := P N)
    have : k / (1 / 2) * (P N).toReal ≤ (2 * k + 1) * (P N).toReal := by
      rw [div_div_eq_mul_div, div_one]; nlinarith
    exact div_le_div_of_nonneg_right this h2.le

theorem entropy_limsup_FIN084 {P : ℕ+ → ℝ≥0∞} {n E : ℕ+ → ℝ} {k J G : ℝ} (hk : 0 ≤ k)
    (hG : 0 < G) (hn0 : ∀ N, 0 ≤ n N)
    (hP : limsup (fun N : ℕ+ => (((N : ℝ)⁻¹ : ℝ) : EReal) * ENNReal.log (P N)) atTop ≤
      ((-J : ℝ) : EReal))
    (hPtop : ∀ N, P N ≠ ⊤)
    (hn : Tendsto (fun N : ℕ+ => ((N : ℝ)⁻¹) * Real.log (n N)) atTop (𝓝 (-G)))
    (hE0 : ∀ N, 0 ≤ E N) (hE : ∀ N, E N ≤ k * (P N).toReal)
    (Ent : ℕ+ → ℝ≥0∞)
    (hR : Tendsto (fun N : ℕ+ => (Ent N).toReal / ((N : ℝ) * G * n N)) atTop (𝓝 1)) :
    limsup (fun N : ℕ+ => (((N : ℝ)⁻¹ : ℝ) : EReal) *
      ENNReal.log (ENNReal.ofReal (2 * E N) / Ent N)) atTop ≤ ((-(J - G) : ℝ) : EReal) := by
  have hnpos := eventually_pos_FIN083 hn0 hG hn
  have hRev := eventually_lower_FIN084 (n := fun N : ℕ+ => (N : ℝ) * G * n N)
    (V := fun N => (Ent N).toReal) (c := 1 / 2) (by norm_num) hR
    (by filter_upwards [hnpos] with N h; have : (0:ℝ) < N := by positivity
        positivity)
  refine quotient_limsup_FIN084 (K := 4 * k / G + 1) (by positivity) hG hn0 hP hPtop ?_ hn ?_
  · filter_upwards [hRev, hnpos] with N h1 h2
    have hN : (0 : ℝ) < N := by positivity
    have : 0 < (Ent N).toReal := lt_trans (by positivity) h1
    exact ENNReal.div_ne_top ENNReal.ofReal_ne_top (ENNReal.toReal_pos_iff.1 this).1.ne'
  · filter_upwards [hRev, hnpos] with N h1 h2
    have hN : (0 : ℝ) < N := by positivity
    have hEnt0 : 0 < (Ent N).toReal := lt_trans (by positivity) h1
    rw [ENNReal.toReal_div, ENNReal.toReal_ofReal (by linarith [hE0 N])]
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast N.pos
    have key := ratio_bound_FIN084 (e := 2 * E N) (d := (Ent N).toReal) (p := (P N).toReal)
      (n := n N) (k := 2 * k) (c0 := G / 2) (by linarith [hE0 N]) (by linarith [hE N])
      ?_ (by positivity) h2
    · refine key.trans ?_
      have hp := ENNReal.toReal_nonneg (a := P N)
      have : 2 * k / (G / 2) * (P N).toReal ≤ (4 * k / G + 1) * (P N).toReal := by
        have : 2 * k / (G / 2) = 4 * k / G := by field_simp; ring
        rw [this]; nlinarith
      exact div_le_div_of_nonneg_right this h2.le
    · have : G / 2 * n N ≤ 1 / 2 * ((N : ℝ) * G * n N) := by
        have : 0 ≤ G * n N := mul_nonneg hG.le (hn0 N)
        nlinarith
      exact this.trans h1.le

theorem rate_transfer_FIN084 {R Q : ℕ+ → ℝ≥0∞} (hR : ∀ N, 0 < R N) (hRtop : ∀ N, R N ≠ ⊤)
    (hle : ∀ᶠ N : ℕ+ in atTop, R N ≤ Q N) {x : EReal}
    (h : limsup (fun N : ℕ+ => (((N : ℕ) : ℝ)⁻¹ : ℝ) * ENNReal.log (Q N)) atTop ≤ x) :
    limsup (fun N : ℕ+ => ((((N : ℕ) : ℝ)⁻¹ * Real.log (R N).toReal : ℝ) : EReal)) atTop ≤ x := by
  refine le_trans (Filter.limsup_le_limsup ?_) h
  filter_upwards [hle] with N hN
  have h1 : ((((N : ℕ) : ℝ)⁻¹ * Real.log (R N).toReal : ℝ) : EReal) =
      (((((N : ℕ) : ℝ)⁻¹ : ℝ)) : EReal) * ENNReal.log (R N) := by
    rw [ENNReal.log_pos_real (hR N).ne' (hRtop N), EReal.coe_mul]
  rw [h1]
  exact mul_le_mul_of_nonneg_left (ENNReal.log_monotone hN) (by
    exact_mod_cast inv_nonneg.2 (Nat.cast_nonneg _))

theorem rates_limsup_FIN084 (κ h : ℝ) {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hχ01 : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1) {a b G J : ℝ} (hG : 0 < G)
    (ha : ∀ x, x ≤ a → χ x = 1) (hb : ∀ x, b ≤ x → χ x = 0)
    (hmass : Tendsto (fun N : ℕ+ => ((N : ℝ)⁻¹) * Real.log (cutoffMassFIN082 κ h χ N)) atTop
      (𝓝 (-G)))
    (hlim : Filter.limsup (fun N : ℕ+ => gibbsLogProbFIN081 κ h N (Set.Icc a b)) atTop ≤
      ((-J : ℝ) : EReal))
    (hJ : G < J) :
    limsup (fun N : ℕ+ => ((((N : ℕ) : ℝ)⁻¹ * Real.log
      (DGPS.particlePoincareRate (scalarCosine κ h) N).toReal : ℝ) : EReal)) atTop ≤
        ((-(J - G) : ℝ) : EReal) ∧
    limsup (fun N : ℕ+ => ((((N : ℕ) : ℝ)⁻¹ * Real.log
      (DGPS.particleRateAll (scalarCosine κ h) N).toReal : ℝ) : EReal)) atTop ≤
        ((-(J - G) : ℝ) : EReal) ∧
    limsup (fun N : ℕ+ => ((((N : ℕ) : ℝ)⁻¹ * Real.log
      (DGPS.particleRateSym (scalarCosine κ h) N).toReal : ℝ) : EReal)) atTop ≤
        ((-(J - G) : ℝ) : EReal) := by
  obtain ⟨hpos, -, -, hR, hVr, -⟩ := branch_FIN083 κ h hχ.continuous (fun x => (hχ01 x).1)
    (fun x => (hχ01 x).2) hG ha hb hmass (J := ((J : ℝ) : EReal))
    (by rw [← EReal.coe_neg]; exact hlim)
    (by rw [← EReal.coe_neg]; exact EReal.coe_lt_coe_iff.2 (by linarith))
  obtain ⟨hcut, C, hC⟩ := cutoff_deriv_FIN084 hχ ha hb
  choose f hf hsym hE using fun N : ℕ+ => test_FIN084 κ h (N := N) hχ hC hcut
  have hn0 : ∀ N : ℕ+, 0 ≤ cutoffMassFIN082 κ h χ N := fun N =>
    integral_nonneg fun x => sq_nonneg _
  have hPtop : ∀ N : ℕ+, DGPS.particleLaw (scalarCosine κ h) N
      {x | empTorusFIN081 N x ∈ Set.Icc a b} ≠ ⊤ := fun N => measure_ne_top _ _
  have hEk : ∀ N : ℕ+, DGPS.particleEnergy (scalarCosine κ h) N (f N) ≤
      a0 * C ^ 2 * (DGPS.particleLaw (scalarCosine κ h) N
        {x | empTorusFIN081 N x ∈ Set.Icc a b}).toReal := fun N => by
    refine (hE N).trans ?_
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast N.pos
    have h0 : 0 ≤ a0 * C ^ 2 * (DGPS.particleLaw (scalarCosine κ h) N
        {x | empTorusFIN081 N x ∈ Set.Icc a b}).toReal := by
      have := a0_pos
      positivity
    exact div_le_self h0 hN1
  have hk : 0 ≤ a0 * C ^ 2 := by have := a0_pos; positivity
  have hnpos := eventually_pos_FIN083 hn0 hG hmass
  have hP : limsup (fun N : ℕ+ => (((N : ℝ)⁻¹ : ℝ) : EReal) * ENNReal.log
      (DGPS.particleLaw (scalarCosine κ h) N {x | empTorusFIN081 N x ∈ Set.Icc a b})) atTop ≤
        ((-J : ℝ) : EReal) := hlim
  have hV : Tendsto (fun N : ℕ+ => ProbabilityTheory.variance (f N).1
      (DGPS.particleLaw (scalarCosine κ h) N) / cutoffMassFIN082 κ h χ N) atTop (𝓝 1) :=
    hVr.congr fun N => by rw [hf N]
  have hEnt : ∀ N : ℕ+, DGPS.particleEntropy (scalarCosine κ h) N (f N) =
      homogeneousEntropy (DGPS.particleLaw (scalarCosine κ h) N)
        (fun x => (χ (empTorusFIN081 N x)) ^ 2) := fun N => by
    show homogeneousEntropy (DGPS.particleLaw (scalarCosine κ h) N) (fun x => (f N).1 x ^ 2) = _
    rw [hf N]
  have hR' : Tendsto (fun N : ℕ+ => (DGPS.particleEntropy (scalarCosine κ h) N (f N)).toReal /
      ((N : ℝ) * G * cutoffMassFIN082 κ h χ N)) atTop (𝓝 1) :=
    hR.congr fun N => by rw [hEnt N]
  have hrates := fun N : ℕ+ => finite_positive_particle_rate_and_real_bridge
    (scalarCosine κ h) Nat.one_pos N
  have hVev := eventually_lower_FIN084 (c := 1 / 2) (by norm_num) hV hnpos
  have hRev := eventually_lower_FIN084 (n := fun N : ℕ+ => (N : ℝ) * G * cutoffMassFIN082 κ h χ N)
    (V := fun N => (DGPS.particleEntropy (scalarCosine κ h) N (f N)).toReal) (c := 1 / 2)
    (by norm_num) hR'
    (by filter_upwards [hnpos] with N hN
        have : (0 : ℝ) < N := by positivity
        positivity)
  have hentpos : ∀ᶠ N : ℕ+ in atTop, 0 < DGPS.particleEntropy (scalarCosine κ h) N (f N) := by
    filter_upwards [hRev, hnpos] with N h1 h2
    have hN : (0 : ℝ) < N := by positivity
    have : 0 < (DGPS.particleEntropy (scalarCosine κ h) N (f N)).toReal :=
      lt_trans (by positivity) h1
    exact (ENNReal.toReal_pos_iff.1 this).1
  have pc := poincare_limsup_FIN084 (P := fun N : ℕ+ => DGPS.particleLaw (scalarCosine κ h) N
      {x | empTorusFIN081 N x ∈ Set.Icc a b}) (n := cutoffMassFIN082 κ h χ)
    (E := fun N => DGPS.particleEnergy (scalarCosine κ h) N (f N))
    (V := fun N => ProbabilityTheory.variance (f N).1 (DGPS.particleLaw (scalarCosine κ h) N))
    hk hG hn0 hP hPtop hmass (fun N => DGPS.particleEnergy_nonneg (f N)) hEk hV
  have ec := entropy_limsup_FIN084 (P := fun N : ℕ+ => DGPS.particleLaw (scalarCosine κ h) N
      {x | empTorusFIN081 N x ∈ Set.Icc a b}) (n := cutoffMassFIN082 κ h χ)
    (E := fun N => DGPS.particleEnergy (scalarCosine κ h) N (f N))
    hk hG hn0 hP hPtop hmass (fun N => DGPS.particleEnergy_nonneg (f N)) hEk
    (fun N => DGPS.particleEntropy (scalarCosine κ h) N (f N)) hR'
  refine ⟨?_, ?_, ?_⟩
  · refine rate_transfer_FIN084 (Q := fun N => DGPS.particlePoincareQuotient
      (scalarCosine κ h) N (f N)) (fun N => (hrates N).2.2.2.2.1.1)
      (fun N => (hrates N).2.2.2.2.1.2.ne) ?_ pc
    filter_upwards [hVev, hnpos] with N h1 h2
    have : 0 < ProbabilityTheory.variance (f N).1 (DGPS.particleLaw (scalarCosine κ h) N) :=
      lt_trans (by positivity) h1
    exact DGPS.particlePoincareRate_le_quotient _ N (f N) this
  · refine rate_transfer_FIN084 (Q := fun N => DGPS.particleQuotient
      (scalarCosine κ h) N (f N)) (fun N => (hrates N).2.2.1.1)
      (fun N => (hrates N).2.2.1.2.ne) ?_ ec
    filter_upwards [hentpos] with N h1
    exact DGPS.particleRateAll_le_quotient _ N (f N) h1
  · refine rate_transfer_FIN084 (Q := fun N => DGPS.particleQuotient
      (scalarCosine κ h) N (f N)) (fun N => (hrates N).2.2.2.1.1)
      (fun N => (hrates N).2.2.2.1.2.ne) ?_ ec
    filter_upwards [hentpos] with N h1
    exact DGPS.particleRateSym_le_quotient _ N (f N) (hsym N) h1

theorem near_FIN084 {κ h s1 s2 tp : ℝ} (hκ : 0 < κ)
    (hG : FalseMinimumGeometryFIN076 κ h s1 s2 tp) {c : ℝ}
    (hc : c < scalarPsi κ h (-s1) - scalarPsi κ h (-s2)) :
    ∃ r : ℝ, 0 < r ∧ ∀ x : ℝ, |x - besselRatio (-s1)| ≤ r →
      ((scalarPsi κ h (-s2) - scalarPsi κ h tp + c : ℝ) : EReal) ≤ gibbsRateFIN081 κ h x := by
  have hm1 : psiDerivFIN056 κ h (-s1) = 0 :=
    (psiDeriv_zero_iff_FIN082 hκ hG _).2 (Or.inr (Or.inl rfl))
  have hUb : ufFIN081 κ h (besselRatio (-s1)) = scalarPsi κ h (-s1) :=
    uf_ratio_FIN081 hκ.ne' h hm1
  have hmem := ratio_mem_FIN081 (-s1)
  have hcont : ContinuousAt (ufFIN081 κ h) (besselRatio (-s1)) :=
    (hasDerivAt_uf_FIN081 κ h hmem).continuousAt
  have hev : ∀ᶠ x in 𝓝 (besselRatio (-s1)),
      ufFIN081 κ h (besselRatio (-s1)) - (scalarPsi κ h (-s1) - scalarPsi κ h (-s2) - c) <
        ufFIN081 κ h x :=
    hcont.eventually (lt_mem_nhds (by linarith))
  have hev2 : ∀ᶠ x in 𝓝 (besselRatio (-s1)), x ∈ Set.Ioo (-1 : ℝ) 1 :=
    Ioo_mem_nhds hmem.1 hmem.2
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 (hev.and hev2)
  refine ⟨ε / 2, by positivity, fun x hx => ?_⟩
  have hd : dist x (besselRatio (-s1)) < ε := by
    rw [Real.dist_eq]; linarith
  obtain ⟨h1, h2⟩ := hball hd
  rw [gibbsRate_eq_FIN081 hκ hG h2]
  refine EReal.coe_le_coe_iff.2 ?_
  rw [hUb] at h1
  linarith

theorem le_rate_mb_FIN084 {κ h s1 s2 tp : ℝ} (hκ : 0 < κ)
    (hG : FalseMinimumGeometryFIN076 κ h s1 s2 tp) :
    gibbsRateFIN081 κ h (besselRatio (-s1)) =
      ((scalarPsi κ h (-s1) - scalarPsi κ h tp : ℝ) : EReal) :=
  gibbsRate_critical_FIN081 hκ hG ((hG.2.2.2.1 _).2 (Or.inr (Or.inl rfl)))

end DGPS.FiniteN.FalseMinimumFIN084

namespace DGPS.FiniteN

open DGPS.FiniteN.FalseMinimumFIN084

theorem false_minimum_symmetric_quotient_upper_barrier (κ h : ℝ) (hκ : 2 < κ) (hh0 : 0 < h)
    (hhc : h < scalarFoldField κ) :
    ∃ s1 s2 tp : ℝ, FalseMinimumGeometryFIN076 κ h s1 s2 tp ∧
      ∃ B : ℝ, B = scalarPsi κ h (-s1) - scalarPsi κ h (-s2) ∧ 0 < B ∧
        Filter.limsup (fun N : ℕ+ => ((((N : ℕ) : ℝ)⁻¹ * Real.log
          (particlePoincareRate (scalarCosine κ h) N).toReal : ℝ) : EReal)) Filter.atTop ≤
            ((-B : ℝ) : EReal) ∧
        Filter.limsup (fun N : ℕ+ => ((((N : ℕ) : ℝ)⁻¹ * Real.log
          (particleRateAll (scalarCosine κ h) N).toReal : ℝ) : EReal)) Filter.atTop ≤
            ((-B : ℝ) : EReal) ∧
        Filter.limsup (fun N : ℕ+ => ((((N : ℕ) : ℝ)⁻¹ * Real.log
          (particleRateSym (scalarCosine κ h) N).toReal : ℝ) : EReal)) Filter.atTop ≤
            ((-B : ℝ) : EReal) := by
  obtain ⟨s1, s2, tp, hs1, hs1', hs2', htp, hGeo, G, hGpos, hGdef, hJm, δ0, hδ0, hall⟩ :=
    false_minimum_branch_cutoff_mass_exponent κ h hκ hh0 hhc
  have hκ0 : 0 < κ := by linarith
  have hB : 0 < scalarPsi κ h (-s1) - scalarPsi κ h (-s2) := hGeo.2.2.2.2.2.2.2.1.1
  refine ⟨s1, s2, tp, hGeo, _, rfl, hB, ?_⟩
  have key : ∀ c : ℝ, c < scalarPsi κ h (-s1) - scalarPsi κ h (-s2) →
      Filter.limsup (fun N : ℕ+ => ((((N : ℕ) : ℝ)⁻¹ * Real.log
          (particlePoincareRate (scalarCosine κ h) N).toReal : ℝ) : EReal)) Filter.atTop ≤
            ((-c : ℝ) : EReal) ∧
        Filter.limsup (fun N : ℕ+ => ((((N : ℕ) : ℝ)⁻¹ * Real.log
          (particleRateAll (scalarCosine κ h) N).toReal : ℝ) : EReal)) Filter.atTop ≤
            ((-c : ℝ) : EReal) ∧
        Filter.limsup (fun N : ℕ+ => ((((N : ℕ) : ℝ)⁻¹ * Real.log
          (particleRateSym (scalarCosine κ h) N).toReal : ℝ) : EReal)) Filter.atTop ≤
            ((-c : ℝ) : EReal) := by
    intro c hc
    obtain ⟨r, hr, hnear⟩ := near_FIN084 hκ0 hGeo hc
    have hδ : 0 < min δ0 r := lt_min hδ0 hr
    obtain ⟨-, -, hGlt, ⟨χ, hχ, hχ01, hχ1, hχ0⟩, hmain⟩ := hall (min δ0 r) hδ (min_le_left _ _)
    obtain ⟨hmass, hlim, -⟩ := hmain χ hχ hχ01 hχ1 hχ0
    set I : EReal := ⨅ x ∈ Set.Icc (besselRatio (-s1) - min δ0 r) (besselRatio (-s1) + min δ0 r),
      gibbsRateFIN081 κ h x with hI
    have hIle : I ≤ ((scalarPsi κ h (-s1) - scalarPsi κ h tp : ℝ) : EReal) := by
      rw [← le_rate_mb_FIN084 hκ0 hGeo]
      exact iInf₂_le (besselRatio (-s1)) ⟨by linarith, by linarith⟩
    have hIge : ((scalarPsi κ h (-s2) - scalarPsi κ h tp + c : ℝ) : EReal) ≤ I := by
      refine le_iInf₂ fun x hx => hnear x ?_
      have := min_le_right δ0 r
      rw [abs_le]
      constructor <;> linarith [hx.1, hx.2]
    have hItop : I ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _) hIle
    have hIbot : I ≠ ⊥ := fun h0 => by
      rw [h0] at hIge
      exact absurd (le_bot_iff.1 hIge) (EReal.coe_ne_bot _)
    have hIJ : I = ((I.toReal : ℝ) : EReal) := (EReal.coe_toReal hItop hIbot).symm
    have hGJ : G + c ≤ I.toReal := by
      have := hIge
      rw [hIJ] at this
      have := EReal.coe_le_coe_iff.1 this
      rw [hGdef]; linarith
    have hGJ' : G < I.toReal := by
      have := hGlt
      rw [hIJ] at this
      exact EReal.coe_lt_coe_iff.1 this
    obtain ⟨h1, h2, h3⟩ := rates_limsup_FIN084 κ h hχ hχ01 hGpos hχ1 hχ0 hmass
      (J := I.toReal) (by rw [EReal.coe_neg, ← hIJ]; exact hlim) hGJ'
    have hle : ((-(I.toReal - G) : ℝ) : EReal) ≤ ((-c : ℝ) : EReal) :=
      EReal.coe_le_coe_iff.2 (by linarith)
    exact ⟨h1.trans hle, h2.trans hle, h3.trans hle⟩
  exact ⟨le_of_forall_FIN084 fun c hc => (key c hc).1,
    le_of_forall_FIN084 fun c hc => (key c hc).2.1,
    le_of_forall_FIN084 fun c hc => (key c hc).2.2⟩

end DGPS.FiniteN
