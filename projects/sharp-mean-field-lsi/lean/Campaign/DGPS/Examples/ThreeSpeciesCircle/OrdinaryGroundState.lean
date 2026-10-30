import DGPS.Examples.ThreeSpeciesCircle.OrdinaryEuler
import DGPS.Frontier.STR029.T32

/-!
# Exact ordinary-equality ground-state transform on the full absolute H1 domain

The positive equality root is fixed, while the competitor is arbitrary in `AbsoluteDensity 1`.
The weak Euler equation is tested with the genuine H1 function `sqrt(sigma) * w^2`.
No Poincare gap, local coercivity or optimizer-localization conclusion is assumed.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace DGPS.Examples.ThreeSpeciesCircle

private theorem entropy_change_of_positive_continuous (ρ : AbsoluteDensity 1)
    (q : Torus 1 → ℝ) (hqc : Continuous q) (hqpos : ∀ x, 0 < q x)
    (hqmass : ∫ x, q x ∂haar 1 = 1) :
    relativeEntropy (densityMeasure ρ : Measure (Torus 1))
        ((haar 1).withDensity fun x => ENNReal.ofReal (q x)) ≠ ⊤ ∧
    (relativeEntropy (densityMeasure ρ : Measure (Torus 1))
        ((haar 1).withDensity fun x => ENNReal.ofReal (q x))).toReal =
      DGPS.Analysis.circleEntropy ρ -
        ∫ x, ρ.density x * Real.log (q x) ∂haar 1 := by
  let P := (haar 1).withDensity fun x => ENNReal.ofReal (q x)
  have hqm : Measurable q := hqc.measurable
  have i4 : Integrable q (haar 1) :=
    hqc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  haveI : IsProbabilityMeasure P := by
    constructor
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal i4 (Eventually.of_forall fun x => (hqpos x).le),
      hqmass, ENNReal.ofReal_one]
  have ilog : Integrable (fun x => ρ.density x * Real.log (q x)) (haar 1) := by
    obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn
      (hqc.log (fun x => (hqpos x).ne')).continuousOn
    exact ρ.integrable_density.mul_bdd
      (hqc.log (fun x => (hqpos x).ne')).aestronglyMeasurable
      (Eventually.of_forall fun x => hB x (Set.mem_univ x))
  set v : Torus 1 → ℝ := fun x => ρ.density x / q x with hv
  have hvm : AEMeasurable v (haar 1) := ρ.integrable_density.aemeasurable.div hqm.aemeasurable
  have hvnn : ∀ x, 0 ≤ v x := fun x => div_nonneg (ρ.density_nonneg x) (hqpos x).le
  have hqv : ∀ x, q x * v x = ρ.density x := fun x => by
    show q x * (ρ.density x / q x) = _
    field_simp [(hqpos x).ne']
  have hν : (densityMeasure ρ : Measure (Torus 1)) =
      (P).withDensity fun x => ENNReal.ofReal (v x) := by
    dsimp only [P]
    rw [← withDensity_mul₀ hqm.ennreal_ofReal.aemeasurable hvm.ennreal_ofReal, densityMeasure_coe]
    congr 1
    funext x
    simp only [Pi.mul_apply]
    rw [← ENNReal.ofReal_mul (hqpos x).le, hqv x]
    rfl
  have hPac : P ≪ haar 1 := withDensity_absolutelyContinuous _ _
  have hmass : ∫ x, v x ∂P = 1 := by
    change ∫ x, v x ∂(haar 1).withDensity (fun x => ENNReal.ofReal (q x)) = _
    rw [integral_withDensity_eq_integral_toReal_smul₀ hqm.ennreal_ofReal.aemeasurable
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    simp only [smul_eq_mul, ENNReal.toReal_ofReal (hqpos _).le]
    exact (integral_congr_ae (Filter.Eventually.of_forall hqv)).trans ρ.integral_density
  set F : Torus 1 → ℝ := fun x => v x * Real.log (v x) - v x + 1 with hF
  have hFnn : ∀ x, 0 ≤ F x := fun x => self_mul_log_sub_add_one_nonneg (hvnn x)
  have hΨ : ∀ x, q x * F x = ρ.density x * Real.log (ρ.density x) - ρ.density x * Real.log (q x)
      - ρ.density x + q x := by
    intro x
    rcases eq_or_ne (ρ.density x) 0 with h0 | h0
    · have : v x = 0 := by rw [hv]; simp [h0]
      simp [hF, this, h0]
    · have hvx : v x ≠ 0 := div_ne_zero h0 (hqpos x).ne'
      have : Real.log (v x) = Real.log (ρ.density x) - Real.log (q x) := by
        rw [hv]; exact Real.log_div h0 (hqpos x).ne'
      simp only [hF]
      rw [this]
      have := hqv x
      calc q x * (v x * (Real.log (ρ.density x) - Real.log (q x)) - v x + 1)
          = (q x * v x) * (Real.log (ρ.density x) - Real.log (q x)) - q x * v x + q x := by ring
        _ = _ := by rw [this]; ring
  have hFm : AEMeasurable (fun x => ENNReal.ofReal (F x)) (haar 1) := by
    refine ENNReal.measurable_ofReal.comp_aemeasurable ?_
    exact ((hvm.mul (Real.measurable_log.comp_aemeasurable hvm)).sub hvm).add_const 1
  have hΨi : Integrable (fun x => ρ.density x * Real.log (ρ.density x) -
      ρ.density x * Real.log (q x) - ρ.density x + q x) (haar 1) :=
    (((absoluteDensity_entropy_finite ρ).1.sub (ilog)).sub
      ρ.integrable_density).add i4
  have hΨnn : 0 ≤ᵐ[haar 1] fun x => ρ.density x * Real.log (ρ.density x) -
      ρ.density x * Real.log (q x) - ρ.density x + q x :=
    Filter.Eventually.of_forall fun x => by
      have := mul_nonneg (hqpos x).le (hFnn x)
      rw [hΨ x] at this
      exact this
  have hcongr : ∀ x, (ENNReal.ofReal (q x) * ENNReal.ofReal (F x)) = ENNReal.ofReal
      (ρ.density x * Real.log (ρ.density x) - ρ.density x * Real.log (q x) - ρ.density x + q x) := by
    intro x
    rw [← ENNReal.ofReal_mul (hqpos x).le, hΨ x]
  have hl : ∫⁻ x, ENNReal.ofReal (q x) * ENNReal.ofReal (F x) ∂haar 1 =
      ENNReal.ofReal (∫ x, (ρ.density x * Real.log (ρ.density x) - ρ.density x * Real.log (q x)
        - ρ.density x + q x) ∂haar 1) := by
    rw [ofReal_integral_eq_lintegral_ofReal hΨi hΨnn]
    exact lintegral_congr hcongr
  have hval : (∫ x, (ρ.density x * Real.log (ρ.density x) - ρ.density x * Real.log (q x)
      - ρ.density x + q x) ∂haar 1) = DGPS.Analysis.circleEntropy ρ -
        ∫ x, ρ.density x * Real.log (q x) ∂haar 1 := by
    rw [circleEntropy_eq]
    have i1 := (absoluteDensity_entropy_finite ρ).1
    have i2 := ilog
    have i3 := ρ.integrable_density
    have j1 : Integrable (fun x => ρ.density x * Real.log (ρ.density x) -
        ρ.density x * Real.log (q x)) (haar 1) := i1.sub i2
    have j2 : Integrable (fun x => ρ.density x * Real.log (ρ.density x) -
        ρ.density x * Real.log (q x) - ρ.density x) (haar 1) := j1.sub i3
    rw [integral_add j2 i4, integral_sub j1 i3, integral_sub i1 i2,
      ρ.integral_density, hqmass]
    ring
  have hnonneg : 0 ≤ DGPS.Analysis.circleEntropy ρ -
      ∫ x, ρ.density x * Real.log (q x) ∂haar 1 := by
    rw [← hval]
    exact integral_nonneg_of_ae hΨnn
  have hH : relativeEntropy (densityMeasure ρ : Measure (Torus 1)) P =
      ENNReal.ofReal (DGPS.Analysis.circleEntropy ρ -
        ∫ x, ρ.density x * Real.log (q x) ∂haar 1) := by
    rw [hν, relativeEntropy_withDensity (Eventually.of_forall hvnn) (hvm.mono_ac hPac),
      entropy_mass_one hmass]
    change ∫⁻ x, ENNReal.ofReal (F x) ∂(haar 1).withDensity (fun x => ENNReal.ofReal (q x)) = _
    rw [lintegral_withDensity_eq_lintegral_mul₀ hqm.ennreal_ofReal.aemeasurable hFm]
    change (∫⁻ x, ENNReal.ofReal (q x) * ENNReal.ofReal (F x) ∂haar 1) = _
    rw [hl, hval]
  exact ⟨by rw [hH]; exact ENNReal.ofReal_ne_top, by rw [hH, ENNReal.toReal_ofReal hnonneg]⟩

/-- The relative root of every absolute H1 density is genuinely H1 at a positive
continuous equality-root representative. The stored root may differ on a Haar-null set. -/
theorem ordinaryEquality_relativeRoot_memH1 (σ ρ : AbsoluteDensity 1)
    (u : Torus 1 → ℝ) (hu : Continuous u) (hupos : ∀ x, 0 < u x)
    (hurep : σ.sqrt =ᵐ[haar 1] u) : MemH1 (fun x => ρ.sqrt x / u x) := by
  have hσ := (isWeakGradient_weakGradient σ.sqrt_mem).congr_ae hurep (EventuallyEq.refl _ _)
  obtain ⟨x0, -, hx0⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty hu.continuousOn
  have hinv := hσ.inv_of_pos hu (hupos x0) (fun x => hx0 (Set.mem_univ x))
  have hp := (isWeakGradient_weakGradient ρ.sqrt_mem).mul_one_dim hinv
  exact ⟨_, hp.congr_ae (Eventually.of_forall fun x => (div_eq_mul_inv _ _).symm)
    (EventuallyEq.refl _ _)⟩

/-- Exact ground-state transform at an actual ordinary optimizer, against EVERY absolute
H1 competitor. The only regularity of the root used is a positive continuous representative;
no spectral gap or coercivity is assumed. All derivatives are physical circle derivatives. -/
theorem ordinaryEquality_groundStateIdentity_quotient (h : ℝ) (σ : AbsoluteDensity 1)
    (hpos : 0 < ordinaryEntropy h σ)
    (hmin : ∀ τ : AbsoluteDensity 1, 0 < ordinaryEntropy h τ →
      str025_quot h σ ≤ str025_quot h τ)
    (u : Torus 1 → ℝ) (hu : Continuous u) (hupos : ∀ x, 0 < u x)
    (hurep : σ.sqrt =ᵐ[haar 1] u) (ρ : AbsoluteDensity 1) :
    let w := fun x => ρ.sqrt x / u x
    let hw := ordinaryEquality_relativeRoot_memH1 σ ρ u hu hupos hurep
    relativeEntropy (densityMeasure ρ : Measure (Torus 1))
        (densityMeasure σ : Measure (Torus 1)) ≠ ⊤ ∧
    (ordinaryFisher h ρ).toReal - 2 * (str025_quot h σ).toReal *
        (ordinaryEntropy h ρ).toReal =
      4 * (∫ x, σ.density x * (weakGradient w hw x 0) ^ 2 ∂haar 1) -
        2 * (str025_quot h σ).toReal *
          (relativeEntropy (densityMeasure ρ : Measure (Torus 1))
            (densityMeasure σ : Measure (Torus 1))).toReal := by
  let w := fun x => ρ.sqrt x / u x
  let hw := ordinaryEquality_relativeRoot_memH1 σ ρ u hu hupos hurep
  let Gw := weakGradient w hw
  let Gσ := weakGradient σ.sqrt σ.sqrt_mem
  have hσ : IsWeakGradient u Gσ :=
    (isWeakGradient_weakGradient σ.sqrt_mem).congr_ae hurep (EventuallyEq.refl _ _)
  have hρ := isWeakGradient_weakGradient ρ.sqrt_mem
  have hW : IsWeakGradient w Gw := isWeakGradient_weakGradient hw
  have hprod : ∀ x, u x * w x = ρ.sqrt x := fun x => by
    dsimp only [w]
    field_simp [(hupos x).ne']
  have hρgrad : weakGradient ρ.sqrt ρ.sqrt_mem =ᵐ[haar 1]
      (fun x => w x • Gσ x + u x • Gw x) := by
    apply hρ.ae_eq
    exact (hσ.mul_one_dim hW).congr_ae (Eventually.of_forall hprod) (EventuallyEq.refl _ _)
  let φ := fun x => u x * (w x * w x)
  let Gφ := fun x => (w x * w x) • Gσ x + u x • (w x • Gw x + w x • Gw x)
  have hφ : IsWeakGradient φ Gφ := hσ.mul_one_dim (hW.mul_one_dim hW)
  let Sσ := fun x => 2 * Gσ x 0 - u x * logScore h x
  let Sρ := fun x => 2 * weakGradient ρ.sqrt ρ.sqrt_mem x 0 - ρ.sqrt x * logScore h x
  let T := fun x => 2 * Gφ x 0 - φ x * logScore h x
  let J := fun x => u x ^ 2 * (Gw x 0) ^ 2
  let B := fun x => ρ.density x * (Real.log (u x ^ 2) - Real.log (referenceDensity h x))
  have hSσ : MemLp Sσ 2 (haar 1) :=
    ((memLp_coord hσ.memLp_grad 0).const_mul 2).sub (memLp_mul_logScore h hσ.memLp)
  have hSρ : MemLp Sρ 2 (haar 1) :=
    ((memLp_coord hρ.memLp_grad 0).const_mul 2).sub (memLp_mul_logScore h hρ.memLp)
  have hT : MemLp T 2 (haar 1) :=
    ((memLp_coord hφ.memLp_grad 0).const_mul 2).sub (memLp_mul_logScore h hφ.memLp)
  have hJ : Integrable J (haar 1) := by
    obtain ⟨M, hM⟩ := isCompact_univ.exists_bound_of_continuousOn (hu.pow 2).continuousOn
    exact ((memLp_coord hW.memLp_grad 0).integrable_sq).bdd_mul (hu.pow 2).aestronglyMeasurable
      (Eventually.of_forall fun x => hM x (Set.mem_univ x))
  have hscore : ∀ᵐ x ∂haar 1, Sρ x ^ 2 = Sσ x * T x + 4 * J x := by
    filter_upwards [hρgrad] with x hx
    have hx0 := congrArg (fun v : Tangent 1 => v 0) hx
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at hx0
    dsimp only [Sρ, Sσ, T, J, φ, Gφ]
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    rw [hx0, ← hprod x]
    ring
  have hI : (ordinaryFisher h ρ).toReal =
      (∫ x, Sσ x * T x ∂haar 1) + 4 * ∫ x, J x ∂haar 1 := by
    rw [ordinaryFisher_eq, ENNReal.toReal_ofReal (integral_nonneg fun _ => sq_nonneg _)]
    change (∫ x, Sρ x ^ 2 ∂haar 1) = _
    have hST : Integrable (fun x => Sσ x * T x) (haar 1) := hSσ.integrable_mul hT
    rw [integral_congr_ae hscore, integral_add hST (hJ.const_mul 4), integral_const_mul]
  have hEuler := ordinaryOptimizer_weakEuler h σ hpos hmin hφ
  have hEL : (fun x =>
      (2 * weakGradient σ.sqrt σ.sqrt_mem x 0 - σ.sqrt x * logScore h x) *
      (2 * Gφ x 0 - φ x * logScore h x)) =ᵐ[haar 1] fun x => Sσ x * T x := by
    filter_upwards [hurep] with x hx
    dsimp only [Sσ, T, Gσ]
    rw [hx]
  have hER : (fun x => σ.sqrt x * φ x *
      (Real.log (σ.sqrt x ^ 2) - Real.log (referenceDensity h x))) =ᵐ[haar 1] B := by
    filter_upwards [hurep] with x hx
    dsimp only [B, φ, AbsoluteDensity.density]
    rw [hx, ← hprod x]
    ring
  rw [integral_congr_ae hEL, integral_congr_ae hER] at hEuler
  have hlogu : Integrable (fun x => ρ.density x * Real.log (u x ^ 2)) (haar 1) := by
    have hc := (hu.pow 2).log (fun x => pow_ne_zero 2 (hupos x).ne')
    obtain ⟨M, hM⟩ := isCompact_univ.exists_bound_of_continuousOn hc.continuousOn
    exact ρ.integrable_density.mul_bdd hc.aestronglyMeasurable
      (Eventually.of_forall fun x => hM x (Set.mem_univ x))
  have hqmass : ∫ x, u x ^ 2 ∂haar 1 = 1 := by
    calc
      (∫ x, u x ^ 2 ∂haar 1) = ∫ x, σ.sqrt x ^ 2 ∂haar 1 := by
        apply integral_congr_ae
        filter_upwards [hurep] with x hx
        rw [hx]
      _ = 1 := σ.mass_one
  have hmeasure : (densityMeasure σ : Measure (Torus 1)) =
      (haar 1).withDensity (fun x => ENNReal.ofReal (u x ^ 2)) := by
    apply withDensity_congr_ae
    filter_upwards [hurep] with x hx
    change ENNReal.ofReal (σ.sqrt x ^ 2) = ENNReal.ofReal (u x ^ 2)
    rw [hx]
  obtain ⟨hHσfinite, hHσ⟩ := entropy_change_of_positive_continuous ρ (fun x => u x ^ 2)
    (hu.pow 2) (fun x => sq_pos_of_pos (hupos x)) hqmass
  rw [← hmeasure] at hHσfinite hHσ
  obtain ⟨-, hHμ⟩ := entropy_change_of_positive_continuous ρ (referenceDensity h)
    (continuous_referenceDensity h) (fun x => referenceDensity_pos (h := h) x) (integral_referenceDensity_eq_one h)
  change (ordinaryEntropy h ρ).toReal = _ at hHμ
  have hB : (ordinaryEntropy h ρ).toReal -
      (relativeEntropy (densityMeasure ρ : Measure (Torus 1))
        (densityMeasure σ : Measure (Torus 1))).toReal = ∫ x, B x ∂haar 1 := by
    rw [hHμ, hHσ]
    dsimp only [B]
    simp_rw [mul_sub]
    rw [integral_sub hlogu (integrable_density_mul_log_reference h ρ)]
    ring
  have hJσ : (∫ x, J x ∂haar 1) =
      ∫ x, σ.density x * (Gw x 0) ^ 2 ∂haar 1 := by
    apply integral_congr_ae
    filter_upwards [hurep] with x hx
    dsimp only [J, AbsoluteDensity.density]
    rw [hx]
  refine ⟨hHσfinite, ?_⟩
  change (ordinaryFisher h ρ).toReal - 2 * (str025_quot h σ).toReal *
    (ordinaryEntropy h ρ).toReal = 4 * (∫ x, σ.density x * (Gw x 0) ^ 2 ∂haar 1) - _
  rw [hI, ← hJσ]
  rw [← hB] at hEuler
  linarith [hEuler]

/-- The same exact transform at the canonical ordinary LSI rate, on the original
absolute H1 competitor domain and the same actual equality-root witness. -/
theorem ordinaryEquality_groundStateIdentity (h : ℝ) (σ : AbsoluteDensity 1)
    (hpos : 0 < ordinaryEntropy h σ)
    (hmin : ∀ τ : AbsoluteDensity 1, 0 < ordinaryEntropy h τ →
      str025_quot h σ ≤ str025_quot h τ)
    (u : Torus 1 → ℝ) (hu : Continuous u) (hupos : ∀ x, 0 < u x)
    (hurep : σ.sqrt =ᵐ[haar 1] u) (ρ : AbsoluteDensity 1) :
    let w := fun x => ρ.sqrt x / u x
    let hw := ordinaryEquality_relativeRoot_memH1 σ ρ u hu hupos hurep
    relativeEntropy (densityMeasure ρ : Measure (Torus 1))
        (densityMeasure σ : Measure (Torus 1)) ≠ ⊤ ∧
    (ordinaryFisher h ρ).toReal - 2 * (ordinaryLSRate (ordinaryReference h)).toReal *
        (ordinaryEntropy h ρ).toReal =
      4 * (∫ x, σ.density x * (weakGradient w hw x 0) ^ 2 ∂haar 1) -
        2 * (ordinaryLSRate (ordinaryReference h)).toReal *
          (relativeEntropy (densityMeasure ρ : Measure (Torus 1))
            (densityMeasure σ : Measure (Torus 1))).toReal := by
  have hcanonical : ordinaryLSRate (ordinaryReference h) = str025_quot h σ :=
    (DGPS.Frontier.STR029.ordinaryLSRate_eq_abs_inf_STR02932 h).trans
      (DGPS.Frontier.STR029.quot_eq_inf_STR02932 h σ hpos hmin).symm
  simpa only [hcanonical] using
    ordinaryEquality_groundStateIdentity_quotient h σ hpos hmin u hu hupos hurep ρ

end DGPS.Examples.ThreeSpeciesCircle
