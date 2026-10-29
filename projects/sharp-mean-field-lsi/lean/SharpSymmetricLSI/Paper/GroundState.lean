import SharpSymmetricLSI.Paper.TorusLSI
import SharpSymmetricLSI.Paper.CosineSecondOrder
import SharpSymmetricLSI.Paper.CosineTagged

/-!
# Weak calculus with smooth periodic factors (Phase 3, lane C; for `cosine_defective`)

* Product rule: `∇(f θ) = (∇f) θ + f ∇θ` for a weak-gradient pair `(f, g)` and smooth periodic `θ`.
* `∫ ∂_k f = 0` for integrable weak-gradient pairs (zero Fourier mode of `mFourierCoeff_grad`).
* Hence periodic integration by parts `∫ f ∂_kθ = -∫ (∂_k f) θ`.
-/

open MeasureTheory InformationTheory Set Filter Topology
open scoped ENNReal Real ContDiff
open UnitAddTorus

namespace SharpLSI

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem locallyIntegrable_mul_continuous {f c : (ι → ℝ) → ℝ}
    (hf : LocallyIntegrable f (volume : Measure (ι → ℝ))) (hc : Continuous c) :
    LocallyIntegrable (fun x => f x * c x) (volume : Measure (ι → ℝ)) :=
  (locallyIntegrable_iff).2 fun K hK =>
    (hf.integrableOn_isCompact hK).mul_continuousOn hc.continuousOn hK

/-- Product rule with a smooth periodic factor. -/
theorem IsWeakGrad.mul_smooth {f : UnitAddTorus ι → ℝ} {g : UnitAddTorus ι → ι → ℝ}
    (h : IsWeakGrad f g) {Θ : (ι → ℝ) → ℝ} (hΘ : ContDiff ℝ ∞ Θ) (hp : IsPer Θ) :
    IsWeakGrad (fun y => f y * Θ (secT y))
      (fun y k => g y k * Θ (secT y) + f y * Dk Θ k (secT y)) := by
  have hlift : ∀ x, Θ (secT (liftT x)) = Θ x := hp.secT_liftT
  have hliftD : ∀ k x, Dk Θ k (secT (liftT x)) = Dk Θ k x := fun k => (hp.Dk k).secT_liftT
  have hDc : ∀ k, Continuous (Dk Θ k) := fun k => (contDiff_Dk hΘ k).continuous
  refine ⟨?_, fun k => ?_, fun ψ hψ hψc k => ?_⟩
  · have := locallyIntegrable_mul_continuous h.locInt hΘ.continuous
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp only [Function.comp_apply, hlift]
  · have h1 := locallyIntegrable_mul_continuous (h.locInt_grad k) hΘ.continuous
    have h2 := locallyIntegrable_mul_continuous h.locInt (hDc k)
    refine (h1.add h2).congr (Eventually.of_forall fun x => ?_)
    simp only [Function.comp_apply, Pi.add_apply, hlift, hliftD]
  · have hΘd : Differentiable ℝ Θ := hΘ.differentiable (by simp)
    have hψd : Differentiable ℝ ψ := hψ.differentiable (by simp)
    set φ : (ι → ℝ) → ℝ := fun x => ψ x * Θ x with hφ
    have hφs : ContDiff ℝ ∞ φ := hψ.mul hΘ
    have hφc : HasCompactSupport φ := hψc.mul_right
    have hdφ : ∀ x, fderiv ℝ φ x (Pi.single k 1) =
        fderiv ℝ ψ x (Pi.single k 1) * Θ x + ψ x * Dk Θ k x := fun x => by
      rw [fderiv_fun_mul (hψd x) (hΘd x)]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, Dk]
      ring
    have key := h.ibp φ hφs hφc k
    simp_rw [hdφ] at key
    have hψ' : Continuous fun x => fderiv ℝ ψ x (Pi.single k 1) :=
      (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
    have i1 := h.locInt.integrable_smul_right_of_hasCompactSupport
      (hψ'.mul hΘ.continuous) ((hψc.fderiv_apply (𝕜 := ℝ) (Pi.single k 1)).mul_right)
    have i2 := h.locInt.integrable_smul_right_of_hasCompactSupport
      (hψ.continuous.mul (hDc k)) hψc.mul_right
    have j1 := (h.locInt_grad k).integrable_smul_right_of_hasCompactSupport
      (hψ.continuous.mul hΘ.continuous) hψc.mul_right
    simp only [smul_eq_mul, Function.comp] at i1 i2 j1
    have i1' : Integrable (fun x => f (liftT x) * (fderiv ℝ ψ x (Pi.single k 1) * Θ x)) := i1
    have i2' : Integrable (fun x => f (liftT x) * (ψ x * Dk Θ k x)) := i2
    have j1' : Integrable (fun x => g (liftT x) k * (ψ x * Θ x)) := j1
    have e1 : ∫ x, f (liftT x) * (fderiv ℝ ψ x (Pi.single k 1) * Θ x + ψ x * Dk Θ k x) =
        (∫ x, f (liftT x) * (fderiv ℝ ψ x (Pi.single k 1) * Θ x)) +
          ∫ x, f (liftT x) * (ψ x * Dk Θ k x) := by
      rw [← integral_add i1' i2']; congr 1; funext x; ring
    rw [e1] at key
    simp only [Function.comp_apply, hlift, hliftD]
    have e2 : ∫ x, f (liftT x) * Θ x * fderiv ℝ ψ x (Pi.single k 1) =
        ∫ x, f (liftT x) * (fderiv ℝ ψ x (Pi.single k 1) * Θ x) := by
      congr 1; funext x; ring
    have e3 : ∫ x, (g (liftT x) k * Θ x + f (liftT x) * Dk Θ k x) * ψ x =
        (∫ x, g (liftT x) k * (ψ x * Θ x)) + ∫ x, f (liftT x) * (ψ x * Dk Θ k x) := by
      rw [← integral_add j1' i2']; congr 1; funext x; ring
    rw [e2, e3]
    linarith

/-- `∫ ∂_k f = 0`. -/
theorem integral_weakGrad_eq_zero {f : UnitAddTorus ι → ℝ} {g : UnitAddTorus ι → ι → ℝ}
    (h : IsWeakGrad f g) (hf : Integrable f volume) (hg : ∀ k, Integrable (fun y => g y k) volume)
    (k : ι) : ∫ y, g y k = 0 := by
  have h0 := mFourierCoeff_grad h hf hg 0 k
  simp only [Pi.zero_apply, Int.cast_zero, mul_zero, zero_mul] at h0
  rw [mFourierCoeff_eq_integral] at h0
  simp only [neg_zero, mFourier_zero, ContinuousMap.one_apply, one_smul] at h0
  rw [integral_complex_ofReal] at h0
  exact_mod_cast h0

/-- Periodic integration by parts against a smooth periodic function. -/
theorem integral_mul_Dk_eq {f : UnitAddTorus ι → ℝ} {g : UnitAddTorus ι → ι → ℝ}
    (h : IsWeakGrad f g) (hf : Integrable f volume) (hg : ∀ k, Integrable (fun y => g y k) volume)
    {Θ : (ι → ℝ) → ℝ} (hΘ : ContDiff ℝ ∞ Θ) (hp : IsPer Θ) (k : ι) :
    ∫ y, f y * Dk Θ k (secT y) = -∫ y, g y k * Θ (secT y) := by
  obtain ⟨B, hB⟩ := periodic_bounded hΘ.continuous hp
  have hbd : ∀ k, ∃ C, ∀ x, ‖Dk Θ k x‖ ≤ C := fun k =>
    periodic_bounded (contDiff_Dk hΘ k).continuous (hp.Dk k)
  choose C hC using hbd
  have hΘm : Measurable fun y => Θ (secT y) := hΘ.continuous.measurable.comp measurable_secT
  have hDm : ∀ k, Measurable fun y => Dk Θ k (secT y) := fun k =>
    (contDiff_Dk hΘ k).continuous.measurable.comp measurable_secT
  have iΘ : ∀ {F : UnitAddTorus ι → ℝ}, Integrable F volume → Integrable (fun y => F y * Θ (secT y)) volume :=
    fun {F} hF => hF.mul_bdd hΘm.aestronglyMeasurable (Eventually.of_forall fun y => hB _)
  have iD : ∀ {F : UnitAddTorus ι → ℝ}, Integrable F volume → ∀ k,
      Integrable (fun y => F y * Dk Θ k (secT y)) volume :=
    fun {F} hF k => hF.mul_bdd (hDm k).aestronglyMeasurable (Eventually.of_forall fun y => hC k _)
  have hm := h.mul_smooth hΘ hp
  have h0 := integral_weakGrad_eq_zero hm (iΘ hf) (fun k => (iΘ (hg k)).add (iD hf k)) k
  rw [integral_add (iΘ (hg k)) (iD hf k)] at h0
  linarith

/-! ### The cosine model on the flat torus -/

section Cosine

variable {N : ℕ}

/-- The normalizing constant `1/K_N = e^{κN/2}/Z_N`. -/
noncomputable def gsC (κ : ℝ) (N : ℕ) : ℝ := Real.exp (κ * N / 2) / partitionFn cosV (cosW κ) N

/-- The Gibbs density on the flat torus, `w = e^{-U_N}/K_N`. -/
noncomputable def gsW (κ : ℝ) (N : ℕ) (y : UnitAddTorus (Fin N × Fin 1)) : ℝ :=
  gsC κ N * Real.exp (-UL κ N (secT y))

theorem partitionFn_cos_pos (κ : ℝ) (N : ℕ) : 0 < partitionFn cosV (cosW κ) N :=
  partition_pos_of_continuous _ (continuous_hamiltonian (cosine_hyp_all κ) N)

theorem gsC_pos (κ : ℝ) (N : ℕ) : 0 < gsC κ N := div_pos (Real.exp_pos _) (partitionFn_cos_pos κ N)

theorem gsW_pos (κ : ℝ) (y : UnitAddTorus (Fin N × Fin 1)) : 0 < gsW κ N y :=
  mul_pos (gsC_pos κ N) (Real.exp_pos _)

theorem UL_nonneg {κ : ℝ} (hκ : 0 ≤ κ) (x : Fin N × Fin 1 → ℝ) : 0 ≤ UL κ N x := by
  unfold UL; positivity

theorem measurable_gsW (κ : ℝ) : Measurable (gsW κ N) :=
  measurable_const.mul (Real.continuous_exp.measurable.comp
    ((contDiff_UL κ).continuous.measurable.comp measurable_secT).neg)

theorem gibbs_map_flat_eq (κ : ℝ) :
    (gibbs cosV (cosW κ) N).map flat =
      (volume : Measure (UnitAddTorus (Fin N × Fin 1))).withDensity
        (fun y => ENNReal.ofReal (gsW κ N y)) := by
  have hpt : ∀ X : Config N 1, ENNReal.ofReal (Real.exp (-hamiltonian cosV (cosW κ) N X) /
      partitionFn cosV (cosW κ) N) = ENNReal.ofReal (gsW κ N (flat X)) := fun X => by
    congr 1
    rw [hamiltonian_cos, gsW, gsC, ← cosU_unflat κ (flat X)]
    rw [show unflat (flat X) = X from rfl, show -(cosU κ N X - κ * N / 2) =
      κ * N / 2 + -cosU κ N X by ring, Real.exp_add]
    ring
  ext s hs
  rw [Measure.map_apply measurable_flat hs, gibbs, withDensity_apply _ (measurable_flat hs),
    withDensity_apply _ hs]
  simp_rw [hpt]
  exact measurePreserving_flat.setLIntegral_comp_preimage hs
    (ENNReal.measurable_ofReal.comp (measurable_gsW κ))

/-- `Θ = √(1/K) e^{-U/2}`, with `Θ² = w`. -/
noncomputable def gsTheta (κ : ℝ) (N : ℕ) (x : Fin N × Fin 1 → ℝ) : ℝ :=
  Real.sqrt (gsC κ N) * Real.exp (-UL κ N x / 2)

theorem smPer_gsTheta (κ : ℝ) : SmPer (gsTheta κ N) := by
  have hU := smPer_UL (N := N) κ
  refine ⟨contDiff_const.mul (Real.contDiff_exp.comp (hU.1.neg.div_const 2)), fun m x => ?_⟩
  simp only [gsTheta, hU.2 m x]

theorem gsTheta_sq (κ : ℝ) (y : UnitAddTorus (Fin N × Fin 1)) :
    gsTheta κ N (secT y) ^ 2 = gsW κ N y := by
  rw [gsTheta, gsW, mul_pow, Real.sq_sqrt (gsC_pos κ N).le, ← Real.exp_nat_mul]
  congr 2; push_cast; ring

theorem Dk_gsTheta (κ : ℝ) (k : Fin N × Fin 1) (x : Fin N × Fin 1 → ℝ) :
    Dk (gsTheta κ N) k x = -(1 / 2) * gsTheta κ N x * Dk (UL κ N) k x := by
  have hU : Differentiable ℝ (UL κ N) := (contDiff_UL κ).differentiable (by simp)
  have hd : HasFDerivAt (gsTheta κ N)
      (Real.sqrt (gsC κ N) • (Real.exp (-UL κ N x / 2) • (-(1 / 2 : ℝ)) • fderiv ℝ (UL κ N) x)) x := by
    have h0 : HasFDerivAt (fun y => -UL κ N y / 2) ((-(1 / 2 : ℝ)) • fderiv ℝ (UL κ N) x) x := by
      have := (hU x).hasFDerivAt.const_mul (-(1 / 2 : ℝ))
      convert this using 1; funext y; ring
    have h2 := h0.exp.const_mul (Real.sqrt (gsC κ N))
    convert h2 using 1
    · rfl
  rw [Dk, hd.fderiv, Dk]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, gsTheta]
  ring

/-- `ΔU = aκ - 2aU` on the lift. -/
theorem laplacian_UL (κ : ℝ) (hN : 1 ≤ N) (x : Fin N × Fin 1 → ℝ) :
    ∑ k, Dk (Dk (UL κ N) k) k x = aCos * κ - 2 * aCos * UL κ N x := by
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_one]
  have hk : ∀ j : Fin N, Dk (Dk (UL κ N) (j, 0)) (j, 0) x =
      κ / (2 * N) * (8 * π ^ 2) * (1 - (sumCos x * Real.cos (thetaC x j) +
        sumSin x * Real.sin (thetaC x j))) := fun j => by
    rw [Dk_UL, Dk, fderiv_dUL, if_pos rfl, one_mul]
    have := Real.cos_sq_add_sin_sq (thetaC x j)
    rw [show Real.cos (thetaC x j) * Real.cos (thetaC x j) + Real.sin (thetaC x j) *
      Real.sin (thetaC x j) = 1 by nlinarith]
  simp_rw [hk]
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  have hN' : (N : ℝ) ≠ 0 := by have : (1 : ℝ) ≤ N := by exact_mod_cast hN
                               linarith
  rw [show (∑ j, Real.cos (thetaC x j)) = sumCos x from rfl,
    show (∑ j, Real.sin (thetaC x j)) = sumSin x from rfl]
  unfold aCos UL
  field_simp
  ring

/-- The flat Gibbs measure `w · m`. -/
noncomputable abbrev gsMeas (κ : ℝ) (N : ℕ) : Measure (UnitAddTorus (Fin N × Fin 1)) :=
  (volume : Measure (UnitAddTorus (Fin N × Fin 1))).withDensity (fun y => ENNReal.ofReal (gsW κ N y))

instance (κ : ℝ) (N : ℕ) : IsProbabilityMeasure (gsMeas κ N) := by
  rw [gsMeas, ← gibbs_map_flat_eq]
  haveI := gibbs_isProbabilityMeasure (cosine_hyp_all κ) N
  infer_instance

theorem integral_gsMeas (κ : ℝ) (F : UnitAddTorus (Fin N × Fin 1) → ℝ) :
    ∫ y, F y ∂gsMeas κ N = ∫ y, gsW κ N y * F y := by
  rw [gsMeas, integral_withDensity_eq_integral_toReal_smul₀ (f := fun y => ENNReal.ofReal (gsW κ N y))
    (ENNReal.measurable_ofReal.comp (measurable_gsW κ)).aemeasurable
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (gsW_pos κ _).le, smul_eq_mul]

theorem lintegral_gsMeas (κ : ℝ) {F : UnitAddTorus (Fin N × Fin 1) → ℝ≥0∞}
    (hF : AEMeasurable F volume) :
    ∫⁻ y, F y ∂gsMeas κ N = ∫⁻ y, ENNReal.ofReal (gsW κ N y) * F y :=
  lintegral_withDensity_eq_lintegral_mul₀
    (ENNReal.measurable_ofReal.comp (measurable_gsW κ)).aemeasurable hF

theorem gsW_bounds {κ : ℝ} (hκ : 0 ≤ κ) :
    ∃ m > 0, ∀ y : UnitAddTorus (Fin N × Fin 1), m ≤ gsW κ N y ∧ gsW κ N y ≤ gsC κ N := by
  obtain ⟨xM, xm, hmm⟩ := periodic_max_min (contDiff_UL (N := N) κ).continuous (smPer_UL κ).2
  refine ⟨gsC κ N * Real.exp (-UL κ N xM), mul_pos (gsC_pos κ N) (Real.exp_pos _), fun y => ?_⟩
  constructor
  · exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith [(hmm (secT y)).2]))
      (gsC_pos κ N).le
  · calc gsW κ N y ≤ gsC κ N * 1 := mul_le_mul_of_nonneg_left
          (Real.exp_le_one_iff.mpr (by linarith [UL_nonneg hκ (secT y)])) (gsC_pos κ N).le
      _ = gsC κ N := mul_one _

theorem integrable_gsW (κ : ℝ) : Integrable (gsW κ N) volume := by
  have := (smPer_UL (N := N) κ).expNeg.integrable.const_mul (gsC κ N)
  exact this

theorem integral_gsW (κ : ℝ) : ∫ y, gsW κ N y = 1 := by
  have h := integral_gsMeas (N := N) κ (fun _ => 1)
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul, mul_one] at h
  exact h.symm

theorem one_le_gsC {κ : ℝ} (hκ : 0 ≤ κ) : 1 ≤ gsC κ N := by
  have h := integral_gsW (N := N) κ
  simp only [gsW] at h
  rw [integral_const_mul] at h
  have hI : ∫ y : UnitAddTorus (Fin N × Fin 1), Real.exp (-UL κ N (secT y)) ≤ 1 := by
    calc ∫ y : UnitAddTorus (Fin N × Fin 1), Real.exp (-UL κ N (secT y))
        ≤ ∫ _y : UnitAddTorus (Fin N × Fin 1), (1 : ℝ) :=
          integral_mono (smPer_UL κ).expNeg.integrable (integrable_const 1) fun y =>
            Real.exp_le_one_iff.mpr (by linarith [UL_nonneg hκ (secT y)])
      _ = 1 := by simp
  have hI0 : 0 < ∫ y : UnitAddTorus (Fin N × Fin 1), Real.exp (-UL κ N (secT y)) := by
    have := gsC_pos κ N; nlinarith
  nlinarith [gsC_pos κ N]

theorem volume_le_smul_gsMeas {κ : ℝ} (hκ : 0 ≤ κ) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ (volume : Measure (UnitAddTorus (Fin N × Fin 1))) ≤ C • gsMeas κ N := by
  obtain ⟨m, hm, hb⟩ := gsW_bounds (N := N) hκ
  refine ⟨ENNReal.ofReal (1 / m), ENNReal.ofReal_ne_top, ?_⟩
  refine Measure.le_iff.2 fun s hs => ?_
  rw [Measure.smul_apply, smul_eq_mul, gsMeas, withDensity_apply _ hs,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← setLIntegral_one]
  refine setLIntegral_mono (measurable_const.mul (ENNReal.measurable_ofReal.comp (measurable_gsW κ)))
    fun y _ => ?_
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal (by rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hm, one_mul]; exact (hb y).1)

theorem gsMeas_le_smul_volume {κ : ℝ} (hκ : 0 ≤ κ) :
    gsMeas κ N ≤ ENNReal.ofReal (gsC κ N) • (volume : Measure (UnitAddTorus (Fin N × Fin 1))) := by
  obtain ⟨m, hm, hb⟩ := gsW_bounds (N := N) hκ
  refine Measure.le_iff.2 fun s hs => ?_
  rw [Measure.smul_apply, smul_eq_mul, gsMeas, withDensity_apply _ hs, ← setLIntegral_const]
  exact setLIntegral_mono measurable_const fun y _ => ENNReal.ofReal_le_ofReal (hb y).2

/-- The ground-state transform of the entropy:
`Ent_P(u²) = Ent_m(u²w) - c log(1/K) + ∫ u² U dP`, `c = ∫ u² dP`. -/
theorem ent_gsMeas_eq {κ : ℝ} (hκ : 0 ≤ κ) {u : UnitAddTorus (Fin N × Fin 1) → ℝ}
    (hu2 : MemLp u 2 volume) (hfin : ent volume (fun y => u y ^ 2 * gsW κ N y) ≠ ⊤) :
    ent (gsMeas κ N) (fun y => u y ^ 2) =
      ENNReal.ofReal ((ent volume (fun y => u y ^ 2 * gsW κ N y)).toReal -
        (∫ y, gsW κ N y * u y ^ 2) * Real.log (gsC κ N) +
        ∫ y, gsW κ N y * u y ^ 2 * UL κ N (secT y)) := by
  obtain ⟨m, hm, hb⟩ := gsW_bounds (N := N) hκ
  have hum : AEStronglyMeasurable u volume := hu2.aestronglyMeasurable
  have hgm := measurable_gsW (N := N) κ
  have hUm : Measurable fun y : UnitAddTorus (Fin N × Fin 1) => UL κ N (secT y) :=
    (contDiff_UL κ).continuous.measurable.comp measurable_secT
  obtain ⟨BU, hBU⟩ := periodic_bounded (contDiff_UL (N := N) κ).continuous (smPer_UL κ).2
  have hi2 : Integrable (fun y => u y ^ 2) volume := hu2.integrable_sq
  have hi2W : Integrable (fun y => u y ^ 2) (gsMeas κ N) :=
    (hu2.of_measure_le_smul ENNReal.ofReal_ne_top (gsMeas_le_smul_volume hκ)).integrable_sq
  have hgb : ∀ y, ‖gsW κ N y‖ ≤ gsC κ N := fun y => by
    rw [Real.norm_eq_abs, abs_of_pos (gsW_pos κ y)]; exact (hb y).2
  have hiv : Integrable (fun y => u y ^ 2 * gsW κ N y) volume :=
    hi2.mul_bdd hgm.aestronglyMeasurable (Eventually.of_forall hgb)
  have hiv' : Integrable (fun y => gsW κ N y * u y ^ 2) volume := by
    simpa only [mul_comm] using hiv
  set c := ∫ y, gsW κ N y * u y ^ 2 with hc
  have hcW : ∫ y, u y ^ 2 ∂gsMeas κ N = c := integral_gsMeas κ _
  have hcv : ∫ y, u y ^ 2 * gsW κ N y = c := by rw [hc]; congr 1; funext y; ring
  have hc0 : 0 ≤ c := integral_nonneg fun y => mul_nonneg (gsW_pos κ y).le (sq_nonneg _)
  have hiU : Integrable (fun y => gsW κ N y * u y ^ 2 * UL κ N (secT y)) volume :=
    hiv'.mul_bdd hUm.aestronglyMeasurable (Eventually.of_forall fun y => hBU _)
  rcases hc0.eq_or_lt with h0 | h0
  · -- `u = 0` a.e.
    have hz : (fun y => gsW κ N y * u y ^ 2) =ᵐ[volume] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun y => mul_nonneg (gsW_pos κ y).le (sq_nonneg _))
        hiv').mp h0.symm
    have hL : ent (gsMeas κ N) (fun y => u y ^ 2) = 0 := by
      rcases ent_eq_zero_of_integral_eq_zero (P := gsMeas κ N) (by rw [hcW, ← h0]) with h | h
      · exact h
      · exact absurd hi2W h
    have hR : ent volume (fun y => u y ^ 2 * gsW κ N y) = 0 := by
      rcases ent_eq_zero_of_integral_eq_zero (P := volume) (by rw [hcv, ← h0]) with h | h
      · exact h
      · exact absurd hiv h
    have hU0 : ∫ y, gsW κ N y * u y ^ 2 * UL κ N (secT y) = 0 := by
      rw [integral_congr_ae (hz.mono fun y hy => by
        show gsW κ N y * u y ^ 2 * UL κ N (secT y) = (0 : UnitAddTorus (Fin N × Fin 1) → ℝ) y
        simp only [Pi.zero_apply] at hy ⊢; rw [hy, zero_mul])]
      simp
    rw [hL, hR, ← h0, hU0]; simp
  · -- `c > 0`
    have hcne : c ≠ 0 := h0.ne'
    set A : UnitAddTorus (Fin N × Fin 1) → ℝ := fun y => c * klFun (u y ^ 2 * gsW κ N y / c)
      with hA
    set B : UnitAddTorus (Fin N × Fin 1) → ℝ :=
      fun y => u y ^ 2 * gsW κ N y * Real.log (gsW κ N y) + c * (1 - gsW κ N y) with hB
    have hA0 : ∀ y, 0 ≤ A y := fun y =>
      mul_nonneg hc0 (klFun_nonneg (div_nonneg (mul_nonneg (sq_nonneg _) (gsW_pos κ y).le) hc0))
    have hpt : ∀ y, gsW κ N y * (c * klFun (u y ^ 2 / c)) = A y - B y := fun y => by
      simp only [hA, hB, klFun_apply]
      by_cases hu0 : u y = 0
      · simp [hu0]; ring
      · have hu2 : u y ^ 2 ≠ 0 := pow_ne_zero 2 hu0
        rw [show u y ^ 2 * gsW κ N y / c = (u y ^ 2 / c) * gsW κ N y by ring,
          Real.log_mul (div_ne_zero hu2 hcne) (gsW_pos κ y).ne']
        field_simp
        ring
    -- `ent_m(v²) = ∫⁻ A`
    have hentv : ent volume (fun y => u y ^ 2 * gsW κ N y) = ∫⁻ y, ENNReal.ofReal (A y) := by
      unfold ent; rw [if_pos hiv, hcv]
    have hAm : AEStronglyMeasurable A volume :=
      (continuous_const.mul continuous_klFun).comp_aestronglyMeasurable
        (hiv.div_const c).aestronglyMeasurable
    have hAi : Integrable A volume := by
      refine ⟨hAm, ?_⟩
      unfold HasFiniteIntegral
      have : (fun y => ‖A y‖ₑ) = fun y => ENNReal.ofReal (A y) := funext fun y =>
        Real.enorm_of_nonneg (hA0 y)
      rw [this, ← hentv]
      exact lt_top_iff_ne_top.mpr hfin
    have hAint : (ent volume (fun y => u y ^ 2 * gsW κ N y)).toReal = ∫ y, A y := by
      rw [hentv, ← ofReal_integral_eq_lintegral_ofReal hAi (Eventually.of_forall hA0),
        ENNReal.toReal_ofReal (integral_nonneg hA0)]
    have hlogb : ∀ y, |Real.log (gsW κ N y)| ≤ |Real.log m| + |Real.log (gsC κ N)| := fun y => by
      have h1 := Real.log_le_log hm (hb y).1
      have h2 := Real.log_le_log (gsW_pos κ y) (hb y).2
      rw [abs_le]; constructor
      · have := neg_abs_le (Real.log m); have := abs_nonneg (Real.log (gsC κ N)); linarith
      · have := le_abs_self (Real.log (gsC κ N)); have := abs_nonneg (Real.log m); linarith
    have hB1 : Integrable (fun y => u y ^ 2 * gsW κ N y * Real.log (gsW κ N y)) volume :=
      hiv.mul_bdd (Real.measurable_log.comp hgm).aestronglyMeasurable
        (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hlogb y)
    have hB2 : Integrable (fun y => c * (1 - gsW κ N y)) volume :=
      ((integrable_const 1).sub (integrable_gsW κ)).const_mul c
    have hBi : Integrable B volume := hB1.add hB2
    have hBint : ∫ y, B y = c * Real.log (gsC κ N) - ∫ y, gsW κ N y * u y ^ 2 * UL κ N (secT y) := by
      rw [integral_add hB1 hB2, integral_const_mul, integral_sub (integrable_const 1) (integrable_gsW κ),
        integral_gsW]
      have e : ∀ y, u y ^ 2 * gsW κ N y * Real.log (gsW κ N y) =
          Real.log (gsC κ N) * (gsW κ N y * u y ^ 2) - gsW κ N y * u y ^ 2 * UL κ N (secT y) :=
        fun y => by
          rw [gsW, Real.log_mul (gsC_pos κ N).ne' (Real.exp_pos _).ne', Real.log_exp]; ring
      simp_rw [e]
      rw [integral_sub (hiv'.const_mul _) hiU, integral_const_mul, ← hc]
      simp only [integral_const, probReal_univ, smul_eq_mul, one_mul, sub_self, mul_zero, add_zero]
      ring
    -- the left side
    rw [hAint]
    unfold ent
    rw [if_pos hi2W, hcW]
    beta_reduce
    rw [lintegral_gsMeas (F := fun x => ENNReal.ofReal (c * klFun (u x ^ 2 / c))) κ
      (ENNReal.measurable_ofReal.comp_aemeasurable
        ((continuous_const.mul continuous_klFun).comp_aestronglyMeasurable
          (hi2.div_const c).aestronglyMeasurable).aemeasurable)]
    have e1 : ∀ y, ENNReal.ofReal (gsW κ N y) * ENNReal.ofReal (c * klFun (u y ^ 2 / c)) =
        ENNReal.ofReal (A y - B y) := fun y => by
      rw [← ENNReal.ofReal_mul (gsW_pos κ y).le, hpt]
    simp_rw [e1]
    have hAB0 : ∀ y, 0 ≤ A y - B y := fun y => by
      rw [← hpt]; exact mul_nonneg (gsW_pos κ y).le (mul_nonneg hc0
        (klFun_nonneg (div_nonneg (sq_nonneg _) hc0)))
    have hABi : Integrable (fun y => A y - B y) volume := hAi.sub hBi
    rw [← ofReal_integral_eq_lintegral_ofReal hABi (Eventually.of_forall hAB0),
      integral_sub hAi hBi, hBint]
    congr 1
    ring

theorem Dk_expNeg_UL (κ : ℝ) (k : Fin N × Fin 1) (x : Fin N × Fin 1 → ℝ) :
    Dk (fun x => gsC κ N * Real.exp (-UL κ N x)) k x =
      -(gsC κ N * Real.exp (-UL κ N x)) * Dk (UL κ N) k x := by
  have hU : Differentiable ℝ (UL κ N) := (contDiff_UL κ).differentiable (by simp)
  have hd : HasFDerivAt (fun x => gsC κ N * Real.exp (-UL κ N x))
      (gsC κ N • (Real.exp (-UL κ N x) • -fderiv ℝ (UL κ N) x)) x :=
    ((hU x).hasFDerivAt.neg.exp).const_mul (gsC κ N)
  rw [Dk, hd.fderiv, Dk]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, ContinuousLinearMap.neg_apply]
  ring

/-- `∫ w u ∂_k u ∂_kU = -½ ∫ w u² (∂_k²U - (∂_kU)²)`. -/
theorem ibp_gs {κ : ℝ} {u : UnitAddTorus (Fin N × Fin 1) → ℝ}
    {g : UnitAddTorus (Fin N × Fin 1) → Fin N × Fin 1 → ℝ} (hw : IsWeakGrad u g)
    (hu2 : MemLp u 2 volume) (hg2 : ∀ k, MemLp (fun y => g y k) 2 volume) (k : Fin N × Fin 1) :
    ∫ y, gsW κ N y * u y * g y k * Dk (UL κ N) k (secT y) =
      -(1 / 2) * ∫ y, gsW κ N y * u y ^ 2 *
        (Dk (Dk (UL κ N) k) k (secT y) - Dk (UL κ N) k (secT y) ^ 2) := by
  have hsq := isWeakGrad_sq hw hu2 hg2
  have hgi : ∀ j, Integrable (fun y => 2 * u y * g y j) volume := fun j => by
    refine Integrable.mono' (hu2.integrable_sq.add (hg2 j).integrable_sq)
      ((hu2.aestronglyMeasurable.const_mul 2).mul (hg2 j).aestronglyMeasurable)
      (Eventually.of_forall fun y => ?_)
    show ‖2 * u y * g y j‖ ≤ u y ^ 2 + g y j ^ 2
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> nlinarith [sq_nonneg (u y + g y j), sq_nonneg (u y - g y j)]
  have hU := smPer_UL (N := N) κ
  set E : (Fin N × Fin 1 → ℝ) → ℝ := fun x => gsC κ N * Real.exp (-UL κ N x) with hE
  have hEs : SmPer E := hU.expNeg.const_mul _
  set Θ' : (Fin N × Fin 1 → ℝ) → ℝ := fun x => E x * Dk (UL κ N) k x with hΘ'
  have hΘs : SmPer Θ' := hEs.mul (hU.Dk k)
  have hDΘ : ∀ x, Dk Θ' k x = E x * (Dk (Dk (UL κ N) k) k x - Dk (UL κ N) k x ^ 2) := fun x => by
    rw [hΘ', Dk_mul (hEs.1.differentiable (by simp)) ((hU.Dk k).1.differentiable (by simp)),
      hE, Dk_expNeg_UL]
    ring
  have key := integral_mul_Dk_eq hsq hu2.integrable_sq hgi hΘs.1 hΘs.2 k
  have hEsec : ∀ y, E (secT y) = gsW κ N y := fun y => rfl
  simp_rw [hDΘ, hΘ', hEsec] at key
  have e1 : ∫ y, u y ^ 2 * (gsW κ N y * (Dk (Dk (UL κ N) k) k (secT y) - Dk (UL κ N) k (secT y) ^ 2)) =
      ∫ y, gsW κ N y * u y ^ 2 * (Dk (Dk (UL κ N) k) k (secT y) - Dk (UL κ N) k (secT y) ^ 2) := by
    congr 1; funext y; ring
  have e2 : ∫ y, 2 * u y * g y k * (gsW κ N y * Dk (UL κ N) k (secT y)) =
      2 * ∫ y, gsW κ N y * u y * g y k * Dk (UL κ N) k (secT y) := by
    rw [← integral_const_mul]; congr 1; funext y; ring
  rw [e1, e2] at key
  linarith

theorem integrable_mul_smPer {ι' : Type} [Fintype ι'] [DecidableEq ι'] {F : UnitAddTorus ι' → ℝ}
    (hF : Integrable F volume) {Φ : (ι' → ℝ) → ℝ} (hΦ : SmPer Φ) :
    Integrable (fun y => F y * Φ (secT y)) volume := by
  obtain ⟨B, hB⟩ := periodic_bounded hΦ.1.continuous hΦ.2
  exact hF.mul_bdd (hΦ.1.continuous.measurable.comp measurable_secT).aestronglyMeasurable
    (Eventually.of_forall fun y => hB _)

/-- The ground-state energy: `∫ |∇(uΘ)|² ≤ ∫ w|∇u|² + (aκ/2) ∫ w u² - a ∫ w u² U`. -/
theorem energy_gs_le {κ : ℝ} (hN : 1 ≤ N) {u : UnitAddTorus (Fin N × Fin 1) → ℝ}
    {g : UnitAddTorus (Fin N × Fin 1) → Fin N × Fin 1 → ℝ} (hw : IsWeakGrad u g)
    (hu2 : MemLp u 2 volume) (hg2 : ∀ k, MemLp (fun y => g y k) 2 volume) :
    ∫ y, sqNorm (fun k => g y k * gsTheta κ N (secT y) + u y * Dk (gsTheta κ N) k (secT y)) ≤
      (∫ y, gsW κ N y * sqNorm (g y)) + aCos * κ / 2 * (∫ y, gsW κ N y * u y ^ 2) -
        aCos * ∫ y, gsW κ N y * u y ^ 2 * UL κ N (secT y) := by
  have hU := smPer_UL (N := N) κ
  have hW : SmPer (fun x => gsC κ N * Real.exp (-UL κ N x)) := hU.expNeg.const_mul _
  have hWsec : ∀ y, gsC κ N * Real.exp (-UL κ N (secT y)) = gsW κ N y := fun y => rfl
  -- integrable pieces
  have hu2i : Integrable (fun y => u y ^ 2) volume := hu2.integrable_sq
  have hug : ∀ k, Integrable (fun y => u y * g y k) volume := fun k => by
    refine Integrable.mono' (hu2.integrable_sq.add (hg2 k).integrable_sq)
      (hu2.aestronglyMeasurable.mul (hg2 k).aestronglyMeasurable)
      (Eventually.of_forall fun y => ?_)
    show ‖u y * g y k‖ ≤ u y ^ 2 + g y k ^ 2
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> nlinarith [sq_nonneg (u y + g y k), sq_nonneg (u y - g y k)]
  have hsqg : Integrable (fun y => sqNorm (g y)) volume :=
    integrable_finset_sum _ fun k _ => (hg2 k).integrable_sq
  have i1 : Integrable (fun y => gsW κ N y * sqNorm (g y)) volume := by
    have := integrable_mul_smPer hsqg hW
    exact this.congr (Eventually.of_forall fun y => by simp only [hWsec]; ring)
  have i2 : ∀ k, Integrable (fun y => gsW κ N y * u y * g y k * Dk (UL κ N) k (secT y)) volume :=
    fun k => by
      have := integrable_mul_smPer (hug k) (hW.mul (hU.Dk k))
      exact this.congr (Eventually.of_forall fun y => by simp only [hWsec]; ring)
  have i3 : Integrable (fun y => gsW κ N y * u y ^ 2 * ∑ k, Dk (UL κ N) k (secT y) ^ 2) volume := by
    have := integrable_mul_smPer hu2i (hW.mul (SmPer.sum Finset.univ fun k => (hU.Dk k).sq'))
    exact this.congr (Eventually.of_forall fun y => by simp only [hWsec]; ring)
  have i4 : ∀ k, Integrable (fun y => gsW κ N y * u y ^ 2 *
      (Dk (Dk (UL κ N) k) k (secT y) - Dk (UL κ N) k (secT y) ^ 2)) volume := fun k => by
    have := integrable_mul_smPer hu2i (hW.mul (((hU.Dk k).Dk k).sub (hU.Dk k).sq'))
    exact this.congr (Eventually.of_forall fun y => by simp only [hWsec]; ring)
  have i5 : Integrable (fun y => gsW κ N y * u y ^ 2) volume := by
    have := integrable_mul_smPer hu2i hW
    exact this.congr (Eventually.of_forall fun y => by simp only [hWsec]; ring)
  have i6 : Integrable (fun y => gsW κ N y * u y ^ 2 * UL κ N (secT y)) volume := by
    have := integrable_mul_smPer hu2i (hW.mul hU)
    exact this.congr (Eventually.of_forall fun y => by simp only [hWsec]; ring)
  -- pointwise expansion
  have hpt : ∀ y, sqNorm (fun k => g y k * gsTheta κ N (secT y) + u y * Dk (gsTheta κ N) k (secT y)) =
      gsW κ N y * sqNorm (g y) - ∑ k, gsW κ N y * u y * g y k * Dk (UL κ N) k (secT y) +
        1 / 4 * (gsW κ N y * u y ^ 2 * ∑ k, Dk (UL κ N) k (secT y) ^ 2) := fun y => by
    unfold sqNorm
    simp_rw [Dk_gsTheta]
    rw [← gsTheta_sq κ y, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  -- the Laplacian
  have hlap : ∀ y, ∑ k, (Dk (Dk (UL κ N) k) k (secT y) - Dk (UL κ N) k (secT y) ^ 2) =
      aCos * κ - 2 * aCos * UL κ N (secT y) - ∑ k, Dk (UL κ N) k (secT y) ^ 2 := fun y => by
    rw [Finset.sum_sub_distrib, laplacian_UL κ hN]
  have hI2 : ∑ k, ∫ y, gsW κ N y * u y * g y k * Dk (UL κ N) k (secT y) =
      -(1 / 2) * (aCos * κ * (∫ y, gsW κ N y * u y ^ 2) -
        2 * aCos * (∫ y, gsW κ N y * u y ^ 2 * UL κ N (secT y)) -
        ∫ y, gsW κ N y * u y ^ 2 * ∑ k, Dk (UL κ N) k (secT y) ^ 2) := by
    simp_rw [ibp_gs hw hu2 hg2]
    rw [← Finset.mul_sum, ← integral_finset_sum _ fun k _ => i4 k]
    congr 1
    have e : ∀ y, ∑ k, gsW κ N y * u y ^ 2 *
        (Dk (Dk (UL κ N) k) k (secT y) - Dk (UL κ N) k (secT y) ^ 2) =
        aCos * κ * (gsW κ N y * u y ^ 2) - 2 * aCos * (gsW κ N y * u y ^ 2 * UL κ N (secT y)) -
          gsW κ N y * u y ^ 2 * ∑ k, Dk (UL κ N) k (secT y) ^ 2 := fun y => by
      rw [← Finset.mul_sum, hlap]; ring
    simp_rw [e]
    have ia : Integrable (fun y => aCos * κ * (gsW κ N y * u y ^ 2) -
        2 * aCos * (gsW κ N y * u y ^ 2 * UL κ N (secT y))) volume :=
      (i5.const_mul _).sub (i6.const_mul _)
    rw [integral_sub (f := fun y => aCos * κ * (gsW κ N y * u y ^ 2) -
        2 * aCos * (gsW κ N y * u y ^ 2 * UL κ N (secT y)))
        (g := fun y => gsW κ N y * u y ^ 2 * ∑ k, Dk (UL κ N) k (secT y) ^ 2) ia i3,
      integral_sub (f := fun y => aCos * κ * (gsW κ N y * u y ^ 2))
        (g := fun y => 2 * aCos * (gsW κ N y * u y ^ 2 * UL κ N (secT y)))
        (i5.const_mul _) (i6.const_mul _), integral_const_mul, integral_const_mul]
  have hI3 : 0 ≤ ∫ y, gsW κ N y * u y ^ 2 * ∑ k, Dk (UL κ N) k (secT y) ^ 2 :=
    integral_nonneg fun y => mul_nonneg (mul_nonneg (gsW_pos κ y).le (sq_nonneg _))
      (Finset.sum_nonneg fun k _ => sq_nonneg _)
  simp_rw [hpt]
  have ib : Integrable (fun y => gsW κ N y * sqNorm (g y) -
      ∑ k, gsW κ N y * u y * g y k * Dk (UL κ N) k (secT y)) volume :=
    i1.sub (integrable_finset_sum _ fun k _ => i2 k)
  have ic : Integrable (fun y => ∑ k, gsW κ N y * u y * g y k * Dk (UL κ N) k (secT y)) volume :=
    integrable_finset_sum _ fun k _ => i2 k
  rw [integral_add (f := fun y => gsW κ N y * sqNorm (g y) -
      ∑ k, gsW κ N y * u y * g y k * Dk (UL κ N) k (secT y))
      (g := fun y => 1 / 4 * (gsW κ N y * u y ^ 2 * ∑ k, Dk (UL κ N) k (secT y) ^ 2))
      ib (i3.const_mul _),
    integral_sub (f := fun y => gsW κ N y * sqNorm (g y))
      (g := fun y => ∑ k, gsW κ N y * u y * g y k * Dk (UL κ N) k (secT y)) i1 ic,
    integral_finset_sum _ fun k _ => i2 k, integral_const_mul, hI2]
  nlinarith

/-- The defective inequality on the flat torus, for `u ∈ H¹(w·m)`. -/
theorem defective_flat {κ : ℝ} (hκ : 0 < κ) (hN : 1 ≤ N) {u : UnitAddTorus (Fin N × Fin 1) → ℝ}
    (hu : MemH1 (gsMeas κ N) u) :
    ent (gsMeas κ N) (fun y => u y ^ 2) ≤
      ENNReal.ofReal (2 / aCos) * dirichlet (gsMeas κ N) u +
        ENNReal.ofReal κ * ∫⁻ y, ENNReal.ofReal (u y ^ 2) ∂gsMeas κ N := by
  have ha0 : 0 < aCos := by unfold aCos; positivity
  obtain ⟨C, hC, hle⟩ := volume_le_smul_gsMeas (N := N) hκ.le
  have hac : gsMeas κ N ≪ volume := withDensity_absolutelyContinuous _ _
  have hw := isWeakGrad_weakGrad hu.1
  set g := weakGrad u with hg
  have hu2 : MemLp u 2 volume := hu.2.1.of_measure_le_smul hC hle
  have hg2W : ∀ k, MemLp (fun y => g y k) 2 (gsMeas κ N) := fun k =>
    hu.2.2.of_le ((hw.aestronglyMeasurable_grad k).mono_ac hac) (Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      exact abs_le_sqrt_sqNorm _ k)
  have hg2 : ∀ k, MemLp (fun y => g y k) 2 volume := fun k => (hg2W k).of_measure_le_smul hC hle
  -- the ground state
  have hΘ := smPer_gsTheta (N := N) κ
  set T : UnitAddTorus (Fin N × Fin 1) → ℝ := fun y => gsTheta κ N (secT y) with hT
  set v : UnitAddTorus (Fin N × Fin 1) → ℝ := fun y => u y * T y with hv
  set G : UnitAddTorus (Fin N × Fin 1) → Fin N × Fin 1 → ℝ :=
    fun y k => g y k * gsTheta κ N (secT y) + u y * Dk (gsTheta κ N) k (secT y) with hG
  have hvw : IsWeakGrad v G := hw.mul_smooth hΘ.1 hΘ.2
  obtain ⟨BT, hBT⟩ := periodic_bounded hΘ.1.continuous hΘ.2
  have hbd : ∀ k, ∃ B, ∀ x, ‖Dk (gsTheta κ N) k x‖ ≤ B := fun k =>
    periodic_bounded (hΘ.Dk k).1.continuous (hΘ.Dk k).2
  choose BD hBD using hbd
  have hTm : Measurable T := hΘ.1.continuous.measurable.comp measurable_secT
  have hDm : ∀ k, Measurable fun y => Dk (gsTheta κ N) k (secT y) := fun k =>
    (hΘ.Dk k).1.continuous.measurable.comp measurable_secT
  have memLp_mul : ∀ {F : UnitAddTorus (Fin N × Fin 1) → ℝ} {H : UnitAddTorus (Fin N × Fin 1) → ℝ},
      MemLp F 2 volume → Measurable H → ∀ B, (∀ y, ‖H y‖ ≤ B) →
        MemLp (fun y => F y * H y) 2 volume := fun {F} {H} hF hH B hB =>
    (hF.const_mul B).of_le (hF.aestronglyMeasurable.mul hH.aestronglyMeasurable)
      (Eventually.of_forall fun y => by
        rw [norm_mul, norm_mul]
        have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB y)
        rw [Real.norm_of_nonneg hB0, mul_comm]
        exact mul_le_mul_of_nonneg_right (hB y) (norm_nonneg _))
  have hv2 : MemLp v 2 volume := memLp_mul hu2 hTm BT fun y => hBT _
  have hG2 : ∀ k, MemLp (fun y => G y k) 2 volume := fun k =>
    (memLp_mul (hg2 k) hTm BT fun y => hBT _).add (memLp_mul hu2 (hDm k) (BD k) fun y => hBD k _)
  have hvH : HasWeakGrad v := ⟨G, hvw⟩
  have hGae : weakGrad v =ᵐ[volume] G := weakGrad_ae_unique (isWeakGrad_weakGrad hvH) hvw
  have hsqG : Integrable (fun y => sqNorm (G y)) volume :=
    integrable_finset_sum _ fun k _ => (hG2 k).integrable_sq
  have hvH1 : MemH1 volume v := by
    refine ⟨hvH, hv2, ?_⟩
    have hm : AEStronglyMeasurable (fun y => Real.sqrt (sqNorm (weakGrad v y))) volume :=
      Real.continuous_sqrt.comp_aestronglyMeasurable
        (isWeakGrad_weakGrad hvH).aestronglyMeasurable_sqNorm
    refine (memLp_two_iff_integrable_sq hm).2 ?_
    refine hsqG.congr (hGae.mono fun y hy => ?_)
    show sqNorm (G y) = Real.sqrt (sqNorm (weakGrad v y)) ^ 2
    rw [Real.sq_sqrt (show 0 ≤ sqNorm (weakGrad v y) from Finset.sum_nonneg fun k _ => sq_nonneg _),
      hy]
  have hL := lsi_torus_H1 hvH1
  have hdirv : dirichlet volume v = ENNReal.ofReal (∫ y, sqNorm (G y)) := by
    rw [dirichlet_eq_ofReal hvH1]
    congr 1
    exact integral_congr_ae (hGae.mono fun y hy => by simp only [hy])
  have hJ := energy_gs_le (κ := κ) hN hw hu2 hg2
  set J := ∫ y, sqNorm (G y) with hJdef
  have hJ0 : 0 ≤ J := integral_nonneg fun y => Finset.sum_nonneg fun k _ => sq_nonneg _
  have hvsq : (fun y => v y ^ 2) = fun y => u y ^ 2 * gsW κ N y := funext fun y => by
    simp only [hv, hT]; rw [mul_pow, gsTheta_sq]
  rw [hvsq, hdirv] at hL
  rw [← ENNReal.ofReal_mul (p := 2 / aCos) (by positivity)] at hL
  have hfin : ent volume (fun y => u y ^ 2 * gsW κ N y) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hL
  have hentV : (ent volume (fun y => u y ^ 2 * gsW κ N y)).toReal ≤ 2 / aCos * J :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) hL
  -- the measure `w·m`
  have hsqgW : Integrable (fun y => sqNorm (g y)) (gsMeas κ N) :=
    integrable_finset_sum _ fun k _ => (hg2W k).integrable_sq
  have hdirW : dirichlet (gsMeas κ N) u = ENNReal.ofReal (∫ y, gsW κ N y * sqNorm (g y)) := by
    unfold dirichlet
    rw [← ofReal_integral_eq_lintegral_ofReal hsqgW
      (Eventually.of_forall fun y => Finset.sum_nonneg fun k _ => sq_nonneg _), integral_gsMeas]
  have hu2W : Integrable (fun y => u y ^ 2) (gsMeas κ N) := hu.2.1.integrable_sq
  have hlinW : ∫⁻ y, ENNReal.ofReal (u y ^ 2) ∂gsMeas κ N =
      ENNReal.ofReal (∫ y, gsW κ N y * u y ^ 2) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hu2W (Eventually.of_forall fun y => sq_nonneg _),
      integral_gsMeas]
  have hp1 : 0 ≤ 2 / aCos * ∫ y, gsW κ N y * sqNorm (g y) :=
    mul_nonneg (by positivity) (integral_nonneg fun y =>
      mul_nonneg (gsW_pos κ y).le (show 0 ≤ sqNorm (g y) from Finset.sum_nonneg fun k _ => sq_nonneg _))
  have hp2 : 0 ≤ κ * ∫ y, gsW κ N y * u y ^ 2 :=
    mul_nonneg hκ.le (integral_nonneg fun y => mul_nonneg (gsW_pos κ y).le (sq_nonneg _))
  rw [ent_gsMeas_eq hκ.le hu2 hfin, hdirW, hlinW, ← ENNReal.ofReal_mul (p := 2 / aCos) (by positivity),
    ← ENNReal.ofReal_mul hκ.le, ← ENNReal.ofReal_add hp1 hp2]
  refine ENNReal.ofReal_le_ofReal ?_
  have hc0 : 0 ≤ ∫ y, gsW κ N y * u y ^ 2 :=
    integral_nonneg fun y => mul_nonneg (gsW_pos κ y).le (sq_nonneg _)
  have hlog : 0 ≤ Real.log (gsC κ N) := Real.log_nonneg (one_le_gsC hκ.le)
  have hIU : 0 ≤ ∫ y, gsW κ N y * u y ^ 2 * UL κ N (secT y) :=
    integral_nonneg fun y => mul_nonneg (mul_nonneg (gsW_pos κ y).le (sq_nonneg _))
      (UL_nonneg hκ.le _)
  have h2J : 2 / aCos * J ≤ 2 / aCos * ((∫ y, gsW κ N y * sqNorm (g y)) +
      aCos * κ / 2 * (∫ y, gsW κ N y * u y ^ 2) -
      aCos * ∫ y, gsW κ N y * u y ^ 2 * UL κ N (secT y)) :=
    mul_le_mul_of_nonneg_left hJ (by positivity)
  have e : 2 / aCos * ((∫ y, gsW κ N y * sqNorm (g y)) +
      aCos * κ / 2 * (∫ y, gsW κ N y * u y ^ 2) -
      aCos * ∫ y, gsW κ N y * u y ^ 2 * UL κ N (secT y)) =
      2 / aCos * (∫ y, gsW κ N y * sqNorm (g y)) + κ * (∫ y, gsW κ N y * u y ^ 2) -
        2 * ∫ y, gsW κ N y * u y ^ 2 * UL κ N (secT y) := by
    field_simp
  rw [e] at h2J
  nlinarith [mul_nonneg hc0 hlog]

/-- Lemma 3.6, (3.29): the defective inequality. -/
theorem cosine_defective_aux {κ : ℝ} (hκ : 0 < κ) (hN : 1 ≤ N) {f : Config N 1 → ℝ}
    (hf : MemH1C (gibbs cosV (cosW κ) N) f) :
    ent (gibbs cosV (cosW κ) N) (fun X => f X ^ 2) ≤
      ENNReal.ofReal (2 / aCos) * energy cosV (cosW κ) N f +
        ENNReal.ofReal κ * ∫⁻ X, ENNReal.ofReal (f X ^ 2) ∂gibbs cosV (cosW κ) N := by
  have hH1 : MemH1 ((gibbs cosV (cosW κ) N).map flat) (f ∘ unflat) := hf
  have henergy := energy_eq_dirichlet (cosine_hyp_all κ) hH1.1
  have hm : AEStronglyMeasurable (fun y => (f ∘ unflat) y ^ 2) ((gibbs cosV (cosW κ) N).map flat) :=
    hH1.2.1.aestronglyMeasurable.pow 2
  have hent := ent_comp (gibbs cosV (cosW κ) N) measurable_flat hm
  have hlin : ∫⁻ X, ENNReal.ofReal (f X ^ 2) ∂gibbs cosV (cosW κ) N =
      ∫⁻ y, ENNReal.ofReal ((f ∘ unflat) y ^ 2) ∂((gibbs cosV (cosW κ) N).map flat) :=
    (lintegral_map' (ENNReal.measurable_ofReal.comp_aemeasurable hm.aemeasurable)
      measurable_flat.aemeasurable).symm
  rw [show (fun X => f X ^ 2) = fun X => (f ∘ unflat) (flat X) ^ 2 from rfl, hent, henergy, hlin]
  rw [gibbs_map_flat_eq] at hH1 ⊢
  exact defective_flat hκ hN hH1

end Cosine

end SharpLSI
