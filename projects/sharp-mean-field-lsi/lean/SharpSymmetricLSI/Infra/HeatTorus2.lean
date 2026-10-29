import SharpSymmetricLSI.Infra.HeatTorus

/-!
# The periodic heat kernel on `𝕋^ι` (I4, part 2): Fourier coefficients

* `heatP_fourier`: `∫ P_t(z) e^{-2πik·z} dz = e^{-4π²|k|²t}`.
* `gauss_fourier`: `∫_{ℝ^ι} G_t(y) e^{-2πik·y} dy = e^{-4π²|k|²t}` for the Gaussian `heatKernel`.
* `measure_eq_of_mFourier`: finite measures on `𝕋^ι` with equal Fourier coefficients are equal.
-/

open MeasureTheory Set Filter Topology Complex UnitAddTorus
open scoped Real ContDiff

namespace SharpLSI

variable {ι : Type*} [Fintype ι]

/-- The Fourier multiplier `e^{-4π²|k|²t}` of `e^{tΔ}`. -/
noncomputable def heatMult (t : ℝ) (k : ι → ℤ) : ℝ :=
  ∏ i, Real.exp (-(4 * π ^ 2) * (k i : ℝ) ^ 2 * t)

theorem heatMult_pos (t : ℝ) (k : ι → ℤ) : 0 < heatMult t k :=
  Finset.prod_pos fun _ _ => Real.exp_pos _

theorem heat_mFourier_liftT (n : ι → ℤ) (x : ι → ℝ) :
    mFourier n (liftT x) = ∏ i, cexp (2 * π * I * n i * x i) := by
  simp only [mFourier, ContinuousMap.coe_mk, liftT, fourier_coe_apply, ofReal_one, div_one]

/-- Integrals over `𝕋^ι` are integrals over the unit box. -/
theorem integral_torus_eq_box {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : UnitAddTorus ι → E} (hg : AEStronglyMeasurable g volume) :
    ∫ z, g z = ∫ x in unitBox ι, g (liftT x) := by
  rw [← (measurePreserving_liftT (ι := ι)).map_eq] at hg ⊢
  exact integral_map measurable_liftT.aemeasurable hg

theorem volume_restrict_unitBox :
    (volume : Measure (ι → ℝ)).restrict (unitBox ι) =
      Measure.pi fun _ => (volume : Measure ℝ).restrict (Ioc 0 1) := by
  rw [unitBox, ← Measure.restrict_pi_pi, volume_pi]

theorem integral_unitBox_prod (f : ι → ℝ → ℂ) :
    ∫ x in unitBox ι, ∏ i, f i (x i) = ∏ i, ∫ y in Ioc (0 : ℝ) 1, f i y := by
  rw [volume_restrict_unitBox]
  exact integral_fintype_prod_eq_prod (μ := fun _ => (volume : Measure ℝ).restrict (Ioc 0 1)) f

/-- Fourier coefficients of the torus kernel. -/
theorem heatP_fourier {t : ℝ} (ht : 0 < t) (k : ι → ℤ) :
    ∫ z, (heatP t z : ℂ) * mFourier (-k) z = (heatMult t k : ℂ) := by
  rw [integral_torus_eq_box (by
    exact ((continuous_ofReal.comp (continuous_heatP ht)).mul
      (mFourier (-k)).continuous).aestronglyMeasurable)]
  have h : ∀ x : ι → ℝ, (heatP t (liftT x) : ℂ) * mFourier (-k) (liftT x) =
      ∏ i, ((heatK t (x i) : ℂ) * cexp (-(2 * π * I * k i * x i))) := by
    intro x
    rw [heatP_liftT, heat_mFourier_liftT, heatPL, ofReal_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    congr 1
    simp only [Pi.neg_apply, Int.cast_neg]
    ring_nf
  simp_rw [h]
  rw [integral_unitBox_prod (fun i y => (heatK t y : ℂ) * cexp (-(2 * π * I * k i * y))),
    heatMult, ofReal_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← intervalIntegral.integral_of_le zero_le_one, heatK_fourier ht]

/-! ### The Gaussian -/

/-- The one-dimensional Gaussian `(4πt)^{-1/2} e^{-s²/(4t)}`. -/
noncomputable def gauss1 (t s : ℝ) : ℝ := (4 * π * t) ^ (-(1 : ℝ) / 2) * Real.exp (-s ^ 2 / (4 * t))

theorem heatKernel_eq_prod {t : ℝ} (ht : 0 < t) (y : ι → ℝ) :
    heatKernel t y = ∏ i, gauss1 t (y i) := by
  unfold heatKernel gauss1
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ← Real.exp_sum]
  congr 1
  · rw [← Real.rpow_mul_natCast (by positivity)]
    congr 1; ring
  · congr 1
    simp only [← Finset.sum_neg_distrib, Finset.sum_div]

theorem gauss1_fourier {t : ℝ} (ht : 0 < t) (n : ℤ) :
    ∫ s : ℝ, (gauss1 t s : ℂ) * cexp (-(2 * π * I * n * s)) =
      (Real.exp (-(4 * π ^ 2) * (n : ℝ) ^ 2 * t) : ℂ) := by
  have hpos : (0 : ℝ) < 4 * π * t := by positivity
  set a : ℝ := 4 * π * t with ha
  have h : ∀ s : ℝ, (gauss1 t s : ℂ) * cexp (-(2 * π * I * n * s)) =
      cexp ((-(1 / (4 * t)) : ℂ) * s ^ 2 + (-(2 * π * I * n)) * s +
        ((-(1 / 2 : ℝ) * Real.log a : ℝ) : ℂ)) := by
    intro s
    rw [gauss1, ofReal_mul, Real.rpow_def_of_pos hpos, ofReal_exp, ofReal_exp,
      ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast; ring
  simp_rw [h]
  have hb : ((-(1 / (4 * t)) : ℂ)).re < 0 := by
    simp only [neg_re, one_div, inv_re, normSq_apply]
    have : (4 * (t : ℂ)).re = 4 * t := by simp
    norm_num
    positivity
  rw [integral_cexp_quadratic hb]
  have hq : (π : ℂ) / -(-(1 / (4 * t)) : ℂ) = ((a : ℝ) : ℂ) := by
    rw [ha]; push_cast; field_simp
  rw [hq, Complex.cpow_def_of_ne_zero (by exact_mod_cast hpos.ne'), ← Complex.ofReal_log hpos.le,
    ← Complex.exp_add, ofReal_exp]
  congr 1
  have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  push_cast
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

theorem integrable_gauss1 {t : ℝ} (ht : 0 < t) : Integrable (gauss1 t) := by
  unfold gauss1
  refine Integrable.const_mul ?_ _
  have := integrable_exp_neg_mul_sq (b := 1 / (4 * t)) (by positivity)
  refine this.congr (Eventually.of_forall fun s => ?_)
  simp only
  congr 1; ring

theorem gauss1_pos {t : ℝ} (ht : 0 < t) (s : ℝ) : 0 < gauss1 t s := by
  unfold gauss1; positivity

theorem heatKernel_pos {t : ℝ} (ht : 0 < t) (y : ι → ℝ) : 0 < heatKernel t y := by
  rw [heatKernel_eq_prod ht]; exact Finset.prod_pos fun i _ => gauss1_pos ht _

theorem integrable_heatKernel {t : ℝ} (ht : 0 < t) : Integrable (heatKernel (ι := ι) t) := by
  have : heatKernel (ι := ι) t = fun y => ∏ i, gauss1 t (y i) :=
    funext (heatKernel_eq_prod ht)
  rw [this]
  exact Integrable.fintype_prod (f := fun _ => gauss1 t) fun _ => integrable_gauss1 ht

/-- Fourier transform of the Gaussian at integer frequencies. -/
theorem gauss_fourier {t : ℝ} (ht : 0 < t) (k : ι → ℤ) :
    ∫ y : ι → ℝ, (heatKernel t y : ℂ) * mFourier (-k) (liftT y) = (heatMult t k : ℂ) := by
  have h : ∀ y : ι → ℝ, (heatKernel t y : ℂ) * mFourier (-k) (liftT y) =
      ∏ i, ((gauss1 t (y i) : ℂ) * cexp (-(2 * π * I * k i * y i))) := by
    intro y
    rw [heatKernel_eq_prod ht, heat_mFourier_liftT, ofReal_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    congr 1
    simp only [Pi.neg_apply, Int.cast_neg]
    ring_nf
  simp_rw [h]
  rw [volume_pi]
  rw [integral_fintype_prod_eq_prod (μ := fun _ => (volume : Measure ℝ))
    (fun i s => (gauss1 t s : ℂ) * cexp (-(2 * π * I * k i * s))), heatMult, ofReal_prod]
  exact Finset.prod_congr rfl fun i _ => gauss1_fourier ht (k i)

theorem integral_heatKernel {t : ℝ} (ht : 0 < t) : ∫ y : ι → ℝ, heatKernel t y = 1 := by
  have h := gauss_fourier (ι := ι) ht 0
  simp only [neg_zero, mFourier_zero, ContinuousMap.one_apply, mul_one, heatMult, Pi.zero_apply,
    Int.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_mul,
    Real.exp_zero, Finset.prod_const_one, ofReal_one] at h
  rw [integral_complex_ofReal] at h
  exact_mod_cast h

/-! ### Uniqueness of Fourier–Stieltjes coefficients -/

theorem measure_eq_of_mFourier {μ ν : Measure (UnitAddTorus ι)} [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (h : ∀ k : ι → ℤ, ∫ z, mFourier k z ∂μ = ∫ z, mFourier k z ∂ν) :
    μ = ν := by
  -- The set of continuous functions on which the two integrals agree is a closed subspace.
  let S : Submodule ℂ C(UnitAddTorus ι, ℂ) :=
    { carrier := {g | ∫ z, g z ∂μ = ∫ z, g z ∂ν}
      add_mem' := fun {a b} ha hb => by
        simp only [mem_ofPred_eq, ContinuousMap.add_apply] at *
        rw [integral_add (a.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
          (b.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)),
          integral_add (a.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
          (b.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)), ha, hb]
      zero_mem' := by simp
      smul_mem' := fun c a ha => by
        simp only [mem_ofPred_eq, ContinuousMap.smul_apply, integral_smul] at *
        rw [ha] }
  have hcont (m : Measure (UnitAddTorus ι)) [IsFiniteMeasure m] :
      Continuous fun g : C(UnitAddTorus ι, ℂ) => ∫ z, g z ∂m := by
    refine LipschitzWith.continuous (K := ⟨m.real univ, measureReal_nonneg⟩) ?_
    refine LipschitzWith.of_dist_le_mul fun g g' => ?_
    rw [dist_eq_norm, ← integral_sub
      (g.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      (g'.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
    refine (norm_integral_le_of_norm_le_const (C := dist g g') (Eventually.of_forall fun z => ?_)).trans
      (le_of_eq (by simp [mul_comm]; left; rfl))
    rw [← dist_eq_norm]
    exact ContinuousMap.dist_apply_le_dist z
  have hclosed : IsClosed (S : Set C(UnitAddTorus ι, ℂ)) :=
    isClosed_eq (hcont μ) (hcont ν)
  have hspan : Submodule.span ℂ (range mFourier) ≤ S := by
    rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    exact h k
  have htop : (⊤ : Submodule ℂ C(UnitAddTorus ι, ℂ)) ≤ S := by
    rw [← span_mFourier_closure_eq_top]
    exact (Submodule.topologicalClosure_minimal _ hspan hclosed)
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => ?_
  have hf : ∫ z, ((f z : ℝ) : ℂ) ∂μ = ∫ z, ((f z : ℝ) : ℂ) ∂ν :=
    htop (Submodule.mem_top (x := ⟨fun z => ((f z : ℝ) : ℂ), by fun_prop⟩))
  rw [integral_complex_ofReal, integral_complex_ofReal] at hf
  exact_mod_cast hf

end SharpLSI
