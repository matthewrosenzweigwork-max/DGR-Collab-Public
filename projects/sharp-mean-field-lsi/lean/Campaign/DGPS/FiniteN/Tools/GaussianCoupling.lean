import DGPS.FiniteN.Tools.Hubbard
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Exact posterior Gaussian coupling (FIN011)

Design notes (R5):
* `xi` is `stdGaussianPi k`, the product of `k` copies of `N(0,1)`; the coupling map is
  `w = h + D m_N + (sqrt N)^-1 D^{1/2} xi` with `D^{1/2}` the positive square root of `D`.
* The conditional law of `w` given `x` is stated in kernel (disintegration) form.
* The gradient of the auxiliary potential is stated via `HasFDerivAt` with `dotCLM`.
* The conditional mean is stated coordinatewise.
* The covariance bound uses the explicit constant `k L^2 sum_ij D_ij^2`, with `L` any sup-norm
  bound for `phi`.
-/

open MeasureTheory ProbabilityTheory
open Matrix hiding smul_apply add_apply sub_apply sum_apply
open scoped ENNReal NNReal MatrixOrder

namespace DGPS.FiniteN.Tools.GaussianCoupling

open DGPS.FiniteN.Tools.Hubbard

variable {k : ℕ}

/-- The standard Gaussian law on `ℝ^k`: the product of `k` copies of `N(0,1)`. -/
noncomputable def stdGaussianPi (k : ℕ) : Measure (Fin k → ℝ) :=
  Measure.pi fun _ : Fin k => gaussianReal 0 1

theorem lintegral_pi_prod_ofReal_sf {ι : Type*} [Fintype ι] {M : Type*} [MeasurableSpace M]
    {μ : Measure M} [SigmaFinite μ]
    (f : ι → M → ℝ) (hf : ∀ i, Integrable (f i) μ) (hf0 : ∀ i x, 0 ≤ f i x) :
    ∫⁻ x : ι → M, ∏ i, ENNReal.ofReal (f i (x i)) ∂(Measure.pi fun _ : ι => μ) =
      ∏ i, ∫⁻ y, ENNReal.ofReal (f i y) ∂μ := by
  have hint : Integrable (fun x : ι → M => ∏ i, f i (x i)) (Measure.pi fun _ : ι => μ) :=
    Integrable.fintype_prod (μ := fun _ : ι => μ) hf
  calc ∫⁻ x : ι → M, ∏ i, ENNReal.ofReal (f i (x i)) ∂(Measure.pi fun _ : ι => μ)
      = ∫⁻ x : ι → M, ENNReal.ofReal (∏ i, f i (x i)) ∂(Measure.pi fun _ : ι => μ) := by
        refine lintegral_congr fun x => ?_
        rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => hf0 i (x i))]
    _ = ENNReal.ofReal (∫ x : ι → M, ∏ i, f i (x i) ∂(Measure.pi fun _ : ι => μ)) :=
        (ofReal_integral_eq_lintegral_ofReal hint
          (Filter.Eventually.of_forall fun x => Finset.prod_nonneg fun i _ => hf0 i (x i))).symm
    _ = ∏ i, ∫⁻ y, ENNReal.ofReal (f i y) ∂μ := by
        rw [integral_fintype_prod_eq_prod (μ := fun _ : ι => μ) (f := fun i y => f i y),
          ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg (hf0 i))]
        refine Finset.prod_congr rfl fun i _ => ?_
        exact ofReal_integral_eq_lintegral_ofReal (hf i) (Filter.Eventually.of_forall (hf0 i))

theorem pi_withDensity_ofReal_sf {M : Type*} [MeasurableSpace M] {m : Measure M} [SigmaFinite m]
    (g : M → ℝ) (hg : Integrable g m) (hg0 : ∀ x, 0 ≤ g x) (n : ℕ) :
    Measure.pi (fun _ : Fin n => m.withDensity fun x => ENNReal.ofReal (g x)) =
      (Measure.pi fun _ : Fin n => m).withDensity
        fun x => ENNReal.ofReal (∏ i, g (x i)) := by
  have hfin : IsFiniteMeasure (m.withDensity fun x => ENNReal.ofReal (g x)) :=
    isFiniteMeasure_withDensity_ofReal hg.hasFiniteIntegral
  refine Measure.pi_eq (μ := fun _ : Fin n => m.withDensity fun x => ENNReal.ofReal (g x)) ?_
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), ← lintegral_indicator (MeasurableSet.univ_pi hs)]
  have hpt : ∀ x : Fin n → M,
      (Set.pi Set.univ s).indicator (fun x => ENNReal.ofReal (∏ i, g (x i))) x =
        ∏ i, ENNReal.ofReal ((s i).indicator g (x i)) := by
    intro x
    by_cases hx : x ∈ Set.pi Set.univ s
    · rw [Set.indicator_of_mem hx, ENNReal.ofReal_prod_of_nonneg (fun i _ => hg0 _)]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [Set.indicator_of_mem (hx i (Set.mem_univ i))]
    · rw [Set.indicator_of_notMem hx]
      simp only [Set.mem_pi, Set.mem_univ, true_implies, not_forall] at hx
      obtain ⟨i, hi⟩ := hx
      symm
      refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
      rw [Set.indicator_of_notMem hi]; simp
  simp_rw [hpt]
  rw [lintegral_pi_prod_ofReal_sf (μ := m) (fun i => (s i).indicator g)
    (fun i => hg.indicator (hs i)) (fun i x => Set.indicator_nonneg (fun y _ => hg0 y) x)]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [withDensity_apply _ (hs i), ← lintegral_indicator (hs i)]
  refine lintegral_congr fun y => ?_
  by_cases hy : y ∈ s i
  · simp [Set.indicator_of_mem hy]
  · simp [Set.indicator_of_notMem hy]


/-- The normalizing constant `(2π)^{-1/2}` of one standard Gaussian coordinate. -/
noncomputable def stdConst : ℝ := (Real.sqrt (2 * Real.pi))⁻¹

theorem stdGaussianPi_eq (k : ℕ) :
    stdGaussianPi k = (volume : Measure (Fin k → ℝ)).withDensity
      fun ξ => ENNReal.ofReal (stdConst ^ k * Real.exp (-(ξ ⬝ᵥ ξ) / 2)) := by
  unfold stdGaussianPi
  have h1 : gaussianReal 0 1 = (volume : Measure ℝ).withDensity
      fun x => ENNReal.ofReal (gaussianPDFReal 0 1 x) :=
    gaussianReal_of_var_ne_zero 0 one_ne_zero
  rw [h1, pi_withDensity_ofReal_sf (gaussianPDFReal 0 1) (integrable_gaussianPDFReal 0 1)
    (gaussianPDFReal_nonneg 0 1) k]
  show (volume : Measure (Fin k → ℝ)).withDensity _ = _
  congr 1
  funext ξ
  congr 1
  have : ∀ i, gaussianPDFReal 0 1 (ξ i) = stdConst * Real.exp (-(ξ i) ^ 2 / 2) := by
    intro i
    rw [gaussianPDFReal_def]
    simp [stdConst]
  simp_rw [this]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← Real.exp_sum]
  congr 2
  simp only [dotProduct, neg_div, Finset.sum_neg_distrib, pow_two]
  rw [← Finset.sum_div]


/-! ### The symmetric square root and the affine Gaussian map -/

/-- The positive semidefinite square root `D^{1/2}`. -/
noncomputable def sqrtD (D : Matrix (Fin k) (Fin k) ℝ) : Matrix (Fin k) (Fin k) ℝ := CFC.sqrt D

section Sqrt

variable {D : Matrix (Fin k) (Fin k) ℝ}

theorem sqrtD_mul_self (hD : D.PosDef) : sqrtD D * sqrtD D = D :=
  CFC.sqrt_mul_sqrt_self D hD.posSemidef.nonneg

theorem sqrtD_transpose : (sqrtD D)ᵀ = sqrtD D := by
  have hRsa : (sqrtD D).PosSemidef := (CFC.sqrt_nonneg D).posSemidef
  have := hRsa.isHermitian.eq
  simpa [conjTranspose_eq_transpose_of_trivial] using this

theorem sqrtD_det_pos (hD : D.PosDef) : 0 < (sqrtD D).det := by
  have := hD.posSemidef.det_sqrt
  have h2 : (sqrtD D).det = Real.sqrt D.det := by simpa [sqrtD] using this
  rw [h2]; exact Real.sqrt_pos.2 hD.det_pos

/-- The affine map `ξ ↦ c + D^{1/2} ξ / √N`. -/
noncomputable def affineMap (D : Matrix (Fin k) (Fin k) ℝ) (N : ℕ+) (c ξ : Fin k → ℝ) :
    Fin k → ℝ :=
  c + (Real.sqrt (N : ℝ))⁻¹ • (sqrtD D *ᵥ ξ)

theorem continuous_affineMap (D : Matrix (Fin k) (Fin k) ℝ) (N : ℕ+) (c : Fin k → ℝ) :
    Continuous (affineMap D N c) := by
  unfold affineMap mulVec dotProduct; fun_prop

theorem measurable_affineMap (D : Matrix (Fin k) (Fin k) ℝ) (N : ℕ+) (c : Fin k → ℝ) :
    Measurable (affineMap D N c) := (continuous_affineMap D N c).measurable

theorem inv_quad (hD : D.PosDef) (N : ℕ+) (v : Fin k → ℝ) :
    ((Real.sqrt (N : ℝ) • (sqrtD D)⁻¹) *ᵥ v) ⬝ᵥ ((Real.sqrt (N : ℝ) • (sqrtD D)⁻¹) *ᵥ v) =
      (N : ℝ) * quadForm D⁻¹ v := by
  have hN : (0 : ℝ) ≤ N := by positivity
  have hRR := sqrtD_mul_self hD
  have hRT := sqrtD_transpose (D := D)
  have hdet : IsUnit (sqrtD D).det := (sqrtD_det_pos hD).ne'.isUnit
  have hDi : D⁻¹ = (sqrtD D)⁻¹ * (sqrtD D)⁻¹ := by
    conv_lhs => rw [← hRR]
    rw [Matrix.mul_inv_rev]
  have hTi : ((sqrtD D)⁻¹)ᵀ = (sqrtD D)⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, hRT]
  unfold quadForm
  rw [hDi, ← mulVec_mulVec, smul_mulVec, dotProduct_smul, smul_dotProduct, smul_eq_mul,
    smul_eq_mul, ← mul_assoc, Real.mul_self_sqrt hN]
  congr 1
  rw [dotProduct_mulVec, ← mulVec_transpose, hTi]
  exact dotProduct_comm _ _


instance (k : ℕ) : IsProbabilityMeasure (stdGaussianPi k) := by
  unfold stdGaussianPi; infer_instance

/-- The Gaussian law `N(c, D/N)` on `ℝ^k`, as a density against Lebesgue measure. -/
noncomputable def gaussLaw (D : Matrix (Fin k) (Fin k) ℝ) (N : ℕ+) (c : Fin k → ℝ) :
    Measure (Fin k → ℝ) :=
  (volume : Measure (Fin k → ℝ)).withDensity
    fun w => ENNReal.ofReal (gaussNorm D N * gaussWeight D c N w)

theorem map_stdGaussian_affine_aux (hD : D.PosDef) (N : ℕ+) (c : Fin k → ℝ) :
    ∃ κ : ℝ, 0 ≤ κ ∧ (stdGaussianPi k).map (affineMap D N c) =
      (volume : Measure (Fin k → ℝ)).withDensity
        fun w => ENNReal.ofReal (κ * gaussWeight D c N w) := by
  classical
  have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
  have hsN : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 hN
  set R := sqrtD D with hR
  have hdet : IsUnit R.det := (sqrtD_det_pos hD).ne'.isUnit
  set A : Matrix (Fin k) (Fin k) ℝ := (Real.sqrt (N : ℝ))⁻¹ • R with hA
  set Ai : Matrix (Fin k) (Fin k) ℝ := Real.sqrt (N : ℝ) • R⁻¹ with hAi
  have hAiA : ∀ ξ : Fin k → ℝ, Ai *ᵥ (A *ᵥ ξ) = ξ := by
    intro ξ
    rw [mulVec_mulVec, hAi, hA, smul_mul_smul_comm, Matrix.nonsing_inv_mul _ hdet,
      mul_inv_cancel₀ hsN.ne', one_smul, one_mulVec]
  have hLdet : LinearMap.det (Matrix.toLin' A) ≠ 0 := by
    rw [LinearMap.det_toLin']
    intro h0
    have h1 : A * Ai = 1 := by
      rw [hAi, hA, smul_mul_smul_comm, Matrix.mul_nonsing_inv _ hdet,
        inv_mul_cancel₀ hsN.ne', one_smul]
    have := congrArg Matrix.det h1
    rw [det_mul, h0, zero_mul, det_one] at this
    exact zero_ne_one this
  set ρ : (Fin k → ℝ) → ℝ≥0∞ := fun ξ =>
    ENNReal.ofReal (stdConst ^ k * Real.exp (-(ξ ⬝ᵥ ξ) / 2)) with hρ
  have hρm : Measurable ρ := by
    refine ENNReal.measurable_ofReal.comp (measurable_const.mul (Real.measurable_exp.comp ?_))
    unfold dotProduct; fun_prop
  set a : ℝ := |(LinearMap.det (Matrix.toLin' A))⁻¹| with ha
  have ha0 : 0 ≤ a := abs_nonneg _
  have hsc : 0 ≤ stdConst ^ k := pow_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _)) k
  refine ⟨a * stdConst ^ k, mul_nonneg ha0 hsc, ?_⟩
  have hTm := measurable_affineMap D N c
  have hAim : Measurable fun y : Fin k → ℝ => Ai *ᵥ y := by
    unfold mulVec dotProduct; fun_prop
  refine Measure.ext fun t ht => ?_
  rw [Measure.map_apply hTm ht, stdGaussianPi_eq, withDensity_apply _ (hTm ht),
    withDensity_apply _ ht, ← lintegral_indicator (hTm ht), ← lintegral_indicator ht]
  set F : (Fin k → ℝ) → ℝ≥0∞ := ((fun y => c + y) ⁻¹' t).indicator (fun y => ρ (Ai *ᵥ y))
    with hF
  have hshift : Measurable fun y : Fin k → ℝ => c + y := measurable_const.add measurable_id
  have hFm : Measurable F := (hρm.comp hAim).indicator (hshift ht)
  have hLm : Measurable (Matrix.toLin' A) := (LinearMap.continuous_of_finiteDimensional _).measurable
  have h1 : ∀ ξ, (affineMap D N c ⁻¹' t).indicator ρ ξ = F (Matrix.toLin' A ξ) := by
    intro ξ
    have hT : affineMap D N c ξ = c + Matrix.toLin' A ξ := by
      simp [affineMap, hA, hR]
    by_cases hξ : ξ ∈ affineMap D N c ⁻¹' t
    · have hξ' : Matrix.toLin' A ξ ∈ (fun y => c + y) ⁻¹' t := by
        show c + Matrix.toLin' A ξ ∈ t
        rw [← hT]; exact hξ
      rw [Set.indicator_of_mem hξ, hF, Set.indicator_of_mem hξ']
      simp only [Matrix.toLin'_apply, hAiA]
    · have hξ' : Matrix.toLin' A ξ ∉ (fun y => c + y) ⁻¹' t := by
        intro hm
        apply hξ
        show affineMap D N c ξ ∈ t
        rw [hT]; exact hm
      rw [Set.indicator_of_notMem hξ, hF, Set.indicator_of_notMem hξ']
  have hh : ∀ ξ, (affineMap D N c ⁻¹' t).indicator
      (fun ξ => ENNReal.ofReal (stdConst ^ k * Real.exp (-(ξ ⬝ᵥ ξ) / 2))) ξ = F (Matrix.toLin' A ξ) :=
    h1
  simp_rw [hh]
  rw [← lintegral_map hFm hLm, Real.map_linearMap_volume_pi_eq_smul_volume_pi hLdet,
    lintegral_smul_measure]
  have h2 : ∀ y, F y = (fun w => t.indicator (fun w => ρ (Ai *ᵥ (w - c))) w) (c + y) := by
    intro y
    simp only [hF]
    by_cases hy : c + y ∈ t
    · rw [Set.indicator_of_mem (show y ∈ (fun y => c + y) ⁻¹' t from hy),
        Set.indicator_of_mem hy, add_sub_cancel_left]
    · rw [Set.indicator_of_notMem (show y ∉ (fun y => c + y) ⁻¹' t from hy),
        Set.indicator_of_notMem hy]
  simp_rw [h2]
  rw [lintegral_add_left_eq_self (fun w => t.indicator (fun w => ρ (Ai *ᵥ (w - c))) w) c,
    smul_eq_mul, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun w => ?_
  by_cases hw : w ∈ t
  · rw [Set.indicator_of_mem hw, Set.indicator_of_mem hw, hρ]
    simp only
    rw [← ENNReal.ofReal_mul ha0]
    congr 1
    have hq := inv_quad hD N (w - c)
    have : Ai *ᵥ (w - c) ⬝ᵥ Ai *ᵥ (w - c) = (N : ℝ) * quadForm D⁻¹ (w - c) := hq
    rw [this]
    unfold gaussWeight
    have : -((N : ℝ) * quadForm D⁻¹ (w - c)) / 2 = -((N : ℝ) / 2) * quadForm D⁻¹ (w - c) := by ring
    rw [this]; ring
  · rw [Set.indicator_of_notMem hw, Set.indicator_of_notMem hw]; simp

theorem map_stdGaussian_affine (hD : D.PosDef) (N : ℕ+) (c : Fin k → ℝ) :
    (stdGaussianPi k).map (affineMap D N c) = gaussLaw D N c := by
  obtain ⟨κ, hκ0, hκ⟩ := map_stdGaussian_affine_aux hD N c
  have hprob : IsProbabilityMeasure ((stdGaussianPi k).map (affineMap D N c)) :=
    (Measure.isProbabilityMeasure_map_iff (measurable_affineMap D N c).aemeasurable).2 inferInstance
  have hg := gaussNorm_pos hD N
  have h1 : (1 : ℝ≥0∞) = ENNReal.ofReal (κ * (gaussNorm D N)⁻¹) := by
    have := hprob.measure_univ
    rw [hκ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at this
    rw [← this, ← ofReal_integral_eq_lintegral_ofReal]
    · rw [integral_const_mul, integral_gaussWeight hD]
    · exact (integrable_gaussWeight hD N c).const_mul κ
    · exact Filter.Eventually.of_forall fun w =>
        mul_nonneg hκ0 (Real.exp_pos _).le
  have h2 : κ * (gaussNorm D N)⁻¹ = 1 := by
    have := h1.symm
    rw [ENNReal.ofReal_eq_one] at this
    exact this
  have h3 : κ = gaussNorm D N := by
    field_simp at h2; exact h2
  rw [hκ, h3]
  rfl

end Sqrt


/-! ### The conditional law of the field given the particles -/

section Posterior

variable {M : Type*} [MeasurableSpace M]

/-- The posterior center `h + D m_N`, `m_N = S(x)/N` the empirical mean of the field. -/
noncomputable def posteriorCenter (D : Matrix (Fin k) (Fin k) ℝ) (h : Fin k → ℝ) (φ : M → Fin k → ℝ)
    (N : ℕ+) (x : Fin N → M) : Fin k → ℝ :=
  h + (N : ℝ)⁻¹ • (D *ᵥ fieldSum φ x)

variable {m : Measure M} {U : M → ℝ} {φ : M → Fin k → ℝ} (hyp : HubbardHyp m U φ)
include hyp

theorem measurable_posteriorCenter (D : Matrix (Fin k) (Fin k) ℝ) (h : Fin k → ℝ) (N : ℕ+) :
    Measurable (posteriorCenter D h φ N : (Fin N → M) → Fin k → ℝ) := by
  have hc : Continuous fun s : Fin k → ℝ => h + (N : ℝ)⁻¹ • (D *ᵥ s) := by
    unfold mulVec dotProduct; fun_prop
  exact hc.measurable.comp (measurable_fieldSum hyp)

theorem measurable_gaussKernel (D : Matrix (Fin k) (Fin k) ℝ) (h : Fin k → ℝ) (N : ℕ+)
    {s : Set ((Fin k → ℝ) × (Fin N → M))} (hs : MeasurableSet s) :
    Measurable fun x : Fin N → M =>
      gaussLaw D N (posteriorCenter D h φ N x) {w | (w, x) ∈ s} := by
  have hq : Continuous (quadForm D⁻¹ : (Fin k → ℝ) → ℝ) := by
    unfold quadForm dotProduct mulVec; fun_prop
  have hdens : Measurable fun p : (Fin N → M) × (Fin k → ℝ) =>
      ENNReal.ofReal (gaussNorm D N * gaussWeight D (posteriorCenter D h φ N p.1) N p.2) := by
    refine ENNReal.measurable_ofReal.comp (measurable_const.mul ?_)
    unfold gaussWeight
    exact Real.measurable_exp.comp (measurable_const.mul (hq.measurable.comp
      (measurable_snd.sub ((measurable_posteriorCenter hyp D h N).comp measurable_fst))))
  have hsw : MeasurableSet {p : (Fin N → M) × (Fin k → ℝ) | (p.2, p.1) ∈ s} :=
    hs.preimage measurable_swap
  have hm := Measurable.lintegral_prod_right' (ν := (volume : Measure (Fin k → ℝ)))
    (hdens.indicator hsw)
  have key : ∀ x : Fin N → M,
      gaussLaw D N (posteriorCenter D h φ N x) {w | (w, x) ∈ s} =
        ∫⁻ w, ({p : (Fin N → M) × (Fin k → ℝ) | (p.2, p.1) ∈ s}.indicator (fun p =>
          ENNReal.ofReal (gaussNorm D N * gaussWeight D (posteriorCenter D h φ N p.1) N p.2))) (x, w) := by
    intro x
    have hsl : MeasurableSet {w : Fin k → ℝ | (w, x) ∈ s} := measurable_prodMk_right hs
    unfold gaussLaw
    rw [withDensity_apply _ hsl, ← lintegral_indicator hsl]
    refine lintegral_congr fun w => ?_
    by_cases hw : (w, x) ∈ s
    · rw [Set.indicator_of_mem (show w ∈ {w : Fin k → ℝ | (w, x) ∈ s} from hw),
        Set.indicator_of_mem (show (x, w) ∈ {p : (Fin N → M) × (Fin k → ℝ) | (p.2, p.1) ∈ s} from hw)]
    · rw [Set.indicator_of_notMem (show w ∉ {w : Fin k → ℝ | (w, x) ∈ s} from hw),
        Set.indicator_of_notMem (show (x, w) ∉ {p : (Fin N → M) × (Fin k → ℝ) | (p.2, p.1) ∈ s} from hw)]
  simp_rw [key]
  exact hm

variable [IsFiniteMeasure m]

theorem hubbardJoint_eq_gauss {D : Matrix (Fin k) (Fin k) ℝ} (hD : D.PosDef) (h : Fin k → ℝ)
    (N : ℕ+) {s : Set ((Fin k → ℝ) × (Fin N → M))} (hs : MeasurableSet s) :
    hubbardJoint D h U φ m N s =
      ∫⁻ x, gaussLaw D N (posteriorCenter D h φ N x) {w | (w, x) ∈ s}
        ∂(hubbardParticleLaw D h U φ m N) := by
  have hG := measurable_gaussKernel hyp D h N hs
  have hpw : Measurable fun x : Fin N → M => ENNReal.ofReal (particleWeight U φ D h N x) :=
    ENNReal.measurable_ofReal.comp (measurable_particleWeight hyp D h N)
  have hinner : ∀ x : Fin N → M,
      ∫⁻ w, s.indicator (hubbardDensity D h U φ N) (w, x) =
        ENNReal.ofReal (particleWeight U φ D h N x) *
          gaussLaw D N (posteriorCenter D h φ N x) {w | (w, x) ∈ s} := by
    intro x
    have hsl : MeasurableSet {w : Fin k → ℝ | (w, x) ∈ s} := measurable_prodMk_right hs
    unfold gaussLaw
    rw [withDensity_apply _ hsl, ← lintegral_indicator hsl,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr fun w => ?_
    by_cases hw : (w, x) ∈ s
    · rw [Set.indicator_of_mem hw,
        Set.indicator_of_mem (show w ∈ {w : Fin k → ℝ | (w, x) ∈ s} from hw)]
      unfold hubbardDensity particleWeight posteriorCenter
      simp only
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
      congr 1
      have e1 := gaussWeight_mul_exp hD N h (fieldSum φ x) w
      have e2 : Real.exp (w ⬝ᵥ fieldSum φ x - ∑ i, U (x i)) =
          Real.exp (w ⬝ᵥ fieldSum φ x) * Real.exp (-(∑ i, U (x i))) := by
        rw [← Real.exp_add]; congr 1
      have e3 : Real.exp (-(∑ i, U (x i)) + h ⬝ᵥ fieldSum φ x +
          (fieldSum φ x ⬝ᵥ D *ᵥ fieldSum φ x) / (2 * (N : ℝ))) =
          Real.exp (-(∑ i, U (x i))) * Real.exp (h ⬝ᵥ fieldSum φ x +
          (fieldSum φ x ⬝ᵥ D *ᵥ fieldSum φ x) / (2 * (N : ℝ))) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [e2, e3]
      calc gaussNorm D N * (gaussWeight D h N w *
            (Real.exp (w ⬝ᵥ fieldSum φ x) * Real.exp (-(∑ i, U (x i)))))
          = gaussNorm D N * ((gaussWeight D h N w * Real.exp (w ⬝ᵥ fieldSum φ x)) *
              Real.exp (-(∑ i, U (x i)))) := by ring
        _ = _ := by rw [e1]; ring
    · rw [Set.indicator_of_notMem hw,
        Set.indicator_of_notMem (show w ∉ {w : Fin k → ℝ | (w, x) ∈ s} from hw)]
      simp
  unfold hubbardJoint hubbardParticleLaw
  rw [Measure.smul_apply, withDensity_apply _ hs, ← lintegral_indicator hs, smul_eq_mul]
  unfold hubbardRef
  rw [lintegral_prod_symm _ ((measurable_hubbardDensity hyp D h N).indicator hs).aemeasurable]
  simp_rw [hinner]
  rw [lintegral_smul_measure, lintegral_withDensity_eq_lintegral_mul _ hpw hG,
    hubbardMass_eq_particleMass hyp hD h N, smul_eq_mul]
  rfl

end Posterior

section Coupling

variable {M : Type*} [MeasurableSpace M]
variable {m : Measure M} [IsFiniteMeasure m] {U : M → ℝ} {φ : M → Fin k → ℝ} (hyp : HubbardHyp m U φ)
include hyp

/-- The coupling map `(x, ξ) ↦ h + D m_N + D^{1/2} ξ/√N`. -/
noncomputable def couplingMap (D : Matrix (Fin k) (Fin k) ℝ) (h : Fin k → ℝ) (φ : M → Fin k → ℝ)
    (N : ℕ+) (p : (Fin N → M) × (Fin k → ℝ)) : (Fin k → ℝ) × (Fin N → M) :=
  (affineMap D N (posteriorCenter D h φ N p.1) p.2, p.1)

theorem coupling_eq {D : Matrix (Fin k) (Fin k) ℝ} (hD : D.PosDef) (h : Fin k → ℝ) (N : ℕ+) :
    ((hubbardParticleLaw D h U φ m N).prod (stdGaussianPi k)).map (couplingMap D h φ N) =
      hubbardJoint D h U φ m N := by
  have hmeas : Measurable (couplingMap D h φ N : (Fin N → M) × (Fin k → ℝ) → _) := by
    have hc : Continuous fun q : (Fin k → ℝ) × (Fin k → ℝ) =>
        q.1 + (Real.sqrt (N : ℝ))⁻¹ • (sqrtD D *ᵥ q.2) := by
      unfold mulVec dotProduct; fun_prop
    have : Measurable fun p : (Fin N → M) × (Fin k → ℝ) =>
        affineMap D N (posteriorCenter D h φ N p.1) p.2 :=
      hc.measurable.comp (((measurable_posteriorCenter hyp D h N).comp measurable_fst).prodMk
        measurable_snd)
    exact this.prodMk measurable_fst
  ext s hs
  rw [Measure.map_apply hmeas hs, hubbardJoint_eq_gauss hyp hD h N hs,
    Measure.prod_apply (hmeas hs)]
  refine lintegral_congr fun x => ?_
  have hsl : MeasurableSet {w : Fin k → ℝ | (w, x) ∈ s} := measurable_prodMk_right hs
  rw [← map_stdGaussian_affine hD N, Measure.map_apply (measurable_affineMap D N _) hsl]
  rfl

end Coupling

/-- The continuous linear functional `v ↦ g · v` on `ℝ^k`. -/
noncomputable def dotCLM (g : Fin k → ℝ) : (Fin k → ℝ) →L[ℝ] ℝ :=
  ∑ i, g i • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin k => ℝ) i

theorem dotCLM_apply (g v : Fin k → ℝ) : dotCLM g v = ∑ i, g i * v i := by
  simp [dotCLM]

theorem continuous_dotCLM : Continuous (dotCLM : (Fin k → ℝ) → _) := by
  unfold dotCLM; fun_prop

theorem norm_dotCLM_le (g : Fin k → ℝ) (L : ℝ) (hL : 0 ≤ L) (hg : ∀ i, |g i| ≤ L) :
    ‖dotCLM g‖ ≤ k * L := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  rw [dotCLM_apply, Real.norm_eq_abs]
  calc |∑ i, g i * v i| ≤ ∑ i, |g i * v i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin k, L * ‖v‖ := Finset.sum_le_sum fun i _ => by
        rw [abs_mul]
        exact mul_le_mul (hg i) (by simpa using norm_le_pi_norm v i) (abs_nonneg _) hL
    _ = k * L * ‖v‖ := by simp; ring

theorem abs_coord_le {M : Type*} {φ : M → Fin k → ℝ} {L : ℝ} (hL : ∀ x, ‖φ x‖ ≤ L) (x : M)
    (i : Fin k) : |φ x i| ≤ L :=
  le_trans (by simpa using norm_le_pi_norm (φ x) i : |φ x i| ≤ ‖φ x‖) (hL x)

theorem expTerm_le_unif {M : Type*} {U : M → ℝ} {φ : M → Fin k → ℝ} {c L r : ℝ}
    (hc : ∀ x, c ≤ U x) (hL : ∀ x, ‖φ x‖ ≤ L) {w : Fin k → ℝ} (hw : ∀ i, |w i| ≤ r) (x : M) :
    expTerm U φ w x ≤ Real.exp (k * r * L - c) := by
  unfold expTerm
  refine Real.exp_le_exp.2 ?_
  have h1 : w ⬝ᵥ φ x ≤ ∑ _i : Fin k, r * L := by
    unfold dotProduct
    refine Finset.sum_le_sum fun i _ => ?_
    calc w i * φ x i ≤ |w i * φ x i| := le_abs_self _
      _ = |w i| * |φ x i| := abs_mul _ _
      _ ≤ r * L := mul_le_mul (hw i) (abs_coord_le hL x i) (abs_nonneg _)
          ((abs_nonneg _).trans (hw i))
  have : ∑ _i : Fin k, r * L = k * r * L := by simp; ring
  linarith [hc x]

section Grad

variable {M : Type*} [MeasurableSpace M] {m : Measure M} [IsFiniteMeasure m] {U : M → ℝ}
  {φ : M → Fin k → ℝ} (hyp : HubbardHyp m U φ)
include hyp

omit [IsFiniteMeasure m] in
theorem measurable_expTerm_w (w : Fin k → ℝ) : Measurable (expTerm U φ w) :=
  (measurable_expTerm hyp).comp (measurable_const.prodMk measurable_id)

omit [IsFiniteMeasure m] in
theorem measurable_coord (j : Fin k) : Measurable fun x => φ x j :=
  (measurable_pi_apply j).comp hyp.φ_meas

theorem integrable_expTerm_mul (w : Fin k → ℝ) (j : Fin k) :
    Integrable (fun x => expTerm U φ w x * φ x j) m := by
  obtain ⟨B, hB⟩ := expTerm_le hyp w
  obtain ⟨L, hL⟩ := hyp.φ_bound
  refine Integrable.mono' (integrable_const (B * max L 0)) 
    ((measurable_expTerm_w hyp w).mul (measurable_coord hyp j)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (expTerm_pos w x)]
  exact mul_le_mul (hB x) ((abs_coord_le hL x j).trans (le_max_left _ _)) (abs_nonneg _)
    ((expTerm_pos w x).le.trans (hB x))

theorem hasFDerivAt_auxPartition (w₀ : Fin k → ℝ) :
    HasFDerivAt (auxPartition U φ m)
      (dotCLM fun j => ∫ x, expTerm U φ w₀ x * φ x j ∂m) w₀ := by
  obtain ⟨c, hc⟩ := hyp.U_lower
  obtain ⟨L, hL⟩ := hyp.φ_bound
  have hL' : ∀ x, ‖φ x‖ ≤ max L 0 := fun x => (hL x).trans (le_max_left _ _)
  have hL0 : 0 ≤ max L 0 := le_max_right _ _
  set L' := max L 0
  set r : ℝ := ‖w₀‖ + 1
  have hr : ∀ w ∈ Metric.ball w₀ 1, ∀ i, |w i| ≤ r := by
    intro w hw i
    have h1 : ‖w - w₀‖ < 1 := by simpa [dist_eq_norm] using hw
    have h2 : |w i| ≤ ‖w‖ := by simpa using norm_le_pi_norm w i
    have h3 : ‖w‖ ≤ ‖w₀‖ + ‖w - w₀‖ := by
      calc ‖w‖ = ‖w₀ + (w - w₀)‖ := by simp
        _ ≤ _ := norm_add_le _ _
    show |w i| ≤ ‖w₀‖ + 1
    linarith
  have hdot : ∀ x, ‖dotCLM (φ x)‖ ≤ k * L' := fun x =>
    norm_dotCLM_le _ _ hL0 (abs_coord_le hL' x)
  have hF'meas : ∀ w, StronglyMeasurable fun x => expTerm U φ w x • dotCLM (φ x) := fun w =>
    (measurable_expTerm_w hyp w).stronglyMeasurable.smul
      (continuous_dotCLM.comp_stronglyMeasurable hyp.φ_meas.stronglyMeasurable)
  have hF'bd : ∀ w ∈ Metric.ball w₀ 1, ∀ x,
      ‖expTerm U φ w x • dotCLM (φ x)‖ ≤ Real.exp (k * r * L' - c) * (k * L') := by
    intro w hw x
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (expTerm_pos w x)]
    exact mul_le_mul (expTerm_le_unif hc hL' (hr w hw) x) (hdot x) (norm_nonneg _)
      (Real.exp_pos _).le
  have hF'int : Integrable (fun x => expTerm U φ w₀ x • dotCLM (φ x)) m :=
    Integrable.mono' (integrable_const _) (hF'meas w₀).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => hF'bd w₀ (Metric.mem_ball_self one_pos) x)
  have key := hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := m)
    (F := fun w x => expTerm U φ w x)
    (F' := fun w x => expTerm U φ w x • dotCLM (φ x)) (x₀ := w₀) (s := Metric.ball w₀ 1)
    (Metric.ball_mem_nhds w₀ one_pos)
    (Filter.Eventually.of_forall fun w => (measurable_expTerm_w hyp w).aestronglyMeasurable)
    (integrable_expTerm hyp w₀) (hF'meas w₀).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x w hw => hF'bd w hw x)
    (integrable_const _)
    (Filter.Eventually.of_forall fun x w _ => by
      have h1 : HasFDerivAt (fun w : Fin k → ℝ => w ⬝ᵥ φ x - U x) (dotCLM (φ x)) w := by
        have : (fun w : Fin k → ℝ => w ⬝ᵥ φ x - U x) = fun w => dotCLM (φ x) w - U x := by
          funext w; rw [dotCLM_apply]; unfold dotProduct
          congr 1; exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
        rw [this]; exact (dotCLM (φ x)).hasFDerivAt.sub_const _
      exact h1.exp)
  have heq : (∫ a, expTerm U φ w₀ a • dotCLM (φ a) ∂m) =
      dotCLM fun j => ∫ x, expTerm U φ w₀ x * φ x j ∂m := by
    ext v
    rw [ContinuousLinearMap.integral_apply hF'int, dotCLM_apply]
    simp only [smul_apply, smul_eq_mul, dotCLM_apply]
    have : (fun a => expTerm U φ w₀ a * ∑ i, φ a i * v i) =
        fun a => ∑ i, (expTerm U φ w₀ a * φ a i) * v i := by
      funext a; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [this, integral_finsetSum _ (fun i _ => (integrable_expTerm_mul hyp w₀ i).mul_const _)]
    exact Finset.sum_congr rfl fun i _ => integral_mul_const _ _
  rw [heq] at key
  exact key

omit hyp in
theorem hasFDerivAt_quad {A : Matrix (Fin k) (Fin k) ℝ} (hA : Aᵀ = A) (h w : Fin k → ℝ) :
    HasFDerivAt (fun w : Fin k → ℝ => (1 / 2) * quadForm A (w - h))
      (dotCLM (A *ᵥ (w - h))) w := by
  have hproj : ∀ i, HasFDerivAt (fun w : Fin k → ℝ => w i - h i)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin k => ℝ) i) w := fun i =>
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin k => ℝ) i).hasFDerivAt).sub_const (h i)
  have hrow : ∀ i, HasFDerivAt (fun w : Fin k → ℝ => ∑ j, A i j * (w j - h j))
      (∑ j, A i j • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin k => ℝ) j) w := fun i =>
    HasFDerivAt.fun_sum fun j _ => (hproj j).const_mul (A i j)
  have hq : HasFDerivAt (fun w : Fin k → ℝ => ∑ i, (w i - h i) * ∑ j, A i j * (w j - h j))
      (∑ i, ((w i - h i) • ∑ j, A i j • ContinuousLinearMap.proj (R := ℝ)
          (φ := fun _ : Fin k => ℝ) j +
        (∑ j, A i j * (w j - h j)) • ContinuousLinearMap.proj (R := ℝ)
          (φ := fun _ : Fin k => ℝ) i)) w :=
    HasFDerivAt.fun_sum fun i _ => (hproj i).mul (hrow i)
  have h2 := hq.const_mul (1 / 2 : ℝ)
  refine h2.congr_fderiv ?_ |>.congr_fderiv rfl
  ext v
  simp only [dotCLM_apply, mulVec, dotProduct, smul_apply, sum_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul, add_apply,
    Pi.sub_apply]
  have hsym : ∀ i j, A j i = A i j := fun i j => by
    have := congrFun (congrFun hA i) j
    simpa [transpose_apply] using this
  have e : ∑ x, (w x - h x) * ∑ i, A x i * v i = ∑ x, (∑ j, A x j * (w j - h j)) * v x := by
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i _ => by rw [hsym]; ring
  rw [Finset.sum_add_distrib, e]; ring

/-- The mean `q_w(φ)` of the field under the one-site law. -/
noncomputable def siteMean (U : M → ℝ) (φ : M → Fin k → ℝ) (m : Measure M) (w : Fin k → ℝ) :
    Fin k → ℝ := fun j => ∫ x, φ x j ∂(siteLaw U φ m w)

/-- The gradient `∇ψ(w) = D⁻¹(w-h) - q_w(φ)`. -/
noncomputable def auxGrad (D : Matrix (Fin k) (Fin k) ℝ) (h : Fin k → ℝ) (U : M → ℝ)
    (φ : M → Fin k → ℝ) (m : Measure M) (w : Fin k → ℝ) : Fin k → ℝ :=
  D⁻¹ *ᵥ (w - h) - siteMean U φ m w

theorem integral_siteLaw (w : Fin k → ℝ) (f : M → ℝ) :
    ∫ x, f x ∂(siteLaw U φ m w) =
      (auxPartition U φ m w)⁻¹ * ∫ x, expTerm U φ w x * f x ∂m := by
  have hz := auxPartition_pos hyp (m := m) w
  unfold siteLaw
  have hmeas : Measurable fun x => ENNReal.ofReal (siteDensity U φ m w x) :=
    ENNReal.measurable_ofReal.comp ((measurable_expTerm_w hyp w).div_const _)
  rw [integral_withDensity_eq_integral_toReal_smul hmeas
    (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top), ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [siteDensity, smul_eq_mul]
  rw [ENNReal.toReal_ofReal (div_nonneg (expTerm_pos w x).le hz.le)]
  field_simp

theorem hasFDerivAt_auxPotential {D : Matrix (Fin k) (Fin k) ℝ} (hD : D.PosDef)
    (h w : Fin k → ℝ) :
    HasFDerivAt (auxPotential U φ D h m) (dotCLM (auxGrad D h U φ m w)) w := by
  have hz := auxPartition_pos hyp (m := m) w
  have hA : (D⁻¹)ᵀ = D⁻¹ := by
    have := hD.inv.isHermitian
    rwa [Matrix.IsHermitian, conjTranspose_eq_transpose_of_trivial] at this
  have h1 := (hasFDerivAt_quad hA h w).sub ((hasFDerivAt_auxPartition hyp w).log hz.ne')
  refine h1.congr_fderiv ?_
  ext v
  simp only [dotCLM_apply, sub_apply, smul_apply, smul_eq_mul, auxGrad, siteMean,
    Pi.sub_apply, integral_siteLaw hyp]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

end Grad

section Moments

variable {M : Type*} [MeasurableSpace M] {m : Measure M} [IsFiniteMeasure m] {U : M → ℝ}
  {φ : M → Fin k → ℝ} (hyp : HubbardHyp m U φ)
include hyp

theorem integrable_coord_eval (N : ℕ+) (w : Fin k → ℝ) (i : Fin N) (j : Fin k) :
    Integrable (fun x : Fin N → M => φ (x i) j) (Measure.pi fun _ : Fin N => siteLaw U φ m w) := by
  have := isProbabilityMeasure_siteLaw hyp (m := m) w
  obtain ⟨L, hL⟩ := hyp.φ_bound
  refine Integrable.mono' (integrable_const L)
    (((measurable_coord hyp j).comp (measurable_pi_apply i)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x => ?_)
  simpa [Real.norm_eq_abs] using abs_coord_le hL (x i) j

theorem integral_coord_eval (N : ℕ+) (w : Fin k → ℝ) (i : Fin N) (j : Fin k) :
    ∫ x : Fin N → M, φ (x i) j ∂(Measure.pi fun _ : Fin N => siteLaw U φ m w) =
      siteMean U φ m w j := by
  have := isProbabilityMeasure_siteLaw hyp (m := m) w
  exact integral_comp_eval (μ := fun _ : Fin N => siteLaw U φ m w) (i := i)
    (f := fun y => φ y j) (measurable_coord hyp j).aestronglyMeasurable

theorem integrable_fieldSum (N : ℕ+) (w : Fin k → ℝ) (j : Fin k) :
    Integrable (fun x : Fin N → M => fieldSum φ x j)
      (Measure.pi fun _ : Fin N => siteLaw U φ m w) := by
  have := isProbabilityMeasure_siteLaw hyp (m := m) w
  have : (fun x : Fin N → M => fieldSum φ x j) = fun x => ∑ i, φ (x i) j := by
    funext x; simp [fieldSum, Finset.sum_apply]
  rw [this]
  exact integrable_finsetSum _ fun i _ => integrable_coord_eval hyp N w i j

theorem integral_fieldSum (N : ℕ+) (w : Fin k → ℝ) (j : Fin k) :
    ∫ x : Fin N → M, fieldSum φ x j ∂(Measure.pi fun _ : Fin N => siteLaw U φ m w) =
      N * siteMean U φ m w j := by
  have : (fun x : Fin N → M => fieldSum φ x j) = fun x => ∑ i, φ (x i) j := by
    funext x; simp [fieldSum, Finset.sum_apply]
  rw [this, integral_finsetSum _ fun i _ => integrable_coord_eval hyp N w i j]
  simp [integral_coord_eval hyp N w]

omit [MeasurableSpace M] [IsFiniteMeasure m] hyp in
theorem sq_dot_le (a : Fin k → ℝ) {L : ℝ} (hL : ∀ x, ‖φ x‖ ≤ L) (y : M) :
    (a ⬝ᵥ φ y) ^ 2 ≤ (a ⬝ᵥ a) * (k * L ^ 2) := by
  have h1 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a (φ y)
  have h2 : ∑ i, φ y i ^ 2 ≤ ∑ _i : Fin k, L ^ 2 :=
    Finset.sum_le_sum fun i _ => by
      have := abs_coord_le hL y i
      calc φ y i ^ 2 = |φ y i| ^ 2 := (sq_abs _).symm
        _ ≤ L ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2
  have h3 : a ⬝ᵥ a = ∑ i, a i ^ 2 := by simp [dotProduct, sq]
  calc (a ⬝ᵥ φ y) ^ 2 ≤ (∑ i, a i ^ 2) * ∑ i, φ y i ^ 2 := h1
    _ ≤ (∑ i, a i ^ 2) * ∑ _i : Fin k, L ^ 2 :=
        mul_le_mul_of_nonneg_left h2 (Finset.sum_nonneg fun i _ => sq_nonneg _)
    _ = (a ⬝ᵥ a) * (k * L ^ 2) := by rw [h3]; simp

theorem variance_bound (N : ℕ+) (w a : Fin k → ℝ) {L : ℝ} (hL : ∀ x, ‖φ x‖ ≤ L) :
    ∫ x : Fin N → M, (a ⬝ᵥ fieldSum φ x -
        ∫ y, a ⬝ᵥ fieldSum φ y ∂(Measure.pi fun _ : Fin N => siteLaw U φ m w)) ^ 2
      ∂(Measure.pi fun _ : Fin N => siteLaw U φ m w) ≤ N * ((a ⬝ᵥ a) * (k * L ^ 2)) := by
  have hP := isProbabilityMeasure_siteLaw hyp (m := m) w
  set P : Measure (Fin N → M) := Measure.pi fun _ : Fin N => siteLaw U φ m w with hPdef
  have hPprob : IsProbabilityMeasure P := by rw [hPdef]; infer_instance
  set X : Fin N → (Fin N → M) → ℝ := fun i x => a ⬝ᵥ φ (x i) with hX
  have hmeas : ∀ i, Measurable (X i) := fun i => by
    have : Measurable fun y : M => a ⬝ᵥ φ y := by
      unfold dotProduct
      exact Finset.measurable_sum _ fun j _ => measurable_const.mul (measurable_coord hyp j)
    exact this.comp (measurable_pi_apply i)
  have hbd : ∀ i x, (X i x) ^ 2 ≤ (a ⬝ᵥ a) * (k * L ^ 2) := fun i x => sq_dot_le a hL (x i)
  have hmem : ∀ i, MemLp (X i) 2 P := fun i =>
    MemLp.of_bound (hmeas i).aestronglyMeasurable (Real.sqrt ((a ⬝ᵥ a) * (k * L ^ 2)))
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs]
        exact Real.abs_le_sqrt (hbd i x))
  have hS : (fun x : Fin N → M => a ⬝ᵥ fieldSum φ x) = ∑ i, X i := by
    funext x; simp [fieldSum, dotProduct_sum, Finset.sum_apply, hX]
  have hind : Set.Pairwise (↑(Finset.univ : Finset (Fin N))) fun i j => X i ⟂ᵢ[P] X j := by
    intro i _ j _ hij
    have := iIndepFun_pi (μ := fun _ : Fin N => siteLaw U φ m w)
      (X := fun _ y => a ⬝ᵥ φ y) (fun i => by
        have : Measurable fun y : M => a ⬝ᵥ φ y := by
          unfold dotProduct
          exact Finset.measurable_sum _ fun j _ => measurable_const.mul (measurable_coord hyp j)
        exact this.aemeasurable)
    exact this.indepFun hij
  have hvar := IndepFun.variance_sum (μ := P) (s := Finset.univ) (fun i _ => hmem i) hind
  have hsum_meas : AEMeasurable (∑ i, X i) P := by
    have := Finset.measurable_sum (Finset.univ : Finset (Fin N)) fun i _ => hmeas i
    rw [← Finset.sum_fn] at this
    exact this.aemeasurable
  rw [variance_eq_integral hsum_meas] at hvar
  have hle : ∀ i, variance (X i) P ≤ (a ⬝ᵥ a) * (k * L ^ 2) := fun i => by
    refine (variance_le_expectation_sq (hmeas i).aestronglyMeasurable).trans ?_
    have : ∫ x, (X i ^ 2) x ∂P ≤ ∫ _x, (a ⬝ᵥ a) * (k * L ^ 2) ∂P :=
      integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => sq_nonneg _)
        (integrable_const _) (Filter.Eventually.of_forall fun x => hbd i x)
    simpa using this
  have hS' : ∀ x, a ⬝ᵥ fieldSum φ x = (∑ i, X i) x := fun x => congrFun hS x
  simp_rw [hS']
  calc ∫ x, ((∑ i, X i) x - P[∑ i, X i]) ^ 2 ∂P = ∑ i, variance (X i) P := hvar
    _ ≤ ∑ _i : Fin N, (a ⬝ᵥ a) * (k * L ^ 2) := Finset.sum_le_sum fun i _ => hle i
    _ = N * ((a ⬝ᵥ a) * (k * L ^ 2)) := by simp

omit [IsFiniteMeasure m] hyp in
theorem center_eq {D : Matrix (Fin k) (Fin k) ℝ} (hD : D.PosDef) (h w : Fin k → ℝ) :
    w - D *ᵥ auxGrad D h U φ m w = h + D *ᵥ siteMean U φ m w := by
  have hu : IsUnit D.det := isUnit_iff_ne_zero.2 hD.det_pos.ne'
  unfold auxGrad
  rw [mulVec_sub, mulVec_mulVec, mul_nonsing_inv _ hu, one_mulVec]
  ext j
  simp only [Pi.sub_apply, Pi.add_apply]
  ring

theorem integral_posteriorCenter {D : Matrix (Fin k) (Fin k) ℝ} (hD : D.PosDef) (h : Fin k → ℝ)
    (N : ℕ+) (w : Fin k → ℝ) (j : Fin k) :
    ∫ x : Fin N → M, posteriorCenter D h φ N x j ∂(Measure.pi fun _ : Fin N => siteLaw U φ m w) =
      (w - D *ᵥ auxGrad D h U φ m w) j := by
  have hP := isProbabilityMeasure_siteLaw hyp (m := m) w
  have hN : (N : ℝ) ≠ 0 := by positivity
  have e : (fun x : Fin N → M => posteriorCenter D h φ N x j) =
      fun x => h j + (N : ℝ)⁻¹ * ∑ l, D j l * fieldSum φ x l := by
    funext x; simp [posteriorCenter, mulVec, dotProduct]
  have hint : ∀ l, Integrable (fun x : Fin N → M => D j l * fieldSum φ x l)
      (Measure.pi fun _ : Fin N => siteLaw U φ m w) := fun l =>
    (integrable_fieldSum hyp N w l).const_mul _
  rw [e, integral_add (integrable_const _)
      ((integrable_finsetSum _ fun l _ => hint l).const_mul _), integral_const_mul,
    integral_finsetSum _ fun l _ => hint l, center_eq hD h w]
  simp only [integral_const, probReal_univ, one_smul, Pi.add_apply]
  have e3 : ∀ l, ∫ x : Fin N → M, D j l * fieldSum φ x l ∂(Measure.pi fun _ : Fin N => siteLaw U φ m w)
      = D j l * (N * siteMean U φ m w l) := fun l => by
    rw [integral_const_mul, integral_fieldSum hyp]
  simp only [e3]
  simp only [mulVec, dotProduct]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  field_simp

omit [MeasurableSpace M] [IsFiniteMeasure m] hyp in
theorem dot_vecMul_le (D : Matrix (Fin k) (Fin k) ℝ) (u : Fin k → ℝ) :
    (u ᵥ* D) ⬝ᵥ (u ᵥ* D) ≤ (∑ i, ∑ j, D i j ^ 2) * (u ⬝ᵥ u) := by
  have h1 : ∀ j, (u ᵥ* D) j * (u ᵥ* D) j ≤ (∑ i, D i j ^ 2) * (u ⬝ᵥ u) := fun j => by
    have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ u (fun i => D i j)
    have e1 : u ᵥ* D = fun j => ∑ i, u i * D i j := by funext j; simp [vecMul, dotProduct]
    have e2 : u ⬝ᵥ u = ∑ i, u i ^ 2 := by simp [dotProduct, sq]
    rw [e1, e2, ← sq]
    simp only
    calc _ ≤ _ := this
      _ = _ := mul_comm _ _
  calc (u ᵥ* D) ⬝ᵥ (u ᵥ* D) = ∑ j, (u ᵥ* D) j * (u ᵥ* D) j := rfl
    _ ≤ ∑ j, (∑ i, D i j ^ 2) * (u ⬝ᵥ u) := Finset.sum_le_sum fun j _ => h1 j
    _ = (∑ i, ∑ j, D i j ^ 2) * (u ⬝ᵥ u) := by rw [← Finset.sum_mul, Finset.sum_comm]

theorem covariance_bound {D : Matrix (Fin k) (Fin k) ℝ} (hD : D.PosDef) (h : Fin k → ℝ)
    (N : ℕ+) (w u : Fin k → ℝ) {L : ℝ} (hL : ∀ x, ‖φ x‖ ≤ L) :
    ∫ x : Fin N → M, (u ⬝ᵥ (posteriorCenter D h φ N x - (w - D *ᵥ auxGrad D h U φ m w))) ^ 2
        ∂(Measure.pi fun _ : Fin N => siteLaw U φ m w) ≤
      (k * L ^ 2 * ∑ i, ∑ j, D i j ^ 2) * (u ⬝ᵥ u) / N := by
  have hP := isProbabilityMeasure_siteLaw hyp (m := m) w
  have hN : (N : ℝ) ≠ 0 := by positivity
  have hNpos : (0 : ℝ) < N := by positivity
  set a : Fin k → ℝ := u ᵥ* D with ha
  set q : Fin k → ℝ := siteMean U φ m w with hq
  have hmean : ∫ y : Fin N → M, a ⬝ᵥ fieldSum φ y ∂(Measure.pi fun _ : Fin N => siteLaw U φ m w) =
      N * (a ⬝ᵥ q) := by
    unfold dotProduct
    rw [integral_finsetSum _ fun l _ => (integrable_fieldSum hyp N w l).const_mul _]
    simp only [integral_const_mul, integral_fieldSum hyp]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring
  have hpt : ∀ x : Fin N → M, u ⬝ᵥ (posteriorCenter D h φ N x - (w - D *ᵥ auxGrad D h U φ m w)) =
      (N : ℝ)⁻¹ * (a ⬝ᵥ fieldSum φ x - N * (a ⬝ᵥ q)) := by
    intro x
    rw [center_eq hD h w]
    have e : posteriorCenter D h φ N x - (h + D *ᵥ q) =
        D *ᵥ ((N : ℝ)⁻¹ • fieldSum φ x - q) := by
      unfold posteriorCenter
      rw [mulVec_sub, mulVec_smul]; abel
    rw [e, dotProduct_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul, mul_sub]
    field_simp
    rfl
  have hint : ∀ x : Fin N → M, (u ⬝ᵥ (posteriorCenter D h φ N x - (w - D *ᵥ auxGrad D h U φ m w))) ^ 2 =
      ((N : ℝ)⁻¹) ^ 2 * (a ⬝ᵥ fieldSum φ x -
        ∫ y : Fin N → M, a ⬝ᵥ fieldSum φ y ∂(Measure.pi fun _ : Fin N => siteLaw U φ m w)) ^ 2 := by
    intro x; rw [hpt, hmean, mul_pow]
  simp_rw [hint]
  rw [integral_const_mul]
  have hv := variance_bound hyp N w a hL
  have hF := dot_vecMul_le D u
  have hk : 0 ≤ (k : ℝ) * L ^ 2 := by positivity
  calc ((N : ℝ)⁻¹) ^ 2 * _ ≤ ((N : ℝ)⁻¹) ^ 2 * (N * ((a ⬝ᵥ a) * (k * L ^ 2))) :=
        mul_le_mul_of_nonneg_left hv (by positivity)
    _ = ((a ⬝ᵥ a) * (k * L ^ 2)) / N := by field_simp
    _ ≤ ((∑ i, ∑ j, D i j ^ 2) * (u ⬝ᵥ u) * (k * L ^ 2)) / N := by
        gcongr
    _ = (k * L ^ 2 * ∑ i, ∑ j, D i j ^ 2) * (u ⬝ᵥ u) / N := by ring

end Moments

end DGPS.FiniteN.Tools.GaussianCoupling

namespace DGPS.FiniteN

open MeasureTheory Matrix ProbabilityTheory
open DGPS.FiniteN.Tools.Hubbard DGPS.FiniteN.Tools.GaussianCoupling

/-- Exact posterior Gaussian coupling for the Hubbard-Stratonovich representation.

(1) Kernel form: conditionally on the particles `x`, the auxiliary field `w` is Gaussian with
centre `posteriorCenter` and covariance `D/N`.
(2) Coupling: `w = h + D m_N + D^{1/2} ξ / √N` with `ξ ~ stdGaussianPi k` independent of `x ~ P_N`
has the joint law `hubbardJoint`.
(3) The auxiliary potential `ψ` is Fréchet differentiable with gradient `auxGrad`.
(4) The conditional mean of the posterior centre under `q_w^{⊗N}` is `w - D ∇ψ(w)`.
(5) Covariance bound with constant `k L² ∑ D_ij²`, where `L` bounds `‖φ‖`. -/
theorem exact_posterior_gaussian_coupling {M : Type*} [MeasurableSpace M] {k : ℕ}
    {m : Measure M} [IsFiniteMeasure m] {U : M → ℝ} {φ : M → Fin k → ℝ}
    (hyp : HubbardHyp m U φ) {D : Matrix (Fin k) (Fin k) ℝ} (hD : D.PosDef)
    (h : Fin k → ℝ) (N : ℕ+) :
    (∀ s : Set ((Fin k → ℝ) × (Fin N → M)), MeasurableSet s →
      hubbardJoint D h U φ m N s =
        ∫⁻ x, gaussLaw D N (posteriorCenter D h φ N x) {w | (w, x) ∈ s}
          ∂(hubbardParticleLaw D h U φ m N)) ∧
    (((hubbardParticleLaw D h U φ m N).prod (stdGaussianPi k)).map (couplingMap D h φ N) =
      hubbardJoint D h U φ m N) ∧
    (∀ w, HasFDerivAt (auxPotential U φ D h m) (dotCLM (auxGrad D h U φ m w)) w ∧
      auxGrad D h U φ m w = D⁻¹ *ᵥ (w - h) - siteMean U φ m w) ∧
    (∀ (w : Fin k → ℝ) (j : Fin k),
      ∫ x : Fin N → M, posteriorCenter D h φ N x j ∂(Measure.pi fun _ : Fin N => siteLaw U φ m w) =
        (w - D *ᵥ auxGrad D h U φ m w) j) ∧
    (∀ {L : ℝ}, (∀ x, ‖φ x‖ ≤ L) → ∀ (w u : Fin k → ℝ),
      ∫ x : Fin N → M,
          (u ⬝ᵥ (posteriorCenter D h φ N x - (w - D *ᵥ auxGrad D h U φ m w))) ^ 2
          ∂(Measure.pi fun _ : Fin N => siteLaw U φ m w) ≤
        (k * L ^ 2 * ∑ i, ∑ j, D i j ^ 2) * (u ⬝ᵥ u) / N) :=
  ⟨fun _ hs => hubbardJoint_eq_gauss hyp hD h N hs, coupling_eq hyp hD h N,
    fun w => ⟨hasFDerivAt_auxPotential hyp hD h w, rfl⟩,
    fun w j => integral_posteriorCenter hyp hD h N w j,
    fun hL w u => covariance_bound hyp hD h N w u hL⟩

end DGPS.FiniteN
