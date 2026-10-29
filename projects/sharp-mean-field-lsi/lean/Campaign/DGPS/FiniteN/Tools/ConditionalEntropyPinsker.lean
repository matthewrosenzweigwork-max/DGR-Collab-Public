import DGPS.FiniteN.Tools.UniformVonMises
import DGPS.FiniteN.Tools.ConditionalMeanDerivative
import DGPS.FiniteN.Tools.Hubbard
import DGPS.Foundations.Entropy
import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace DGPS.FiniteN.Tools.ConditionalEntropyPinsker

section Abstract

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- Pointwise Young inequality for the entropy integrand. -/
theorem young_pointwise {g a ψ c : ℝ} (hg : 0 ≤ g) (ha : 0 < a) :
    g * (ψ - c) ≤ g * Real.log (g / a) - g + a * Real.exp (ψ - c) := by
  rcases hg.eq_or_lt with h0 | h0
  · subst h0; simp; positivity
  · have hy := Real.add_one_le_exp (ψ - c - Real.log (g / a))
    have hexp : Real.exp (ψ - c - Real.log (g / a)) = a * Real.exp (ψ - c) / g := by
      rw [Real.exp_sub, Real.exp_log (div_pos h0 ha)]
      field_simp
    rw [hexp, le_div_iff₀ h0] at hy
    nlinarith [hy]

theorem mul_log_split {g a : ℝ} (hg : 0 ≤ g) (ha : 0 < a) :
    g * Real.log (g / a) = g * Real.log g - g * Real.log a := by
  rcases hg.eq_or_lt with h0 | h0
  · subst h0; simp
  · rw [Real.log_div h0.ne' ha.ne']; ring

/-- Gibbs variational inequality `∫ g ψ ≤ Ent(g) + (∫ g) log ∫ e^ψ`. -/
theorem gibbs_variational {g ψ : Ω → ℝ} (hg : Measurable g) (hψ : Measurable ψ) {B Bψ : ℝ}
    (hgB : ∀ x, |g x| ≤ B) (hψB : ∀ x, |ψ x| ≤ Bψ) (hg0 : ∀ x, 0 ≤ g x)
    (hglog : Integrable (fun x => g x * Real.log (g x)) P)
    (ha : 0 < ∫ x, g x ∂P) :
    ∫ x, g x * ψ x ∂P ≤ (∫ x, g x * Real.log (g x) ∂P - (∫ x, g x ∂P) * Real.log (∫ x, g x ∂P))
      + (∫ x, g x ∂P) * Real.log (∫ x, Real.exp (ψ x) ∂P) := by
  set a := ∫ x, g x ∂P with hadef
  set Z := ∫ x, Real.exp (ψ x) ∂P with hZ
  have hint : ∀ {h : Ω → ℝ}, Measurable h → ∀ {C : ℝ}, (∀ x, |h x| ≤ C) → Integrable h P :=
    fun {h} hm {C} hC => Integrable.of_bound hm.aestronglyMeasurable C
      (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hC x)
  have hgi : Integrable g P := hint hg hgB
  have hexpm : Measurable fun x => Real.exp (ψ x) := Real.measurable_exp.comp hψ
  have hexpi : Integrable (fun x => Real.exp (ψ x)) P := by
    refine hint hexpm (C := Real.exp Bψ) fun x => ?_
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.2 ((le_abs_self _).trans (hψB x))
  have hZpos : 0 < Z := by
    rw [hZ]
    exact (integral_pos_iff_support_of_nonneg (fun x => (Real.exp_pos _).le) hexpi).2
      (by simp [Function.support, Real.exp_ne_zero])
  set c := Real.log Z with hc
  have hgψi : Integrable (fun x => g x * ψ x) P := by
    refine hint (hg.mul hψ) (C := B * Bψ) fun x => ?_
    rw [abs_mul]
    exact mul_le_mul (hgB x) (hψB x) (abs_nonneg _) ((abs_nonneg _).trans (hgB x))
  have hgc : Integrable (fun x => g x * (ψ x - c)) P := by
    have := hgψi.sub (hgi.mul_const c)
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [Pi.sub_apply]; ring
  have hR : Integrable (fun x => g x * Real.log (g x) - g x * Real.log a - g x
      + a * Real.exp (ψ x - c)) P := by
    have h1 : Integrable (fun x => g x * Real.log (g x) - g x * Real.log a - g x) P :=
      (hglog.sub (hgi.mul_const (Real.log a))).sub hgi
    have h2 := (hexpi.const_mul (a * Real.exp (-c)))
    refine (h1.add h2).congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply]
    rw [Real.exp_sub, Real.exp_neg]; ring
  have hmono := integral_mono hgc hR fun x => by
    have := young_pointwise (ψ := ψ x) (c := c) (hg0 x) ha
    rw [mul_log_split (hg0 x) ha] at this
    exact this
  have hL : ∫ x, g x * (ψ x - c) ∂P = ∫ x, g x * ψ x ∂P - a * c := by
    have : ∀ x, g x * (ψ x - c) = g x * ψ x - g x * c := fun x => by ring
    simp_rw [this]
    rw [integral_sub hgψi (hgi.mul_const c), integral_mul_const]
  have hRv : ∫ x, (g x * Real.log (g x) - g x * Real.log a - g x
      + a * Real.exp (ψ x - c)) ∂P = ∫ x, g x * Real.log (g x) ∂P - a * Real.log a := by
    have h1 : Integrable (fun x => g x * Real.log (g x) - g x * Real.log a) P :=
      hglog.sub (hgi.mul_const (Real.log a))
    have h2 : Integrable (fun x => a * Real.exp (ψ x - c)) P := by
      refine (hexpi.const_mul (a * Real.exp (-c))).congr (Filter.Eventually.of_forall fun x => ?_)
      simp only
      rw [Real.exp_sub, Real.exp_neg]; ring
    rw [integral_add (f := fun x => g x * Real.log (g x) - g x * Real.log a - g x)
      (g := fun x => a * Real.exp (ψ x - c)) (h1.sub hgi) h2,
      integral_sub (f := fun x => g x * Real.log (g x) - g x * Real.log a) (g := g) h1 hgi,
      integral_sub (f := fun x => g x * Real.log (g x)) (g := fun x => g x * Real.log a) hglog
        (hgi.mul_const _),
      integral_mul_const, integral_const_mul]
    have : ∫ x, Real.exp (ψ x - c) ∂P = 1 := by
      simp_rw [Real.exp_sub]
      rw [integral_div, ← hZ, hc, Real.exp_log hZpos, div_self hZpos.ne']
    rw [this]; ring
  rw [hL, hRv] at hmono
  linarith

/-- Quadratic optimisation: from `t K ≤ E + (s / 2) t²` for all `t` and `s ≥ 0`, `K² ≤ 2 s E`. -/
theorem sq_le_of_linear_le {K E s : ℝ} (hs : 0 ≤ s) (h : ∀ t : ℝ, t * K ≤ E + s / 2 * t ^ 2) :
    K ^ 2 ≤ 2 * s * E := by
  have hE : 0 ≤ E := by simpa using h 0
  rcases hs.eq_or_lt with h0 | h0
  · subst h0
    by_contra hK
    have hK0 : K ≠ 0 := by rintro rfl; apply hK; simp
    have := h ((E + 1) / K)
    rw [div_mul_cancel₀ _ hK0] at this
    norm_num at this
  · have := h (K / s)
    have e1 : K / s * K = K ^ 2 / s := by ring
    have e2 : s / 2 * (K / s) ^ 2 = K ^ 2 / (2 * s) := by field_simp
    rw [e1, e2] at this
    have e3 : K ^ 2 / s = 2 * (K ^ 2 / (2 * s)) := by field_simp
    have : K ^ 2 / (2 * s) ≤ E := by linarith
    rw [div_le_iff₀ (by positivity)] at this
    linarith

/-- Covariance versus entropy for a sub-Gaussian observable:
`(∫ g (H - ∫ H))² ≤ 2 σ (∫ g) Ent(g)`. -/
theorem cov_sq_le_entropy {g H : Ω → ℝ} (hg : Measurable g) (hH : Measurable H) {B BH : ℝ}
    (hgB : ∀ x, |g x| ≤ B) (hHB : ∀ x, |H x| ≤ BH) (hg0 : ∀ x, 0 ≤ g x)
    (hglog : Integrable (fun x => g x * Real.log (g x)) P)
    (ha : 0 < ∫ x, g x ∂P) {σ : ℝ≥0}
    (hsub : HasSubgaussianMGF (fun x => H x - ∫ y, H y ∂P) σ P) :
    (∫ x, g x * (H x - ∫ y, H y ∂P) ∂P) ^ 2 ≤
      2 * (σ * ∫ x, g x ∂P) *
        (∫ x, g x * Real.log (g x) ∂P - (∫ x, g x ∂P) * Real.log (∫ x, g x ∂P)) := by
  set a := ∫ x, g x ∂P with hadef
  set μH := ∫ y, H y ∂P with hμH
  have hμB : |μH| ≤ BH := by
    have := norm_integral_le_of_norm_le_const (μ := P) (f := H) (C := BH)
      (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hHB x)
    simpa [Real.norm_eq_abs] using this
  have hgi : Integrable g P := Integrable.of_bound hg.aestronglyMeasurable B
    (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hgB x)
  have hgH : Integrable (fun x => g x * H x) P := by
    refine Integrable.of_bound (hg.mul hH).aestronglyMeasurable (B * BH)
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hgB x) (hHB x) (abs_nonneg _) ((abs_nonneg _).trans (hgB x))
  have key : ∀ t : ℝ, t * ∫ x, g x * (H x - μH) ∂P ≤
      (∫ x, g x * Real.log (g x) ∂P - a * Real.log a) + (σ * a) / 2 * t ^ 2 := by
    intro t
    have hψm : Measurable fun x => t * (H x - μH) := measurable_const.mul (hH.sub measurable_const)
    have hψB : ∀ x, |t * (H x - μH)| ≤ |t| * (BH + BH) := fun x => by
      rw [abs_mul]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      calc |H x - μH| ≤ |H x| + |μH| := abs_sub _ _
        _ ≤ BH + BH := add_le_add (hHB x) hμB
    have hG := gibbs_variational (P := P) hg hψm hgB hψB hg0 hglog ha
    have hexp : ∫ x, Real.exp (t * (H x - μH)) ∂P ≤ Real.exp (σ * t ^ 2 / 2) := by
      have := hsub.mgf_le t
      simpa [mgf] using this
    have hexpint : 0 < ∫ x, Real.exp (t * (H x - μH)) ∂P := by
      have hi := hsub.integrable_exp_mul t
      exact (integral_pos_iff_support_of_nonneg (fun x => (Real.exp_pos _).le) hi).2
        (by simp [Function.support, Real.exp_ne_zero])
    have hlog : Real.log (∫ x, Real.exp (t * (H x - μH)) ∂P) ≤ σ * t ^ 2 / 2 := by
      calc _ ≤ Real.log (Real.exp (σ * t ^ 2 / 2)) := Real.log_le_log hexpint hexp
        _ = _ := Real.log_exp _
    have hlin : ∫ x, g x * (t * (H x - μH)) ∂P = t * ∫ x, g x * (H x - μH) ∂P := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only; ring
    rw [hlin] at hG
    have := mul_le_mul_of_nonneg_left hlog ha.le
    nlinarith [this, hG]
  have := sq_le_of_linear_le (K := ∫ x, g x * (H x - μH) ∂P) (s := σ * a)
    (mul_nonneg σ.2 ha.le) key
  simpa [mul_comm, mul_assoc, mul_left_comm] using this

end Abstract

section SubGaussian

variable {α : Type*} [MeasurableSpace α] (μ0 : Measure α) [IsProbabilityMeasure μ0]

/-- Hoeffding for a sum of i.i.d. bounded observables under a product law. -/
theorem subgaussian_tensor_sum (N : ℕ) {c : α → ℝ} (hc : Measurable c) {r : ℝ≥0}
    (hr : ∀ a, |c a| ≤ r) :
    HasSubgaussianMGF
      (fun x : Fin N → α => ∑ i, c (x i) - ∫ y, ∑ i, c (y i) ∂(Measure.pi fun _ : Fin N => μ0))
      ((N : ℝ≥0) * r ^ 2) (Measure.pi fun _ : Fin N => μ0) := by
  set P := Measure.pi fun _ : Fin N => μ0 with hP
  have hcm : ∀ i : Fin N, Measurable fun x : Fin N → α => c (x i) := fun i =>
    hc.comp (measurable_pi_apply i)
  have hbd : ∀ (i : Fin N) (x : Fin N → α), |c (x i)| ≤ r := fun i x => hr _
  have hint : ∀ i : Fin N, Integrable (fun x : Fin N → α => c (x i)) P := fun i =>
    Integrable.of_bound (hcm i).aestronglyMeasurable r
      (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hbd i x)
  have hind : iIndepFun (fun (i : Fin N) (x : Fin N → α) => c (x i)) P :=
    iIndepFun_pi (μ := fun _ => μ0) (X := fun _ => c) (fun _ => hc.aemeasurable)
  set κ : Fin N → ℝ := fun i => ∫ y, c (y i) ∂P with hκ
  have hind' : iIndepFun (fun (i : Fin N) (x : Fin N → α) => c (x i) - κ i) P :=
    hind.comp (fun i u => u - κ i) (fun i => measurable_id.sub_const _)
  have hsub : ∀ i ∈ (Finset.univ : Finset (Fin N)),
      HasSubgaussianMGF (fun x : Fin N → α => c (x i) - κ i) ((‖(r : ℝ) - -r‖₊ / 2) ^ 2) P := by
    intro i _
    have := hasSubgaussianMGF_of_mem_Icc (μ := P) (X := fun x : Fin N → α => c (x i))
      (a := -r) (b := r) (hcm i).aemeasurable
      (Filter.Eventually.of_forall fun x => abs_le.1 (hbd i x))
    exact this
  have hsum := HasSubgaussianMGF.sum_of_iIndepFun hind' hsub
  have hpar : ∑ _i : Fin N, (‖(r : ℝ) - -r‖₊ / 2) ^ 2 = (N : ℝ≥0) * r ^ 2 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    congr 2
    apply NNReal.coe_injective
    simp only [NNReal.coe_div, coe_nnnorm, Real.norm_eq_abs, NNReal.coe_ofNat]
    rw [show (r : ℝ) - -r = 2 * r by ring, abs_of_nonneg (by positivity)]
    ring
  rw [hpar] at hsum
  refine hsum.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [hκ]
  rw [integral_finsetSum _ (fun i _ => hint i), Finset.sum_sub_distrib]

end SubGaussian

section Concrete

open DGPS.FiniteN.Tools.UniformVonMises DGPS.FiniteN.Tools.Hubbard
  DGPS.FiniteN.Tools.ConditionalMeanDerivative DGPS.Circle.AngularNormalization

/-- The Euclidean plane carrying the field `w`. -/
abbrev E2 : Type := EuclideanSpace ℝ (Fin 2)

/-- The feature map `θ ↦ (cos θ, sin θ)` on the angular circle. -/
noncomputable def phi (θ : AngCircle) : Fin 2 → ℝ :=
  ![((AddCircle.toCircle θ : Circle) : ℂ).re, ((AddCircle.toCircle θ : Circle) : ℂ).im]

theorem re_sq_add_im_sq (θ : AngCircle) :
    ((AddCircle.toCircle θ : Circle) : ℂ).re ^ 2 + ((AddCircle.toCircle θ : Circle) : ℂ).im ^ 2 = 1 := by
  have := (AddCircle.toCircle θ).normSq_coe
  simpa [Complex.normSq_apply, sq] using this

theorem phi_zero (θ : AngCircle) : phi θ 0 = ((AddCircle.toCircle θ : Circle) : ℂ).re := rfl

theorem phi_one (θ : AngCircle) : phi θ 1 = ((AddCircle.toCircle θ : Circle) : ℂ).im := rfl

theorem measurable_phi : Measurable phi := by
  have h : Continuous phi := by
    refine continuous_pi fun i => ?_
    fin_cases i
    · exact Complex.continuous_re.comp (continuous_subtype_val.comp AddCircle.continuous_toCircle)
    · exact Complex.continuous_im.comp (continuous_subtype_val.comp AddCircle.continuous_toCircle)
  exact h.measurable

theorem norm_phi_le (θ : AngCircle) : ‖phi θ‖ ≤ 1 := by
  rw [pi_norm_le_iff_of_nonneg zero_le_one]
  intro i
  have h := re_sq_add_im_sq θ
  fin_cases i
  · show ‖phi θ 0‖ ≤ 1
    rw [phi_zero, Real.norm_eq_abs]
    exact abs_le_one_iff_mul_self_le_one.2 (by nlinarith [sq_nonneg (((AddCircle.toCircle θ : Circle) : ℂ).im)])
  · show ‖phi θ 1‖ ≤ 1
    rw [phi_one, Real.norm_eq_abs]
    exact abs_le_one_iff_mul_self_le_one.2 (by nlinarith [sq_nonneg (((AddCircle.toCircle θ : Circle) : ℂ).re)])

theorem hubbardHyp_angular : HubbardHyp angHaar (fun _ : AngCircle => (0 : ℝ)) phi where
  m_ne_zero := (IsProbabilityMeasure.ne_zero angHaar)
  U_meas := measurable_const
  U_lower := ⟨0, fun _ => le_rfl⟩
  φ_meas := measurable_phi
  φ_bound := ⟨1, norm_phi_le⟩

theorem dot_phi (w : E2) (θ : AngCircle) : w.ofLp ⬝ᵥ phi θ = vmPhase w θ := by
  simp [dotProduct, Fin.sum_univ_two, phi, vmPhase]

theorem vmLaw_eq_siteLaw (w : E2) :
    vmLaw w = siteLaw (fun _ : AngCircle => (0 : ℝ)) phi angHaar w.ofLp := by
  unfold vmLaw siteLaw siteDensity expTerm auxPartition vmNorm
  simp only [expTerm, dot_phi, sub_zero]

theorem pi_vmLaw_eq_condLaw (N : ℕ+) (w : E2) :
    Measure.pi (fun _ : Fin N => vmLaw w) =
      condLaw (fun _ : AngCircle => (0 : ℝ)) phi angHaar N w.ofLp := by
  unfold condLaw
  simp_rw [vmLaw_eq_siteLaw]

section Derivative

variable (N : ℕ+) (g : (Fin N → AngCircle) → ℝ)

/-- The second moment `m(w) = q_w^{⊗N}(g)` as a function of the field. -/
noncomputable def condMoment (w : E2) : ℝ := ∫ x, g x ∂(Measure.pi fun _ : Fin N => vmLaw w)

/-- The linear map `E2 → ℝ^2` forgetting the Euclidean structure. -/
noncomputable def toFun2 : E2 →L[ℝ] (Fin 2 → ℝ) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).toContinuousLinearMap

theorem toFun2_apply (w : E2) : toFun2 w = w.ofLp := rfl

theorem condMoment_eq (w : E2) :
    condMoment N g w = condMean (fun _ : AngCircle => (0 : ℝ)) phi angHaar N g w.ofLp := by
  unfold condMoment condMean
  rw [pi_vmLaw_eq_condLaw]

variable {g}

theorem hasFDerivAt_condMoment (hg : Measurable g) {B : ℝ} (hB : ∀ x, |g x| ≤ B) (w : E2) :
    HasFDerivAt (condMoment N g)
      ((lin (condGrad (fun _ : AngCircle => (0 : ℝ)) phi angHaar N g w.ofLp)).comp toFun2) w := by
  have h1 := hasFDerivAt_condMean hubbardHyp_angular hg hB w.ofLp
  have h2 := h1.comp w (toFun2.hasFDerivAt (x := w))
  have hfun : condMoment N g = condMean (fun _ : AngCircle => (0 : ℝ)) phi angHaar N g ∘ toFun2 := by
    funext w'
    exact condMoment_eq N g w'
  rw [hfun]
  exact h2

end Derivative

section Covariance

/-- The one-site observable `θ ↦ v · (cos θ, sin θ)`. -/
noncomputable def cv (v : E2) (θ : AngCircle) : ℝ := v.ofLp ⬝ᵥ phi θ

theorem measurable_cv (v : E2) : Measurable (cv v) := by
  unfold cv dotProduct
  refine Finset.measurable_sum _ fun j _ => measurable_const.mul ?_
  exact (measurable_pi_apply j).comp measurable_phi

theorem abs_cv_le (v : E2) (θ : AngCircle) : |cv v θ| ≤ ‖v‖ := by
  have h := re_sq_add_im_sq θ
  have hn : ‖v‖ ^ 2 = v 0 ^ 2 + v 1 ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]; simp [Fin.sum_univ_two]
  have hc : cv v θ = v 0 * ((AddCircle.toCircle θ : Circle) : ℂ).re +
      v 1 * ((AddCircle.toCircle θ : Circle) : ℂ).im := by
    simp [cv, dotProduct, Fin.sum_univ_two, phi]
  rw [hc]
  refine abs_le_of_sq_le_sq' ?_ (norm_nonneg _) |> fun h' => abs_le.2 h'
  rw [hn]
  nlinarith [sq_nonneg (v 0 * ((AddCircle.toCircle θ : Circle) : ℂ).im -
    v 1 * ((AddCircle.toCircle θ : Circle) : ℂ).re)]

variable (N : ℕ+)

/-- The tensor sum `x ↦ ∑ᵢ v · (cos xᵢ, sin xᵢ)`. -/
noncomputable def tensorField (v : E2) (x : Fin N → AngCircle) : ℝ := ∑ i, cv v (x i)

theorem lin_condGrad_apply {g : (Fin N → AngCircle) → ℝ} (hg : Measurable g) {B : ℝ}
    (hB : ∀ x, |g x| ≤ B) (w v : E2) :
    ((lin (condGrad (fun _ : AngCircle => (0 : ℝ)) phi angHaar N g w.ofLp)).comp toFun2) v =
      ∫ x, g x * (tensorField N v x -
        ∫ y, tensorField N v y ∂(Measure.pi fun _ : Fin N => vmLaw w))
        ∂(Measure.pi fun _ : Fin N => vmLaw w) := by
  have hyp := hubbardHyp_angular
  obtain ⟨c, hc0, hc⟩ := abs_fieldSum_le hyp (N := N)
  set Q := condLaw (fun _ : AngCircle => (0 : ℝ)) phi angHaar N w.ofLp with hQ
  have hPQ : IsProbabilityMeasure Q := isProbabilityMeasure_condLaw hyp N w.ofLp
  have hQe : Q = Measure.pi fun _ : Fin N => vmLaw w := (pi_vmLaw_eq_condLaw N w).symm
  have hS : ∀ j, MemLp (fun x : Fin N → AngCircle => fieldSum phi x j) 2 Q := fun j =>
    memLp_condLaw hyp w.ofLp (measurable_fieldSum_apply hyp j) (fun x => hc x j)
  have hg2 : MemLp g 2 Q := memLp_condLaw hyp w.ofLp hg hB
  have hT : tensorField N v = fun x => ∑ j, v j * fieldSum phi x j := by
    funext x
    simp only [tensorField, cv, dotProduct, fieldSum, Finset.sum_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
  have hTm : MemLp (tensorField N v) 2 Q := by
    rw [hT]
    exact memLp_finsetSum (p := 2) (μ := Q) Finset.univ
      (f := fun j (x : Fin N → AngCircle) => v j * fieldSum phi x j)
      (fun j _ => (hS j).const_mul (v j))
  have hcov : cov[g, tensorField N v; Q] =
      ∑ j, v j * condGrad (fun _ : AngCircle => (0 : ℝ)) phi angHaar N g w.ofLp j := by
    rw [hT, covariance_fun_sum_right (fun j => (hS j).const_mul (v j)) hg2]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [covariance_const_mul_right]
    simp [condGrad, hQ]
  have hlin : ((lin (condGrad (fun _ : AngCircle => (0 : ℝ)) phi angHaar N g w.ofLp)).comp
      toFun2) v = ∑ j, v j * condGrad (fun _ : AngCircle => (0 : ℝ)) phi angHaar N g w.ofLp j := by
    rw [ContinuousLinearMap.comp_apply, lin_apply, toFun2_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hlin, ← hcov, ← hQe, covariance_eq_sub hg2 hTm]
  simp only [Pi.mul_apply]
  have hgi : Integrable g Q := hg2.integrable (by norm_num)
  have hgT : Integrable (fun x => g x * tensorField N v x) Q := by
    exact hg2.integrable_mul hTm
  have : ∀ x, g x * (tensorField N v x - ∫ y, tensorField N v y ∂Q) =
      g x * tensorField N v x - g x * ∫ y, tensorField N v y ∂Q := fun x => by ring
  simp_rw [this]
  rw [integral_sub hgT (hgi.mul_const _), integral_mul_const]

end Covariance

section Dichotomy

variable (N : ℕ+)

theorem pi_vm_absolutelyContinuous (w w' : E2) :
    (Measure.pi fun _ : Fin N => vmLaw w) ≪ Measure.pi fun _ : Fin N => vmLaw w' := by
  have hyp := hubbardHyp_angular
  rw [pi_vmLaw_eq_condLaw, pi_vmLaw_eq_condLaw, condLaw_eq hyp, condLaw_eq hyp]
  refine (withDensity_absolutelyContinuous _ _).trans ?_
  refine withDensity_absolutelyContinuous' ?_ ?_
  · refine ENNReal.measurable_ofReal.comp_aemeasurable ?_
    refine Measurable.aemeasurable ?_
    refine Measurable.div ?_ measurable_const
    refine Real.measurable_exp.comp ?_
    refine Measurable.sub ?_ ?_
    · unfold dotProduct
      refine Finset.measurable_sum _ fun j _ => measurable_const.mul ?_
      exact measurable_fieldSum_apply hyp j
    · unfold potSum
      exact Finset.measurable_sum _ fun i _ => measurable_const
  · refine Filter.Eventually.of_forall fun x => ?_
    have hz := auxPartition_pos hyp (m := angHaar) (U := fun _ : AngCircle => (0 : ℝ)) (φ := phi)
      w'.ofLp
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    positivity

/-- If a nonnegative integrable function has zero mean for one field, it has zero mean for all. -/
theorem integral_eq_zero_of_integral_eq_zero {g : (Fin N → AngCircle) → ℝ} (hg0 : ∀ x, 0 ≤ g x)
    {B : ℝ} (hgB : ∀ x, |g x| ≤ B) (hgm : Measurable g) (w w' : E2)
    (h : ∫ x, g x ∂(Measure.pi fun _ : Fin N => vmLaw w) = 0) :
    ∫ x, g x ∂(Measure.pi fun _ : Fin N => vmLaw w') = 0 := by
  have : IsProbabilityMeasure (Measure.pi fun _ : Fin N => vmLaw w) := by
    rw [pi_vmLaw_eq_condLaw]; exact isProbabilityMeasure_condLaw hubbardHyp_angular N w.ofLp
  have : IsProbabilityMeasure (Measure.pi fun _ : Fin N => vmLaw w') := by
    rw [pi_vmLaw_eq_condLaw]; exact isProbabilityMeasure_condLaw hubbardHyp_angular N w'.ofLp
  have hint : Integrable g (Measure.pi fun _ : Fin N => vmLaw w) :=
    Integrable.of_bound hgm.aestronglyMeasurable B (Filter.Eventually.of_forall fun x => by
      simpa using hgB x)
  have hz : g =ᵐ[Measure.pi fun _ : Fin N => vmLaw w] 0 :=
    (integral_eq_zero_iff_of_nonneg hg0 hint).mp h
  have hz' := (pi_vm_absolutelyContinuous N w' w).ae_eq hz
  rw [integral_congr_ae hz']
  simp

end Dichotomy

section Bound

variable (N : ℕ+)

theorem integrable_mul_log_of_bdd {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {g : Ω → ℝ} (hg : Measurable g) {B : ℝ} (hg0 : ∀ x, 0 ≤ g x)
    (hB : ∀ x, g x ≤ B) : Integrable (fun x => g x * Real.log (g x)) P := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := B)).exists_bound_of_continuousOn
    (f := fun t => t * Real.log t) (Real.continuous_mul_log.continuousOn)
  refine Integrable.of_bound ?_ C (Filter.Eventually.of_forall fun x => ?_)
  · exact (hg.mul (Real.measurable_log.comp hg)).aestronglyMeasurable
  · exact hC (g x) ⟨hg0 x, hB x⟩

theorem lin_sq_le {g : (Fin N → AngCircle) → ℝ} (hg : Measurable g) {B : ℝ}
    (hB : ∀ x, |g x| ≤ B) (hg0 : ∀ x, 0 ≤ g x) (w : E2) (ha : 0 < condMoment N g w) :
    ‖(lin (condGrad (fun _ : AngCircle => (0 : ℝ)) phi angHaar N g w.ofLp)).comp toFun2‖ ^ 2 ≤
      2 * (N : ℝ) * condMoment N g w *
        (∫ x, g x * Real.log (g x) ∂(Measure.pi fun _ : Fin N => vmLaw w) -
          condMoment N g w * Real.log (condMoment N g w)) := by
  have hprob : IsProbabilityMeasure (Measure.pi fun _ : Fin N => vmLaw w) := by
    rw [pi_vmLaw_eq_condLaw]; exact isProbabilityMeasure_condLaw hubbardHyp_angular N w.ofLp
  set P := Measure.pi fun _ : Fin N => vmLaw w with hP
  set a := condMoment N g w with hadef
  set ent := ∫ x, g x * Real.log (g x) ∂P - a * Real.log a with hent
  set L := (lin (condGrad (fun _ : AngCircle => (0 : ℝ)) phi angHaar N g w.ofLp)).comp toFun2
    with hL
  have hglog : Integrable (fun x => g x * Real.log (g x)) P :=
    integrable_mul_log_of_bdd hg hg0 (fun x => (abs_le.1 (hB x)).2)
  have key : ∀ v : E2, (L v) ^ 2 ≤ (2 * (N : ℝ) * a * ent) * ‖v‖ ^ 2 := by
    intro v
    have hsub := subgaussian_tensor_sum (vmLaw w) N (c := cv v) (measurable_cv v)
      (r := ‖v‖₊) (fun θ => by simpa using abs_cv_le v θ)
    have hT : Measurable (tensorField N v) :=
      Finset.measurable_sum _ fun i _ => (measurable_cv v).comp (measurable_pi_apply i)
    have hTB : ∀ x, |tensorField N v x| ≤ (N : ℝ) * ‖v‖ := by
      intro x
      calc |tensorField N v x| ≤ ∑ i, |cv v (x i)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i : Fin N, ‖v‖ := Finset.sum_le_sum fun i _ => abs_cv_le v _
        _ = (N : ℝ) * ‖v‖ := by simp
    have h := cov_sq_le_entropy (P := P) hg hT hB hTB hg0 hglog ha hsub
    rw [hL, lin_condGrad_apply N hg hB w v]
    have hσ : (((N : ℝ≥0) * ‖v‖₊ ^ 2 : ℝ≥0) : ℝ) = (N : ℝ) * ‖v‖ ^ 2 := by
      simp
    have hadef' : ∫ x, g x ∂P = a := rfl
    rw [hσ, hadef'] at h
    refine h.trans (le_of_eq ?_)
    simp only [hent]
    ring
  have h1 : 0 ≤ 2 * (N : ℝ) * a * ent := by
    have := key (EuclideanSpace.single 0 1)
    simp only [PiLp.norm_single, norm_one, one_pow, mul_one] at this
    exact le_trans (sq_nonneg _) this
  have hn : ‖L‖ ≤ Real.sqrt (2 * (N : ℝ) * a * ent) := by
    refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun v => ?_
    have : |L v| ≤ Real.sqrt (2 * (N : ℝ) * a * ent) * ‖v‖ := by
      rw [← Real.sqrt_sq (norm_nonneg v), ← Real.sqrt_mul h1, ← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt (by simpa [mul_pow] using key v)
    simpa [Real.norm_eq_abs] using this
  calc ‖L‖ ^ 2 ≤ (Real.sqrt (2 * (N : ℝ) * a * ent)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hn 2
    _ = 2 * (N : ℝ) * a * ent := Real.sq_sqrt h1

end Bound

end Concrete

end DGPS.FiniteN.Tools.ConditionalEntropyPinsker

namespace DGPS.FiniteN

open MeasureTheory DGPS.Circle.AngularNormalization DGPS.FiniteN.Tools.UniformVonMises
  DGPS.FiniteN.Tools.BoundedComparison DGPS.FiniteN.Tools.ConditionalMeanDerivative
  DGPS.FiniteN.Tools.ConditionalEntropyPinsker
open scoped ENNReal NNReal

/-- FIN014: conditional entropy mean derivative.  Given the tensorized angular log-Sobolev
inequality with constant `2/γ` for every von Mises field (the clause of FIN009), the map
`w ↦ G(w) = √(q_w^{⊗N}(f²))` is differentiable and `|∇G(w)|² ≤ (N/γ) q_w^{⊗N}(Σ_i |∂_{θ_i} f|²)`
for every admissible `f`.  The case `G(w) = 0` is handled by the dichotomy `G ≡ 0`. -/
theorem conditional_entropy_mean_derivative_by_pinsker {γ : ℝ} (hγ : 0 < γ) (N : ℕ+)
    (hlsi : ∀ (w : EuclideanSpace ℝ (Fin 2)) (F : (Fin N → AngCircle) → ℝ),
      TP AngularH1 vmGamma (fun _ : Fin N => vmLaw w) F →
        homogeneousEntropy (Measure.pi fun _ : Fin N => vmLaw w) (fun x => F x ^ 2) ≤
          ENNReal.ofReal (2 / γ) *
            ∫⁻ x, ∑ i, vmGamma (slice i F x) (x i) ∂Measure.pi fun _ : Fin N => vmLaw w)
    {f : (Fin N → AngCircle) → ℝ} (hf : Measurable f) {C : ℝ} (hC : ∀ x, |f x| ≤ C)
    (w : EuclideanSpace ℝ (Fin 2)) :
    ∃ L : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ,
      HasFDerivAt (fun w' : EuclideanSpace ℝ (Fin 2) =>
        Real.sqrt (∫ x, f x ^ 2 ∂(Measure.pi fun _ : Fin N => vmLaw w'))) L w ∧
      (TP AngularH1 vmGamma (fun _ : Fin N => vmLaw w) f →
        ENNReal.ofReal (‖L‖ ^ 2) ≤ ENNReal.ofReal ((N : ℝ) / γ) *
          ∫⁻ x, ∑ i, vmGamma (slice i f x) (x i) ∂Measure.pi fun _ : Fin N => vmLaw w) := by
  set g : (Fin N → AngCircle) → ℝ := fun x => f x ^ 2 with hgdef
  have hg : Measurable g := hf.pow_const 2
  have hg0 : ∀ x, 0 ≤ g x := fun x => sq_nonneg _
  have hB : ∀ x, |g x| ≤ C ^ 2 := fun x => by
    rw [abs_of_nonneg (hg0 x), hgdef]
    exact (sq_le_sq' (abs_le.1 (hC x)).1 (abs_le.1 (hC x)).2)
  have hprob : ∀ w' : EuclideanSpace ℝ (Fin 2),
      IsProbabilityMeasure (Measure.pi fun _ : Fin N => vmLaw w') := fun w' => by
    rw [pi_vmLaw_eq_condLaw]; exact isProbabilityMeasure_condLaw hubbardHyp_angular N w'.ofLp
  have hm0 : 0 ≤ condMoment N g w := integral_nonneg hg0
  rcases hm0.eq_or_lt with h0 | hpos
  · refine ⟨0, ?_, fun _ => by simp⟩
    have hz : ∀ w', condMoment N g w' = 0 := fun w' =>
      integral_eq_zero_of_integral_eq_zero N hg0 hB hg w w' h0.symm
    have : (fun w' : EuclideanSpace ℝ (Fin 2) =>
        Real.sqrt (∫ x, f x ^ 2 ∂(Measure.pi fun _ : Fin N => vmLaw w'))) = fun _ => 0 := by
      funext w'
      have := hz w'
      simp only [condMoment, hgdef] at this
      rw [this]; simp
    rw [this]
    exact hasFDerivAt_const _ _
  · set Lg := (lin (condGrad (fun _ : AngCircle => (0 : ℝ)) phi angHaar N g w.ofLp)).comp toFun2
      with hLg
    have hd := (hasFDerivAt_condMoment N hg hB w).sqrt hpos.ne'
    refine ⟨(1 / (2 * Real.sqrt (condMoment N g w))) • Lg, hd, fun hTP => ?_⟩
    set a := condMoment N g w with ha
    set E := ∫⁻ x, ∑ i, vmGamma (slice i f x) (x i) ∂Measure.pi fun _ : Fin N => vmLaw w with hE
    by_cases hEt : E = ⊤
    · rw [hEt, ENNReal.mul_top (by simp; positivity)]; exact le_top
    have hP := hprob w
    have hint : Integrable g (Measure.pi fun _ : Fin N => vmLaw w) :=
      Integrable.of_bound hg.aestronglyMeasurable (C ^ 2)
        (Filter.Eventually.of_forall fun x => by simpa using hB x)
    have hglog : Integrable (fun x => g x * Real.log (g x))
        (Measure.pi fun _ : Fin N => vmLaw w) :=
      integrable_mul_log_of_bdd hg hg0 (fun x => (abs_le.1 (hB x)).2)
    have hent := homogeneousEntropy_eq_formula (P := Measure.pi fun _ : Fin N => vmLaw w)
      (Filter.Eventually.of_forall hg0) hint hglog
    have hl := hlsi w f hTP
    have hl' : ENNReal.ofReal (∫ x, g x * Real.log (g x) ∂(Measure.pi fun _ : Fin N => vmLaw w) -
        a * Real.log a) ≤ ENNReal.ofReal (2 / γ) * E := by
      have : homogeneousEntropy (Measure.pi fun _ : Fin N => vmLaw w) (fun x => f x ^ 2) =
          homogeneousEntropy (Measure.pi fun _ : Fin N => vmLaw w) g := rfl
      rw [this, hent] at hl
      exact hl
    set e := E.toReal with he
    have hEe : E = ENNReal.ofReal e := (ENNReal.ofReal_toReal hEt).symm
    have he0 : 0 ≤ e := ENNReal.toReal_nonneg
    rw [hEe, ← ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_le_ofReal_iff (by positivity)] at hl'
    have hb := lin_sq_le N hg hB hg0 w hpos
    set ent := ∫ x, g x * Real.log (g x) ∂(Measure.pi fun _ : Fin N => vmLaw w) -
      a * Real.log a with hentdef
    rw [hEe, ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hsa : 0 < Real.sqrt a := Real.sqrt_pos.2 hpos
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    have hsq : (1 / (2 * Real.sqrt a)) ^ 2 = 1 / (4 * a) := by
      rw [div_pow, mul_pow, Real.sq_sqrt hpos.le]; norm_num
    rw [hsq]
    have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
    calc 1 / (4 * a) * ‖Lg‖ ^ 2 ≤ 1 / (4 * a) * (2 * (N : ℝ) * a * ent) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ = (N : ℝ) / 2 * ent := by field_simp; ring
      _ ≤ (N : ℝ) / 2 * (2 / γ * e) := mul_le_mul_of_nonneg_left hl' (by positivity)
      _ = (N : ℝ) / γ * e := by field_simp

/-- FIN014 with the constant supplied by FIN009 (`uniform_one_site_von_mises_lsi`). -/
theorem conditional_entropy_mean_derivative_by_pinsker_exists (N : ℕ+) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ {f : (Fin N → AngCircle) → ℝ}, Measurable f → ∀ {C : ℝ},
      (∀ x, |f x| ≤ C) → ∀ w : EuclideanSpace ℝ (Fin 2),
        ∃ L : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ,
          HasFDerivAt (fun w' : EuclideanSpace ℝ (Fin 2) =>
            Real.sqrt (∫ x, f x ^ 2 ∂(Measure.pi fun _ : Fin N => vmLaw w'))) L w ∧
          (TP AngularH1 vmGamma (fun _ : Fin N => vmLaw w) f →
            ENNReal.ofReal (‖L‖ ^ 2) ≤ ENNReal.ofReal ((N : ℝ) / γ) *
              ∫⁻ x, ∑ i, vmGamma (slice i f x) (x i) ∂Measure.pi fun _ : Fin N => vmLaw w) := by
  obtain ⟨γ, hγ, -, h⟩ := uniform_one_site_von_mises_lsi
  exact ⟨γ, hγ, fun {_} hf {_} hC w =>
    conditional_entropy_mean_derivative_by_pinsker hγ N
      (fun w' F hF => h N (fun _ => w') F hF) hf hC w⟩

end DGPS.FiniteN
