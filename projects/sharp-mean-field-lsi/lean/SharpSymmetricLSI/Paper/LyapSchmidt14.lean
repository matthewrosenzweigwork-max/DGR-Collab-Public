import SharpSymmetricLSI.Paper.LyapSchmidt13

/-!
# Section 4.2 (lane s42; R14): minimizers near `μ` in the reduction coordinates

* `convC F ν = ∫ F(·, y) dν(y)` is continuous from `𝒫(𝕋^d)` (weak topology) into `C(𝕋^d)`
  (sup norm), by a finite-rank approximation of `F`;
* the density ratio `hR ν = elDens(ν)/p - 1` is continuous in `ν` (weak → sup norm);
* for a minimizer `ν`: `ν = p(1 + hR ν) m`, `μ(hR ν) = 0`, `1 + hR ν > 0`, and
  `log(1 + hR ν) + T(hR ν)` is constant (Euler–Lagrange), so `P(log(1+h) + T h) = 0`.
-/

noncomputable section
open MeasureTheory InformationTheory Filter Real Topology Metric BoundedContinuousFunction
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-- `∫ F(·, y) dν(y)` as a continuous function. -/
def convC {F : Torus d → Torus d → ℝ} (hF : Continuous (Function.uncurry F))
    (ν : ProbabilityMeasure (Torus d)) : CT d :=
  ⟨fun x => ∫ y, F x y ∂(ν : Measure (Torus d)), cont_integral_right hF (ν : Measure (Torus d))⟩

theorem convC_apply {F : Torus d → Torus d → ℝ} (hF : Continuous (Function.uncurry F))
    (ν : ProbabilityMeasure (Torus d)) (x : Torus d) :
    convC hF ν x = ∫ y, F x y ∂(ν : Measure (Torus d)) := rfl

/-- **`ν ↦ ∫ F(·,y) dν(y)` is continuous into `C(𝕋^d)`.** -/
theorem continuous_convC {F : Torus d → Torus d → ℝ} (hF : Continuous (Function.uncurry F)) :
    Continuous (convC hF) := by
  rw [continuous_iff_continuousAt]
  intro ν₀
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨m, f, g, hfg⟩ := exists_finiteRank_approx hF (by positivity : 0 < ε / 4)
  set Cf := ∑ i, ‖f i‖ + 1 with hCf
  have hCf0 : 0 < Cf := by positivity
  set δ := ε / (4 * Cf) with hδ
  have hδ0 : 0 < δ := by positivity
  have hG : ∀ i, Continuous fun ν : ProbabilityMeasure (Torus d) =>
      ∫ y, g i y ∂(ν : Measure (Torus d)) := fun i =>
    ProbabilityMeasure.continuous_integral_boundedContinuousFunction (mkOfCompact (g i))
  have hev : ∀ᶠ ν : ProbabilityMeasure (Torus d) in 𝓝 ν₀, ∀ i, |∫ y, g i y ∂(ν : Measure (Torus d)) -
      ∫ y, g i y ∂(ν₀ : Measure (Torus d))| < δ := by
    refine Filter.eventually_all.mpr fun i => ?_
    have := ((hG i).tendsto ν₀).eventually (Metric.ball_mem_nhds _ hδ0)
    filter_upwards [this] with ν hν
    rwa [Real.dist_eq] at hν
  have key : ∀ (ν : ProbabilityMeasure (Torus d)) (x : Torus d),
      ∫ y, F x y ∂(ν : Measure (Torus d)) =
        ∫ y, (F x y - ∑ i, f i x * g i y) ∂(ν : Measure (Torus d)) +
          ∑ i, f i x * ∫ y, g i y ∂(ν : Measure (Torus d)) := fun ν x => by
    have i1 : Integrable (fun y => F x y) (ν : Measure (Torus d)) :=
      integrable_of_continuous (cont_right hF x)
    have i2 : ∀ i ∈ (Finset.univ : Finset (Fin m)),
        Integrable (fun y => f i x * g i y) (ν : Measure (Torus d)) := fun i _ =>
      integrable_of_continuous (continuous_const.mul (g i).continuous)
    have i3 : Integrable (fun y => ∑ i, f i x * g i y) (ν : Measure (Torus d)) :=
      integrable_finsetSum _ i2
    rw [integral_sub i1 i3, integral_finsetSum _ i2]
    simp_rw [integral_const_mul]
    ring
  have happrox : ∀ (ν : ProbabilityMeasure (Torus d)) (x : Torus d),
      |∫ y, (F x y - ∑ i, f i x * g i y) ∂(ν : Measure (Torus d))| ≤ ε / 4 := fun ν x =>
    abs_integral_le_of_bdd fun y => (hfg x y).le
  filter_upwards [hev] with ν hν
  rw [dist_eq_norm]
  refine lt_of_le_of_lt ((ContinuousMap.norm_le _ (by positivity : (0 : ℝ) ≤ 3 * ε / 4)).mpr
    fun x => ?_) (by linarith)
  rw [Real.norm_eq_abs, ContinuousMap.sub_apply, convC_apply, convC_apply, key ν x, key ν₀ x]
  have h1 := happrox ν x
  have h2 := happrox ν₀ x
  have h3 : |∑ i, f i x * ∫ y, g i y ∂(ν : Measure (Torus d)) -
      ∑ i, f i x * ∫ y, g i y ∂(ν₀ : Measure (Torus d))| ≤ ε / 4 := by
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i, |f i x * ∫ y, g i y ∂(ν : Measure (Torus d)) -
          f i x * ∫ y, g i y ∂(ν₀ : Measure (Torus d))| ≤ ∑ i, ‖f i‖ * δ :=
          Finset.sum_le_sum fun i _ => by
            rw [← mul_sub, abs_mul]
            exact mul_le_mul (abs_CT_le (f i) x) (hν i).le (abs_nonneg _) (norm_nonneg _)
      _ ≤ Cf * δ := by
          rw [← Finset.sum_mul]
          exact mul_le_mul_of_nonneg_right (by rw [hCf]; linarith) hδ0.le
      _ = ε / 4 := by rw [hδ]; field_simp
  calc |∫ y, (F x y - ∑ i, f i x * g i y) ∂(ν : Measure (Torus d)) +
        ∑ i, f i x * ∫ y, g i y ∂(ν : Measure (Torus d)) -
        (∫ y, (F x y - ∑ i, f i x * g i y) ∂(ν₀ : Measure (Torus d)) +
        ∑ i, f i x * ∫ y, g i y ∂(ν₀ : Measure (Torus d)))|
      ≤ |∫ y, (F x y - ∑ i, f i x * g i y) ∂(ν : Measure (Torus d))| +
        |∫ y, (F x y - ∑ i, f i x * g i y) ∂(ν₀ : Measure (Torus d))| +
        |∑ i, f i x * ∫ y, g i y ∂(ν : Measure (Torus d)) -
          ∑ i, f i x * ∫ y, g i y ∂(ν₀ : Measure (Torus d))| := by
        have := abs_add_three
          (∫ y, (F x y - ∑ i, f i x * g i y) ∂(ν : Measure (Torus d)))
          (-∫ y, (F x y - ∑ i, f i x * g i y) ∂(ν₀ : Measure (Torus d)))
          (∑ i, f i x * ∫ y, g i y ∂(ν : Measure (Torus d)) -
            ∑ i, f i x * ∫ y, g i y ∂(ν₀ : Measure (Torus d)))
        rw [abs_neg] at this
        convert this using 2; ring
    _ ≤ 3 * ε / 4 := by linarith

section ratio
variable (hyp : Hyp V W KV KW)
include hyp

/-- `u ↦ e^{-V-u}` on `C(𝕋^d)`. -/
def expVC (u : CT d) : CT d :=
  (⟨Real.exp, continuous_exp⟩ : C(ℝ, ℝ)).comp (⟨fun x => -V x, hyp.continuous_V.neg⟩ - u)

theorem expVC_apply (u : CT d) (x : Torus d) : expVC hyp u x = Real.exp (-V x - u x) := rfl

theorem continuous_expVC : Continuous (expVC hyp (d := d)) :=
  (ContinuousMap.continuous_postcomp _).comp (continuous_const.sub continuous_id)

theorem integral_expVC_pos (u : CT d) : 0 < ∫ x, expVC hyp u x ∂haar d :=
  integral_exp_pos (integrable_of_continuous (expVC hyp u).continuous)

/-- `e^{-V-u} / ∫ e^{-V-u} dm`. -/
def elC (u : CT d) : CT d := (∫ x, expVC hyp u x ∂haar d)⁻¹ • expVC hyp u

theorem continuous_elC : Continuous (elC hyp (d := d)) := by
  have h1 : Continuous fun u : CT d => ∫ x, expVC hyp u x ∂haar d := by
    have : (fun u : CT d => ∫ x, expVC hyp u x ∂haar d) =
        fun u => meanC (haar d) (expVC hyp u) := by
      funext u; rw [meanC_apply]
    rw [this]
    exact (meanC (haar d)).continuous.comp (continuous_expVC hyp)
  exact (h1.inv₀ fun u => (integral_expVC_pos hyp u).ne').smul (continuous_expVC hyp)

theorem elC_convC (ν : ProbabilityMeasure (Torus d)) (x : Torus d) :
    elC hyp (convC hyp.continuous_W ν) x = elDens V W (ν : Measure (Torus d)) x := by
  simp only [elC, ContinuousMap.smul_apply, smul_eq_mul, expVC_apply, convC_apply, elDens,
    convMeas]
  rw [div_eq_inv_mul]

/-- `1 / p` as a continuous function (`p = elDens μ`). -/
def pinvC (μ : ProbabilityMeasure (Torus d)) : CT d :=
  ⟨fun x => (elC hyp (convC hyp.continuous_W μ) x)⁻¹,
    (elC hyp (convC hyp.continuous_W μ)).continuous.inv₀ fun x => by
      rw [elC_convC]
      exact ((elDensity_props hyp (μ : Measure (Torus d))).2.1 x).ne'⟩

/-- The density ratio `elDens(ν)/p - 1`. -/
def hR (μ ν : ProbabilityMeasure (Torus d)) : CT d :=
  elC hyp (convC hyp.continuous_W ν) * pinvC hyp μ - 1

variable {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
include hμ

omit hμ in
theorem hR_apply (ν : ProbabilityMeasure (Torus d)) (x : Torus d) :
    hR hyp μ ν x = elDens V W (ν : Measure (Torus d)) x /
      elDens V W (μ : Measure (Torus d)) x - 1 := by
  simp only [hR, pinvC, ContinuousMap.sub_apply, ContinuousMap.mul_apply, ContinuousMap.coe_mk,
    ContinuousMap.one_apply, elC_convC, div_eq_mul_inv]

omit hμ in
theorem continuous_hR : Continuous (hR hyp μ) :=
  (((continuous_elC hyp).comp (continuous_convC hyp.continuous_W)).mul continuous_const).sub
    continuous_const

theorem hR_self : hR hyp μ μ = 0 := by
  ext x
  rw [hR_apply, div_self ((elDensity_props hyp (μ : Measure (Torus d))).2.1 x).ne', sub_self]
  rfl

theorem elDens_eq_hR (ν : ProbabilityMeasure (Torus d)) (x : Torus d) :
    elDens V W (ν : Measure (Torus d)) x =
      elDens V W (μ : Measure (Torus d)) x * (1 + hR hyp μ ν x) := by
  rw [hR_apply]
  have := ((elDensity_props hyp (μ : Measure (Torus d))).2.1 x).ne'
  field_simp
  ring

theorem hR_pos (ν : ProbabilityMeasure (Torus d)) : hR hyp μ ν ∈ posSet := fun x => by
  have h1 := (elDensity_props hyp (ν : Measure (Torus d))).2.1 x
  have h2 := (elDensity_props hyp (μ : Measure (Torus d))).2.1 x
  rw [elDens_eq_hR hyp hμ ν x] at h1
  exact pos_of_mul_pos_right h1 h2.le

theorem mean_hR (ν : ProbabilityMeasure (Torus d)) :
    ∫ x, hR hyp μ ν x ∂(μ : Measure (Torus d)) = 0 := by
  have h1 := (elDensity_props hyp (ν : Measure (Torus d))).2.2
  simp_rw [elDens_eq_hR hyp hμ ν] at h1
  rw [← integral_minimizer hyp hμ (fun x => 1 + hR hyp μ ν x),
    integral_add (integrable_const _) (integrable_of_continuous (hR hyp μ ν).continuous)] at h1
  simp only [integral_const, probReal_univ, smul_eq_mul, mul_one] at h1
  linarith

theorem minimizer_eq_graph {ν : ProbabilityMeasure (Torus d)} (hν : IsMinimizer V W ν) :
    (ν : Measure (Torus d)) = densMeasure fun x =>
      elDens V W (μ : Measure (Torus d)) x * (1 + hR hyp μ ν x) := by
  rw [minimizer_eq_elDensity hyp hν]
  congr 1
  funext x
  exact elDens_eq_hR hyp hμ ν x

theorem integral_minimizer_graph {ν : ProbabilityMeasure (Torus d)} (hν : IsMinimizer V W ν)
    (F : Torus d → ℝ) : ∫ x, F x ∂(ν : Measure (Torus d)) =
      ∫ x, (1 + hR hyp μ ν x) * F x ∂(μ : Measure (Torus d)) := by
  rw [minimizer_eq_graph hyp hμ hν]
  exact integral_graph_density hyp hμ (hR_pos hyp hμ ν) (mean_hR hyp hμ ν) F

omit hμ in
theorem log_elDens (ν : Measure (Torus d)) [IsProbabilityMeasure ν] (x : Torus d) :
    Real.log (elDens V W ν x) = -V x - convMeas W ν x -
      Real.log (∫ y, Real.exp (-V y - convMeas W ν y) ∂haar d) := by
  have hZ : 0 < ∫ y, Real.exp (-V y - convMeas W ν y) ∂haar d := by
    exact integral_exp_pos (integrable_of_continuous
      (continuous_exp.comp (hyp.continuous_V.neg.sub (cont_integral_right hyp.continuous_W ν))))
  simp only [elDens]
  rw [Real.log_div (exp_pos _).ne' hZ.ne', Real.log_exp]

/-- Euler–Lagrange: `log(1 + hR ν) + T(hR ν)` is constant for a minimizer `ν`. -/
theorem PhiC_hR_const {ν : ProbabilityMeasure (Torus d)} (hν : IsMinimizer V W ν) :
    ∃ c : ℝ, ∀ x, PhiC hyp (μ : Measure (Torus d)) (hR hyp μ ν) x = c := by
  obtain ⟨Kh, hKh⟩ : ∃ K : ℝ, ∀ x, Top W (μ : Measure (Torus d)) (⇑(hR hyp μ ν)) x =
      ∫ y, W x y * hR hyp μ ν y ∂(μ : Measure (Torus d)) - K := ⟨_, fun x => rfl⟩
  refine ⟨Real.log (∫ y, Real.exp (-V y - convMeas W (μ : Measure (Torus d)) y) ∂haar d) -
    Real.log (∫ y, Real.exp (-V y - convMeas W (ν : Measure (Torus d)) y) ∂haar d) - Kh,
    fun x => ?_⟩
  have hp0 := (elDensity_props hyp (μ : Measure (Torus d))).2.1 x
  have hν0 := (elDensity_props hyp (ν : Measure (Torus d))).2.1 x
  have h1 : 1 + hR hyp μ ν x = elDens V W (ν : Measure (Torus d)) x /
      elDens V W (μ : Measure (Torus d)) x := by
    rw [hR_apply]; ring
  have hconv : convMeas W (ν : Measure (Torus d)) x = convMeas W (μ : Measure (Torus d)) x +
      ∫ y, W x y * hR hyp μ ν y ∂(μ : Measure (Torus d)) := by
    unfold convMeas
    rw [integral_minimizer_graph hyp hμ hν]
    have i1 : Integrable (fun y => W x y) (μ : Measure (Torus d)) :=
      integrable_of_continuous (cont_right hyp.continuous_W x)
    have i2 : Integrable (fun y => W x y * hR hyp μ ν y) (μ : Measure (Torus d)) :=
      integrable_of_continuous ((cont_right hyp.continuous_W x).mul (hR hyp μ ν).continuous)
    rw [← integral_add i1 i2]
    congr 1; funext y; ring
  have e : PhiC hyp (μ : Measure (Torus d)) (hR hyp μ ν) x =
      logC (hR hyp μ ν) x + Top W (μ : Measure (Torus d)) (⇑(hR hyp μ ν)) x := rfl
  rw [e, logC_apply (hR_pos hyp hμ ν), hKh x, h1, Real.log_div hν0.ne' hp0.ne',
    log_elDens hyp, log_elDens hyp, hconv]
  ring

theorem QCraw_PhiC_hR {n : ℕ} {φ : Fin n → Torus d → ℝ} (hφ : IsKerBasis' W μ φ)
    {ν : ProbabilityMeasure (Torus d)} (hν : IsMinimizer V W ν) :
    QCraw hyp hφ (PhiC hyp (μ : Measure (Torus d)) (hR hyp μ ν)) = 0 := by
  obtain ⟨c, hc⟩ := PhiC_hR_const hyp hμ hν
  have e : PhiC hyp (μ : Measure (Torus d)) (hR hyp μ ν) = c • (1 : CT d) := by
    ext x; rw [hc x]; simp
  rw [e, map_smul]
  have h1 : QCraw hyp hφ (1 : CT d) = 0 := by
    ext x
    rw [QCraw_apply]
    simp [integral_phiC hyp hφ]
  rw [h1, smul_zero]

theorem coord_minimizer {n : ℕ} {φ : Fin n → Torus d → ℝ} (hφ : IsKerBasis' W μ φ)
    {ν : ProbabilityMeasure (Torus d)} (hν : IsMinimizer V W ν) (i : Fin n) :
    ∫ x, phiC hyp hφ i x ∂(ν : Measure (Torus d)) =
      ∫ x, hR hyp μ ν x * phiC hyp hφ i x ∂(μ : Measure (Torus d)) := by
  rw [integral_minimizer_graph hyp hμ hν]
  have i1 : Integrable (fun x => phiC hyp hφ i x) (μ : Measure (Torus d)) :=
    integrable_of_continuous (phiC hyp hφ i).continuous
  have i2 : Integrable (fun x => hR hyp μ ν x * phiC hyp hφ i x) (μ : Measure (Torus d)) :=
    integrable_of_continuous ((hR hyp μ ν).continuous.mul (phiC hyp hφ i).continuous)
  have e : (fun x => (1 + hR hyp μ ν x) * phiC hyp hφ i x) =
      fun x => phiC hyp hφ i x + hR hyp μ ν x * phiC hyp hφ i x := by funext x; ring
  rw [e, integral_add i1 i2, integral_phiC hyp hφ, zero_add]

end ratio

end SharpLSI
