import SharpSymmetricLSI.Paper.LyapSchmidt17

/-!
# Section 4.2 (lane s42; R14): weak gradients on the graph

For `h` on the zero set (`log(1+h) + T h = c + ∑ bᵢ φᵢ`): `1 + h = exp(F)` with
`F = const - W * (p (h + ∑ bᵢ φᵢ))`, hence
`∇h = -(1 + h) (∇(W * (p h)) + ∑ bᵢ ∇(W * (p φᵢ)))`; and `∇ φᵢ = -∇(W * (p φᵢ))`.
-/

noncomputable section
open MeasureTheory Filter Real Topology Metric
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

section wgrad
variable (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
  {n : ℕ} {φ : Fin n → Torus d → ℝ} (hφ : IsKerBasis' W μ φ)
include hyp hμ hφ

theorem isWeakGrad_phiC (i : Fin n) :
    IsWeakGrad (⇑(phiC hyp hφ i))
      (fun x k => -bForceL W (fun y => elDens V W (μ : Measure (Torus d)) y * φ i y) x k) := by
  obtain ⟨Ki, hKi⟩ := Top_eq_convDens hyp hμ (φ i)
  have hpφ : Integrable (fun y => elDens V W (μ : Measure (Torus d)) y * φ i y) (haar d) :=
    integrable_elDens_mul hyp hμ ((memL20_phi hyp hφ i).1.integrable one_le_two)
  have h1 := ((isWeakGrad_convDens' hyp hpφ).sub_const Ki).cmul (-1)
  convert h1 using 1
  · funext x
    show -Top W (μ : Measure (Torus d)) (φ i) x = _
    rw [hKi x]; ring
  · funext x k; ring

theorem isWeakGrad_kC (a : EuclideanSpace ℝ (Fin n)) :
    IsWeakGrad (⇑(kC hyp hφ a))
      (fun x k => -∑ i, a i * bForceL W (fun y => elDens V W (μ : Measure (Torus d)) y * φ i y)
        x k) := by
  have h1 := isWeakGrad_finsetSum (ι := Fin d) Finset.univ
    (f := fun i x => a i * phiC hyp hφ i x)
    (g := fun i x k => a i * -bForceL W (fun y => elDens V W (μ : Measure (Torus d)) y * φ i y)
      x k) fun i _ => (isWeakGrad_phiC hyp hμ hφ i).cmul (a i)
  convert h1 using 1
  · funext x; rw [kC_apply]
  · funext x k
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring

/-- **The weak gradient of `h` on the zero set.** -/
theorem isWeakGrad_graph {h : CT d} (hpos : h ∈ posSet)
    (hh0 : ∫ x, h x ∂(μ : Measure (Torus d)) = 0) {c : ℝ} {b : Fin n → ℝ}
    (hP : ∀ x, PhiC hyp (μ : Measure (Torus d)) h x = c + ∑ i, b i * phiC hyp hφ i x) :
    IsWeakGrad (⇑h) (fun x k => -(1 + h x) *
      (bForceL W (fun y => elDens V W (μ : Measure (Torus d)) y * h y) x k +
        ∑ i, b i * bForceL W (fun y => elDens V W (μ : Measure (Torus d)) y * φ i y) x k)) := by
  set μm := (μ : Measure (Torus d))
  set p := elDens V W μm with hp
  obtain ⟨hpm, hp0, hp1⟩ := elDensity_props hyp μm
  have hpi : Integrable p (haar d) := integrable_of_integral_eq_one' hp1
  have hph : Integrable (fun y => p y * h y) (haar d) :=
    integrable_elDens_mul hyp hμ (integrable_of_continuous h.continuous)
  have hpφ : ∀ i, Integrable (fun y => p y * φ i y) (haar d) := fun i =>
    integrable_elDens_mul hyp hμ ((memL20_phi hyp hφ i).1.integrable one_le_two)
  have hsum : Integrable (fun y => ∑ i, b i * (p y * φ i y)) (haar d) :=
    integrable_finsetSum _ fun i _ => (hpφ i).const_mul (b i)
  obtain ⟨K₀, hK₀⟩ := log_density_eq hyp hμ hφ hpos hP
  set g : Torus d → ℝ := fun y => p y * (1 + h y + ∑ i, b i * φ i y) with hg
  have hgsplit : g = fun y => 1 * p y + 1 * (fun y => 1 * (p y * h y) +
      1 * ∑ i, b i * (p y * φ i y)) y := by
    funext y; simp only [hg, one_mul]
    rw [mul_add, mul_add, mul_one, Finset.mul_sum]
    rw [add_assoc]; congr 2
    exact Finset.sum_congr rfl fun i _ => by ring
  have hrest : Integrable (fun y => 1 * (p y * h y) + 1 * ∑ i, b i * (p y * φ i y)) (haar d) :=
    (hph.const_mul 1).add (hsum.const_mul 1)
  have hgi : Integrable g (haar d) := by
    rw [hgsplit]; exact (hpi.const_mul 1).add (hrest.const_mul 1)
  set Zμ := ∫ y, Real.exp (-V y - convMeas W μm y) ∂haar d
  -- `log(1 + h) = F`
  set F : Torus d → ℝ := fun x => K₀ + Real.log Zμ - convDens W g x + convDens W p x with hF
  have hconv : ∀ x, convMeas W μm x = convDens W p x := fun x => by
    unfold convMeas
    rw [integral_minimizer hyp hμ]
    unfold convDens
    congr 1; funext y; ring
  have hFeq : ∀ x, F x = Real.log (1 + h x) := fun x => by
    have h1 := hK₀ x
    rw [Real.log_mul (hp0 x).ne' (hpos x).ne', log_elDens hyp μm x, hconv x] at h1
    simp only [hF]
    linarith
  -- weak gradient of `F`
  set GF : Torus d → Fin d → ℝ := fun x k => -bForceL W g x k + bForceL W p x k with hGF
  have hFw : IsWeakGrad F GF := by
    have := ((isWeakGrad_const (K₀ + Real.log Zμ)).add
      ((isWeakGrad_convDens' hyp hgi).cmul (-1))).add (isWeakGrad_convDens' hyp hpi)
    convert this using 1
    · funext x; simp only [hF]; ring
    · funext x k; simp only [hGF, Pi.zero_apply]; ring
  -- bounds on `F`
  obtain ⟨mh, hmh, hmhx⟩ := exists_pos_lower hpos
  set M := 2 * (|Real.log mh| + |Real.log (1 + ‖h‖)|) with hM
  have hM0 : 0 ≤ M := by positivity
  have h2F : ∀ x, |2 * F x| ≤ M := fun x => by
    rw [hFeq, abs_mul, abs_two, hM]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    have h1 := Real.log_le_log hmh (hmhx x)
    have h2 := Real.log_le_log (hpos x) (show 1 + h x ≤ 1 + ‖h‖ by
      linarith [le_abs_self (h x), abs_CT_le h x])
    rw [abs_le]
    constructor
    · linarith [neg_abs_le (Real.log mh), abs_nonneg (Real.log (1 + ‖h‖))]
    · linarith [le_abs_self (Real.log (1 + ‖h‖)), abs_nonneg (Real.log mh)]
  have hFc : Continuous F := by
    have : F = fun x => Real.log (1 + h x) := funext hFeq
    rw [this]; exact (continuous_const.add h.continuous).log fun x => (hpos x).ne'
  obtain ⟨Cb₀, hCb₀⟩ := bGrad_bdd hyp (W := W)
  have hbF : ∀ {u : Torus d → ℝ}, Integrable u (haar d) → ∀ x k,
      |bForceL W u x k| ≤ max Cb₀ 0 * ∫ y, |u y| ∂haar d := fun {u} hu x k => by
    unfold bForceL
    refine (abs_integral_le_integral_abs).trans ?_
    rw [← integral_const_mul]
    refine integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _)
      (hu.abs.const_mul _) (Eventually.of_forall fun y => ?_)
    show |bGrad W x y k * u y| ≤ max Cb₀ 0 * |u y|
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right ((hCb₀ x y k).trans (le_max_left _ _)) (abs_nonneg _)
  have hGFm : ∀ k, Measurable fun x => 2 * GF x k := fun k =>
    measurable_const.mul (((measurable_bForceL' hyp hgi k).neg).add (measurable_bForceL' hyp hpi k))
  have hGFi : ∀ k, Integrable (fun x => 2 * GF x k) volume := fun k =>
    integrable_of_bdd (hGFm k)
      (C := 2 * (max Cb₀ 0 * ∫ y, |g y| ∂haar d + max Cb₀ 0 * ∫ y, |p y| ∂haar d)) fun x => by
      simp only [hGF, abs_mul, abs_two]
      refine mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans (add_le_add ?_ (hbF hpi x k)))
        (by norm_num)
      rw [abs_neg]; exact hbF hgi x k
  obtain ⟨Lc, hLc⟩ := deriv_expCut_bdd M hM0
  have h3 := isWeakGrad_comp (hFw.cmul 2) (integrable_of_continuous (continuous_const.mul hFc))
    hGFi ((contDiff_expCut M hM0).of_le (by simp)) hLc
  have hexp : ∀ x, Real.exp (2 * F x / 2) = 1 + h x := fun x => by
    rw [mul_div_cancel_left₀ _ two_ne_zero, hFeq, Real.exp_log (hpos x)]
  have h4 : IsWeakGrad (fun x => 1 + h x) (fun x k => (1 + h x) * GF x k) := by
    convert h3 using 1
    · funext x; rw [expCut_eq hM0 (h2F x), hexp]
    · funext x k; rw [deriv_expCut hM0 (h2F x), hexp]; ring
  have h5 := h4.sub_const 1
  -- the linear algebra of the forces
  have hdiff : ∀ x k, GF x k = -(bForceL W (fun y => p y * h y) x k +
      ∑ i, b i * bForceL W (fun y => p y * φ i y) x k) := fun x k => by
    simp only [hGF]
    rw [hgsplit, bForceL_add hyp hpi hrest 1 1 x k, bForceL_add hyp hph hsum 1 1 x k]
    have hs := bForceL_finsetSum hyp hpφ b x k
    have e : (fun y => ∑ i, b i * (p y * φ i y)) = fun y => ∑ i, b i * (fun y => p y * φ i y) y :=
      rfl
    rw [e, hs]
    ring
  convert h5 using 1
  · funext x; ring
  · funext x k; rw [hdiff]; ring

end wgrad

end SharpLSI
