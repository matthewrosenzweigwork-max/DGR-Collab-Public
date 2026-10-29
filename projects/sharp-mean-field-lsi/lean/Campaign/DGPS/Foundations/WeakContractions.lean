import DGPS.Foundations.PeriodicSmoothing
import SharpSymmetricLSI.Infra.ChainRule
import SharpSymmetricLSI.Infra.Mollify

/-!
# Weak contractions, products and the norm chain rule (FOU003)

On the unit torus `Torus d` with Haar probability measure, for the campaign weak gradient
`IsWeakGradient`:

* a bridge from the campaign weak gradient to the legacy `SharpLSI.IsWeakGrad`, giving
  `∇u = 0` a.e. on level sets;
* `L¹`-closure of weak gradients, and the product rule with smooth and `W^{1,∞}` factors;
* the vector chain rule `|u| ∈ H¹` for finite vectors `u`, with gradient `(u·∇u)/|u|`
  (zero on `{|u| = 0}`) and `|∇|u||² ≤ ∑ |∇uᵢ|²`;
* scalar consequences: `|u|`, `u⁺`, `u⁻`, truncations at any level, affine rescaling.

The canonical bundle is `DGPS.Analysis.weak_contractions_products_and_norm_chain`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

namespace DGPS

variable {d : ℕ}

theorem coordPartial_mul {v φ : Torus d → ℝ} (hv : IsSmoothPeriodic v)
    (hφ : IsSmoothPeriodic φ) (j : Fin d) (y : Torus d) :
    coordPartial j (fun x => v x * φ x) y
      = v y * coordPartial j φ y + coordPartial j v y * φ y := by
  have hv1 : DifferentiableAt ℝ (v ∘ SharpLSI.liftT) (SharpLSI.secT y) :=
    (hv.differentiable (by simp)) _
  have hφ1 : DifferentiableAt ℝ (φ ∘ SharpLSI.liftT) (SharpLSI.secT y) :=
    (hφ.differentiable (by simp)) _
  have : ((fun x => v x * φ x) ∘ SharpLSI.liftT) =
      fun x => (v ∘ SharpLSI.liftT) x * (φ ∘ SharpLSI.liftT) x := rfl
  unfold coordPartial
  rw [this, fderiv_fun_mul hv1 hφ1]
  simp only [add_apply, smul_apply, smul_eq_mul,
    Function.comp_apply, SharpLSI.liftT_secT]
  ring

theorem isWeakGradient_const (c : ℝ) : IsWeakGradient (fun _ : Torus d => c) (fun _ => 0) where
  memLp := memLp_const c
  memLp_grad := memLp_const 0
  ibp φ hφ j := by
    have h := integral_mul_coordPartial_of_smooth (v := fun _ => (1:ℝ)) (φ := φ)
      (contDiff_const) hφ j
    have h0 : ∀ x, coordPartial j (fun _ : Torus d => (1:ℝ)) x = 0 := by
      intro x
      unfold coordPartial
      have : ((fun _ : Torus d => (1:ℝ)) ∘ torusLift) = fun _ => (1:ℝ) := rfl
      rw [this, fderiv_fun_const]; rfl
    simp only [h0, zero_mul, integral_zero, neg_zero, one_mul] at h
    simp only [PiLp.zero_apply, zero_mul, integral_zero, neg_zero]
    rw [integral_const_mul, h, mul_zero]

theorem tendsto_lintegral_moll_sub {f : Torus d → ℝ} (hf : MemLp f 2 (haar d)) :
    Tendsto (fun n => ∫⁻ y, ‖SharpLSI.moll n f y - f y‖ₑ ∂haar d) atTop (𝓝 0) := by
  have := tendsto_eLpNorm_moll_sub (p := 1) le_rfl ENNReal.one_ne_top
    (hf.mono_exponent one_le_two)
  refine this.congr (fun n => ?_)
  exact eLpNorm_one_eq_lintegral_enorm
    (((memLp_moll n one_le_two ENNReal.ofNat_ne_top hf).aestronglyMeasurable).sub
      hf.aestronglyMeasurable)

/-- Bridge: a campaign weak gradient is a legacy weak gradient. -/
theorem IsWeakGradient.isWeakGrad {u : Torus d → ℝ} {g : Torus d → Tangent d}
    (h : IsWeakGradient u g) : SharpLSI.IsWeakGrad u (fun y k => g y k) := by
  have hu1 : Integrable u (haar d) := h.memLp.integrable one_le_two
  have hgj : ∀ k, MemLp (fun x => g x k) 2 (haar d) := memLp_coord h.memLp_grad
  have hpair : ∀ n, SharpLSI.IsWeakGrad (SharpLSI.moll n u)
      (fun y k => SharpLSI.moll n (fun x => g x k) y) := by
    intro n
    have hc := SharpLSI.isWeakGrad_of_contDiff
      ((SharpLSI.moll_comp_liftT_contDiff n hu1).of_le (by simp))
    convert hc using 1
    funext y k
    have := congrFun (coordPartial_moll h n k) y
    rw [← this]; rfl
  have hint : ∀ n, Integrable (SharpLSI.moll n u) (haar d) := fun n =>
    (memLp_moll n one_le_two ENNReal.ofNat_ne_top h.memLp).integrable one_le_two
  have hinti : ∀ n k, Integrable (fun y => SharpLSI.moll n (fun x => g x k) y) (haar d) :=
    fun n k => (memLp_moll n one_le_two ENNReal.ofNat_ne_top (hgj k)).integrable one_le_two
  refine SharpLSI.isWeakGrad_of_tendsto hpair hint hinti hu1
    (fun k => (hgj k).integrable one_le_two) ?_ ?_
  · exact tendsto_lintegral_moll_sub h.memLp
  · intro k
    exact tendsto_lintegral_moll_sub (hgj k)

/-- `∇u = 0` a.e. on the level set `{u = M}`. -/
theorem IsWeakGradient.ae_grad_eq_zero {u : Torus d → ℝ} {g : Torus d → Tangent d}
    (h : IsWeakGradient u g) (M : ℝ) : ∀ᵐ x ∂haar d, u x = M → g x = 0 := by
  have hu1 : Integrable u (haar d) := h.memLp.integrable one_le_two
  have hgj : ∀ k, MemLp (fun x => g x k) 2 (haar d) := memLp_coord h.memLp_grad
  have := SharpLSI.ae_grad_eq_zero_of_eq h.isWeakGrad hu1
    (fun k => (hgj k).integrable one_le_two) M
  filter_upwards [this] with x hx hux
  ext k
  simpa using hx hux k


/-! ### Pairing and closure in `L¹` -/

theorem integrable_mul_top {a b : Torus d → ℝ} (ha : MemLp a ∞ (haar d))
    (hb : MemLp b ∞ (haar d)) : Integrable (fun x => a x * b x) (haar d) :=
  integrable_mul_of_memLp_two (ha.mono_exponent le_top) hb

theorem ae_norm_le_of_memLp_top {E : Type*} [NormedAddCommGroup E] {ψ : Torus d → E} (hψ : MemLp ψ ∞ (haar d)) :
    ∃ C : ℝ, ∀ᵐ x ∂haar d, ‖ψ x‖ ≤ C := by
  refine ⟨(eLpNorm ψ ∞ (haar d)).toReal, ?_⟩
  filter_upwards [enorm_ae_le_eLpNormEssSup ψ (haar d)] with x hx
  rw [← eLpNorm_exponent_top hψ.aestronglyMeasurable] at hx
  have := ENNReal.toReal_mono hψ.eLpNorm_ne_top hx
  simpa using this

theorem tendsto_integral_mul_of_L1 {F : ℕ → Torus d → ℝ} {f ψ : Torus d → ℝ}
    (hF : ∀ n, Integrable (F n) (haar d)) (hf : Integrable f (haar d))
    (hψ : MemLp ψ ∞ (haar d))
    (h : Tendsto (fun n => ∫⁻ y, ‖F n y - f y‖ₑ ∂haar d) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, F n x * ψ x ∂haar d) atTop (𝓝 (∫ x, f x * ψ x ∂haar d)) := by
  obtain ⟨C, hC⟩ := ae_norm_le_of_memLp_top hψ
  have hbound : ∀ n, ‖(∫ x, F n x * ψ x ∂haar d) - ∫ x, f x * ψ x ∂haar d‖
      ≤ (∫⁻ y, ‖F n y - f y‖ₑ ∂haar d).toReal * C := by
    intro n
    have e := integral_sub ((hF n).mul_of_top_left hψ) (hf.mul_of_top_left hψ)
    simp only [Pi.mul_apply] at e
    rw [← e]
    simp_rw [← sub_mul]
    have hint : Integrable (fun x => ‖F n x - f x‖ * C) (haar d) :=
      ((hF n).sub hf).norm.mul_const C
    calc ‖∫ x, (F n x - f x) * ψ x ∂haar d‖
        ≤ ∫ x, ‖F n x - f x‖ * C ∂haar d := by
          refine norm_integral_le_of_norm_le hint ?_
          filter_upwards [hC] with x hx
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left hx (norm_nonneg _)
      _ = (∫⁻ y, ‖F n y - f y‖ₑ ∂haar d).toReal * C := by
          have := integral_norm_eq_lintegral_enorm (μ := haar d)
            ((hF n).sub hf).aestronglyMeasurable
          simp only [Pi.sub_apply] at this
          rw [integral_mul_const, this]
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun n => norm_nonneg _) hbound ?_
  have : Tendsto (fun n => (∫⁻ y, ‖F n y - f y‖ₑ ∂haar d).toReal) atTop (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
    rwa [ENNReal.toReal_zero] at this
  simpa using this.mul_const C

/-- Closure of the weak gradient under `L¹` convergence of the function and the gradient
components. -/
theorem IsWeakGradient.of_tendsto_L1 {U : ℕ → Torus d → ℝ} {G : ℕ → Torus d → Tangent d}
    {u : Torus d → ℝ} {g : Torus d → Tangent d}
    (hu : MemLp u 2 (haar d)) (hg : MemLp g 2 (haar d))
    (hU : ∀ n, IsWeakGradient (U n) (G n))
    (h1 : Tendsto (fun n => ∫⁻ y, ‖U n y - u y‖ₑ ∂haar d) atTop (𝓝 0))
    (h2 : ∀ j, Tendsto (fun n => ∫⁻ y, ‖G n y j - g y j‖ₑ ∂haar d) atTop (𝓝 0)) :
    IsWeakGradient u g where
  memLp := hu
  memLp_grad := hg
  ibp φ hφ j := by
    have t1 := tendsto_integral_mul_of_L1 (fun n => (hU n).memLp.integrable one_le_two)
      (hu.integrable one_le_two) (hφ.memLp_top_coordPartial j) h1
    have t2 := tendsto_integral_mul_of_L1 (F := fun n y => G n y j)
      (fun n => (memLp_coord (hU n).memLp_grad j).integrable one_le_two)
      ((memLp_coord hg j).integrable one_le_two) hφ.memLp_top (h2 j)
    have t3 := (t2.neg).congr (fun n => ((hU n).ibp φ hφ j).symm)
    exact (tendsto_nhds_unique t3 t1).symm


/-! ### Products with bounded functions -/

theorem memLp_smul_top {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a : Torus d → ℝ} {b : Torus d → E}
    (ha : MemLp a ∞ (haar d)) (hb : MemLp b 2 (haar d)) :
    MemLp (fun x => a x • b x) 2 (haar d) := by
  obtain ⟨C, hC⟩ := ae_norm_le_of_memLp_top ha
  refine hb.of_le_mul (c := C) (ha.aestronglyMeasurable.smul hb.aestronglyMeasurable) ?_
  filter_upwards [hC] with x hx
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)

theorem memLp_mul_top {a b : Torus d → ℝ} (ha : MemLp a ∞ (haar d)) (hb : MemLp b 2 (haar d)) :
    MemLp (fun x => b x * a x) 2 (haar d) := by
  have := memLp_smul_top ha hb
  simpa [mul_comm] using this

theorem lintegral_mul_sub_le {a b w : Torus d → ℝ} {C : ℝ} (hC : ∀ᵐ x ∂haar d, ‖w x‖ ≤ C) :
    ∫⁻ y, ‖a y * w y - b y * w y‖ₑ ∂haar d
      ≤ ENNReal.ofReal C * ∫⁻ y, ‖a y - b y‖ₑ ∂haar d := by
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono_ae ?_
  filter_upwards [hC] with y hy
  rw [← sub_mul, enorm_mul, mul_comm]
  gcongr
  rw [← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal hy

theorem tendsto_zero_of_le_two {a b f : ℕ → ℝ≥0∞} {C C' : ℝ}
    (ha : Tendsto a atTop (𝓝 0)) (hb : Tendsto b atTop (𝓝 0))
    (hf : ∀ n, f n ≤ ENNReal.ofReal C * a n + ENNReal.ofReal C' * b n) :
    Tendsto f atTop (𝓝 0) := by
  have h1 := ENNReal.Tendsto.const_mul ha (Or.inr (ENNReal.ofReal_ne_top (r := C)))
  have h2 := ENNReal.Tendsto.const_mul hb (Or.inr (ENNReal.ofReal_ne_top (r := C')))
  have := h1.add h2
  simp only [mul_zero, add_zero] at this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds this (fun n => zero_le) hf

/-- Product rule with a smooth periodic factor. -/
theorem IsWeakGradient.mul_smooth {v w : Torus d → ℝ} {h : Torus d → Tangent d}
    (hv : IsSmoothPeriodic v) (hw : IsWeakGradientLp ∞ w h) :
    IsWeakGradient (fun x => v x * w x) (fun x => w x • smoothGrad v x + v x • h x) where
  memLp := by
    have := memLp_mul_top (a := w) hw.memLp (hv.memLp_top.mono_exponent le_top)
    simpa [mul_comm] using this
  memLp_grad := by
    have h2 : MemLp h 2 (haar d) := hw.memLp_grad.mono_exponent le_top
    exact (memLp_smul_top hw.memLp (hv.isWeakGradient.memLp_grad)).add
      (memLp_smul_top hv.memLp_top h2)
  ibp φ hφ j := by
    have hvφ : IsSmoothPeriodic (fun x => v x * φ x) := hv.mul hφ
    have e1 := hw.ibp _ hvφ j
    have hwt := hw.memLp
    have hhj : MemLp (fun x => h x j) ∞ (haar d) := memLp_coord_of_memLp hw.memLp_grad j
    have s1 : IsSmoothPeriodic (fun x => v x * coordPartial j φ x) :=
      hv.mul (hφ.isSmoothPeriodic_coordPartial j)
    have s2 : IsSmoothPeriodic (fun x => coordPartial j v x * φ x) :=
      (hv.isSmoothPeriodic_coordPartial j).mul hφ
    have i1 := integrable_mul_top hwt s1.memLp_top
    have i2 := integrable_mul_top hwt s2.memLp_top
    have i3 := integrable_mul_top hhj hvφ.memLp_top
    simp_rw [coordPartial_mul hv hφ, mul_add] at e1
    rw [integral_add i1 i2] at e1
    have eL : (fun x => v x * w x * coordPartial j φ x)
        = fun x => w x * (v x * coordPartial j φ x) := by funext x; ring
    have eR : (fun x => (w x • smoothGrad v x + v x • h x) j * φ x)
        = fun x => w x * (coordPartial j v x * φ x) + h x j * (v x * φ x) := by
      funext x; simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, smoothGrad_apply]; ring
    rw [eL, eR, integral_add i2 i3]
    linarith

/-- Weak product rule with a `W^{1,∞}` factor. -/
theorem IsWeakGradient.mul_W1infty {u w : Torus d → ℝ} {g h : Torus d → Tangent d}
    (hu : IsWeakGradient u g) (hw : IsWeakGradientLp ∞ w h) :
    IsWeakGradient (fun x => u x * w x) (fun x => w x • g x + u x • h x) := by
  have hu1 : Integrable u (haar d) := hu.memLp.integrable one_le_two
  obtain ⟨C, hC⟩ := ae_norm_le_of_memLp_top hw.memLp
  obtain ⟨C', hC'⟩ := ae_norm_le_of_memLp_top hw.memLp_grad
  have hconv1 : Tendsto (fun n => ∫⁻ y, ‖SharpLSI.moll n u y - u y‖ₑ ∂haar d) atTop (𝓝 0) :=
    tendsto_lintegral_moll_sub hu.memLp
  have hgj : ∀ k, MemLp (fun x => g x k) 2 (haar d) := memLp_coord hu.memLp_grad
  have hum : MemLp (fun x => u x • h x) 2 (haar d) := by
    refine hu.memLp.of_le_mul (c := C') (hu.memLp.aestronglyMeasurable.smul
      hw.memLp_grad.aestronglyMeasurable) ?_
    filter_upwards [hC'] with x hx
    rw [norm_smul, mul_comm]
    exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)
  refine IsWeakGradient.of_tendsto_L1 (U := fun n x => SharpLSI.moll n u x * w x)
    (G := fun n x => w x • smoothGrad (SharpLSI.moll n u) x + SharpLSI.moll n u x • h x)
    (memLp_mul_top hw.memLp hu.memLp)
    ((memLp_smul_top hw.memLp hu.memLp_grad).add hum)
    (fun n => IsWeakGradient.mul_smooth (isSmoothPeriodic_moll n hu1) hw) ?_ ?_
  · refine tendsto_zero_of_le_two (C := C) (C' := 0) hconv1 tendsto_const_nhds
      (b := fun _ => 0) (fun n => ?_)
    exact (lintegral_mul_sub_le (a := SharpLSI.moll n u) (b := u) hC).trans (by simp)
  · intro j
    refine tendsto_zero_of_le_two (C := C) (C' := C')
      (tendsto_lintegral_moll_sub (hgj j)) hconv1 (fun n => ?_)
    have hmeas1 : AEMeasurable (fun y => ‖SharpLSI.moll n (fun x => g x j) y - g y j‖ₑ)
        (haar d) :=
      (((memLp_moll n one_le_two ENNReal.ofNat_ne_top (hgj j)).aestronglyMeasurable).sub
        (hgj j).aestronglyMeasurable).enorm
    calc ∫⁻ y, ‖w y * smoothGrad (SharpLSI.moll n u) y j + SharpLSI.moll n u y * h y j
            - (w y * g y j + u y * h y j)‖ₑ ∂haar d
        ≤ ∫⁻ y, (ENNReal.ofReal C * ‖SharpLSI.moll n (fun x => g x j) y - g y j‖ₑ
            + ENNReal.ofReal C' * ‖SharpLSI.moll n u y - u y‖ₑ) ∂haar d := by
          refine lintegral_mono_ae ?_
          filter_upwards [hC, hC'] with y hy hy'
          have e : w y * smoothGrad (SharpLSI.moll n u) y j + SharpLSI.moll n u y * h y j
              - (w y * g y j + u y * h y j)
              = w y * (SharpLSI.moll n (fun x => g x j) y - g y j)
                + (SharpLSI.moll n u y - u y) * h y j := by
            rw [smoothGrad_apply, congrFun (coordPartial_moll hu n j) y]; ring
          rw [e]
          refine (enorm_add_le _ _).trans ?_
          rw [enorm_mul, enorm_mul]
          have hw1 : ‖w y‖ₑ ≤ ENNReal.ofReal C := by
            rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal hy
          have hh1 : ‖h y j‖ₑ ≤ ENNReal.ofReal C' := by
            rw [← ofReal_norm]
            exact ENNReal.ofReal_le_ofReal ((PiLp.norm_apply_le (h y) j).trans hy')
          exact add_le_add (by gcongr) (by rw [mul_comm]; gcongr)
      _ = _ := by
          rw [lintegral_add_left' (hmeas1.const_mul _), lintegral_const_mul' _ _
            ENNReal.ofReal_ne_top, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

/-! ### Smoothed Euclidean norm -/

/-- Smoothed Euclidean norm `√(ε + ∑ vᵢ²)`. -/
noncomputable def sqrtSum {ι : Type*} [Fintype ι] (ε : ℝ) (v : ι → Torus d → ℝ)
    (x : Torus d) : ℝ := √(ε + ∑ i, v i x ^ 2)

theorem sqrtSum_pos {ι : Type*} [Fintype ι] {ε : ℝ} (hε : 0 < ε) (v : ι → Torus d → ℝ)
    (x : Torus d) : 0 < sqrtSum ε v x :=
  Real.sqrt_pos.2 (by have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => sq_nonneg (v i x)); linarith)

theorem isSmoothPeriodic_sqrtSum {ι : Type*} [Fintype ι] {ε : ℝ} (hε : 0 < ε)
    {v : ι → Torus d → ℝ} (hv : ∀ i, IsSmoothPeriodic (v i)) :
    IsSmoothPeriodic (sqrtSum ε v) := by
  unfold IsSmoothPeriodic at *
  have : (sqrtSum ε v ∘ torusLift) = fun y => √(ε + ∑ i, ((v i) ∘ torusLift) y ^ 2) := rfl
  rw [this]
  refine ContDiff.sqrt ?_ (fun y => ?_)
  · exact contDiff_const.add (ContDiff.sum fun i _ => (hv i).pow 2)
  · have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => sq_nonneg (((v i) ∘ torusLift) y))
    linarith

theorem coordPartial_sqrtSum {ι : Type*} [Fintype ι] {ε : ℝ} (hε : 0 < ε)
    {v : ι → Torus d → ℝ} (hv : ∀ i, IsSmoothPeriodic (v i)) (j : Fin d) (y : Torus d) :
    coordPartial j (sqrtSum ε v) y
      = (∑ i, v i y * coordPartial j (v i) y) / sqrtSum ε v y := by
  have hd : ∀ i, HasFDerivAt ((v i) ∘ SharpLSI.liftT)
      (fderiv ℝ ((v i) ∘ SharpLSI.liftT) (SharpLSI.secT y)) (SharpLSI.secT y) :=
    fun i => ((hv i).differentiable (by simp) _).hasFDerivAt
  have h2 := HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ => (hd i).pow 2)
  have h3 := (h2.const_add ε)
  have hpos : (ε + ∑ i, ((v i) ∘ SharpLSI.liftT) (SharpLSI.secT y) ^ 2) ≠ 0 := by
    have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) =>
      sq_nonneg (((v i) ∘ SharpLSI.liftT) (SharpLSI.secT y)))
    linarith
  have h4 := h3.sqrt hpos
  unfold coordPartial
  have e : (sqrtSum ε v ∘ SharpLSI.liftT) =
      fun z => √(ε + ∑ i, ((v i) ∘ SharpLSI.liftT) z ^ 2) := rfl
  rw [e, h4.fderiv]
  simp only [smul_apply, sum_apply,
    smul_apply, smul_eq_mul, Function.comp_apply, SharpLSI.liftT_secT]
  unfold sqrtSum
  have hs : (0:ℝ) < √(ε + ∑ i, v i y ^ 2) := by
    have := sqrtSum_pos hε v y
    exact this
  rw [one_div, mul_comm (2 * _)⁻¹ _] ; rw [div_eq_inv_mul]
  have : ∀ x, (2 • v x y ^ (2 - 1) * (fderiv ℝ (v x ∘ SharpLSI.liftT) (SharpLSI.secT y)) (Pi.single j 1))
      = 2 * (v x y * (fderiv ℝ (v x ∘ torusLift) (SharpLSI.secT y)) (Pi.single j 1)) := by
    intro x; simp; ring
  simp_rw [this, ← Finset.mul_sum]
  field_simp



theorem sqrt_sum_sq_le_sum_abs {ι : Type*} [Fintype ι] (w : ι → ℝ) :
    √(∑ i, w i ^ 2) ≤ ∑ i, |w i| := by
  refine Real.sqrt_le_iff.2 ⟨Finset.sum_nonneg (fun i _ => abs_nonneg _), ?_⟩
  have := Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ) (f := fun i => |w i|)
    (fun i _ => abs_nonneg _)
  simpa [sq_abs] using this

theorem abs_sqrt_sum_sq_sub_le {ι : Type*} [Fintype ι] (a b : ι → ℝ) :
    |√(∑ i, a i ^ 2) - √(∑ i, b i ^ 2)| ≤ ∑ i, |a i - b i| := by
  have h : ∀ w : ι → ℝ, √(∑ i, w i ^ 2) = ‖(WithLp.toLp 2 w : EuclideanSpace ℝ ι)‖ := by
    intro w
    rw [EuclideanSpace.norm_eq]
    simp [sq_abs]
  rw [h, h]
  refine (abs_norm_sub_norm_le _ _).trans ?_
  have : (WithLp.toLp 2 a : EuclideanSpace ℝ ι) - WithLp.toLp 2 b
      = WithLp.toLp 2 (fun i => a i - b i) := rfl
  rw [this, ← h]
  refine (sqrt_sum_sq_le_sum_abs _)

theorem sqrt_add_le_sqrt_add_sqrt {ε A : ℝ} (hε : 0 ≤ ε) (hA : 0 ≤ A) :
    √(ε + A) ≤ √ε + √A := by
  refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
  have h1 := Real.sq_sqrt hε
  have h2 := Real.sq_sqrt hA
  nlinarith [Real.sqrt_nonneg ε, Real.sqrt_nonneg A, mul_nonneg (Real.sqrt_nonneg ε) (Real.sqrt_nonneg A)]

theorem abs_sqrtSum_sub_le {ι : Type*} [Fintype ι] {ε : ℝ} (hε : 0 < ε) (V u : ι → Torus d → ℝ)
    (x : Torus d) :
    |sqrtSum ε V x - √(∑ i, u i x ^ 2)| ≤ √ε + ∑ i, |V i x - u i x| := by
  have hA : 0 ≤ ∑ i, V i x ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have h1 := sqrt_add_le_sqrt_add_sqrt hε.le hA
  have h2 : √(∑ i, V i x ^ 2) ≤ √(ε + ∑ i, V i x ^ 2) :=
    Real.sqrt_le_sqrt (by linarith)
  have h3 := abs_sqrt_sum_sq_sub_le (fun i => V i x) (fun i => u i x)
  unfold sqrtSum
  rw [abs_le] at h3 ⊢
  constructor <;> linarith [h3.1, h3.2]

theorem abs_le_sqrtSum {ι : Type*} [Fintype ι] {ε : ℝ} (hε : 0 < ε) (V : ι → Torus d → ℝ)
    (x : Torus d) (i : ι) : |V i x| ≤ sqrtSum ε V x := by
  unfold sqrtSum
  refine Real.abs_le_sqrt ?_
  have := Finset.single_le_sum (f := fun i => V i x ^ 2) (fun i _ => sq_nonneg _)
    (Finset.mem_univ i)
  linarith

theorem abs_div_le_one {a c : ℝ} (h : |a| ≤ c) : |a / c| ≤ 1 := by
  rcases (abs_nonneg a).trans h |>.eq_or_lt with h0 | h0
  · rw [← h0] at h; have : a = 0 := abs_nonpos_iff.1 h
    simp [this]
  · rw [abs_div, abs_of_pos h0]
    exact (div_le_one h0).2 h

theorem smoothGrad_sqrtSum {ι : Type*} [Fintype ι] {ε : ℝ} (hε : 0 < ε)
    {V : ι → Torus d → ℝ} (hV : ∀ i, IsSmoothPeriodic (V i)) (y : Torus d) :
    smoothGrad (sqrtSum ε V) y = ∑ i, (V i y / sqrtSum ε V y) • smoothGrad (V i) y := by
  ext j
  rw [smoothGrad_apply, coordPartial_sqrtSum hε hV]
  simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smoothGrad_apply, smul_eq_mul]
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ring


/-- Euclidean norm of a finite vector of functions. -/
noncomputable def eNorm {ι : Type*} [Fintype ι] (u : ι → Torus d → ℝ) (x : Torus d) : ℝ :=
  √(∑ i, u i x ^ 2)

/-- The chain-rule gradient `(u·∇u)/|u|` (zero where `|u| = 0`, by `inv_zero`). -/
noncomputable def eNormGrad {ι : Type*} [Fintype ι] (u : ι → Torus d → ℝ)
    (g : ι → Torus d → Tangent d) (x : Torus d) : Tangent d :=
  (eNorm u x)⁻¹ • ∑ i, u i x • g i x

theorem eNorm_nonneg {ι : Type*} [Fintype ι] (u : ι → Torus d → ℝ) (x : Torus d) :
    0 ≤ eNorm u x := Real.sqrt_nonneg _

theorem abs_le_eNorm {ι : Type*} [Fintype ι] (u : ι → Torus d → ℝ) (x : Torus d) (i : ι) :
    |u i x| ≤ eNorm u x := by
  unfold eNorm
  refine Real.abs_le_sqrt ?_
  exact Finset.single_le_sum (f := fun i => u i x ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ i)

theorem eNormGrad_apply {ι : Type*} [Fintype ι] (u : ι → Torus d → ℝ)
    (g : ι → Torus d → Tangent d) (x : Torus d) (j : Fin d) :
    eNormGrad u g x j = ∑ i, (u i x / eNorm u x) * g i x j := by
  unfold eNormGrad
  simp only [PiLp.smul_apply, WithLp.ofLp_sum, Finset.sum_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ring

theorem norm_eNormGrad_le {ι : Type*} [Fintype ι] (u : ι → Torus d → ℝ)
    (g : ι → Torus d → Tangent d) (x : Torus d) :
    ‖eNormGrad u g x‖ ^ 2 ≤ ∑ i, ‖g i x‖ ^ 2 := by
  have hS : 0 ≤ ∑ i, ‖g i x‖ ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  by_cases h0 : eNorm u x = 0
  · simp [eNormGrad, h0, hS]
  · have hpos : 0 < eNorm u x := lt_of_le_of_ne (eNorm_nonneg u x) (Ne.symm h0)
    have h1 : ‖∑ i, u i x • g i x‖ ≤ eNorm u x * √(∑ i, ‖g i x‖ ^ 2) := by
      calc ‖∑ i, u i x • g i x‖ ≤ ∑ i, ‖u i x • g i x‖ := norm_sum_le _ _
        _ = ∑ i, |u i x| * ‖g i x‖ := by simp [norm_smul]
        _ ≤ √(∑ i, |u i x| ^ 2) * √(∑ i, ‖g i x‖ ^ 2) :=
            Real.sum_mul_le_sqrt_mul_sqrt _ _ _
        _ = eNorm u x * √(∑ i, ‖g i x‖ ^ 2) := by simp [eNorm, sq_abs]
    have h2 : ‖eNormGrad u g x‖ ≤ √(∑ i, ‖g i x‖ ^ 2) := by
      unfold eNormGrad
      rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hpos, inv_mul_le_iff₀ hpos]
      exact h1
    calc ‖eNormGrad u g x‖ ^ 2 ≤ (√(∑ i, ‖g i x‖ ^ 2)) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h2 2
      _ = _ := Real.sq_sqrt hS

theorem norm_eNormGrad_le_sum {ι : Type*} [Fintype ι] (u : ι → Torus d → ℝ)
    (g : ι → Torus d → Tangent d) (x : Torus d) :
    ‖eNormGrad u g x‖ ≤ ∑ i, ‖g i x‖ := by
  calc ‖eNormGrad u g x‖ = √(‖eNormGrad u g x‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ √(∑ i, ‖g i x‖ ^ 2) := Real.sqrt_le_sqrt (norm_eNormGrad_le u g x)
    _ ≤ ∑ i, |‖g i x‖| := sqrt_sum_sq_le_sum_abs _
    _ = _ := by simp

theorem tendsto_lintegral_of_eLpNorm_two {F : ℕ → Torus d → ℝ} {f : Torus d → ℝ}
    (hF : ∀ n, AEStronglyMeasurable (F n) (haar d)) (hf : AEStronglyMeasurable f (haar d))
    (h : Tendsto (fun n => eLpNorm (fun x => F n x - f x) 2 (haar d)) atTop (𝓝 0)) :
    Tendsto (fun n => ∫⁻ y, ‖F n y - f y‖ₑ ∂haar d) atTop (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun _ => zero_le) ?_
  intro n
  have e := eLpNorm_one_eq_lintegral_enorm ((hF n).sub hf)
  have e2 := eLpNorm_le_eLpNorm_of_exponent_le (μ := haar d) (f := F n - f) one_le_two
  show ∫⁻ y, ‖F n y - f y‖ₑ ∂haar d ≤ eLpNorm (F n - f) 2 (haar d)
  exact e ▸ e2


theorem tendsto_sqrt_inv_succ : Tendsto (fun k : ℕ => √(1 / ((k : ℝ) + 1))) atTop (𝓝 0) := by
  have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have h2 := (Real.continuous_sqrt.tendsto 0).comp h
  rw [Real.sqrt_zero] at h2
  exact h2

theorem IsWeakGradient.norm_vec {ι : Type*} [Fintype ι] {u : ι → Torus d → ℝ}
    {g : ι → Torus d → Tangent d} (hu : ∀ i, IsWeakGradient (u i) (g i)) :
    IsWeakGradient (eNorm u) (eNormGrad u g) := by
  classical
  have hum : ∀ i, AEStronglyMeasurable (u i) (haar d) := fun i => (hu i).memLp.aestronglyMeasurable
  have hnrm_meas : AEStronglyMeasurable (eNorm u) (haar d) :=
    Real.continuous_sqrt.comp_aestronglyMeasurable
      (Finset.aestronglyMeasurable_fun_sum _ fun i _ =>
        (continuous_pow 2).comp_aestronglyMeasurable (hum i))
  have hnrm_L2 : MemLp (eNorm u) 2 (haar d) := by
    have hs : MemLp (fun x => ∑ i, ‖u i x‖) 2 (haar d) :=
      memLp_finsetSum _ (fun i _ => (hu i).memLp.norm)
    refine hs.mono' hnrm_meas (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (eNorm_nonneg u x)]
    exact (sqrt_sum_sq_le_sum_abs (fun i => u i x)).trans (by simp)
  have hgm : ∀ i, AEStronglyMeasurable (g i) (haar d) := fun i => (hu i).memLp_grad.aestronglyMeasurable
  have hG_L2 : MemLp (eNormGrad u g) 2 (haar d) := by
    have hs : MemLp (fun x => ∑ i, ‖g i x‖) 2 (haar d) :=
      memLp_finsetSum _ (fun i _ => (hu i).memLp_grad.norm)
    refine hs.mono' ?_ (Eventually.of_forall fun x => ?_)
    · unfold eNormGrad
      exact (hnrm_meas.aemeasurable.inv.aestronglyMeasurable).smul
        (Finset.aestronglyMeasurable_fun_sum _ fun i _ => (hum i).smul (hgm i))
    · exact norm_eNormGrad_le_sum u g x
  choose V hVs hVw hV2 hVg using fun i => exists_smooth_tendsto_H1 (hu i)
  have hVm : ∀ i n, AEStronglyMeasurable (V i n) (haar d) :=
    fun i n => (hVw i n).memLp.aestronglyMeasurable
  have hL1u : ∀ i, Tendsto (fun n => ∫⁻ y, ‖V i n y - u i y‖ₑ ∂haar d) atTop (𝓝 0) :=
    fun i => tendsto_lintegral_of_eLpNorm_two (hVm i) (hum i) (hV2 i)
  have hgjm : ∀ i j, AEStronglyMeasurable (fun x => g i x j) (haar d) :=
    fun i j => (memLp_coord (hu i).memLp_grad j).aestronglyMeasurable
  have hL1g : ∀ i j, Tendsto (fun n => ∫⁻ y, ‖smoothGrad (V i n) y j - g i y j‖ₑ ∂haar d)
      atTop (𝓝 0) := fun i j =>
    tendsto_lintegral_of_eLpNorm_two
      (fun n => (memLp_coord (hVw i n).memLp_grad j).aestronglyMeasurable) (hgjm i j) (hVg i j)
  -- a.e. convergent subsequence
  set D : ℕ → Torus d → ℝ := fun n x => ∑ i, |V i n x - u i x| with hD
  have hDm : ∀ n, AEStronglyMeasurable (D n) (haar d) := fun n =>
    Finset.aestronglyMeasurable_fun_sum _ fun i _ => ((hVm i n).sub (hum i)).norm
  have hDL1 : Tendsto (fun n => ∫⁻ y, ‖D n y - (0 : Torus d → ℝ) y‖ₑ ∂haar d) atTop (𝓝 0) := by
    have hsum : Tendsto (fun n => ∑ i, ∫⁻ y, ‖V i n y - u i y‖ₑ ∂haar d) atTop (𝓝 0) := by
      have := tendsto_finsetSum (Finset.univ : Finset ι) (fun i _ => hL1u i)
      simpa using this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
      (fun _ => zero_le) (fun n => ?_)
    calc ∫⁻ y, ‖D n y - (0 : Torus d → ℝ) y‖ₑ ∂haar d
        ≤ ∫⁻ y, ∑ i, ‖V i n y - u i y‖ₑ ∂haar d := by
          refine lintegral_mono (fun y => ?_)
          simp only [Pi.zero_apply, sub_zero]
          calc ‖D n y‖ₑ ≤ ∑ i, ‖|V i n y - u i y|‖ₑ := enorm_sum_le _ _
            _ = _ := by simp
      _ = ∑ i, ∫⁻ y, ‖V i n y - u i y‖ₑ ∂haar d :=
          lintegral_finsetSum' _ (fun i _ => (((hVm i n).sub (hum i)).enorm))
  obtain ⟨ns, hns, hae⟩ := SharpLSI.exists_subseq_ae_of_tendsto_lintegral hDm
    aestronglyMeasurable_zero hDL1
  set ε : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1) with hεdef
  have hε : ∀ k, 0 < ε k := fun k => by simp only [hεdef]; positivity
  set s : ℕ → Torus d → ℝ := fun k => sqrtSum (ε k) (fun i => V i (ns k)) with hsdef
  have hWs : ∀ k i, IsSmoothPeriodic (V i (ns k)) := fun k i => hVs i (ns k)
  have hsS : ∀ k, IsSmoothPeriodic (s k) := fun k => isSmoothPeriodic_sqrtSum (hε k) (hWs k)
  have hsm : ∀ k, AEStronglyMeasurable (s k) (haar d) :=
    fun k => (hsS k).memLp_top.aestronglyMeasurable
  have hnsT := hns.tendsto_atTop
  have hε0 : Tendsto (fun k => √(ε k)) atTop (𝓝 0) := tendsto_sqrt_inv_succ
  have h1 : Tendsto (fun k => ∫⁻ y, ‖s k y - eNorm u y‖ₑ ∂haar d) atTop (𝓝 0) := by
    have hsum : Tendsto (fun k => ∑ i, ∫⁻ y, ‖V i (ns k) y - u i y‖ₑ ∂haar d) atTop (𝓝 0) := by
      have := tendsto_finsetSum (Finset.univ : Finset ι) (fun i _ => (hL1u i).comp hnsT)
      simpa using this
    have hc : Tendsto (fun k => ENNReal.ofReal (√(ε k))) atTop (𝓝 0) := by
      have := ENNReal.tendsto_ofReal hε0
      simpa using this
    have := hc.add hsum
    rw [add_zero] at this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds this
      (fun _ => zero_le) (fun k => ?_)
    calc ∫⁻ y, ‖s k y - eNorm u y‖ₑ ∂haar d
        ≤ ∫⁻ y, (ENNReal.ofReal (√(ε k)) + ∑ i, ‖V i (ns k) y - u i y‖ₑ) ∂haar d := by
          refine lintegral_mono (fun y => ?_)
          rw [← ofReal_norm, Real.norm_eq_abs]
          refine (ENNReal.ofReal_le_ofReal (abs_sqrtSum_sub_le (hε k) _ u y)).trans ?_
          rw [ENNReal.ofReal_add (Real.sqrt_nonneg _)
            (Finset.sum_nonneg fun i _ => abs_nonneg _),
            ENNReal.ofReal_sum_of_nonneg (fun i _ => abs_nonneg _)]
          exact le_of_eq (congrArg _ (Finset.sum_congr rfl fun i _ => by rw [← ofReal_norm, Real.norm_eq_abs]))
      _ = ENNReal.ofReal (√(ε k)) + ∑ i, ∫⁻ y, ‖V i (ns k) y - u i y‖ₑ ∂haar d := by
          rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
          refine congrArg _ (lintegral_finsetSum' _ ?_)
          intro i _
          exact ((hVm i (ns k)).sub (hum i)).enorm
  have hgrad : ∀ k y j, smoothGrad (s k) y j
      = ∑ i, V i (ns k) y / s k y * smoothGrad (V i (ns k)) y j := by
    intro k y j
    have := smoothGrad_sqrtSum (hε k) (hWs k) y
    show smoothGrad (sqrtSum (ε k) (fun i => V i (ns k))) y j = _
    rw [this]
    simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul]
    rfl
  have hae2 : ∀ᵐ y ∂haar d, (∀ i, Tendsto (fun k => V i (ns k) y) atTop (𝓝 (u i y))) ∧
      Tendsto (fun k => s k y) atTop (𝓝 (eNorm u y)) := by
    filter_upwards [hae] with y hy
    have hy' : Tendsto (fun k => D (ns k) y) atTop (𝓝 0) := by simpa using hy
    refine ⟨fun i => ?_, ?_⟩
    · rw [tendsto_iff_norm_sub_tendsto_zero]
      refine squeeze_zero (fun k => norm_nonneg _) (fun k => ?_) hy'
      rw [Real.norm_eq_abs]
      exact Finset.single_le_sum (f := fun i => |V i (ns k) y - u i y|)
        (fun i _ => abs_nonneg _) (Finset.mem_univ i)
    · rw [tendsto_iff_norm_sub_tendsto_zero]
      have := hε0.add hy'
      rw [add_zero] at this
      refine squeeze_zero (fun k => norm_nonneg _) (fun k => ?_) this
      rw [Real.norm_eq_abs]
      exact abs_sqrtSum_sub_le (hε k) _ u y
  have hzero : ∀ᵐ y ∂haar d, ∀ i, u i y = 0 → g i y = 0 :=
    ae_all_iff.2 fun i => (hu i).ae_grad_eq_zero 0
  have h2 : ∀ j, Tendsto (fun k => ∫⁻ y, ‖smoothGrad (s k) y j - eNormGrad u g y j‖ₑ ∂haar d)
      atTop (𝓝 0) := by
    intro j
    have hE2 : ∀ i, Tendsto (fun k => ∫⁻ y,
        ‖(V i (ns k) y / s k y - u i y / eNorm u y) * g i y j‖ₑ ∂haar d) atTop (𝓝 0) := by
      intro i
      have hgi : ∫⁻ y, ‖g i y j‖ₑ ∂haar d < ⊤ :=
        ((memLp_coord (hu i).memLp_grad j).integrable one_le_two).hasFiniteIntegral
      have hbd : ∀ k y, ‖(V i (ns k) y / s k y - u i y / eNorm u y) * g i y j‖ₑ
          ≤ 2 * ‖g i y j‖ₑ := by
        intro k y
        rw [enorm_mul]
        have ha : |V i (ns k) y / s k y| ≤ 1 :=
          abs_div_le_one (abs_le_sqrtSum (hε k) (fun i => V i (ns k)) y i)
        have hb : |u i y / eNorm u y| ≤ 1 := abs_div_le_one (abs_le_eNorm u y i)
        gcongr
        rw [← ofReal_norm, Real.norm_eq_abs]
        calc ENNReal.ofReal |V i (ns k) y / s k y - u i y / eNorm u y| ≤ ENNReal.ofReal 2 :=
              ENNReal.ofReal_le_ofReal (by linarith [abs_sub (V i (ns k) y / s k y) (u i y / eNorm u y)])
          _ = 2 := by simp
      have := tendsto_lintegral_of_dominated_convergence' (μ := haar d)
        (F := fun k y => ‖(V i (ns k) y / s k y - u i y / eNorm u y) * g i y j‖ₑ)
        (f := fun _ => (0 : ℝ≥0∞)) (bound := fun y => 2 * ‖g i y j‖ₑ)
        (fun k => ((((hVm i (ns k)).aemeasurable.div (hsm k).aemeasurable).sub
          ((hum i).aemeasurable.div hnrm_meas.aemeasurable)).mul (hgjm i j).aemeasurable).enorm)
        (fun k => Eventually.of_forall fun y => hbd k y)
        (by
          rw [lintegral_const_mul' _ _ (by norm_num)]
          exact ENNReal.mul_ne_top (by norm_num) hgi.ne)
        (by
          filter_upwards [hae2, hzero] with y hy hz
          obtain ⟨hV, hs⟩ := hy
          by_cases hn : eNorm u y = 0
          · have hu0 : u i y = 0 := abs_nonpos_iff.1 ((abs_le_eNorm u y i).trans hn.le)
            have hg0 : g i y j = 0 := by simp [hz i hu0]
            simp [hg0]
          · have hl := (((hV i).div hs hn).sub_const (u i y / eNorm u y)).mul_const (g i y j)
            simp only [sub_self, zero_mul] at hl
            have h3 := (continuous_enorm.tendsto (0 : ℝ)).comp hl
            rw [enorm_zero] at h3
            exact h3)
      simpa using this
    have hE1 : ∀ i, Tendsto (fun k => ∫⁻ y, ‖smoothGrad (V i (ns k)) y j - g i y j‖ₑ ∂haar d)
        atTop (𝓝 0) := fun i => (hL1g i j).comp hnsT
    have hsum : Tendsto (fun k => ∑ i, (∫⁻ y, ‖smoothGrad (V i (ns k)) y j - g i y j‖ₑ ∂haar d
        + ∫⁻ y, ‖(V i (ns k) y / s k y - u i y / eNorm u y) * g i y j‖ₑ ∂haar d))
        atTop (𝓝 0) := by
      have := tendsto_finsetSum (Finset.univ : Finset ι) (fun i _ => (hE1 i).add (hE2 i))
      simpa using this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
      (fun _ => zero_le) (fun k => ?_)
    have hE1m : ∀ i, AEMeasurable (fun y => ‖smoothGrad (V i (ns k)) y j - g i y j‖ₑ) (haar d) :=
      fun i => (((memLp_coord (hVw i (ns k)).memLp_grad j).aestronglyMeasurable).sub
        (hgjm i j)).enorm
    have hE2m : ∀ i, AEMeasurable (fun y =>
        ‖(V i (ns k) y / s k y - u i y / eNorm u y) * g i y j‖ₑ) (haar d) := fun i =>
      ((((hVm i (ns k)).aemeasurable.div (hsm k).aemeasurable).sub
        ((hum i).aemeasurable.div hnrm_meas.aemeasurable)).mul (hgjm i j).aemeasurable).enorm
    calc ∫⁻ y, ‖smoothGrad (s k) y j - eNormGrad u g y j‖ₑ ∂haar d
        ≤ ∫⁻ y, ∑ i, (‖smoothGrad (V i (ns k)) y j - g i y j‖ₑ
            + ‖(V i (ns k) y / s k y - u i y / eNorm u y) * g i y j‖ₑ) ∂haar d := by
          refine lintegral_mono (fun y => ?_)
          rw [hgrad, eNormGrad_apply, ← Finset.sum_sub_distrib]
          refine (enorm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => ?_))
          have e : V i (ns k) y / s k y * smoothGrad (V i (ns k)) y j
              - u i y / eNorm u y * g i y j
              = V i (ns k) y / s k y * (smoothGrad (V i (ns k)) y j - g i y j)
                + (V i (ns k) y / s k y - u i y / eNorm u y) * g i y j := by ring
          rw [e]
          refine (enorm_add_le _ _).trans (add_le_add ?_ le_rfl)
          rw [enorm_mul]
          have ha : ‖V i (ns k) y / s k y‖ₑ ≤ 1 := by
            rw [← ofReal_norm, Real.norm_eq_abs]
            calc ENNReal.ofReal |V i (ns k) y / s k y| ≤ ENNReal.ofReal 1 :=
                  ENNReal.ofReal_le_ofReal
                    (abs_div_le_one (abs_le_sqrtSum (hε k) (fun i => V i (ns k)) y i))
              _ = 1 := by simp
          calc ‖V i (ns k) y / s k y‖ₑ * ‖smoothGrad (V i (ns k)) y j - g i y j‖ₑ
              ≤ 1 * ‖smoothGrad (V i (ns k)) y j - g i y j‖ₑ := by gcongr
            _ = _ := one_mul _
      _ = ∑ i, (∫⁻ y, ‖smoothGrad (V i (ns k)) y j - g i y j‖ₑ ∂haar d
            + ∫⁻ y, ‖(V i (ns k) y / s k y - u i y / eNorm u y) * g i y j‖ₑ ∂haar d) := by
          refine (lintegral_finsetSum' _ (fun i _ => (hE1m i).add (hE2m i))).trans ?_
          refine Finset.sum_congr rfl (fun i _ => ?_)
          exact lintegral_add_left' (hE1m i) _
  exact IsWeakGradient.of_tendsto_L1 hnrm_L2 hG_L2 (fun k => (hsS k).isWeakGradient) h1 h2


/-! ### Scalar clauses from the vector clause with one component -/

theorem eNorm_unit (u : Torus d → ℝ) : eNorm (fun _ : Unit => u) = fun x => |u x| := by
  funext x
  simp [eNorm, Real.sqrt_sq_eq_abs]

/-- Chain-rule gradient of `|u|`. -/
theorem IsWeakGradient.abs {u : Torus d → ℝ} {g : Torus d → Tangent d}
    (hu : IsWeakGradient u g) :
    IsWeakGradient (fun x => |u x|)
      (fun x => if 0 < u x then g x else if u x < 0 then -g x else 0) := by
  have h := IsWeakGradient.norm_vec (u := fun _ : Unit => u) (g := fun _ => g) (fun _ => hu)
  rw [eNorm_unit] at h
  convert h using 1
  funext x
  rw [eNormGrad]
  simp only [eNorm_unit, Finset.univ_unique, Finset.sum_singleton]
  split_ifs with h1 h2
  · rw [abs_of_pos h1, smul_smul, inv_mul_cancel₀ h1.ne', one_smul]
  · have hne : u x ≠ 0 := h2.ne
    have e : (-u x)⁻¹ * u x = -1 := by rw [inv_neg, neg_mul, inv_mul_cancel₀ hne]
    rw [abs_of_neg h2, smul_smul, e, neg_one_smul]
  · have : u x = 0 := le_antisymm (not_lt.1 h1) (not_lt.1 h2)
    simp [this]


theorem IsWeakGradient.sub_const {u : Torus d → ℝ} {g : Torus d → Tangent d}
    (hu : IsWeakGradient u g) (c : ℝ) : IsWeakGradient (fun x => u x - c) g :=
  (hu.add (isWeakGradient_const (d := d) (-c))).congr_ae
    (Eventually.of_forall fun x => by simp [sub_eq_add_neg])
    (Eventually.of_forall fun x => by simp)

theorem IsWeakGradient.abs_sub {u : Torus d → ℝ} {g : Torus d → Tangent d}
    (hu : IsWeakGradient u g) (c : ℝ) :
    IsWeakGradient (fun x => |u x - c|)
      (fun x => if c < u x then g x else if u x < c then -g x else 0) := by
  simpa only [sub_pos, sub_neg] using (hu.sub_const c).abs

/-- Truncation from below: `max (u, c)`. -/
theorem IsWeakGradient.max_const {u : Torus d → ℝ} {g : Torus d → Tangent d}
    (hu : IsWeakGradient u g) (c : ℝ) :
    IsWeakGradient (fun x => max (u x) c) (fun x => if c < u x then g x else 0) := by
  have hA := hu.add (isWeakGradient_const (d := d) c)
  have hS := (hA.add (hu.abs_sub c)).smul (1 / 2)
  refine hS.congr_ae (Eventually.of_forall fun x => ?_) ?_
  · show 1 / 2 * ((u x + c) + |u x - c|) = max (u x) c
    rcases le_total (u x) c with h | h
    · rw [max_eq_right h, abs_of_nonpos (by linarith)]; ring
    · rw [max_eq_left h, abs_of_nonneg (by linarith)]; ring
  · filter_upwards [hu.ae_grad_eq_zero c] with x hx
    show (1 / 2 : ℝ) • ((g x + 0) + (if c < u x then g x else if u x < c then -g x else 0))
      = if c < u x then g x else 0
    rcases lt_trichotomy (u x) c with h | h | h
    · simp [h, not_lt.2 h.le]
    · simp [h, hx h]
    · simp [h]
      module

/-- Truncation from above: `min (u, c)`. -/
theorem IsWeakGradient.min_const {u : Torus d → ℝ} {g : Torus d → Tangent d}
    (hu : IsWeakGradient u g) (c : ℝ) :
    IsWeakGradient (fun x => min (u x) c) (fun x => if u x < c then g x else 0) := by
  have hA := hu.add (isWeakGradient_const (d := d) c)
  have hS := (hA.add ((hu.abs_sub c).smul (-1))).smul (1 / 2)
  refine hS.congr_ae (Eventually.of_forall fun x => ?_) ?_
  · show 1 / 2 * ((u x + c) + -1 * |u x - c|) = min (u x) c
    rcases le_total (u x) c with h | h
    · rw [min_eq_left h, abs_of_nonpos (by linarith)]; ring
    · rw [min_eq_right h, abs_of_nonneg (by linarith)]; ring
  · filter_upwards [hu.ae_grad_eq_zero c] with x hx
    show (1 / 2 : ℝ) • ((g x + 0) + (-1 : ℝ) • (if c < u x then g x else if u x < c then -g x else 0))
      = if u x < c then g x else 0
    rcases lt_trichotomy (u x) c with h | h | h
    · simp [h, not_lt.2 h.le]
      module
    · simp [h, hx h]
    · simp [h, not_lt.2 h.le]

theorem IsWeakGradient.posPart {u : Torus d → ℝ} {g : Torus d → Tangent d}
    (hu : IsWeakGradient u g) :
    IsWeakGradient (fun x => max (u x) 0) (fun x => if 0 < u x then g x else 0) :=
  hu.max_const 0

theorem IsWeakGradient.negPart {u : Torus d → ℝ} {g : Torus d → Tangent d}
    (hu : IsWeakGradient u g) :
    IsWeakGradient (fun x => max (-u x) 0) (fun x => if u x < 0 then -g x else 0) :=
  ((hu.smul (-1)).max_const 0).congr_ae (Eventually.of_forall fun x => by simp)
    (Eventually.of_forall fun x => by simp)

theorem IsWeakGradient.affine {u : Torus d → ℝ} {g : Torus d → Tangent d}
    (hu : IsWeakGradient u g) (a b : ℝ) :
    IsWeakGradient (fun x => a * u x + b) (fun x => a • g x) :=
  ((hu.smul a).add (isWeakGradient_const (d := d) b)).congr_ae
    (Eventually.of_forall fun x => rfl) (Eventually.of_forall fun x => by simp)

theorem integral_norm_sq_le_of_le {G g : Torus d → Tangent d} (hG : MemLp G 2 (haar d))
    (hg : MemLp g 2 (haar d)) (h : ∀ x, ‖G x‖ ≤ ‖g x‖) :
    ∫ x, ‖G x‖ ^ 2 ∂haar d ≤ ∫ x, ‖g x‖ ^ 2 ∂haar d := by
  refine integral_mono ((memLp_two_iff_integrable_sq_norm hG.aestronglyMeasurable).1 hG)
    ((memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).1 hg) (fun x => ?_)
  exact pow_le_pow_left₀ (norm_nonneg _) (h x) 2


theorem integral_eNormGrad_le {ι : Type*} [Fintype ι] {u : ι → Torus d → ℝ}
    {g : ι → Torus d → Tangent d} (hu : ∀ i, IsWeakGradient (u i) (g i)) :
    ∫ x, ‖eNormGrad u g x‖ ^ 2 ∂haar d ≤ ∑ i, ∫ x, ‖g i x‖ ^ 2 ∂haar d := by
  have hG := (IsWeakGradient.norm_vec hu).memLp_grad
  have hi : ∀ i, Integrable (fun x => ‖g i x‖ ^ 2) (haar d) := fun i =>
    (memLp_two_iff_integrable_sq_norm (hu i).memLp_grad.aestronglyMeasurable).1 (hu i).memLp_grad
  rw [← integral_finsetSum _ (fun i _ => hi i)]
  exact integral_mono
    ((memLp_two_iff_integrable_sq_norm hG.aestronglyMeasurable).1 hG)
    (integrable_finsetSum _ (fun i _ => hi i)) (fun x => norm_eNormGrad_le u g x)

end DGPS

namespace DGPS.Analysis

open DGPS MeasureTheory

/-- FOU003 canonical bundle. -/
theorem weak_contractions_products_and_norm_chain (d : ℕ) :
    -- bridge to the legacy weak gradient, and vanishing of the gradient on level sets
    (∀ (u : Torus d → ℝ) (g : Torus d → Tangent d), IsWeakGradient u g →
      SharpLSI.IsWeakGrad u (fun y k => g y k) ∧ ∀ M : ℝ, ∀ᵐ x ∂haar d, u x = M → g x = 0) ∧
    -- |u|, u⁺, u⁻ with chain formulas and pointwise norm bounds
    (∀ (u : Torus d → ℝ) (g : Torus d → Tangent d), IsWeakGradient u g →
      IsWeakGradient (fun x => |u x|)
        (fun x => if 0 < u x then g x else if u x < 0 then -g x else 0) ∧
      IsWeakGradient (fun x => max (u x) 0) (fun x => if 0 < u x then g x else 0) ∧
      IsWeakGradient (fun x => max (-u x) 0) (fun x => if u x < 0 then -g x else 0) ∧
      (∀ x, ‖(if 0 < u x then g x else if u x < 0 then -g x else 0)‖ ≤ ‖g x‖) ∧
      (∀ x, ‖(if 0 < u x then g x else 0)‖ ≤ ‖g x‖) ∧
      (∀ x, ‖(if u x < 0 then -g x else 0)‖ ≤ ‖g x‖)) ∧
    -- truncation at any level
    (∀ (u : Torus d → ℝ) (g : Torus d → Tangent d), IsWeakGradient u g → ∀ c : ℝ,
      IsWeakGradient (fun x => max (u x) c) (fun x => if c < u x then g x else 0) ∧
      IsWeakGradient (fun x => min (u x) c) (fun x => if u x < c then g x else 0) ∧
      (∀ x, ‖(if c < u x then g x else 0)‖ ≤ ‖g x‖) ∧
      (∀ x, ‖(if u x < c then g x else 0)‖ ≤ ‖g x‖)) ∧
    -- affine rescaling
    (∀ (u : Torus d → ℝ) (g : Torus d → Tangent d), IsWeakGradient u g → ∀ a b : ℝ,
      IsWeakGradient (fun x => a * u x + b) (fun x => a • g x)) ∧
    -- energy comparison for contractions
    (∀ (G g : Torus d → Tangent d), MemLp G 2 (haar d) → MemLp g 2 (haar d) →
      (∀ x, ‖G x‖ ≤ ‖g x‖) → ∫ x, ‖G x‖ ^ 2 ∂haar d ≤ ∫ x, ‖g x‖ ^ 2 ∂haar d) ∧
    -- product with W^{1,∞}
    (∀ (u w : Torus d → ℝ) (g h : Torus d → Tangent d), IsWeakGradient u g →
      IsWeakGradientLp ∞ w h →
      IsWeakGradient (fun x => u x * w x) (fun x => w x • g x + u x • h x)) ∧
    -- vector norm chain rule
    (∀ (N : ℕ) (u : Fin N → Torus d → ℝ) (g : Fin N → Torus d → Tangent d),
      (∀ i, IsWeakGradient (u i) (g i)) →
      IsWeakGradient (eNorm u) (eNormGrad u g) ∧
      (∀ x, 0 < eNorm u x → eNormGrad u g x = (eNorm u x)⁻¹ • ∑ i, u i x • g i x) ∧
      (∀ x, eNorm u x = 0 → eNormGrad u g x = 0) ∧
      (∀ x, ‖eNormGrad u g x‖ ^ 2 ≤ ∑ i, ‖g i x‖ ^ 2) ∧
      ∫ x, ‖eNormGrad u g x‖ ^ 2 ∂haar d ≤ ∑ i, ∫ x, ‖g i x‖ ^ 2 ∂haar d) := by
  refine ⟨fun u g h => ⟨h.isWeakGrad, h.ae_grad_eq_zero⟩, fun u g h => ⟨h.abs, h.posPart,
    h.negPart, fun x => ?_, fun x => ?_, fun x => ?_⟩, fun u g h c => ⟨h.max_const c,
    h.min_const c, fun x => ?_, fun x => ?_⟩, fun u g h a b => h.affine a b,
    fun G g hG hg h => integral_norm_sq_le_of_le hG hg h,
    fun u w g h hu hw => hu.mul_W1infty hw, fun N u g hu => ⟨IsWeakGradient.norm_vec hu,
    fun x hx => rfl, fun x hx => by simp [eNormGrad, hx], norm_eNormGrad_le u g,
    integral_eNormGrad_le hu⟩⟩ <;> split_ifs <;> simp

end DGPS.Analysis
