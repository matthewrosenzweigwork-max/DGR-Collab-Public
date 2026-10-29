import DGPS.Basic.HeatKernelBounds
import DGPS.Foundations.AbsoluteDensity
import DGPS.Foundations.SobolevCalculus
import DGPS.Foundations.WeakContractions
import DGPS.Foundations.PeriodicSmoothing
import SharpSymmetricLSI.Infra.HeatTorus4

/-!
# Heat recovery of absolute square root Sobolev densities (LIP019)

For an absolute density `ρ = u²` (`u ∈ H¹(m)`, `u ≥ 0`, `∫ u² = 1`) the heat flow `ρ_t = H_t ρ`
is smooth, strictly positive and of mass one for `t > 0`; `|∇ √ρ_t|² ≤ H_t |∇u|²` pointwise
(weighted Cauchy-Schwarz for the heat kernel); `‖√ρ_t - u‖₂² ≤ ‖ρ_t - ρ‖₁`; and `√ρ_t → u`
strongly in `H¹` as `t ↓ 0` (weak convergence against smooth fields plus the norm upper bound).

Main result: `DGPS.Lipschitz.heat_recovery_of_absolute_square_root_sobolev_densities`.
Smoothness of `H_t f` is taken from the legacy `SharpSymmetricLSI.Infra.HeatTorus4`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal Real

namespace DGPS.Lipschitz

open DGPS

variable {d : ℕ}

theorem isSmoothPeriodic_heatOp {t : ℝ} (ht : 0 < t) {f : Torus d → ℝ}
    (hf : Integrable f (haar d)) : IsSmoothPeriodic (heatOp t f) := by
  have h := SharpLSI.isSmoothT_heatT ht hf
  have e : heatOp t f = SharpLSI.heatT t f := by
    funext x
    rw [SharpLSI.heatT_eq' ht hf.aestronglyMeasurable x]
    unfold heatOp torusConv
    simp_rw [mul_comm]
  rw [e]
  exact h


theorem heatOp_pos {t : ℝ} (ht : 0 < t) {f : Torus d → ℝ} (hf : Integrable f (haar d))
    (hf0 : 0 ≤ᵐ[haar d] f) (hf1 : ∫ w, f w ∂haar d = 1) (x : Torus d) : 0 < heatOp t f x := by
  have hK := continuous_heatKernelT (d := d) ht
  have hψ : Continuous fun w : Torus d => heatKernelT t (x - w) :=
    hK.comp (continuous_const.sub continuous_id)
  obtain ⟨w0, -, hw0⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty hψ.continuousOn
  set c := heatKernelT t (x - w0) with hc
  have hcpos : 0 < c := heatKernelT_pos ht _
  have h1 : ∫ w, c * f w ∂haar d ≤ ∫ w, heatKernelT t (x - w) * f w ∂haar d := by
    refine integral_mono_ae (hf.const_mul c) (integrable_conv_integrand hK hf x) ?_
    filter_upwards [hf0] with w hw
    exact mul_le_mul_of_nonneg_right (hw0 (Set.mem_univ w)) hw
  rw [integral_const_mul, hf1, mul_one] at h1
  exact lt_of_lt_of_le hcpos h1

theorem integral_heatOp {t : ℝ} (ht : 0 < t) {f : Torus d → ℝ} (hf : Integrable f (haar d)) :
    ∫ x, heatOp t f x ∂haar d = ∫ w, f w ∂haar d := by
  unfold heatOp
  rw [integral_torusConv (continuous_heatKernelT ht) hf, integral_heatKernelT ht, one_mul]

theorem coordPartial_heatOp_sq {t : ℝ} (ht : 0 < t) {u : Torus d → ℝ} {g : Torus d → Tangent d}
    (hu : IsWeakGradient u g) (j : Fin d) :
    coordPartial j (heatOp t fun x => u x ^ 2) = heatOp t fun x => 2 * u x * g x j := by
  have hρ : Integrable (fun x => u x ^ 2) (haar d) := hu.memLp.integrable_sq
  have hG : Integrable (fun x => 2 * u x * g x j) (haar d) := by
    have := (hu.memLp.integrable_mul (memLp_coord hu.memLp_grad j)).const_mul 2
    simpa [mul_assoc] using this
  have hφ0 := isSmoothPeriodic_heatOp ht hρ
  have hsq := weak_square_gradient hu
  refine eq_of_fourierCoeff_eq (hφ0.continuous_coordPartial j)
    (continuous_torusConv (continuous_heatKernelT ht) hG) fun k => ?_
  have e1 : fourierCoeff (coordPartial j (heatOp t fun x => u x ^ 2)) k =
      2 * π * Complex.I * (k j : ℂ) * fourierCoeff (heatOp t fun x => u x ^ 2) k :=
    mFourierCoeff_of_ibp (integrable_of_continuous_torus hφ0.continuous_torus)
      (integrable_of_continuous_torus (hφ0.continuous_coordPartial j)) j
      (fun φ hφ => integral_mul_coordPartial_of_smooth hφ0 hφ j) k
  have e2 : fourierCoeff (fun x => 2 * u x * g x j) k =
      2 * π * Complex.I * (k j : ℂ) * fourierCoeff (fun x => u x ^ 2) k :=
    mFourierCoeff_of_ibp hρ hG j (fun φ hφ => by
      have := hsq.ibp φ hφ j
      simpa [mul_assoc] using this) k
  show fourierCoeff _ k = fourierCoeff (heatOp t _) k
  rw [e1, fourierCoeff_heatOp ht hρ, fourierCoeff_heatOp ht hG, e2]
  ring


theorem weighted_cs {α : Type*} [MeasurableSpace α] {μ : Measure α} {K a b : α → ℝ}
    (hK : 0 ≤ᵐ[μ] K) (hA : Integrable (fun x => K x * (a x * a x)) μ)
    (hB : Integrable (fun x => K x * (a x * b x)) μ)
    (hC : Integrable (fun x => K x * (b x * b x)) μ) :
    (∫ x, K x * (a x * b x) ∂μ) ^ 2 ≤
      (∫ x, K x * (a x * a x) ∂μ) * ∫ x, K x * (b x * b x) ∂μ := by
  have hq : ∀ r : ℝ, 0 ≤ (∫ x, K x * (a x * a x) ∂μ) * (r * r) +
      (2 * ∫ x, K x * (a x * b x) ∂μ) * r + ∫ x, K x * (b x * b x) ∂μ := by
    intro r
    have e : ∫ x, K x * ((r * a x + b x) * (r * a x + b x)) ∂μ =
        (∫ x, K x * (a x * a x) ∂μ) * (r * r) +
          (2 * ∫ x, K x * (a x * b x) ∂μ) * r + ∫ x, K x * (b x * b x) ∂μ := by
      have : ∀ x, K x * ((r * a x + b x) * (r * a x + b x)) =
          (r * r) * (K x * (a x * a x)) + (2 * r) * (K x * (a x * b x)) +
            K x * (b x * b x) := fun x => by ring
      simp_rw [this]
      have i1 := hA.const_mul (r * r)
      have i2 := hB.const_mul (2 * r)
      have i12 : Integrable (fun x => r * r * (K x * (a x * a x)) +
          2 * r * (K x * (a x * b x))) μ := i1.add i2
      rw [integral_add i12 hC, integral_add i1 i2, integral_const_mul, integral_const_mul]
      ring
    rw [← e]
    refine integral_nonneg_of_ae ?_
    filter_upwards [hK] with x hx
    exact mul_nonneg hx (mul_self_nonneg _)
  have := discrim_le_zero hq
  unfold discrim at this
  nlinarith

theorem heatOp_cs {t : ℝ} (ht : 0 < t) {a b : Torus d → ℝ} (ha : MemLp a 2 (haar d))
    (hb : MemLp b 2 (haar d)) (x : Torus d) :
    (heatOp t (fun w => a w * b w) x) ^ 2 ≤
      heatOp t (fun w => a w * a w) x * heatOp t (fun w => b w * b w) x := by
  have hK := continuous_heatKernelT (d := d) ht
  unfold heatOp torusConv
  exact weighted_cs (K := fun w => heatKernelT t (x - w))
    (Eventually.of_forall fun w => (heatKernelT_pos ht _).le)
    (integrable_conv_integrand hK (ha.integrable_mul ha) x)
    (integrable_conv_integrand hK (ha.integrable_mul hb) x)
    (integrable_conv_integrand hK (hb.integrable_mul hb) x)

theorem coordPartial_sqrt {φ : Torus d → ℝ} (hφ : IsSmoothPeriodic φ) (hpos : ∀ x, 0 < φ x)
    (j : Fin d) (x : Torus d) :
    coordPartial j (fun y => √(φ y)) x = coordPartial j φ x / (2 * √(φ x)) := by
  have hd : DifferentiableAt ℝ (φ ∘ SharpLSI.liftT) (SharpLSI.secT x) :=
    (hφ.differentiable (by simp)) _
  have hx : (φ ∘ SharpLSI.liftT) (SharpLSI.secT x) ≠ 0 := by
    simp only [Function.comp_apply, SharpLSI.liftT_secT]; exact (hpos x).ne'
  have h := (hd.hasFDerivAt.sqrt hx).fderiv
  unfold coordPartial
  have e : ((fun y => √(φ y)) ∘ SharpLSI.liftT) = fun z => √((φ ∘ SharpLSI.liftT) z) := rfl
  rw [e, h]
  simp only [Function.comp_apply, SharpLSI.liftT_secT, smul_apply, smul_eq_mul]
  field_simp

theorem isSmoothPeriodic_sqrt {φ : Torus d → ℝ} (hφ : IsSmoothPeriodic φ) (hpos : ∀ x, 0 < φ x) :
    IsSmoothPeriodic (fun y => √(φ y)) := by
  unfold IsSmoothPeriodic at *
  exact ContDiff.sqrt hφ fun z => (hpos _).ne'


theorem heatOp_const_mul (t c : ℝ) (f : Torus d → ℝ) (x : Torus d) :
    heatOp t (fun w => c * f w) x = c * heatOp t f x := by
  unfold heatOp torusConv
  rw [← integral_const_mul]
  congr 1
  funext w
  ring

theorem heatOp_norm_sq {t : ℝ} (ht : 0 < t) {g : Torus d → Tangent d} (hg : MemLp g 2 (haar d))
    (x : Torus d) :
    heatOp t (fun w => ‖g w‖ ^ 2) x = ∑ j, heatOp t (fun w => g w j * g w j) x := by
  have hK := continuous_heatKernelT (d := d) ht
  unfold heatOp torusConv
  have hi : ∀ j : Fin d, Integrable (fun w => heatKernelT t (x - w) * (g w j * g w j)) (haar d) :=
    fun j => integrable_conv_integrand hK (f := fun w => g w j * g w j)
      ((memLp_coord hg j).integrable_mul (memLp_coord hg j)) x
  rw [← integral_finsetSum _ fun j _ => hi j]
  congr 1
  funext w
  rw [← Finset.mul_sum]
  beta_reduce
  rw [tangent_norm_sq]
  simp_rw [sq]

theorem norm_sq_smoothGrad_sqrt_heatOp_le {t : ℝ} (ht : 0 < t) {u : Torus d → ℝ}
    {g : Torus d → Tangent d} (hu : IsWeakGradient u g) (hmass : ∫ x, u x ^ 2 ∂haar d = 1)
    (x : Torus d) :
    ‖smoothGrad (fun y => √(heatOp t (fun w => u w ^ 2) y)) x‖ ^ 2 ≤
      heatOp t (fun w => ‖g w‖ ^ 2) x := by
  have hρ : Integrable (fun x => u x ^ 2) (haar d) := hu.memLp.integrable_sq
  have hR := isSmoothPeriodic_heatOp ht hρ
  have hpos : ∀ y, 0 < heatOp t (fun w => u w ^ 2) y :=
    heatOp_pos ht hρ (Eventually.of_forall fun w => sq_nonneg _) hmass
  rw [heatOp_norm_sq ht hu.memLp_grad, tangent_norm_sq]
  refine Finset.sum_le_sum fun j _ => ?_
  have e : heatOp t (fun w => 2 * u w * g w j) = heatOp t (fun w => 2 * (u w * g w j)) := by
    simp_rw [mul_assoc]
  have hcs := heatOp_cs ht hu.memLp (memLp_coord hu.memLp_grad j) x
  have e2 : heatOp t (fun w => u w ^ 2) = heatOp t (fun w => u w * u w) := by simp_rw [sq]
  rw [smoothGrad_apply, coordPartial_sqrt hR hpos, coordPartial_heatOp_sq ht hu, e,
    heatOp_const_mul, div_pow, mul_pow, mul_pow, Real.sq_sqrt (hpos x).le, div_le_iff₀ (by
      have := hpos x; positivity)]
  rw [e2]
  nlinarith [hcs]


theorem integrable_norm_sq_of_memLp {A : Torus d → Tangent d} (hA : MemLp A 2 (haar d)) :
    Integrable (fun x => ‖A x‖ ^ 2) (haar d) := hA.norm.integrable_sq

theorem integrable_inner_of_memLp {A B : Torus d → Tangent d} (hA : MemLp A 2 (haar d))
    (hB : MemLp B 2 (haar d)) : Integrable (fun x => inner ℝ (A x) (B x)) (haar d) := by
  refine Integrable.mono' (hA.norm.integrable_mul hB.norm)
    (hA.aestronglyMeasurable.inner hB.aestronglyMeasurable) (Eventually.of_forall fun x => ?_)
  simpa [norm_mul] using abs_real_inner_le_norm (A x) (B x)

theorem integral_norm_sub_sq {A B : Torus d → Tangent d} (hA : MemLp A 2 (haar d))
    (hB : MemLp B 2 (haar d)) :
    ∫ x, ‖A x - B x‖ ^ 2 ∂haar d =
      ∫ x, ‖A x‖ ^ 2 ∂haar d - 2 * ∫ x, inner ℝ (A x) (B x) ∂haar d + ∫ x, ‖B x‖ ^ 2 ∂haar d := by
  have h1 := integrable_norm_sq_of_memLp hA
  have h2 := integrable_norm_sq_of_memLp hB
  have h3 := integrable_inner_of_memLp hA hB
  have : ∀ x, ‖A x - B x‖ ^ 2 = ‖A x‖ ^ 2 - 2 * inner ℝ (A x) (B x) + ‖B x‖ ^ 2 :=
    fun x => norm_sub_sq_real _ _
  simp_rw [this]
  have i12 : Integrable (fun x => ‖A x‖ ^ 2 - 2 * inner ℝ (A x) (B x)) (haar d) :=
    h1.sub (h3.const_mul 2)
  rw [integral_add i12 h2, integral_sub h1 (h3.const_mul 2), integral_const_mul]

theorem tendsto_L2_of_weak_of_bound {w : ℝ → Torus d → Tangent d} {g : Torus d → Tangent d}
    (S : (Torus d → Tangent d) → Prop) (hw : ∀ t, 0 < t → MemLp (w t) 2 (haar d))
    (hg : MemLp g 2 (haar d))
    (hbound : ∀ t, 0 < t → ∫ x, ‖w t x‖ ^ 2 ∂haar d ≤ ∫ x, ‖g x‖ ^ 2 ∂haar d)
    (hS : ∀ h, S h → MemLp h 2 (haar d))
    (hweak : ∀ h, S h → Tendsto (fun t : ℝ => ∫ x, inner ℝ (w t x) (h x) ∂haar d) (𝓝[>] 0)
      (𝓝 (∫ x, inner ℝ (g x) (h x) ∂haar d)))
    (hdense : ∀ ε : ℝ, 0 < ε → ∃ h, S h ∧ ∫ x, ‖h x - g x‖ ^ 2 ∂haar d < ε) :
    Tendsto (fun t : ℝ => ∫ x, ‖w t x - g x‖ ^ 2 ∂haar d) (𝓝[>] 0) (𝓝 0) := by
  rw [tendsto_order]
  refine ⟨fun a ha => ?_, fun a ha => ?_⟩
  · filter_upwards with t
    exact lt_of_lt_of_le ha (integral_nonneg fun x => sq_nonneg _)
  · obtain ⟨h, hSh, hD⟩ := hdense (a / 8) (by linarith)
    have hh := hS h hSh
    have hI := (tendsto_order.1 (hweak h hSh)).1
      ((∫ x, inner ℝ (g x) (h x) ∂haar d) - a / 8) (by linarith)
    filter_upwards [hI, self_mem_nhdsWithin] with t hIt ht
    have ht : 0 < t := ht
    have hwt := hw t ht
    have e1 := integral_norm_sub_sq hwt hh
    have e2 := integral_norm_sub_sq hh hg
    have e3 := integral_norm_sub_sq hg hh
    have hsym : ∀ x, inner ℝ (h x) (g x) = inner ℝ (g x) (h x) := fun x => real_inner_comm _ _
    simp_rw [hsym] at e2
    have e4 : ∫ x, ‖g x - h x‖ ^ 2 ∂haar d = ∫ x, ‖h x - g x‖ ^ 2 ∂haar d := by
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only [norm_sub_rev]
    have hb := hbound t ht
    have hmono : ∫ x, ‖w t x - g x‖ ^ 2 ∂haar d ≤
        2 * ∫ x, ‖w t x - h x‖ ^ 2 ∂haar d + 2 * ∫ x, ‖h x - g x‖ ^ 2 ∂haar d := by
      rw [← integral_const_mul, ← integral_const_mul, ← integral_add]
      · refine integral_mono (integrable_norm_sq_of_memLp (hwt.sub hg)) ?_ fun x => ?_
        · exact ((integrable_norm_sq_of_memLp (hwt.sub hh)).const_mul 2).add
            ((integrable_norm_sq_of_memLp (hh.sub hg)).const_mul 2)
        · have := norm_sub_le_norm_sub_add_norm_sub (w t x) (h x) (g x)
          have h0 := norm_nonneg (w t x - h x)
          have h1 := norm_nonneg (h x - g x)
          simp only
          nlinarith [sq_nonneg (‖w t x - h x‖ - ‖h x - g x‖), norm_nonneg (w t x - g x)]
      · exact (integrable_norm_sq_of_memLp (hwt.sub hh)).const_mul 2
      · exact (integrable_norm_sq_of_memLp (hh.sub hg)).const_mul 2
    linarith


theorem cs_L2 {a b : Torus d → ℝ} (ha : MemLp a 2 (haar d)) (hb : MemLp b 2 (haar d)) :
    (∫ x, a x * b x ∂haar d) ^ 2 ≤ (∫ x, a x ^ 2 ∂haar d) * ∫ x, b x ^ 2 ∂haar d := by
  have i1 : Integrable (fun x => a x * a x) (haar d) := ha.integrable_mul ha
  have i2 : Integrable (fun x => a x * b x) (haar d) := ha.integrable_mul hb
  have i3 : Integrable (fun x => b x * b x) (haar d) := hb.integrable_mul hb
  have h := weighted_cs (μ := haar d) (K := fun _ => (1 : ℝ)) (a := a) (b := b)
    (Eventually.of_forall fun _ => zero_le_one)
    (by simpa only [one_mul] using i1) (by simpa only [one_mul] using i2)
    (by simpa only [one_mul] using i3)
  simpa [sq] using h

theorem sqrt_sub_sq_le {a u : ℝ} (ha : 0 ≤ a) (hu : 0 ≤ u) : (√a - u) ^ 2 ≤ |a - u ^ 2| := by
  have hs := Real.sq_sqrt ha
  have hs0 := Real.sqrt_nonneg a
  rcases le_total (√a) u with h | h
  · rw [abs_of_nonpos (by nlinarith)]
    nlinarith
  · rw [abs_of_nonneg (by nlinarith)]
    nlinarith

/-- Basic regularity of the heat-flowed density, packaged for `t > 0`. -/
theorem heat_density_facts {t : ℝ} (ht : 0 < t) {u : Torus d → ℝ} (hu : MemLp u 2 (haar d))
    (hmass : ∫ x, u x ^ 2 ∂haar d = 1) :
    IsSmoothPeriodic (heatOp t fun w => u w ^ 2) ∧ (∀ y, 0 < heatOp t (fun w => u w ^ 2) y) ∧
      ∫ y, heatOp t (fun w => u w ^ 2) y ∂haar d = 1 := by
  have hρ : Integrable (fun x => u x ^ 2) (haar d) := hu.integrable_sq
  exact ⟨isSmoothPeriodic_heatOp ht hρ,
    heatOp_pos ht hρ (Eventually.of_forall fun w => sq_nonneg _) hmass,
    by rw [integral_heatOp ht hρ, hmass]⟩

theorem isSmoothPeriodic_sqrt_heatOp {t : ℝ} (ht : 0 < t) {u : Torus d → ℝ}
    (hu : MemLp u 2 (haar d)) (hmass : ∫ x, u x ^ 2 ∂haar d = 1) :
    IsSmoothPeriodic (fun y => √(heatOp t (fun w => u w ^ 2) y)) := by
  obtain ⟨h1, h2, -⟩ := heat_density_facts ht hu hmass
  exact isSmoothPeriodic_sqrt h1 h2

theorem memLp_sqrt_heatOp {t : ℝ} (ht : 0 < t) {u : Torus d → ℝ}
    (hu : MemLp u 2 (haar d)) (hmass : ∫ x, u x ^ 2 ∂haar d = 1) :
    MemLp (fun y => √(heatOp t (fun w => u w ^ 2) y)) 2 (haar d) :=
  memLp_two_of_continuous (isSmoothPeriodic_sqrt_heatOp ht hu hmass).continuous_torus

/-- Pointwise `L²`-by-`L¹` comparison for the square root of the heat flow. -/
theorem integral_sqrt_heatOp_sub_sq_le {t : ℝ} (ht : 0 < t) {u : Torus d → ℝ}
    (hu : MemLp u 2 (haar d)) (hu0 : 0 ≤ᵐ[haar d] u) (hmass : ∫ x, u x ^ 2 ∂haar d = 1) :
    ∫ x, (√(heatOp t (fun w => u w ^ 2) x) - u x) ^ 2 ∂haar d ≤
      ∫ x, |heatOp t (fun w => u w ^ 2) x - u x ^ 2| ∂haar d := by
  obtain ⟨h1, h2, -⟩ := heat_density_facts ht hu hmass
  have hρ : Integrable (fun x => u x ^ 2) (haar d) := hu.integrable_sq
  have hi : Integrable (fun x => heatOp t (fun w => u w ^ 2) x - u x ^ 2) (haar d) :=
    (integrable_of_continuous_torus h1.continuous_torus).sub hρ
  refine integral_mono_of_nonneg (Eventually.of_forall fun x => sq_nonneg _) hi.abs ?_
  filter_upwards [hu0] with x hx
  exact sqrt_sub_sq_le (h2 x).le hx

theorem tendsto_integral_abs_heatOp_sub {u : Torus d → ℝ} (hu : MemLp u 2 (haar d)) :
    Tendsto (fun t : ℝ => ∫ x, |heatOp t (fun w => u w ^ 2) x - u x ^ 2| ∂haar d) (𝓝[>] 0)
      (𝓝 0) := by
  have hρ : MemLp (fun x => u x ^ 2) 1 (haar d) := by
    have := hu.integrable_sq
    exact memLp_one_iff_integrable.2 this
  have h := tendsto_eLpNorm_heatOp_sub (d := d) (p := 1) le_rfl (by simp) hρ
  have h2 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
  simp only [ENNReal.toReal_zero] at h2
  refine h2.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht : 0 < t := ht
  have hm : MemLp (fun y => heatOp t (fun w => u w ^ 2) y) 1 (haar d) :=
    memLp_heatOp ht le_rfl (by simp) hρ
  have hs := hm.sub hρ
  simp only [Function.comp]
  have e := integral_norm_eq_lintegral_enorm (μ := haar d)
    (f := fun x => heatOp t (fun w => u w ^ 2) x - u x ^ 2) hs.aestronglyMeasurable
  simp only [Real.norm_eq_abs] at e
  have hs' : AEStronglyMeasurable (fun y => heatOp t (fun w => u w ^ 2) y - u y ^ 2)
      (haar d) := hs.aestronglyMeasurable
  rw [eLpNorm_one_eq_lintegral_enorm hs']
  exact e.symm

theorem tendsto_sqrt_heatOp_L2 {u : Torus d → ℝ} (hu : MemLp u 2 (haar d))
    (hu0 : 0 ≤ᵐ[haar d] u) (hmass : ∫ x, u x ^ 2 ∂haar d = 1) :
    Tendsto (fun t : ℝ => ∫ x, (√(heatOp t (fun w => u w ^ 2) x) - u x) ^ 2 ∂haar d) (𝓝[>] 0)
      (𝓝 0) := by
  refine squeeze_zero' (Eventually.of_forall fun t => integral_nonneg fun x => sq_nonneg _) ?_
    (tendsto_integral_abs_heatOp_sub hu)
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact integral_sqrt_heatOp_sub_sq_le ht hu hu0 hmass

theorem tendsto_integral_sqrt_heatOp_mul {u : Torus d → ℝ} (hu : MemLp u 2 (haar d))
    (hu0 : 0 ≤ᵐ[haar d] u) (hmass : ∫ x, u x ^ 2 ∂haar d = 1) {ψ : Torus d → ℝ}
    (hψ : Continuous ψ) :
    Tendsto (fun t : ℝ => ∫ x, √(heatOp t (fun w => u w ^ 2) x) * ψ x ∂haar d) (𝓝[>] 0)
      (𝓝 (∫ x, u x * ψ x ∂haar d)) := by
  have hψ2 := memLp_two_of_continuous hψ
  have hD := tendsto_sqrt_heatOp_L2 hu hu0 hmass
  have hC : Tendsto (fun t : ℝ => √((∫ x, (√(heatOp t (fun w => u w ^ 2) x) - u x) ^ 2 ∂haar d) *
      ∫ x, ψ x ^ 2 ∂haar d)) (𝓝[>] 0) (𝓝 0) := by
    have := (hD.mul_const (∫ x, ψ x ^ 2 ∂haar d)).sqrt
    simpa using this
  rw [← tendsto_sub_nhds_zero_iff]
  refine squeeze_zero_norm' ?_ hC
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht : 0 < t := ht
  have hv := memLp_sqrt_heatOp ht hu hmass
  have e : ∫ x, √(heatOp t (fun w => u w ^ 2) x) * ψ x ∂haar d - ∫ x, u x * ψ x ∂haar d =
      ∫ x, (√(heatOp t (fun w => u w ^ 2) x) - u x) * ψ x ∂haar d := by
    have i1 : Integrable (fun x => √(heatOp t (fun w => u w ^ 2) x) * ψ x) (haar d) :=
      hv.integrable_mul hψ2
    have i2 : Integrable (fun x => u x * ψ x) (haar d) := hu.integrable_mul hψ2
    rw [← integral_sub i1 i2]
    simp_rw [sub_mul]
  rw [e, Real.norm_eq_abs]
  exact Real.abs_le_sqrt (cs_L2 (hv.sub hu) hψ2)

theorem integral_inner_eq_sum {A h : Torus d → Tangent d} (hA : MemLp A 2 (haar d))
    (hh : MemLp h 2 (haar d)) :
    ∫ x, inner ℝ (A x) (h x) ∂haar d = ∑ j, ∫ x, A x j * h x j ∂haar d := by
  have hi : ∀ j, Integrable (fun x => A x j * h x j) (haar d) := fun j =>
    (memLp_coord hA j).integrable_mul (memLp_coord hh j)
  rw [← integral_finsetSum _ fun j _ => hi j]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp [PiLp.inner_apply, mul_comm]

theorem tendsto_inner_smoothGrad_sqrt_heatOp {u : Torus d → ℝ} {g : Torus d → Tangent d}
    (hu : IsWeakGradient u g) (hu0 : 0 ≤ᵐ[haar d] u) (hmass : ∫ x, u x ^ 2 ∂haar d = 1)
    {h : Torus d → Tangent d} (hh : ∀ j, IsSmoothPeriodic fun x => h x j) :
    Tendsto (fun t : ℝ => ∫ x, inner ℝ (smoothGrad (fun y => √(heatOp t (fun w => u w ^ 2) y)) x)
        (h x) ∂haar d) (𝓝[>] 0) (𝓝 (∫ x, inner ℝ (g x) (h x) ∂haar d)) := by
  have hh2 : MemLp h 2 (haar d) :=
    memLp_piLp_iff.mpr fun j => memLp_two_of_continuous (hh j).continuous_torus
  have hlim : Tendsto (fun t : ℝ => -∑ j, ∫ x, √(heatOp t (fun w => u w ^ 2) x) *
      coordPartial j (fun x => h x j) x ∂haar d) (𝓝[>] 0)
      (𝓝 (-∑ j, ∫ x, u x * coordPartial j (fun x => h x j) x ∂haar d)) :=
    (tendsto_finsetSum _ fun j _ => tendsto_integral_sqrt_heatOp_mul hu.memLp hu0 hmass
      ((hh j).continuous_coordPartial j)).neg
  have hrhs : ∫ x, inner ℝ (g x) (h x) ∂haar d =
      -∑ j, ∫ x, u x * coordPartial j (fun x => h x j) x ∂haar d := by
    rw [integral_inner_eq_sum hu.memLp_grad hh2, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hu.ibp _ (hh j) j, neg_neg]
  rw [hrhs]
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht : 0 < t := ht
  have hv := isSmoothPeriodic_sqrt_heatOp ht hu.memLp hmass
  rw [integral_inner_eq_sum (hv.isWeakGradient).memLp_grad hh2, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [smoothGrad_apply]
  rw [integral_mul_coordPartial_of_smooth hv (hh j) j, neg_neg]

/-- The gradient norms of `√(H_t ρ)` are bounded in `L²` by those of `∇u`. -/
theorem integral_norm_sq_smoothGrad_sqrt_heatOp_le {t : ℝ} (ht : 0 < t) {u : Torus d → ℝ}
    {g : Torus d → Tangent d} (hu : IsWeakGradient u g) (hmass : ∫ x, u x ^ 2 ∂haar d = 1) :
    ∫ x, ‖smoothGrad (fun y => √(heatOp t (fun w => u w ^ 2) y)) x‖ ^ 2 ∂haar d ≤
      ∫ x, ‖g x‖ ^ 2 ∂haar d := by
  have hv := isSmoothPeriodic_sqrt_heatOp ht hu.memLp hmass
  have hgi : Integrable (fun x => ‖g x‖ ^ 2) (haar d) := integrable_norm_sq_of_memLp hu.memLp_grad
  have hH : Integrable (fun x => heatOp t (fun w => ‖g w‖ ^ 2) x) (haar d) :=
    integrable_of_continuous_torus (isSmoothPeriodic_heatOp ht hgi).continuous_torus
  calc ∫ x, ‖smoothGrad (fun y => √(heatOp t (fun w => u w ^ 2) y)) x‖ ^ 2 ∂haar d
      ≤ ∫ x, heatOp t (fun w => ‖g w‖ ^ 2) x ∂haar d :=
        integral_mono (integrable_norm_sq_of_memLp hv.isWeakGradient.memLp_grad) hH
          fun x => norm_sq_smoothGrad_sqrt_heatOp_le ht hu hmass x
    _ = ∫ x, ‖g x‖ ^ 2 ∂haar d := integral_heatOp ht hgi

/-- Strong `H¹` convergence of `√(H_t ρ)` to `u`, for a nonnegative `u` of mass one. -/
theorem tendsto_H1_sqrt_heatOp {u : Torus d → ℝ} {g : Torus d → Tangent d}
    (hu : IsWeakGradient u g) (hu0 : 0 ≤ᵐ[haar d] u) (hmass : ∫ x, u x ^ 2 ∂haar d = 1) :
    Tendsto (fun t : ℝ => ∫ x, (√(heatOp t (fun w => u w ^ 2) x) - u x) ^ 2 ∂haar d +
      ∫ x, ‖smoothGrad (fun y => √(heatOp t (fun w => u w ^ 2) y)) x - g x‖ ^ 2 ∂haar d)
      (𝓝[>] 0) (𝓝 0) := by
  have h1 := tendsto_sqrt_heatOp_L2 hu.memLp hu0 hmass
  have h2 : Tendsto (fun t : ℝ => ∫ x,
      ‖smoothGrad (fun y => √(heatOp t (fun w => u w ^ 2) y)) x - g x‖ ^ 2 ∂haar d)
      (𝓝[>] 0) (𝓝 0) := by
    refine tendsto_L2_of_weak_of_bound
      (fun h : Torus d → Tangent d => ∀ j, IsSmoothPeriodic fun x => h x j)
      (fun t ht => (isSmoothPeriodic_sqrt_heatOp ht hu.memLp hmass).isWeakGradient.memLp_grad)
      hu.memLp_grad (fun t ht => integral_norm_sq_smoothGrad_sqrt_heatOp_le ht hu hmass)
      (fun h hh => memLp_piLp_iff.mpr fun j => memLp_two_of_continuous (hh j).continuous_torus)
      (fun h hh => tendsto_inner_smoothGrad_sqrt_heatOp hu hu0 hmass hh) ?_
    intro ε hε
    have hT := tendsto_integral_norm_sq_heatGrad_sub hu.memLp_grad
    obtain ⟨s, hs, hsp⟩ := ((hT.eventually (gt_mem_nhds hε)).and self_mem_nhdsWithin).exists
    have hs0 : 0 < s := hsp
    refine ⟨heatGrad s g, fun j => ?_, hs⟩
    exact isSmoothPeriodic_heatOp hs0
      ((memLp_coord hu.memLp_grad j).integrable one_le_two)
  simpa using h1.add h2

/-- **Heat recovery of absolute square root Sobolev densities (LIP019).**
Let `ρ = u²` be an absolute density with `u ∈ H¹(m)`, `u ≥ 0`, `∫ u² = 1`, and `g = ∇u`. Then
for every `t > 0` the heat flow `ρ_t = H_t ρ` is smooth, strictly positive and of mass one, its
square root is smooth, `|∇ √ρ_t|² ≤ H_t |∇u|²` pointwise and `‖√ρ_t - u‖₂² ≤ ‖ρ_t - ρ‖₁`;
and `√ρ_t → u` strongly in `H¹` as `t ↓ 0`. -/
theorem heat_recovery_of_absolute_square_root_sobolev_densities (ρ : AbsoluteDensity d) :
    (∀ t : ℝ, 0 < t →
      IsSmoothPeriodic (heatOp t ρ.density) ∧ (∀ x, 0 < heatOp t ρ.density x) ∧
        ∫ x, heatOp t ρ.density x ∂haar d = 1) ∧
    (∀ t : ℝ, 0 < t → IsSmoothPeriodic (fun y => √(heatOp t ρ.density y))) ∧
    (∀ t : ℝ, 0 < t → ∀ x,
      ‖smoothGrad (fun y => √(heatOp t ρ.density y)) x‖ ^ 2 ≤
        heatOp t (fun w => ‖weakGradient ρ.sqrt ρ.sqrt_mem w‖ ^ 2) x) ∧
    (∀ t : ℝ, 0 < t →
      ∫ x, (√(heatOp t ρ.density x) - ρ.sqrt x) ^ 2 ∂haar d ≤
        ∫ x, |heatOp t ρ.density x - ρ.density x| ∂haar d) ∧
    Tendsto (fun t : ℝ => ∫ x, (√(heatOp t ρ.density x) - ρ.sqrt x) ^ 2 ∂haar d +
      ∫ x, ‖smoothGrad (fun y => √(heatOp t ρ.density y)) x -
        weakGradient ρ.sqrt ρ.sqrt_mem x‖ ^ 2 ∂haar d) (𝓝[>] 0) (𝓝 0) := by
  have hu := isWeakGradient_weakGradient ρ.sqrt_mem
  have hm := ρ.mass_one
  refine ⟨fun t ht => heat_density_facts ht hu.memLp hm,
    fun t ht => isSmoothPeriodic_sqrt_heatOp ht hu.memLp hm,
    fun t ht x => norm_sq_smoothGrad_sqrt_heatOp_le ht hu hm x,
    fun t ht => integral_sqrt_heatOp_sub_sq_le ht hu.memLp ρ.sqrt_nonneg hm,
    tendsto_H1_sqrt_heatOp hu ρ.sqrt_nonneg hm⟩

end DGPS.Lipschitz
