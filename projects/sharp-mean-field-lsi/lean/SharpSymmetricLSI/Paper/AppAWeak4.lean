import SharpSymmetricLSI.Paper.AppAWeak3

/-!
# The weak formulation (4): the flux is bounded by the dissipation

For a probability density `f` with weak gradient `g`:
`∫ |g + f a_f| ≤ D(f)^{1/2}` (`lintegral_flux_le`), by `∇f = 2√f ∇√f` and Cauchy–Schwarz
against `∫ f = 1`.
-/

open MeasureTheory Set Filter Topology
open scoped Real ENNReal

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-- `∇(V + W*f) = a_f` a.e. -/
theorem weakGrad_potential_ae (hyp : Hyp V W KV KW) {f : Torus d → ℝ} (hf : Integrable f (haar d)) :
    weakGrad (fun x => V x + convDens W f x) =ᵐ[haar d] fun x k => appADrift V W f x k := by
  have hVl := isWeakGrad_lipGrad hyp.continuous_V (lipschitz_V hyp (W := W))
  have hsum := hVl.add (isWeakGrad_convDens' hyp hf)
  filter_upwards [appA_weakGrad_ae_eq hsum, appA_weakGrad_ae_eq hVl,
    weakGrad_convDens_ae hyp hf] with x h1 h2 h3
  funext k
  rw [h1]; unfold appADrift; rw [h2, h3]

theorem memLp_weakGrad_comp_of_memH1 {f : UnitAddTorus (Fin d) → ℝ} (hf : MemH1 volume f) (k : Fin d) :
    MemLp (fun x => weakGrad f x k) 2 volume := by
  refine hf.2.2.of_le (appA_aestronglyMeasurable_grad (appA_isWeakGrad_weakGrad hf.1) k)
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  refine Real.le_sqrt_of_sq_le ?_
  rw [sq_abs]
  exact Finset.single_le_sum (f := fun j => weakGrad f x j ^ 2) (fun j _ => sq_nonneg _)
    (Finset.mem_univ k)

/-- **The flux bound** `∫ |∇f + f a_f| ≤ D(f)^{1/2}`. -/
theorem lintegral_flux_le (hyp : Hyp V W KV KW) {f : Torus d → ℝ} (hf : Integrable f (haar d))
    (h0 : ∀ᵐ x ∂haar d, 0 ≤ f x) (h1 : ∫ x, f x ∂haar d = 1) {g : Torus d → Fin d → ℝ}
    (hg : IsWeakGrad f g) :
    ∫⁻ x, ENNReal.ofReal (Real.sqrt (∑ j, (g x j + modFlux V W f x j) ^ 2)) ∂haar d ≤
      dissipation V W f ^ (1 / 2 : ℝ) := by
  unfold dissipation
  split_ifs with hD
  swap
  · rw [ENNReal.top_rpow_of_pos (by norm_num)]; exact le_top
  obtain ⟨hH1, hPot⟩ := hD
  set s : Torus d → ℝ := fun x => Real.sqrt (f x) with hs
  set ψ := weakGrad s
  set a := weakGrad (fun x => V x + convDens W f x)
  have hψ : IsWeakGrad s ψ := appA_isWeakGrad_weakGrad hH1.1
  have hψ2 : ∀ k, MemLp (fun x => ψ x k) 2 volume := memLp_weakGrad_comp_of_memH1 hH1
  have hsq : (fun y => s y ^ 2) =ᵐ[volume] f :=
    h0.mono fun y hy => Real.sq_sqrt hy
  have hg' : IsWeakGrad f (fun y k => 2 * s y * ψ y k) :=
    appA_isWeakGrad_congr_ae (isWeakGrad_sq hψ hH1.2.1 hψ2) hsq
  have hgeq : g =ᵐ[volume] fun y k => 2 * s y * ψ y k := weakGrad_ae_unique hg hg'
  have hflux : ∀ᵐ y ∂haar d, ∀ k, modFlux V W f y k = f y * a y k := by
    rw [ae_all_iff]; intro k
    filter_upwards [modFlux_ae_eq hyp hf h0 h1 k, weakGrad_potential_ae hyp hf] with y h2 h3
    rw [h2]; exact congrArg _ (congrFun h3 k).symm
  -- `X = 2∇√f + √f a`
  set X : Torus d → ℝ := fun x => Real.sqrt (∑ k, (2 * ψ x k + s x * a x k) ^ 2) with hX
  have hpt : ∀ᵐ x ∂haar d, ENNReal.ofReal (Real.sqrt (∑ j, (g x j + modFlux V W f x j) ^ 2)) =
      ENNReal.ofReal (s x) * ENNReal.ofReal (X x) := by
    filter_upwards [hgeq, hflux, h0] with x hx1 hx2 hx3
    have hf' : f x = s x ^ 2 := (Real.sq_sqrt hx3).symm
    have hsx : 0 ≤ s x := Real.sqrt_nonneg _
    rw [← ENNReal.ofReal_mul hsx]
    congr 1
    have e : s x * X x = Real.sqrt (s x ^ 2 * ∑ k, (2 * ψ x k + s x * a x k) ^ 2) := by
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hsx]
    rw [e, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [congrFun hx1 k, hx2 k, hf']
    ring
  rw [lintegral_congr_ae hpt]
  have hsm : AEMeasurable (fun x => ENNReal.ofReal (s x)) (haar d) :=
    ENNReal.measurable_ofReal.comp_aemeasurable (hf.aestronglyMeasurable.aemeasurable.sqrt)
  have ham : ∀ k, AEStronglyMeasurable (fun x => a x k) (haar d) := fun k =>
    (aestronglyMeasurable_appADrift hyp hf k).congr
      ((weakGrad_potential_ae hyp hf).mono fun x hx => (congrFun hx k).symm)
  have hXm : AEMeasurable (fun x => ENNReal.ofReal (X x)) (haar d) := by
    refine ENNReal.measurable_ofReal.comp_aemeasurable ?_
    refine AEMeasurable.sqrt (Finset.aemeasurable_fun_sum _ fun k _ => ?_)
    exact ((((hψ2 k).aestronglyMeasurable.aemeasurable.const_mul 2).add
      ((hf.aestronglyMeasurable.aemeasurable.sqrt).mul (ham k).aemeasurable)).pow_const 2)
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq (haar d) Real.HolderConjugate.two_two hsm hXm
  refine (le_of_eq_of_le rfl hH).trans (le_of_eq ?_)
  have e1 : ∫⁻ x, ENNReal.ofReal (s x) ^ (2 : ℝ) ∂haar d = 1 := by
    have : ∀ᵐ x ∂haar d, ENNReal.ofReal (s x) ^ (2 : ℝ) = ENNReal.ofReal (f x) := by
      filter_upwards [h0] with x hx
      rw [ENNReal.ofReal_rpow_of_nonneg (Real.sqrt_nonneg _) (by norm_num)]
      norm_num [Real.sq_sqrt hx]
    rw [lintegral_congr_ae this, ← ofReal_integral_eq_lintegral_ofReal hf h0, h1, ENNReal.ofReal_one]
  have e2 : ∀ x, ENNReal.ofReal (X x) ^ (2 : ℝ) =
      ENNReal.ofReal (∑ k, (2 * ψ x k + s x * a x k) ^ 2) := fun x => by
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.sqrt_nonneg _) (by norm_num)]
    norm_num [Real.sq_sqrt (Finset.sum_nonneg fun k _ => sq_nonneg (2 * ψ x k + s x * a x k))]
  simp_rw [e2, e1, ENNReal.one_rpow, one_mul]
  rfl

end SharpLSI
