import FullLabeledLSI.Infra.GaussianTilt
import FullLabeledLSI.Infra.GaussianLSIBlock
import FullLabeledLSI.Infra.GaussianEntProd
import FullLabeledLSI.Infra.HypercontrTorus3
import FullLabeledLSI.Infra.HypercontrTorus5
import FullLabeledLSI.Paper.Hybrid63Defs
import FullLabeledLSI.Paper.HybridRLS
import Mathlib.Analysis.Distribution.TemperateGrowth

/-!
# Hybrid tilted log-Sobolev inequality (alternative route), part A: generic tools

* Gaussian moments: `(1+‖g‖)^k` is `gpi M`-integrable; polynomially bounded functions are integrable.
* `tg_bound`: functions of temperate growth and their derivatives are polynomially bounded.
* `torus_lsi_bdd`: the torus log-Sobolev inequality for every bounded `C¹` function (no positive
  lower bound), by the regularisation `√(F² + ε²)`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace SharpLSI.FL.HLA

open SharpLSI

/-! ### Gaussian moments -/

theorem one_add_pow_le (t : ℝ) (ht : 0 ≤ t) (k : ℕ) : (1 + t) ^ k ≤ 2 ^ k * (1 + t ^ k) := by
  rcases le_total t 1 with h | h
  · calc (1 + t) ^ k ≤ 2 ^ k := pow_le_pow_left₀ (by linarith) (by linarith) k
      _ ≤ 2 ^ k * (1 + t ^ k) := by
        have : 0 ≤ t ^ k := pow_nonneg ht k
        nlinarith [pow_pos (by norm_num : (0:ℝ) < 2) k]
  · calc (1 + t) ^ k ≤ (2 * t) ^ k := pow_le_pow_left₀ (by linarith) (by linarith) k
      _ = 2 ^ k * t ^ k := mul_pow _ _ _
      _ ≤ 2 ^ k * (1 + t ^ k) := by
        have := pow_pos (by norm_num : (0:ℝ) < 2) k
        nlinarith [pow_nonneg ht k]

theorem integrable_abs_pow_gaussian (k : ℕ) :
    Integrable (fun x : ℝ => |x| ^ k) (gaussianReal 0 1) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · have := (memLp_id_gaussianReal (μ := 0) (v := 1) k).integrable_norm_pow hk.ne'
    simpa using this

theorem norm_pow_le_sum_abs_pow {M : ℕ} (g : Fin M → ℝ) (k : ℕ) (hk : 0 < k) :
    ‖g‖ ^ k ≤ ∑ m, |g m| ^ k := by
  rcases isEmpty_or_nonempty (Fin M) with hJ | hJ
  · have : g = 0 := Subsingleton.elim _ _
    simp [this, hk.ne']
  · obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty
      (fun b => ‖g b‖₊)
    have hn : ‖g‖ = |g i| := by
      rw [← Real.norm_eq_abs, ← coe_nnnorm, Pi.nnnorm_def, hi]
      simp
    rw [hn]
    exact Finset.single_le_sum (f := fun m => |g m| ^ k) (fun m _ => by positivity)
      (Finset.mem_univ i)

theorem integrable_norm_pow_gpi (M k : ℕ) :
    Integrable (fun g : Fin M → ℝ => ‖g‖ ^ k) (gpi M) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  refine Integrable.mono' (g := fun g : Fin M → ℝ => ∑ m, |g m| ^ k)
    (integrable_finsetSum Finset.univ (fun m _ => ?_)) (by fun_prop)
    (Eventually.of_forall fun g => ?_)
  · exact (measurePreserving_eval (fun _ : Fin M => gaussianReal 0 1) m).integrable_comp_of_integrable
      (integrable_abs_pow_gaussian k)
  · rw [norm_pow, norm_norm]
    exact norm_pow_le_sum_abs_pow g k hk

theorem integrable_one_add_norm_pow (M k : ℕ) :
    Integrable (fun g : Fin M → ℝ => (1 + ‖g‖) ^ k) (gpi M) := by
  refine Integrable.mono' (((integrable_const (1:ℝ)).add (integrable_norm_pow_gpi M k)).const_mul
    ((2:ℝ) ^ k)) (by fun_prop) (Eventually.of_forall fun g => ?_)
  rw [Real.norm_of_nonneg (by positivity)]
  exact one_add_pow_le _ (norm_nonneg g) k

/-- Polynomially bounded measurable functions are `gpi M`-integrable. -/
theorem integrable_of_poly {M : ℕ} {f : (Fin M → ℝ) → ℝ} (hf : AEStronglyMeasurable f (gpi M))
    (C : ℝ) (k : ℕ) (hb : ∀ g, |f g| ≤ C * (1 + ‖g‖) ^ k) : Integrable f (gpi M) :=
  Integrable.mono' ((integrable_one_add_norm_pow M k).const_mul C) hf
    (Eventually.of_forall fun g => by rw [Real.norm_eq_abs]; exact hb g)

/-! ### Temperate growth -/

theorem tg_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ}
    (hf : f.HasTemperateGrowth) :
    ∃ (k : ℕ) (C : ℝ), 0 ≤ C ∧ (∀ x, |f x| ≤ C * (1 + ‖x‖) ^ k) ∧
      ∀ x, ‖fderiv ℝ f x‖ ≤ C * (1 + ‖x‖) ^ k := by
  obtain ⟨k, C, hC, h⟩ := hf.norm_iteratedFDeriv_le_uniform 1
  refine ⟨k, C, hC, fun x => ?_, fun x => ?_⟩
  · have := h 0 (by norm_num) x
    simpa [norm_iteratedFDeriv_zero] using this
  · have := h 1 le_rfl x
    rwa [← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_zero] at this


/-! ### The torus log-Sobolev inequality for bounded `C¹` functions -/

section torus
open SharpLSI.FL.Gross

variable {N d : ℕ} {mu : Measure (Torus d)} [IsProbabilityMeasure mu]

theorem contDiff_sqrt_sq_add (ε : ℝ) (hε : 0 < ε) :
    ContDiff ℝ 1 (fun s : ℝ => Real.sqrt (s ^ 2 + ε ^ 2)) :=
  ((contDiff_id.pow 2).add contDiff_const).sqrt (fun s => by positivity)

theorem deriv_sqrt_sq_add_sq_le (ε : ℝ) (hε : 0 < ε) (s : ℝ) :
    deriv (fun s : ℝ => Real.sqrt (s ^ 2 + ε ^ 2)) s *
      deriv (fun s : ℝ => Real.sqrt (s ^ 2 + ε ^ 2)) s ≤ 1 := by
  have hb : 0 < s ^ 2 + ε ^ 2 := by positivity
  have h1 : HasDerivAt (fun s : ℝ => s ^ 2 + ε ^ 2) (2 * s) s := by
    simpa using (hasDerivAt_pow 2 s).add_const (ε ^ 2)
  have h2 := h1.sqrt hb.ne'
  rw [h2.deriv]
  have hs : Real.sqrt (s ^ 2 + ε ^ 2) ^ 2 = s ^ 2 + ε ^ 2 := Real.sq_sqrt hb.le
  have hpos : 0 < Real.sqrt (s ^ 2 + ε ^ 2) := Real.sqrt_pos.2 hb
  have : 2 * s / (2 * Real.sqrt (s ^ 2 + ε ^ 2)) * (2 * s / (2 * Real.sqrt (s ^ 2 + ε ^ 2))) =
      s ^ 2 / (s ^ 2 + ε ^ 2) := by
    rw [div_mul_div_comm, show 2 * s * (2 * s) = 4 * s ^ 2 by ring,
      show 2 * Real.sqrt (s ^ 2 + ε ^ 2) * (2 * Real.sqrt (s ^ 2 + ε ^ 2)) =
        4 * Real.sqrt (s ^ 2 + ε ^ 2) ^ 2 by ring, hs]
    field_simp
  rw [this, div_le_one hb]
  nlinarith [sq_nonneg ε]

/-- Torus LSI for the regularised function. -/
theorem torus_lsi_reg (hac : mu ≪ volume) {a : ℝ} (ha : 0 < a) (hrls : ENNReal.ofReal a ≤ rLS mu)
    {F : Config N d → ℝ} (hF : C1C F) {ε : ℝ} (hε : 0 < ε) :
    a * entR (Measure.pi fun _ : Fin N => mu) (fun x => F x ^ 2 + ε ^ 2) ≤
      2 * ∫ x, gradPair F F x ∂(Measure.pi fun _ : Fin N => mu) := by
  set ψ : ℝ → ℝ := fun s => Real.sqrt (s ^ 2 + ε ^ 2) with hψ
  have hψc : ContDiff ℝ 1 ψ := contDiff_sqrt_sq_add ε hε
  have hG : C1C (ψ ∘ F) := hF.comp hψc
  obtain ⟨K, hK⟩ := hF.bounded
  have hc : 0 < ε := hε
  have hFc : ∀ x, ε ≤ (ψ ∘ F) x := fun x => by
    simp only [Function.comp, hψ]
    calc ε = Real.sqrt (ε ^ 2) := (Real.sqrt_sq hε.le).symm
      _ ≤ _ := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (F x)])
  have hFB : ∀ x, (ψ ∘ F) x ≤ Real.sqrt (K ^ 2 + ε ^ 2) := fun x => by
    simp only [Function.comp, hψ]
    refine Real.sqrt_le_sqrt ?_
    have := hK x
    nlinarith [sq_abs (F x), abs_nonneg (F x)]
  have key := torus_lsi hac ha hrls hG hc hFc hFB
  have hsq : (fun x => (ψ ∘ F) x ^ 2) = fun x => F x ^ 2 + ε ^ 2 := by
    funext x
    simp only [Function.comp, hψ]
    exact Real.sq_sqrt (by positivity)
  rw [hsq] at key
  have hle : ∫ x, gradPair (ψ ∘ F) (ψ ∘ F) x ∂(Measure.pi fun _ : Fin N => mu) ≤
      ∫ x, gradPair F F x ∂(Measure.pi fun _ : Fin N => mu) := by
    obtain ⟨K1, hK1⟩ := bounded_gradPair hF hF
    obtain ⟨K2, hK2⟩ := bounded_gradPair hG hG
    refine integral_mono (integrable_of_bdd (measurable_gradPair hG hG) hK2)
      (integrable_of_bdd (measurable_gradPair hF hF) hK1) fun x => ?_
    rw [gradPair_comp_comp hF hψc hψc x]
    have h0 := gradPair_nonneg_self F x
    have := deriv_sqrt_sq_add_sq_le ε hε (F x)
    nlinarith
  have h2 : a * entR (Measure.pi fun _ : Fin N => mu) (fun x => F x ^ 2 + ε ^ 2) ≤
      2 * ∫ x, gradPair (ψ ∘ F) (ψ ∘ F) x ∂(Measure.pi fun _ : Fin N => mu) := by
    have := mul_le_mul_of_nonneg_left key ha.le
    rw [← mul_assoc, mul_div_cancel₀ _ ha.ne'] at this
    simpa [mul_comm] using this
  linarith

theorem tendsto_entR_add_sq {F : Config N d → ℝ} (hF : C1C F) :
    Tendsto (fun ε : ℝ => entR (Measure.pi fun _ : Fin N => mu) (fun x => F x ^ 2 + ε ^ 2))
      (𝓝 0) (𝓝 (entR (Measure.pi fun _ : Fin N => mu) (fun x => F x ^ 2))) := by
  set Q : Measure (Config N d) := Measure.pi fun _ : Fin N => mu with hQ
  obtain ⟨K, hK⟩ := hF.bounded
  have hm : Measurable F := hF.measurable
  -- first part
  have hcomp : IsCompact (Set.Icc (0 : ℝ) (K ^ 2 + 1)) := isCompact_Icc
  obtain ⟨B, hB⟩ := hcomp.exists_bound_of_continuousOn
    (Real.continuous_mul_log.continuousOn (s := Set.Icc (0 : ℝ) (K ^ 2 + 1)))
  have hT1 : Tendsto (fun ε : ℝ => ∫ x, (F x ^ 2 + ε ^ 2) * Real.log (F x ^ 2 + ε ^ 2) ∂Q)
      (𝓝 0) (𝓝 (∫ x, F x ^ 2 * Real.log (F x ^ 2) ∂Q)) := by
    have := continuousAt_of_dominated (μ := Q) (x₀ := (0 : ℝ))
      (F := fun ε x => (F x ^ 2 + ε ^ 2) * Real.log (F x ^ 2 + ε ^ 2)) (bound := fun _ => B)
      (Eventually.of_forall fun ε => (Real.continuous_mul_log.comp_aestronglyMeasurable
        ((hm.pow_const 2).add_const _).aestronglyMeasurable))
      (by
        filter_upwards [Metric.ball_mem_nhds (0 : ℝ) one_pos] with ε hε
        refine Eventually.of_forall fun x => ?_
        have hε1 : ε ^ 2 ≤ 1 := by
          have := abs_lt.1 (by simpa [Metric.mem_ball, Real.dist_eq] using hε : |ε| < 1)
          nlinarith [this.1, this.2]
        have hmem : F x ^ 2 + ε ^ 2 ∈ Set.Icc (0 : ℝ) (K ^ 2 + 1) := by
          refine ⟨by positivity, ?_⟩
          have := hK x
          nlinarith [sq_abs (F x), abs_nonneg (F x)]
        simpa [Real.norm_eq_abs] using hB _ hmem)
      (integrable_const B)
      (Eventually.of_forall fun x => (Real.continuous_mul_log.comp
        ((continuous_const.add (continuous_id.pow 2)))).continuousAt)
    simpa using this.tendsto
  have hint : ∀ ε : ℝ, ∫ x, (F x ^ 2 + ε ^ 2) ∂Q = (∫ x, F x ^ 2 ∂Q) + ε ^ 2 := by
    intro ε
    rw [integral_add (hF.mul hF |>.integrable.congr (Eventually.of_forall fun x => by simp [sq]))
      (integrable_const _)]
    simp
    rfl
  have hT2 : Tendsto (fun ε : ℝ => (∫ x, (F x ^ 2 + ε ^ 2) ∂Q) *
      Real.log (∫ x, (F x ^ 2 + ε ^ 2) ∂Q)) (𝓝 0)
      (𝓝 ((∫ x, F x ^ 2 ∂Q) * Real.log (∫ x, F x ^ 2 ∂Q))) := by
    simp_rw [hint]
    have : Continuous fun ε : ℝ => ((∫ x, F x ^ 2 ∂Q) + ε ^ 2) *
        Real.log ((∫ x, F x ^ 2 ∂Q) + ε ^ 2) :=
      Real.continuous_mul_log.comp (continuous_const.add (continuous_id.pow 2))
    simpa using this.tendsto 0
  exact hT1.sub hT2

/-- **Torus log-Sobolev inequality for bounded `C¹` functions** (no positive lower bound). -/
theorem torus_lsi_bdd (hac : mu ≪ volume) {a : ℝ} (ha : 0 < a) (hrls : ENNReal.ofReal a ≤ rLS mu)
    {F : Config N d → ℝ} (hF : C1C F) :
    a * entR (Measure.pi fun _ : Fin N => mu) (fun x => F x ^ 2) ≤
      2 * ∫ x, gradPair F F x ∂(Measure.pi fun _ : Fin N => mu) := by
  have hlim := (tendsto_entR_add_sq (mu := mu) hF).const_mul a
  have hlim' : Tendsto (fun ε : ℝ => a * entR (Measure.pi fun _ : Fin N => mu)
      (fun x => F x ^ 2 + ε ^ 2)) (𝓝[>] 0) (𝓝 (a * entR (Measure.pi fun _ : Fin N => mu)
        (fun x => F x ^ 2))) := hlim.mono_left nhdsWithin_le_nhds
  refine le_of_tendsto hlim' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact torus_lsi_reg hac ha hrls hF hε

end torus

end SharpLSI.FL.HLA
