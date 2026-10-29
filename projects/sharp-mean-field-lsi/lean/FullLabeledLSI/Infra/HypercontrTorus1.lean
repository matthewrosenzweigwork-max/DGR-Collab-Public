import FullLabeledLSI.Infra.HypercontrTorusCalc
import FullLabeledLSI.Defs.F02_Constants
import SharpSymmetricLSI.Paper.R37Particle
import SharpSymmetricLSI.Infra.EntropyTensor

/-!
# One-particle classical eigen-structure on the torus

From a reference eigenbasis `(e, lam)` of `-L_μ` in `L²(μ)` (with `μ` equivalent to Haar measure), `C¹`
representatives `eC j` and a rate `a` with `ofReal a ≤ r_LS(μ)`, we derive the *classical* statements
used by the product-space Gross lemma:
* `memH1_of_C1T`: `C¹` functions lie in `H¹(μ)`;
* `classical_eigen`: `∫ ∇(eC j)·∇φ dμ = λ_j ∫ eC j φ dμ` for `C¹` test functions `φ`;
* `classical_lsi`: `Ent_μ(f²) ≤ (2/a) ∫ |∇f|² dμ` for `C¹` functions `f ≥ c > 0`.
-/

open MeasureTheory SharpLSI

namespace SharpLSI.FL.Gross

variable {d : ℕ}

/-- Squared classical gradient `Γ(f,g) = ∑_k ∂_k f ∂_k g` on `𝕋^d`. -/
noncomputable def GammaT (f g : Torus d → ℝ) (y : Torus d) : ℝ := ∑ k, dT f k y * dT g k y

lemma GammaT_comm (f g : Torus d → ℝ) : GammaT f g = GammaT g f := by
  funext y; unfold GammaT; exact Finset.sum_congr rfl fun k _ => mul_comm _ _

section OneParticle

variable {mu : Measure (Torus d)} [IsProbabilityMeasure mu]

lemma ae_dT_weakGrad (hac : mu ≪ volume) {f : Torus d → ℝ} (hf : C1T f) :
    ∀ᵐ y ∂mu, ∀ k, weakGrad f y k = dT f k y := by
  have := hac.ae_le (weakGrad_ae_eq_dT hf)
  filter_upwards [this] with y hy k
  exact congrFun hy k

lemma measurable_GammaT {f g : Torus d → ℝ} (hf : C1T f) (hg : C1T g) :
    Measurable (GammaT f g) := by
  unfold GammaT
  exact Finset.measurable_sum _ fun k _ => (hf.dT_measurable k).mul (hg.dT_measurable k)

lemma bounded_GammaT {f g : Torus d → ℝ} (hf : C1T f) (hg : C1T g) :
    ∃ K, ∀ y, |GammaT f g y| ≤ K := by
  choose Kf hKf using fun k => hf.dT_bounded k
  choose Kg hKg using fun k => hg.dT_bounded k
  refine ⟨∑ k, Kf k * Kg k, fun y => ?_⟩
  unfold GammaT
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [abs_mul]
  exact mul_le_mul (hKf k y) (hKg k y) (abs_nonneg _) ((abs_nonneg _).trans (hKf k y))

lemma memH1_of_C1T (hac : mu ≪ volume) {φ : Torus d → ℝ} (hφ : C1T φ) : MemH1 mu φ := by
  refine ⟨⟨_, isWeakGrad_of_contDiff hφ⟩, ?_, ?_⟩
  · obtain ⟨K, hK⟩ := hφ.bounded
    exact MemLp.of_bound hφ.measurable.aestronglyMeasurable K
      (Filter.Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hK y)
  · have hm : Measurable fun y => Real.sqrt (∑ k, dT φ k y ^ 2) :=
      (Finset.measurable_sum _ fun k _ => (hφ.dT_measurable k).pow_const 2).sqrt
    have hb : ∃ K, ∀ y, |Real.sqrt (∑ k, dT φ k y ^ 2)| ≤ K := by
      choose Kf hKf using fun k => hφ.dT_bounded k
      refine ⟨Real.sqrt (∑ k, Kf k ^ 2), fun y => ?_⟩
      rw [abs_of_nonneg (Real.sqrt_nonneg _)]
      refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun k _ => ?_)
      have := hKf k y
      nlinarith [abs_nonneg (dT φ k y), sq_abs (dT φ k y)]
    obtain ⟨K, hK⟩ := hb
    have hmem : MemLp (fun y => Real.sqrt (∑ k, dT φ k y ^ 2)) 2 mu :=
      MemLp.of_bound hm.aestronglyMeasurable K
        (Filter.Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hK y)
    refine hmem.ae_eq ?_
    filter_upwards [ae_dT_weakGrad hac hφ] with y hy
    simp only [sqNorm, hy]

/-- Classical form of the eigen-equation. -/
theorem classical_eigen (hac : mu ≪ volume) (hca : volume ≪ mu) {e : ℕ → Torus d → ℝ}
    {lam : ℕ → ℝ} (hb : IsRefEigenbasis mu e lam) {eC : ℕ → Torus d → ℝ}
    (hC1 : ∀ j, C1T (eC j)) (hae : ∀ j, eC j =ᵐ[mu] e j) (j : ℕ) {φ : Torus d → ℝ}
    (hφ : C1T φ) :
    ∫ y, GammaT (eC j) φ y ∂mu = lam j * ∫ y, eC j y * φ y ∂mu := by
  have h := hb.eigen j φ (memH1_of_C1T hac hφ)
  have hv : e j =ᵐ[volume] eC j := hca.ae_le (hae j).symm
  have hw : weakGrad (eC j) =ᵐ[volume] weakGrad (e j) :=
    (weakGrad_congr_ae (hb.memH1 j).1 hv).2
  have hw' : ∀ᵐ y ∂mu, ∀ k, weakGrad (e j) y k = dT (eC j) k y := by
    have h1 := hac.ae_le hw
    have h2 := ae_dT_weakGrad hac (hC1 j)
    filter_upwards [h1, h2] with y hy1 hy2 k
    rw [← congrFun hy1 k, hy2 k]
  have hφ' := ae_dT_weakGrad hac hφ
  have e1 : ∫ y, ∑ k, weakGrad (e j) y k * weakGrad φ y k ∂mu = ∫ y, GammaT (eC j) φ y ∂mu := by
    refine integral_congr_ae ?_
    filter_upwards [hw', hφ'] with y h1 h2
    unfold GammaT
    exact Finset.sum_congr rfl fun k _ => by rw [h1 k, h2 k]
  have e2 : ∫ y, e j y * φ y ∂mu = ∫ y, eC j y * φ y ∂mu := by
    refine integral_congr_ae ?_
    filter_upwards [hae j] with y hy
    rw [hy]
  rw [← e1, h, e2]

/-- Orthonormality of the `C¹` representatives. -/
theorem classical_orth {e : ℕ → Torus d → ℝ} {lam : ℕ → ℝ} (hb : IsRefEigenbasis mu e lam)
    {eC : ℕ → Torus d → ℝ} (hae : ∀ j, eC j =ᵐ[mu] e j) (i j : ℕ) :
    ∫ y, eC i y * eC j y ∂mu = if i = j then 1 else 0 := by
  rw [← hb.orthonormal i j]
  refine integral_congr_ae ?_
  filter_upwards [hae i, hae j] with y h1 h2
  rw [h1, h2]

/-- Classical form of the one-particle logarithmic Sobolev inequality. -/
theorem classical_lsi (hac : mu ≪ volume) {a : ℝ} (ha : 0 < a)
    (hrls : ENNReal.ofReal a ≤ rLS mu) {f : Torus d → ℝ} (hf : C1T f) {c : ℝ} (hc : 0 < c)
    (hfc : ∀ y, c ≤ f y) :
    entR mu (fun y => f y ^ 2) ≤ 2 / a * ∫ y, GammaT f f y ∂mu := by
  have hm : Measurable f := hf.measurable
  obtain ⟨K, hK⟩ := hf.bounded
  have hsqint : Integrable (fun y => f y ^ 2) mu :=
    Integrable.of_bound (hm.pow_const 2).aestronglyMeasurable (K ^ 2)
      (Filter.Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hK y) 2)
  have hlogint : Integrable (fun y => f y ^ 2 * Real.log (f y ^ 2)) mu := by
    have hc2 : 0 < c ^ 2 := by positivity
    refine Integrable.of_bound ((hm.pow_const 2).mul
      (Real.measurable_log.comp (hm.pow_const 2))).aestronglyMeasurable
      (K ^ 2 * (|Real.log (c ^ 2)| + |Real.log (K ^ 2)|)) (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs]
    have hfy : c ^ 2 ≤ f y ^ 2 := pow_le_pow_left₀ hc.le (hfc y) 2
    have hfK : f y ^ 2 ≤ K ^ 2 := by
      have := hK y
      rw [abs_of_pos (lt_of_lt_of_le hc (hfc y))] at this
      exact pow_le_pow_left₀ (lt_of_lt_of_le hc (hfc y)).le this 2
    exact abs_mul_log_le hc2 hfy hfK
  have hent : ent mu (fun y => f y ^ 2) = ENNReal.ofReal (entR mu fun y => f y ^ 2) :=
    ent_eq_formula mu (fun y => f y ^ 2) (fun y => sq_nonneg _) hsqint hlogint
  have hGint : Integrable (fun y => GammaT f f y) mu := by
    obtain ⟨K', hK'⟩ := bounded_GammaT hf hf
    exact Integrable.of_bound (measurable_GammaT hf hf).aestronglyMeasurable K'
      (Filter.Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hK' y)
  have hG0 : 0 ≤ ∫ y, GammaT f f y ∂mu :=
    integral_nonneg fun y => Finset.sum_nonneg fun k _ => mul_self_nonneg _
  by_cases hE : entR mu (fun y => f y ^ 2) ≤ 0
  · exact hE.trans (by positivity)
  · rw [not_le] at hE
    have hentpos : 0 < ent mu (fun y => f y ^ 2) := by
      rw [hent]; exact ENNReal.ofReal_pos.mpr hE
    have hmem : f ∈ {f : Torus d → ℝ | MemH1 mu f ∧ 0 < ent mu (fun x => f x ^ 2)} :=
      ⟨memH1_of_C1T hac hf, hentpos⟩
    have h1 : ENNReal.ofReal a ≤ 2 * dirichlet mu f / ent mu (fun x => f x ^ 2) :=
      hrls.trans (iInf₂_le f hmem)
    have hdir : dirichlet mu f = ENNReal.ofReal (∫ y, GammaT f f y ∂mu) := by
      unfold dirichlet
      rw [ofReal_integral_eq_lintegral_ofReal hGint (Filter.Eventually.of_forall fun y =>
        Finset.sum_nonneg fun k _ => mul_self_nonneg _)]
      refine lintegral_congr_ae ?_
      filter_upwards [ae_dT_weakGrad hac hf] with y hy
      unfold sqNorm GammaT
      congr 1
      exact Finset.sum_congr rfl fun k _ => by rw [hy k]; ring
    rw [hent, hdir] at h1
    have hne : ENNReal.ofReal (entR mu fun y => f y ^ 2) ≠ 0 := (ENNReal.ofReal_pos.mpr hE).ne'
    rw [ENNReal.le_div_iff_mul_le (Or.inl hne) (Or.inl ENNReal.ofReal_ne_top)] at h1
    have h2 : a * entR mu (fun y => f y ^ 2) ≤ 2 * ∫ y, GammaT f f y ∂mu := by
      have := ENNReal.toReal_mono (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top) h1
      rwa [← ENNReal.ofReal_mul ha.le, ENNReal.toReal_ofReal (by positivity),
        ENNReal.toReal_mul, ENNReal.toReal_ofReal hG0, ENNReal.toReal_ofNat] at this
    rw [div_mul_eq_mul_div, le_div_iff₀ ha]
    linarith

end OneParticle

end SharpLSI.FL.Gross
