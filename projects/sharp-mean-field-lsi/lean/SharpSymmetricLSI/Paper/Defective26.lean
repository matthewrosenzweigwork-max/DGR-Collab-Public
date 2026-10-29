import SharpSymmetricLSI.Paper.Defective25

/-!
# R03 (Proposition 2.2), part 26: the regularized law

For `ν = Q · Leb = ψ_n(f)² P_N / Z`:
* `isSymmetricMeasure_Qreg`: `ν` is symmetric when `f` is;
* `klDiv_Qreg_gibbs_ne_top`: `H(ν | P_N) < ∞`;
* `fisher_Qreg_eq`: `∑ᵢ E_ν |sᵢ|² = (4/Z) ℰ_N(ψ_n(f))`;
* `klDiv_Qreg_gibbs_eq`: `H(ν | P_N) = Ent_{P_N}(ψ_n(f)²) / Z`.
-/

open MeasureTheory Filter Topology InformationTheory ProbabilityTheory
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-- `H(ρP | P) ≤ B log B + 1` for a probability density `0 ≤ ρ ≤ B`, `B ≥ 1`. -/
theorem klDiv_withDensity_le {α : Type*} [MeasurableSpace α] {P : Measure α} [IsProbabilityMeasure P]
    {ρ : α → ℝ} (hρm : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) {B : ℝ} (hB : 1 ≤ B) (hρB : ∀ x, ρ x ≤ B)
    [IsFiniteMeasure (P.withDensity fun x => ENNReal.ofReal (ρ x))] :
    klDiv (P.withDensity fun x => ENNReal.ofReal (ρ x)) P ≤ ENNReal.ofReal (B * Real.log B + 1) := by
  have hac : P.withDensity (fun x => ENNReal.ofReal (ρ x)) ≪ P := withDensity_absolutelyContinuous _ _
  have hrn := Measure.rnDeriv_withDensity P hρm.ennreal_ofReal
  rw [klDiv_eq_lintegral_klFun_of_ac hac]
  calc ∫⁻ x, ENNReal.ofReal (klFun ((P.withDensity fun x => ENNReal.ofReal (ρ x)).rnDeriv P x).toReal) ∂P
      = ∫⁻ x, ENNReal.ofReal (klFun (ρ x)) ∂P := by
        refine lintegral_congr_ae ?_
        filter_upwards [hrn] with x hx
        rw [hx, ENNReal.toReal_ofReal (hρ0 x)]
    _ ≤ ∫⁻ _, ENNReal.ofReal (B * Real.log B + 1) ∂P :=
        lintegral_mono fun x => ENNReal.ofReal_le_ofReal (klFun_le_of_le (hρ0 x) (hρB x) hB)
    _ = _ := by simp

theorem deriv_psiSqR_eq (n : ℕ) (t : ℝ) :
    deriv (psiSqR n) t = 2 * psiReg n t * deriv (psiReg n) t := by
  have h : psiSqR n = psiReg n ^ 2 := by funext t; rw [Pi.pow_apply, psiSqR_eq]
  have hd := (((contDiff_psiReg n).differentiable one_ne_zero) t).hasDerivAt.pow 2
  rw [h, hd.deriv]
  first | (norm_num; done) | (norm_num; ring) | ring

section reg
variable (hyp : Hyp V W KV KW) {N : ℕ} {f : Config N d → ℝ} (hf : MemH1C (gibbs V W N) f)
  (hfm : Measurable f)
include hyp hf hfm

theorem isSymmetricMeasure_Qreg (hsym : IsSymmetric f) (n : ℕ) :
    IsSymmetricMeasure ((volume : Measure (Config N d)).withDensity
      fun X => ENNReal.ofReal (Qreg V W n f X)) := by
  intro σ
  have hQm := measurable_Qreg hyp hf hfm n
  change ((volume : Measure (Config N d)).withDensity fun X => ENNReal.ofReal (Qreg V W n f X)).map
    (permEquiv σ) = _
  rw [map_withDensity_equiv (permEquiv σ) _ ((hQm).ennreal_ofReal), volume_map_perm]
  congr 1; funext X
  simp only [Function.comp_apply, permEquiv_symm_apply, Qreg_perm hsym]

theorem klDiv_Qreg_gibbs_ne_top (n : ℕ) :
    klDiv ((volume : Measure (Config N d)).withDensity fun X => ENNReal.ofReal (Qreg V W n f X))
      (gibbs V W N) ≠ ⊤ := by
  haveI := gibbs_isProbabilityMeasure hyp N
  haveI := isProbabilityMeasure_Qreg hyp hf hfm n
  have hZ0 : 0 < Zreg V W n f := lt_of_lt_of_le (by positivity) (Zreg_bounds hyp hf n).1
  have hm : Measurable fun X => regF n f X ^ 2 / ∫ Y, regF n f Y ^ 2 ∂gibbs V W N :=
    (((contDiff_psiReg n).continuous.measurable.comp hfm).pow_const 2).div_const _
  set B := max (((n : ℝ) + 2) ^ 2 * ((n : ℝ) + 1) ^ 2) 1
  rw [← sqMeasure_regF_eq hyp hf hfm n]
  haveI : IsFiniteMeasure ((gibbs V W N).withDensity fun X =>
      ENNReal.ofReal (regF n f X ^ 2 / ∫ Y, regF n f Y ^ 2 ∂gibbs V W N)) := by
    have h := sqMeasure_regF_eq hyp hf hfm n
    unfold sqMeasure at h
    rw [h]; infer_instance
  refine ne_top_of_le_ne_top ENNReal.ofReal_ne_top (klDiv_withDensity_le (B := B) hm
    (fun X => div_nonneg (sq_nonneg _) (integral_nonneg fun _ => sq_nonneg _)) (le_max_right _ _)
    fun X => ?_)
  rw [← Zreg_eq hyp hf n, div_le_iff₀ hZ0]
  have h1 : regF n f X ^ 2 ≤ ((n : ℝ) + 2) ^ 2 := by
    simp only [regF]; rw [← psiSqR_eq]; exact (psiSqR_bounds n (f X)).2
  have h2 : 1 / ((n : ℝ) + 1) ^ 2 ≤ Zreg V W n f := (Zreg_bounds hyp hf n).1
  have h3 : ((n : ℝ) + 2) ^ 2 * ((n : ℝ) + 1) ^ 2 * (1 / ((n : ℝ) + 1) ^ 2) = ((n : ℝ) + 2) ^ 2 := by
    field_simp
  calc regF n f X ^ 2 ≤ ((n : ℝ) + 2) ^ 2 * ((n : ℝ) + 1) ^ 2 * (1 / ((n : ℝ) + 1) ^ 2) := by
        rw [h3]; exact h1
    _ ≤ B * Zreg V W n f := mul_le_mul (le_max_left _ _) h2 (by positivity)
        (zero_le_one.trans (le_max_right _ _))

/-- **`H(ν | P_N) = Ent_{P_N}(ψ_n(f)²) / Z`** (when the entropy is positive). -/
theorem klDiv_Qreg_gibbs_eq (n : ℕ) (hent : 0 < ent (gibbs V W N) (fun X => regF n f X ^ 2)) :
    klDiv ((volume : Measure (Config N d)).withDensity fun X => ENNReal.ofReal (Qreg V W n f X))
      (gibbs V W N) = ENNReal.ofReal (Zreg V W n f)⁻¹ * ent (gibbs V W N) (fun X => regF n f X ^ 2) := by
  rw [← sqMeasure_regF_eq hyp hf hfm n, Zreg_eq hyp hf n]
  exact (sqMeasure_props hyp ((contDiff_psiReg n).continuous.measurable.comp hfm)
    (memH1C_regF hyp hf n) hent).2.2.1

/-- **`∑ᵢ E_ν |sᵢ|² = (4/Z) ℰ_N(ψ_n(f))`.** -/
theorem fisher_Qreg_eq {g : UnitAddTorus (Fin N × Fin d) → Fin N × Fin d → ℝ}
    (hw : IsWeakGrad (f ∘ unflat) g) (hgm : ∀ p, Measurable fun y => g y p) (n : ℕ) :
    ∑ i, ∑ k, ∫⁻ X, ENNReal.ofReal (sfun n f g i k X ^ 2)
        ∂((volume : Measure (Config N d)).withDensity fun X => ENNReal.ofReal (Qreg V W n f X)) =
      ENNReal.ofReal (4 / Zreg V W n f) * energy V W N (regF n f) := by
  obtain ⟨c1, C1, hc1, h1⟩ := gibbsDensR_bounds hyp (N := N)
  have hZ0 : 0 < Zreg V W n f := lt_of_lt_of_le (by positivity) (Zreg_bounds hyp hf n).1
  have hwr := isWeakGrad_regF hyp hf n
  have hQm := measurable_Qreg hyp hf hfm n
  -- the energy on the configuration side
  have hE : energy V W N (regF n f) = ∫⁻ X, ENNReal.ofReal
      (sqNorm (weakGrad (regF n f ∘ unflat) (flat X))) * ENNReal.ofReal (gibbsDensR V W N X) := by
    rw [energy_eq hyp ⟨_, hwr⟩, measurableEmbedding_flat.lintegral_map, gibbs_eq_gibbsDensR hyp,
      lintegral_withDensity_eq_lintegral_mul_non_measurable _
        ((measurable_gibbsDensR hyp).ennreal_ofReal)
        (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
    refine lintegral_congr fun X => ?_
    rw [Pi.mul_apply, mul_comm]
  -- a.e. identification of the gradients
  have hgw : ∀ᵐ y ∂(volume : Measure (UnitAddTorus (Fin N × Fin d))),
      weakGrad (regF n f ∘ unflat) y = fun k => deriv (psiReg n) (f (unflat y)) * g y k := by
    filter_upwards [weakGrad_ae_eq hwr, weakGrad_ae_unique (isWeakGrad_weakGrad ⟨_, hw⟩) hw]
      with y h1 h2
    rw [h1, h2]
  have hgwX : ∀ᵐ X ∂(volume : Measure (Config N d)),
      weakGrad (regF n f ∘ unflat) (flat X) = fun k => deriv (psiReg n) (f X) * g (flat X) k :=
    (measurePreserving_flat' N).quasiMeasurePreserving.ae hgw
  have hsm : ∀ i k, Measurable (sfun n f g i k) := fun i k => by
    unfold sfun uReg
    exact ((((contDiff_psiSqR n).continuous_deriv le_rfl).measurable.comp hfm).mul
      ((hgm (i, k)).comp measurable_flat)).div ((contDiff_psiSqR n).continuous.measurable.comp hfm)
  have hFm : ∀ i k, Measurable fun X => ENNReal.ofReal (Qreg V W n f X) *
      ENNReal.ofReal (sfun n f g i k X ^ 2) := fun i k =>
    ((hQm).ennreal_ofReal).mul (((hsm i k).pow_const 2).ennreal_ofReal)
  have e1 : ∀ i k, ∫⁻ X, ENNReal.ofReal (sfun n f g i k X ^ 2)
      ∂((volume : Measure (Config N d)).withDensity fun X => ENNReal.ofReal (Qreg V W n f X)) =
      ∫⁻ X, ENNReal.ofReal (Qreg V W n f X) * ENNReal.ofReal (sfun n f g i k X ^ 2) := fun i k =>
    lintegral_withDensity_eq_lintegral_mul_non_measurable _ ((hQm).ennreal_ofReal)
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top) _
  simp_rw [e1]
  have e2 : ∑ i, ∑ k, ∫⁻ X, ENNReal.ofReal (Qreg V W n f X) * ENNReal.ofReal (sfun n f g i k X ^ 2) =
      ∫⁻ X, ∑ i, ∑ k, ENNReal.ofReal (Qreg V W n f X) * ENNReal.ofReal (sfun n f g i k X ^ 2) := by
    rw [lintegral_finset_sum _ fun i _ => Finset.measurable_sum _ fun k _ => hFm i k]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [lintegral_finset_sum _ fun k _ => hFm i k]
  rw [e2, hE, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr_ae ?_
  filter_upwards [hgwX] with X hX
  rw [hX]
  have hgD : 0 ≤ gibbsDensR V W N X := hc1.le.trans (h1 X).1
  have hp : 0 < psiReg n (f X) := by rw [psiReg_eq_sqrt]; exact Real.sqrt_pos.mpr (psiSqR_pos n _)
  have hQ0 : 0 ≤ Qreg V W n f X := by
    unfold Qreg uReg; exact div_nonneg (mul_nonneg (psiSqR_pos n _).le hgD) hZ0.le
  have hin : ∀ i, ∑ k, ENNReal.ofReal (Qreg V W n f X) * ENNReal.ofReal (sfun n f g i k X ^ 2) =
      ENNReal.ofReal (∑ k, Qreg V W n f X * sfun n f g i k X ^ 2) := fun i => by
    rw [ENNReal.ofReal_sum_of_nonneg fun k _ => mul_nonneg hQ0 (sq_nonneg _)]
    exact Finset.sum_congr rfl fun k _ => (ENNReal.ofReal_mul hQ0).symm
  simp_rw [hin]
  rw [← ENNReal.ofReal_sum_of_nonneg fun i _ => Finset.sum_nonneg fun k _ => mul_nonneg hQ0 (sq_nonneg _),
    ← ENNReal.ofReal_mul (show (0 : ℝ) ≤ sqNorm (fun k => deriv (psiReg n) (f X) * g (flat X) k) from
      Finset.sum_nonneg fun p _ => sq_nonneg _), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  simp only [sqNorm, Fintype.sum_prod_type]
  rw [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold Qreg sfun uReg
  rw [deriv_psiSqR_eq, psiSqR_eq]
  first | (field_simp; done) | (field_simp; ring)

end reg

end SharpLSI
