import DGRHS.Gaussian.SharpnessCutoffDomination
import DGRHS.Gaussian.GaussianRieszFullPositivity

/-! Genuine positivity of the full singular centered form on bounded tests.
Only the Gaussian cutoffs use an L2 kernel operator. The full form is defined
by its proper pair integral and justified by actual L1 dominated convergence. -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology InnerProductSpace
namespace DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]

theorem sharpness_centered_riesz_bounded_form_nonneg (s : ℝ) (hs : 0 < s)
    (ha : 0 < (Fintype.card ι : ℝ)-s)
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M)
    (f : EuclideanSpace ℝ ι → ℝ) (hf : StronglyMeasurable f)
    (K : ℝ) (hK : 0 ≤ K) (hbound : ∀ x, ‖f x‖ ≤ K) :
    Integrable (fun p => hoeffdingCentered (gaussianRieszDensityMeasure ρ)
      (gaussianRieszPhysicalPair s) p * f p.1 * f p.2)
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)) ∧
    0 ≤ (∫ p, hoeffdingCentered (gaussianRieszDensityMeasure ρ)
      (gaussianRieszPhysicalPair s) p * f p.1 * f p.2
      ∂(gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)) := by
  have hc : 0 < Fintype.card ι := by
    exact_mod_cast (show (0 : ℝ) < Fintype.card ι by linarith)
  have : Nonempty ι := Fintype.card_pos_iff.mp hc
  let μ := gaussianRieszDensityMeasure ρ
  let B := gaussianRieszPhysicalPotentialConstant s M ι
  let η : ℕ → ℝ := fun j => 1 / ((j : ℝ)+1)
  have hη (j : ℕ) : 0 < η j := by dsimp [η]; positivity
  have hη0 : Tendsto η atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let H := hoeffdingCentered μ (gaussianRieszPhysicalPair s)
  let Hj := fun j => hoeffdingCentered μ (gaussianRieszTruncatedPair s (η j))
  let G := fun p => H p * f p.1 * f p.2
  let Gj := fun j p => Hj j p * f p.1 * f p.2
  let D := fun p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι => (gaussianRieszPhysicalPair s p + 3*B) * K^2
  have hm := sharpness_riesz_pair_mean_bound s hs ha ρ M hM hρ
  have hB : 0 ≤ B := hm.1.trans hm.2
  have hfm : StronglyMeasurable (fun p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι => f p.1) := hf.comp_measurable measurable_fst
  have hsm : StronglyMeasurable (fun p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι => f p.2) := hf.comp_measurable measurable_snd
  have hHm := stronglyMeasurable_hoeffdingCentered μ _ (stronglyMeasurable_gaussianRieszPhysicalPair s)
  have hGm : StronglyMeasurable G := (hHm.mul hfm).mul hsm
  have hi := sharpness_centered_riesz_integrable s hs ha ρ M hM hρ
  have hiG : Integrable G (μ.prod μ) := by
    apply (hi.norm.mul_const (K^2)).mono' hGm.aestronglyMeasurable
    apply Eventually.of_forall
    intro p
    change ‖H p * f p.1 * f p.2‖ ≤ ‖H p‖ * K^2
    rw [norm_mul, norm_mul]
    calc
      _ ≤ ‖H p‖ * K * K := by
        gcongr
        · exact hbound p.1
        · exact hbound p.2
      _ = _ := by ring
  have hDi : Integrable D (μ.prod μ) :=
    ((sharpness_riesz_pair_integrable s hs ha ρ M hM hρ).add (integrable_const (3*B))).mul_const (K^2)
  have ht : Tendsto (fun j => ∫ p, Gj j p ∂μ.prod μ) atTop (𝓝 (∫ p, G p ∂μ.prod μ)) := by
    apply tendsto_integral_of_dominated_convergence D
    · intro j
      exact (((stronglyMeasurable_hoeffdingCentered μ _
        (stronglyMeasurable_gaussianRieszTruncatedPair s (η j) hs (hη j))).mul hfm).mul hsm).aestronglyMeasurable
    · exact hDi
    · intro j
      filter_upwards [sharpness_centered_cutoff_domination s (η j) hs (hη j) ha ρ M hM hρ] with p hp
      change ‖Hj j p * f p.1 * f p.2‖ ≤ _
      rw [norm_mul, norm_mul]
      have hw : 0 ≤ gaussianRieszPhysicalPair s p := by unfold gaussianRieszPhysicalPair; positivity
      dsimp [D, B]
      calc
        _ ≤ (gaussianRieszPhysicalPair s p + 3*gaussianRieszPhysicalPotentialConstant s M ι) * K * K := by
          gcongr
          · exact hp
          · exact hbound p.1
          · exact hbound p.2
        _ = _ := by ring
    · filter_upwards [ae_gaussianRieszDensity_pair_ne ρ] with p hp
      exact ((sharpness_tendsto_riesz_centered_cutoff s hs ha ρ M hM hρ η hη hη0 p hp).mul
        tendsto_const_nhds).mul tendsto_const_nhds
  have hf2 : MemLp f 2 μ := (memLp_const K).of_le hf.aestronglyMeasurable
    (Eventually.of_forall fun x => by simpa only [Real.norm_of_nonneg hK] using hbound x)
  let v := hf2.toLp f
  have hnonneg (j : ℕ) : 0 ≤ ∫ p, Gj j p ∂μ.prod μ := by
    have hj := memLp_gaussianRieszCenteredTruncatedPair s (η j) hs (hη j) μ
    have he : (∫ p, Gj j p ∂μ.prod μ) =
        inner ℝ (DGRHS.Kernel.integralOperator (Hj j) hj v) v := by
      rw [DGRHS.Kernel.inner_integralOperator]
      apply integral_congr_ae
      filter_upwards [
        (measurePreserving_fst (μ := μ) (ν := μ)).quasiMeasurePreserving.ae hf2.coeFn_toLp,
        (measurePreserving_snd (μ := μ) (ν := μ)).quasiMeasurePreserving.ae hf2.coeFn_toLp] with p hp1 hp2
      change Hj j p * f p.1 * f p.2 = Hj j p * v p.1 * v p.2
      rw [hp1, hp2]
    rw [he, real_inner_comm]
    exact gaussianRieszTruncatedOperator_positive s (η j) hs (hη j) ρ v
  exact ⟨hiG, ge_of_tendsto ht (Eventually.of_forall hnonneg)⟩

end DGRHS.Gaussian
#print axioms DGRHS.Gaussian.sharpness_centered_riesz_bounded_form_nonneg
#check @DGRHS.Gaussian.sharpness_centered_riesz_bounded_form_nonneg
