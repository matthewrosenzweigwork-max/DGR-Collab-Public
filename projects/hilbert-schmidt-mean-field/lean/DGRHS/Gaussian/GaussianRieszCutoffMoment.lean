import DGRHS.Gaussian.GaussianRieszMasterData

/-! True uniform centered cutoff exponential moments derived from the actual
physical master fields. The constants and low scale are constructed here. -/
noncomputable section
open MeasureTheory Real
open scoped ENNReal
namespace DGRHS.Gaussian
open DGRHS.Concentration
variable {ι : Type*} [Fintype ι]

lemma measurable_physical_iidNegativeStatistic {X : Type*} [MeasurableSpace X]
    (n : ℕ) (W : X × X → ℝ) (hW : Measurable W) :
    Measurable (iidNegativeStatistic n W) := by
  classical
  unfold iidNegativeStatistic iidCoupledSum DGRHS.Decoupling.offDiagonalSum
  have hm : Measurable (fun ω : Fin n → X => ∑ i : Fin n, ∑ j : Fin n,
      if i ≠ j then W (ω i,ω j) else 0) := by
    apply Finset.measurable_sum
    intro i hi
    apply Finset.measurable_sum
    intro j hj
    by_cases hij : i ≠ j
    · simp only [if_pos hij]
      exact hW.comp ((measurable_pi_apply i).prodMk (measurable_pi_apply j))
    · simp only [if_neg hij]
      exact measurable_const
  exact hm.neg.div_const _

lemma measurable_gaussianRieszCutoff_exponent (s η β : ℝ) (hs : 0 < s) (hη : 0 < η)
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ] (n : ℕ) :
    Measurable (fun ω => β*iidNegativeStatistic n (hoeffdingCentered μ (gaussianRieszTruncatedPair s η)) ω) :=
  (measurable_physical_iidNegativeStatistic n _
    (stronglyMeasurable_hoeffdingCentered μ _
      (stronglyMeasurable_gaussianRieszTruncatedPair s η hs hη)).measurable).const_mul β

theorem gaussianRieszCutoff_uniform_small_scale_exponential (s β : ℝ) (hs : 0 < s) (hβ : 0 ≤ β)
    (ha : 0 < (Fintype.card ι : ℝ)/2-s)
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] (hρ : ∀ᵐ x ∂volume, ρ x ≤ M) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∃ C : ℝ, ∀ η : ℝ, 0 < η → η ≤ δ → ∀ n : ℕ, 1 ≤ n →
      Integrable (fun ω => Real.exp (β*iidNegativeStatistic n
        (hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianRieszTruncatedPair s η)) ω))
          (Measure.pi (fun _ : Fin n => gaussianRieszDensityMeasure ρ)) ∧
      (∫ ω, Real.exp (β*iidNegativeStatistic n
        (hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianRieszTruncatedPair s η)) ω)
          ∂Measure.pi (fun _ : Fin n => gaussianRieszDensityMeasure ρ)) ≤ C := by
  let μ := gaussianRieszDensityMeasure ρ
  obtain ⟨δ,hδ,hδ1,hrow,hop⟩ := exists_gaussianRieszMaster_scale (ι := ι) s β M hM ha
  let A := 1+4*β*gaussianRieszShortConstant s M ι
  let u₀ := 1+8*β*(gaussianRieszSourceCoefficient s/s*δ^(-s))
  have hc : 0 ≤ gaussianRieszShortConstant s M ι := by
    have hp := (gaussianRieszSourceCoefficient_pos s hs).le
    have hd : 0 < (Fintype.card ι : ℝ)-s := by linarith
    unfold gaussianRieszShortConstant
    positivity
  have hA : 0 < A := by dsimp [A];positivity
  have hAcontrol : 4*β*gaussianRieszShortConstant s M ι ≤ A := by dsimp [A];linarith
  have hD : 0 ≤ gaussianRieszSourceCoefficient s/s*δ^(-s) := by
    have hp := (gaussianRieszSourceCoefficient_pos s hs).le
    positivity
  have hu₀ : 1 ≤ u₀ := by
    have hh := mul_nonneg (by positivity : 0 ≤ 8*β) hD
    dsimp [u₀]
    linarith
  have hlow : 8*β*(gaussianRieszSourceCoefficient s/s*δ^(-s)) ≤ u₀ := by dsimp [u₀];linarith
  let I := {η : ℝ // 0 < η ∧ η ≤ δ}
  let X := fun (θ : I) (n : ℕ) (ω : Fin n → EuclideanSpace ℝ ι) =>
    β*iidNegativeStatistic n (hoeffdingCentered μ (gaussianRieszTruncatedPair s θ.val)) ω
  have hX (θ : I) (n : ℕ) (hn : 1 ≤ n) : AEMeasurable (X θ n) (Measure.pi (fun _ : Fin n => μ)) :=
    (measurable_gaussianRieszCutoff_exponent s θ.val β hs θ.property.1 μ n).aemeasurable
  let data := fun (θ : I) (n : ℕ) (hn : 1 ≤ n) => gaussianRieszMasterCutoffData s θ.val δ β A u₀
    hs θ.property.1 θ.property.2 hδ hβ ha ρ M hM hρ n hn hA hAcontrol hu₀ hlow hrow.le hop.le
  let K := (1+gaussianRieszAdaptiveC0 s δ β+gaussianRieszAdaptiveC1 s β A ι)^2
  have hdim : 0 < (Fintype.card ι : ℝ) := by linarith
  have hp : 2*s/(Fintype.card ι : ℝ) < 1 := riesz_master_power_lt_one _ _ hdim (by linarith)
  have hsize (θ : I) (n : ℕ) (hn : 1 ≤ n) :
      masterCutoffSize μ (data θ n hn).kernel (data θ n hn).cap u₀ ≤ 0+K*(n : ℝ)^(2*s/(Fintype.card ι : ℝ)) := by
    have hb (u : ℝ) (hu : u₀ ≤ u) := gaussianRieszAdaptiveBand_cap_ess_bounds s θ.val δ β A hs
      θ.property.2 hδ hβ hA ha ρ M hM hρ n hn u (hu₀.trans hu)
    have hex := gaussianRieszAdaptive_exponents (Fintype.card ι : ℝ) s hs (by linarith)
    have hn' : 1 ≤ (n : ℝ) := by exact_mod_cast hn
    have hz := (masterCutoffSize_le_adaptive_power μ (fun u => gaussianRieszAdaptiveBand s θ.val δ β A n u ρ)
      (fun u => gaussianRieszAdaptiveCap s θ.val δ β A n u ι) (n : ℝ) u₀
      (s/((Fintype.card ι : ℝ)-s)) (gaussianRieszAdaptiveC0 s δ β) (gaussianRieszAdaptiveC1 s β A ι)
      hn' hu₀ hex.1 hex.2.1 (hb u₀ le_rfl).1 (hb u₀ le_rfl).2.1
      (fun u hu => (hb u hu).2.2.2.1) (fun u hu => (hb u hu).2.2.2.2)).2
    rw [hex.2.2] at hz
    simpa only [data,gaussianRieszMasterCutoffData,K,zero_add] using hz
  obtain ⟨C,hC⟩ := master_uniform_sublinear_exponential_envelope μ X hX u₀ hu₀ data 0 K
    (2*s/(Fintype.card ι : ℝ)) hp hsize
  exact ⟨δ,hδ,hδ1,C,fun η hη hηδ n hn => hC ⟨η,hη,hηδ⟩ n hn⟩

end DGRHS.Gaussian

#check DGRHS.Gaussian.measurable_physical_iidNegativeStatistic
#print axioms DGRHS.Gaussian.measurable_physical_iidNegativeStatistic

#check DGRHS.Gaussian.measurable_gaussianRieszCutoff_exponent
#print axioms DGRHS.Gaussian.measurable_gaussianRieszCutoff_exponent

#check DGRHS.Gaussian.gaussianRieszCutoff_uniform_small_scale_exponential
#print axioms DGRHS.Gaussian.gaussianRieszCutoff_uniform_small_scale_exponential
