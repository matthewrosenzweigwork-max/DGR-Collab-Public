import DGRHS.Gaussian.GaussianRieszFullMoment

/-! Actual source interpolated Gaussian-profile Riesz kernel G_eta+t*f_eta.
Its centered iid exponent is the legitimate AE convex combination of the
actual cutoff and full exponents; uniform moments are derived at every beta. -/
noncomputable section
open MeasureTheory Real
open scoped ENNReal
namespace DGRHS.Gaussian
open DGRHS.Concentration

lemma hoeffdingCentered_const_smul {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (W : X × X → ℝ) (c : ℝ) :
    hoeffdingCentered μ (c • W)=c • hoeffdingCentered μ W := by
  funext p
  unfold hoeffdingCentered DGRHS.centeredKernel DGRHS.potential DGRHS.secondPotential
  simp only [Pi.smul_apply,smul_eq_mul]
  simp_rw [integral_const_mul]
  ring

variable {ι : Type*} [Fintype ι]

def gaussianRieszInterpolatedPair (s η t : ℝ) : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι → ℝ :=
  gaussianRieszTruncatedPair s η+t • gaussianRieszShortPair s η

lemma ae_gaussianRieszInterpolated_exponent (s η β t : ℝ) (hs : 0 < s) (hη : 0 < η)
    (ha : 0 < (Fintype.card ι : ℝ)/2-s)
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] (hρ : ∀ᵐ x ∂volume, ρ x ≤ M) (n : ℕ) :
    (fun ω => β*iidNegativeStatistic n (hoeffdingCentered (gaussianRieszDensityMeasure ρ)
      (gaussianRieszInterpolatedPair s η t)) ω) =ᵐ[Measure.pi (fun _ : Fin n => gaussianRieszDensityMeasure ρ)]
      (fun ω => (1-t)*(β*iidNegativeStatistic n (hoeffdingCentered (gaussianRieszDensityMeasure ρ)
        (gaussianRieszTruncatedPair s η)) ω) +
        t*(β*iidNegativeStatistic n (hoeffdingCentered (gaussianRieszDensityMeasure ρ)
        (gaussianRieszPhysicalPair s)) ω)) := by
  let μ := gaussianRieszDensityMeasure ρ
  let W := gaussianRieszTruncatedPair (ι := ι) s η
  let V := gaussianRieszPhysicalPair (ι := ι) s
  have hW : Integrable W (μ.prod μ) := (memLp_gaussianRieszTruncatedPair s η hs hη μ).integrable (by norm_num)
  have hV : Integrable V (μ.prod μ) := (memLp_gaussianRieszPhysicalPair s hs ha ρ M hM hρ).integrable (by norm_num)
  have he : gaussianRieszInterpolatedPair s η t =ᵐ[μ.prod μ] (1-t) • W+t • V := by
    filter_upwards [ae_gaussianRieszEuclideanShortRange_eq_physical_remainder s η hs hη ha ρ] with p hp
    unfold gaussianRieszInterpolatedPair gaussianRieszShortPair
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    rw [hp]
    dsimp [W,V,gaussianRieszTruncatedPair,gaussianRieszPhysicalPair]
    ring
  have hc := ae_hoeffdingCentered_congr μ _ _ he
  have haC := ae_hoeffdingCentered_add μ ((1-t) • W) (t • V) (hW.smul (1-t)) (hV.smul t)
  have hcenter : hoeffdingCentered μ (gaussianRieszInterpolatedPair s η t) =ᵐ[μ.prod μ]
      (1-t) • hoeffdingCentered μ W+t • hoeffdingCentered μ V := by
    filter_upwards [hc,haC] with p hp1 hp2
    rw [hp1,hp2,hoeffdingCentered_const_smul,hoeffdingCentered_const_smul]
  have hstat := ae_physical_iidNegativeStatistic_congr μ n _ _ hcenter
  filter_upwards [hstat] with ω hω
  rw [hω,physical_iidNegativeStatistic_add,physical_iidNegativeStatistic_const_smul,
    physical_iidNegativeStatistic_const_smul]
  ring

theorem gaussianRieszInterpolated_uniform_exponential (s β : ℝ) (hs : 0 < s) (hβ : 0 ≤ β)
    (ha : 0 < (Fintype.card ι : ℝ)/2-s)
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] (hρ : ∀ᵐ x ∂volume, ρ x ≤ M) :
    ∃ C : ℝ, ∀ η : ℝ, 0 < η → ∀ n : ℕ, 1 ≤ n → ∀ t ∈ Set.Icc (0 : ℝ) 1,
      Integrable (fun ω => Real.exp (β*iidNegativeStatistic n
        (hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianRieszInterpolatedPair s η t)) ω))
          (Measure.pi (fun _ : Fin n => gaussianRieszDensityMeasure ρ)) ∧
      (∫ ω,Real.exp (β*iidNegativeStatistic n
        (hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianRieszInterpolatedPair s η t)) ω)
          ∂Measure.pi (fun _ : Fin n => gaussianRieszDensityMeasure ρ)) ≤ C := by
  let μ := gaussianRieszDensityMeasure ρ
  obtain ⟨C₀,hC₀⟩ := gaussianRieszCutoff_uniform_exponential s β hs hβ ha ρ M hM hρ
  obtain ⟨C₁,hC₁⟩ := gaussianRieszPhysical_uniform_exponential s β hs hβ ha ρ M hM hρ
  refine ⟨max C₀ C₁,?_⟩
  intro η hη n hn t ht
  let X := fun ω => β*iidNegativeStatistic n (hoeffdingCentered μ (gaussianRieszTruncatedPair s η)) ω
  let Y := fun ω => β*iidNegativeStatistic n (hoeffdingCentered μ (gaussianRieszPhysicalPair s)) ω
  have hX : AEMeasurable X (Measure.pi (fun _ : Fin n => μ)) :=
    (measurable_gaussianRieszCutoff_exponent s η β hs hη μ n).aemeasurable
  have hY : AEMeasurable Y (Measure.pi (fun _ : Fin n => μ)) :=
    ((measurable_physical_iidNegativeStatistic n _ (stronglyMeasurable_hoeffdingCentered μ _
      (stronglyMeasurable_gaussianRieszPhysicalPair s)).measurable).const_mul β).aemeasurable
  obtain ⟨hi,hb⟩ := interpolated_exp_integral (Measure.pi (fun _ : Fin n => μ)) X Y hX hY
    (hC₀ η hη n hn).1 (hC₁ n hn).1 t ht.1 ht.2
  have he : (fun ω => Real.exp (β*iidNegativeStatistic n (hoeffdingCentered μ
      (gaussianRieszInterpolatedPair s η t)) ω)) =ᵐ[Measure.pi (fun _ : Fin n => μ)]
      (fun ω => Real.exp ((1-t)*X ω+t*Y ω)) := (ae_gaussianRieszInterpolated_exponent s η β t hs hη ha ρ M hM hρ n).mono
    (fun ω h => congrArg Real.exp h)
  refine ⟨hi.congr he.symm,?_⟩
  rw [integral_congr_ae he]
  refine hb.trans ?_
  calc
    _ ≤ (1-t)*max C₀ C₁+t*max C₀ C₁ :=
      add_le_add (mul_le_mul_of_nonneg_left ((hC₀ η hη n hn).2.trans (le_max_left _ _)) (by linarith [ht.2]))
        (mul_le_mul_of_nonneg_left ((hC₁ n hn).2.trans (le_max_right _ _)) ht.1)
    _ = _ := by ring

end DGRHS.Gaussian

#check DGRHS.Gaussian.hoeffdingCentered_const_smul
#print axioms DGRHS.Gaussian.hoeffdingCentered_const_smul

#check DGRHS.Gaussian.gaussianRieszInterpolatedPair
#print axioms DGRHS.Gaussian.gaussianRieszInterpolatedPair

#check DGRHS.Gaussian.ae_gaussianRieszInterpolated_exponent
#print axioms DGRHS.Gaussian.ae_gaussianRieszInterpolated_exponent

#check DGRHS.Gaussian.gaussianRieszInterpolated_uniform_exponential
#print axioms DGRHS.Gaussian.gaussianRieszInterpolated_uniform_exponential
