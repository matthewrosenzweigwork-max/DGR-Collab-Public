import DGRHS.Gaussian.PeriodicRieszCutoff

/-!
Packet P9h, unit 2 (part 21): norm controls of the centered cutoff family on the torus: cap
`|q_η| ≤ 4 γ C_cap η^{-s}`, memLp, symmetry, canonicality, row/joint `L²` and operator bounds
`‖T_q‖ ≤ 4 γ √NC`, with `NC = C_r² (2 M ‖Ψ‖²_{L²(Haar)} + 2)`.
-/

noncomputable section
open MeasureTheory Set Metric Filter
open scoped Classical BigOperators NNReal ENNReal
namespace DGRHS.Periodic
open DGRHS.Commutator DGRHS.Gaussian DGRHS.Concentration
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]
local notation "E" => EuclideanSpace ℝ ι

/-- The `L²` control constant of the cutoff family. -/
def periodicRieszNormControl (ι : Type u) [Fintype ι] [Nonempty ι] (s M : ℝ) : ℝ :=
  periodicRieszRawConst ι s ^ 2 * (2 * (M * ∫ z, (periodicRieszMajorantFun (ι := ι) s z) ^ 2 ∂periodicHaar ι) + 2)

lemma stronglyMeasurable_periodicRieszRawCutoff (s η : ℝ) (n : ℕ) (hn : 1 ≤ n) (hs : 0 < s)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) (hη : 0 < η) (γ σ : ℝ) {K : ℝ≥0}
    {v : PeriodicTorus ι → E} (hv : LipschitzWith K v) :
    StronglyMeasurable (periodicRieszRawCutoff (ι := ι) s η n γ σ K v) :=
  (measurable_periodicRieszRawCutoff n hn s η hs hs2 hη γ σ hv).stronglyMeasurable

lemma periodicRieszCapConst_nonneg (s : ℝ) (hs : 0 < s) (hs2 : 2 * s < (Fintype.card ι : ℝ)) :
    0 ≤ periodicRieszCapConst ι s := by
  unfold periodicRieszCapConst
  have := periodicRieszLongBound_nonneg (ι := ι) s hs 0
  have := periodicRieszMeanConst_nonneg (ι := ι) s hs hs2
  have := (periodicRieszSmoothCoeff_pos (ι := ι) s hs).le
  have := periodicLatticeGaussConst_pos (ι := ι)
  positivity

lemma periodicRieszCenteredCutoff_cap (μ : Measure (PeriodicTorus ι)) [IsProbabilityMeasure μ]
    (s η : ℝ) (n : ℕ) (hn : 1 ≤ n) (hs : 0 < s) (hs2 : 2 * s < (Fintype.card ι : ℝ)) (hη : 0 < η)
    (hη2 : 2 * η ≤ periodicRieszTau) (γ σ : ℝ) (hγ : 0 ≤ γ) (hσ : |σ| ≤ 1) {K : ℝ≥0}
    {v : PeriodicTorus ι → E} (hv : LipschitzWith K v) (p : PeriodicTorus ι × PeriodicTorus ι) :
    |periodicRieszCenteredCutoff μ s η n γ σ K v p| ≤ 4 * (γ * periodicRieszCapConst ι s * η ^ (-s)) := by
  have hcap : 0 ≤ γ * periodicRieszCapConst ι s * η ^ (-s) := by
    have h := periodicRieszCapConst_nonneg (ι := ι) s hs hs2
    have := Real.rpow_nonneg hη.le (-s)
    positivity
  exact sourceRieszLocal_centered_bound μ _ (stronglyMeasurable_periodicRieszRawCutoff s η n hn hs hs2 hη γ σ hv)
    _ hcap (fun q => periodicRieszRawCutoff_cap s η n hn hs hs2 hη hη2 γ σ hγ hσ hv q) p


lemma stronglyMeasurable_periodicRieszCenteredCutoff (μ : Measure (PeriodicTorus ι)) [IsProbabilityMeasure μ]
    (s η : ℝ) (n : ℕ) (hn : 1 ≤ n) (hs : 0 < s) (hs2 : 2 * s < (Fintype.card ι : ℝ)) (hη : 0 < η)
    (γ σ : ℝ) {K : ℝ≥0} {v : PeriodicTorus ι → E} (hv : LipschitzWith K v) :
    StronglyMeasurable (periodicRieszCenteredCutoff μ s η n γ σ K v) :=
  stronglyMeasurable_hoeffdingCentered μ _ (stronglyMeasurable_periodicRieszRawCutoff s η n hn hs hs2 hη γ σ hv)

lemma memLp_periodicRieszCenteredCutoff (μ : Measure (PeriodicTorus ι)) [IsProbabilityMeasure μ]
    (s η : ℝ) (n : ℕ) (hn : 1 ≤ n) (hs : 0 < s) (hs2 : 2 * s < (Fintype.card ι : ℝ)) (hη : 0 < η)
    (hη2 : 2 * η ≤ periodicRieszTau) (γ σ : ℝ) (hγ : 0 ≤ γ) (hσ : |σ| ≤ 1) {K : ℝ≥0}
    {v : PeriodicTorus ι → E} (hv : LipschitzWith K v) (q : ℝ≥0∞) :
    MemLp (periodicRieszCenteredCutoff μ s η n γ σ K v) q (μ.prod μ) := by
  have hcap : 0 ≤ 4 * (γ * periodicRieszCapConst ι s * η ^ (-s)) := by
    have h := periodicRieszCapConst_nonneg (ι := ι) s hs hs2
    have := Real.rpow_nonneg hη.le (-s)
    positivity
  apply (memLp_const (4 * (γ * periodicRieszCapConst ι s * η ^ (-s)))).of_le
    (stronglyMeasurable_periodicRieszCenteredCutoff μ s η n hn hs hs2 hη γ σ hv).aestronglyMeasurable
  filter_upwards [] with z
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hcap]
  exact periodicRieszCenteredCutoff_cap μ s η n hn hs hs2 hη hη2 γ σ hγ hσ hv z

lemma periodicRieszCenteredCutoff_symmetric (μ : Measure (PeriodicTorus ι)) [IsProbabilityMeasure μ]
    (s η : ℝ) (n : ℕ) (hn : 1 ≤ n) (hs : 0 < s) (hs2 : 2 * s < (Fintype.card ι : ℝ)) (hη : 0 < η)
    (hη2 : 2 * η ≤ periodicRieszTau) (γ σ : ℝ) (K : ℝ≥0) (v : PeriodicTorus ι → E)
    (x y : PeriodicTorus ι) :
    periodicRieszCenteredCutoff μ s η n γ σ K v (x, y) = periodicRieszCenteredCutoff μ s η n γ σ K v (y, x) :=
  DGRHS.centeredKernel_symmetric μ (fun a b => periodicRieszRawCutoff s η n γ σ K v (a, b))
    (fun a b => (periodicRieszRawCutoff_symm n hn s η hs hs2 hη hη2 γ σ K v (a, b)).symm) x y

lemma periodicRieszCenteredCutoff_canonical (μ : Measure (PeriodicTorus ι)) [IsProbabilityMeasure μ]
    (s η : ℝ) (n : ℕ) (hn : 1 ≤ n) (hs : 0 < s) (hs2 : 2 * s < (Fintype.card ι : ℝ)) (hη : 0 < η)
    (hη2 : 2 * η ≤ periodicRieszTau) (γ σ : ℝ) (hγ : 0 ≤ γ) (hσ : |σ| ≤ 1) {K : ℝ≥0}
    {v : PeriodicTorus ι → E} (hv : LipschitzWith K v) :
    ∀ᵐ x ∂μ, ∫ y, periodicRieszCenteredCutoff μ s η n γ σ K v (x, y) ∂μ = 0 := by
  have hcap : 0 ≤ γ * periodicRieszCapConst ι s * η ^ (-s) := by
    have h := periodicRieszCapConst_nonneg (ι := ι) s hs hs2
    have := Real.rpow_nonneg hη.le (-s)
    positivity
  have hi := sourceRieszLocal_bounded_integrable (μ.prod μ) _
    (stronglyMeasurable_periodicRieszRawCutoff s η n hn hs hs2 hη γ σ hv) _ hcap
    (fun q => periodicRieszRawCutoff_cap s η n hn hs hs2 hη hη2 γ σ hγ hσ hv q)
  exact DGRHS.integral_centeredKernel_right μ _ hi

lemma essential_periodicRieszCenteredCutoff_le (μ : Measure (PeriodicTorus ι)) [IsProbabilityMeasure μ]
    (s η : ℝ) (n : ℕ) (hn : 1 ≤ n) (hs : 0 < s) (hs2 : 2 * s < (Fintype.card ι : ℝ)) (hη : 0 < η)
    (hη2 : 2 * η ≤ periodicRieszTau) (γ σ : ℝ) (hγ : 0 ≤ γ) (hσ : |σ| ≤ 1) {K : ℝ≥0}
    {v : PeriodicTorus ι → E} (hv : LipschitzWith K v) :
    (eLpNormEssSup (periodicRieszCenteredCutoff μ s η n γ σ K v) (μ.prod μ)).toReal ≤
      4 * (γ * periodicRieszCapConst ι s * η ^ (-s)) := by
  have hcap : 0 ≤ 4 * (γ * periodicRieszCapConst ι s * η ^ (-s)) := by
    have h := periodicRieszCapConst_nonneg (ι := ι) s hs hs2
    have := Real.rpow_nonneg hη.le (-s)
    positivity
  have hAE : ∀ᵐ p ∂μ.prod μ, ‖periodicRieszCenteredCutoff μ s η n γ σ K v p‖ ≤
      4 * (γ * periodicRieszCapConst ι s * η ^ (-s)) := Filter.Eventually.of_forall (fun p => by
    simpa only [Real.norm_eq_abs] using periodicRieszCenteredCutoff_cap μ s η n hn hs hs2 hη hη2 γ σ hγ hσ hv p)
  have h := eLpNormEssSup_le_of_ae_bound hAE
  simpa only [ENNReal.toReal_ofReal hcap] using ENNReal.toReal_mono ENNReal.ofReal_ne_top h


lemma periodicRieszNormControl_nonneg (s M : ℝ) (hs : 0 < s) (hs2 : 2 * s < (Fintype.card ι : ℝ)) (hM : 0 ≤ M) :
    0 ≤ periodicRieszNormControl ι s M := by
  unfold periodicRieszNormControl
  have : 0 ≤ ∫ z, (periodicRieszMajorantFun (ι := ι) s z) ^ 2 ∂periodicHaar ι :=
    integral_nonneg fun z => sq_nonneg _
  positivity

lemma periodicRieszMajorantFun_sq_integrable (s : ℝ) (hs : 0 < s) (hs2 : 2 * s < (Fintype.card ι : ℝ)) :
    Integrable (fun z => (periodicRieszMajorantFun (ι := ι) s z) ^ 2) (periodicHaar ι) :=
  (periodicRieszMajorantFun_memLp s hs hs2).integrable_sq

lemma periodicRieszRawConst_nonneg (s : ℝ) (hs : 0 < s) (hs2 : 2 * s < (Fintype.card ι : ℝ)) :
    0 ≤ periodicRieszRawConst ι s := by
  unfold periodicRieszRawConst
  have := periodicRieszLongBound_nonneg (ι := ι) s hs 0
  have := periodicRieszMeanConst_nonneg (ι := ι) s hs hs2
  positivity

/-- The squared raw cutoff is dominated by an integrable majorant, uniformly in the scale. -/
lemma periodicRieszRawCutoff_sq_le (s η : ℝ) (n : ℕ) (hn : 1 ≤ n) (hs : 0 < s)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) (hη : 0 < η) (hη2 : 2 * η ≤ periodicRieszTau) (γ σ : ℝ)
    (hγ : 0 ≤ γ) (hσ : |σ| ≤ 1) {K : ℝ≥0} {v : PeriodicTorus ι → E} (hv : LipschitzWith K v)
    (p : PeriodicTorus ι × PeriodicTorus ι) :
    (periodicRieszRawCutoff s η n γ σ K v p) ^ 2 ≤
      γ ^ 2 * periodicRieszRawConst ι s ^ 2 * (2 * (periodicRieszMajorantFun s (p.1 - p.2)) ^ 2 + 2) := by
  have hb := periodicRieszRawCutoff_bound s η n hn hs hs2 hη hη2 γ σ hγ hσ hv p
  have hr0 := periodicRieszRawConst_nonneg (ι := ι) s hs hs2
  have h0 : 0 ≤ periodicRieszMajorantFun (ι := ι) s (p.1 - p.2) := periodicRieszShortFun_nonneg s 1 hs _
  have hC0 : 0 ≤ γ * periodicRieszRawConst ι s * (periodicRieszMajorantFun s (p.1 - p.2) + 1) :=
    mul_nonneg (mul_nonneg hγ hr0) (by linarith)
  have hsq := (sq_le_sq₀ (abs_nonneg _) hC0).2 hb
  rw [sq_abs] at hsq
  refine hsq.trans ?_
  have h1 : (periodicRieszMajorantFun (ι := ι) s (p.1 - p.2) + 1) ^ 2 ≤
      2 * (periodicRieszMajorantFun s (p.1 - p.2)) ^ 2 + 2 := by
    nlinarith [sq_nonneg (periodicRieszMajorantFun (ι := ι) s (p.1 - p.2) - 1)]
  have h2 : 0 ≤ γ ^ 2 * periodicRieszRawConst ι s ^ 2 := by positivity
  calc (γ * periodicRieszRawConst ι s * (periodicRieszMajorantFun s (p.1 - p.2) + 1)) ^ 2
      = γ ^ 2 * periodicRieszRawConst ι s ^ 2 * (periodicRieszMajorantFun s (p.1 - p.2) + 1) ^ 2 := by ring
    _ ≤ γ ^ 2 * periodicRieszRawConst ι s ^ 2 * (2 * (periodicRieszMajorantFun s (p.1 - p.2)) ^ 2 + 2) :=
        mul_le_mul_of_nonneg_left h1 h2

/-- Row `L²` bound of the raw cutoff kernel. -/
lemma periodicRieszRawCutoff_square_row (s η : ℝ) (n : ℕ) (hn : 1 ≤ n) (hs : 0 < s)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) (hη : 0 < η) (hη2 : 2 * η ≤ periodicRieszTau) (γ σ : ℝ)
    (hγ : 0 ≤ γ) (hσ : |σ| ≤ 1) {K : ℝ≥0} {v : PeriodicTorus ι → E} (hv : LipschitzWith K v)
    (ρ : PeriodicTorus ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)] (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M)
    (x : PeriodicTorus ι) :
    Integrable (fun y => (periodicRieszRawCutoff s η n γ σ K v (x, y)) ^ 2) (periodicCappedDensityMeasure ρ) ∧
      (∫ y, (periodicRieszRawCutoff s η n γ σ K v (x, y)) ^ 2 ∂periodicCappedDensityMeasure ρ) ≤
        γ ^ 2 * periodicRieszNormControl ι s M := by
  have hm := stronglyMeasurable_periodicRieszRawCutoff s η n hn hs hs2 hη γ σ hv
  have hcap0 : 0 ≤ γ * periodicRieszCapConst ι s * η ^ (-s) := by
    have h := periodicRieszCapConst_nonneg (ι := ι) s hs hs2
    have := Real.rpow_nonneg hη.le (-s)
    positivity
  have hrm : StronglyMeasurable (fun y => periodicRieszRawCutoff s η n γ σ K v (x, y)) :=
    hm.comp_measurable (measurable_const.prodMk measurable_id)
  have hi : Integrable (fun y => (periodicRieszRawCutoff s η n γ σ K v (x, y)) ^ 2)
      (periodicCappedDensityMeasure ρ) :=
    sourceRieszLocal_bounded_integrable (periodicCappedDensityMeasure ρ) _ (hrm.pow 2)
      ((γ * periodicRieszCapConst ι s * η ^ (-s)) ^ 2)
      (sq_nonneg _) (fun y => by
        rw [abs_of_nonneg (sq_nonneg _)]
        have hb := periodicRieszRawCutoff_cap s η n hn hs hs2 hη hη2 γ σ hγ hσ hv (x, y)
        have hsq := (sq_le_sq₀ (abs_nonneg _) hcap0).2 hb
        simpa only [sq_abs] using hsq)
  have hΨ2 := periodicRieszMajorantFun_sq_integrable (ι := ι) s hs hs2
  have hrow := periodicDensityRow_integrable_of_haar ρ M hρ _ hΨ2 x
  have hrowb := periodicDensityRow_nonnegative_bound ρ M hM hρ _ hΨ2 (fun z => sq_nonneg _) x
  have hpt := fun y => periodicRieszRawCutoff_sq_le s η n hn hs hs2 hη hη2 γ σ hγ hσ hv (x, y)
  refine ⟨hi, ?_⟩
  have hint : Integrable (fun y => γ ^ 2 * periodicRieszRawConst ι s ^ 2 *
      (2 * (periodicRieszMajorantFun s (x - y)) ^ 2 + 2)) (periodicCappedDensityMeasure ρ) :=
    ((hrow.const_mul 2).add (integrable_const 2)).const_mul _
  have h1 := integral_mono hi hint hpt
  have h2 : (∫ y, γ ^ 2 * periodicRieszRawConst ι s ^ 2 * (2 * (periodicRieszMajorantFun s (x - y)) ^ 2 + 2)
      ∂periodicCappedDensityMeasure ρ) = γ ^ 2 * periodicRieszRawConst ι s ^ 2 *
        (2 * ∫ y, (periodicRieszMajorantFun s (x - y)) ^ 2 ∂periodicCappedDensityMeasure ρ + 2) := by
    rw [integral_const_mul, integral_add (hrow.const_mul 2) (integrable_const 2), integral_const_mul]
    simp
  rw [h2] at h1
  refine h1.trans ?_
  have h3 : 2 * ∫ y, (periodicRieszMajorantFun s (x - y)) ^ 2 ∂periodicCappedDensityMeasure ρ + 2 ≤
      2 * (M * ∫ z, (periodicRieszMajorantFun (ι := ι) s z) ^ 2 ∂periodicHaar ι) + 2 := by linarith
  have h4 : 0 ≤ γ ^ 2 * periodicRieszRawConst ι s ^ 2 := by positivity
  calc _ ≤ γ ^ 2 * periodicRieszRawConst ι s ^ 2 *
        (2 * (M * ∫ z, (periodicRieszMajorantFun (ι := ι) s z) ^ 2 ∂periodicHaar ι) + 2) :=
        mul_le_mul_of_nonneg_left h3 h4
    _ = _ := by unfold periodicRieszNormControl; ring


lemma memLp_periodicRieszRawCutoff (μ : Measure (PeriodicTorus ι)) [IsProbabilityMeasure μ]
    (s η : ℝ) (n : ℕ) (hn : 1 ≤ n) (hs : 0 < s) (hs2 : 2 * s < (Fintype.card ι : ℝ)) (hη : 0 < η)
    (hη2 : 2 * η ≤ periodicRieszTau) (γ σ : ℝ) (hγ : 0 ≤ γ) (hσ : |σ| ≤ 1) {K : ℝ≥0}
    {v : PeriodicTorus ι → E} (hv : LipschitzWith K v) (q : ℝ≥0∞) :
    MemLp (periodicRieszRawCutoff s η n γ σ K v) q (μ.prod μ) := by
  have hcap0 : 0 ≤ γ * periodicRieszCapConst ι s * η ^ (-s) := by
    have h := periodicRieszCapConst_nonneg (ι := ι) s hs hs2
    have := Real.rpow_nonneg hη.le (-s)
    positivity
  apply (memLp_const (γ * periodicRieszCapConst ι s * η ^ (-s))).of_le
    (stronglyMeasurable_periodicRieszRawCutoff s η n hn hs hs2 hη γ σ hv).aestronglyMeasurable
  filter_upwards [] with z
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hcap0]
  exact periodicRieszRawCutoff_cap s η n hn hs hs2 hη hη2 γ σ hγ hσ hv z

lemma periodicRieszRawCutoff_square_pair (s η : ℝ) (n : ℕ) (hn : 1 ≤ n) (hs : 0 < s)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) (hη : 0 < η) (hη2 : 2 * η ≤ periodicRieszTau) (γ σ : ℝ)
    (hγ : 0 ≤ γ) (hσ : |σ| ≤ 1) {K : ℝ≥0} {v : PeriodicTorus ι → E} (hv : LipschitzWith K v)
    (ρ : PeriodicTorus ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)] (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) :
    (∫ p, (periodicRieszRawCutoff s η n γ σ K v p) ^ 2
      ∂(periodicCappedDensityMeasure ρ).prod (periodicCappedDensityMeasure ρ)) ≤
      γ ^ 2 * periodicRieszNormControl ι s M := by
  have hi := (memLp_periodicRieszRawCutoff (periodicCappedDensityMeasure ρ) s η n hn hs hs2 hη hη2 γ σ hγ hσ
    hv 2).integrable_sq
  rw [integral_prod _ hi]
  calc _ ≤ ∫ _ : PeriodicTorus ι, γ ^ 2 * periodicRieszNormControl ι s M ∂periodicCappedDensityMeasure ρ :=
        integral_mono_ae hi.integral_prod_left (integrable_const _) (Filter.Eventually.of_forall (fun x =>
          (periodicRieszRawCutoff_square_row s η n hn hs hs2 hη hη2 γ σ hγ hσ hv ρ M hM hρ x).2))
    _ = _ := by simp

lemma periodicRieszCenteredCutoff_square_controls (s η : ℝ) (n : ℕ) (hn : 1 ≤ n) (hs : 0 < s)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) (hη : 0 < η) (hη2 : 2 * η ≤ periodicRieszTau) (γ σ : ℝ)
    (hγ : 0 ≤ γ) (hσ : |σ| ≤ 1) {K : ℝ≥0} {v : PeriodicTorus ι → E} (hv : LipschitzWith K v)
    (ρ : PeriodicTorus ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)] (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) :
    (∀ᵐ x ∂periodicCappedDensityMeasure ρ,
      (∫ y, (periodicRieszCenteredCutoff (periodicCappedDensityMeasure ρ) s η n γ σ K v (x, y)) ^ 2
        ∂periodicCappedDensityMeasure ρ) ≤ 16 * (γ ^ 2 * periodicRieszNormControl ι s M)) ∧
    (∫ p, (periodicRieszCenteredCutoff (periodicCappedDensityMeasure ρ) s η n γ σ K v p) ^ 2
      ∂(periodicCappedDensityMeasure ρ).prod (periodicCappedDensityMeasure ρ)) ≤
        16 * (γ ^ 2 * periodicRieszNormControl ι s M) := by
  have hm := stronglyMeasurable_periodicRieszRawCutoff s η n hn hs hs2 hη γ σ hv
  have h2 := memLp_periodicRieszRawCutoff (periodicCappedDensityMeasure ρ) s η n hn hs hs2 hη hη2 γ σ hγ hσ hv 2
  constructor
  · exact ae_row_sq_hoeffdingCentered_le (periodicCappedDensityMeasure ρ) _ hm h2 _
      (Filter.Eventually.of_forall (fun x =>
        (periodicRieszRawCutoff_square_row s η n hn hs hs2 hη hη2 γ σ hγ hσ hv ρ M hM hρ x).2))
  · exact (integral_sq_hoeffdingCentered_le (periodicCappedDensityMeasure ρ) _ hm h2).trans
      (mul_le_mul_of_nonneg_left (periodicRieszRawCutoff_square_pair s η n hn hs hs2 hη hη2 γ σ hγ hσ hv ρ M hM hρ)
        (by norm_num))

lemma norm_periodicRieszCenteredCutoff_operator (s η : ℝ) (n : ℕ) (hn : 1 ≤ n) (hs : 0 < s)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) (hη : 0 < η) (hη2 : 2 * η ≤ periodicRieszTau) (γ σ : ℝ)
    (hγ : 0 ≤ γ) (hσ : |σ| ≤ 1) {K : ℝ≥0} {v : PeriodicTorus ι → E} (hv : LipschitzWith K v)
    (ρ : PeriodicTorus ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)] (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) :
    ‖DGRHS.Kernel.integralOperator (periodicRieszCenteredCutoff (periodicCappedDensityMeasure ρ) s η n γ σ K v)
      (memLp_periodicRieszCenteredCutoff (periodicCappedDensityMeasure ρ) s η n hn hs hs2 hη hη2 γ σ hγ hσ hv 2)‖ ≤
        4 * γ * Real.sqrt (periodicRieszNormControl ι s M) := by
  have hC := periodicRieszNormControl_nonneg (ι := ι) s M hs hs2 hM
  have hW := memLp_periodicRieszCenteredCutoff (periodicCappedDensityMeasure ρ) s η n hn hs hs2 hη hη2 γ σ hγ hσ hv 2
  have hb : ‖hW.toLp (periodicRieszCenteredCutoff (periodicCappedDensityMeasure ρ) s η n γ σ K v)‖ ^ 2 ≤
      16 * (γ ^ 2 * periodicRieszNormControl ι s M) := by
    rw [DGRHS.Kernel.norm_toLp_sq]
    exact (periodicRieszCenteredCutoff_square_controls s η n hn hs hs2 hη hη2 γ σ hγ hσ hv ρ M hM hρ).2
  have hn' : ‖hW.toLp (periodicRieszCenteredCutoff (periodicCappedDensityMeasure ρ) s η n γ σ K v)‖ ≤
      4 * γ * Real.sqrt (periodicRieszNormControl ι s M) := by
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ 4 * γ * Real.sqrt (periodicRieszNormControl ι s M))).mp
    rw [mul_pow, mul_pow, Real.sq_sqrt hC]
    convert hb using 1 <;> ring
  exact (DGRHS.Kernel.norm_integralOperator_le _ hW).trans hn'

end DGRHS.Periodic
