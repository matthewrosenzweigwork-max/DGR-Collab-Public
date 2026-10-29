import DGRHS.Commutator.SourceLogStaticDerivative
import DGRHS.Commutator.SourceLogClassicalBackwardInterface
import DGRHS.Commutator.SourceMovingTestDerivative

/-! Derive the actual moving-test derivative from the static LOG class and
the source classical backward regularity. Law and time-derivative clamps have
different horizons. All identities are transported back to the original
every-time law; no density time derivative or desired moving equation is a
premise. Endpoint continuity/AC is a subsequent step. -/
noncomputable section
open MeasureTheory Set Filter Laplacian
open scoped Topology Interval NNReal
namespace DGRHS.Commutator
open DGRHS.Gaussian
variable {ι : Type*} [Fintype ι] [Nonempty ι]
local notation "E" => EuclideanSpace ℝ ι

lemma SourceLogStaticWeakMeanField.hasDerivAt_classical_moving_pairing
    (β T : ℝ) (hT : 0 ≤ T) (ρ : ℝ → E → ℝ)
    (h : SourceLogStaticWeakMeanField β T ρ)
    (hprob : ∀ r ∈ Icc 0 T, IsProbabilityMeasure (gaussianRieszDensityMeasure (ρ r)))
    (M : ℝ) (hM : 0 ≤ M) (hρ : ∀ r ∈ Icc 0 T, ∀ᵐ x ∂volume, ρ r x ≤ M)
    (t : ℝ≥0) (ht : (t : ℝ) ≤ T) (φ : E → ℝ) (f : ℝ → E → ℝ)
    (hf : SourceLogClassicalBackwardSolution β ρ t φ f)
    (r : ℝ) (hr : r ∈ Ioo 0 (t : ℝ)) :
    HasDerivAt (fun u => ∫ x, f u x ∂gaussianRieszDensityMeasure (ρ u))
      (DGRHS.Dynamics.sourceLogMeanTestDrift β f r (gaussianRieszDensityMeasure (ρ r))) r := by
  obtain ⟨μ,hμ,hρμ⟩ := h.exists_continuous_probability_path β T hT ρ hprob
  have hμe (u : ℝ) (hu : u ∈ Icc 0 T) :
      (μ u : Measure E) = gaussianRieszDensityMeasure (ρ u) := by
    rw [hρμ u,min_eq_right hu.2,max_eq_right hu.1]
  obtain ⟨C,hC,hb⟩ := hf.bounded
  have hslice (u : ℝ) (hu : u ∈ Icc 0 (t : ℝ)) : SourceBoundedC2Test (f u) :=
    (sourceBoundedC2Test_iff_classical_bounds (f u)).2
      ⟨hf.spatial_contdiff u hu,C,hC,hb u hu⟩
  have hrcc : r ∈ Icc 0 (t : ℝ) := ⟨hr.1.le,hr.2.le⟩
  have hrT : r ∈ Ioo 0 T := ⟨hr.1,hr.2.trans_le ht⟩
  have hstatic0 := h.hasDerivAt_static_pairing β T hT ρ hprob M hM hρ
    (f r) (hslice r hrcc) r hrT
  have hstatic : HasDerivAt (fun u => ∫ x, f r x ∂(μ u : Measure E))
      (sourceLogStaticMeanTestDrift β (ρ r) (f r)) r := by
    apply hstatic0.congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds hrT.1 hrT.2] with u hu
    rw [hμe u ⟨hu.1.le,hu.2.le⟩]
  obtain ⟨δ,hδc,⟨D,hDb⟩,hδ,hEq⟩ := hf.time_equation
  let c : ℝ → ℝ := fun u => max 0 (min (t : ℝ) u)
  have hcm (u : ℝ) : c u ∈ Icc 0 (t : ℝ) :=
    ⟨le_max_left _ _,max_le t.coe_nonneg (min_le_left _ _)⟩
  have hce (u : ℝ) (hu : u ∈ Icc 0 (t : ℝ)) : c u = u := by
    dsimp only [c]
    rw [min_eq_right hu.2,max_eq_right hu.1]
  let deltaExt : ℝ × E → ℝ := fun p => δ (c p.1) p.2
  have hc : Continuous (fun p : ℝ × E => (c p.1,p.2)) :=
    (continuous_const.max (continuous_const.min continuous_fst)).prodMk continuous_snd
  have hdeltaExt : Continuous deltaExt := hδc.comp_continuous hc (fun p => ⟨hcm p.1,mem_univ _⟩)
  have hdeltaExtb (p : ℝ × E) : |deltaExt p| ≤ D := hDb (c p.1) (hcm p.1) p.2
  let ε : ℝ := min r ((t : ℝ)-r) / 2
  have hε : 0 < ε := by
    exact div_pos (lt_min hr.1 (sub_pos.mpr hr.2)) (by norm_num)
  have hnear (u : ℝ) (hu : u ∈ Ioo (r-ε) (r+ε)) : u ∈ Ioo 0 (t : ℝ) := by
    have h1 := min_le_left r ((t : ℝ)-r)
    have h2 := min_le_right r ((t : ℝ)-r)
    dsimp only [ε] at hu
    constructor <;> linarith [hu.1,hu.2,hr.1,hr.2]
  have htime : ∀ u ∈ Ioo (r-ε) (r+ε), ∀ x,
      HasDerivAt (fun v => f v x) (deltaExt (u,x)) u := by
    intro u hu x
    have hui := hnear u hu
    dsimp only [deltaExt]
    rw [hce u ⟨hui.1.le,hui.2.le⟩]
    exact hδ u hui x
  have hproper : ∀ u ∈ Ioo (r-ε) (r+ε),
      Integrable (f u) (μ u : Measure E) ∧ Integrable (f r) (μ u : Measure E) := by
    intro u hu
    have hui := hnear u hu
    exact ⟨((hslice u ⟨hui.1.le,hui.2.le⟩).log_spatial_properness (f u) _).1,
      ((hslice r hrcc).log_spatial_properness (f r) _).1⟩
  have hd := hasDerivAt_integral_moving_probability μ hμ f deltaExt hdeltaExt D hdeltaExtb
    r ε (sourceLogStaticMeanTestDrift β (ρ r) (f r)) hε htime hproper hstatic
  letI := hprob r ⟨hr.1.le,hr.2.le.trans ht⟩
  have hideltaExt : Integrable (fun x => deltaExt (r,x)) (gaussianRieszDensityMeasure (ρ r)) :=
    integrable_of_abs_bound _
      (hdeltaExt.comp (continuous_const.prodMk continuous_id)).measurable (fun x => hdeltaExtb (r,x))
  have hiLap := ((hslice r hrcc).log_spatial_properness (f r)
    (gaussianRieszDensityMeasure (ρ r))).2.1
  have heDeriv (x : E) : deriv (fun u => f u x) r = deltaExt (r,x) := by
    rw [(hδ r hr x).deriv]
    dsimp only [deltaExt]
    rw [hce r hrcc]
  have he : sourceLogStaticMeanTestDrift β (ρ r) (f r) +
      (∫ x, deltaExt (r,x) ∂(μ r : Measure E)) =
      DGRHS.Dynamics.sourceLogMeanTestDrift β f r (gaussianRieszDensityMeasure (ρ r)) := by
    rw [hμe r ⟨hr.1.le,hr.2.le.trans ht⟩]
    unfold sourceLogStaticMeanTestDrift DGRHS.Dynamics.sourceLogMeanTestDrift
    simp_rw [heDeriv]
    rw [integral_add hideltaExt (hiLap.const_mul β⁻¹),integral_const_mul]
    ring
  rw [he] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hr.1 hr.2] with u hu
  rw [hμe u ⟨hu.1.le,hu.2.le.trans ht⟩]

end DGRHS.Commutator
set_option pp.maxSteps 1000000
set_option pp.deepTerms true
#check @DGRHS.Commutator.SourceLogStaticWeakMeanField.hasDerivAt_classical_moving_pairing
#print axioms DGRHS.Commutator.SourceLogStaticWeakMeanField.hasDerivAt_classical_moving_pairing
