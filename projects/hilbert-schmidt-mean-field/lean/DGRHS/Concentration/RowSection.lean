import DGRHS.Concentration.KernelEnvelope
import Mathlib.MeasureTheory.Measure.SeparableMeasure

noncomputable section
open MeasureTheory ProbabilityTheory TopologicalSpace
open scoped Topology InnerProductSpace ENNReal
namespace DGRHS.Concentration

lemma aestronglyMeasurable_of_distances {Ω E : Type*} [MeasurableSpace Ω]
    [PseudoMetricSpace E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure Ω) (f : Ω → E)
    (h : ∀ a : E, AEMeasurable (fun x ↦ dist (f x) a) μ) : AEStronglyMeasurable f μ := by
  have hb : IsTopologicalBasis {s : Set E | ∃ a r, s = Metric.ball a r} := by
    apply isTopologicalBasis_of_isOpen_of_nhds
    · rintro s ⟨a,r,rfl⟩
      exact Metric.isOpen_ball
    · intro a s ha hs
      obtain ⟨r,hr,hsub⟩ := Metric.mem_nhds_iff.mp (hs.mem_nhds ha)
      exact ⟨Metric.ball a r,⟨a,r,rfl⟩,Metric.mem_ball_self hr,hsub⟩
  have hn : NullMeasurable f μ := by
    intro s hs
    rw [BorelSpace.measurable_eq (α := E), hb.borel_eq_generateFrom] at hs
    change MeasurableSpace.GenerateMeasurable _ s at hs
    induction hs with
    | basic s hs =>
      rcases hs with ⟨a,r,rfl⟩
      exact (h a).nullMeasurable measurableSet_Iio
    | empty => simp
    | compl s hs ih => simpa only [Set.preimage_compl] using ih.compl
    | iUnion s hs ih => simpa only [Set.preimage_iUnion] using NullMeasurableSet.iUnion ih
  exact hn.aemeasurable.aestronglyMeasurable

/-- The actual L2 section, set to zero only when that section is not in L2. -/
def rowSection {Ω Ψ : Type*} [MeasurableSpace Ψ]
    (ν : Measure Ψ) (h : Ω × Ψ → ℝ) (x : Ω) : Lp ℝ 2 ν :=
  by
    classical
    exact if hh : MemLp (fun y ↦ h (x,y)) 2 ν then hh.toLp (fun y ↦ h (x,y)) else 0

lemma bounded_kernel_sections_memLp {Ω Ψ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ψ] (μ : Measure Ω) (ν : Measure Ψ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (h : Ω × Ψ → ℝ) (A : ℝ)
    (hAES : AEStronglyMeasurable h (μ.prod ν))
    (hBound : ∀ᵐ p ∂μ.prod ν, |h p| ≤ A) :
    ∀ᵐ x ∂μ, MemLp (fun y ↦ h (x,y)) 2 ν := by
  filter_upwards [hAES.prodMk_left, Measure.ae_ae_of_ae_prod hBound] with x hx hb
  apply (memLp_two_iff_integrable_sq hx).mpr
  apply integrable_of_ae_abs_le (hx.fun_pow 2)
  filter_upwards [hb] with y hy
  rw [abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) hy 2

lemma rowSection_coe {Ω Ψ : Type*} [MeasurableSpace Ψ]
    (ν : Measure Ψ) (h : Ω × Ψ → ℝ) (x : Ω)
    (hx : MemLp (fun y ↦ h (x,y)) 2 ν) :
    (rowSection ν h x : Ψ → ℝ) =ᵐ[ν] (fun y ↦ h (x,y)) := by
  rw [rowSection,dite_eq_left hx]
  exact hx.coeFn_toLp

lemma rowSection_norm_square {Ω Ψ : Type*} [MeasurableSpace Ψ]
    (ν : Measure Ψ) (h : Ω × Ψ → ℝ) (x : Ω)
    (hx : MemLp (fun y ↦ h (x,y)) 2 ν) :
    ‖rowSection ν h x‖^2 = ∫ y, (h (x,y))^2 ∂ν := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [rowSection_coe ν h x hx] with y hy
  simp [hy,pow_two]

lemma rowSection_distance {Ω Ψ : Type*} [MeasurableSpace Ψ]
    (ν : Measure Ψ) (h : Ω × Ψ → ℝ) (x : Ω) (g : Lp ℝ 2 ν)
    (hx : MemLp (fun y ↦ h (x,y)) 2 ν) :
    dist (rowSection ν h x) g = Real.sqrt (∫ y, (h (x,y)-g y)^2 ∂ν) := by
  have he : ‖rowSection ν h x-g‖^2 = ∫ y, (h (x,y)-g y)^2 ∂ν := by
    rw [← real_inner_self_eq_norm_sq,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (rowSection ν h x) g,rowSection_coe ν h x hx] with y hy hh
    rw [hy]
    simp [Pi.sub_apply,hh,pow_two]
  rw [dist_eq_norm,← he,Real.sqrt_sq (norm_nonneg _)]

/-- Actual strong measurability of L2 kernel sections on countably generated
second-coordinate spaces. No separability premise on arbitrary L2 spaces is imposed. -/
theorem rowSection_aestronglyMeasurable {Ω Ψ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ψ] [MeasurableSpace.CountablyGenerated Ψ]
    (μ : Measure Ω) (ν : Measure Ψ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : Ω × Ψ → ℝ) (A : ℝ) (hAES : AEStronglyMeasurable h (μ.prod ν))
    (hBound : ∀ᵐ p ∂μ.prod ν, |h p| ≤ A) : AEStronglyMeasurable (rowSection ν h) μ := by
  let : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  let : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  let : MeasurableSpace (Lp ℝ 2 ν) := borel (Lp ℝ 2 ν)
  let : BorelSpace (Lp ℝ 2 ν) := ⟨rfl⟩
  apply aestronglyMeasurable_of_distances μ (rowSection ν h)
  intro g
  have hg : AEStronglyMeasurable (fun p : Ω × Ψ ↦ (g : Ψ → ℝ) p.2) (μ.prod ν) :=
    (Lp.memLp g).aestronglyMeasurable.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
  have hm := ((hAES.sub hg).fun_pow 2).integral_prod_right'
  have hs : AEStronglyMeasurable (fun x ↦ Real.sqrt (∫ y, (h (x,y)-g y)^2 ∂ν)) μ :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hm
  apply hs.aemeasurable.congr
  filter_upwards [bounded_kernel_sections_memLp μ ν h A hAES hBound] with x hx
  exact (rowSection_distance ν h x g hx).symm

lemma rowSection_bounded {Ω Ψ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ψ]
    (μ : Measure Ω) (ν : Measure Ψ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : Ω × Ψ → ℝ) (A : ℝ) (hA : 0 ≤ A)
    (hAES : AEStronglyMeasurable h (μ.prod ν))
    (hBound : ∀ᵐ p ∂μ.prod ν, |h p| ≤ A) :
    ∀ᵐ x ∂μ, ‖rowSection ν h x‖ ≤ A := by
  filter_upwards [bounded_kernel_sections_memLp μ ν h A hAES hBound,
    Measure.ae_ae_of_ae_prod hBound] with x hx hb
  have hi := integral_mono_ae hx.integrable_sq (integrable_const (A^2))
    (hb.mono fun y hy ↦ by simpa only [sq_abs] using (pow_le_pow_left₀ (abs_nonneg _) hy 2))
  have hh : ‖rowSection ν h x‖^2 ≤ A^2 := by
    rw [rowSection_norm_square ν h x hx]
    simpa using hi
  nlinarith [norm_nonneg (rowSection ν h x)]

lemma rowSection_inner {Ω Ψ : Type*} [MeasurableSpace Ψ]
    (ν : Measure Ψ) (h : Ω × Ψ → ℝ) (x : Ω) (g : Lp ℝ 2 ν)
    (hx : MemLp (fun y ↦ h (x,y)) 2 ν) :
    inner ℝ g (rowSection ν h x) = ∫ y, g y*h (x,y) ∂ν := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [rowSection_coe ν h x hx] with y hy
  simp [hy,mul_comm]

/-- First-coordinate canonicality gives the actual Bochner center of the L2 row. -/
theorem rowSection_centered {Ω Ψ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ψ] [MeasurableSpace.CountablyGenerated Ψ]
    (μ : Measure Ω) (ν : Measure Ψ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : Ω × Ψ → ℝ) (A : ℝ) (hA : 0 ≤ A)
    (hAES : AEStronglyMeasurable h (μ.prod ν))
    (hBound : ∀ᵐ p ∂μ.prod ν, |h p| ≤ A)
    (hMean : ∀ᵐ y ∂ν, ∫ x, h (x,y) ∂μ = 0) :
    (∫ x, rowSection ν h x ∂μ) = 0 := by
  have hRow := rowSection_aestronglyMeasurable μ ν h A hAES hBound
  have hRowI := bounded_hilbert_integrable hRow (rowSection_bounded μ ν h A hA hAES hBound)
  apply integral_eq_zero_of_forall_integral_inner_eq_zero ℝ (rowSection ν h) hRowI
  intro g
  have hSq : Integrable (fun p ↦ (h p)^2) (μ.prod ν) := by
    simpa only [sq_abs] using bounded_kernel_abs_moment_integrable μ ν h A hAES hBound 2
  have hMem := (memLp_two_iff_integrable_sq hAES).mpr hSq
  have hGM : MemLp (fun p : Ω × Ψ ↦ (g : Ψ → ℝ) p.2) 2 (μ.prod ν) :=
    (Lp.memLp g).comp_measurePreserving measurePreserving_snd
  have hProd : Integrable (fun p : Ω × Ψ ↦ (g : Ψ → ℝ) p.2*h p) (μ.prod ν) :=
    hGM.integrable_mul hMem
  calc
    (∫ x, inner ℝ g (rowSection ν h x) ∂μ) = ∫ x, ∫ y, g y*h (x,y) ∂ν ∂μ := by
      apply integral_congr_ae
      filter_upwards [bounded_kernel_sections_memLp μ ν h A hAES hBound] with x hx
      exact rowSection_inner ν h x g hx
    _ = ∫ p : Ω × Ψ, g p.2*h p ∂μ.prod ν := (integral_prod _ hProd).symm
    _ = ∫ y, ∫ x, g y*h (x,y) ∂μ ∂ν := integral_prod_symm _ hProd
    _ = 0 := by
      have he : (fun y ↦ ∫ x, g y*h (x,y) ∂μ) =ᵐ[ν] (fun _ ↦ (0 : ℝ)) := by
        filter_upwards [hMean] with y hy
        rw [integral_const_mul,hy,mul_zero]
      rw [integral_congr_ae he]
      simp

#check @DGRHS.Concentration.rowSection_centered
#print axioms DGRHS.Concentration.rowSection_centered
#check @DGRHS.Concentration.rowSection_aestronglyMeasurable
#print axioms DGRHS.Concentration.rowSection_aestronglyMeasurable
#print axioms DGRHS.Concentration.rowSection_norm_square
#print axioms DGRHS.Concentration.aestronglyMeasurable_of_distances
#print axioms DGRHS.Concentration.rowSection_bounded
#print axioms DGRHS.Concentration.rowSection_inner
end DGRHS.Concentration
