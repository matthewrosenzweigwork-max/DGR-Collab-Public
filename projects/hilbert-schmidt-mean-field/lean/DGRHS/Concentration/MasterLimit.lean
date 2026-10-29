import DGRHS.Concentration.MasterGrowth
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal
namespace DGRHS.Concentration

/-- Fatou constructs the proper limit exponential integral. Measurability of the
limit exponential is derived from the actual AE convergence, and its
integrability and expectation bound are conclusions. -/
theorem exponential_integrable_of_ae_tendsto {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Xₘ : ℕ → Ω → ℝ) (X : Ω → ℝ)
    (hXi : ∀ m, Integrable (fun ω ↦ Real.exp (Xₘ m ω)) μ)
    (M : ℝ) (hBound : ∀ m, (∫ ω,Real.exp (Xₘ m ω) ∂μ) ≤ M)
    (hLim : ∀ᵐ ω ∂μ, Tendsto (fun m ↦ Xₘ m ω) atTop (𝓝 (X ω))) :
    Integrable (fun ω ↦ Real.exp (X ω)) μ ∧
      (∫ ω,Real.exp (X ω) ∂μ) ≤ M := by
  have hExpLim : ∀ᵐ ω ∂μ, Tendsto (fun m ↦ Real.exp (Xₘ m ω)) atTop (𝓝 (Real.exp (X ω))) :=
    hLim.mono fun ω h ↦ (Real.continuous_exp.tendsto (X ω)).comp h
  have hMeas : AEStronglyMeasurable (fun ω ↦ Real.exp (X ω)) μ :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun m ↦ (hXi m).aestronglyMeasurable) hExpLim
  have hNNLim : ∀ᵐ ω ∂μ, Tendsto (fun m ↦ ENNReal.ofReal (Real.exp (Xₘ m ω))) atTop
      (𝓝 (ENNReal.ofReal (Real.exp (X ω)))) :=
    hExpLim.mono fun _ h ↦ ENNReal.tendsto_ofReal h
  have hNnm : ∀ m, AEMeasurable (fun ω ↦ ENNReal.ofReal (Real.exp (Xₘ m ω))) μ :=
    fun m ↦ ENNReal.measurable_ofReal.comp_aemeasurable (hXi m).aestronglyMeasurable.aemeasurable
  have hNnBound : ∀ m, (∫⁻ ω,ENNReal.ofReal (Real.exp (Xₘ m ω)) ∂μ) ≤ ENNReal.ofReal M := by
    intro m
    rw [← ofReal_integral_eq_lintegral_ofReal (hXi m)
      (Eventually.of_forall fun ω ↦ (Real.exp_pos (Xₘ m ω)).le)]
    exact ENNReal.ofReal_le_ofReal (hBound m)
  have hFatou : (∫⁻ ω,ENNReal.ofReal (Real.exp (X ω)) ∂μ) ≤ ENNReal.ofReal M := by
    calc
      _ = ∫⁻ ω,liminf (fun m ↦ ENNReal.ofReal (Real.exp (Xₘ m ω))) atTop ∂μ :=
        lintegral_congr_ae (hNNLim.mono fun _ h ↦ h.liminf_eq.symm)
      _ ≤ liminf (fun m ↦ ∫⁻ ω,ENNReal.ofReal (Real.exp (Xₘ m ω)) ∂μ) atTop :=
        lintegral_liminf_le' hNnm
      _ ≤ ENNReal.ofReal M := liminf_le_of_frequently_le' (Frequently.of_forall hNnBound)
  have hNn : 0 ≤ᵐ[μ] (fun ω ↦ Real.exp (X ω)) :=
    Eventually.of_forall fun ω ↦ (Real.exp_pos (X ω)).le
  have hi : Integrable (fun ω ↦ Real.exp (X ω)) μ :=
    ⟨hMeas,(hasFiniteIntegral_iff_ofReal hNn).mpr (hFatou.trans_lt ENNReal.ofReal_lt_top)⟩
  have hM : 0 ≤ M := (integral_nonneg fun ω ↦ (Real.exp_pos (Xₘ 0 ω)).le).trans (hBound 0)
  refine ⟨hi,?_⟩
  have hb := ENNReal.toReal_mono ENNReal.ofReal_ne_top hFatou
  rw [← ofReal_integral_eq_lintegral_ofReal hi hNn] at hb
  simpa only [ENNReal.toReal_ofReal (integral_nonneg fun ω ↦ (Real.exp_pos (X ω)).le),
    ENNReal.toReal_ofReal hM] using hb

/-- Convergence in measure suffices: a genuine native AE subsequence supplies
Fatou, preserving the same finite expectation bound. -/
theorem exponential_integrable_of_tendstoInMeasure {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (Xₘ : ℕ → Ω → ℝ) (X : Ω → ℝ)
    (hXi : ∀ m, Integrable (fun ω ↦ Real.exp (Xₘ m ω)) μ)
    (M : ℝ) (hBound : ∀ m, (∫ ω,Real.exp (Xₘ m ω) ∂μ) ≤ M)
    (hLim : TendstoInMeasure μ Xₘ atTop X) :
    Integrable (fun ω ↦ Real.exp (X ω)) μ ∧
      (∫ ω,Real.exp (X ω) ∂μ) ≤ M := by
  obtain ⟨ns,_hns,hns⟩ := hLim.exists_seq_tendsto_ae
  exact exponential_integrable_of_ae_tendsto μ (fun m ↦ Xₘ (ns m)) X
    (fun m ↦ hXi (ns m)) M (fun m ↦ hBound (ns m)) hns

/-- Proper full-limit exponential control, uniform in auxiliary parameters and
all positive particle numbers, from actual cutoff master data and a common
sublinear size estimate. No limiting integrability or expectation is assumed. -/
theorem master_sublinear_limit_exponential_envelope {I Ω : Type*} [MeasurableSpace Ω]
    [MeasurableSpace.CountablyGenerated Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xₘ : ℕ → I → (n : ℕ) → (Fin n → Ω) → ℝ)
    (X : I → (n : ℕ) → (Fin n → Ω) → ℝ)
    (hXm : ∀ m θ n, 1 ≤ n → AEMeasurable (Xₘ m θ n) (Measure.pi (fun _ : Fin n ↦ μ)))
    (u₀ : ℝ) (hu₀ : 1 ≤ u₀)
    (d : ∀ m θ n, 1 ≤ n → MasterCutoffData μ n (Xₘ m θ n) u₀)
    (C₀ C₁ p : ℝ) (hp : p < 1)
    (hSize : ∀ m θ n (hn : 1 ≤ n), masterCutoffSize μ (d m θ n hn).kernel (d m θ n hn).cap u₀ ≤
      C₀+C₁*(n : ℝ)^p)
    (hLim : ∀ θ n, 1 ≤ n → ∀ᵐ ω ∂Measure.pi (fun _ : Fin n ↦ μ),
      Tendsto (fun m ↦ Xₘ m θ n ω) atTop (𝓝 (X θ n ω))) :
    ∃ M : ℝ, ∀ θ n, 1 ≤ n →
      Integrable (fun ω ↦ Real.exp (X θ n ω)) (Measure.pi (fun _ : Fin n ↦ μ)) ∧
      (∫ ω,Real.exp (X θ n ω) ∂Measure.pi (fun _ : Fin n ↦ μ)) ≤ M := by
  obtain ⟨M,hM⟩ := master_uniform_sublinear_exponential_envelope μ
    (fun z : ℕ × I ↦ Xₘ z.1 z.2) (fun z n hn ↦ hXm z.1 z.2 n hn) u₀ hu₀
    (fun z n hn ↦ d z.1 z.2 n hn) C₀ C₁ p hp (fun z n hn ↦ hSize z.1 z.2 n hn)
  refine ⟨M,?_⟩
  intro θ n hn
  exact exponential_integrable_of_ae_tendsto (Measure.pi (fun _ : Fin n ↦ μ))
    (fun m ↦ Xₘ m θ n) (X θ n) (fun m ↦ (hM (m,θ) n hn).1) M
    (fun m ↦ (hM (m,θ) n hn).2) (hLim θ n hn)

/-- Full singular interpolation after the actual cutoff passage. A single
bound is uniform in approximation, auxiliary parameter, positive particle
number and the entire interpolation interval; full-limit proper integrability
and measurability are constructed, not supplied. -/
theorem master_sublinear_interpolated_limit_exponential_envelope {I Ω : Type*} [MeasurableSpace Ω]
    [MeasurableSpace.CountablyGenerated Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xₘ Yₘ : ℕ → I → (n : ℕ) → (Fin n → Ω) → ℝ)
    (X Y : I → (n : ℕ) → (Fin n → Ω) → ℝ)
    (hXm : ∀ m θ n, 1 ≤ n → AEMeasurable (Xₘ m θ n) (Measure.pi (fun _ : Fin n ↦ μ)))
    (hYm : ∀ m θ n, 1 ≤ n → AEMeasurable (Yₘ m θ n) (Measure.pi (fun _ : Fin n ↦ μ)))
    (u₀ : ℝ) (hu₀ : 1 ≤ u₀)
    (dX : ∀ m θ n, 1 ≤ n → MasterCutoffData μ n (Xₘ m θ n) u₀)
    (dY : ∀ m θ n, 1 ≤ n → MasterCutoffData μ n (Yₘ m θ n) u₀)
    (C₀ C₁ p : ℝ) (hp : p < 1)
    (hSizeX : ∀ m θ n (hn : 1 ≤ n), masterCutoffSize μ (dX m θ n hn).kernel (dX m θ n hn).cap u₀ ≤
      C₀+C₁*(n : ℝ)^p)
    (hSizeY : ∀ m θ n (hn : 1 ≤ n), masterCutoffSize μ (dY m θ n hn).kernel (dY m θ n hn).cap u₀ ≤
      C₀+C₁*(n : ℝ)^p)
    (hLimX : ∀ θ n, 1 ≤ n → ∀ᵐ ω ∂Measure.pi (fun _ : Fin n ↦ μ),
      Tendsto (fun m ↦ Xₘ m θ n ω) atTop (𝓝 (X θ n ω)))
    (hLimY : ∀ θ n, 1 ≤ n → ∀ᵐ ω ∂Measure.pi (fun _ : Fin n ↦ μ),
      Tendsto (fun m ↦ Yₘ m θ n ω) atTop (𝓝 (Y θ n ω))) :
    ∃ M : ℝ, ∀ θ n, 1 ≤ n → ∀ t ∈ Set.Icc (0 : ℝ) 1,
      Integrable (fun ω ↦ Real.exp ((1-t)*X θ n ω+t*Y θ n ω)) (Measure.pi (fun _ : Fin n ↦ μ)) ∧
      (∫ ω,Real.exp ((1-t)*X θ n ω+t*Y θ n ω) ∂Measure.pi (fun _ : Fin n ↦ μ)) ≤ M := by
  obtain ⟨M,hM⟩ := master_sublinear_interpolated_exponential_envelope μ
    (fun z : ℕ × I ↦ Xₘ z.1 z.2) (fun z : ℕ × I ↦ Yₘ z.1 z.2)
    (fun z n hn ↦ hXm z.1 z.2 n hn) (fun z n hn ↦ hYm z.1 z.2 n hn) u₀ hu₀
    (fun z n hn ↦ dX z.1 z.2 n hn) (fun z n hn ↦ dY z.1 z.2 n hn)
    C₀ C₁ p hp (fun z n hn ↦ hSizeX z.1 z.2 n hn) (fun z n hn ↦ hSizeY z.1 z.2 n hn)
  refine ⟨M,?_⟩
  intro θ n hn t ht
  apply exponential_integrable_of_ae_tendsto (Measure.pi (fun _ : Fin n ↦ μ))
    (fun m ω ↦ (1-t)*Xₘ m θ n ω+t*Yₘ m θ n ω) (fun ω ↦ (1-t)*X θ n ω+t*Y θ n ω)
    (fun m ↦ (hM (m,θ) n hn t ht).1) M (fun m ↦ (hM (m,θ) n hn t ht).2)
  filter_upwards [hLimX θ n hn,hLimY θ n hn] with ω hx hy
  exact (hx.const_mul (1-t)).add (hy.const_mul t)

#print axioms DGRHS.Concentration.exponential_integrable_of_ae_tendsto
#print axioms DGRHS.Concentration.exponential_integrable_of_tendstoInMeasure
#print axioms DGRHS.Concentration.master_sublinear_limit_exponential_envelope
#check @DGRHS.Concentration.exponential_integrable_of_ae_tendsto
#check @DGRHS.Concentration.exponential_integrable_of_tendstoInMeasure
#check @DGRHS.Concentration.master_sublinear_limit_exponential_envelope
#print axioms DGRHS.Concentration.master_sublinear_interpolated_limit_exponential_envelope
#check @DGRHS.Concentration.master_sublinear_interpolated_limit_exponential_envelope
end DGRHS.Concentration
