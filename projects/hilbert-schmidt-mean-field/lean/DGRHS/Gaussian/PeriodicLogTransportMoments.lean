import DGRHS.Gaussian.PeriodicLogParticleLink
import DGRHS.Gaussian.PeriodicLogBoundedMoments
import DGRHS.Commutator.SourceLogTransportGibbsMoments
import DGRHS.Entropy.SourceLogForcingNormalization

/-!
Packet P9h, unit 3 (LOG, part 10): the torus LOG local numerator (`β ≤ β_loc`, bound `e`), the
kernel-generic Gibbs moment lemmas (division by the Jensen partition lower bound, Hölder bootstrap) and
the Gibbs exponential moments of both signs with the printed piecewise parameter and `C_em`
(torus version of `SourceLogTransportLocal` and `SourceLogTransportGibbsMoments`).
-/

noncomputable section
open MeasureTheory Set Metric Filter
open scoped Classical BigOperators NNReal ENNReal
namespace DGRHS.Periodic
open DGRHS.Commutator DGRHS.Gaussian DGRHS.Concentration DGRHS.Entropy
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]
local notation "E" => EuclideanSpace ℝ ι

/-! ### Kernel-generic Gibbs moment lemmas -/

lemma gibbs_moment_of_numerator {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (u a : Ω → ℝ) (hu : Integrable (fun x => Real.exp (u x)) P)
    (z0 B : ℝ) (hz0 : 0 < z0) (hz : z0 ≤ ∫ x, Real.exp (u x) ∂P)
    (hi : Integrable (fun x => Real.exp (u x + a x)) P) (hb : (∫ x, Real.exp (u x + a x) ∂P) ≤ B) :
    Integrable (fun x => Real.exp (a x)) (P.tilted u) ∧
      (∫ x, Real.exp (a x) ∂P.tilted u) ≤ B / z0 := by
  have ht : Integrable (fun x => Real.exp (a x)) (P.tilted u) := by
    apply (integrable_tilted_iff hu _).mpr
    apply hi.congr
    exact ae_of_all _ fun x => by
      change Real.exp (u x + a x) = Real.exp (u x) * Real.exp (a x)
      rw [Real.exp_add]
  refine ⟨ht, ?_⟩
  rw [integral_exp_tilted]
  have hnum : 0 ≤ ∫ x, Real.exp (u x + a x) ∂P := integral_nonneg fun x => (Real.exp_pos _).le
  have hdpos : 0 < ∫ x, Real.exp (u x) ∂P := lt_of_lt_of_le hz0 hz
  exact div_le_div₀ (hnum.trans hb) hb hz0 hz

lemma gibbs_moment_holder {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (u u1 u2 c : Ω → ℝ) (hu : ∀ x, u x = (u1 x + u2 x) / 2)
    (hui : Integrable (fun x => Real.exp (u x)) P)
    (h1 : Integrable (fun x => Real.exp (u1 x + c x)) P) (B : ℝ)
    (hB : (∫ x, Real.exp (u1 x + c x) ∂P) ≤ B)
    (h2 : Integrable (fun x => Real.exp (u2 x)) P) (Cub : ℝ)
    (hCub : (∫ x, Real.exp (u2 x) ∂P) ≤ Cub) (z0 : ℝ) (hz0 : 0 < z0)
    (hz : z0 ≤ ∫ x, Real.exp (u x) ∂P) :
    Integrable (fun x => Real.exp (c x / 2)) (P.tilted u) ∧
      (∫ x, Real.exp (c x / 2) ∂P.tilted u) ≤ Real.sqrt B * Real.sqrt Cub / z0 := by
  let X := fun x => (u1 x + c x) / 2
  let Y := fun x => u2 x / 2
  have hxi : Integrable (fun x => Real.exp (2 * X x)) P := by
    refine h1.congr (ae_of_all _ fun x => ?_)
    dsimp only [X]; congr 1; ring
  have hyi : Integrable (fun x => Real.exp (2 * Y x)) P := by
    refine h2.congr (ae_of_all _ fun x => ?_)
    dsimp only [Y]; congr 1; ring
  obtain ⟨hi, hb⟩ := DGRHS.CLT.exponential_sum_integral_cs X Y
    (aemeasurable_of_exp_double_integrable _ X hxi) (aemeasurable_of_exp_double_integrable _ Y hyi) hxi hyi
  have hxe : (fun x => Real.exp (u x + c x / 2)) = fun x => Real.exp (X x + Y x) := by
    funext x
    congr 1
    dsimp only [X, Y]
    rw [hu x]; ring
  have hxb : (∫ x, Real.exp (2 * X x) ∂P) ≤ B := by
    refine le_trans (le_of_eq (integral_congr_ae (ae_of_all _ fun x => ?_))) hB
    dsimp only [X]; congr 1; ring
  have hyb : (∫ x, Real.exp (2 * Y x) ∂P) ≤ Cub := by
    refine le_trans (le_of_eq (integral_congr_ae (ae_of_all _ fun x => ?_))) hCub
    dsimp only [Y]; congr 1; ring
  have hmain := gibbs_moment_of_numerator P u (fun x => c x / 2) hui z0
    (Real.sqrt B * Real.sqrt Cub) hz0 hz (by rw [hxe]; exact hi)
    (by rw [hxe]; exact hb.trans (mul_le_mul (Real.sqrt_le_sqrt hxb) (Real.sqrt_le_sqrt hyb)
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)))
  exact hmain

/-! ### The local numerator -/

/-- The transport energy statistic `N A_n` of the torus LOG kernel. -/
abbrev periodicLogA (ρ : PeriodicTorus ι → ℝ) [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (n : ℕ) (v : PeriodicTorus ι → E) (N : ℕ) (x : Fin N → PeriodicTorus ι) : ℝ :=
  (N : ℝ) * sourceTransportEnergy (periodicCappedDensityMeasure ρ) (periodicLogTransportKernel n v) N x

lemma periodicLog_u_eq (ρ : PeriodicTorus ι → ℝ) [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (γ : ℝ) (N : ℕ) (x : Fin N → PeriodicTorus ι) :
    periodicLogParticleExponent ρ γ N x = γ * periodicLogParticleExponent ρ 1 N x := by
  unfold periodicLogParticleExponent
  ring

/-- Local numerator, bounded by `e`, with the printed small-temperature parameter. -/
theorem periodicLog_local_numerator (n : ℕ) (hn : 1 ≤ n) :
    ∃ Csr : ℝ, 0 < Csr ∧ ∀ {K : ℝ≥0} {v : PeriodicTorus ι → E}, LipschitzWith K v → 0 < (K : ℝ) →
      ∀ (ρ : PeriodicTorus ι → ℝ) (M : ℝ), 0 ≤ M →
      ∀ [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)],
      (∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) →
      ∃ βloc : ℝ, 0 < βloc ∧ ∀ γ : ℝ, 0 ≤ γ → γ ≤ βloc → ∀ σ : ℝ, |σ| = 1 → ∀ N : ℕ, 0 < N →
        Integrable (fun x => Real.exp (periodicLogParticleExponent ρ γ N x +
          (σ * (γ / (4 * Csr * (K : ℝ) ^ n))) * periodicLogA ρ n v N x))
          (Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ)) ∧
        (∫ x, Real.exp (periodicLogParticleExponent ρ γ N x +
          (σ * (γ / (4 * Csr * (K : ℝ) ^ n))) * periodicLogA ρ n v N x)
          ∂Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ)) ≤ Real.exp 1 := by
  obtain ⟨C, hC, hb⟩ := periodicLogTransportKernel_bound (ι := ι) n hn
  refine ⟨C + 1, by linarith, ?_⟩
  intro K v hv hK ρ M hM hprob hρ
  let μ := periodicCappedDensityMeasure ρ
  obtain ⟨Cp, hCp, hrep⟩ := periodicLogParticleWeight_uniform 1 zero_le_one ρ M hM hρ
  let βloc := min (1 / 6 : ℝ) (min (1 / (16 * DGRHS.Attractive.attractiveMomentConstant))
    (1 / (6 * (Cp + 1))))
  have hA := DGRHS.Attractive.attractiveMomentConstant_pos
  have hloc : 0 < βloc := by
    dsimp [βloc]
    exact lt_min (by norm_num) (lt_min (by positivity) (by positivity))
  refine ⟨βloc, hloc, ?_⟩
  intro γ hγ hγloc σ hσ N hN
  have hγ6 : γ ≤ 1 / 6 := hγloc.trans (min_le_left _ _)
  have hγq : γ ≤ 1 / (16 * DGRHS.Attractive.attractiveMomentConstant) :=
    hγloc.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hγp : γ ≤ 1 / (6 * (Cp + 1)) :=
    hγloc.trans ((min_le_right _ _).trans (min_le_right _ _))
  let t := σ * (γ / (4 * (C + 1) * (K : ℝ) ^ n))
  have hscalar := local_log_transport_scalar C ((K : ℝ) ^ n) γ σ hC.le (pow_pos hK n) hγ hγ6 hγq hσ
  have hL : 0 ≤ C * (K : ℝ) ^ n := by positivity
  have hkm := periodicLogTransportKernel_measurable (ι := ι) n hv
  have hks : ∀ a b, periodicLogTransportKernel n v (a, b) = periodicLogTransportKernel n v (b, a) :=
    fun a b => (periodicLogTransportKernel_symm n v (a, b)).symm
  have ht2 : |2 * t| * (DGRHS.Attractive.attractiveMomentConstant * (4 * (C * (K : ℝ) ^ n))) < 1 := by
    have := hscalar.1
    simpa [t, mul_assoc] using this
  obtain ⟨hc, hcb⟩ := boundedKernel_energy_exponential μ (periodicLogTransportKernel n v) hkm hks
    (C * (K : ℝ) ^ n) hL (hb hv) (2 * t) ht2 N hN
  have hcBound : (∫ x : Fin N → PeriodicTorus ι,
      Real.exp ((2 * t) * (N : ℝ) * sourceTransportEnergy μ (periodicLogTransportKernel n v) N x)
      ∂Measure.pi (fun _ : Fin N => μ)) ≤ (128 / 63 : ℝ) * Real.exp (1 / 4) := by
    refine hcb.trans ?_
    have := hscalar.2
    simpa [t, mul_assoc] using this
  obtain ⟨hr, hrb, hrC⟩ := hrep N hN
  -- the repulsive exponent at temperature `2 γ` by interpolation
  let Eb := fun x : Fin N → PeriodicTorus ι => -periodicLogParticleExponent ρ 1 N x
  have hr' : Integrable (fun x => Real.exp (-Eb x)) (Measure.pi (fun _ : Fin N => μ)) := by
    simpa [Eb] using hr
  have hrb' : (∫ x, Real.exp (-Eb x) ∂Measure.pi (fun _ : Fin N => μ)) ≤ Cp := by
    simpa [Eb] using hrC
  obtain ⟨hri, hrbi⟩ := local_repulsive_interpolation
    (Measure.pi (fun _ : Fin N => μ)) Eb Cp γ hCp hr' hrb' hγ hγ6 hγp
  let X := fun x => periodicLogParticleExponent ρ γ N x
  let Y := fun x : Fin N → PeriodicTorus ι =>
    t * (N : ℝ) * sourceTransportEnergy μ (periodicLogTransportKernel n v) N x
  have hx : Integrable (fun x => Real.exp (2 * X x)) (Measure.pi (fun _ : Fin N => μ)) := by
    refine hri.congr (ae_of_all _ fun x => ?_)
    dsimp only [X, Eb]
    rw [periodicLog_u_eq ρ γ N x]
    congr 1; ring
  have hy : Integrable (fun x => Real.exp (2 * Y x)) (Measure.pi (fun _ : Fin N => μ)) := by
    refine hc.congr (ae_of_all _ fun x => ?_)
    dsimp only [Y]
    congr 1; ring
  obtain ⟨hi, hib⟩ := DGRHS.CLT.exponential_sum_integral_cs X Y
    (aemeasurable_of_exp_double_integrable _ X hx)
    (aemeasurable_of_exp_double_integrable _ Y hy) hx hy
  have hxb : (∫ x, Real.exp (2 * X x) ∂Measure.pi (fun _ : Fin N => μ)) ≤ 4 / 3 := by
    refine le_trans (le_of_eq (integral_congr_ae (ae_of_all _ fun x => ?_))) hrbi
    dsimp only [X, Eb]
    rw [periodicLog_u_eq ρ γ N x]
    congr 1; ring
  have hyb : (∫ x, Real.exp (2 * Y x) ∂Measure.pi (fun _ : Fin N => μ)) ≤
      (128 / 63 : ℝ) * Real.exp (1 / 4) := by
    refine le_trans (le_of_eq (integral_congr_ae (ae_of_all _ fun x => ?_))) hcBound
    dsimp only [Y]
    congr 1; ring
  have he : (fun x => Real.exp (X x + Y x)) = fun x => Real.exp (periodicLogParticleExponent ρ γ N x +
      (σ * (γ / (4 * (C + 1) * (K : ℝ) ^ n))) * periodicLogA ρ n v N x) := by
    funext x
    congr 1
    dsimp only [X, Y, t, periodicLogA]
    ring
  rw [he] at hi hib
  exact ⟨hi, hib.trans ((mul_le_mul (Real.sqrt_le_sqrt hxb) (Real.sqrt_le_sqrt hyb)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)).trans local_log_transport_cs_constant)⟩

end DGRHS.Periodic
#print axioms DGRHS.Periodic.periodicLog_local_numerator
