import DGRHS.Gaussian.PeriodicMeanFieldDrift
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
Packet P11e, unit 1 (part 5): periodic mollification of `C²` torus tests.

A torus test `ψ` with `C²` lift `g` is approximated by `C^∞` torus tests `χ` whose lifts are the
convolutions `φ ⋆ g` with a normed `C^∞` bump `φ` of small radius on `ℝ^d`.  Convolution preserves
lattice periodicity, so `φ ⋆ g` descends to the torus; its value and (by differentiation under the
integral sign, `hasFDerivAt_bump_convolution`) its first two Fréchet derivatives are the convolutions of
those of `g`.  Since `g` and its second derivative are continuous and periodic they are uniformly
continuous (`periodic_uniformContinuous`), so `φ ⋆ g → g` and `∇²(φ ⋆ g) → ∇²g` uniformly.  This replaces
the compact cutoff and mollifier modules of the Euclidean chain (`SourceCompactC2Mollifier`, ...).
-/

noncomputable section
open MeasureTheory Set Filter
open scoped NNReal Topology Convolution ContDiff
namespace DGRHS.Periodic
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]
local notation "E" => EuclideanSpace ℝ ι

lemma lipschitzWith_periodicLift : LipschitzWith 1 (periodicLift : E → PeriodicTorus ι) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [NNReal.coe_one, one_mul, dist_pi_le_iff dist_nonneg]
  intro i
  have h1 : dist (periodicLift x i) (periodicLift y i) ≤ |x i - y i| := by
    rw [dist_eq_norm]
    have : periodicLift x i - periodicLift y i = (((x i - y i : ℝ)) : UnitAddCircle) := by
      simp [periodicLift]
    rw [this]
    exact (QuotientAddGroup.norm_mk_le_norm).trans (le_of_eq (Real.norm_eq_abs _))
  refine h1.trans ?_
  have := PiLp.norm_apply_le (x - y) i
  rw [dist_eq_norm]
  simpa [Real.norm_eq_abs] using this

/-- A continuous lattice-periodic map into a metric space is uniformly continuous. -/
lemma periodic_uniformContinuous {W : Type*} [PseudoMetricSpace W] {G : E → W}
    (hG : Continuous G) (hper : ∀ x (m : PeriodicFrequency ι), G (x + periodicFrequencyVector m) = G x) :
    UniformContinuous G := by
  let G' : PeriodicTorus ι → W := fun z => G (periodicCenteredLift z)
  have hGG : ∀ x, G' (periodicLift x) = G x := by
    intro x
    obtain ⟨m, hm⟩ := periodicCenteredLift_periodicLift (ι := ι) x
    simp only [G', hm]
    exact hper x m
  have hG'c : Continuous G' := by
    apply continuous_of_continuous_periodicLift
    have : (fun x : E => G' (periodicLift x)) = G := funext hGG
    rw [this]; exact hG
  have hu : UniformContinuous G' := CompactSpace.uniformContinuous_of_continuous hG'c
  have : G = G' ∘ periodicLift := funext fun x => (hGG x).symm
  rw [this]
  exact hu.comp lipschitzWith_periodicLift.uniformContinuous

/-- Differentiation of a convolution with a bump, with the derivative moved onto the function. -/
lemma hasFDerivAt_bump_convolution {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [CompleteSpace V] (φ : E → ℝ) (hφc : Continuous φ) (hφs : HasCompactSupport φ)
    (g : E → V) (hg : ContDiff ℝ 1 g) (Bg : ℝ) (hBg : ∀ x, ‖g x‖ ≤ Bg) (B : ℝ)
    (hB : ∀ x, ‖fderiv ℝ g x‖ ≤ B) (x₀ : E) :
    HasFDerivAt (fun x => ∫ t, φ t • g (x - t)) (∫ t, φ t • fderiv ℝ g (x₀ - t)) x₀ := by
  have hφi : Integrable φ := hφc.integrable_of_hasCompactSupport hφs
  have hgc : Continuous g := hg.continuous
  have hg1c : Continuous (fderiv ℝ g) := hg.continuous_fderiv one_ne_zero
  have hshift : ∀ x : E, Continuous (fun t : E => x - t) := fun x => continuous_const.sub continuous_id
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (F := fun x t => φ t • g (x - t))
    (F' := fun x t => φ t • fderiv ℝ g (x - t)) (bound := fun t => |φ t| * B) (s := univ)
    univ_mem ?_ ?_ ?_ ?_ ?_ ?_
  · exact Eventually.of_forall fun x =>
      (hφc.smul (hgc.comp (hshift x))).aestronglyMeasurable
  · refine (hφi.abs.mul_const Bg).mono' ?_ (ae_of_all _ fun t => ?_)
    · exact (hφc.smul (hgc.comp (hshift x₀))).aestronglyMeasurable
    · rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hBg _) (abs_nonneg _)
  · exact (hφc.smul (hg1c.comp (hshift x₀))).aestronglyMeasurable
  · refine ae_of_all _ fun t x _ => ?_
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hB _) (abs_nonneg _)
  · exact hφi.abs.mul_const B
  · refine ae_of_all _ fun t x _ => ?_
    have h0 := ((hg.differentiable one_ne_zero) (x - t)).hasFDerivAt.comp x
        ((hasFDerivAt_id x).sub_const t)
    rw [ContinuousLinearMap.comp_id] at h0
    exact h0.const_smul (φ t)

lemma isLatticePeriodic_fderiv {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {g : E → V}
    (hper : ∀ x (m : PeriodicFrequency ι), g (x + periodicFrequencyVector m) = g x) :
    ∀ x (m : PeriodicFrequency ι),
      fderiv ℝ g (x + periodicFrequencyVector m) = fderiv ℝ g x := by
  intro x m
  have h : (fun y => g (y + periodicFrequencyVector m)) = g := funext fun y => hper y m
  have := fderiv_comp_add_right (f := g) (𝕜 := ℝ) (periodicFrequencyVector m) (x := x)
  rw [h] at this
  exact this.symm

/-- Smooth periodic approximation of a `C²` torus test, uniformly in the test and its Hessian. -/
theorem exists_periodic_smooth_approx (ψ : PeriodicTorus ι → ℝ) (hψ : ContDiff ℝ 2 (periodicLiftFn ψ))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ χ : PeriodicTorus ι → ℝ, ContDiff ℝ ∞ (periodicLiftFn χ) ∧
      (∀ x, |periodicLiftFn χ x - periodicLiftFn ψ x| ≤ ε) ∧
      (∀ x, ‖iteratedFDeriv ℝ 2 (periodicLiftFn χ) x - iteratedFDeriv ℝ 2 (periodicLiftFn ψ) x‖ ≤ ε) := by
  set g : E → ℝ := periodicLiftFn ψ with hgdef
  have hgper : ∀ x (m : PeriodicFrequency ι), g (x + periodicFrequencyVector m) = g x :=
    fun x m => isLatticePeriodic_periodicLiftFn ψ x m
  have hg1 : ContDiff ℝ 1 (fderiv ℝ g) := (contDiff_succ_iff_fderiv.mp hψ).2.2
  set g1 : E → (E →L[ℝ] ℝ) := fderiv ℝ g with hg1def
  set g2 : E → (E →L[ℝ] E →L[ℝ] ℝ) := fderiv ℝ g1 with hg2def
  have hg1per := isLatticePeriodic_fderiv hgper
  have hg2per := isLatticePeriodic_fderiv hg1per
  have hg1c : Continuous g1 := hg1.continuous
  have hg2c : Continuous g2 := hg1.continuous_fderiv one_ne_zero
  have hgc : Continuous g := hψ.continuous
  -- bounds
  obtain ⟨Bg, hBg0, hBg⟩ := periodic_continuous_bounded hgc hgper
  have hg1n : Continuous (fun x => ‖g1 x‖) := continuous_norm.comp hg1c
  obtain ⟨B1, hB10, hB1⟩ := periodic_continuous_bounded hg1n (fun x m => by
    exact congrArg norm (hg1per x m))
  obtain ⟨K2, hK2⟩ := exists_hessian_bound hψ
  have hB2 : ∀ x, ‖g2 x‖ ≤ (K2 : ℝ) := fun x => by
    have hn : ‖fderiv ℝ (fderiv ℝ g) x‖ = ‖iteratedFDeriv ℝ 2 g x‖ := by
      rw [← norm_iteratedFDeriv_one (fderiv ℝ g), norm_iteratedFDeriv_fderiv]
    exact hn ▸ hK2 x
  -- uniform continuity
  have hgu := periodic_uniformContinuous hgc hgper
  have hg2u := periodic_uniformContinuous hg2c hg2per
  obtain ⟨r1, hr1, h1⟩ := Metric.uniformContinuous_iff.mp hgu ε hε
  obtain ⟨r2, hr2, h2⟩ := Metric.uniformContinuous_iff.mp hg2u ε hε
  let r0 : ℝ := min r1 r2
  have hr0 : 0 < r0 := lt_min hr1 hr2
  let η : ContDiffBump (0 : E) := ⟨r0 / 2, r0, half_pos hr0, half_lt_self hr0⟩
  set φ : E → ℝ := η.normed volume with hφdef
  have hφc : Continuous φ := η.continuous_normed
  have hφs : HasCompactSupport φ := η.hasCompactSupport_normed
  -- the convolution
  set χ' : E → ℝ := fun x => ∫ t, φ t • g (x - t) with hχ'def
  have hχ'conv : χ' = (φ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g : E → ℝ) := rfl
  have hχ'smooth : ContDiff ℝ ∞ χ' := by
    rw [hχ'conv]
    exact hφs.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) η.contDiff_normed
      hgc.locallyIntegrable
  have hχ'per : ∀ x (m : PeriodicFrequency ι), χ' (x + periodicFrequencyVector m) = χ' x := by
    intro x m
    simp only [hχ'def]
    refine integral_congr_ae (ae_of_all _ fun t => ?_)
    have : x + periodicFrequencyVector m - t = (x - t) + periodicFrequencyVector m := by abel
    simp only [this, hgper]
  -- first derivative
  have hd1 : ∀ x, HasFDerivAt χ' (∫ t, φ t • g1 (x - t)) x := fun x =>
    hasFDerivAt_bump_convolution φ hφc hφs g (hψ.of_le (by norm_num)) Bg hBg B1 (fun y => by
      simpa using hB1 y) x
  have hf1 : fderiv ℝ χ' = fun x => ∫ t, φ t • g1 (x - t) := funext fun x => (hd1 x).fderiv
  -- second derivative
  have hd2 : ∀ x, HasFDerivAt (fderiv ℝ χ') (∫ t, φ t • g2 (x - t)) x := by
    intro x
    rw [hf1]
    exact hasFDerivAt_bump_convolution φ hφc hφs g1 hg1 B1 (fun y => by simpa using hB1 y) K2
      (fun y => by simpa using hB2 y) x
  have hf2 : fderiv ℝ (fderiv ℝ χ') = fun x => ∫ t, φ t • g2 (x - t) := funext fun x => (hd2 x).fderiv
  -- approximation estimates
  have happrox0 : ∀ x, |χ' x - g x| ≤ ε := by
    intro x
    have := ContDiffBump.dist_normed_convolution_le (g := g) (μ := volume) (φ := η) (x₀ := x)
      hgc.aestronglyMeasurable (ε := ε) (fun y hy => by
        refine (h1 (a := y) (b := x) ?_).le
        rw [Metric.mem_ball] at hy
        exact lt_of_lt_of_le hy (min_le_left _ _))
    have h : dist (χ' x) (g x) ≤ ε := this
    simpa only [Real.dist_eq] using h
  have happrox2 : ∀ x, ‖fderiv ℝ (fderiv ℝ χ') x - g2 x‖ ≤ ε := by
    intro x
    have := ContDiffBump.dist_normed_convolution_le (g := g2) (μ := volume) (φ := η) (x₀ := x)
      hg2c.aestronglyMeasurable (ε := ε) (fun y hy => by
        refine (h2 (a := y) (b := x) ?_).le
        rw [Metric.mem_ball] at hy
        exact lt_of_lt_of_le hy (min_le_right _ _))
    rw [hf2]
    exact ((dist_eq_norm _ _).symm).trans_le this
  -- descend to the torus
  let χ : PeriodicTorus ι → ℝ := fun z => χ' (periodicCenteredLift z)
  have hχlift : periodicLiftFn χ = χ' := by
    funext x
    obtain ⟨m, hm⟩ := periodicCenteredLift_periodicLift (ι := ι) x
    simp only [periodicLiftFn, χ, hm]
    exact hχ'per x m
  refine ⟨χ, by rw [hχlift]; exact hχ'smooth, by rw [hχlift]; exact happrox0, ?_⟩
  rw [hχlift]
  intro x
  have hχ2 : ContDiff ℝ 2 χ' := hχ'smooth.of_le (by exact WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  set q : E → ℝ := fun y => χ' y - g y with hqdef
  have hq : ContDiff ℝ 2 q := hχ2.sub hψ
  have he : iteratedFDeriv ℝ 2 q x = iteratedFDeriv ℝ 2 χ' x - iteratedFDeriv ℝ 2 g x :=
    iteratedFDeriv_sub_apply hχ2.contDiffAt hψ.contDiffAt
  have hn : ∀ w : E, ‖fderiv ℝ (fderiv ℝ q) w‖ = ‖iteratedFDeriv ℝ 2 q w‖ := fun w => by
    rw [← norm_iteratedFDeriv_one (fderiv ℝ q), norm_iteratedFDeriv_fderiv]
  have hq1 : fderiv ℝ q = fun y => fderiv ℝ χ' y - g1 y := by
    funext y
    exact fderiv_fun_sub (hχ2.differentiable (by norm_num) y) (hψ.differentiable (by norm_num) y)
  have hq2 : fderiv ℝ (fderiv ℝ q) x = fderiv ℝ (fderiv ℝ χ') x - g2 x := by
    rw [hq1]
    have hd1' : Differentiable ℝ (fderiv ℝ χ') :=
      (contDiff_succ_iff_fderiv.mp hχ2).2.2.differentiable one_ne_zero
    exact fderiv_fun_sub (hd1' x) ((hg1.differentiable one_ne_zero) x)
  rw [← he, ← hn x, hq2]
  exact happrox2 x

end DGRHS.Periodic
