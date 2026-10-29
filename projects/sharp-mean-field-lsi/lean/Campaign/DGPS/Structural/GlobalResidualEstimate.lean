import DGPS.Structural.ResidualEstimate
import DGPS.Structural.FrozenGibbsIdentities

/-!
# Global residual estimate (STR007)

If `μ` is the unique probability fixed point of the frozen Gibbs map `P` and the density Hessian
at `μ` is coercive (so the local estimate STR006 holds), then
`‖ν - μ‖_TV ≤ C_err ‖ν - Pν‖_TV` for **every** Borel probability `ν`, singular ones included.

Route: the local estimate covers `‖ν - μ‖_TV ≤ δ`.  Outside, suppose the residual could be
arbitrarily small.  A weak cluster point `ν` of the (ultrafilter-)limit exists by compactness of
`ProbabilityMeasure (Torus d)`; STR001 gives `P ν_n → P ν` uniformly in density, hence in
variation, so the small residual gives `ν_n → Pν` in variation, hence weakly.  Uniqueness of
weak limits yields `ν = Pν = μ`, so `ν_n → μ` in variation, contradicting `‖ν_n - μ‖_TV > δ`.
The variation exclusion set is never claimed weakly closed.
-/

open MeasureTheory Filter Topology
open scoped BoundedContinuousFunction

namespace DGPS.Structural

variable {d : ℕ}

/-- Densities uniformly `ε`-close give reference measures `ε`-close in full variation. -/
theorem fullVariation_boundedReference_le (P Q : BoundedPositiveReference d) {ε : ℝ}
    (h : ∀ x, |P.density x - Q.density x| ≤ ε) :
    fullVariation P.measure Q.measure ≤ ε := by
  have hP : P.measure ≪ haar d := P.measure_ac_haar
  have hQ : Q.measure ≪ haar d := Q.measure_ac_haar
  rw [fullVariation_eq_integral_abs P.measure Q.measure (haar d) hP hQ]
  have e : ∀ R : BoundedPositiveReference d, ∀ᵐ x ∂haar d,
      (R.measure.rnDeriv (haar d) x).toReal = R.density x := by
    intro R
    have h1 := Measure.rnDeriv_withDensity (haar d) R.measurable_ofReal_density
    filter_upwards [h1, R.ae_pos] with x hx hpos
    show ((((haar d).withDensity fun x => ENNReal.ofReal (R.density x)).rnDeriv (haar d)) x).toReal
      = _
    rw [hx, ENNReal.toReal_ofReal hpos.le]
  have hint : ∫ x, |(P.measure.rnDeriv (haar d) x).toReal - (Q.measure.rnDeriv (haar d) x).toReal|
      ∂haar d ≤ ∫ _x, ε ∂haar d := by
    refine integral_mono_ae ?_ (integrable_const ε) ?_
    · exact ((Measure.integrable_toReal_rnDeriv).sub (Measure.integrable_toReal_rnDeriv)).abs
    · filter_upwards [e P, e Q] with x h1 h2
      rw [h1, h2]
      exact h x
  simpa using hint

/-- Bounded continuous functionals are `‖f‖`-Lipschitz for the full variation. -/
theorem abs_integral_sub_le_fullVariation (ν η : Measure (Torus d)) [IsProbabilityMeasure ν]
    [IsProbabilityMeasure η] (f : Torus d →ᵇ ℝ) :
    |(∫ x, f x ∂ν) - ∫ x, f x ∂η| ≤ ‖f‖ * fullVariation ν η := by
  have hνa : ν ≪ ν + η := Measure.absolutelyContinuous_of_le (Measure.le_add_right le_rfl)
  have hηa : η ≪ ν + η := Measure.absolutelyContinuous_of_le (Measure.le_add_left le_rfl)
  rw [fullVariation_eq_integral_abs ν η (ν + η) hνa hηa,
    ← integral_toReal_rnDeriv_mul hνa, ← integral_toReal_rnDeriv_mul hηa]
  have i1 := Measure.integrable_toReal_rnDeriv (μ := ν) (ν := ν + η)
  have i2 := Measure.integrable_toReal_rnDeriv (μ := η) (ν := ν + η)
  have hb : ∀ (g : Torus d → ℝ), Integrable g (ν + η) →
      Integrable (fun x => g x * f x) (ν + η) := fun g hg =>
    hg.mul_bdd (c := ‖f‖) f.continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by simpa using f.norm_coe_le_norm x)
  rw [← integral_sub (hb _ i1) (hb _ i2)]
  calc |∫ x, ((ν.rnDeriv (ν + η) x).toReal * f x - (η.rnDeriv (ν + η) x).toReal * f x) ∂(ν + η)|
      ≤ ∫ x, ‖(ν.rnDeriv (ν + η) x).toReal * f x - (η.rnDeriv (ν + η) x).toReal * f x‖ ∂(ν + η) :=
        by simpa [Real.norm_eq_abs] using
          norm_integral_le_integral_norm (fun x => (ν.rnDeriv (ν + η) x).toReal * f x -
            (η.rnDeriv (ν + η) x).toReal * f x)
    _ ≤ ∫ x, ‖f‖ * |(ν.rnDeriv (ν + η) x).toReal - (η.rnDeriv (ν + η) x).toReal| ∂(ν + η) := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => norm_nonneg _) ?_
          (Filter.Eventually.of_forall fun x => ?_)
        · exact (((i1.sub i2).abs).const_mul ‖f‖)
        · beta_reduce
          rw [← sub_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs (f x), mul_comm]
          exact mul_le_mul (by simpa using f.norm_coe_le_norm x) le_rfl (abs_nonneg _)
            (norm_nonneg _)
    _ = _ := integral_const_mul _ _

theorem fullVariation_triangle (a b c : Measure (Torus d)) [IsProbabilityMeasure a]
    [IsProbabilityMeasure b] [IsProbabilityMeasure c] :
    fullVariation a c ≤ fullVariation a b + fullVariation b c := by
  rw [← norm_ofMeasure_sub, ← norm_ofMeasure_sub, ← norm_ofMeasure_sub]
  calc ‖SMeas.ofMeasure a - SMeas.ofMeasure c‖
      = ‖(SMeas.ofMeasure a - SMeas.ofMeasure b) + (SMeas.ofMeasure b - SMeas.ofMeasure c)‖ := by
        congr 1; abel
    _ ≤ _ := norm_add_le _ _

/-- The frozen Gibbs law as a `ProbabilityMeasure`. -/
noncomputable def frozenGibbsPM (A : InteractionData d) (ν : ProbabilityMeasure (Torus d)) :
    ProbabilityMeasure (Torus d) :=
  ⟨(frozenGibbs A ν).measure, inferInstance⟩

/-- Exterior estimate: away from the unique fixed point, the residual is bounded below. -/
theorem frozenResidual_exterior_lowerBound (A : InteractionData d)
    (μ : ProbabilityMeasure (Torus d))
    (huniq : ∀ ν : ProbabilityMeasure (Torus d),
      (ν : Measure (Torus d)) = (frozenGibbs A ν).measure → ν = μ)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ c : ℝ, 0 < c ∧ ∀ ν : ProbabilityMeasure (Torus d),
      δ < fullVariation (ν : Measure (Torus d)) (μ : Measure (Torus d)) →
        c ≤ fullVariation (ν : Measure (Torus d)) (frozenGibbs A ν).measure := by
  by_contra hcon
  push Not at hcon
  have hseq : ∀ n : ℕ, ∃ ν : ProbabilityMeasure (Torus d),
      δ < fullVariation (ν : Measure (Torus d)) (μ : Measure (Torus d)) ∧
        fullVariation (ν : Measure (Torus d)) (frozenGibbs A ν).measure < 1 / ((n : ℝ) + 1) :=
    fun n => hcon (1 / ((n : ℝ) + 1)) (by positivity)
  choose νs hνδ hνres using hseq
  let U : Ultrafilter ℕ := Ultrafilter.of atTop
  have hUle : (U : Filter ℕ) ≤ atTop := Ultrafilter.of_le _
  obtain ⟨ν, -, hν⟩ := isCompact_univ.ultrafilter_le_nhds (U.map νs) (by simp)
  have hνU : Tendsto νs U (𝓝 ν) := hν
  -- residual tends to zero along `U`
  have hres : Tendsto (fun n => fullVariation (νs n : Measure (Torus d))
      (frozenGibbs A (νs n)).measure) U (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le (tendsto_const_nhds)
      ((tendsto_one_div_add_atTop_nhds_zero_nat).mono_left hUle)
      (fun n => fullVariation_nonneg _ _) (fun n => (hνres n).le)
  -- uniform convergence of the frozen densities, hence variation convergence of `P ν_n`
  have hunif := frozenGibbs_weak_to_uniform A νs ν hνU
  have hPtv : Tendsto (fun n => fullVariation (frozenGibbs A (νs n)).measure
      (frozenGibbs A ν).measure) U (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have := (Metric.tendstoUniformly_iff.1 hunif) (ε / 2) (by positivity)
    filter_upwards [this] with n hn
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (fullVariation_nonneg _ _)]
    refine lt_of_le_of_lt (fullVariation_boundedReference_le _ _ (ε := ε / 2) fun x => ?_)
      (by linarith)
    have := hn x
    rw [Real.dist_eq, abs_sub_comm] at this
    exact this.le
  have hνtv : Tendsto (fun n => fullVariation (νs n : Measure (Torus d))
      (frozenGibbs A ν).measure) U (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa using hres.add hPtv) (fun n => fullVariation_nonneg _ _) (fun n => ?_)
    exact fullVariation_triangle _ (frozenGibbs A (νs n)).measure _
  -- the variation limit is also the weak limit
  have hweak : Tendsto νs U (𝓝 (frozenGibbsPM A ν)) := by
    rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
    intro f
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_)
      (by simpa using hνtv.const_mul ‖f‖)
    rw [Real.dist_eq]
    exact abs_integral_sub_le_fullVariation _ _ f
  have hEq : ν = frozenGibbsPM A ν := tendsto_nhds_unique hνU hweak
  have hfix : (ν : Measure (Torus d)) = (frozenGibbs A ν).measure :=
    congrArg (fun p : ProbabilityMeasure (Torus d) => (p : Measure (Torus d))) hEq
  have hνμ : ν = μ := huniq ν hfix
  have hlim : (frozenGibbs A ν).measure = (μ : Measure (Torus d)) := by
    rw [← hfix, hνμ]
  have hcg : ∀ n, fullVariation (νs n : Measure (Torus d)) (frozenGibbs A ν).measure =
      fullVariation (νs n : Measure (Torus d)) (μ : Measure (Torus d)) := fun n => by
    congr 1
  simp only [hcg] at hνtv
  have hev : ∀ᶠ n in (U : Filter ℕ), fullVariation (νs n : Measure (Torus d))
      (μ : Measure (Torus d)) < δ :=
    (Metric.tendsto_nhds.1 hνtv δ hδ).mono fun n hn => by
      rwa [Real.dist_eq, sub_zero, abs_of_nonneg (fullVariation_nonneg _ _)] at hn
  obtain ⟨n, hn⟩ := hev.exists
  exact absurd (hνδ n) (not_lt.2 hn.le)

/-- **STR007, global residual estimate.**  If `μ` is the unique probability fixed point of the
frozen Gibbs map and the density Hessian at `μ` is coercive (STR006), there is `C_err` with
`‖ν - μ‖_TV ≤ C_err ‖ν - Pν‖_TV` for every Borel probability `ν` (singular allowed). -/
theorem frozenResidual_global_errorBound (A : InteractionData d)
    (μ : ProbabilityMeasure (Torus d))
    (hμ : (frozenGibbs A μ).measure = (μ : Measure (Torus d)))
    (huniq : ∀ ν : ProbabilityMeasure (Torus d),
      (ν : Measure (Torus d)) = (frozenGibbs A ν).measure → ν = μ)
    (hH : IsCoerciveDensityHessian A μ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ν : ProbabilityMeasure (Torus d),
      fullVariation (ν : Measure (Torus d)) (μ : Measure (Torus d)) ≤
        C * fullVariation (ν : Measure (Torus d)) (frozenGibbs A ν).measure := by
  obtain ⟨δ, hδ, Cl, hCl, hloc⟩ := frozenResidual_local_errorBound A μ hμ hH
  obtain ⟨c, hc, hext⟩ := frozenResidual_exterior_lowerBound A μ huniq δ hδ
  refine ⟨max Cl (2 / c), le_max_of_le_left hCl, fun ν => ?_⟩
  by_cases hν : fullVariation (ν : Measure (Torus d)) (μ : Measure (Torus d)) ≤ δ
  · exact (hloc ν hν).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (fullVariation_nonneg _ _))
  · push Not at hν
    have h1 := hext ν hν
    have h2 := fullVariation_le_two (ν : Measure (Torus d)) (μ : Measure (Torus d))
    calc fullVariation (ν : Measure (Torus d)) (μ : Measure (Torus d)) ≤ 2 := h2
      _ = (2 / c) * c := by field_simp
      _ ≤ (2 / c) * fullVariation (ν : Measure (Torus d)) (frozenGibbs A ν).measure :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (fullVariation_nonneg _ _)

end DGPS.Structural
