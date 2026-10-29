import DGRHS.Gaussian.PeriodicDynamicTerminal
import DGRHS.Commutator.SourceRieszFiniteItoVolterra
import DGRHS.Commutator.SourceRieszTerminalPhase

/-!
Packet P11c, unit 3 (part 4): the characteristic-function comparison of Proposition 8.2
(`eq:dynamicBracketReplacement`, `eq:dynamicCharacteristicFactorization`, TeX 3952-4012) on the torus,
for an abstract periodic force, with Lemma 8.1(iii) entering as the hypothesis `hlin`.

The stopped squared gradient `S^r = |Σ_a θ_a ∇̃f_a^r|²` is expanded into pair terms
`Q_{ab} = ⟪∇̃f_a, ∇̃f_b⟫`, each of oscillation `≤ 2 Gmax²`, so that the bracket-replacement constant
`(2/β) Dl` is independent of the family size and of `θ` (as in the Euclidean statement).
-/

noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Laplacian Set
open scoped NNReal RealInnerProductSpace ENNReal BigOperators Classical Interval
namespace DGRHS.Periodic
open DGRHS.Commutator DGRHS.Dynamics
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]
local notation "E" => EuclideanSpace ℝ ι

lemma periodicStoppedGradNormSq (k : ℕ) (t θ : Fin k → ℝ) (f : Fin k → ℝ → PeriodicTorus ι → ℝ)
    (r : ℝ) (z : PeriodicTorus ι) :
    ‖∑ a : Fin k, θ a • periodicStoppedGrad (t a) (f a) r z‖ ^ 2 =
      ∑ a : Fin k, ∑ b : Fin k, (θ a * θ b) *
        ⟪periodicStoppedGrad (t a) (f a) r z, periodicStoppedGrad (t b) (f b) r z⟫ := by
  rw [← real_inner_self_eq_norm_sq, sum_inner]
  simp_rw [inner_sum, real_inner_smul_left, real_inner_smul_right, mul_assoc]

lemma periodicStopped_square_bound (k : ℕ) (t θ : Fin k → ℝ) (f : Fin k → ℝ → PeriodicTorus ι → ℝ)
    (G : ℝ≥0) (hb : ∀ a, ∀ r ∈ Icc 0 (t a), ∀ z, ‖periodicGrad (f a r) z‖ ≤ (G : ℝ))
    (r : ℝ) (z : PeriodicTorus ι) :
    ‖∑ a, θ a • periodicStoppedGrad (t a) (f a) r z‖ ^ 2 ≤ ((G : ℝ) * (∑ a, |θ a|)) ^ 2 := by
  have hnorm : ‖∑ a, θ a • periodicStoppedGrad (t a) (f a) r z‖ ≤ (G : ℝ) * (∑ a, |θ a|) := by
    calc
      _ ≤ ∑ a, ‖θ a • periodicStoppedGrad (t a) (f a) r z‖ := norm_sum_le _ _
      _ ≤ ∑ a, |θ a| * (G : ℝ) := by
        apply Finset.sum_le_sum; intro a _
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left
          (norm_periodicStoppedGrad_le (t a) (f a) G (hb a) r z) (abs_nonneg _)
      _ = _ := by rw [← Finset.sum_mul, mul_comm]
  exact pow_le_pow_left₀ (norm_nonneg _) hnorm 2

lemma measurable_periodicStopped_square (k : ℕ) (t θ : Fin k → ℝ) (f : Fin k → ℝ → PeriodicTorus ι → ℝ)
    (hf : ∀ a, ContinuousOn (fun p : ℝ × E => gradient (periodicLiftFn (f a p.1)) p.2)
      (Icc 0 (t a) ×ˢ univ)) :
    Measurable (fun p : ℝ × PeriodicTorus ι =>
      ‖∑ a, θ a • periodicStoppedGrad (t a) (f a) p.1 p.2‖ ^ 2) := by
  have heq : (fun p : ℝ × PeriodicTorus ι =>
      ‖∑ a, θ a • periodicStoppedGrad (t a) (f a) p.1 p.2‖ ^ 2) =
      (fun p => ∑ a, ∑ b, (θ a * θ b) * ⟪periodicStoppedGrad (t a) (f a) p.1 p.2,
        periodicStoppedGrad (t b) (f b) p.1 p.2⟫) :=
    funext fun p => periodicStoppedGradNormSq k t θ f p.1 p.2
  rw [heq]
  exact Finset.measurable_sum _ fun a _ => Finset.measurable_sum _ fun b _ =>
    ((measurable_periodicStoppedGrad (t a) (f a) (hf a)).inner
      (measurable_periodicStoppedGrad (t b) (f b) (hf b))).const_mul _

/-- Joint measurability of the empirical difference in time. -/
theorem measurable_dynEmpiricalDifference_time {Ω : Type*} [MeasurableSpace Ω]
    (ρ : ℝ → PeriodicTorus ι → ℝ) (hρ : Measurable (Function.uncurry ρ))
    (q : ℝ × PeriodicTorus ι → ℝ) (hq : Measurable q) (N : ℕ)
    (X : ℝ × Ω → Fin N → PeriodicTorus ι) (hX : Measurable X) :
    Measurable (fun p : ℝ × Ω => dynEmpiricalDifference (periodicCappedDensityMeasure (ρ p.1))
      (fun z => q (p.1, z)) N (X p)) := by
  let κ := DGRHS.Dynamics.sourceDensityKernel (periodicHaar ι) ρ
  letI := DGRHS.Dynamics.sourceDensityKernel_sfinite (periodicHaar ι) ρ
  have hκ (r : ℝ) : κ r = periodicCappedDensityMeasure (ρ r) :=
    DGRHS.Dynamics.sourceDensityKernel_apply (periodicHaar ι) ρ hρ r
  have hI : Measurable (fun r => ∫ z, q (r, z) ∂κ r) :=
    hq.stronglyMeasurable.integral_kernel_prod_right'.measurable
  have hsum : Measurable (fun p : ℝ × Ω => ∑ i : Fin N, q (p.1, X p i)) :=
    Finset.measurable_sum _ (fun i _ => hq.comp
      (measurable_fst.prodMk ((measurable_pi_apply i).comp hX)))
  simp_rw [dynEmpiricalDifference, integral_sourceRieszLocalEmpiricalLaw]
  have hh := (hsum.const_mul (N : ℝ)⁻¹).sub (hI.comp measurable_fst)
  change Measurable (fun p : ℝ × Ω => (N : ℝ)⁻¹ * (∑ i : Fin N, q (p.1, X p i)) -
    (∫ z, q (p.1, z) ∂κ p.1)) at hh
  simpa only [hκ] using hh

/-- Spatial properness justifies the square's empirical/background expansion. -/
lemma periodicStopped_square_difference (k : ℕ) (t θ : Fin k → ℝ)
    (f : Fin k → ℝ → PeriodicTorus ι → ℝ) (r : ℝ) (μ : Measure (PeriodicTorus ι)) (N : ℕ)
    (x : Fin N → PeriodicTorus ι)
    (hi : ∀ a b, Integrable (fun z => ⟪periodicStoppedGrad (t a) (f a) r z,
      periodicStoppedGrad (t b) (f b) r z⟫) μ) :
    ((∫ z, ‖∑ a, θ a • periodicStoppedGrad (t a) (f a) r z‖ ^ 2 ∂sourceRieszLocalEmpiricalLaw N x) -
      (∫ z, ‖∑ a, θ a • periodicStoppedGrad (t a) (f a) r z‖ ^ 2 ∂μ)) =
      ∑ a, ∑ b, (θ a * θ b) *
        ((∫ z, ⟪periodicStoppedGrad (t a) (f a) r z, periodicStoppedGrad (t b) (f b) r z⟫
          ∂sourceRieszLocalEmpiricalLaw N x) -
        (∫ z, ⟪periodicStoppedGrad (t a) (f a) r z, periodicStoppedGrad (t b) (f b) r z⟫ ∂μ)) := by
  simp_rw [periodicStoppedGradNormSq]
  rw [integral_finsetSum _ (fun a _ => integrable_finsetSum _ fun b _ =>
    (integrable_sourceRieszLocalEmpiricalLaw N x _).const_mul _),
    integral_finsetSum _ (fun a _ => integrable_finsetSum _ fun b _ => (hi a b).const_mul _)]
  simp_rw [integral_finsetSum _ (fun b _ => (integrable_sourceRieszLocalEmpiricalLaw N x _).const_mul _),
    integral_finsetSum _ (fun b _ => (hi _ b).const_mul _), integral_const_mul,
    ← Finset.sum_sub_distrib, ← mul_sub]

/-- Bracket replacement (`eq:dynamicBracketReplacement`, TeX 3961-3966): the product-`L¹` bound of
`(2/β)(∫ S^r dμ_N^r - ∫ S^r dμ^r)` from Lemma 8.1(iii) for the pair tests `Q_{ab}`. -/
theorem periodic_stopped_square_product_replacement (β T : ℝ) (hβ : 0 < β) (hT : 0 ≤ T) (k : ℕ)
    (t θ : Fin k → ℝ) (N : ℕ) (hN : 1 ≤ N) (Gmax : ℝ≥0) (Dl : ℝ) (hDl : 0 ≤ Dl)
    {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
    (ρ : ℝ → PeriodicTorus ι → ℝ) (hρm : Measurable (Function.uncurry ρ))
    (hprob : ∀ r ∈ Icc 0 T, IsProbabilityMeasure (periodicCappedDensityMeasure (ρ r)))
    (f : Fin k → ℝ → PeriodicTorus ι → ℝ)
    (hf : ∀ a, ContinuousOn (fun p : ℝ × E => gradient (periodicLiftFn (f a p.1)) p.2)
      (Icc 0 (t a) ×ˢ univ))
    (hfB : ∀ a, ∀ r ∈ Icc 0 (t a), ∀ z, ‖periodicGrad (f a r) z‖ ≤ (Gmax : ℝ))
    (X : ℝ → Ω → Fin N → PeriodicTorus ι) (hXm : Measurable (Function.uncurry X))
    (hlin : ∀ r ∈ Icc 0 T, ∀ q : PeriodicTorus ι → ℝ, Measurable q → BddBelow (range q) →
      BddAbove (range q) → sSup (range q) - sInf (range q) ≤ 2 * (Gmax : ℝ) ^ 2 →
      Integrable (fun ω => dynEmpiricalDifference (periodicCappedDensityMeasure (ρ r)) q N (X r ω)) ν ∧
      (∫ ω, |dynEmpiricalDifference (periodicCappedDensityMeasure (ρ r)) q N (X r ω)| ∂ν) ≤
        Dl / Real.sqrt N) :
    let S := fun r z => ‖∑ a, θ a • periodicStoppedGrad (t a) (f a) r z‖ ^ 2
    let J := fun r ω => (2 / β) * dynEmpiricalDifference (periodicCappedDensityMeasure (ρ r)) (S r) N
      (X r ω)
    Measurable (Function.uncurry J) ∧
    (∀ r ∈ Icc 0 T, Integrable (J r) ν ∧
      (∫ ω, |J r ω| ∂ν) ≤ ((2 / β) * Dl) * (∑ a : Fin k, |θ a|) ^ 2 / Real.sqrt N) ∧
    Integrable (Function.uncurry J) ((volume.restrict (Ioc 0 T)).prod ν) ∧
    Integrable (fun r => ∫ ω, |J r ω| ∂ν) (volume.restrict (Ioc 0 T)) ∧
    (∫ r in Ioc 0 T, ∫ ω, |J r ω| ∂ν) ≤ T * ((2 / β) * Dl) * (∑ a : Fin k, |θ a|) ^ 2 / Real.sqrt N := by
  intro S J
  have hc : 0 < (2 : ℝ) / β := div_pos (by norm_num) hβ
  let Q := fun a b (p : ℝ × PeriodicTorus ι) => ⟪periodicStoppedGrad (t a) (f a) p.1 p.2,
    periodicStoppedGrad (t b) (f b) p.1 p.2⟫
  have hQm (a b : Fin k) : Measurable (Q a b) :=
    (measurable_periodicStoppedGrad (t a) (f a) (hf a)).inner
      (measurable_periodicStoppedGrad (t b) (f b) (hf b))
  have hQb (a b : Fin k) (r : ℝ) (z : PeriodicTorus ι) : |Q a b (r, z)| ≤ (Gmax : ℝ) ^ 2 := by
    apply (abs_real_inner_le_norm _ _).trans
    simpa only [pow_two] using mul_le_mul
      (norm_periodicStoppedGrad_le (t a) (f a) Gmax (hfB a) r z)
      (norm_periodicStoppedGrad_le (t b) (f b) Gmax (hfB b) r z)
      (norm_nonneg _) Gmax.coe_nonneg
  let P := fun a b r ω => dynEmpiricalDifference (periodicCappedDensityMeasure (ρ r))
    (fun z => Q a b (r, z)) N (X r ω)
  have hpair (r : ℝ) (hr : r ∈ Icc 0 T) (a b : Fin k) :
      Integrable (fun z => Q a b (r, z)) (periodicCappedDensityMeasure (ρ r)) ∧
      Integrable (P a b r) ν ∧ (∫ ω, |P a b r ω| ∂ν) ≤ Dl / Real.sqrt N := by
    haveI := hprob r hr
    let q := fun z => Q a b (r, z)
    have hlo : BddBelow (range q) := ⟨-((Gmax : ℝ) ^ 2), by
      rintro y ⟨z, rfl⟩; exact (abs_le.mp (hQb a b r z)).1⟩
    have hup : BddAbove (range q) := ⟨(Gmax : ℝ) ^ 2, by
      rintro y ⟨z, rfl⟩; exact (abs_le.mp (hQb a b r z)).2⟩
    have hsup := csSup_le (range_nonempty q) (fun y hy => by
      rcases hy with ⟨z, rfl⟩; exact (abs_le.mp (hQb a b r z)).2)
    have hinf := le_csInf (range_nonempty q) (fun y hy => by
      rcases hy with ⟨z, rfl⟩; exact (abs_le.mp (hQb a b r z)).1)
    have hosc : sSup (range q) - sInf (range q) ≤ 2 * (Gmax : ℝ) ^ 2 := by linarith
    have hqm : Measurable q := (hQm a b).comp (measurable_const.prodMk measurable_id)
    obtain ⟨hi, hb⟩ := hlin r hr q hqm hlo hup hosc
    have hiq : Integrable q (periodicCappedDensityMeasure (ρ r)) :=
      (integrable_const ((Gmax : ℝ) ^ 2)).mono' hqm.aestronglyMeasurable
        (Filter.Eventually.of_forall fun z => by simpa only [Real.norm_eq_abs] using hQb a b r z)
    exact ⟨hiq, hi, hb⟩
  have hSm : Measurable (fun p : ℝ × PeriodicTorus ι => S p.1 p.2) := by
    have heq : (fun p : ℝ × PeriodicTorus ι => S p.1 p.2) = (fun p => ∑ a, ∑ b, (θ a * θ b) * Q a b p) :=
      funext fun p => periodicStoppedGradNormSq k t θ f p.1 p.2
    rw [heq]
    exact Finset.measurable_sum _ fun a _ => Finset.measurable_sum _ fun b _ => (hQm a b).const_mul _
  have hJm : Measurable (Function.uncurry J) :=
    (measurable_dynEmpiricalDifference_time ρ hρm _ hSm N (Function.uncurry X) hXm).const_mul _
  have hslice (r : ℝ) (hr : r ∈ Icc 0 T) : Integrable (J r) ν ∧
      (∫ ω, |J r ω| ∂ν) ≤ ((2 / β) * Dl) * (∑ a : Fin k, |θ a|) ^ 2 / Real.sqrt N := by
    obtain ⟨hi, hb⟩ := sourceRiesz_weighted_finite_L1 ν k θ (fun a b => P a b r) (Dl / Real.sqrt N)
      (fun a b => (hpair r hr a b).2.1) (fun a b => (hpair r hr a b).2.2)
    haveI := hprob r hr
    have hXr : Measurable (X r) := hXm.comp (measurable_const.prodMk measurable_id)
    have heq (ω : Ω) : dynEmpiricalDifference (periodicCappedDensityMeasure (ρ r)) (S r) N (X r ω) =
        ∑ a, ∑ b, (θ a * θ b) * P a b r ω := by
      change (∫ z, S r z ∂sourceRieszLocalEmpiricalLaw N (X r ω)) -
        (∫ z, S r z ∂periodicCappedDensityMeasure (ρ r)) = _
      exact periodicStopped_square_difference k t θ f r (periodicCappedDensityMeasure (ρ r)) N (X r ω)
        (fun a b => (hpair r hr a b).1)
    have hdi : Integrable (fun ω => dynEmpiricalDifference (periodicCappedDensityMeasure (ρ r)) (S r) N
        (X r ω)) ν :=
      hi.congr (Filter.Eventually.of_forall fun ω => (heq ω).symm)
    refine ⟨hdi.const_mul _, ?_⟩
    calc
      (∫ ω, |J r ω| ∂ν) = (2 / β) * (∫ ω, |∑ a, ∑ b, (θ a * θ b) * P a b r ω| ∂ν) := by
        simp only [J, abs_mul, abs_of_pos hc, heq]
        exact integral_const_mul _ _
      _ ≤ (2 / β) * ((Dl / Real.sqrt N) * (∑ a : Fin k, |θ a|) ^ 2) :=
        mul_le_mul_of_nonneg_left hb hc.le
      _ = _ := by ring
  let η := volume.restrict (Ioc 0 T)
  have hslices : ∀ᵐ r ∂η, Integrable (J r) ν ∧
      (∫ ω, |J r ω| ∂ν) ≤ ((2 / β) * Dl) * (∑ a : Fin k, |θ a|) ^ 2 / Real.sqrt N := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact hslice r ⟨hr.1.le, hr.2⟩
  obtain ⟨hi, -, -⟩ := sourceRiesz_time_integral_from_slices η ν J hJm
    (((2 / β) * Dl) * (∑ a : Fin k, |θ a|) ^ 2 / Real.sqrt N)
    (hslices.mono fun r hr => hr.1) (hslices.mono fun r hr => hr.2)
  refine ⟨hJm, hslice, hi, hi.abs.integral_prod_left, ?_⟩
  calc
    (∫ r in Ioc 0 T, ∫ ω, |J r ω| ∂ν) ≤
        ∫ _ : ℝ, ((2 / β) * Dl) * (∑ a : Fin k, |θ a|) ^ 2 / Real.sqrt N ∂η :=
      integral_mono_ae hi.abs.integral_prod_left (integrable_const _) (hslices.mono fun r hr => hr.2)
    _ = _ := by
      rw [integral_const, smul_eq_mul, measureReal_restrict_apply_univ,
        Real.volume_real_Ioc_of_le hT, sub_zero]
      ring

/-- The finite-`N` characteristic-function comparison from the literal finite Itô formula for the
phase and the bracket replacement (TeX 3971-3997, `eq:dynamicCharacteristicFactorization`). -/
theorem periodic_physical_finite_Ito_comparison (β T : ℝ) (hβ : 0 < β) (hT : 0 ≤ T) (k : ℕ)
    (t θ : Fin k → ℝ) (N : ℕ) (hN : 1 ≤ N) (Gmax : ℝ≥0) (Dl : ℝ) (hDl : 0 ≤ Dl)
    {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
    (ρ : ℝ → PeriodicTorus ι → ℝ) (hρm : Measurable (Function.uncurry ρ))
    (hprob : ∀ r ∈ Icc 0 T, IsProbabilityMeasure (periodicCappedDensityMeasure (ρ r)))
    (f : Fin k → ℝ → PeriodicTorus ι → ℝ)
    (hf : ∀ a, ContinuousOn (fun p : ℝ × E => gradient (periodicLiftFn (f a p.1)) p.2)
      (Icc 0 (t a) ×ˢ univ))
    (hfB : ∀ a, ∀ r ∈ Icc 0 (t a), ∀ z, ‖periodicGrad (f a r) z‖ ≤ (Gmax : ℝ))
    (X : ℝ → Ω → Fin N → PeriodicTorus ι) (hXm : Measurable (Function.uncurry X))
    (hlin : ∀ r ∈ Icc 0 T, ∀ q : PeriodicTorus ι → ℝ, Measurable q → BddBelow (range q) →
      BddAbove (range q) → sSup (range q) - sInf (range q) ≤ 2 * (Gmax : ℝ) ^ 2 →
      Integrable (fun ω => dynEmpiricalDifference (periodicCappedDensityMeasure (ρ r)) q N (X r ω)) ν ∧
      (∫ ω, |dynEmpiricalDifference (periodicCappedDensityMeasure (ρ r)) q N (X r ω)| ∂ν) ≤
        Dl / Real.sqrt N)
    (A₀ : Ω → ℝ) (hA₀ : Measurable A₀) (M₀ : ℝ → Ω → ℝ) (hM₀ : Measurable (Function.uncurry M₀)) :
    let S := fun r z => ‖∑ a, θ a • periodicStoppedGrad (t a) (f a) r z‖ ^ 2
    let H := fun r ω => ∫ z, S r z ∂sourceRieszLocalEmpiricalLaw N (X r ω)
    let m := fun r => ∫ z, S r z ∂periodicCappedDensityMeasure (ρ r)
    let Φ := fun r ω => sourceRieszFinitePhase (A₀ ω + M₀ r ω)
    let chi := fun r => ∫ ω, Φ r ω ∂ν
    (∀ r ∈ Icc 0 T, chi r = chi 0 - (1 / β : ℝ) •
      (∫ u in 0..r, ∫ ω, Φ u ω * (H u ω : ℂ) ∂ν)) →
    ‖chi T - chi 0 * (Real.exp (-(1 / β) * (∫ r in 0..T, m r)) : ℂ)‖ ≤
      Real.exp ((((Gmax : ℝ) * (∑ a : Fin k, |θ a|)) ^ 2 / β) * T) *
        (T * ((2 / β) * Dl) * (∑ a : Fin k, |θ a|) ^ 2 / Real.sqrt N) := by
  intro S H m Φ chi hIto
  let C := ((Gmax : ℝ) * (∑ a : Fin k, |θ a|)) ^ 2
  have hC : 0 ≤ C := sq_nonneg _
  have hSm : Measurable (fun p : ℝ × PeriodicTorus ι => S p.1 p.2) :=
    measurable_periodicStopped_square k t θ f hf
  have hSb (r : ℝ) (z : PeriodicTorus ι) : S r z ∈ Icc 0 C :=
    ⟨sq_nonneg _, periodicStopped_square_bound k t θ f Gmax hfB r z⟩
  have hHm : Measurable (Function.uncurry H) := by
    have heq : Function.uncurry H = (fun p : ℝ × Ω => (N : ℝ)⁻¹ * ∑ i : Fin N, S p.1 (X p.1 p.2 i)) :=
      funext fun p => integral_sourceRieszLocalEmpiricalLaw N (X p.1 p.2) _
    rw [heq]
    exact (Finset.measurable_sum _ fun i _ => hSm.comp
      (measurable_fst.prodMk ((measurable_pi_apply i).comp hXm))).const_mul _
  have hHb (r : ℝ) (hr : r ∈ Icc 0 T) (ω : Ω) : |H r ω| ≤ C := by
    haveI := sourceRieszLocalEmpiricalLaw_probability N (by omega : 0 < N) (X r ω)
    have hh : ∀ᵐ z ∂sourceRieszLocalEmpiricalLaw N (X r ω), ‖S r z‖ ≤ C :=
      Filter.Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hSb r z).1]
        exact (hSb r z).2
    simpa only [Real.norm_eq_abs, measureReal_def, measure_univ, ENNReal.toReal_one, mul_one] using
      norm_integral_le_of_norm_le_const (μ := sourceRieszLocalEmpiricalLaw N (X r ω)) hh
  let κ := DGRHS.Dynamics.sourceDensityKernel (periodicHaar ι) ρ
  letI := DGRHS.Dynamics.sourceDensityKernel_sfinite (periodicHaar ι) ρ
  have hκ (r : ℝ) : κ r = periodicCappedDensityMeasure (ρ r) :=
    DGRHS.Dynamics.sourceDensityKernel_apply (periodicHaar ι) ρ hρm r
  have hmm : Measurable m := by
    simpa only [hκ] using (hSm.stronglyMeasurable.integral_kernel_prod_right' (κ := κ)).measurable
  have hmb (r : ℝ) (hr : r ∈ Icc 0 T) : 0 ≤ m r ∧ m r ≤ C := by
    haveI := hprob r hr
    refine ⟨integral_nonneg fun z => (hSb r z).1, ?_⟩
    apply (le_abs_self _).trans
    have hh : ∀ᵐ z ∂periodicCappedDensityMeasure (ρ r), ‖S r z‖ ≤ C :=
      Filter.Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hSb r z).1]
        exact (hSb r z).2
    simpa only [Real.norm_eq_abs, measureReal_def, measure_univ, ENNReal.toReal_one, mul_one] using
      norm_integral_le_of_norm_le_const (μ := periodicCappedDensityMeasure (ρ r)) hh
  have hh := sourceRiesz_finite_Ito_volterra ν T β C hT hβ hC A₀ hA₀ M₀ H hM₀ hHm hHb m hmm hmb hIto
  obtain ⟨-, -, -, -, hb⟩ := periodic_stopped_square_product_replacement β T hβ hT k t θ N hN Gmax Dl hDl
    ν ρ hρm hprob f hf hfB X hXm hlin
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  exact hb

/-- Finite-`N` terminal characteristic-function comparison (TeX 3933-4012): the terminal
representation of `Σ θ_a S_N^{t_a}(φ_a)` and the factorization of the phase expectation. -/
theorem periodic_finite_terminal_CF_comparison (D : PeriodicForceData ι) (β M : ℝ) (hβ : 0 < β)
    (hM : 0 ≤ M) (K Gmax : ℝ≥0) (T : ℝ) (hT : 0 ≤ T) (k : ℕ) (t θ : Fin k → ℝ)
    (ht : ∀ a, t a ∈ Icc 0 T) (N : ℕ) (hN : 1 ≤ N) (Dc Dl : ℝ) (hDc : 0 ≤ Dc) (hDl : 0 ≤ Dl)
    {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
    (ρ : ℝ → PeriodicTorus ι → ℝ) (hρm : Measurable (Function.uncurry ρ))
    (hprob : ∀ r ∈ Icc 0 T, IsProbabilityMeasure (periodicCappedDensityMeasure (ρ r)))
    (hρ : ∀ r ∈ Icc 0 T, ∀ᵐ z ∂periodicHaar ι, ρ r z ≤ M)
    (f : Fin k → ℝ → PeriodicTorus ι → ℝ)
    (hfd : ∀ a, ∀ r ∈ Icc 0 (t a), ContDiff ℝ 2 (periodicLiftFn (f a r)))
    (hK : ∀ a, ∀ r ∈ Icc 0 (t a), ∀ z, ‖iteratedFDeriv ℝ 2 (periodicLiftFn (f a r)) z‖ ≤ (K : ℝ))
    (hgrad : ∀ a, ContinuousOn (fun p : ℝ × E => gradient (periodicLiftFn (f a p.1)) p.2)
      (Icc 0 (t a) ×ˢ univ))
    (hfB : ∀ a, ∀ r ∈ Icc 0 (t a), ∀ z, ‖periodicGrad (f a r) z‖ ≤ (Gmax : ℝ))
    (L : ℝ) (hL : ∀ a, ∀ r ∈ Icc 0 (t a), ∀ z, |f a r z| ≤ L)
    (hback : ∀ a, ∀ᵐ r ∂volume.restrict (Ioc 0 (t a)), PeriodicBackwardEq D.F β (ρ r) (f a) r)
    (X : ℝ → Ω → Fin N → PeriodicTorus ι) (hXm : Measurable (Function.uncurry X))
    (hA1 : ∀ a, ∀ r ∈ Icc 0 (t a),
      Integrable (fun ω => sourceTransportEnergy (periodicCappedDensityMeasure (ρ r))
        (periodicForcePair D.F (periodicGrad (f a r))) N (X r ω)) ν ∧
      (∫ ω, |sourceTransportEnergy (periodicCappedDensityMeasure (ρ r))
        (periodicForcePair D.F (periodicGrad (f a r))) N (X r ω)| ∂ν) ≤ Dc / (N : ℝ))
    (hlin : ∀ r ∈ Icc 0 T, ∀ q : PeriodicTorus ι → ℝ, Measurable q → BddBelow (range q) →
      BddAbove (range q) → sSup (range q) - sInf (range q) ≤ 2 * (Gmax : ℝ) ^ 2 →
      Integrable (fun ω => dynEmpiricalDifference (periodicCappedDensityMeasure (ρ r)) q N (X r ω)) ν ∧
      (∫ ω, |dynEmpiricalDifference (periodicCappedDensityMeasure (ρ r)) q N (X r ω)| ∂ν) ≤
        Dl / Real.sqrt N)
    (m : Fin k → ℝ → Ω → ℝ) (hmm : ∀ a, Measurable (Function.uncurry (m a)))
    (hm0 : ∀ a ω, m a 0 ω = 0)
    (hIto : ∀ a, ∀ᵐ ω ∂ν, (∫ z, f a (t a) z ∂sourceRieszLocalEmpiricalLaw N (X (t a) ω)) -
      (∫ z, f a 0 z ∂sourceRieszLocalEmpiricalLaw N (X 0 ω)) =
      (∫ r in Ioc 0 (t a), periodicEmpiricalTestDrift D.F β (f a) N r (X r ω)) + m a (t a) ω)
    (hweak : ∀ a, (∫ z, f a (t a) z ∂periodicCappedDensityMeasure (ρ (t a))) -
      (∫ z, f a 0 z ∂periodicCappedDensityMeasure (ρ 0)) =
      ∫ r in Ioc 0 (t a), periodicMeanTestDrift D.F β (ρ r) (f a) r) :
    let A₀ := fun ω => ∑ a, θ a * (Real.sqrt N *
      dynEmpiricalDifference (periodicCappedDensityMeasure (ρ 0)) (f a 0) N (X 0 ω))
    let Z := fun ω => ∑ a, θ a * (Real.sqrt N *
      dynEmpiricalDifference (periodicCappedDensityMeasure (ρ (t a))) (f a (t a)) N (X (t a) ω))
    let W := fun r ω => ∑ a, θ a * (Real.sqrt N * m a (min r (t a)) ω)
    let S := fun r z => ‖∑ a, θ a • periodicStoppedGrad (t a) (f a) r z‖ ^ 2
    let Φ := fun r ω => sourceRieszFinitePhase (A₀ ω + W r ω)
    let chi := fun r => ∫ ω, Φ r ω ∂ν
    (∀ r ∈ Icc 0 T, chi r = chi 0 - (1 / β : ℝ) •
      (∫ u in 0..r, ∫ ω, Φ u ω * ((∫ z, S u z ∂sourceRieszLocalEmpiricalLaw N (X u ω) : ℝ) : ℂ) ∂ν)) →
    ‖(∫ ω, sourceRieszFinitePhase (Z ω) ∂ν) -
      (∫ ω, sourceRieszFinitePhase (A₀ ω) ∂ν) *
        (Real.exp (-(1 / β) * (∫ r in 0..T, ∫ z, S r z ∂periodicCappedDensityMeasure (ρ r))) : ℂ)‖ ≤
      T * Dc * (∑ a, |θ a|) / (2 * Real.sqrt N) +
        Real.exp ((((Gmax : ℝ) * (∑ a, |θ a|)) ^ 2 / β) * T) *
          (T * ((2 / β) * Dl) * (∑ a, |θ a|) ^ 2 / Real.sqrt N) := by
  intro A₀ Z W S Φ chi hphase
  obtain ⟨hA₀, hZ, hRm, hRi, hRb, hrep⟩ := periodic_finite_terminal_representation D β M hM K T hT k t θ ht
    N hN Dc hDc ν ρ hρm hprob hρ f hfd hK hgrad L hL hback X hXm hA1 (fun a => m a (t a)) hIto hweak
  have hWm : Measurable (Function.uncurry W) := by
    apply Finset.measurable_sum
    intro a _
    exact (((hmm a).comp ((measurable_fst.min measurable_const).prodMk measurable_snd)).const_mul _).const_mul _
  have hWT (ω : Ω) : W T ω = ∑ a, θ a * (Real.sqrt N * m a (t a) ω) := by
    dsimp only [W]
    apply Finset.sum_congr rfl
    intro a _
    rw [min_eq_right (ht a).2]
  have hW0 (ω : Ω) : W 0 ω = 0 := by
    dsimp only [W]
    have hh (a : Fin k) : min 0 (t a) = 0 := min_eq_left (ht a).1
    simp only [hh, hm0, mul_zero, Finset.sum_const_zero]
  have hcomp := periodic_physical_finite_Ito_comparison β T hβ hT k t θ N hN Gmax Dl hDl ν ρ hρm hprob f
    hgrad hfB X hXm hlin A₀ hA₀ W hWm hphase
  simp only [hW0, add_zero] at hcomp
  have hY : Measurable (fun ω => A₀ ω + W T ω) :=
    hA₀.add (hWm.comp (measurable_const.prodMk measurable_id))
  obtain ⟨-, -, hpert⟩ := sourceRiesz_terminal_phase_expectation ν (fun ω => A₀ ω + W T ω)
    (fun ω => ∑ a, θ a * (-((Real.sqrt N / 2) * (∫ r in Ioc 0 (t a),
      sourceTransportEnergy (periodicCappedDensityMeasure (ρ r))
        (periodicForcePair D.F (periodicGrad (f a r))) N (X r ω))))) hY hRm hRi
  have he : (∫ ω, sourceRieszFinitePhase (Z ω) ∂ν) =
      ∫ ω, sourceRieszFinitePhase (A₀ ω + W T ω + ∑ a, θ a * (-((Real.sqrt N / 2) *
        (∫ r in Ioc 0 (t a), sourceTransportEnergy (periodicCappedDensityMeasure (ρ r))
          (periodicForcePair D.F (periodicGrad (f a r))) N (X r ω))))) ∂ν := by
    apply integral_congr_ae
    filter_upwards [hrep] with ω hω
    exact congrArg sourceRieszFinitePhase (hω.trans (by rw [hWT]))
  calc
    _ ≤ ‖(∫ ω, sourceRieszFinitePhase (Z ω) ∂ν) -
        (∫ ω, sourceRieszFinitePhase (A₀ ω + W T ω) ∂ν)‖ +
      ‖(∫ ω, sourceRieszFinitePhase (A₀ ω + W T ω) ∂ν) -
        (∫ ω, sourceRieszFinitePhase (A₀ ω) ∂ν) *
          (Real.exp (-(1 / β) * (∫ r in 0..T, ∫ z, S r z ∂periodicCappedDensityMeasure (ρ r))) : ℂ)‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ _ := add_le_add (by rw [he]; exact hpert.trans hRb) hcomp

end DGRHS.Periodic
