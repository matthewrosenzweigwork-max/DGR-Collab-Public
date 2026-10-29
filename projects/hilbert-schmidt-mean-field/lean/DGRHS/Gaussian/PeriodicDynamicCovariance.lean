import DGRHS.Gaussian.PeriodicDynamicCF
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
Packet P11c, unit 4 (part 1): the time part of the covariance (2.42) (TeX 905-912) on the torus,
`periodicDynamicTimeCovariance β ρ k t f a b = (2/β) ∫_{(0, t_a ∧ t_b]} ∫ ⟪∇f_a^r, ∇f_b^r⟫ dμ_r dr`,
its quadratic form `(2/β) ∫_0^T ∫ |Σ θ_a ∇̃f_a^r|² dμ_r dr` and positive semidefiniteness.
Torus form of `DGRHS.Dynamics.sourceDynamicTimeCovariance` and its lemmas.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal RealInnerProductSpace BigOperators Classical
namespace DGRHS.Periodic
open DGRHS.Commutator
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]
local notation "E" => EuclideanSpace ℝ ι

def periodicDynamicTimeCovariance (β : ℝ) (ρ : ℝ → PeriodicTorus ι → ℝ) (k : ℕ)
    (t : Fin k → ℝ) (f : Fin k → ℝ → PeriodicTorus ι → ℝ) (a b : Fin k) : ℝ :=
  (2 / β) * ∫ r in Ioc 0 (min (t a) (t b)),
    ∫ z, ⟪periodicGrad (f a r) z, periodicGrad (f b r) z⟫ ∂periodicCappedDensityMeasure (ρ r)

def periodicCrossGradientCut (T : ℝ) (f g : ℝ → PeriodicTorus ι → ℝ) : ℝ × PeriodicTorus ι → ℝ :=
  (Icc 0 T ×ˢ (univ : Set (PeriodicTorus ι))).piecewise
    (fun p => ⟪periodicGrad (f p.1) p.2, periodicGrad (g p.1) p.2⟫) (fun _ => 0)

lemma periodicStoppedGrad_inner_eq_cut (ta tb : ℝ) (f g : ℝ → PeriodicTorus ι → ℝ)
    (r : ℝ) (z : PeriodicTorus ι) :
    ⟪periodicStoppedGrad ta f r z, periodicStoppedGrad tb g r z⟫ =
      periodicCrossGradientCut (min ta tb) f g (r, z) := by
  have hh : (r, z) ∈ Icc 0 (min ta tb) ×ˢ (univ : Set (PeriodicTorus ι)) ↔
      r ∈ Icc 0 ta ∧ r ∈ Icc 0 tb := by
    simp only [mem_prod, mem_univ, and_true, mem_Icc, le_min_iff]
    tauto
  by_cases ha : r ∈ Icc 0 ta <;> by_cases hb : r ∈ Icc 0 tb <;>
    simp only [periodicStoppedGrad, periodicCrossGradientCut, Set.piecewise, hh, ha, hb, ite_true,
      ite_false, inner_zero_right, inner_zero_left, true_and, false_and]

lemma periodic_stopped_pair_proper (T : ℝ) (ρ : ℝ → PeriodicTorus ι → ℝ)
    (hρ : Measurable (Function.uncurry ρ))
    (hp : ∀ r ∈ Icc 0 T, IsProbabilityMeasure (periodicCappedDensityMeasure (ρ r)))
    (k : ℕ) (t : Fin k → ℝ) (f : Fin k → ℝ → PeriodicTorus ι → ℝ) (G : ℝ≥0)
    (hf : ∀ a, ContinuousOn (fun p : ℝ × E => gradient (periodicLiftFn (f a p.1)) p.2)
      (Icc 0 (t a) ×ˢ univ))
    (hb : ∀ a, ∀ r ∈ Icc 0 (t a), ∀ z, ‖periodicGrad (f a r) z‖ ≤ (G : ℝ)) (a b : Fin k) :
    (∀ r ∈ Icc 0 T, Integrable (fun z => ⟪periodicStoppedGrad (t a) (f a) r z,
        periodicStoppedGrad (t b) (f b) r z⟫) (periodicCappedDensityMeasure (ρ r))) ∧
    Integrable (fun r => ∫ z, ⟪periodicStoppedGrad (t a) (f a) r z,
      periodicStoppedGrad (t b) (f b) r z⟫ ∂periodicCappedDensityMeasure (ρ r))
      (volume.restrict (Ioc 0 T)) := by
  let Q := fun p : ℝ × PeriodicTorus ι => ⟪periodicStoppedGrad (t a) (f a) p.1 p.2,
    periodicStoppedGrad (t b) (f b) p.1 p.2⟫
  have hQ : Measurable Q :=
    (measurable_periodicStoppedGrad (t a) (f a) (hf a)).inner
      (measurable_periodicStoppedGrad (t b) (f b) (hf b))
  have hbound (r : ℝ) (z : PeriodicTorus ι) : |Q (r, z)| ≤ (G : ℝ) ^ 2 := by
    apply (abs_real_inner_le_norm _ _).trans
    simpa only [pow_two] using mul_le_mul
      (norm_periodicStoppedGrad_le (t a) (f a) G (hb a) r z)
      (norm_periodicStoppedGrad_le (t b) (f b) G (hb b) r z)
      (norm_nonneg _) G.coe_nonneg
  have hspace (r : ℝ) (hr : r ∈ Icc 0 T) :
      Integrable (fun z => Q (r, z)) (periodicCappedDensityMeasure (ρ r)) := by
    haveI := hp r hr
    apply (integrable_const ((G : ℝ) ^ 2)).mono'
      (hQ.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun z => by
      simpa only [Real.norm_eq_abs, Function.comp_apply, id_eq] using hbound r z
  let κ := DGRHS.Dynamics.sourceDensityKernel (periodicHaar ι) ρ
  letI := DGRHS.Dynamics.sourceDensityKernel_sfinite (periodicHaar ι) ρ
  have hκ (r : ℝ) : κ r = periodicCappedDensityMeasure (ρ r) :=
    DGRHS.Dynamics.sourceDensityKernel_apply (periodicHaar ι) ρ hρ r
  have hm : Measurable (fun r => ∫ z, Q (r, z) ∂periodicCappedDensityMeasure (ρ r)) := by
    simpa only [hκ] using (hQ.stronglyMeasurable.integral_kernel_prod_right' (κ := κ)).measurable
  refine ⟨hspace, ?_⟩
  apply (integrable_const ((G : ℝ) ^ 2)).mono' hm.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
  haveI := hp r ⟨hr.1.le, hr.2⟩
  simpa only [measureReal_def, measure_univ, ENNReal.toReal_one, mul_one] using
    (norm_integral_le_of_norm_le_const (μ := periodicCappedDensityMeasure (ρ r))
      (Filter.Eventually.of_forall fun z => by simpa only [Real.norm_eq_abs] using hbound r z))

lemma periodic_stopped_pair_identity (T ta tb : ℝ) (hta : ta ≤ T)
    (β : ℝ) (ρ : ℝ → PeriodicTorus ι → ℝ) (f g : ℝ → PeriodicTorus ι → ℝ) :
    (2 / β) * (∫ r in Ioc 0 T, ∫ z,
      ⟪periodicStoppedGrad ta f r z, periodicStoppedGrad tb g r z⟫
        ∂periodicCappedDensityMeasure (ρ r)) =
    (2 / β) * (∫ r in Ioc 0 (min ta tb), ∫ z, ⟪periodicGrad (f r) z, periodicGrad (g r) z⟫
      ∂periodicCappedDensityMeasure (ρ r)) := by
  let U := min ta tb
  let A := fun r => ∫ z, ⟪periodicGrad (f r) z, periodicGrad (g r) z⟫ ∂periodicCappedDensityMeasure (ρ r)
  have heq : (fun r => ∫ z, ⟪periodicStoppedGrad ta f r z, periodicStoppedGrad tb g r z⟫
        ∂periodicCappedDensityMeasure (ρ r)) =ᵐ[volume.restrict (Ioc 0 T)] (Ioc 0 U).indicator A := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    by_cases hu : r ≤ U
    · have ha : r ∈ Icc 0 ta := ⟨hr.1.le, hu.trans (min_le_left _ _)⟩
      have hb : r ∈ Icc 0 tb := ⟨hr.1.le, hu.trans (min_le_right _ _)⟩
      simp [periodicStoppedGrad, ha, hb, Set.indicator, A, hr.1, hu, mem_Ioc]
    · have hcut : ∀ z, ⟪periodicStoppedGrad ta f r z, periodicStoppedGrad tb g r z⟫ = 0 := by
        intro z
        rw [periodicStoppedGrad_inner_eq_cut]
        simp [periodicCrossGradientCut, Set.piecewise, U, mem_Icc, hu]
      simp only [hcut, integral_zero]
      simp [Set.indicator, mem_Ioc, hu]
  have hsub : Ioc 0 U ⊆ Ioc 0 T := fun r hr => ⟨hr.1, hr.2.trans ((min_le_left _ _).trans hta)⟩
  rw [integral_congr_ae heq, setIntegral_indicator measurableSet_Ioc, inter_eq_right.mpr hsub]

theorem periodic_time_covariance_quadratic (T β : ℝ) (ρ : ℝ → PeriodicTorus ι → ℝ)
    (hρ : Measurable (Function.uncurry ρ))
    (hp : ∀ r ∈ Icc 0 T, IsProbabilityMeasure (periodicCappedDensityMeasure (ρ r)))
    (k : ℕ) (t θ : Fin k → ℝ) (ht : ∀ a, t a ≤ T) (f : Fin k → ℝ → PeriodicTorus ι → ℝ) (G : ℝ≥0)
    (hf : ∀ a, ContinuousOn (fun p : ℝ × E => gradient (periodicLiftFn (f a p.1)) p.2)
      (Icc 0 (t a) ×ˢ univ))
    (hb : ∀ a, ∀ r ∈ Icc 0 (t a), ∀ z, ‖periodicGrad (f a r) z‖ ≤ (G : ℝ)) :
    (∑ a, ∑ b, (θ a * θ b) * periodicDynamicTimeCovariance β ρ k t f a b) =
      (2 / β) * ∫ r in Ioc 0 T, ∫ z,
        ‖∑ a, θ a • periodicStoppedGrad (t a) (f a) r z‖ ^ 2 ∂periodicCappedDensityMeasure (ρ r) := by
  let Q := fun a b r => ∫ z, ⟪periodicStoppedGrad (t a) (f a) r z,
    periodicStoppedGrad (t b) (f b) r z⟫ ∂periodicCappedDensityMeasure (ρ r)
  have hi (a b : Fin k) := periodic_stopped_pair_proper T ρ hρ hp k t f G hf hb a b
  have hspace (r : ℝ) (hr : r ∈ Icc 0 T) :
      (∫ z, ‖∑ a, θ a • periodicStoppedGrad (t a) (f a) r z‖ ^ 2
        ∂periodicCappedDensityMeasure (ρ r)) = ∑ a, ∑ b, (θ a * θ b) * Q a b r := by
    simp_rw [periodicStoppedGradNormSq]
    rw [integral_finsetSum _ (fun a _ => integrable_finsetSum _ fun b _ => ((hi a b).1 r hr).const_mul _)]
    simp_rw [integral_finsetSum _ (fun b _ => ((hi _ b).1 r hr).const_mul _), integral_const_mul]
    rfl
  have heq : (fun r => ∫ z, ‖∑ a, θ a • periodicStoppedGrad (t a) (f a) r z‖ ^ 2
      ∂periodicCappedDensityMeasure (ρ r)) =ᵐ[volume.restrict (Ioc 0 T)]
      (fun r => ∑ a, ∑ b, (θ a * θ b) * Q a b r) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact hspace r ⟨hr.1.le, hr.2⟩
  rw [integral_congr_ae heq, integral_finsetSum _
    (fun a _ => integrable_finsetSum _ fun b _ => (hi a b).2.const_mul _)]
  simp_rw [integral_finsetSum _ (fun b _ => (hi _ b).2.const_mul _), integral_const_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro b _
  have hp := periodic_stopped_pair_identity T (t a) (t b) (ht a) β ρ (f a) (f b)
  change (θ a * θ b) * periodicDynamicTimeCovariance β ρ k t f a b =
    (2 / β) * ((θ a * θ b) * (∫ r in Ioc 0 T, Q a b r))
  calc
    _ = (θ a * θ b) * ((2 / β) * (∫ r in Ioc 0 T, Q a b r)) := by rw [hp]; rfl
    _ = _ := by ring

theorem periodic_time_covariance_posSemidef (T β : ℝ) (hβ : 0 ≤ β)
    (ρ : ℝ → PeriodicTorus ι → ℝ) (hρ : Measurable (Function.uncurry ρ))
    (hp : ∀ r ∈ Icc 0 T, IsProbabilityMeasure (periodicCappedDensityMeasure (ρ r)))
    (k : ℕ) (t : Fin k → ℝ) (ht : ∀ a, t a ≤ T) (f : Fin k → ℝ → PeriodicTorus ι → ℝ) (G : ℝ≥0)
    (hf : ∀ a, ContinuousOn (fun p : ℝ × E => gradient (periodicLiftFn (f a p.1)) p.2)
      (Icc 0 (t a) ×ˢ univ))
    (hb : ∀ a, ∀ r ∈ Icc 0 (t a), ∀ z, ‖periodicGrad (f a r) z‖ ≤ (G : ℝ)) :
    Matrix.PosSemidef (periodicDynamicTimeCovariance β ρ k t f) := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · change Matrix.conjTranspose (periodicDynamicTimeCovariance β ρ k t f) =
      periodicDynamicTimeCovariance β ρ k t f
    funext a b
    change periodicDynamicTimeCovariance β ρ k t f b a = periodicDynamicTimeCovariance β ρ k t f a b
    unfold periodicDynamicTimeCovariance
    rw [min_comm (t b) (t a)]
    apply congrArg (fun v : ℝ => (2 / β) * v)
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun r => integral_congr_ae
      (Filter.Eventually.of_forall fun z => real_inner_comm _ _)
  · intro θ
    have hh := periodic_time_covariance_quadratic T β ρ hρ hp k t θ ht f G hf hb
    have hn : 0 ≤ ∑ a, ∑ b, (θ a * θ b) * periodicDynamicTimeCovariance β ρ k t f a b := by
      rw [hh]
      exact mul_nonneg (div_nonneg (by norm_num) hβ)
        (integral_nonneg fun r => integral_nonneg fun z => sq_nonneg _)
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial, Finset.mul_sum]
    convert hn using 1
    apply Finset.sum_congr rfl; intro a _
    apply Finset.sum_congr rfl; intro b _
    ring

/-- Horizon-only form of the quadratic identity and positivity (interval covariance). -/
theorem periodic_interval_covariance (T β : ℝ) (hT : 0 ≤ T) (hβ : 0 ≤ β)
    (ρ : ℝ → PeriodicTorus ι → ℝ)
    (hρ : Measurable (fun p : Icc (0 : ℝ) T × PeriodicTorus ι => ρ p.1 p.2))
    (hp : ∀ r ∈ Icc 0 T, IsProbabilityMeasure (periodicCappedDensityMeasure (ρ r)))
    (k : ℕ) (t : Fin k → ℝ) (ht : ∀ a, t a ≤ T) (f : Fin k → ℝ → PeriodicTorus ι → ℝ) (G : ℝ≥0)
    (hf : ∀ a, ContinuousOn (fun p : ℝ × E => gradient (periodicLiftFn (f a p.1)) p.2)
      (Icc 0 (t a) ×ˢ univ))
    (hb : ∀ a, ∀ r ∈ Icc 0 (t a), ∀ z, ‖periodicGrad (f a r) z‖ ≤ (G : ℝ)) :
    Matrix.PosSemidef (periodicDynamicTimeCovariance β ρ k t f) ∧
    ∀ θ : Fin k → ℝ,
      (∑ a, ∑ b, (θ a * θ b) * periodicDynamicTimeCovariance β ρ k t f a b) =
      (2 / β) * ∫ r in Ioc 0 T, ∫ z,
        ‖∑ a, θ a • periodicStoppedGrad (t a) (f a) r z‖ ^ 2
          ∂periodicCappedDensityMeasure (ρ r) := by
  let ρe := fun r => ρ (projIcc 0 T hT r)
  have hρe : Measurable (Function.uncurry ρe) :=
    hρ.comp (((continuous_projIcc : Continuous (projIcc 0 T hT)).measurable.comp
      measurable_fst).prodMk measurable_snd)
  have heq (r : ℝ) (hr : r ∈ Icc 0 T) : ρe r = ρ r := by
    dsimp only [ρe]; rw [projIcc_of_mem hT hr]
  have hpe : ∀ r ∈ Icc 0 T, IsProbabilityMeasure (periodicCappedDensityMeasure (ρe r)) := by
    intro r hr; rw [heq r hr]; exact hp r hr
  have hcov : periodicDynamicTimeCovariance β ρe k t f = periodicDynamicTimeCovariance β ρ k t f := by
    funext a b
    unfold periodicDynamicTimeCovariance
    apply congrArg (fun v : ℝ => (2 / β) * v)
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    rw [heq r ⟨hr.1.le, hr.2.trans ((min_le_left _ _).trans (ht a))⟩]
  refine ⟨hcov ▸ periodic_time_covariance_posSemidef T β hβ ρe hρe hpe k t ht f G hf hb, ?_⟩
  intro θ
  have hh := periodic_time_covariance_quadratic T β ρe hρe hpe k t θ ht f G hf hb
  rw [hcov] at hh
  refine hh.trans ?_
  apply congrArg (fun v : ℝ => (2 / β) * v)
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
  rw [heq r ⟨hr.1.le, hr.2⟩]

end DGRHS.Periodic
