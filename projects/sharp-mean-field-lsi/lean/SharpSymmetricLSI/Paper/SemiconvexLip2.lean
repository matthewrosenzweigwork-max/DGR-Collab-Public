import SharpSymmetricLSI.Paper.SemiconvexLip

/-!
# Semiconvex periodic functions: Lipschitz bound and weak gradient (Phase 3, lane D)
-/

open MeasureTheory Set Filter Topology
open scoped ContDiff ENNReal NNReal

namespace SharpLSI

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem lipschitz_mollL {u : UnitAddTorus ι → ℝ} (hu : Continuous u) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : CoordSemiconvex u K) (n : ℕ) :
    LipschitzWith (Real.toNNReal (K * Fintype.card ι / 2)) (mollL n (u ∘ liftT)) := by
  have hF : LocallyIntegrable (u ∘ liftT) volume := (hu.comp continuous_liftT).locallyIntegrable
  have hd : Differentiable ℝ (mollL n (u ∘ liftT)) :=
    (contDiff_mollL n hF).differentiable (by simp)
  refine lipschitzWith_of_nnnorm_fderiv_le hd fun x => ?_
  rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ (by positivity)]
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  have hv : v = ∑ k, v k • (Pi.single k 1 : ι → ℝ) := by
    conv_lhs => rw [← Finset.univ_sum_single v]
    refine Finset.sum_congr rfl fun k _ => ?_
    funext j; by_cases h : j = k
    · subst h; simp
    · simp [h]
  rw [hv, map_sum]
  simp_rw [map_smul, smul_eq_mul]
  rw [Real.norm_eq_abs]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ k, |v k * fderiv ℝ (mollL n (u ∘ liftT)) x (Pi.single k 1)|
      ≤ ∑ _k : ι, ‖∑ k, v k • (Pi.single k 1 : ι → ℝ)‖ * (K / 2) := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [abs_mul]
        refine mul_le_mul ?_ (abs_fderiv_mollL_le hu hK n k x) (abs_nonneg _) (by positivity)
        rw [← hv]; exact norm_le_pi_norm v k
    _ = K * Fintype.card ι / 2 * ‖∑ k, v k • (Pi.single k 1 : ι → ℝ)‖ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

theorem tendsto_mollL_apply {u : UnitAddTorus ι → ℝ} (hu : Continuous u) (x : ι → ℝ) :
    Tendsto (fun n => mollL n (u ∘ liftT) x) atTop (𝓝 (u (liftT x))) := by
  rw [Metric.tendsto_atTop]
  intro δ hδ
  obtain ⟨N, hN⟩ := eventually_atTop.mp (moll_uniform_of_continuous hu (half_pos hδ))
  refine ⟨N, fun n hn => ?_⟩
  have := hN n hn (liftT x)
  rw [← Function.comp_apply (f := moll n u), moll_comp_liftT] at this
  linarith

/-- **Semiconvex periodic functions are Lipschitz**. -/
theorem lipschitz_of_coordSemiconvex {u : UnitAddTorus ι → ℝ} (hu : Continuous u) {K : ℝ}
    (hK0 : 0 ≤ K) (hK : CoordSemiconvex u K) :
    LipschitzWith (Real.toNNReal (K * Fintype.card ι / 2)) (u ∘ liftT) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  have h := fun n => (lipschitz_mollL hu hK0 hK n).dist_le_mul x y
  exact le_of_tendsto' (((tendsto_mollL_apply hu x).dist (tendsto_mollL_apply hu y))) h

/-- The weak gradient of a Lipschitz periodic function. -/
noncomputable def lipGrad (u : UnitAddTorus ι → ℝ) (y : UnitAddTorus ι) (k : ι) : ℝ :=
  lineDeriv ℝ (u ∘ liftT) (secT y) (Pi.single k 1)

theorem lineDeriv_comp_liftT_periodic (u : UnitAddTorus ι → ℝ) (x : ι → ℝ) (m : ι → ℤ)
    (v : ι → ℝ) :
    lineDeriv ℝ (u ∘ liftT) (x + intVec m) v = lineDeriv ℝ (u ∘ liftT) x v := by
  unfold lineDeriv
  congr 1
  funext t
  simp only [Function.comp]
  rw [show x + intVec m + t • v = (x + t • v) + intVec m by abel, liftT_add_intVec]

theorem lipGrad_liftT (u : UnitAddTorus ι → ℝ) (x : ι → ℝ) (k : ι) :
    lipGrad u (liftT x) k = lineDeriv ℝ (u ∘ liftT) x (Pi.single k 1) := by
  obtain ⟨m, hm⟩ := secT_liftT_eq x
  rw [lipGrad, hm, lineDeriv_comp_liftT_periodic]

theorem abs_lipGrad_le {u : UnitAddTorus ι → ℝ} {C : ℝ≥0} (hL : LipschitzWith C (u ∘ liftT))
    (y : UnitAddTorus ι) (k : ι) : |lipGrad u y k| ≤ C := by
  have := norm_lineDeriv_le_of_lipschitz ℝ (x₀ := secT y) (v := (Pi.single k 1 : ι → ℝ)) hL
  rw [Real.norm_eq_abs] at this
  refine this.trans ?_
  have : ‖(Pi.single k 1 : ι → ℝ)‖ ≤ 1 := by
    refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun j => ?_
    by_cases h : j = k
    · subst h; simp
    · simp [h]
  calc (C : ℝ) * ‖(Pi.single k 1 : ι → ℝ)‖ ≤ C * 1 := by gcongr
    _ = C := mul_one _

theorem measurable_lipGrad {u : UnitAddTorus ι → ℝ} (hu : Continuous u) (k : ι) :
    Measurable fun y => lipGrad u y k :=
  (measurable_lineDeriv (𝕜 := ℝ) (v := (Pi.single k 1 : ι → ℝ))
    (hu.comp continuous_liftT)).comp measurable_secT

theorem locallyIntegrable_of_bdd {g : (ι → ℝ) → ℝ} (hg : Measurable g) {C : ℝ}
    (hC : ∀ x, |g x| ≤ C) : LocallyIntegrable g volume :=
  (locallyIntegrable_iff).mpr fun K hK => IntegrableOn.of_bound hK.measure_lt_top
    hg.aestronglyMeasurable C (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hC x)

/-- **Lipschitz periodic functions have a bounded weak gradient** (Rademacher). -/
theorem isWeakGrad_lipGrad {u : UnitAddTorus ι → ℝ} (hu : Continuous u) {C : ℝ≥0}
    (hL : LipschitzWith C (u ∘ liftT)) : IsWeakGrad u (lipGrad u) := by
  refine ⟨(hu.comp continuous_liftT).locallyIntegrable, fun k => ?_, fun φ hφ hφc k => ?_⟩
  · exact locallyIntegrable_of_bdd ((measurable_lipGrad hu k).comp measurable_liftT)
      fun x => abs_lipGrad_le hL _ k
  · obtain ⟨D, hD⟩ := hφ.lipschitzWith_of_hasCompactSupport hφc (by simp) |>.imp fun D h => h
    have h := hL.integral_lineDeriv_mul_eq (μ := volume) hD hφc (Pi.single k 1)
    have hφd : ∀ x, lineDeriv ℝ φ x (-(Pi.single k 1 : ι → ℝ)) = -fderiv ℝ φ x (Pi.single k 1) :=
      fun x => by
        rw [((hφ.differentiable (by simp)) x).lineDeriv_eq_fderiv, map_neg]
    simp_rw [hφd, lipGrad_liftT] at h ⊢
    rw [show (fun x => u (liftT x) * fderiv ℝ φ x (Pi.single k 1)) =
      fun x => -(-fderiv ℝ φ x (Pi.single k 1) * (u ∘ liftT) x) by funext x; simp; ring,
      integral_neg, ← h]

end SharpLSI
