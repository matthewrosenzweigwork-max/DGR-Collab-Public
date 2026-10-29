import SharpSymmetricLSI.Paper.GroundT9
import SharpSymmetricLSI.Paper.GaussLaw11

/-!
# R30 groundwork: weighted limits of joint laws

If `(A_k, U_k)` converge jointly in law (tested against bounded continuous functions), `w ≥ 0` is
continuous with `∫ w(U_k)^q ≤ B` (`q > 1`) and `w(U_∞)` integrable, then
`∫ w(U_k) Φ(A_k, U_k) → ∫ w(U_∞) Φ(A_∞, U_∞)` for every bounded continuous `Φ`
(truncation `min(w, M)` and `w - min(w, M) ≤ M^{1-q} w^q`).
-/

open MeasureTheory InformationTheory Set Filter Topology Real
open scoped ENNReal NNReal BoundedContinuousFunction

namespace SharpLSI

/-- `(a, u) ↦ min(w(u), M) Φ(a, u)`. -/
noncomputable def truncW {E : Type*} [TopologicalSpace E] {w : ℝ → ℝ} (hw : Continuous w)
    (hw0 : ∀ u, 0 ≤ w u) (Φ : E × ℝ →ᵇ ℝ) (M : ℝ) : E × ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound ⟨fun t => min (w t.2) M * Φ t,
    ((hw.comp continuous_snd).min continuous_const).mul Φ.continuous⟩ (2 * (|M| * ‖Φ‖))
    fun a b => by
      simp only [ContinuousMap.coe_mk, Real.dist_eq]
      have hb : ∀ t : E × ℝ, |min (w t.2) M * Φ t| ≤ |M| * ‖Φ‖ := fun t => by
        rw [abs_mul]
        refine mul_le_mul ?_ ?_ (abs_nonneg _) (abs_nonneg _)
        · rcases le_or_gt 0 M with h | h
          · rw [abs_of_nonneg (le_min (hw0 _) h), abs_of_nonneg h]; exact min_le_right _ _
          · rw [min_eq_right (h.le.trans (hw0 _))]
        · rw [← Real.norm_eq_abs]; exact Φ.norm_coe_le_norm t
      have := hb a; have := hb b
      have := abs_sub (min (w a.2) M * Φ a) (min (w b.2) M * Φ b)
      linarith

theorem truncW_apply {E : Type*} [TopologicalSpace E] {w : ℝ → ℝ} (hw : Continuous w)
    (hw0 : ∀ u, 0 ≤ w u) (Φ : E × ℝ →ᵇ ℝ) (M : ℝ) (t : E × ℝ) :
    truncW hw hw0 Φ M t = min (w t.2) M * Φ t := rfl

theorem tendsto_weighted_gen {E : Type*} [TopologicalSpace E] {Ω : ℕ → Type*}
    [∀ k, MeasurableSpace (Ω k)] {P : ∀ k, Measure (Ω k)} [∀ k, IsProbabilityMeasure (P k)]
    {A : ∀ k, Ω k → E} {U : ∀ k, Ω k → ℝ} {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'}
    [IsProbabilityMeasure P'] {A' : Ω' → E} {U' : Ω' → ℝ}
    (hconv : ∀ G : E × ℝ →ᵇ ℝ,
      Tendsto (fun k => ∫ x, G (A k x, U k x) ∂P k) atTop (𝓝 (∫ x, G (A' x, U' x) ∂P')))
    {w : ℝ → ℝ} (hw : Continuous w) (hw0 : ∀ u, 0 ≤ w u) {q B : ℝ} (hq : 1 < q)
    (hm : ∀ k, AEStronglyMeasurable (fun x => (A k x, U k x)) (P k))
    (hm' : AEStronglyMeasurable (fun x => (A' x, U' x)) P')
    (hwi : ∀ k, Integrable (fun x => w (U k x)) (P k))
    (hwq : ∀ k, Integrable (fun x => w (U k x) ^ q) (P k))
    (hB : ∀ k, ∫ x, w (U k x) ^ q ∂P k ≤ B)
    (hwi' : Integrable (fun x => w (U' x)) P') (Φ : E × ℝ →ᵇ ℝ) :
    Tendsto (fun k => ∫ x, w (U k x) * Φ (A k x, U k x) ∂P k) atTop
      (𝓝 (∫ x, w (U' x) * Φ (A' x, U' x) ∂P')) := by
  refine tendsto_of_trunc (b := fun M k => ∫ x, truncW hw hw0 Φ M (A k x, U k x) ∂P k)
    (b0 := fun M => ∫ x, truncW hw hw0 Φ M (A' x, U' x) ∂P') (fun M => hconv _) fun ε hε => ?_
  have hΦm' : AEStronglyMeasurable (fun x => Φ (A' x, U' x)) P' :=
    Φ.continuous.comp_aestronglyMeasurable hm'
  have hUm' : AEStronglyMeasurable (fun x => w (U' x)) P' := hwi'.1
  have h0 : Tendsto (fun M : ℝ => ∫ x, truncW hw hw0 Φ M (A' x, U' x) ∂P') atTop
      (𝓝 (∫ x, w (U' x) * Φ (A' x, U' x) ∂P')) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun x => w (U' x) * ‖Φ‖)
      (Eventually.of_forall fun M => ?_) ?_ (hwi'.mul_const _) (Eventually.of_forall fun x => ?_)
    · simp only [truncW_apply]
      exact (hUm'.inf aestronglyMeasurable_const).mul hΦm'
    · filter_upwards [eventually_ge_atTop 0] with M hM
      refine Eventually.of_forall fun x => ?_
      rw [truncW_apply, norm_mul]
      refine mul_le_mul ?_ (Φ.norm_coe_le_norm _) (norm_nonneg _) (hw0 _)
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min (hw0 _) hM)]
      exact min_le_left _ _
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop (w (U' x))] with M hM
      rw [truncW_apply, min_eq_left hM]
  have hev1 : ∀ᶠ M in atTop, |∫ x, w (U' x) * Φ (A' x, U' x) ∂P' -
      ∫ x, truncW hw hw0 Φ M (A' x, U' x) ∂P'| ≤ ε := by
    filter_upwards [Metric.tendsto_nhds.1 h0 ε hε] with M hM
    rw [Real.dist_eq, abs_sub_comm] at hM; exact hM.le
  set B' := max B 0
  have h1 : Tendsto (fun M : ℝ => ‖Φ‖ * (M ^ (1 - q) * B')) atTop (𝓝 (‖Φ‖ * (0 * B'))) := by
    have := tendsto_rpow_neg_atTop (y := q - 1) (by linarith)
    rw [show -(q - 1) = 1 - q by ring] at this
    exact (this.mul_const B').const_mul ‖Φ‖
  rw [zero_mul, mul_zero] at h1
  obtain ⟨M, ⟨hM1, hM2⟩, hM0⟩ := ((hev1.and (h1.eventually (ge_mem_nhds hε))).and
    (eventually_gt_atTop 0)).exists
  refine ⟨M, fun k => ?_, hM1⟩
  have h2 := abs_integral_sub_min_le (P := P k) (h := fun x => Φ (A k x, U k x))
    (w := fun x => w (U k x)) (fun x => hw0 _) (hwi k) hq.le (hwq k) hM0 (c := ‖Φ‖)
    (fun x => by rw [← Real.norm_eq_abs]; exact Φ.norm_coe_le_norm _)
    (Φ.continuous.comp_aestronglyMeasurable (hm k))
  have e1 : ∫ x, w (U k x) * Φ (A k x, U k x) ∂P k = ∫ x, Φ (A k x, U k x) * w (U k x) ∂P k := by
    simp_rw [mul_comm]
  have e2 : ∫ x, truncW hw hw0 Φ M (A k x, U k x) ∂P k =
      ∫ x, Φ (A k x, U k x) * min (w (U k x)) M ∂P k := by
    simp_rw [truncW_apply, mul_comm]
  rw [e1, e2]
  refine h2.trans ?_
  calc ‖Φ‖ * M ^ (1 - q) * ∫ x, w (U k x) ^ q ∂P k ≤ ‖Φ‖ * (M ^ (1 - q) * B') := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          ((hB k).trans (le_max_left _ _)) (Real.rpow_nonneg hM0.le _)) (norm_nonneg _)
    _ ≤ ε := hM2

end SharpLSI
