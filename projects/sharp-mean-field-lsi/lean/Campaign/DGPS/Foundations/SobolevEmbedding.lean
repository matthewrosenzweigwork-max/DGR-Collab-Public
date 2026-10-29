import DGPS.Foundations.WeakContractions
import DGPS.Foundations.SobolevFourier
import Mathlib.Analysis.FunctionalSpaces.SobolevInequality

/-!
# Periodic Sobolev embeddings and entropy integrability (FOU006)

On the unit torus `𝕋^d`:
* `d > 2`: `H¹ ↪ L^{2d/(d-2)}`; `d = 2`: `H¹ ↪ L^q` for every finite `q` (periodic chart cutoffs
  and the Euclidean Gagliardo-Nirenberg-Sobolev inequality, then Fatou along smooth approximants);
* `d = 1`: a continuous representative that is Hölder-1/2 for `torusDist` with constant `‖g‖₂`
  and bounded by `‖u‖₂ + ‖g‖₂`;
* `u ∈ H¹` implies `u² log u²` integrable;
* in `d = 1`, `H¹` is an algebra, and the weak chain rule holds for `F` smooth on a compact interval
  containing the range; positive continuous `H¹` functions bounded away from zero have `H¹`
  reciprocals.
-/

open MeasureTheory Set Filter Topology Module
open scoped ENNReal ContDiff NNReal

namespace DGPS

variable {d : ℕ}

/-- The cutoff on `ℝ^d` equal to `1` on `[0,1]^d` supported in `(-3/2, 5/2)^d`. -/
noncomputable def sobBump (d : ℕ) : ContDiffBump (fun _ : Fin d => (1 / 2 : ℝ)) where
  rIn := 1
  rOut := 2
  rIn_pos := one_pos
  rIn_lt_rOut := one_lt_two

theorem sobBump_eq_one {x : Fin d → ℝ} (hx : x ∈ SharpLSI.unitBox (Fin d)) : sobBump d x = 1 := by
  apply ContDiffBump.one_of_mem_closedBall
  rw [Metric.mem_closedBall, show (sobBump d).rIn = 1 from rfl]
  refine (dist_pi_le_iff zero_le_one).mpr fun i => ?_
  have := hx i (mem_univ i)
  rw [Real.dist_eq, abs_le]; constructor <;> linarith [this.1, this.2]

theorem sobBump_tsupport {x : Fin d → ℝ} (hx : x ∈ tsupport (sobBump d)) :
    x ∈ SharpLSI.cube (Fin d) 3 := by
  rw [ContDiffBump.tsupport_eq, Metric.mem_closedBall, show (sobBump d).rOut = 2 from rfl] at hx
  intro i _
  have := (dist_le_pi_dist x (fun _ => (1 / 2 : ℝ)) i).trans hx
  rw [Real.dist_eq, abs_le] at this
  change x i ∈ Icc (-(3 : ℝ)) 3
  constructor <;> linarith [this.1, this.2]

theorem opNorm_le_sum_single' (L : (Fin d → ℝ) →L[ℝ] ℝ) :
    ‖L‖ ≤ ∑ k, |L (Pi.single k 1)| := by
  refine ContinuousLinearMap.opNorm_le_bound _ (Finset.sum_nonneg fun k _ => abs_nonneg _)
    fun v => ?_
  have hv : v = ∑ k, v k • Pi.single k (1 : ℝ) := by
    funext i; simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hv]
  rw [map_sum, Real.norm_eq_abs, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [map_smul, smul_eq_mul, abs_mul, mul_comm]
  exact mul_le_mul_of_nonneg_left ((Real.norm_eq_abs (v k)).symm ▸ norm_le_pi_norm v k)
    (abs_nonneg _)

theorem exists_bound_fderiv_sobBump : ∃ A : ℝ, 0 ≤ A ∧ ∀ z, ‖fderiv ℝ (sobBump d) z‖ ≤ A := by
  obtain ⟨A, hA⟩ := (((sobBump d).contDiff (n := 1)).continuous_fderiv
    one_ne_zero).bounded_above_of_compact_support ((sobBump d).hasCompactSupport.fderiv (𝕜 := ℝ))
  exact ⟨A, (norm_nonneg _).trans (hA 0), hA⟩

/-- Pointwise bound on the derivative of `χ Φ`. -/
theorem norm_fderiv_bump_mul_le {Φ : (Fin d → ℝ) → ℝ} (hΦ : ContDiff ℝ 1 Φ) {A : ℝ}
    (hA : ∀ z, ‖fderiv ℝ (sobBump d) z‖ ≤ A) (z : Fin d → ℝ) :
    ‖fderiv ℝ (fun x => sobBump d x * Φ x) z‖ ≤
      (SharpLSI.cube (Fin d) 3).indicator (fun x => ‖fderiv ℝ Φ x‖ + A * |Φ x|) z := by
  have hA0 : 0 ≤ A := le_trans (norm_nonneg _) (hA 0)
  by_cases hz : z ∈ tsupport (sobBump d)
  · rw [indicator_of_mem (sobBump_tsupport hz)]
    have hχ := ((sobBump d).contDiff (n := 1)).differentiable one_ne_zero z
    have hΦd := (hΦ.differentiable one_ne_zero) z
    have h3 := hχ.hasFDerivAt.mul hΦd.hasFDerivAt
    rw [show (fun x => sobBump d x * Φ x) = (⇑(sobBump d) * Φ) from rfl, h3.fderiv]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul (sobBump d z), norm_smul (Φ z)]
    have hχ0 : 0 ≤ sobBump d z := (sobBump d).nonneg
    have hχ1 : sobBump d z ≤ 1 := (sobBump d).le_one
    rw [Real.norm_eq_abs, abs_of_nonneg hχ0, Real.norm_eq_abs]
    have e1 : sobBump d z * ‖fderiv ℝ Φ z‖ ≤ ‖fderiv ℝ Φ z‖ :=
      mul_le_of_le_one_left (norm_nonneg _) hχ1
    have e2 : |Φ z| * ‖fderiv ℝ (sobBump d) z‖ ≤ A * |Φ z| := by
      rw [mul_comm]; exact mul_le_mul_of_nonneg_right (hA z) (abs_nonneg _)
    linarith
  · have hz' : (fun x => sobBump d x * Φ x) =ᶠ[𝓝 z] fun _ => 0 := by
      have : ∀ᶠ w in 𝓝 z, w ∉ tsupport (sobBump d) :=
        (isClosed_tsupport _).isOpen_compl.eventually_mem hz
      filter_upwards [this] with w hw
      rw [image_eq_zero_of_notMem_tsupport hw, zero_mul]
    rw [hz'.fderiv_eq, fderiv_const_apply, norm_zero]
    by_cases hm : z ∈ SharpLSI.cube (Fin d) 3
    · rw [indicator_of_mem hm]; positivity
    · rw [indicator_of_notMem hm]


theorem eLpNorm_torus_le_bump {φ : Torus d → ℝ} (hφ : Continuous φ) (q : ℝ≥0∞) :
    eLpNorm φ q (haar d) ≤ eLpNorm (fun x => sobBump d x * φ (torusLift x)) q volume := by
  have hbox : MeasurableSet (SharpLSI.unitBox (Fin d)) :=
    MeasurableSet.univ_pi fun _ => measurableSet_Ioc
  rw [haar_eq_map_unitBox, eLpNorm_map_measure hφ.aestronglyMeasurable
    SharpLSI.measurable_liftT.aemeasurable]
  calc eLpNorm (φ ∘ torusLift) q (volume.restrict (SharpLSI.unitBox (Fin d)))
      = eLpNorm (fun x => sobBump d x * φ (torusLift x)) q
          (volume.restrict (SharpLSI.unitBox (Fin d))) := by
        refine eLpNorm_congr_ae ?_
        filter_upwards [ae_restrict_mem hbox] with x hx
        simp [sobBump_eq_one hx]
    _ ≤ _ := eLpNorm_mono_measure _ Measure.restrict_le_self

theorem eLpNorm_cube_comp_le {H : Torus d → ℝ} (hH : Measurable H) {p : ℝ≥0∞} (hp0 : p ≠ 0)
    (hpt : p ≠ (⊤ : ℝ≥0∞)) :
    eLpNorm (fun x => H (torusLift x)) p (volume.restrict (SharpLSI.cube (Fin d) 3)) ≤
      ((8 : ℝ≥0∞) ^ d) ^ (1 / p.toReal) * eLpNorm H p (haar d) := by
  have hr : 0 < p.toReal := ENNReal.toReal_pos hp0 hpt
  have hHl : AEStronglyMeasurable (fun x : Fin d → ℝ => H (torusLift x))
      (volume.restrict (SharpLSI.cube (Fin d) 3)) :=
    (hH.comp SharpLSI.measurable_liftT).aestronglyMeasurable
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt hHl,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt hH.aestronglyMeasurable]
  have h := SharpLSI.lintegral_cube_le (ι := Fin d) 3
    (H := fun y => ‖H y‖ₑ ^ p.toReal)
    ((hH.enorm.pow_const _).aemeasurable)
  have h8 : (((2 * 3 + 2 : ℕ) : ℝ≥0∞)) ^ Fintype.card (Fin d) = (8 : ℝ≥0∞) ^ d := by
    simp only [Fintype.card_fin]; norm_num
  rw [h8] at h
  rw [← ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]
  exact ENNReal.rpow_le_rpow h (by positivity)


theorem coordPartial_torusLift (j : Fin d) (φ : Torus d → ℝ) (x : Fin d → ℝ) :
    coordPartial j φ (torusLift x) = fderiv ℝ (φ ∘ torusLift) x (Pi.single j 1) := by
  simp only [coordPartial]
  rw [SharpLSI.fderiv_lift_secT]

theorem eLpNorm_fderiv_bump_le {φ : Torus d → ℝ} (hφ : IsSmoothPeriodic φ) {A : ℝ}
    (hA : ∀ z, ‖fderiv ℝ (sobBump d) z‖ ≤ A) {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ (⊤ : ℝ≥0∞)) :
    eLpNorm (fderiv ℝ (fun x => sobBump d x * φ (torusLift x))) p volume ≤
      ((8 : ℝ≥0∞) ^ d) ^ (1 / p.toReal) *
        (ENNReal.ofReal A * eLpNorm φ p (haar d) +
          ∑ j, eLpNorm (coordPartial j φ) p (haar d)) := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  have hA0 : 0 ≤ A := le_trans (norm_nonneg _) (hA 0)
  have hΦ : ContDiff ℝ 1 (φ ∘ torusLift) := hφ.of_le (by exact_mod_cast le_top)
  set Ht : Torus d → ℝ := fun y => ∑ j, ‖coordPartial j φ y‖ + A * ‖φ y‖ with hHt
  have hHtm : Measurable Ht := by
    refine (Finset.measurable_sum _ fun j _ => ?_).add (measurable_const.mul ?_)
    · exact (hφ.continuous_coordPartial j).norm.measurable
    · exact hφ.continuous_torus.norm.measurable
  have hcube : MeasurableSet (SharpLSI.cube (Fin d) 3) :=
    MeasurableSet.univ_pi fun _ => measurableSet_Icc
  have hpt1 : ∀ x, ‖fderiv ℝ (fun x => sobBump d x * φ (torusLift x)) x‖ ≤
      (SharpLSI.cube (Fin d) 3).indicator (fun x => Ht (torusLift x)) x := by
    intro x
    refine (norm_fderiv_bump_mul_le (Φ := φ ∘ torusLift) hΦ hA x).trans ?_
    by_cases hx : x ∈ SharpLSI.cube (Fin d) 3
    · rw [indicator_of_mem hx, indicator_of_mem hx]
      have h1 := opNorm_le_sum_single' (fderiv ℝ (φ ∘ torusLift) x)
      simp only [hHt, coordPartial_torusLift, Real.norm_eq_abs, Function.comp_apply]
      linarith
    · rw [indicator_of_notMem hx, indicator_of_notMem hx]
  have hfd : AEStronglyMeasurable (fderiv ℝ (fun x => sobBump d x * φ (torusLift x))) volume :=
    (((sobBump d).contDiff (n := 1)).mul hΦ).continuous_fderiv one_ne_zero |>.aestronglyMeasurable
  calc eLpNorm (fderiv ℝ (fun x => sobBump d x * φ (torusLift x))) p volume
      ≤ eLpNorm ((SharpLSI.cube (Fin d) 3).indicator (fun x => Ht (torusLift x))) p volume :=
        eLpNorm_mono_real hfd hpt1
    _ = eLpNorm (fun x => Ht (torusLift x)) p
          (volume.restrict (SharpLSI.cube (Fin d) 3)) :=
        eLpNorm_indicator_eq_eLpNorm_restrict hcube.nullMeasurableSet
    _ ≤ ((8 : ℝ≥0∞) ^ d) ^ (1 / p.toReal) * eLpNorm Ht p (haar d) :=
        eLpNorm_cube_comp_le hHtm hp0 hpt
    _ ≤ _ := by
        have hsum : Ht = (∑ j, fun y => ‖coordPartial j φ y‖) + fun y => A * ‖φ y‖ := by
          funext y; simp [hHt, Finset.sum_apply]
        have e1 : (fun y => A * ‖φ y‖) = A • fun y => ‖φ y‖ := by funext y; simp
        have b1 : eLpNorm (∑ j, fun y => ‖coordPartial j φ y‖) p (haar d) ≤
            ∑ j, eLpNorm (coordPartial j φ) p (haar d) := by
          refine (eLpNorm_sum_le hp).trans ?_
          refine Finset.sum_le_sum fun j _ => ?_
          rw [eLpNorm_norm _ (hφ.continuous_coordPartial j).aestronglyMeasurable]
        have b2 : eLpNorm (fun y => A * ‖φ y‖) p (haar d) ≤
            ENNReal.ofReal A * eLpNorm φ p (haar d) := by
          rw [e1, eLpNorm_const_smul, eLpNorm_norm _ hφ.continuous_torus.aestronglyMeasurable,
            Real.enorm_eq_ofReal hA0]
        rw [hsum]
        refine mul_le_mul' le_rfl ((eLpNorm_add_le hp).trans ?_)
        rw [add_comm]
        exact add_le_add b2 b1


theorem smooth_sobolev (p q : ℝ≥0) (hp : 1 ≤ p) (hpd : (p : ℝ) < d)
    (hpq : (p : ℝ)⁻¹ - (d : ℝ)⁻¹ ≤ (q : ℝ)⁻¹) :
    ∃ C : ℝ≥0, ∀ φ : Torus d → ℝ, IsSmoothPeriodic φ →
      eLpNorm φ q (haar d) ≤
        C * (eLpNorm φ p (haar d) + ∑ j, eLpNorm (coordPartial j φ) p (haar d)) := by
  obtain ⟨A, hA0, hA⟩ := exists_bound_fderiv_sobBump (d := d)
  have hbd : Bornology.IsBounded (SharpLSI.cube (Fin d) 3) := by
    unfold SharpLSI.cube
    exact (isCompact_univ_pi fun _ => isCompact_Icc).isBounded
  set K : ℝ≥0 := eLpNormLESNormFDerivOfLeConst ℝ (volume : Measure (Fin d → ℝ))
    (SharpLSI.cube (Fin d) 3) p q with hK
  refine ⟨K * ((8 : ℝ≥0) ^ d) ^ (1 / (p : ℝ)) * (A.toNNReal + 1), fun φ hφ => ?_⟩
  have hp1 : (1 : ℝ≥0∞) ≤ (p : ℝ≥0∞) := by exact_mod_cast hp
  have hpt : (p : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  have hΦ : ContDiff ℝ 1 (φ ∘ torusLift) := hφ.of_le (by exact_mod_cast le_top)
  have hcd : ContDiff ℝ 1 (fun x => sobBump d x * φ (torusLift x)) :=
    ((sobBump d).contDiff (n := 1)).mul hΦ
  have hsupp : (fun x => sobBump d x * φ (torusLift x)).support ⊆ SharpLSI.cube (Fin d) 3 := by
    intro x hx
    refine sobBump_tsupport (subset_tsupport _ ?_)
    intro h0
    exact hx (by simp [h0])
  have hfr : (Module.finrank ℝ (Fin d → ℝ) : ℝ) = d := by simp
  have h2p : p < Module.finrank ℝ (Fin d → ℝ) := by
    have : (p : ℝ) < (Module.finrank ℝ (Fin d → ℝ) : ℝ) := by rw [hfr]; exact hpd
    exact_mod_cast this
  have hpq' : (p : ℝ)⁻¹ - (Module.finrank ℝ (Fin d → ℝ) : ℝ)⁻¹ ≤ (q : ℝ)⁻¹ := by
    rw [hfr]; exact hpq
  have hG := eLpNorm_le_eLpNorm_fderiv_of_le (volume : Measure (Fin d → ℝ)) hcd hsupp hp h2p hpq' hbd
  have hB := eLpNorm_fderiv_bump_le hφ hA hp1 hpt
  have hT := eLpNorm_torus_le_bump (d := d) hφ.continuous_torus (q : ℝ≥0∞)
  set E1 := eLpNorm φ (p : ℝ≥0∞) (haar d)
  set E2 := ∑ j, eLpNorm (coordPartial j φ) (p : ℝ≥0∞) (haar d)
  have hc : ((8 : ℝ≥0∞) ^ d) ^ (1 / ((p : ℝ≥0∞)).toReal) = (((8 : ℝ≥0) ^ d) ^ (1 / (p : ℝ)) : ℝ≥0) := by
    rw [ENNReal.coe_toReal, ENNReal.coe_rpow_of_nonneg _ (by positivity)]
    simp
  rw [hc] at hB
  have hA' : ENNReal.ofReal A ≤ ((A.toNNReal + 1 : ℝ≥0) : ℝ≥0∞) := by
    rw [ENNReal.ofReal]
    push_cast
    exact le_self_add
  calc eLpNorm φ q (haar d) ≤ K * eLpNorm (fderiv ℝ (fun x => sobBump d x * φ (torusLift x)))
        (p : ℝ≥0∞) volume := hT.trans hG
    _ ≤ K * ((((8 : ℝ≥0) ^ d) ^ (1 / (p : ℝ)) : ℝ≥0) *
          (ENNReal.ofReal A * E1 + E2)) := by gcongr
    _ ≤ K * ((((8 : ℝ≥0) ^ d) ^ (1 / (p : ℝ)) : ℝ≥0) *
          (((A.toNNReal + 1 : ℝ≥0) : ℝ≥0∞) * (E1 + E2))) := by
        gcongr
        have h1 : (1 : ℝ≥0∞) ≤ ((A.toNNReal + 1 : ℝ≥0) : ℝ≥0∞) := by
          exact_mod_cast le_add_self
        calc ENNReal.ofReal A * E1 + E2
            ≤ ((A.toNNReal + 1 : ℝ≥0) : ℝ≥0∞) * E1 + ((A.toNNReal + 1 : ℝ≥0) : ℝ≥0∞) * E2 := by
              gcongr
              exact le_mul_of_one_le_left' h1
          _ = _ := by rw [mul_add]
    _ = _ := by push_cast; ring


theorem eLpNorm_le_add_sub {α : Type*} {m : MeasurableSpace α} {μ : Measure α} (f g : α → ℝ)
    {p : ℝ≥0∞} (hp : 1 ≤ p) :
    eLpNorm f p μ ≤ eLpNorm g p μ + eLpNorm (fun x => f x - g x) p μ := by
  have : f = g + fun x => f x - g x := by funext x; simp
  calc eLpNorm f p μ = eLpNorm (g + fun x => f x - g x) p μ := by rw [← this]
    _ ≤ _ := eLpNorm_add_le hp

/-- Passage from smooth periodic functions to `H¹`: a Sobolev-type estimate valid for smooth
periodic functions extends to every function with an `L²` weak gradient (Fatou). -/
theorem eLpNorm_le_of_smooth_bound {q C : ℝ≥0∞} (hCt : C ≠ ⊤)
    (hC : ∀ φ : Torus d → ℝ, IsSmoothPeriodic φ → eLpNorm φ q (haar d) ≤
      C * (eLpNorm φ 2 (haar d) + ∑ j, eLpNorm (coordPartial j φ) 2 (haar d)))
    {u : Torus d → ℝ} {g : Torus d → Tangent d} (hg : IsWeakGradient u g) :
    eLpNorm u q (haar d) ≤
      C * (eLpNorm u 2 (haar d) + ∑ j, eLpNorm (fun x => g x j) 2 (haar d)) := by
  obtain ⟨v, hv, -, hvu, hvg⟩ := exists_smooth_tendsto_H1 hg
  set L : ℝ≥0∞ := C * (eLpNorm u 2 (haar d) + ∑ j, eLpNorm (fun x => g x j) 2 (haar d)) with hL
  set b : ℕ → ℝ≥0∞ := fun n => C * ((eLpNorm u 2 (haar d) + eLpNorm (fun x => v n x - u x) 2 (haar d)) +
    ∑ j, (eLpNorm (fun x => g x j) 2 (haar d) +
      eLpNorm (fun x => smoothGrad (v n) x j - g x j) 2 (haar d))) with hb
  have hbt : Tendsto b atTop (𝓝 L) := by
    have h1 : Tendsto (fun n => eLpNorm u 2 (haar d) + eLpNorm (fun x => v n x - u x) 2 (haar d))
        atTop (𝓝 (eLpNorm u 2 (haar d) + 0)) := tendsto_const_nhds.add hvu
    have h2 : Tendsto (fun n => ∑ j, (eLpNorm (fun x => g x j) 2 (haar d) +
        eLpNorm (fun x => smoothGrad (v n) x j - g x j) 2 (haar d))) atTop
        (𝓝 (∑ j, (eLpNorm (fun x => g x j) 2 (haar d) + 0))) :=
      tendsto_finsetSum _ fun j _ => tendsto_const_nhds.add (hvg j)
    have := ENNReal.Tendsto.const_mul (h1.add h2) (Or.inr hCt)
    simpa [hL, hb] using this
  have hbd : ∀ n, eLpNorm (v n) q (haar d) ≤ b n := by
    intro n
    refine (hC _ (hv n)).trans (mul_le_mul' le_rfl (add_le_add ?_ ?_))
    · exact eLpNorm_le_add_sub _ _ one_le_two
    · refine Finset.sum_le_sum fun j _ => ?_
      have := eLpNorm_le_add_sub (μ := haar d) (fun x => coordPartial j (v n) x)
        (fun x => g x j) one_le_two
      simpa using this
  have hmeas : TendstoInMeasure (haar d) v atTop u :=
    tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (by norm_num) (by
      simpa [Pi.sub_def] using hvu)
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  refine eLpNorm_le_of_tendstoInMeasure ?_ hmeas fun n => (hv n).continuous_torus.aestronglyMeasurable
  have hLfin : L ≠ ⊤ := by
    refine ENNReal.mul_ne_top hCt (ENNReal.add_ne_top.mpr ⟨hg.memLp.eLpNorm_lt_top.ne, ?_⟩)
    exact (ENNReal.sum_lt_top.mpr fun j _ => (memLp_coord hg.memLp_grad j).eLpNorm_lt_top).ne
  have hlt : L < L + ε := ENNReal.lt_add_right hLfin (by simpa using hε.ne')
  filter_upwards [hbt.eventually (gt_mem_nhds hlt)] with n hn
  exact (hbd n).trans hn.le


theorem eLpNorm_coord_le {g : Torus d → Tangent d} (hg : AEStronglyMeasurable g (haar d))
    (j : Fin d) (r : ℝ≥0∞) :
    eLpNorm (fun x => g x j) r (haar d) ≤ eLpNorm g r (haar d) :=
  eLpNorm_mono_ae
    (((EuclideanSpace.proj j : Tangent d →L[ℝ] ℝ).continuous.comp_aestronglyMeasurable hg))
    (Eventually.of_forall fun x => by simpa using PiLp.norm_apply_le (g x) j)

/-- The `H¹` Sobolev embedding in the subcritical range, with explicit exponents. -/
theorem h1_embedding (p q : ℝ≥0) (hp : 1 ≤ p) (hp2 : p ≤ 2) (hpd : (p : ℝ) < d)
    (hpq : (p : ℝ)⁻¹ - (d : ℝ)⁻¹ ≤ (q : ℝ)⁻¹) :
    ∃ C : ℝ≥0, ∀ (u : Torus d → ℝ) (g : Torus d → Tangent d), IsWeakGradient u g →
      MemLp u q (haar d) ∧
      eLpNorm u q (haar d) ≤ C * (eLpNorm u 2 (haar d) + eLpNorm g 2 (haar d)) := by
  obtain ⟨C, hC⟩ := smooth_sobolev p q hp hpd hpq
  have hp2' : (p : ℝ≥0∞) ≤ 2 := by exact_mod_cast hp2
  have hC2 : ∀ φ : Torus d → ℝ, IsSmoothPeriodic φ → eLpNorm φ (q : ℝ≥0∞) (haar d) ≤
      (C : ℝ≥0∞) * (eLpNorm φ 2 (haar d) + ∑ j, eLpNorm (coordPartial j φ) 2 (haar d)) := by
    intro φ hφ
    refine (hC φ hφ).trans (mul_le_mul' le_rfl (add_le_add ?_ ?_))
    · exact eLpNorm_le_eLpNorm_of_exponent_le hp2'
    · exact Finset.sum_le_sum fun j _ => eLpNorm_le_eLpNorm_of_exponent_le hp2'
  refine ⟨C * ((d : ℝ≥0) + 1), fun u g hg => ?_⟩
  have hb := eLpNorm_le_of_smooth_bound ENNReal.coe_ne_top hC2 hg
  have hgm := hg.memLp_grad.aestronglyMeasurable
  have hsum : ∑ j, eLpNorm (fun x => g x j) 2 (haar d) ≤ (d : ℝ≥0∞) * eLpNorm g 2 (haar d) := by
    calc ∑ j, eLpNorm (fun x => g x j) 2 (haar d) ≤ ∑ _j : Fin d, eLpNorm g 2 (haar d) :=
          Finset.sum_le_sum fun j _ => eLpNorm_coord_le hgm j 2
      _ = _ := by simp
  have hfin : eLpNorm u (q : ℝ≥0∞) (haar d) < ⊤ := by
    refine hb.trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top (ENNReal.add_lt_top.mpr
      ⟨hg.memLp.eLpNorm_lt_top, ENNReal.sum_lt_top.mpr fun j _ =>
        (memLp_coord hg.memLp_grad j).eLpNorm_lt_top⟩))
  refine ⟨hfin, hb.trans ?_⟩
  push_cast
  calc (C : ℝ≥0∞) * (eLpNorm u 2 (haar d) + ∑ j, eLpNorm (fun x => g x j) 2 (haar d))
      ≤ C * (eLpNorm u 2 (haar d) + (d : ℝ≥0∞) * eLpNorm g 2 (haar d)) := by gcongr
    _ ≤ C * (((d : ℝ≥0∞) + 1) * (eLpNorm u 2 (haar d) + eLpNorm g 2 (haar d))) := by
        gcongr
        calc eLpNorm u 2 (haar d) + (d : ℝ≥0∞) * eLpNorm g 2 (haar d)
            ≤ ((d : ℝ≥0∞) + 1) * eLpNorm u 2 (haar d) + ((d : ℝ≥0∞) + 1) * eLpNorm g 2 (haar d) := by
              gcongr
              · exact le_mul_of_one_le_left' (by simp)
              · exact le_self_add
          _ = _ := by rw [mul_add]
    _ = _ := by ring


/-- `d > 2`: `H¹ ↪ L^{2d/(d-2)}`. -/
theorem sobolev_embedding_critical (hd : 2 < d) :
    ∃ C : ℝ≥0, ∀ (u : Torus d → ℝ) (g : Torus d → Tangent d), IsWeakGradient u g →
      MemLp u (ENNReal.ofReal (2 * d / (d - 2))) (haar d) ∧
      eLpNorm u (ENNReal.ofReal (2 * d / (d - 2))) (haar d) ≤
        C * (eLpNorm u 2 (haar d) + eLpNorm g 2 (haar d)) := by
  have hd' : (2 : ℝ) < d := by exact_mod_cast hd
  have hpos : 0 < (2 * (d : ℝ) / (d - 2)) := by
    apply div_pos <;> linarith
  obtain ⟨C, hC⟩ := h1_embedding (d := d) 2 (Real.toNNReal (2 * d / (d - 2))) one_le_two le_rfl
    (by simpa using hd') (by
      rw [Real.coe_toNNReal _ hpos.le]
      simp only [NNReal.coe_ofNat]
      have : (d : ℝ) - 2 ≠ 0 := by linarith
      have h2 : (d : ℝ) ≠ 0 := by linarith
      rw [inv_div]
      field_simp
      rfl)
  exact ⟨C, hC⟩

/-- `d = 2`: `H¹ ↪ L^q` for every finite `q`. -/
theorem sobolev_embedding_dim_two (hd : d = 2) (q : ℝ≥0) :
    ∃ C : ℝ≥0, ∀ (u : Torus d → ℝ) (g : Torus d → Tangent d), IsWeakGradient u g →
      MemLp u (q : ℝ≥0∞) (haar d) ∧
      eLpNorm u (q : ℝ≥0∞) (haar d) ≤ C * (eLpNorm u 2 (haar d) + eLpNorm g 2 (haar d)) := by
  subst hd
  set q' : ℝ≥0 := max q 2 with hq'
  have hq2 : (2 : ℝ≥0) ≤ q' := le_max_right _ _
  have hqq : q ≤ q' := le_max_left _ _
  have hq2r : (2 : ℝ) ≤ q' := by exact_mod_cast hq2
  have hqpos : (0 : ℝ) < q' := by linarith
  set p : ℝ≥0 := 2 * q' / (q' + 2) with hp
  have hpr : (p : ℝ) = 2 * q' / (q' + 2) := by simp [hp]
  have hp1 : 1 ≤ p := by
    rw [← NNReal.coe_le_coe, hpr]
    rw [NNReal.coe_one, le_div_iff₀ (by positivity)]
    linarith
  have hp2 : p ≤ 2 := by
    rw [← NNReal.coe_le_coe, hpr, div_le_iff₀ (by positivity)]
    push_cast; linarith
  obtain ⟨C, hC⟩ := h1_embedding (d := 2) p q' hp1 hp2 (by
      rw [hpr]; push_cast
      rw [div_lt_iff₀ (by positivity)]; linarith) (by
      rw [hpr]; push_cast
      rw [inv_div]
      have : (q' : ℝ) ≠ 0 := hqpos.ne'
      field_simp
      ring_nf
      rfl)
  refine ⟨C, fun u g hg => ?_⟩
  obtain ⟨h1, h2⟩ := hC u g hg
  have hqq' : (q : ℝ≥0∞) ≤ q' := by exact_mod_cast hqq
  exact ⟨h1.mono_exponent hqq', (eLpNorm_le_eLpNorm_of_exponent_le hqq').trans h2⟩


theorem abs_sq_mul_log_sq_le {q : ℝ} (hq : 2 < q) (s : ℝ) :
    |s ^ 2 * Real.log (s ^ 2)| ≤ 1 + ‖s‖ ^ q / (q / 2 - 1) := by
  have hr : 0 < q / 2 - 1 := by linarith
  have hpos : 0 ≤ ‖s‖ ^ q / (q / 2 - 1) := by positivity
  set t : ℝ := s ^ 2 with ht
  have ht0 : 0 ≤ t := sq_nonneg s
  rcases ht0.eq_or_lt with h0 | hpos'
  · rw [← h0, zero_mul, abs_zero]; linarith
  rcases le_or_gt t 1 with h1 | h1
  · have hlog : Real.log t ≤ 0 := Real.log_nonpos ht0 h1
    rw [abs_of_nonpos (mul_nonpos_of_nonneg_of_nonpos ht0 hlog)]
    have h2 : Real.log (1 / t) ≤ 1 / t - 1 := Real.log_le_sub_one_of_pos (by positivity)
    rw [one_div, Real.log_inv] at h2
    have h3 : t * (-Real.log t) ≤ t * (t⁻¹ - 1) := mul_le_mul_of_nonneg_left h2 ht0
    have h4 : t * (t⁻¹ - 1) = 1 - t := by field_simp
    nlinarith
  · have hlog : 0 ≤ Real.log t := Real.log_nonneg h1.le
    rw [abs_of_nonneg (mul_nonneg ht0 hlog)]
    have h2 : Real.log t ≤ t ^ (q / 2 - 1) / (q / 2 - 1) := Real.log_le_rpow_div ht0 hr
    have h3 : t * Real.log t ≤ t * (t ^ (q / 2 - 1) / (q / 2 - 1)) :=
      mul_le_mul_of_nonneg_left h2 ht0
    have h4 : t * (t ^ (q / 2 - 1) / (q / 2 - 1)) = ‖s‖ ^ q / (q / 2 - 1) := by
      rw [← mul_div_assoc]
      congr 1
      have : t ^ (q / 2) = ‖s‖ ^ q := by
        rw [ht, ← sq_abs s, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg s),
          Real.norm_eq_abs]
        congr 1
        push_cast; ring
      rw [← this, Real.rpow_sub_one hpos'.ne']
      field_simp
    linarith


theorem integrable_sq_mul_log_sq_of_memLp {u : Torus d → ℝ} {q : ℝ≥0∞} (hq : 2 < q)
    (hqt : q ≠ ⊤) (hu : MemLp u q (haar d)) :
    Integrable (fun x => u x ^ 2 * Real.log (u x ^ 2)) (haar d) := by
  have hq0 : q ≠ 0 := (lt_trans zero_lt_two hq).ne'
  have hqr : 2 < q.toReal := by
    have := (ENNReal.ofReal_lt_iff_lt_toReal (a := 2) (b := q) (by norm_num) hqt).mp
      (by simpa using hq)
    exact this
  have hint : Integrable (fun x => ‖u x‖ ^ q.toReal) (haar d) := hu.integrable_norm_rpow hq0 hqt
  have hm := hu.aestronglyMeasurable
  have hmeas : AEStronglyMeasurable (fun x => u x ^ 2 * Real.log (u x ^ 2)) (haar d) :=
    ((hm.aemeasurable.pow_const 2).mul
      (Real.measurable_log.comp_aemeasurable (hm.aemeasurable.pow_const 2))).aestronglyMeasurable
  refine Integrable.mono' ((integrable_const (1 : ℝ)).add (hint.div_const (q.toReal / 2 - 1))) hmeas
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs]
  exact abs_sq_mul_log_sq_le hqr (u x)



theorem sq_intervalIntegral_le {f : ℝ → ℝ} (hf : Continuous f) {a b : ℝ} (hab : a ≤ b) :
    (∫ x in a..b, f x) ^ 2 ≤ (b - a) * ∫ x in a..b, f x ^ 2 := by
  rcases hab.eq_or_lt with h | h
  · subst h; simp
  have key : ∀ c : ℝ, 0 ≤ (∫ x in a..b, f x ^ 2) - 2 * c * (∫ x in a..b, f x) + c ^ 2 * (b - a) := by
    intro c
    have h1 : 0 ≤ ∫ x in a..b, (f x - c) ^ 2 :=
      intervalIntegral.integral_nonneg hab fun x _ => sq_nonneg _
    have h2 : ∫ x in a..b, (f x - c) ^ 2 =
        (∫ x in a..b, f x ^ 2) - 2 * c * (∫ x in a..b, f x) + c ^ 2 * (b - a) := by
      have e : (fun x => (f x - c) ^ 2) = fun x => (f x ^ 2 - (2 * c) * f x) + c ^ 2 := by
        funext x; ring
      rw [e, intervalIntegral.integral_add, intervalIntegral.integral_sub,
        intervalIntegral.integral_const_mul]
      · simp; ring
      · exact (hf.pow 2).intervalIntegrable _ _
      · exact (hf.const_smul (2 * c)).intervalIntegrable _ _
      · exact ((hf.pow 2).sub (continuous_const.mul hf)).intervalIntegrable _ _
      · exact intervalIntegrable_const
    linarith
  have hL : 0 < b - a := sub_pos.mpr h
  have := key ((∫ x in a..b, f x) / (b - a))
  set I := ∫ x in a..b, f x
  set J := ∫ x in a..b, f x ^ 2
  have e : J - 2 * (I / (b - a)) * I + (I / (b - a)) ^ 2 * (b - a) = J - I ^ 2 / (b - a) := by
    field_simp; ring
  rw [e] at this
  rw [← sub_nonneg]
  have : 0 ≤ (b - a) * (J - I ^ 2 / (b - a)) := mul_nonneg hL.le this
  calc 0 ≤ (b - a) * (J - I ^ 2 / (b - a)) := this
    _ = (b - a) * J - I ^ 2 := by field_simp


theorem integral_haar_one (f : Torus 1 → ℝ) (hf : Continuous f) :
    ∫ x, f x ∂haar 1 = ∫ t in (0 : ℝ)..1, f (torusLift (fun _ => t)) := by
  rw [haar_eq_map_unitBox, integral_map SharpLSI.measurable_liftT.aemeasurable
    hf.aestronglyMeasurable]
  have hmp := (volume_preserving_funUnique (Fin 1) ℝ).symm
  have hemb : MeasurableEmbedding (MeasurableEquiv.funUnique (Fin 1) ℝ).symm :=
    (MeasurableEquiv.funUnique (Fin 1) ℝ).symm.measurableEmbedding
  have := hmp.setIntegral_preimage_emb hemb (fun x => f (torusLift x)) (SharpLSI.unitBox (Fin 1))
  have hpre : (MeasurableEquiv.funUnique (Fin 1) ℝ).symm ⁻¹' (SharpLSI.unitBox (Fin 1)) =
      Ioc (0 : ℝ) 1 := by
    ext t
    simp [SharpLSI.unitBox]
  rw [hpre] at this
  rw [intervalIntegral.integral_of_le zero_le_one]
  exact this.symm

theorem torusLift_one_add (t : ℝ) :
    (torusLift (fun _ : Fin 1 => t + 1) : Torus 1) = torusLift (fun _ => t) := by
  ext i
  simp [torusLift, SharpLSI.liftT]

theorem hasDerivAt_smooth_one {φ : Torus 1 → ℝ} (hφ : IsSmoothPeriodic φ) (t : ℝ) :
    HasDerivAt (fun t : ℝ => φ (torusLift (fun _ => t)))
      (coordPartial 0 φ (torusLift (fun _ => t))) t := by
  have hF : DifferentiableAt ℝ (φ ∘ torusLift) (fun _ : Fin 1 => t) :=
    (hφ.differentiable (by simp)) _
  have hc : HasDerivAt (fun t : ℝ => (fun _ : Fin 1 => t)) (fun _ : Fin 1 => (1 : ℝ)) t :=
    hasDerivAt_pi.mpr fun _ => hasDerivAt_id t
  have h := hF.hasFDerivAt.comp_hasDerivAt t hc
  rw [coordPartial_torusLift]
  have e : (Pi.single (0 : Fin 1) (1 : ℝ)) = fun _ : Fin 1 => (1 : ℝ) := by
    funext i; fin_cases i; simp
  rw [e]
  exact h

theorem periodic_coordPartial_one {φ : Torus 1 → ℝ} :
    Function.Periodic (fun t : ℝ => coordPartial 0 φ (torusLift (fun _ => t))) 1 := by
  intro t
  simp only [torusLift_one_add]

theorem smooth_holder_sq_aux {φ : Torus 1 → ℝ} (hφ : IsSmoothPeriodic φ) {a b : ℝ} (hab : a ≤ b)
    (hba : b - a ≤ 1) :
    (φ (torusLift (fun _ => b)) - φ (torusLift (fun _ => a))) ^ 2 ≤
      (b - a) * ∫ x, (coordPartial 0 φ x) ^ 2 ∂haar 1 := by
  have hc : Continuous (fun t : ℝ => coordPartial 0 φ (torusLift (fun _ : Fin 1 => t))) :=
    (hφ.continuous_coordPartial 0).comp
      (SharpLSI.continuous_liftT.comp (continuous_pi fun _ => continuous_id))
  have hftc : ∫ t in a..b, coordPartial 0 φ (torusLift (fun _ : Fin 1 => t)) =
      φ (torusLift (fun _ => b)) - φ (torusLift (fun _ => a)) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hasDerivAt_smooth_one hφ t)
      (hc.intervalIntegrable _ _)
  have h1 := sq_intervalIntegral_le hc hab
  rw [hftc] at h1
  have hper : Function.Periodic
      (fun t : ℝ => (coordPartial 0 φ (torusLift (fun _ : Fin 1 => t))) ^ 2) 1 := by
    intro t; simp only [torusLift_one_add]
  have h2 : ∫ t in a..b, (coordPartial 0 φ (torusLift (fun _ : Fin 1 => t))) ^ 2 ≤
      ∫ t in (0 : ℝ)..1, (coordPartial 0 φ (torusLift (fun _ : Fin 1 => t))) ^ 2 := by
    have h3 : ∫ t in a..a + 1, (coordPartial 0 φ (torusLift (fun _ : Fin 1 => t))) ^ 2 =
        ∫ t in (0 : ℝ)..0 + 1, (coordPartial 0 φ (torusLift (fun _ : Fin 1 => t))) ^ 2 :=
      hper.intervalIntegral_add_eq a 0
    rw [zero_add] at h3
    rw [← h3]
    exact intervalIntegral.integral_mono_interval le_rfl hab (by linarith)
      (Filter.Eventually.of_forall fun t => sq_nonneg _) ((hc.pow 2).intervalIntegrable _ _)
  have h4 : ∫ x, (coordPartial 0 φ x) ^ 2 ∂haar 1 =
      ∫ t in (0 : ℝ)..1, (coordPartial 0 φ (torusLift (fun _ : Fin 1 => t))) ^ 2 :=
    integral_haar_one _ ((hφ.continuous_coordPartial 0).pow 2)
  rw [h4]
  calc _ ≤ (b - a) * ∫ t in a..b, (coordPartial 0 φ (torusLift (fun _ : Fin 1 => t))) ^ 2 := h1
    _ ≤ _ := mul_le_mul_of_nonneg_left h2 (by linarith)

theorem torusDist_one (x y : Torus 1) : torusDist x y = ‖x 0 - y 0‖ := by
  unfold torusDist SharpLSI.flatDist
  simp

theorem exists_lifts_one (x y : Torus 1) :
    ∃ a b : ℝ, torusLift (fun _ => a) = x ∧ torusLift (fun _ => b) = y ∧
      |a - b| = torusDist x y ∧ torusDist x y ≤ 1 / 2 := by
  obtain ⟨a0, ha0⟩ := QuotientAddGroup.mk_surjective (x 0)
  obtain ⟨b0, hb0⟩ := QuotientAddGroup.mk_surjective (y 0)
  refine ⟨a0, b0 + round (a0 - b0), ?_, ?_, ?_, ?_⟩
  · ext i; fin_cases i; simpa [torusLift, SharpLSI.liftT] using ha0
  · ext i; fin_cases i
    simp only [torusLift, SharpLSI.liftT]
    show ((b0 + (round (a0 - b0) : ℝ) : ℝ) : AddCircle (1 : ℝ)) = y 0
    rw [← hb0, AddCircle.coe_add]
    have : (((round (a0 - b0) : ℤ) : ℝ) : AddCircle (1 : ℝ)) = 0 :=
      (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).mpr ⟨round (a0 - b0), by simp⟩
    rw [this, add_zero]
  · rw [torusDist_one, ← ha0, ← hb0, ← AddCircle.coe_sub, UnitAddCircle.norm_eq]
    congr 1
    ring
  · rw [torusDist_one, ← ha0, ← hb0, ← AddCircle.coe_sub, UnitAddCircle.norm_eq]
    exact abs_sub_round _

theorem toReal_eLpNorm_two {α : Type*} {m : MeasurableSpace α} {μ : Measure α} {f : α → ℝ}
    (hf : MemLp f 2 μ) : (eLpNorm f 2 μ).toReal = Real.sqrt (∫ x, f x ^ 2 ∂μ) := by
  have h := hf.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)
  rw [h, ENNReal.toReal_ofReal (by positivity)]
  rw [Real.sqrt_eq_rpow]
  simp only [ENNReal.toReal_ofNat, Real.norm_eq_abs]
  congr 1
  · congr 1
    funext x
    rw [Real.rpow_two, sq_abs]
  · norm_num

theorem smooth_holder_one {φ : Torus 1 → ℝ} (hφ : IsSmoothPeriodic φ) (x y : Torus 1) :
    (φ x - φ y) ^ 2 ≤ torusDist x y * ∫ z, (coordPartial 0 φ z) ^ 2 ∂haar 1 := by
  obtain ⟨a, b, rfl, rfl, hab, hle⟩ := exists_lifts_one x y
  rw [← hab]
  rcases le_total b a with h | h
  · have h1 := smooth_holder_sq_aux hφ h (by
      have := le_abs_self (a - b); linarith)
    rwa [abs_of_nonneg (sub_nonneg.mpr h)]
  · have h1 := smooth_holder_sq_aux hφ h (by
      have := le_abs_self (b - a); rw [abs_sub_comm] at hab; linarith)
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr h), ← neg_sub, neg_sq]
    exact h1

theorem torusDist_one_le (x y : Torus 1) : torusDist x y ≤ 1 / 2 := by
  obtain ⟨a, b, -, -, -, h⟩ := exists_lifts_one x y
  exact h

theorem smooth_sup_one {φ : Torus 1 → ℝ} (hφ : IsSmoothPeriodic φ) (x : Torus 1) :
    |φ x| ≤ Real.sqrt (∫ z, φ z ^ 2 ∂haar 1) +
      Real.sqrt (∫ z, (coordPartial 0 φ z) ^ 2 ∂haar 1) := by
  have hint : Integrable (fun z => φ z ^ 2) (haar 1) :=
    (memLp_two_of_continuous hφ.continuous_torus).integrable_sq
  obtain ⟨y, hy⟩ := exists_le_integral hint
  have h1 : |φ y| ≤ Real.sqrt (∫ z, φ z ^ 2 ∂haar 1) := Real.abs_le_sqrt hy
  have hS : 0 ≤ ∫ z, (coordPartial 0 φ z) ^ 2 ∂haar 1 := integral_nonneg fun z => sq_nonneg _
  have h2 : |φ x - φ y| ≤ Real.sqrt (∫ z, (coordPartial 0 φ z) ^ 2 ∂haar 1) := by
    apply Real.abs_le_sqrt
    refine (smooth_holder_one hφ x y).trans ?_
    have := torusDist_one_le x y
    nlinarith
  calc |φ x| = |φ y + (φ x - φ y)| := by ring_nf
    _ ≤ |φ y| + |φ x - φ y| := abs_add_le _ _
    _ ≤ _ := add_le_add h1 h2

theorem smooth_sup_one' {φ : Torus 1 → ℝ} (hφ : IsSmoothPeriodic φ) (x : Torus 1) :
    |φ x| ≤ (eLpNorm φ 2 (haar 1)).toReal +
      (eLpNorm (coordPartial 0 φ) 2 (haar 1)).toReal := by
  rw [toReal_eLpNorm_two (memLp_two_of_continuous hφ.continuous_torus),
    toReal_eLpNorm_two (memLp_two_of_continuous (hφ.continuous_coordPartial 0))]
  exact smooth_sup_one hφ x

theorem smooth_holder_one' {φ : Torus 1 → ℝ} (hφ : IsSmoothPeriodic φ) (x y : Torus 1) :
    (φ x - φ y) ^ 2 ≤ torusDist x y * (eLpNorm (coordPartial 0 φ) 2 (haar 1)).toReal ^ 2 := by
  rw [toReal_eLpNorm_two (memLp_two_of_continuous (hφ.continuous_coordPartial 0)),
    Real.sq_sqrt (integral_nonneg fun z => sq_nonneg _)]
  exact smooth_holder_one hφ x y

theorem coordPartial_sub {d : ℕ} {v w : Torus d → ℝ} (hv : IsSmoothPeriodic v)
    (hw : IsSmoothPeriodic w) (j : Fin d) (x : Torus d) :
    coordPartial j (fun y => v y - w y) x = coordPartial j v x - coordPartial j w x := by
  have hv1 : DifferentiableAt ℝ (v ∘ torusLift) (SharpLSI.secT x) :=
    (hv.differentiable (by simp)) _
  have hw1 : DifferentiableAt ℝ (w ∘ torusLift) (SharpLSI.secT x) :=
    (hw.differentiable (by simp)) _
  show fderiv ℝ (fun y => (v ∘ torusLift) y - (w ∘ torusLift) y) (SharpLSI.secT x)
    (Pi.single j 1) = _
  rw [fderiv_fun_sub hv1 hw1]
  rfl

theorem IsSmoothPeriodic.sub' {d : ℕ} {v w : Torus d → ℝ} (hv : IsSmoothPeriodic v)
    (hw : IsSmoothPeriodic w) : IsSmoothPeriodic (fun y => v y - w y) :=
  ContDiff.sub hv hw

theorem eLpNorm_sub_le_fun {α : Type*} {m : MeasurableSpace α} {μ : Measure α}
    (f h : α → ℝ) : eLpNorm (fun x => f x - h x) 2 μ ≤ eLpNorm f 2 μ + eLpNorm h 2 μ :=
  eLpNorm_sub_le (f := f) (g := h) (by norm_num)

theorem toReal_eLpNorm_le_add_sub {α : Type*} {m : MeasurableSpace α} {μ : Measure α}
    {f g : α → ℝ} (hg : MemLp g 2 μ) (hfg : MemLp (fun x => f x - g x) 2 μ) :
    (eLpNorm f 2 μ).toReal ≤
      (eLpNorm g 2 μ).toReal + (eLpNorm (fun x => f x - g x) 2 μ).toReal := by
  rw [← ENNReal.toReal_add hg.eLpNorm_lt_top.ne hfg.eLpNorm_lt_top.ne]
  exact ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hg.eLpNorm_lt_top.ne, hfg.eLpNorm_lt_top.ne⟩)
    (eLpNorm_le_add_sub f g (by norm_num))

theorem toReal_eLpNorm_sub_le {α : Type*} {m : MeasurableSpace α} {μ : Measure α}
    {f g : α → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (eLpNorm (fun x => f x - g x) 2 μ).toReal ≤
      (eLpNorm f 2 μ).toReal + (eLpNorm g 2 μ).toReal := by
  rw [← ENNReal.toReal_add hf.eLpNorm_lt_top.ne hg.eLpNorm_lt_top.ne]
  exact ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hf.eLpNorm_lt_top.ne, hg.eLpNorm_lt_top.ne⟩)
    (eLpNorm_sub_le_fun f g)


theorem torusDist_one_nonneg (x y : Torus 1) : 0 ≤ torusDist x y := by
  rw [torusDist_one]; exact norm_nonneg _

theorem exists_continuous_rep_one {u : Torus 1 → ℝ} {g : Torus 1 → Tangent 1}
    (hg : IsWeakGradient u g) :
    ∃ w : Torus 1 → ℝ, Continuous w ∧ w =ᵐ[haar 1] u ∧
      (∀ x y, (w x - w y) ^ 2 ≤ torusDist x y * (eLpNorm g 2 (haar 1)).toReal ^ 2) ∧
      ∀ x, |w x| ≤ (eLpNorm u 2 (haar 1)).toReal + (eLpNorm g 2 (haar 1)).toReal := by
  obtain ⟨v, hv, -, h1, h2⟩ := exists_smooth_tendsto_H1 hg
  have h20 := h2 0
  set G0 : Torus 1 → ℝ := fun x => g x 0 with hG0
  have hG0m : MemLp G0 2 (haar 1) := memLp_coord hg.memLp_grad 0
  have hvm : ∀ n, MemLp (v n) 2 (haar 1) := fun n =>
    memLp_two_of_continuous (hv n).continuous_torus
  have hdm : ∀ n, MemLp (fun x => v n x - u x) 2 (haar 1) := fun n => (hvm n).sub hg.memLp
  have hpm : ∀ n, MemLp (coordPartial 0 (v n)) 2 (haar 1) := fun n =>
    memLp_two_of_continuous ((hv n).continuous_coordPartial 0)
  have hpdm : ∀ n, MemLp (fun x => coordPartial 0 (v n) x - G0 x) 2 (haar 1) := fun n =>
    (hpm n).sub hG0m
  have h20' : Tendsto (fun n => eLpNorm (fun x => coordPartial 0 (v n) x - G0 x) 2 (haar 1))
      atTop (𝓝 0) := h20
  set a : ℕ → ℝ := fun n => (eLpNorm (fun x => v n x - u x) 2 (haar 1)).toReal with ha_def
  set b : ℕ → ℝ := fun n =>
    (eLpNorm (fun x => coordPartial 0 (v n) x - G0 x) 2 (haar 1)).toReal with hb_def
  have ha : Tendsto a atTop (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h1
    rw [ENNReal.toReal_zero] at this
    exact this
  have hb : Tendsto b atTop (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h20'
    rw [ENNReal.toReal_zero] at this
    exact this
  have hc : Tendsto (fun n => a n + b n) atTop (𝓝 0) := by simpa using ha.add hb
  have hU : ∀ n m x, |v n x - v m x| ≤ (a n + b n) + (a m + b m) := by
    intro n m x
    have hs : |v n x - v m x| ≤
        (eLpNorm (fun y => v n y - v m y) 2 (haar 1)).toReal +
        (eLpNorm (coordPartial 0 (fun y => v n y - v m y)) 2 (haar 1)).toReal :=
      smooth_sup_one' ((hv n).sub' (hv m)) x
    have e1 : coordPartial 0 (fun y => v n y - v m y) =
        fun x => coordPartial 0 (v n) x - coordPartial 0 (v m) x :=
      funext fun x => coordPartial_sub (hv n) (hv m) 0 x
    rw [e1] at hs
    have s1 : (eLpNorm (fun y => v n y - v m y) 2 (haar 1)).toReal ≤ a n + a m := by
      have : (fun y => v n y - v m y) = fun y => (v n y - u y) - (v m y - u y) := by
        funext y; ring
      rw [this]; exact toReal_eLpNorm_sub_le (hdm n) (hdm m)
    have s2 : (eLpNorm (fun x => coordPartial 0 (v n) x - coordPartial 0 (v m) x) 2
        (haar 1)).toReal ≤ b n + b m := by
      have : (fun x => coordPartial 0 (v n) x - coordPartial 0 (v m) x) =
          fun x => (coordPartial 0 (v n) x - G0 x) - (coordPartial 0 (v m) x - G0 x) := by
        funext y; ring
      rw [this]; exact toReal_eLpNorm_sub_le (hpdm n) (hpdm m)
    linarith
  have hcau : ∀ x, ∃ l, Tendsto (fun n => v n x) atTop (𝓝 l) := by
    intro x
    apply cauchySeq_tendsto_of_complete
    rw [Metric.cauchySeq_iff']
    intro ε hε
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
      (hc.eventually (gt_mem_nhds (show (0 : ℝ) < ε / 2 by positivity)))
    refine ⟨N, fun n hn => ?_⟩
    rw [Real.dist_eq]
    have := hU n N x
    have := hN n hn
    have := hN N le_rfl
    linarith
  choose w hw using hcau
  have hwb : ∀ n x, |v n x - w x| ≤ a n + b n := by
    intro n x
    have h3 : Tendsto (fun m => |v n x - v m x|) atTop (𝓝 |v n x - w x|) :=
      (tendsto_const_nhds.sub (hw x)).abs
    have h4 : Tendsto (fun m => (a n + b n) + (a m + b m)) atTop (𝓝 ((a n + b n) + 0)) :=
      tendsto_const_nhds.add hc
    have := le_of_tendsto_of_tendsto' h3 h4 (fun m => hU n m x)
    simpa using this
  have hcont : Continuous w := by
    have hT : TendstoUniformly (fun n => v n) w atTop := by
      rw [Metric.tendstoUniformly_iff]
      intro ε hε
      filter_upwards [hc.eventually (gt_mem_nhds hε)] with n hn x
      rw [Real.dist_eq, abs_sub_comm]
      exact lt_of_le_of_lt (hwb n x) hn
    exact hT.continuous (Eventually.of_forall fun n => (hv n).continuous_torus).frequently
  have hae : w =ᵐ[haar 1] u := by
    have hbound : ∀ n, eLpNorm (fun x => w x - u x) 2 (haar 1) ≤
        ENNReal.ofReal (a n + b n) + eLpNorm (fun x => v n x - u x) 2 (haar 1) := by
      intro n
      have hsplit : (fun x => w x - u x) = fun x => (w x - v n x) + (v n x - u x) := by
        funext x; ring
      rw [hsplit]
      refine (eLpNorm_add_le (f := fun x => w x - v n x) (g := fun x => v n x - u x)
        (by norm_num)).trans (add_le_add ?_ le_rfl)
      have := eLpNorm_le_of_ae_bound (μ := haar 1) (p := 2) (f := fun x => w x - v n x)
        (C := a n + b n) (hcont.sub (hv n).continuous_torus).aestronglyMeasurable
        (Eventually.of_forall fun x => by
          rw [Real.norm_eq_abs, abs_sub_comm]; exact hwb n x)
      simpa using this
    have hlim : Tendsto (fun n => ENNReal.ofReal (a n + b n) +
        eLpNorm (fun x => v n x - u x) 2 (haar 1)) atTop (𝓝 0) := by
      have : Tendsto (fun n => ENNReal.ofReal (a n + b n)) atTop (𝓝 0) := by
        simpa using ENNReal.tendsto_ofReal hc
      simpa using this.add h1
    have h0 : eLpNorm (fun x => w x - u x) 2 (haar 1) ≤ 0 := ge_of_tendsto' hlim hbound
    have h00 : eLpNorm (fun x => w x - u x) 2 (haar 1) = 0 := le_zero_iff.mp h0
    rw [eLpNorm_eq_zero_iff (by norm_num)] at h00
    filter_upwards [h00] with x hx
    simpa [sub_eq_zero] using hx
  have hB0 : (eLpNorm G0 2 (haar 1)).toReal ≤ (eLpNorm g 2 (haar 1)).toReal :=
    ENNReal.toReal_mono hg.memLp_grad.eLpNorm_lt_top.ne
      (eLpNorm_coord_le hg.memLp_grad.aestronglyMeasurable 0 2)
  have hAn : ∀ n, (eLpNorm (v n) 2 (haar 1)).toReal ≤ (eLpNorm u 2 (haar 1)).toReal + a n :=
    fun n => toReal_eLpNorm_le_add_sub hg.memLp (hdm n)
  have hBn : ∀ n, (eLpNorm (coordPartial 0 (v n)) 2 (haar 1)).toReal ≤
      (eLpNorm G0 2 (haar 1)).toReal + b n :=
    fun n => toReal_eLpNorm_le_add_sub hG0m (hpdm n)
  refine ⟨w, hcont, hae, ?_, ?_⟩
  · intro x y
    have hn : ∀ n, (v n x - v n y) ^ 2 ≤
        torusDist x y * ((eLpNorm G0 2 (haar 1)).toReal + b n) ^ 2 := by
      intro n
      refine (smooth_holder_one' (hv n) x y).trans ?_
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ ENNReal.toReal_nonneg (hBn n) 2) (torusDist_one_nonneg x y)
    have h3 : Tendsto (fun n => (v n x - v n y) ^ 2) atTop (𝓝 ((w x - w y) ^ 2)) :=
      ((hw x).sub (hw y)).pow 2
    have h4 : Tendsto (fun n => torusDist x y * ((eLpNorm G0 2 (haar 1)).toReal + b n) ^ 2)
        atTop (𝓝 (torusDist x y * ((eLpNorm G0 2 (haar 1)).toReal + 0) ^ 2)) :=
      tendsto_const_nhds.mul ((tendsto_const_nhds.add hb).pow 2)
    have := le_of_tendsto_of_tendsto' h3 h4 hn
    refine this.trans ?_
    rw [add_zero]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ENNReal.toReal_nonneg hB0 2)
      (torusDist_one_nonneg x y)
  · intro x
    have hn : ∀ n, |v n x| ≤ ((eLpNorm u 2 (haar 1)).toReal + (eLpNorm G0 2 (haar 1)).toReal) +
        (a n + b n) := by
      intro n
      have := smooth_sup_one' (hv n) x
      have := hAn n
      have := hBn n
      linarith
    have h3 : Tendsto (fun n => |v n x|) atTop (𝓝 |w x|) := (hw x).abs
    have h4 : Tendsto (fun n => ((eLpNorm u 2 (haar 1)).toReal +
        (eLpNorm G0 2 (haar 1)).toReal) + (a n + b n)) atTop
        (𝓝 (((eLpNorm u 2 (haar 1)).toReal + (eLpNorm G0 2 (haar 1)).toReal) + 0)) :=
      tendsto_const_nhds.add hc
    have := le_of_tendsto_of_tendsto' h3 h4 hn
    rw [add_zero] at this
    linarith


theorem memLp_top_of_continuous' {h : Torus d → ℝ} (hc : Continuous h) : MemLp h ⊤ (haar d) := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hc.continuousOn
  exact memLp_top_of_bound hc.aestronglyMeasurable C
    (Eventually.of_forall fun x => hC x (mem_univ x))

theorem moll_mem_Icc {W : Torus d → ℝ} (hW : Continuous W) {a b : ℝ}
    (hab : ∀ x, W x ∈ Icc a b) (n : ℕ) (y : Torus d) : SharpLSI.moll n W y ∈ Icc a b := by
  have hphi : Integrable (SharpLSI.phiSeq (ι := Fin d) n) := by
    refine Integrable.of_integral_ne_zero ?_
    rw [SharpLSI.integral_phiSeq]; exact one_ne_zero
  have hWc : Continuous fun s : Fin d → ℝ => W (y - torusLift s) := by
    have : Continuous fun s : Fin d → ℝ => (y - torusLift s) :=
      continuous_const.sub SharpLSI.continuous_liftT
    exact hW.comp this
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hW.continuousOn
  have hi : Integrable (fun s => SharpLSI.phiSeq (ι := Fin d) n s * W (y - torusLift s)) := by
    refine hphi.mul_bdd (c := C) hWc.aestronglyMeasurable ?_ |>.congr ?_
    · exact Eventually.of_forall fun s => hC _ (mem_univ _)
    · exact Eventually.of_forall fun s => by simp
  rw [moll_apply_eq]
  have hphi' : ∀ s, 0 ≤ SharpLSI.phiSeq (ι := Fin d) n s := SharpLSI.phiSeq_nonneg n
  constructor
  · calc a = ∫ s, SharpLSI.phiSeq (ι := Fin d) n s * a := by
          rw [integral_mul_const, SharpLSI.integral_phiSeq, one_mul]
      _ ≤ _ := integral_mono (hphi.mul_const a) hi fun s =>
          mul_le_mul_of_nonneg_left (hab _).1 (hphi' s)
  · calc _ ≤ ∫ s, SharpLSI.phiSeq (ι := Fin d) n s * b :=
          integral_mono hi (hphi.mul_const b) fun s =>
            mul_le_mul_of_nonneg_left (hab _).2 (hphi' s)
      _ = b := by rw [integral_mul_const, SharpLSI.integral_phiSeq, one_mul]


theorem isSmoothPeriodic_comp {v : Torus d → ℝ} (hv : IsSmoothPeriodic v) {F : ℝ → ℝ} {a b : ℝ}
    (hF : ContDiffOn ℝ ∞ F (Icc a b)) (hr : ∀ x, v x ∈ Icc a b) :
    IsSmoothPeriodic (fun x => F (v x)) :=
  hF.comp_contDiff hv (fun _ => hr _)

theorem coordPartial_comp {v : Torus d → ℝ} (hv : IsSmoothPeriodic v) {F : ℝ → ℝ} {a b : ℝ}
    (hF : ContDiffOn ℝ ∞ F (Icc a b)) (hr : ∀ x, v x ∈ Icc a b)
    (j : Fin d) (y : Torus d) :
    coordPartial j (fun x => F (v x)) y
      = derivWithin F (Icc a b) (v y) * coordPartial j v y := by
  have hv1 : DifferentiableAt ℝ (v ∘ torusLift) (SharpLSI.secT y) :=
    (hv.differentiable (by simp)) _
  have hFd : DifferentiableWithinAt ℝ F (Icc a b) (v y) :=
    (hF.differentiableOn (by simp)) _ (hr y)
  have hF1 : HasDerivWithinAt F (derivWithin F (Icc a b) (v y)) (Icc a b) (v y) :=
    hFd.hasDerivWithinAt
  have hF2 : HasDerivWithinAt F (derivWithin F (Icc a b) (v y)) (Icc a b)
      ((v ∘ torusLift) (SharpLSI.secT y)) := by
    simpa [Function.comp_apply, SharpLSI.liftT_secT] using hF1
  have h := hF2.comp_hasFDerivAt (SharpLSI.secT y) hv1.hasFDerivAt
    (Eventually.of_forall fun x => hr _)
  unfold coordPartial
  have e : ((fun x => F (v x)) ∘ torusLift) = F ∘ (v ∘ torusLift) := rfl
  rw [e, h.fderiv]
  simp


theorem tendsto_lintegral_mul_of_unif {A : ℕ → Torus d → ℝ} {B k : Torus d → ℝ}
    (hk : Integrable k (haar d))
    (h : ∀ ε > 0, ∀ᶠ n in atTop, ∀ x, |A n x - B x| ≤ ε) :
    Tendsto (fun n => ∫⁻ y, ‖(A n y - B y) * k y‖ₑ ∂haar d) atTop (𝓝 0) := by
  have hL : ∫⁻ y, ‖k y‖ₑ ∂haar d < ⊤ := hk.2
  set L := ∫⁻ y, ‖k y‖ₑ ∂haar d with hLdef
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  by_cases hεt : ε = ⊤
  · exact Eventually.of_forall fun n => hεt ▸ le_top
  have hεr : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hεt
  have hδp : 0 < ε.toReal / (L.toReal + 1) := by positivity
  filter_upwards [h _ hδp] with n hn
  calc ∫⁻ y, ‖(A n y - B y) * k y‖ₑ ∂haar d
      ≤ ∫⁻ y, ENNReal.ofReal (ε.toReal / (L.toReal + 1)) * ‖k y‖ₑ ∂haar d := by
        refine lintegral_mono fun y => ?_
        rw [enorm_mul]
        gcongr
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (by simpa [Real.norm_eq_abs] using hn y)
    _ = ENNReal.ofReal (ε.toReal / (L.toReal + 1)) * L :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (ε.toReal / (L.toReal + 1) * L.toReal) := by
        rw [ENNReal.ofReal_mul hδp.le, ENNReal.ofReal_toReal hL.ne]
    _ ≤ ENNReal.ofReal ε.toReal := by
        apply ENNReal.ofReal_le_ofReal
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        nlinarith [ENNReal.toReal_nonneg (a := L)]
    _ = ε := ENNReal.ofReal_toReal hεt

theorem unif_comp {H : ℝ → ℝ} {a b : ℝ} (hH : ContinuousOn H (Icc a b))
    {V : ℕ → Torus d → ℝ} {W : Torus d → ℝ}
    (hV : ∀ n x, V n x ∈ Icc a b) (hW : ∀ x, W x ∈ Icc a b)
    (hu : ∀ δ > 0, ∀ᶠ n in atTop, ∀ x, |V n x - W x| ≤ δ) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ x, |H (V n x) - H (W x)| ≤ ε := by
  intro ε hε
  obtain ⟨δ, hδ, hδ'⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hH) ε hε
  filter_upwards [hu (δ / 2) (by positivity)] with n hn x
  have := hδ' _ (hV n x) _ (hW x) (by
    rw [Real.dist_eq]; exact lt_of_le_of_lt (hn x) (by linarith))
  rw [Real.dist_eq] at this
  exact this.le


theorem chain_rule_of_cont_rep {u : Torus d → ℝ} {g : Torus d → Tangent d}
    (hg : IsWeakGradient u g) {W : Torus d → ℝ} (hW : Continuous W) (hWu : W =ᵐ[haar d] u)
    {a b : ℝ} (hab : a < b) (hWr : ∀ x, W x ∈ Icc a b)
    {F : ℝ → ℝ} (hF : ContDiffOn ℝ ∞ F (Icc a b)) :
    IsWeakGradient (fun x => F (u x)) (fun x => derivWithin F (Icc a b) (u x) • g x) := by
  set F' : ℝ → ℝ := derivWithin F (Icc a b) with hF'
  have hFc : ContinuousOn F (Icc a b) := hF.continuousOn
  have hF'c : ContinuousOn F' (Icc a b) :=
    hF.continuousOn_derivWithin (uniqueDiffOn_Icc hab) (by simp)
  have hvu : ∀ n, SharpLSI.moll n u = SharpLSI.moll n W := fun n =>
    SharpLSI.moll_congr_ae n hWu.symm
  have hvs : ∀ n, IsSmoothPeriodic (SharpLSI.moll n u) := fun n =>
    isSmoothPeriodic_moll n (hg.memLp.integrable one_le_two)
  have hvr : ∀ n x, SharpLSI.moll n u x ∈ Icc a b := fun n x => by
    rw [hvu]; exact moll_mem_Icc hW hWr n x
  have huni : ∀ δ > 0, ∀ᶠ n in atTop, ∀ x, |SharpLSI.moll n u x - W x| ≤ δ := by
    intro δ hδ
    filter_upwards [SharpLSI.moll_uniform_of_continuous hW hδ] with n hn x
    rw [hvu n]
    simpa [Real.dist_eq] using hn x
  obtain ⟨C1, hC1⟩ := isCompact_Icc.exists_bound_of_continuousOn hF'c
  have hgj : ∀ k, MemLp (fun x => g x k) 2 (haar d) := memLp_coord hg.memLp_grad
  have hconv : ∀ j, Tendsto (fun n => ∫⁻ y, ‖SharpLSI.moll n (fun x => g x j) y - g y j‖ₑ ∂haar d)
      atTop (𝓝 0) := fun j => tendsto_lintegral_moll_sub (hgj j)
  have hmain : IsWeakGradient (fun x => F (W x)) (fun x => F' (W x) • g x) := by
    refine IsWeakGradient.of_tendsto_L1 (U := fun n x => F (SharpLSI.moll n u x))
      (G := fun n => smoothGrad (fun x => F (SharpLSI.moll n u x)))
      (memLp_two_of_continuous (hFc.comp_continuous hW hWr))
      (memLp_smul_top (memLp_top_of_continuous' (hF'c.comp_continuous hW hWr)) hg.memLp_grad)
      (fun n => (isSmoothPeriodic_comp (hvs n) hF (hvr n)).isWeakGradient) ?_ ?_
    · have := tendsto_lintegral_mul_of_unif (A := fun n x => F (SharpLSI.moll n u x))
        (B := fun x => F (W x)) (k := fun _ => 1) (integrable_const _)
        (unif_comp hFc hvr hWr huni)
      refine this.congr (fun n => ?_)
      simp
    · intro j
      have hk : Integrable (fun x => g x j) (haar d) := (hgj j).integrable one_le_two
      have h2 := tendsto_lintegral_mul_of_unif
        (A := fun n x => F' (SharpLSI.moll n u x)) (B := fun x => F' (W x)) hk
        (unif_comp hF'c hvr hWr huni)
      have h3 : Tendsto (fun n => ENNReal.ofReal C1 *
          ∫⁻ y, ‖SharpLSI.moll n (fun x => g x j) y - g y j‖ₑ ∂haar d
          + ∫⁻ y, ‖(F' (SharpLSI.moll n u y) - F' (W y)) * g y j‖ₑ ∂haar d) atTop (𝓝 0) := by
        have := (ENNReal.Tendsto.const_mul (hconv j)
          (Or.inr (ENNReal.ofReal_ne_top (r := C1)))).add h2
        simpa using this
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h3
        (fun n => zero_le) (fun n => ?_)
      have hmeas1 : AEMeasurable (fun y => ‖SharpLSI.moll n (fun x => g x j) y - g y j‖ₑ)
          (haar d) :=
        (((memLp_moll n one_le_two ENNReal.ofNat_ne_top (hgj j)).aestronglyMeasurable).sub
          (hgj j).aestronglyMeasurable).enorm
      calc ∫⁻ y, ‖smoothGrad (fun x => F (SharpLSI.moll n u x)) y j - (F' (W y) • g y) j‖ₑ ∂haar d
          ≤ ∫⁻ y, (ENNReal.ofReal C1 * ‖SharpLSI.moll n (fun x => g x j) y - g y j‖ₑ
              + ‖(F' (SharpLSI.moll n u y) - F' (W y)) * g y j‖ₑ) ∂haar d := by
            refine lintegral_mono fun y => ?_
            have e : smoothGrad (fun x => F (SharpLSI.moll n u x)) y j - (F' (W y) • g y) j
                = F' (SharpLSI.moll n u y) * (SharpLSI.moll n (fun x => g x j) y - g y j)
                  + (F' (SharpLSI.moll n u y) - F' (W y)) * g y j := by
              rw [smoothGrad_apply, coordPartial_comp (hvs n) hF (hvr n) j y,
                congrFun (coordPartial_moll hg n j) y]
              simp only [PiLp.smul_apply, smul_eq_mul]
              ring
            rw [e]
            refine (enorm_add_le _ _).trans (add_le_add ?_ le_rfl)
            rw [enorm_mul]
            gcongr
            rw [← ofReal_norm]
            exact ENNReal.ofReal_le_ofReal (hC1 _ (hvr n y))
        _ = _ := by
            rw [lintegral_add_left' (hmeas1.const_mul _), lintegral_const_mul' _ _
              ENNReal.ofReal_ne_top]
  refine hmain.congr_ae ?_ ?_
  · filter_upwards [hWu] with x hx; rw [hx]
  · filter_upwards [hWu] with x hx; rw [hx]


/-! ### One-dimensional consequences -/

theorem exists_ae_bound_one {u : Torus 1 → ℝ} {g : Torus 1 → Tangent 1}
    (hg : IsWeakGradient u g) : ∃ B : ℝ, 0 ≤ B ∧ ∀ᵐ x ∂haar 1, |u x| ≤ B := by
  obtain ⟨w, -, hae, -, hb⟩ := exists_continuous_rep_one hg
  refine ⟨(eLpNorm u 2 (haar 1)).toReal + (eLpNorm g 2 (haar 1)).toReal, by positivity, ?_⟩
  filter_upwards [hae] with x hx
  rw [← hx]
  exact hb x

/-- `d = 1`: `H¹ ↪ C^{0,1/2} ∩ L^∞`, with a continuous representative, explicit Hölder constant
`‖g‖₂` for the quotient distance and sup bound `‖u‖₂ + ‖g‖₂`. -/
theorem sobolev_embedding_dim_one {u : Torus 1 → ℝ} {g : Torus 1 → Tangent 1}
    (hg : IsWeakGradient u g) :
    ∃ w : Torus 1 → ℝ, Continuous w ∧ w =ᵐ[haar 1] u ∧
      (∀ x y, |w x - w y| ≤ (eLpNorm g 2 (haar 1)).toReal * Real.sqrt (torusDist x y)) ∧
      (∀ x, |w x| ≤ (eLpNorm u 2 (haar 1)).toReal + (eLpNorm g 2 (haar 1)).toReal) ∧
      MemLp u ⊤ (haar 1) := by
  obtain ⟨w, hc, hae, hh, hb⟩ := exists_continuous_rep_one hg
  refine ⟨w, hc, hae, fun x y => ?_, hb, ?_⟩
  · refine (Real.abs_le_sqrt (hh x y)).trans ?_
    rw [Real.sqrt_mul (torusDist_one_nonneg x y), Real.sqrt_sq ENNReal.toReal_nonneg, mul_comm]
  · refine memLp_top_of_bound hg.memLp.aestronglyMeasurable
      ((eLpNorm u 2 (haar 1)).toReal + (eLpNorm g 2 (haar 1)).toReal) ?_
    filter_upwards [hae] with x hx
    rw [Real.norm_eq_abs, ← hx]
    exact hb x

theorem rep_mem_Icc_one {W u : Torus 1 → ℝ} (hW : Continuous W) (hWu : W =ᵐ[haar 1] u) {a b : ℝ}
    (hu : ∀ᵐ x ∂haar 1, u x ∈ Icc a b) : ∀ x, W x ∈ Icc a b := by
  intro x
  by_contra hx
  have hopen : IsOpen (W ⁻¹' (Icc a b)ᶜ) := isClosed_Icc.isOpen_compl.preimage hW
  have hpos : 0 < haar 1 (W ⁻¹' (Icc a b)ᶜ) := hopen.measure_pos (haar 1) ⟨x, hx⟩
  have hae : ∀ᵐ y ∂haar 1, W y ∈ Icc a b := by
    filter_upwards [hWu, hu] with y h1 h2
    rwa [h1]
  exact absurd (ae_iff.mp hae) hpos.ne'

/-- Weak chain rule in `d = 1`. -/
theorem IsWeakGradient.comp_smooth_one {u : Torus 1 → ℝ} {g : Torus 1 → Tangent 1}
    (hg : IsWeakGradient u g) {a b : ℝ} (hab : a < b) (hu : ∀ᵐ x ∂haar 1, u x ∈ Icc a b)
    {F : ℝ → ℝ} (hF : ContDiffOn ℝ ∞ F (Icc a b)) :
    IsWeakGradient (fun x => F (u x)) (fun x => derivWithin F (Icc a b) (u x) • g x) := by
  obtain ⟨W, hWc, hWu, -, -⟩ := exists_continuous_rep_one hg
  exact chain_rule_of_cont_rep hg hWc hWu hab (rep_mem_Icc_one hWc hWu hu) hF

/-- `H¹(𝕋¹)` is an algebra. -/
theorem IsWeakGradient.mul_one_dim {u v : Torus 1 → ℝ} {g k : Torus 1 → Tangent 1}
    (hu : IsWeakGradient u g) (hv : IsWeakGradient v k) :
    IsWeakGradient (fun x => u x * v x) (fun x => v x • g x + u x • k x) := by
  obtain ⟨Bu, hBu0, hBu⟩ := exists_ae_bound_one hu
  obtain ⟨Bv, hBv0, hBv⟩ := exists_ae_bound_one hv
  set M := Bu + Bv + 1 with hMdef
  have hM : -M < M := by linarith
  have hF : ContDiffOn ℝ ∞ (fun s : ℝ => s ^ 2) (Icc (-M) M) := (contDiff_id.pow 2).contDiffOn
  have hd : ∀ s ∈ Icc (-M) M, derivWithin (fun s : ℝ => s ^ 2) (Icc (-M) M) s = 2 * s := by
    intro s hs
    have h : HasDerivAt (fun s : ℝ => s ^ 2) (2 * s) s := by simpa using hasDerivAt_pow 2 s
    exact h.hasDerivWithinAt.derivWithin (uniqueDiffOn_Icc hM s hs)
  have hp := hu.add hv
  have hm := hu.add (hv.smul (-1))
  have hpb : ∀ᵐ x ∂haar 1, u x + v x ∈ Icc (-M) M := by
    filter_upwards [hBu, hBv] with x h1 h2
    rw [abs_le] at h1 h2
    constructor <;> linarith
  have hmb : ∀ᵐ x ∂haar 1, u x + (-1) * v x ∈ Icc (-M) M := by
    filter_upwards [hBu, hBv] with x h1 h2
    rw [abs_le] at h1 h2
    constructor <;> linarith
  have hp2 := hp.comp_smooth_one hM hpb hF
  have hm2 := hm.comp_smooth_one hM hmb hF
  have H := (hp2.smul (1 / 4)).add (hm2.smul (-1 / 4))
  refine H.congr_ae (Eventually.of_forall fun x => by ring) ?_
  filter_upwards [hpb, hmb] with x h1 h2
  simp only [hd _ h1, hd _ h2]
  module

/-- Reciprocals of positive continuous `H¹` functions bounded away from zero. -/
theorem IsWeakGradient.inv_of_pos {u : Torus d → ℝ} {g : Torus d → Tangent d}
    (hg : IsWeakGradient u g) (hc : Continuous u) {c : ℝ} (hc0 : 0 < c) (hcu : ∀ x, c ≤ u x) :
    IsWeakGradient (fun x => (u x)⁻¹) (fun x => (-((u x) ^ 2)⁻¹) • g x) := by
  obtain ⟨M, hM⟩ := isCompact_univ.exists_bound_of_continuousOn hc.continuousOn
  have hab : c < max M c + 1 := by linarith [le_max_right M c]
  have hr : ∀ x, u x ∈ Icc c (max M c + 1) := fun x =>
    ⟨hcu x, by
      have := (le_abs_self (u x)).trans (by simpa using hM x (mem_univ x))
      linarith [le_max_left M c]⟩
  have hF : ContDiffOn ℝ ∞ (fun s : ℝ => s⁻¹) (Icc c (max M c + 1)) :=
    contDiffOn_id.inv (fun s hs => (lt_of_lt_of_le hc0 hs.1).ne')
  have hd : ∀ s ∈ Icc c (max M c + 1),
      derivWithin (fun s : ℝ => s⁻¹) (Icc c (max M c + 1)) s = -(s ^ 2)⁻¹ := by
    intro s hs
    exact (hasDerivAt_inv (lt_of_lt_of_le hc0 hs.1).ne').hasDerivWithinAt.derivWithin
      (uniqueDiffOn_Icc hab s hs)
  refine (chain_rule_of_cont_rep hg hc (Eventually.of_forall fun _ => rfl) hab hr hF).congr_ae
    (Eventually.of_forall fun _ => rfl) (Eventually.of_forall fun x => ?_)
  simp only [hd _ (hr x)]

/-! ### Entropy integrability -/

theorem integrable_sq_mul_log_sq_of_memH1 (d : ℕ) {u : Torus d → ℝ} (hu : MemH1 u) :
    Integrable (fun x => u x ^ 2 * Real.log (u x ^ 2)) (haar d) := by
  obtain ⟨g, hg⟩ := hu
  rcases (by omega : d = 0 ∨ d = 1 ∨ d = 2 ∨ 2 < d) with rfl | rfl | rfl | h
  · have hc : u = fun _ => u (fun i => i.elim0) := by
      funext x; congr 1; funext i; exact i.elim0
    have : MemLp u 3 (haar 0) := by rw [hc]; exact memLp_const _
    exact integrable_sq_mul_log_sq_of_memLp (by norm_num) (by simp) this
  · obtain ⟨w, -, -, -, -, hw⟩ := sobolev_embedding_dim_one hg
    exact integrable_sq_mul_log_sq_of_memLp (q := 3) (by norm_num) (by simp)
      (hw.mono_exponent le_top)
  · obtain ⟨C, hC⟩ := sobolev_embedding_dim_two (d := 2) rfl 3
    have := (hC u g hg).1
    exact integrable_sq_mul_log_sq_of_memLp (q := ((3 : ℝ≥0) : ℝ≥0∞)) (by norm_num) (by simp) this
  · obtain ⟨C, hC⟩ := sobolev_embedding_critical h
    have hd' : (2 : ℝ) < d := by exact_mod_cast h
    have hlt : (2 : ℝ) < 2 * d / (d - 2) := by
      rw [lt_div_iff₀ (by linarith)]; linarith
    refine integrable_sq_mul_log_sq_of_memLp ?_ ENNReal.ofReal_ne_top (hC u g hg).1
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp]
    exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 hlt

end DGPS

namespace DGPS.Analysis

open DGPS MeasureTheory
open scoped ENNReal NNReal ContDiff

/-- FOU006 canonical bundle. -/
theorem periodic_sobolev_embeddings_and_entropy_integrability :
    -- `d > 2`: `H¹ ↪ L^{2d/(d-2)}`
    (∀ d : ℕ, 2 < d → ∃ C : ℝ≥0, ∀ (u : Torus d → ℝ) (g : Torus d → Tangent d),
      IsWeakGradient u g →
        MemLp u (ENNReal.ofReal (2 * d / (d - 2))) (haar d) ∧
        eLpNorm u (ENNReal.ofReal (2 * d / (d - 2))) (haar d) ≤
          C * (eLpNorm u 2 (haar d) + eLpNorm g 2 (haar d))) ∧
    -- `d = 2`: `H¹ ↪ L^q` for every finite `q`
    (∀ d : ℕ, d = 2 → ∀ q : ℝ≥0, ∃ C : ℝ≥0, ∀ (u : Torus d → ℝ) (g : Torus d → Tangent d),
      IsWeakGradient u g →
        MemLp u (q : ℝ≥0∞) (haar d) ∧
        eLpNorm u (q : ℝ≥0∞) (haar d) ≤ C * (eLpNorm u 2 (haar d) + eLpNorm g 2 (haar d))) ∧
    -- `d = 1`: continuous representative, Hölder-1/2 and sup bounds
    (∀ (u : Torus 1 → ℝ) (g : Torus 1 → Tangent 1), IsWeakGradient u g →
      ∃ w : Torus 1 → ℝ, Continuous w ∧ w =ᵐ[haar 1] u ∧
        (∀ x y, |w x - w y| ≤ (eLpNorm g 2 (haar 1)).toReal * Real.sqrt (torusDist x y)) ∧
        (∀ x, |w x| ≤ (eLpNorm u 2 (haar 1)).toReal + (eLpNorm g 2 (haar 1)).toReal) ∧
        MemLp u ⊤ (haar 1)) ∧
    -- entropy integrability
    (∀ (d : ℕ) (u : Torus d → ℝ), MemH1 u →
      Integrable (fun x => u x ^ 2 * Real.log (u x ^ 2)) (haar d)) ∧
    -- `d = 1`: algebra
    (∀ (u v : Torus 1 → ℝ) (g k : Torus 1 → Tangent 1), IsWeakGradient u g →
      IsWeakGradient v k →
      IsWeakGradient (fun x => u x * v x) (fun x => v x • g x + u x • k x)) ∧
    -- `d = 1`: weak chain rule
    (∀ (u : Torus 1 → ℝ) (g : Torus 1 → Tangent 1), IsWeakGradient u g →
      ∀ a b : ℝ, a < b → (∀ᵐ x ∂haar 1, u x ∈ Set.Icc a b) →
      ∀ F : ℝ → ℝ, ContDiffOn ℝ ∞ F (Set.Icc a b) →
      IsWeakGradient (fun x => F (u x))
        (fun x => derivWithin F (Set.Icc a b) (u x) • g x)) ∧
    -- reciprocals of positive continuous `H¹` functions bounded away from zero
    (∀ (d : ℕ) (u : Torus d → ℝ) (g : Torus d → Tangent d), IsWeakGradient u g →
      Continuous u → ∀ c : ℝ, 0 < c → (∀ x, c ≤ u x) →
      IsWeakGradient (fun x => (u x)⁻¹) (fun x => (-((u x) ^ 2)⁻¹) • g x)) :=
  ⟨fun _ hd => sobolev_embedding_critical hd,
   fun _ hd q => sobolev_embedding_dim_two hd q,
   fun _ _ hg => sobolev_embedding_dim_one hg,
   fun d _ hu => integrable_sq_mul_log_sq_of_memH1 d hu,
   fun _ _ _ _ hu hv => hu.mul_one_dim hv,
   fun _ _ hg _ _ hab hu _ hF => hg.comp_smooth_one hab hu hF,
   fun _ _ _ hg hc _ hc0 hcu => hg.inv_of_pos hc hc0 hcu⟩

end DGPS.Analysis
