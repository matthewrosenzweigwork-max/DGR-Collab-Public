import DGPS.Foundations.WeakContractions
import DGPS.Foundations.WeakSobolev
import DGPS.Foundations.SmoothingLp
import DGPS.Foundations.PeriodicSmoothing

/-!
# Lipschitz representatives and `W^{1,∞}` (LIP001)

On the flat unit torus `𝕋^d`, a function is Lipschitz for the Euclidean quotient distance iff it
has an `L^∞` weak gradient (`IsWeakGradientLp ∞`), the continuous representative is unique, and
the essential supremum of the Euclidean norm of the weak gradient is the Lipschitz constant.
Main export: `DGPS.Lipschitz.lipschitz_representative_and_weak_gradient`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal ContDiff

namespace DGPS.Lipschitz

variable {d : ℕ}

/-- Cauchy–Schwarz for the Euclidean tangent norm. -/
theorem abs_sum_mul_le (w : Fin d → ℝ) (v : Tangent d) :
    |∑ j, w j * v j| ≤ Real.sqrt (∑ j, w j ^ 2) * ‖v‖ := by
  have h := abs_real_inner_le_norm (WithLp.toLp 2 w : Tangent d) v
  have e1 : ‖(WithLp.toLp 2 w : Tangent d)‖ = Real.sqrt (∑ j, w j ^ 2) := by
    rw [EuclideanSpace.norm_eq]; simp
  have e2 : inner ℝ (WithLp.toLp 2 w : Tangent d) v = ∑ j, w j * v j := by
    simp [PiLp.inner_apply, mul_comm]
  rwa [e1, e2] at h

theorem moll_dir_bound (n : ℕ) {g : Torus d → Tangent d} {M : ℝ} (hg : MemLp g ∞ (haar d))
    (hM : ∀ᵐ y ∂haar d, ‖g y‖ ≤ M) (w : Fin d → ℝ) (x : Torus d) :
    |∑ j, w j * SharpLSI.moll n (fun y => g y j) x| ≤ M * Real.sqrt (∑ j, w j ^ 2) := by
  set a := SharpLSI.secT x with ha
  set F : Fin d → (Fin d → ℝ) → ℝ := fun j t => g (torusLift t) j with hF
  have hint : ∀ j, Integrable (fun t => F j t * SharpLSI.phiSeq n (a - t)) := by
    intro j
    have hl : LocallyIntegrable (F j) (volume : Measure (Fin d → ℝ)) :=
      SharpLSI.locallyIntegrable_comp_liftT
        (u := fun y => g y j) (((memLp_coord_of_memLp hg j).integrable (by simp)))
    have := (SharpLSI.hasCompactSupport_phiSeq (ι := Fin d) n).convolutionExists_right
      (ContinuousLinearMap.mul ℝ ℝ) hl (contDiff_phiSeq n).continuous a
    simpa [MeasureTheory.ConvolutionExistsAt] using this
  have hm : ∀ j, SharpLSI.moll n (fun y => g y j) x = ∫ t, F j t * SharpLSI.phiSeq n (a - t) := by
    intro j
    rfl
  simp_rw [hm]
  have key : ∑ j, w j * ∫ t, F j t * SharpLSI.phiSeq n (a - t)
      = ∫ t, (∑ j, w j * F j t) * SharpLSI.phiSeq n (a - t) := by
    simp_rw [← integral_const_mul]
    rw [← integral_finsetSum _ (fun j _ => (hint j).const_mul (w j))]
    congr 1; funext t
    rw [Finset.sum_mul]; simp_rw [mul_assoc]
  rw [key]
  have hφ1 : ∫ t : Fin d → ℝ, SharpLSI.phiSeq n (a - t) = 1 := by
    rw [integral_sub_left_eq_self (fun t => SharpLSI.phiSeq n t) volume a]
    exact integral_phiSeq n
  have hφi : Integrable (fun t : Fin d → ℝ => SharpLSI.phiSeq n (a - t)) :=
    (integrable_phiSeq n).comp_sub_left a
  have hae : ∀ᵐ t ∂(volume : Measure (Fin d → ℝ)), ‖g (torusLift t)‖ ≤ M :=
    SharpLSI.ae_liftT_of_ae hM
  have hle := norm_integral_le_of_norm_le (f := fun t => (∑ j, w j * F j t) * SharpLSI.phiSeq n (a - t))
    (g := fun t => (M * Real.sqrt (∑ j, w j ^ 2)) * SharpLSI.phiSeq n (a - t))
    (hφi.const_mul _) (by
      filter_upwards [hae] with t ht
      rw [norm_mul, Real.norm_of_nonneg (phiSeq_nonneg n _)]
      refine mul_le_mul_of_nonneg_right ?_ (phiSeq_nonneg n _)
      rw [Real.norm_eq_abs]
      refine (abs_sum_mul_le w (g (torusLift t))).trans ?_
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right ht (Real.sqrt_nonneg _))
  rw [integral_const_mul, hφ1, mul_one] at hle
  simpa using hle


/-- Shortest lifts: any two points of the torus have lifts within half a period per coordinate,
and the quotient distance is the Euclidean length of the displacement. -/
theorem exists_short_lift (x y : Torus d) :
    ∃ a δ : Fin d → ℝ, torusLift a = x ∧ torusLift (a + δ) = y ∧
      torusDist x y = Real.sqrt (∑ j, δ j ^ 2) := by
  set a := SharpLSI.secT x with ha
  set r : Fin d → ℝ := fun j => SharpLSI.secT y j - a j with hr
  set δ : Fin d → ℝ := fun j => r j - round (r j) with hδ
  have h1 : torusLift a = x := SharpLSI.liftT_secT x
  have hδ2 : ∀ j, |δ j| ≤ 1 / 2 := fun j => abs_sub_round (r j)
  have h2 : torusLift (a + δ) = y := by
    funext j
    have hy : ((SharpLSI.secT y j : ℝ) : UnitAddCircle) = y j := by
      have := congrFun (SharpLSI.liftT_secT y) j
      simpa [SharpLSI.liftT] using this
    have hz : ((round (r j) : ℝ) : UnitAddCircle) = 0 :=
      (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr ⟨round (r j), by simp⟩
    show (((a + δ) j : ℝ) : UnitAddCircle) = y j
    rw [← hy]
    have : (a + δ) j = SharpLSI.secT y j - round (r j) := by
      simp only [Pi.add_apply, hδ, hr]; ring
    rw [this, AddCircle.coe_sub, hz, sub_zero]
  refine ⟨a, δ, h1, h2, ?_⟩
  rw [← h1, ← h2, torusDist_metric.2.1]
  rw [torusDist_liftT_eq (x := a + δ) (y := a) (fun j => by simpa using hδ2 j)]
  simp

theorem torusLipschitz_of_smooth {v : Torus d → ℝ} (hv : IsSmoothPeriodic v) {M : ℝ}
    (hb : ∀ (x : Torus d) (w : Fin d → ℝ),
      |∑ j, w j * coordPartial j v x| ≤ M * Real.sqrt (∑ j, w j ^ 2)) :
    TorusLipschitzWith M v := by
  intro x y
  obtain ⟨a, δ, ha, hy, hd⟩ := exists_short_lift x y
  set h : ℝ → ℝ := fun t => (v ∘ torusLift) (a + t • δ) with hh
  have hdiff : Differentiable ℝ (v ∘ torusLift) := hv.differentiable (by simp)
  have hder : ∀ t : ℝ, HasDerivAt h (fderiv ℝ (v ∘ torusLift) (a + t • δ) δ) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => a + t • δ) δ t := by
      simpa using ((hasDerivAt_id t).smul_const δ).const_add a
    have h2 := (hdiff (a + t • δ)).hasFDerivAt.comp_hasDerivAt t h1
    exact h2
  have hδsum : ∀ z : Fin d → ℝ, fderiv ℝ (v ∘ torusLift) z δ
      = ∑ j, δ j * coordPartial j v (torusLift z) := by
    intro z
    have e : δ = ∑ j, δ j • (Pi.single j (1 : ℝ) : Fin d → ℝ) := by
      ext i; simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [e]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, smul_eq_mul]
    congr 1
    exact (congrFun (coordPartial_comp_torusLift j v) z).symm
  have hbd : ∀ t : ℝ, ‖fderiv ℝ (v ∘ torusLift) (a + t • δ) δ‖ ≤ M * Real.sqrt (∑ j, δ j ^ 2) := by
    intro t
    rw [hδsum, Real.norm_eq_abs]
    exact hb _ δ
  have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (s := univ)
    (f := h) (f' := fun t => fderiv ℝ (v ∘ torusLift) (a + t • δ) δ)
    (fun t _ => (hder t).hasDerivWithinAt) (fun t _ => hbd t) convex_univ
    (mem_univ 0) (mem_univ 1)
  have e0 : h 0 = v x := by simp [hh, ← ha]
  have e1 : h 1 = v y := by simp [hh, ← hy]
  rw [e0, e1] at hmv
  rw [hd, abs_sub_comm]
  simpa [Real.norm_eq_abs] using hmv


theorem torusLipschitz_continuous {v : Torus d → ℝ} {M : ℝ} (hv : TorusLipschitzWith M v) :
    Continuous v := by
  have key : ∀ x y, dist (v x) (v y) ≤ (|M| * Real.sqrt d) * dist x y := by
    intro x y
    rw [Real.dist_eq]
    calc |v x - v y| ≤ M * torusDist x y := hv x y
      _ ≤ |M| * torusDist x y := mul_le_mul_of_nonneg_right (le_abs_self M)
            (by
              have := (torusDist_comparison x y).1
              exact (dist_nonneg).trans this)
      _ ≤ |M| * (Real.sqrt d * dist x y) :=
            mul_le_mul_of_nonneg_left (torusDist_comparison x y).2 (abs_nonneg M)
      _ = _ := by ring
  exact (LipschitzWith.of_dist_le_mul (K := ⟨|M| * Real.sqrt d, by positivity⟩) key).continuous

theorem exists_lipschitz_limit {w : ℕ → Torus d → ℝ} {u : Torus d → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hw : ∀ k, TorusLipschitzWith M (w k))
    (hconv : ∀ᵐ x ∂haar d, Tendsto (fun k => w k x) atTop (𝓝 (u x))) :
    ∃ v : Torus d → ℝ, Continuous v ∧ v =ᵐ[haar d] u ∧ TorusLipschitzWith M v := by
  have hdense : Dense {x | Tendsto (fun k => w k x) atTop (𝓝 (u x))} :=
    Measure.dense_of_ae (μ := haar d) hconv
  have hex : ∀ x, ∃ l, Tendsto (fun k => w k x) atTop (𝓝 l) := by
    intro x
    refine cauchySeq_tendsto_of_complete (Metric.cauchySeq_iff'.mpr fun ε hε => ?_)
    set δ : ℝ := ε / (4 * (M + 1)) with hδ
    have hδpos : 0 < δ := by positivity
    have hx : x ∈ closure {x | Tendsto (fun k => w k x) atTop (𝓝 (u x))} := hdense.closure_eq ▸ mem_univ x
    obtain ⟨y, hy, hxy⟩ := (mem_closure_iff_nhds_basis (torusDist_metric.2.2.2.2 x)).mp hx δ hδpos
    have hyc := (hy.cauchySeq)
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff'.mp hyc (ε / 2) (by positivity)
    refine ⟨N, fun n hn => ?_⟩
    have h1 : |w n x - w n y| ≤ M * δ := (hw n x y).trans
      (mul_le_mul_of_nonneg_left (le_of_lt (show torusDist x y < δ from hxy)) hM)
    have h2 : |w N x - w N y| ≤ M * δ := (hw N x y).trans
      (mul_le_mul_of_nonneg_left (le_of_lt (show torusDist x y < δ from hxy)) hM)
    have h3 := hN n hn
    rw [Real.dist_eq] at h3 ⊢
    have h4 : M * δ ≤ ε / 4 := by
      rw [hδ]
      have : M * (ε / (4 * (M + 1))) = ε / 4 * (M / (M + 1)) := by field_simp
      rw [this]
      have : M / (M + 1) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
      nlinarith
    calc |w n x - w N x| = |(w n x - w n y) + (w n y - w N y) + (w N y - w N x)| := by ring_nf
      _ ≤ |w n x - w n y| + |w n y - w N y| + |w N y - w N x| := by
          refine (abs_add_le _ _).trans ?_
          gcongr
          exact abs_add_le _ _
      _ < ε := by rw [abs_sub_comm (w N y)] ; linarith
  choose v hv using hex
  have hlip : TorusLipschitzWith M v := by
    intro x y
    refine le_of_tendsto ((hv x).sub (hv y)).abs ?_
    exact Eventually.of_forall fun k => hw k x y
  refine ⟨v, torusLipschitz_continuous hlip, ?_, hlip⟩
  filter_upwards [hconv] with x hx
  exact tendsto_nhds_unique (hv x) hx



theorem exists_lipschitz_rep {u : Torus d → ℝ} {g : Torus d → Tangent d}
    (hg : IsWeakGradientLp ∞ u g) {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ᵐ y ∂haar d, ‖g y‖ ≤ M) :
    ∃ v : Torus d → ℝ, Continuous v ∧ v =ᵐ[haar d] u ∧ TorusLipschitzWith M v := by
  have hu2 : MemLp u 2 (haar d) := hg.memLp.mono_exponent le_top
  have hu1 : Integrable u (haar d) := hg.memLp.integrable (by simp)
  have hlip : ∀ n, TorusLipschitzWith M (SharpLSI.moll n u) := by
    intro n
    refine torusLipschitz_of_smooth (isSmoothPeriodic_moll n hu1) fun x w => ?_
    simp_rw [hg.coordPartial_moll (by simp) n]
    exact moll_dir_bound n hg.memLp_grad hM w x
  have hT := tendsto_eLpNorm_moll_sub (p := 2) one_le_two ENNReal.ofNat_ne_top hu2
  have hTM : TendstoInMeasure (haar d) (fun n => SharpLSI.moll n u) atTop u :=
    tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (by simp) hT
  obtain ⟨ns, hns, hae⟩ := hTM.exists_seq_tendsto_ae
  exact exists_lipschitz_limit hM0 (w := fun k => SharpLSI.moll (ns k) u) (fun k => hlip _) hae


/-! ### Direction A: from a Lipschitz function to a weak gradient -/

theorem fderiv_apply_eq_sum (f : (Fin d → ℝ) → ℝ) (z δ : Fin d → ℝ) :
    fderiv ℝ f z δ = ∑ j, δ j * fderiv ℝ f z (Pi.single j 1) := by
  have e : δ = ∑ j, δ j • (Pi.single j (1 : ℝ) : Fin d → ℝ) := by
    ext i; simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [e]
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, smul_eq_mul]

theorem lift_lipschitz {u : Torus d → ℝ} {L : ℝ} (hL : 0 ≤ L) (hu : TorusLipschitzWith L u)
    (a b : Fin d → ℝ) :
    |u (torusLift a) - u (torusLift b)| ≤ L * Real.sqrt (∑ j, (a j - b j) ^ 2) :=
  (hu _ _).trans (mul_le_mul_of_nonneg_left (torusDist_liftT_le a b) hL)

theorem tendsto_slope_line {F : (Fin d → ℝ) → ℝ} {z : Fin d → ℝ}
    (hF : DifferentiableAt ℝ F z) (w : Fin d → ℝ) :
    Tendsto (fun s : ℝ => s⁻¹ * (F (z + s • w) - F z)) (𝓝[≠] 0) (𝓝 (fderiv ℝ F z w)) := by
  have h1 : HasDerivAt (fun t : ℝ => z + t • w) w 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add z
  have h2 : HasDerivAt (fun t : ℝ => F (z + t • w)) (fderiv ℝ F z w) 0 := by
    have hF' : HasFDerivAt F (fderiv ℝ F z) (z + (0 : ℝ) • w) := by simpa using hF.hasFDerivAt
    exact hF'.comp_hasDerivAt (0 : ℝ) h1
  have := (hasDerivAt_iff_tendsto_slope_zero.mp h2)
  simpa using this

theorem fderiv_line_bound {u : Torus d → ℝ} {L : ℝ} (hL : 0 ≤ L) (hu : TorusLipschitzWith L u)
    {z : Fin d → ℝ} (hz : DifferentiableAt ℝ (u ∘ torusLift) z) (w : Fin d → ℝ) :
    |fderiv ℝ (u ∘ torusLift) z w| ≤ L * Real.sqrt (∑ j, w j ^ 2) := by
  have h1 : HasDerivAt (fun t : ℝ => z + t • w) w 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add z
  have h2 : HasDerivAt (fun t : ℝ => (u ∘ torusLift) (z + t • w))
      (fderiv ℝ (u ∘ torusLift) z w) 0 := by
    have hz' : HasFDerivAt (u ∘ torusLift) (fderiv ℝ (u ∘ torusLift) z) (z + (0 : ℝ) • w) := by
      simpa using hz.hasFDerivAt
    exact hz'.comp_hasDerivAt (0 : ℝ) h1
  have := norm_deriv_le_of_lip' (f := fun t : ℝ => (u ∘ torusLift) (z + t • w)) (x₀ := 0)
    (C := L * Real.sqrt (∑ j, w j ^ 2)) (by positivity) (Eventually.of_forall fun t => by
      have := lift_lipschitz hL hu (z + t • w) z
      simp only [Function.comp, zero_smul, add_zero, sub_zero, Real.norm_eq_abs]
      refine this.trans (le_of_eq ?_)
      have e : ∀ j, (z + t • w) j - z j = t * w j := fun j => by simp
      simp_rw [e, mul_pow]
      rw [← Finset.mul_sum, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]
      ring)
  rw [h2.deriv] at this
  simpa using this


theorem lipschitzWith_lift {u : Torus d → ℝ} {L : ℝ} (hL : 0 ≤ L) (hu : TorusLipschitzWith L u) :
    LipschitzWith ⟨L * Real.sqrt d, by positivity⟩ (u ∘ torusLift) := by
  refine LipschitzWith.of_dist_le_mul fun a b => ?_
  rw [Real.dist_eq, dist_eq_norm]
  refine (lift_lipschitz hL hu a b).trans ?_
  show _ ≤ L * Real.sqrt d * ‖a - b‖
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hL
  calc Real.sqrt (∑ j, (a j - b j) ^ 2) ≤ Real.sqrt (d * ‖a - b‖ ^ 2) := by
        apply Real.sqrt_le_sqrt
        calc ∑ j, (a j - b j) ^ 2 ≤ ∑ _j : Fin d, ‖a - b‖ ^ 2 := by
              refine Finset.sum_le_sum fun j _ => ?_
              have : |a j - b j| ≤ ‖a - b‖ := by
                simpa [Real.norm_eq_abs] using norm_le_pi_norm (a - b) j
              calc (a j - b j) ^ 2 = |a j - b j| ^ 2 := (sq_abs _).symm
                _ ≤ _ := pow_le_pow_left₀ (abs_nonneg _) this 2
          _ = d * ‖a - b‖ ^ 2 := by simp
    _ = Real.sqrt d * ‖a - b‖ := by
        rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq (norm_nonneg _)]

theorem ae_differentiableAt_secT {u : Torus d → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hu : TorusLipschitzWith L u) :
    ∀ᵐ x ∂haar d, DifferentiableAt ℝ (u ∘ torusLift) (SharpLSI.secT x) :=
  SharpLSI.quasiMeasurePreserving_secT.ae (lipschitzWith_lift hL hu).ae_differentiableAt

theorem measurable_coordPartial {u : Torus d → ℝ} (j : Fin d) : Measurable (coordPartial j u) :=
  (measurable_fderiv_apply_const ℝ (u ∘ torusLift) (Pi.single j 1)).comp SharpLSI.measurable_secT

theorem measurable_smoothGrad {u : Torus d → ℝ} : Measurable (smoothGrad u) :=
  (PiLp.continuous_toLp 2 _).measurable.comp (Measurable.of_eval fun j => measurable_coordPartial j)

theorem ae_norm_smoothGrad_le {u : Torus d → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hu : TorusLipschitzWith L u) : ∀ᵐ x ∂haar d, ‖smoothGrad u x‖ ≤ L := by
  filter_upwards [ae_differentiableAt_secT hL hu] with x hx
  have h := fderiv_line_bound hL hu hx (fun j => coordPartial j u x)
  rw [fderiv_apply_eq_sum] at h
  have e1 : ∑ j, coordPartial j u x * fderiv ℝ (u ∘ torusLift) (SharpLSI.secT x) (Pi.single j 1)
      = ‖smoothGrad u x‖ ^ 2 := by
    rw [tangent_norm_sq]; simp [coordPartial, sq]
  have e2 : Real.sqrt (∑ j, coordPartial j u x ^ 2) = ‖smoothGrad u x‖ := by
    have : ∑ j, coordPartial j u x ^ 2 = ‖smoothGrad u x‖ ^ 2 := by
      rw [tangent_norm_sq]; rfl
    rw [this, Real.sqrt_sq (norm_nonneg _)]
  rw [e1, e2, abs_of_nonneg (sq_nonneg _)] at h
  rcases (norm_nonneg (smoothGrad u x)).eq_or_lt with h0 | h0
  · rw [← h0]; exact hL
  · nlinarith



theorem exists_bound_continuous {ψ : Torus d → ℝ} (hψ : Continuous ψ) :
    ∃ C, ∀ x, |ψ x| ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_univ (X := Torus d)).exists_bound_of_continuousOn hψ.continuousOn
  exact ⟨C, fun x => by simpa using hC x (Set.mem_univ x)⟩

theorem torusLift_add (a b : Fin d → ℝ) : torusLift (a + b) = torusLift a + torusLift b := by
  ext j; simp [torusLift, SharpLSI.liftT]

/-- Translation of the torus by the lift of `s • eⱼ`. -/
theorem lift_line_bound {f : Torus d → ℝ} {L : ℝ} (hL : 0 ≤ L) (hf : TorusLipschitzWith L f)
    (z : Fin d → ℝ) (j : Fin d) (s : ℝ) :
    |f (torusLift (z + s • Pi.single j 1)) - f (torusLift z)| ≤ L * |s| := by
  refine (lift_lipschitz hL hf _ _).trans (le_of_eq ?_)
  have e : ∀ i, (z + s • (Pi.single j (1 : ℝ) : Fin d → ℝ)) i - z i
      = s * (Pi.single j (1 : ℝ) : Fin d → ℝ) i := fun i => by simp
  simp_rw [e, mul_pow]
  rw [← Finset.mul_sum]
  have : ∑ i, ((Pi.single j (1 : ℝ) : Fin d → ℝ) i) ^ 2 = 1 := by
    simp [Pi.single_apply]
  rw [this, mul_one, Real.sqrt_sq_eq_abs]

theorem shift_bound {f : Torus d → ℝ} {L : ℝ} (hL : 0 ≤ L) (hf : TorusLipschitzWith L f)
    (x : Torus d) (j : Fin d) {s : ℝ} (hs : s ≠ 0) :
    |s⁻¹ * (f (x + torusLift (s • Pi.single j 1)) - f x)| ≤ L := by
  have h := lift_line_bound hL hf (SharpLSI.secT x) j s
  have e : torusLift (SharpLSI.secT x) = x := SharpLSI.liftT_secT x
  rw [torusLift_add, e] at h
  rw [abs_mul, abs_inv]
  have hs' : 0 < |s| := abs_pos.mpr hs
  rw [inv_mul_le_iff₀ hs']
  linarith [mul_comm L |s|]

theorem tendsto_shift_quot {f : Torus d → ℝ} (j : Fin d) (x : Torus d)
    (hx : DifferentiableAt ℝ (f ∘ torusLift) (SharpLSI.secT x)) :
    Tendsto (fun s : ℝ => s⁻¹ * (f (x + torusLift (s • Pi.single j 1)) - f x)) (𝓝[≠] 0)
      (𝓝 (coordPartial j f x)) := by
  refine (tendsto_slope_line hx (Pi.single j 1)).congr fun s => ?_
  simp only [Function.comp_apply, torusLift_add, SharpLSI.liftT_secT]

theorem torusLift_neg_smul (s : ℝ) (j : Fin d) :
    torusLift ((-s) • (Pi.single j (1 : ℝ) : Fin d → ℝ)) = -torusLift (s • Pi.single j 1) := by
  ext i; simp [torusLift, SharpLSI.liftT]

theorem continuous_shift (τ : Torus d) : Continuous fun x : Torus d => x + τ :=
  continuous_id.add continuous_const

theorem exists_smooth_lipschitz {φ : Torus d → ℝ} (hφ : IsSmoothPeriodic φ) :
    ∃ M, 0 ≤ M ∧ TorusLipschitzWith M φ := by
  obtain ⟨B, hB⟩ := exists_bound_continuous (hφ.continuous_smoothGrad.norm)
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  refine ⟨B, hB0, torusLipschitz_of_smooth hφ fun x w => ?_⟩
  have h := abs_sum_mul_le w (smoothGrad φ x)
  have h2 : ‖smoothGrad φ x‖ ≤ B := (le_abs_self _).trans (hB x)
  simp only [smoothGrad_apply] at h
  calc _ ≤ _ := h
    _ ≤ Real.sqrt (∑ j, w j ^ 2) * B := mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg _)
    _ = _ := mul_comm _ _

theorem ibp_lipschitz {u : Torus d → ℝ} {L : ℝ} (hL : 0 ≤ L) (hu : TorusLipschitzWith L u)
    {φ : Torus d → ℝ} (hφ : IsSmoothPeriodic φ) (j : Fin d) :
    ∫ x, u x * coordPartial j φ x ∂haar d = -∫ x, coordPartial j u x * φ x ∂haar d := by
  have huc : Continuous u := torusLipschitz_continuous hu
  have hφc : Continuous φ := hφ.continuous_torus
  obtain ⟨Cu, hCu⟩ := exists_bound_continuous huc
  obtain ⟨Cφ, hCφ⟩ := exists_bound_continuous hφc
  obtain ⟨M, hM0, hM⟩ := exists_smooth_lipschitz hφ
  set τ : ℝ → Torus d := fun s => torusLift (s • Pi.single j 1) with hτ
  -- the two families
  let E : ℝ → Torus d → ℝ := fun s x => u x * (s⁻¹ * (φ (x + τ s) - φ x))
  let D : ℝ → Torus d → ℝ := fun s x => (s⁻¹ * (u (x + τ s) - u x)) * φ x
  have hEc : ∀ s, Continuous (E s) := fun s => by
    have := continuous_shift (τ s)
    simp only [E]; fun_prop
  have hDc : ∀ s, Continuous (D s) := fun s => by
    have := continuous_shift (τ s)
    simp only [D]; fun_prop
  have hEl : Tendsto (fun s => ∫ x, E s x ∂haar d) (𝓝[≠] 0)
      (𝓝 (∫ x, u x * coordPartial j φ x ∂haar d)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => Cu * M) ?_ ?_
      (integrable_const _) ?_
    · exact Eventually.of_forall fun s => (hEc s).aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with s hs
      refine Eventually.of_forall fun x => ?_
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul ((hCu x)) (shift_bound hM0 hM x j hs) (abs_nonneg _)
        ((abs_nonneg _).trans (hCu x))
    · refine Eventually.of_forall fun x => ?_
      exact (tendsto_shift_quot (f := φ) j x
        (hφ.differentiable (by simp) _)).const_mul (u x)
  have hDl : Tendsto (fun s => ∫ x, D (-s) x ∂haar d) (𝓝[≠] 0)
      (𝓝 (∫ x, coordPartial j u x * φ x ∂haar d)) := by
    have hneg : Tendsto (fun s : ℝ => -s) (𝓝[≠] 0) (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · simpa using (continuous_neg.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with s hs
        simpa using hs
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => L * Cφ) ?_ ?_
      (integrable_const _) ?_
    · exact Eventually.of_forall fun s => (hDc (-s)).aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with s hs
      refine Eventually.of_forall fun x => ?_
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (shift_bound hL hu x j (neg_ne_zero.mpr hs)) (hCφ x) (abs_nonneg _) hL
    · filter_upwards [ae_differentiableAt_secT hL hu] with x hx
      exact ((tendsto_shift_quot (f := u) j x hx).comp hneg).mul_const (φ x)
  have heq : ∀ s : ℝ, ∫ x, E s x ∂haar d = -∫ x, D (-s) x ∂haar d := by
    intro s
    have hτn : τ (-s) = -τ s := torusLift_neg_smul s j
    have hint : ∀ {f : Torus d → ℝ}, Continuous f → Integrable f (haar d) := fun {f} hf =>
      hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)
    have c1 := continuous_shift (τ s)
    have c2 := continuous_shift (τ (-s))
    have I1 : Integrable (fun x => u x * φ (x + τ s)) (haar d) := hint (by fun_prop)
    have I2 : Integrable (fun x => u x * φ x) (haar d) := hint (by fun_prop)
    have I3 : Integrable (fun x => u (x + τ (-s)) * φ x) (haar d) := hint (by fun_prop)
    have hE : ∫ x, E s x ∂haar d
        = s⁻¹ * (∫ x, u x * φ (x + τ s) ∂haar d - ∫ x, u x * φ x ∂haar d) := by
      rw [← integral_sub I1 I2, ← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only [E]; ring
    have hD : ∫ x, D (-s) x ∂haar d
        = (-s)⁻¹ * (∫ x, u (x + τ (-s)) * φ x ∂haar d - ∫ x, u x * φ x ∂haar d) := by
      rw [← integral_sub I3 I2, ← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only [D]; ring
    have hA : ∫ x, u (x + τ (-s)) * φ x ∂haar d = ∫ x, u x * φ (x + τ s) ∂haar d := by
      have := integral_sub_right_eq_self (μ := haar d) (fun y => u y * φ (y + τ s)) (τ s)
      simp only [sub_add_cancel] at this
      rw [← this]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only [hτn, ← sub_eq_add_neg]
    rw [hE, hD, hA, inv_neg]; ring
  have hEl' : Tendsto (fun s => ∫ x, E s x ∂haar d) (𝓝[≠] 0)
      (𝓝 (-∫ x, coordPartial j u x * φ x ∂haar d)) := by
    simp_rw [heq]; exact hDl.neg
  exact tendsto_nhds_unique hEl hEl'

theorem exists_weak_gradient {u : Torus d → ℝ} {L : ℝ} (hL : 0 ≤ L) (hu : TorusLipschitzWith L u) :
    IsWeakGradientLp ∞ u (smoothGrad u) ∧ ∀ᵐ x ∂haar d, ‖smoothGrad u x‖ ≤ L := by
  have huc : Continuous u := torusLipschitz_continuous hu
  obtain ⟨Cu, hCu⟩ := exists_bound_continuous huc
  have hb := ae_norm_smoothGrad_le hL hu
  refine ⟨⟨memLp_top_of_bound huc.aestronglyMeasurable Cu
      (Eventually.of_forall fun x => by simpa using hCu x),
    memLp_top_of_bound measurable_smoothGrad.aestronglyMeasurable L hb, ?_⟩, hb⟩
  intro φ hφ j
  exact ibp_lipschitz hL hu hφ j

theorem continuous_ae_eq {v w : Torus d → ℝ} (hv : Continuous v) (hw : Continuous w)
    (h : v =ᵐ[haar d] w) : v = w :=
  (Continuous.ae_eq_iff_eq (haar d) hv hw).mp h

theorem ae_norm_le_toReal {g : Torus d → Tangent d} (hg : MemLp g ∞ (haar d)) :
    ∀ᵐ x ∂haar d, ‖g x‖ ≤ (eLpNorm g ∞ (haar d)).toReal := by
  have hfin : eLpNorm g ∞ (haar d) ≠ ⊤ := hg.eLpNorm_lt_top.ne
  have h := ae_le_eLpNormEssSup (f := g) (μ := haar d)
  rw [← eLpNorm_exponent_top hg.aestronglyMeasurable] at h
  filter_upwards [h] with x hx
  rw [← ofReal_norm] at hx
  exact (ENNReal.ofReal_le_iff_le_toReal hfin).mp hx

theorem ae_grad_bound_of_lipschitz {u : Torus d → ℝ} {g : Torus d → Tangent d}
    (hg : IsWeakGradientLp ∞ u g) {L : ℝ} (hL : 0 ≤ L) (hu : TorusLipschitzWith L u) :
    ∀ᵐ x ∂haar d, ‖g x‖ ≤ L := by
  obtain ⟨hg', hb⟩ := exists_weak_gradient hL hu
  have h2 : IsWeakGradient u g := isWeakGradient_iff_isWeakGradientLp.mpr
    ⟨hg.memLp.mono_exponent (by simp), hg.memLp_grad.mono_exponent (by simp), hg.ibp⟩
  have h2' : IsWeakGradient u (smoothGrad u) := isWeakGradient_iff_isWeakGradientLp.mpr
    ⟨hg'.memLp.mono_exponent (by simp), hg'.memLp_grad.mono_exponent (by simp), hg'.ibp⟩
  filter_upwards [h2.ae_eq h2', hb] with x hx hb'
  rw [hx]; exact hb'

/-- **LIP001.** Lipschitz representatives and `W^{1,∞}` on the flat unit torus. -/
theorem lipschitz_representative_and_weak_gradient (d : ℕ) :
    (∀ u : Torus d → ℝ, ∀ L : ℝ, 0 ≤ L → TorusLipschitzWith L u →
      ∃ g : Torus d → Tangent d, IsWeakGradientLp ∞ u g ∧ ∀ᵐ x ∂haar d, ‖g x‖ ≤ L) ∧
    (∀ (u : Torus d → ℝ) (g : Torus d → Tangent d), IsWeakGradientLp ∞ u g →
      ∃ v : Torus d → ℝ, Continuous v ∧ v =ᵐ[haar d] u ∧
        TorusLipschitzWith (eLpNorm g ∞ (haar d)).toReal v) ∧
    (∀ (u : Torus d → ℝ) (g : Torus d → Tangent d), Continuous u → IsWeakGradientLp ∞ u g →
      ∀ L : ℝ, 0 ≤ L → (TorusLipschitzWith L u ↔ ∀ᵐ x ∂haar d, ‖g x‖ ≤ L)) ∧
    (∀ v w : Torus d → ℝ, Continuous v → Continuous w → v =ᵐ[haar d] w → v = w) ∧
    (∀ (u : Torus d → ℝ) (g : Torus d → Tangent d), Continuous u → IsWeakGradientLp ∞ u g →
      eLpNorm g ∞ (haar d) = ⨅ (L : ℝ≥0) (_ : TorusLipschitzWith (L : ℝ) u), (L : ℝ≥0∞)) := by
  have part3 : ∀ (u : Torus d → ℝ) (g : Torus d → Tangent d), Continuous u →
      IsWeakGradientLp ∞ u g → ∀ L : ℝ, 0 ≤ L →
      (TorusLipschitzWith L u ↔ ∀ᵐ x ∂haar d, ‖g x‖ ≤ L) := by
    intro u g hc hg L hL
    refine ⟨fun hu => ae_grad_bound_of_lipschitz hg hL hu, fun hb => ?_⟩
    obtain ⟨v, hvc, hvu, hv⟩ := exists_lipschitz_rep hg hL hb
    rw [← continuous_ae_eq hvc hc hvu]
    exact hv
  refine ⟨fun u L hL hu => ⟨smoothGrad u, exists_weak_gradient hL hu⟩, ?_, part3,
    fun v w hv hw h => continuous_ae_eq hv hw h, ?_⟩
  · intro u g hg
    exact exists_lipschitz_rep hg ENNReal.toReal_nonneg (ae_norm_le_toReal hg.memLp_grad)
  · intro u g hc hg
    have hfin : eLpNorm g ∞ (haar d) ≠ ⊤ := hg.memLp_grad.eLpNorm_lt_top.ne
    apply le_antisymm
    · refine le_iInf fun L => le_iInf fun hL => ?_
      rw [eLpNorm_exponent_top hg.memLp_grad.aestronglyMeasurable]
      have := (part3 u g hc hg L L.2).mp hL
      exact eLpNormEssSup_le_of_ae_bound this |>.trans (by simp)
    · have hM := (part3 u g hc hg _ ENNReal.toReal_nonneg).mpr (ae_norm_le_toReal hg.memLp_grad)
      refine (iInf₂_le (eLpNorm g ∞ (haar d)).toReal.toNNReal ?_).trans ?_
      · rw [Real.coe_toNNReal _ ENNReal.toReal_nonneg]; exact hM
      · have e : (eLpNorm g ⊤ (haar d)).toReal.toNNReal = (eLpNorm g ⊤ (haar d)).toNNReal :=
          Real.toNNReal_coe
        rw [e, ENNReal.coe_toNNReal hfin]

end DGPS.Lipschitz
