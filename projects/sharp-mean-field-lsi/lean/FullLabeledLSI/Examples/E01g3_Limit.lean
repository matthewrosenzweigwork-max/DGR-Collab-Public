import FullLabeledLSI.Examples.E01g3_Apriori
import FullLabeledLSI.Examples.E01g2_Compact

/-!
# Lane D, Task C (E01g3): passage to the limit of entropy, interaction and dissipation

(`DensConv` and its entropy lemma are adapted from Prop 8.2 lane B, `B1Convergence.lean`, via lane C's
`Sec9DeficitCompact.lean`; attribution: copied/adapted.)
-/

open MeasureTheory InformationTheory Filter Topology
open scoped Real ENNReal ContDiff

namespace SharpLSI.FL.Ex.LaneD

open SharpLSI

theorem klDiv_toReal_eq_integral {ρ : Torus 1 → ℝ} (h0 : ∀ x, 0 ≤ ρ x)
    (h1 : ∫ x, ρ x ∂haar 1 = 1) :
    (klDiv (densMeasure ρ) (haar 1)).toReal = ∫ x, klFun (ρ x) ∂haar 1 := by
  have hi := integrable_of_integral_eq_one' h1
  have hmeas : AEStronglyMeasurable (fun x => klFun (ρ x)) (haar 1) :=
    continuous_klFun.comp_aestronglyMeasurable hi.aestronglyMeasurable
  rw [klDiv_densMeasure' h0 h1, integral_eq_lintegral_of_nonneg_ae
    (Eventually.of_forall fun x => klFun_nonneg (h0 x)) hmeas]

theorem klFun_le_bound' {x B : ℝ} (hx : 0 ≤ x) (hB : x ≤ B) : klFun x ≤ B ^ 2 + 1 := by
  have h1 : klFun x ≤ (x - 1) ^ 2 := by
    rw [klFun_apply]
    rcases hx.eq_or_lt with h | h
    · rw [← h]; simp
    · have := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos h) hx
      nlinarith
  nlinarith

/-- A uniformly bounded sequence of probability densities converging pointwise. -/
structure DensConv (rho : ℕ → Torus 1 → Real) (rhoInf : Torus 1 → Real) (B : Real) : Prop where
  nonneg : ∀ n x, 0 ≤ rho n x
  mass : ∀ n, ∫ x, rho n x ∂haar 1 = 1
  bound : ∀ n x, rho n x ≤ B
  tendsto : ∀ x, Tendsto (fun n => rho n x) atTop (𝓝 (rhoInf x))

namespace DensConv

variable {rho : ℕ → Torus 1 → Real} {rhoInf : Torus 1 → Real} {B : Real}

theorem tendsto_mom (h : DensConv rho rhoInf B) {F : Torus 1 → Real} (hF : Continuous F)
    {M : Real} (hb : ∀ x, |F x| ≤ M) :
    Tendsto (fun n => ∫ x, F x * rho n x ∂haar 1) atTop (𝓝 (∫ x, F x * rhoInf x ∂haar 1)) := by
  refine tendsto_integral_of_dominated_convergence (fun _ => M * B) (fun n => ?_)
    (integrable_const _) (fun n => ?_) ?_
  · exact (hF.aestronglyMeasurable.mul
      (integrable_of_integral_eq_one (h.mass n)).aestronglyMeasurable)
  · refine Eventually.of_forall fun x => ?_
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (h.nonneg n x)]
    exact mul_le_mul (hb x) (h.bound n x) (h.nonneg n x) ((abs_nonneg _).trans (hb x))
  · exact Eventually.of_forall fun x => (h.tendsto x).const_mul _

theorem mass_inf (h : DensConv rho rhoInf B) : ∫ x, rhoInf x ∂haar 1 = 1 := by
  have := h.tendsto_mom (F := fun _ => 1) continuous_const (M := 1) (fun x => by simp)
  simp only [one_mul, h.mass] at this
  exact tendsto_nhds_unique this tendsto_const_nhds

theorem inf_nonneg (h : DensConv rho rhoInf B) (x : Torus 1) : 0 ≤ rhoInf x :=
  ge_of_tendsto' (h.tendsto x) fun n => h.nonneg n x

theorem tendsto_entropy (h : DensConv rho rhoInf B) :
    Tendsto (fun n => entR (rho n)) atTop (𝓝 (entR rhoInf)) := by
  unfold entR
  rw [klDiv_toReal_eq_integral h.inf_nonneg h.mass_inf]
  have : (fun n => (klDiv (densMeasure (rho n)) (haar 1)).toReal) =
      fun n => ∫ x, klFun (rho n x) ∂haar 1 := by
    funext n; exact klDiv_toReal_eq_integral (h.nonneg n) (h.mass n)
  rw [this]
  refine tendsto_integral_of_dominated_convergence (fun _ => B ^ 2 + 1) (fun n => ?_)
    (integrable_const _) (fun n => ?_) ?_
  · exact continuous_klFun.comp_aestronglyMeasurable
      (integrable_of_integral_eq_one (h.mass n)).aestronglyMeasurable
  · refine Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (klFun_nonneg (h.nonneg n x))]
    exact klFun_le_bound' (h.nonneg n x) (h.bound n x)
  · exact Eventually.of_forall fun x => (continuous_klFun.tendsto _).comp (h.tendsto x)

/-- `g * ρ_n → g * ρ_∞` pointwise, for a continuous kernel. -/
theorem tendsto_convT (h : DensConv rho rhoInf B) {g : Torus 1 → ℝ} (hg : Continuous g) {M : ℝ}
    (hM : ∀ z, |g z| ≤ M) (x : Torus 1) :
    Tendsto (fun n => convT g (rho n) x) atTop (𝓝 (convT g rhoInf x)) :=
  h.tendsto_mom (F := fun y => g (x - y)) (hg.comp (continuous_sub_left x)) (M := M)
    (fun y => hM _)

/-- `⟨ρ_n, C*ρ_n⟩ → ⟨ρ_∞, C*ρ_∞⟩`. -/
theorem tendsto_cqR (h : DensConv rho rhoInf B) {C : Torus 1 → ℝ} (hC : GoodKernel C) :
    Tendsto (fun n => cqR C (rho n)) atTop (𝓝 (cqR C rhoInf)) := by
  have hCc := continuous_of_smooth hC.smooth
  obtain ⟨M, hM0⟩ := (isCompact_univ (X := Torus 1)).exists_bound_of_continuousOn hCc.continuousOn
  have hM : ∀ z, |C z| ≤ M := fun z => by simpa using hM0 z (Set.mem_univ _)
  have hcc : ∀ n, Continuous (convT C (rho n)) := fun n => by
    haveI := isProbabilityMeasure_densMeasure' (h.nonneg n) (h.mass n)
    have : IsSmoothT (convT C (rho n)) := by
      rw [convT_eq_conv (h.nonneg n) (h.mass n)]; exact isSmoothT_conv hC.smooth _
    exact continuous_of_smooth this
  unfold cqR
  refine tendsto_integral_of_dominated_convergence (fun _ => B * M) (fun n => ?_)
    (integrable_const _) (fun n => ?_) ?_
  · exact (integrable_of_integral_eq_one (h.mass n)).aestronglyMeasurable.mul
      (hcc n).aestronglyMeasurable
  · refine Eventually.of_forall fun x => ?_
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (h.nonneg n x)]
    exact mul_le_mul (h.bound n x) (abs_convT_le hCc hM (h.nonneg n) (h.mass n) x)
      (abs_nonneg _) ((h.nonneg n x).trans (h.bound n x))
  · exact Eventually.of_forall fun x => (h.tendsto x).mul (h.tendsto_convT hCc hM x)

end DensConv

theorem memLp_mul_cont {f b : Torus 1 → ℝ} (hf : MemLp f 2 (haar 1)) (hb : Continuous b) :
    MemLp (fun x => f x * b x) 2 (haar 1) := by
  obtain ⟨M, hM⟩ := (isCompact_univ (X := Torus 1)).exists_bound_of_continuousOn hb.continuousOn
  have hbm : MemLp b ⊤ (haar 1) :=
    MemLp.of_bound hb.aestronglyMeasurable M (Eventually.of_forall fun x => by
      simpa using hM x (Set.mem_univ _))
  have := hbm.mul hf (r := 2)
  refine this.ae_eq (Eventually.of_forall fun x => ?_)
  simp only [Pi.mul_apply]; ring

theorem continuous_convT_dT {C : Torus 1 → ℝ} (hC : GoodKernel C) {ρ : Torus 1 → ℝ}
    (h0 : ∀ x, 0 ≤ ρ x) (h1 : ∫ x, ρ x ∂haar 1 = 1) : Continuous (convT (dT C) ρ) := by
  haveI := isProbabilityMeasure_densMeasure' h0 h1
  have : IsSmoothT (convT (dT C) ρ) := by
    rw [convT_eq_conv h0 h1]; exact isSmoothT_conv (isSmoothT_dT hC.smooth) _
  exact continuous_of_smooth this

/-- Lower semicontinuity of the dissipation along a sequence converging as in `h1_unif_compact`. -/
theorem DR_lsc {C : Torus 1 → ℝ} (hC : GoodKernel C) {ρ : ℕ → Torus 1 → ℝ} {f : Torus 1 → ℝ}
    {B : ℝ} (hρ : DensConv ρ (fun x => f x ^ 2) B) (hf0 : ∀ x, 0 ≤ f x)
    (hfH : MemH1 (haar 1) f) (hH : ∀ n, MemH1 (haar 1) (fun x => Real.sqrt (ρ n x)))
    (hweak : ∀ g : Torus 1 → ℝ, MemLp g 2 (haar 1) →
      Tendsto (fun n => ∫ x, weakGrad (fun y => Real.sqrt (ρ n y)) x 0 * g x ∂haar 1) atTop
        (𝓝 (∫ x, weakGrad f x 0 * g x ∂haar 1)))
    {Lim : ℝ} (hD : Tendsto (fun n => DR C (ρ n)) atTop (𝓝 Lim)) :
    DR C (fun x => f x ^ 2) ≤ Lim := by
  have hc1 := continuous_of_smooth (isSmoothT_dT hC.smooth)
  obtain ⟨M, hM0⟩ := (isCompact_univ (X := Torus 1)).exists_bound_of_continuousOn hc1.continuousOn
  have hM : ∀ z, |dT C z| ≤ M := fun z => by simpa using hM0 z (Set.mem_univ _)
  have hmassInf := hρ.mass_inf
  have hnnInf : ∀ x, 0 ≤ f x ^ 2 := fun x => sq_nonneg _
  set v : ℕ → Torus 1 → ℝ := fun n x => 2 * weakGrad (fun y => Real.sqrt (ρ n y)) x 0 -
    Real.sqrt (ρ n x) * convT (dT C) (ρ n) x with hv
  set vInf : Torus 1 → ℝ := fun x => 2 * weakGrad f x 0 - f x * convT (dT C) (fun y => f y ^ 2) x
    with hvInf
  have hvL : ∀ n, MemLp (v n) 2 (haar 1) := fun n =>
    ((memLp_weakGrad_zero (hH n)).const_mul 2).sub
      (memLp_mul_cont (hH n).2.1 (continuous_convT_dT hC (hρ.nonneg n) (hρ.mass n)))
  have hvInfL : MemLp vInf 2 (haar 1) :=
    ((memLp_weakGrad_zero hfH).const_mul 2).sub
      (memLp_mul_cont hfH.2.1 (continuous_convT_dT hC hnnInf hmassInf))
  have hweakv : ∀ g : Torus 1 → ℝ, MemLp g 2 (haar 1) →
      Tendsto (fun n => ∫ x, v n x * g x ∂haar 1) atTop (𝓝 (∫ x, vInf x * g x ∂haar 1)) := by
    intro g hg
    have hgi : Integrable g (haar 1) := hg.integrable one_le_two
    have iw : ∀ n, Integrable (fun x => weakGrad (fun y => Real.sqrt (ρ n y)) x 0 * g x) (haar 1) :=
      fun n => integrable_mul_of_memLp_two (memLp_weakGrad_zero (hH n)) hg
    have ib : ∀ n, Integrable (fun x => Real.sqrt (ρ n x) * convT (dT C) (ρ n) x * g x) (haar 1) :=
      fun n => integrable_mul_of_memLp_two
        (memLp_mul_cont (hH n).2.1 (continuous_convT_dT hC (hρ.nonneg n) (hρ.mass n))) hg
    have e1 : ∀ n, ∫ x, v n x * g x ∂haar 1 =
        2 * ∫ x, weakGrad (fun y => Real.sqrt (ρ n y)) x 0 * g x ∂haar 1 -
          ∫ x, Real.sqrt (ρ n x) * convT (dT C) (ρ n) x * g x ∂haar 1 := by
      intro n
      rw [← integral_const_mul, ← integral_sub ((iw n).const_mul 2) (ib n)]
      congr 1; funext x; simp only [hv]; ring
    have e2 : ∫ x, vInf x * g x ∂haar 1 =
        2 * ∫ x, weakGrad f x 0 * g x ∂haar 1 -
          ∫ x, f x * convT (dT C) (fun y => f y ^ 2) x * g x ∂haar 1 := by
      have iw' : Integrable (fun x => weakGrad f x 0 * g x) (haar 1) :=
        integrable_mul_of_memLp_two (memLp_weakGrad_zero hfH) hg
      have ib' : Integrable (fun x => f x * convT (dT C) (fun y => f y ^ 2) x * g x) (haar 1) :=
        integrable_mul_of_memLp_two
          (memLp_mul_cont hfH.2.1 (continuous_convT_dT hC hnnInf hmassInf)) hg
      rw [← integral_const_mul, ← integral_sub (iw'.const_mul 2) ib']
      congr 1; funext x; simp only [hvInf]; ring
    simp_rw [e1, e2]
    refine ((hweak g hg).const_mul 2).sub ?_
    have hB0 : 0 ≤ B := (hρ.nonneg 0 0).trans (hρ.bound 0 0)
    refine tendsto_integral_of_dominated_convergence
      (fun x => Real.sqrt B * M * |g x|) (fun n => (ib n).aestronglyMeasurable) (hgi.abs.const_mul _)
      (fun n => Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_)
    · have hb := abs_convT_le hc1 hM (hρ.nonneg n) (hρ.mass n) x
      rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _)]
      have hs : Real.sqrt (ρ n x) ≤ Real.sqrt B := Real.sqrt_le_sqrt (hρ.bound n x)
      calc Real.sqrt (ρ n x) * |convT (dT C) (ρ n) x| * |g x| ≤ Real.sqrt B * M * |g x| := by
            refine mul_le_mul (mul_le_mul hs hb (abs_nonneg _) (Real.sqrt_nonneg _)) le_rfl
              (abs_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) ((abs_nonneg _).trans (hM 0)))
        _ = _ := rfl
    · have h1 : Tendsto (fun n => Real.sqrt (ρ n x)) atTop (𝓝 (f x)) := by
        have := (Real.continuous_sqrt.tendsto (f x ^ 2)).comp (hρ.tendsto x)
        rwa [Real.sqrt_sq (hf0 x)] at this
      exact (h1.mul (hρ.tendsto_convT hc1 hM x)).mul_const _
  have hlim := sq_integral_le_of_weak_tendsto hvL hvInfL hweakv hD
  have hfun : (fun y => Real.sqrt (f y ^ 2)) = f := funext fun y => Real.sqrt_sq (hf0 y)
  have : DR C (fun x => f x ^ 2) = ∫ x, vInf x ^ 2 ∂haar 1 := by
    unfold DR; rw [hfun]
    congr 1; funext x; simp only [hvInf, Real.sqrt_sq (hf0 x)]
  rw [this]
  exact hlim

end SharpLSI.FL.Ex.LaneD
