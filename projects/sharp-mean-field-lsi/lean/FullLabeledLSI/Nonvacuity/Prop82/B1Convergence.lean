import FullLabeledLSI.Nonvacuity.Prop82.Subthreshold
import SharpSymmetricLSI.Paper.CosineDissipation
import SharpSymmetricLSI.Paper.CircleNear

/-!
# Lane B, module 1: convergence of moments, force energy and entropy

Generic dominated convergence lemmas for a sequence of densities that is
uniformly bounded and converges almost everywhere, together with the closed
forms of `firstMode` and `forceEnergy` in terms of finitely many moments.
-/

open MeasureTheory InformationTheory Filter Topology
open scoped ENNReal Real

namespace SharpLSI.FL.Prop82

attribute [local fun_prop] SharpLSI.continuous_sCos

/-! ### Moments -/

/-- `∫ F ρ` against the density. -/
noncomputable def mom (F : Torus 1 → Real) (rho : Torus 1 → Real) : Real :=
  ∫ x, F x * rho x ∂haar 1

theorem integrable_mom {rho F : Torus 1 → Real} (hi : Integrable rho (haar 1))
    (hF : Continuous F) {M : Real} (hb : ∀ x, |F x| ≤ M) :
    Integrable (fun x => F x * rho x) (haar 1) :=
  Integrable.mono' (hi.norm.const_mul M) (hF.aestronglyMeasurable.mul hi.aestronglyMeasurable)
    (Eventually.of_forall fun x => by
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hb x) (abs_nonneg _))

theorem abs_gCos_sq_le (x : Torus 1) : |gCos x ^ 2| ≤ 1 := by
  rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) (abs_gCos_le x)

theorem abs_sCos_sq_le (x : Torus 1) : |sCos x ^ 2| ≤ 1 := by
  rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) (abs_sCos_le x)

theorem abs_sCos_mul_gCos_le (x : Torus 1) : |sCos x * gCos x| ≤ 1 := by
  rw [abs_mul]
  nlinarith [abs_sCos_le x, abs_gCos_le x, abs_nonneg (sCos x), abs_nonneg (gCos x)]

theorem firstMode_eq_mom {rho : Torus 1 → Real} (hi : Integrable rho (haar 1)) :
    firstMode rho = mom gCos rho ^ 2 + mom sCos rho ^ 2 :=
  firstMode_eq hi

/-- The weak derivative of the mean-field potential. -/
theorem weakGrad_gConv_ae {rho : Torus 1 → Real} (h1 : ∫ x, rho x ∂haar 1 = 1) :
    ∀ᵐ x ∂haar 1, weakGrad (gConv rho) x 0 =
      2 * π * (-(mom gCos rho) * sCos x + mom sCos rho * gCos x) := by
  have hG1 : ContDiff ℝ 1 (gConv rho ∘ liftT) := (contDiff_gConv_lift h1).of_le le_top
  filter_upwards [weakGrad_ae_eq_of_contDiff hG1] with x hx
  rw [hx]
  simp only
  rw [gConv_lift h1, fderiv_trig_lift, ← gCos_secT, ← sCos_secT]
  rfl

theorem forceEnergy_eq_mom {rho : Torus 1 → Real} (h1 : ∫ x, rho x ∂haar 1 = 1) :
    forceEnergy rho =
      aCos * (mom gCos rho ^ 2 * mom (fun x => sCos x ^ 2) rho
        - 2 * (mom gCos rho * mom sCos rho) * mom (fun x => sCos x * gCos x) rho
        + mom sCos rho ^ 2 * mom (fun x => gCos x ^ 2) rho) := by
  have hi := integrable_of_integral_eq_one h1
  set C := mom gCos rho
  set S := mom sCos rho
  have i1 := integrable_mom hi (F := fun x => sCos x ^ 2) (by fun_prop) abs_sCos_sq_le
  have i2 := integrable_mom hi (F := fun x => sCos x * gCos x) (by fun_prop)
    abs_sCos_mul_gCos_le
  have i3 := integrable_mom hi (F := fun x => gCos x ^ 2) (by fun_prop) abs_gCos_sq_le
  unfold forceEnergy
  have h : ∫ x, rho x * weakGrad (gConv rho) x 0 ^ 2 ∂haar 1 =
      ∫ x, aCos * (C ^ 2 * (sCos x ^ 2 * rho x)
        - 2 * (C * S) * ((sCos x * gCos x) * rho x) + S ^ 2 * (gCos x ^ 2 * rho x)) ∂haar 1 := by
    refine integral_congr_ae ?_
    filter_upwards [weakGrad_gConv_ae h1] with x hx
    rw [hx]
    unfold aCos
    ring
  rw [h, integral_const_mul]
  congr 1
  rw [integral_add (f := fun x => C ^ 2 * (sCos x ^ 2 * rho x)
      - 2 * (C * S) * ((sCos x * gCos x) * rho x))
    (g := fun x => S ^ 2 * (gCos x ^ 2 * rho x))
    ((i1.const_mul _).sub (i2.const_mul _)) (i3.const_mul _),
    integral_sub (f := fun x => C ^ 2 * (sCos x ^ 2 * rho x))
    (g := fun x => 2 * (C * S) * ((sCos x * gCos x) * rho x))
    (i1.const_mul _) (i2.const_mul _), integral_const_mul, integral_const_mul,
    integral_const_mul]
  rfl

/-! ### Dominated convergence for density sequences -/

/-- A uniformly bounded sequence of probability densities converging a.e. -/
structure DensConv (rho : ℕ → Torus 1 → Real) (rhoInf : Torus 1 → Real) (B : Real) : Prop where
  nonneg : ∀ n x, 0 ≤ rho n x
  mass : ∀ n, ∫ x, rho n x ∂haar 1 = 1
  bound : ∀ n, ∀ᵐ x ∂haar 1, rho n x ≤ B
  tendsto : ∀ᵐ x ∂haar 1, Tendsto (fun n => rho n x) atTop (𝓝 (rhoInf x))

namespace DensConv

variable {rho : ℕ → Torus 1 → Real} {rhoInf : Torus 1 → Real} {B : Real}

theorem bound' (h : DensConv rho rhoInf B) : ∀ᵐ x ∂haar 1, ∀ n, rho n x ≤ B :=
  ae_all_iff.mpr h.bound

theorem inf_nonneg (h : DensConv rho rhoInf B) : ∀ᵐ x ∂haar 1, 0 ≤ rhoInf x := by
  filter_upwards [h.tendsto] with x hx
  exact ge_of_tendsto' hx fun n => h.nonneg n x

theorem inf_le (h : DensConv rho rhoInf B) : ∀ᵐ x ∂haar 1, rhoInf x ≤ B := by
  filter_upwards [h.tendsto, h.bound'] with x hx hb
  exact le_of_tendsto' hx hb

theorem aesm_inf (h : DensConv rho rhoInf B) : AEStronglyMeasurable rhoInf (haar 1) :=
  aestronglyMeasurable_of_tendsto_ae atTop
    (fun n => (integrable_of_integral_eq_one (h.mass n)).aestronglyMeasurable) h.tendsto

theorem tendsto_mom (h : DensConv rho rhoInf B) {F : Torus 1 → Real} (hF : Continuous F)
    {M : Real} (hb : ∀ x, |F x| ≤ M) :
    Tendsto (fun n => mom F (rho n)) atTop (𝓝 (mom F rhoInf)) := by
  unfold mom
  refine tendsto_integral_of_dominated_convergence (fun _ => M * B) (fun n => ?_)
    (integrable_const _) (fun n => ?_) ?_
  · exact (hF.aestronglyMeasurable.mul
      (integrable_of_integral_eq_one (h.mass n)).aestronglyMeasurable)
  · filter_upwards [h.bound n] with x hx
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (h.nonneg n x)]
    exact mul_le_mul (hb x) hx (h.nonneg n x) ((abs_nonneg _).trans (hb x))
  · filter_upwards [h.tendsto] with x hx
    exact hx.const_mul _

theorem mass_inf (h : DensConv rho rhoInf B) : ∫ x, rhoInf x ∂haar 1 = 1 := by
  have := h.tendsto_mom (F := fun _ => 1) continuous_const (M := 1) (fun x => by simp)
  simp only [mom, one_mul, h.mass] at this
  exact tendsto_nhds_unique this tendsto_const_nhds

theorem integrable_inf (h : DensConv rho rhoInf B) : Integrable rhoInf (haar 1) :=
  integrable_of_integral_eq_one h.mass_inf

theorem tendsto_firstMode (h : DensConv rho rhoInf B) :
    Tendsto (fun n => firstMode (rho n)) atTop (𝓝 (firstMode rhoInf)) := by
  have hC := h.tendsto_mom continuous_gCos abs_gCos_le
  have hS := h.tendsto_mom continuous_sCos abs_sCos_le
  rw [firstMode_eq_mom h.integrable_inf]
  have := (hC.pow 2).add (hS.pow 2)
  refine this.congr fun n => ?_
  rw [firstMode_eq_mom (integrable_of_integral_eq_one (h.mass n))]

theorem tendsto_forceEnergy (h : DensConv rho rhoInf B) :
    Tendsto (fun n => forceEnergy (rho n)) atTop (𝓝 (forceEnergy rhoInf)) := by
  have hC := h.tendsto_mom continuous_gCos abs_gCos_le
  have hS := h.tendsto_mom continuous_sCos abs_sCos_le
  have h1 := h.tendsto_mom (F := fun x => sCos x ^ 2) (by fun_prop) abs_sCos_sq_le
  have h2 := h.tendsto_mom (F := fun x => sCos x * gCos x) (by fun_prop) abs_sCos_mul_gCos_le
  have h3 := h.tendsto_mom (F := fun x => gCos x ^ 2) (by fun_prop) abs_gCos_sq_le
  rw [forceEnergy_eq_mom h.mass_inf]
  have := (((hC.pow 2).mul h1).sub (((hC.mul hS).const_mul 2).mul h2)).add ((hS.pow 2).mul h3)
  refine (this.const_mul aCos).congr fun n => ?_
  rw [forceEnergy_eq_mom (h.mass n)]

end DensConv

/-! ### Entropy -/

theorem entropy_eq_integral {rho : Torus 1 → Real} (h0 : ∀ x, 0 ≤ rho x)
    (h1 : ∫ x, rho x ∂haar 1 = 1) : entropy rho = ∫ x, klFun (rho x) ∂haar 1 := by
  have hi := integrable_of_integral_eq_one h1
  have hmeas : AEStronglyMeasurable (fun x => klFun (rho x)) (haar 1) :=
    continuous_klFun.comp_aestronglyMeasurable hi.aestronglyMeasurable
  unfold entropy
  rw [klDiv_densMeasure h0 h1, integral_eq_lintegral_of_nonneg_ae
    (Eventually.of_forall fun x => klFun_nonneg (h0 x)) hmeas]

theorem DensConv.tendsto_entropy {rho : ℕ → Torus 1 → Real} {rhoInf : Torus 1 → Real}
    {B : Real} (h : DensConv rho rhoInf B)
    (h0 : ∀ x, 0 ≤ rhoInf x) :
    Tendsto (fun n => entropy (rho n)) atTop (𝓝 (entropy rhoInf)) := by
  rw [entropy_eq_integral h0 h.mass_inf]
  have hB0 : ∀ n, ∀ᵐ x ∂haar 1, 0 ≤ B := fun n => by
    filter_upwards [h.bound n] with x hx
    exact (h.nonneg n x).trans hx
  have hK : ∀ n, ∀ᵐ x ∂haar 1, klFun (rho n x) ≤ (B + 1) ^ 2 := fun n => by
    filter_upwards [h.bound n] with x hx
    exact klFun_le_bound (h.nonneg n x) hx
  have : (fun n => entropy (rho n)) = fun n => ∫ x, klFun (rho n x) ∂haar 1 := by
    funext n; exact entropy_eq_integral (h.nonneg n) (h.mass n)
  rw [this]
  refine tendsto_integral_of_dominated_convergence (fun _ => (B + 1) ^ 2) (fun n => ?_)
    (integrable_const _) (fun n => ?_) ?_
  · exact continuous_klFun.comp_aestronglyMeasurable
      (integrable_of_integral_eq_one (h.mass n)).aestronglyMeasurable
  · filter_upwards [hK n] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (klFun_nonneg (h.nonneg n x))]
    exact hx
  · filter_upwards [h.tendsto] with x hx
    exact (continuous_klFun.tendsto _).comp hx

/-! ### A.e. convergent subsequence from `L²` convergence -/

theorem exists_ae_subseq_of_L2 {f : ℕ → Torus 1 → Real} {u : Torus 1 → Real}
    (hf : ∀ n, MemLp (f n) 2 (haar 1)) (hu : MemLp u 2 (haar 1))
    (h : Tendsto (fun n => ∫ x, (f n x - u x) ^ 2 ∂haar 1) atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ᵐ x ∂haar 1, Tendsto (fun n => f (φ n) x) atTop (𝓝 (u x)) := by
  have he : Tendsto (fun n => eLpNorm (f n - u) 2 (haar 1)) atTop (𝓝 0) := by
    have key : ∀ n, eLpNorm (f n - u) 2 (haar 1) =
        ENNReal.ofReal (Real.sqrt (∫ x, (f n x - u x) ^ 2 ∂haar 1)) := by
      intro n
      have hm := (hf n).sub hu
      rw [hm.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
      congr 1
      rw [Real.sqrt_eq_rpow]
      simp only [ENNReal.toReal_ofNat, Pi.sub_apply, Real.norm_eq_abs]
      norm_num
    simp_rw [key]
    have := ((Real.continuous_sqrt.tendsto 0).comp h)
    rw [Real.sqrt_zero] at this
    simpa using ENNReal.tendsto_ofReal this
  exact (tendstoInMeasure_of_tendsto_eLpNorm two_ne_zero he).exists_seq_tendsto_ae

end SharpLSI.FL.Prop82
