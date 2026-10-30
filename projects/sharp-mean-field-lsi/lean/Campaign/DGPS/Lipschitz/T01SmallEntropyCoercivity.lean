import DGPS.Lipschitz.T01EntropyCoercivity
import SharpSymmetricLSI.Paper.Coercivity3

/-!
# Small-entropy coercivity for the actual centered kernel

The finite-rank/Pinsker/entropy-duality proof reuses the assumption-free analytic machinery
of the older Coercivity1--3 files. Its kernel and equilibrium inputs here are current campaign
objects. No semiconvex `Hyp` is assumed or constructed.
-/

noncomputable section
open MeasureTheory InformationTheory Filter Real BoundedContinuousFunction
open scoped ENNReal

namespace DGPS.Lipschitz

open SharpLSI

variable {d : ℕ}

/-- Full support of a minimizing Gibbs law makes the continuous L² pairing definite. -/
theorem t01_bcf_eq_zero_of_sq (A : InteractionData d)
    {μ : ProbabilityMeasure (Torus d)} (hμ : freeEnergy A μ = freeEnergyMinimum A)
    (u : Torus d →ᵇ ℝ) (h0 : ∫ x, u x * u x ∂(μ : Measure (Torus d)) = 0) : u = 0 := by
  have hae : (fun x => u x * u x) =ᵐ[(μ : Measure (Torus d))] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun x => mul_self_nonneg _) ((u * u).integrable _)).mp h0
  have hac : haar d ≪ (μ : Measure (Torus d)) := by
    rw [DGPS.Structural.minimizer_eq_frozenGibbs A hμ]
    exact (frozenGibbs A μ).haar_ac_measure
  have heq := (Continuous.ae_eq_iff_eq (μ := haar d)
    (u.continuous.mul u.continuous) continuous_const).mp (hac.ae_le hae)
  ext x
  exact mul_self_eq_zero.mp (congrFun heq x)

/-- The centered product correction is the quadratic form of the signed probability difference. -/
theorem t01_two_correction_eq_bForm (A : InteractionData d)
    (μ ρ : ProbabilityMeasure (Torus d)) :
    2 * t01CenteredCorrection A μ ρ =
      SharpLSI.bForm (centeredKernel A (μ : Measure (Torus d)))
        (μ : Measure (Torus d)) (ρ : Measure (Torus d)) := by
  let K := centeredKernel A (μ : Measure (Torus d))
  have hc : Continuous (Function.uncurry K) := centeredKernel_continuous A _
  have h0 : ∀ y, ∫ x, K x y ∂(μ : Measure (Torus d)) = 0 := fun y => by
    simp_rw [show ∀ x, K x y = K y x from fun x => centeredKernel_symm A _ x y]
    exact integral_centeredKernel_right A _ y
  have e1 : SharpLSI.interE K (μ : Measure (Torus d)) ρ = 0 := by
    simp only [SharpLSI.interE, h0, integral_zero]
  have e2 : SharpLSI.interE K (μ : Measure (Torus d)) μ = 0 := by
    simp only [SharpLSI.interE, h0, integral_zero]
  have e3 : SharpLSI.interE K (ρ : Measure (Torus d)) μ = 0 := by
    unfold SharpLSI.interE
    rw [integral_integral_swap (f := fun y x => K x y)
      ((hc.comp continuous_swap).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))]
    simp only [K, integral_centeredKernel_right, integral_zero]
  have heq : t01CenteredCorrection A μ ρ = SharpLSI.interE K ρ ρ / 2 := by
    change (1 / 2 : ℝ) * (∫ p, Function.uncurry K p
      ∂((ρ : Measure (Torus d)).prod (ρ : Measure (Torus d)))) =
        SharpLSI.interE K ρ ρ / 2
    rw [integral_prod_symm _ (hc.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))]
    unfold SharpLSI.interE
    simp only [Function.uncurry]
    ring
  rw [heq]
  change 2 * (SharpLSI.interE K ρ ρ / 2) = SharpLSI.interE K ρ ρ -
    SharpLSI.interE K μ ρ - SharpLSI.interE K ρ μ + SharpLSI.interE K μ μ
  rw [e1, e2, e3]
  ring

/-- The finite-rank entropy argument with a positive continuous Hessian form. The form premise
is tested only on continuous mean-zero functions and does not contain an entropy estimate. -/
theorem t01_small_entropy_coercive_of_form (A : InteractionData d)
    {μ : ProbabilityMeasure (Torus d)} (hμ : freeEnergy A μ = freeEnergyMinimum A)
    {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ ≤ 1)
    (hσ : ∀ w : C(Torus d, ℝ), (∫ x, w x ∂(μ : Measure (Torus d))) = 0 →
      σ * (∫ x, w x ^ 2 ∂(μ : Measure (Torus d))) ≤
        (∫ x, w x ^ 2 ∂(μ : Measure (Torus d))) +
          SharpLSI.quadF (centeredKernel A (μ : Measure (Torus d))) μ w) :
    ∃ δ > 0, ∀ ρ : ProbabilityMeasure (Torus d),
      klDiv (ρ : Measure (Torus d)) (μ : Measure (Torus d)) ≠ ⊤ →
      (klDiv (ρ : Measure (Torus d)) (μ : Measure (Torus d))).toReal ≤ δ →
        σ / 2 * (klDiv (ρ : Measure (Torus d)) (μ : Measure (Torus d))).toReal ≤
          (klDiv (ρ : Measure (Torus d)) (μ : Measure (Torus d))).toReal +
            t01CenteredCorrection A μ ρ := by
  set μm := (μ : Measure (Torus d)) with hμm
  set K := centeredKernel A μm with hKdef
  have hK : Continuous (Function.uncurry K) := centeredKernel_continuous A μm
  -- finite-rank approximation
  set ε := σ / 8 with hε
  obtain ⟨n, f, g, hfg⟩ := exists_finiteRank_approx hK (by positivity : 0 < ε)
  set KM : Torus d → Torus d → ℝ := fun x y => ∑ i, f i x * g i y with hKM
  have hKMc : Continuous (Function.uncurry KM) :=
    continuous_finsetSum _ fun i _ =>
      ((f i).continuous.comp continuous_fst).mul ((g i).continuous.comp continuous_snd)
  have hDc : Continuous (Function.uncurry fun x y => K x y - KM x y) := hK.sub hKMc
  have hD : ∀ x y, |K x y - KM x y| ≤ ε := fun x y => (hfg x y).le
  -- orthonormal features
  set fg : Fin (n + n) → C(Torus d, ℝ) := Fin.append f g with hfgdef
  set cc : Fin (n + n) → ℝ := fun k => ∫ x, fg k x ∂μm with hcc
  set u : Fin (n + n) → Torus d →ᵇ ℝ := fun k => mkOfCompact (fg k) - const _ (cc k) with hu
  have hu0 : ∀ k, ∫ x, u k x ∂μm = 0 := fun k => by
    simp only [hu, coe_sub, Pi.sub_apply, mkOfCompact_apply, const_apply]
    rw [integral_sub (integrable_of_continuous (fg k).continuous) (integrable_const _)]
    simp [hcc]
  obtain ⟨m, e, he0, heo, hα⟩ := exists_orthonormal_features μm (t01_bcf_eq_zero_of_sq A hμ) u hu0
  choose α hα using hα
  have hfgk : ∀ k x, fg k x = cc k + ∑ j, α k j * e j x := fun k x => by
    have := hα k x
    simp only [hu, coe_sub, Pi.sub_apply, mkOfCompact_apply, const_apply] at this
    linarith
  -- constants
  set E := ∑ j, ‖e j‖ with hE
  have hE0 : 0 ≤ E := Finset.sum_nonneg fun j _ => norm_nonneg _
  have heb : ∀ j x, |e j x| ≤ ‖e j‖ := fun j x => by
    rw [← Real.norm_eq_abs]; exact norm_coe_le_norm (e j) x
  set s0 := σ / (16 * (E + 1) ^ 3) with hs0
  have hs00 : 0 < s0 := by positivity
  set δ := (s0 / (E + 1)) ^ 2 / 2 with hδ
  refine ⟨δ, by positivity, fun ρ hKρ hHδ => ?_⟩
  set H := (klDiv ρ μm).toReal with hHdef
  have hH0 : 0 ≤ H := ENNReal.toReal_nonneg
  -- the coordinates `z`
  set z : Fin m → ℝ := fun j => ∫ x, e j x ∂ρ with hz
  have hzb : ∀ j, |z j| ≤ ‖e j‖ * Real.sqrt (2 * H) := fun j => by
    have := abs_integral_sub_le_pinsker (e j).continuous.measurable (heb j) hKρ
    rwa [he0 j, sub_zero] at this
  set S2 := ∑ j, z j ^ 2 with hS2
  set s := Real.sqrt S2 with hs
  have hS20 : 0 ≤ S2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hss : s ^ 2 = S2 := Real.sq_sqrt hS20
  have hs0' : 0 ≤ s := Real.sqrt_nonneg _
  have hzs : ∀ j, |z j| ≤ s := fun j => by
    rw [hs, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (Finset.single_le_sum (f := fun j => z j ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ j))
  -- `s ≤ E √(2H) ≤ s0`
  have hsle : s ≤ E * Real.sqrt (2 * H) := by
    rw [hs]
    refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
    calc S2 ≤ ∑ j, (‖e j‖ * Real.sqrt (2 * H)) ^ 2 :=
          Finset.sum_le_sum fun j _ => by
            rw [← sq_abs (z j)]
            exact pow_le_pow_left₀ (abs_nonneg _) (hzb j) 2
      _ = (∑ j, ‖e j‖ ^ 2) * Real.sqrt (2 * H) ^ 2 := by
          rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun j _ => by ring
      _ ≤ E ^ 2 * Real.sqrt (2 * H) ^ 2 :=
          mul_le_mul_of_nonneg_right (Finset.sum_sq_le_sq_sum_of_nonneg fun j _ => norm_nonneg _)
            (sq_nonneg _)
      _ = (E * Real.sqrt (2 * H)) ^ 2 := by ring
  have hsqδ : Real.sqrt (2 * δ) = s0 / (E + 1) := by
    rw [hδ, show 2 * ((s0 / (E + 1)) ^ 2 / 2) = (s0 / (E + 1)) ^ 2 by ring]
    exact Real.sqrt_sq (by positivity)
  have hss0 : s ≤ s0 := by
    have h1 : Real.sqrt (2 * H) ≤ Real.sqrt (2 * δ) := Real.sqrt_le_sqrt (by linarith)
    calc s ≤ E * Real.sqrt (2 * H) := hsle
      _ ≤ (E + 1) * Real.sqrt (2 * δ) :=
          mul_le_mul (by linarith) h1 (Real.sqrt_nonneg _) (by linarith)
      _ = s0 := by rw [hsqδ]; field_simp
  have hs16 : 16 * (E + 1) ^ 3 * s ≤ σ := by
    have : 16 * (E + 1) ^ 3 * s0 = σ := by rw [hs0]; field_simp
    calc 16 * (E + 1) ^ 3 * s ≤ 16 * (E + 1) ^ 3 * s0 :=
          mul_le_mul_of_nonneg_left hss0 (by positivity)
      _ = σ := this
  have hsE1 : s * E ≤ 1 := by
    have h1 : (E + 1) ≤ 16 * (E + 1) ^ 3 := by nlinarith [sq_nonneg (E + 1)]
    nlinarith [mul_le_mul_of_nonneg_left h1 hs0']
  -- the test function `w`
  set w : Torus d →ᵇ ℝ := ∑ j, z j • e j with hw
  have hwx : ∀ x, w x = ∑ j, z j * e j x := fun x => by
    simp only [hw, coe_sum, coe_smul, Finset.sum_apply, smul_eq_mul]
  have hwc : Continuous (fun x => w x) := w.continuous
  have hwb : ∀ x, |w x| ≤ s * E := fun x => by
    rw [hwx, hE, Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [abs_mul]
    exact mul_le_mul (hzs j) (heb j x) (abs_nonneg _) hs0'
  have hwlin : ∀ (v : Torus d → ℝ), Continuous v → ∀ (ν : Measure (Torus d)) [IsProbabilityMeasure ν],
      ∫ x, v x * w x ∂ν = ∑ j, z j * ∫ x, v x * e j x ∂ν := fun v hv ν _ => by
    have := integral_mul_lincomb ν 0 z e hv
    simp only [zero_add, zero_mul] at this
    rw [← this]; congr 1; funext x; rw [hwx]
  have hw0 : ∫ x, w x ∂μm = 0 := by
    have := hwlin (fun _ => 1) continuous_const μm
    simp only [one_mul] at this
    rw [this]; exact Finset.sum_eq_zero fun j _ => by rw [he0 j, mul_zero]
  have hwe : ∀ j, ∫ x, e j x * w x ∂μm = z j := fun j => by
    rw [hwlin _ (e j).continuous μm]
    simp only [heo, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  have hw2 : ∫ x, w x ^ 2 ∂μm = S2 := by
    have : ∫ x, w x ^ 2 ∂μm = ∫ x, w x * w x ∂μm := by congr 1; funext x; ring
    rw [this, hwlin _ hwc μm, hS2]
    refine Finset.sum_congr rfl fun j _ => ?_
    have h' : ∫ x, w x * e j x ∂μm = z j := by
      rw [← hwe j]; congr 1; funext x; ring
    rw [h']; ring
  have hwρ : ∫ x, w x ∂ρ = S2 := by
    have := hwlin (fun _ => 1) continuous_const ρ
    simp only [one_mul] at this
    rw [this, hS2]
    exact Finset.sum_congr rfl fun j _ => by rw [hz]; ring
  -- (4.16): the entropy variational formula
  have hent : S2 / 2 - E ^ 3 * s ^ 3 ≤ H := by
    have hdv := dvFun_le_klDiv (ρ := ρ) (ν := μm) w.continuous.measurable hwb
    rw [← EReal.coe_ennreal_toReal hKρ, EReal.coe_le_coe_iff] at hdv
    have hlog := log_integral_exp_le μm hwc hsE1 hwb hw0
    rw [hw2] at hlog
    simp only [dvFun, hwρ] at hdv
    have : (s * E) ^ 3 = E ^ 3 * s ^ 3 := by ring
    linarith
  -- `I + T ≥ σ` tested with `w`
  -- the finite-rank quantities
  set L : Fin (n + n) → ℝ := fun k => ∑ j, α k j * z j with hL
  have hLw : ∀ k, ∫ x, w x * fg k x ∂μm = L k := fun k => by
    have : ∫ x, w x * fg k x ∂μm = ∫ x, w x * (cc k + ∑ j, α k j * e j x) ∂μm := by
      congr 1; funext x; rw [hfgk k x]
    rw [this, integral_mul_lincomb μm _ _ _ hwc, hw0, mul_zero, zero_add, hL]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hwe j]; congr 1; congr 1; funext x; ring
  have hLρ : ∀ k, ∫ x, fg k x ∂ρ - ∫ x, fg k x ∂μm = L k := fun k => by
    have e1 : ∀ (ν : Measure (Torus d)) [IsProbabilityMeasure ν],
        ∫ x, fg k x ∂ν = cc k + ∑ j, α k j * ∫ x, e j x ∂ν := fun ν _ => by
      rw [← integral_lincomb ν]; congr 1; funext x; rw [hfgk k x]
    rw [e1 ρ, e1 μm, hL]
    simp only [he0, mul_zero, Finset.sum_const_zero, add_zero, add_sub_cancel_left, hz]
  have hfi : ∀ i, fg (Fin.castAdd n i) = f i := fun i => by rw [hfgdef]; exact Fin.append_left f g i
  have hgi : ∀ i, fg (Fin.natAdd n i) = g i := fun i => by rw [hfgdef]; exact Fin.append_right f g i
  set X := ∑ i, L (Fin.castAdd n i) * L (Fin.natAdd n i) with hX
  have hquadM : quadF KM μm (fun x => w x) = X := by
    rw [hKM, quadF_finiteRank f g μm hwc, hX]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hLw (Fin.castAdd n i), ← hLw (Fin.natAdd n i), hfi, hgi]
    congr 1; congr 1; funext y; ring
  have hbM : bForm KM μm ρ = X := by
    rw [hKM, bForm_finiteRank f g μm ρ, hX]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hLρ (Fin.castAdd n i), ← hLρ (Fin.natAdd n i), hfi, hgi]
  -- `X ≥ (σ - 1 - ε) S2`
  have hXlow : (σ - 1 - σ / 8) * S2 ≤ X := by
    have h1 := hσ (⟨w, hwc⟩ : C(Torus d, ℝ)) hw0
    change σ * (∫ x, w x ^ 2 ∂μm) ≤ (∫ x, w x ^ 2 ∂μm) + quadF K μm w at h1
    rw [hw2, quadF_sub hK hKMc μm hwc, hquadM] at h1
    have h2 := abs_quadF_le hDc hD μm hwc
    rw [hw2] at h2
    have h3 := le_abs_self (quadF (fun x y => K x y - KM x y) μm fun x => w x)
    rw [hε] at h2
    linarith
  -- (4.17): `2J ≥ X - 2εH`
  have hJlow : X - σ / 8 * (2 * H) ≤ 2 * t01CenteredCorrection A μ ρ := by
    rw [t01_two_correction_eq_bForm A μ ρ, bForm_sub hK hKMc μm ρ, hbM]
    have h2 := abs_bForm_le hDc hD μm ρ hKρ
    have h3 := neg_abs_le (bForm (fun x y => K x y - KM x y) μm ρ)
    rw [hε, ← hHdef] at h2
    linarith
  have := coercive_algebra hσ0 hσ1 hH0 hs0' hE0 hss.symm hs16 hent hXlow hJlow
  linarith


end DGPS.Lipschitz
