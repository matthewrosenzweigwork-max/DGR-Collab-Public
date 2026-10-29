import SharpSymmetricLSI.Paper.Coercivity1
import SharpSymmetricLSI.Paper.Coercivity2
import SharpSymmetricLSI.Infra.W1InfFiniteRank
import SharpSymmetricLSI.Paper.Centering

/-!
# Lemma 4.2 (lane s42; R16): coercivity for small relative entropy

Manuscript, proof of Lemma 4.2, first paragraph, with the interaction kernel `K` (4.14)
approximated uniformly by a finite-rank kernel `K_M = ∑ fᵢ ⊗ gᵢ` (Stone–Weierstrass), the
features `fᵢ, gᵢ` (centered) expanded in an `L²(μ)`-orthonormal family `e_j`, `z_j = ρ(e_j)` and
`w = ∑ z_j e_j`. With `S = |z|²`:
* (4.16) the entropy variational formula tested with `w`: `H ≥ S/2 - E³ |z|³`;
* `I + T ≥ σ` tested with `w` and `|T - T_M| ≤ ε`: `K_M(ρ-μ,ρ-μ) = ⟨w, T_M w⟩ ≥ (σ-1-ε) S`;
* (4.17) `2J(ρ) = K(ρ-μ,ρ-μ) ≥ K_M(ρ-μ,ρ-μ) - 2εH`;
which give `G = H + J ≥ (σ/2) H` for `H` small.
-/

noncomputable section
open MeasureTheory InformationTheory Filter Real BoundedContinuousFunction
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ}

/-- The final scalar inequality of the small-entropy case. -/
theorem coercive_algebra {σ H S2 X J2 E s : ℝ} (hσ0 : 0 < σ) (hσ1 : σ ≤ 1) (hH : 0 ≤ H)
    (hs : 0 ≤ s) (hE : 0 ≤ E) (hS2 : S2 = s ^ 2) (hsE : 16 * (E + 1) ^ 3 * s ≤ σ)
    (hent : S2 / 2 - E ^ 3 * s ^ 3 ≤ H) (hX : (σ - 1 - σ / 8) * S2 ≤ X)
    (hJ : X - σ / 8 * (2 * H) ≤ J2) : σ / 2 * H ≤ H + J2 / 2 := by
  have hE3 : E ^ 3 ≤ (E + 1) ^ 3 := pow_le_pow_left₀ hE (by linarith) 3
  have h1 : E ^ 3 * s ≤ σ / 16 := by nlinarith [mul_le_mul_of_nonneg_right hE3 hs]
  have hS0 : 0 ≤ S2 := by rw [hS2]; positivity
  have h2 : E ^ 3 * s ^ 3 ≤ σ / 16 * S2 := by
    have := mul_le_mul_of_nonneg_right h1 (sq_nonneg s)
    rw [hS2]; nlinarith [this]
  have h3 : (8 - σ) * S2 ≤ 16 * H := by nlinarith
  have h4 : 0 ≤ 1 - 7 * σ / 8 := by linarith
  have h5 : (1 - 7 * σ / 8) * S2 * (8 - σ) ≤ 2 * (1 - 5 * σ / 8) * H * (8 - σ) := by
    nlinarith [mul_le_mul_of_nonneg_left h3 h4, mul_nonneg (by positivity : 0 ≤ 2 * σ + 5 * σ ^ 2 / 4) hH]
  have h6 : (1 - 7 * σ / 8) * S2 ≤ 2 * (1 - 5 * σ / 8) * H :=
    le_of_mul_le_mul_right h5 (by linarith)
  nlinarith

section lincomb
variable (ν : Measure (Torus d)) [IsProbabilityMeasure ν] {m : ℕ}

theorem integral_mul_lincomb (c : ℝ) (α : Fin m → ℝ) (e : Fin m → Torus d →ᵇ ℝ)
    {v : Torus d → ℝ} (hv : Continuous v) :
    ∫ x, v x * (c + ∑ j, α j * e j x) ∂ν = c * ∫ x, v x ∂ν + ∑ j, α j * ∫ x, v x * e j x ∂ν := by
  have h : (fun x => v x * (c + ∑ j, α j * e j x)) =
      fun x => c * v x + ∑ j, α j * (v x * e j x) := by
    funext x
    rw [mul_add, Finset.mul_sum, mul_comm (v x) c]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by ring
  have i1 : Integrable (fun x => c * v x) ν := integrable_of_continuous (continuous_const.mul hv)
  have i2 : ∀ j ∈ (Finset.univ : Finset (Fin m)), Integrable (fun x => α j * (v x * e j x)) ν :=
    fun j _ => integrable_of_continuous (continuous_const.mul (hv.mul (e j).continuous))
  have i3 : Integrable (fun x => ∑ j, α j * (v x * e j x)) ν := integrable_finsetSum _ i2
  rw [h, integral_add i1 i3, integral_const_mul, integral_finsetSum _ i2]
  congr 1
  exact Finset.sum_congr rfl fun j _ => integral_const_mul _ _

theorem integral_lincomb (c : ℝ) (α : Fin m → ℝ) (e : Fin m → Torus d →ᵇ ℝ) :
    ∫ x, (c + ∑ j, α j * e j x) ∂ν = c + ∑ j, α j * ∫ x, e j x ∂ν := by
  have := integral_mul_lincomb ν c α e (v := fun _ => 1) continuous_const
  simp only [one_mul, integral_const, probReal_univ, smul_eq_mul, mul_one] at this
  exact this

end lincomb

section main
variable {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ} (hyp : Hyp V W KV KW)
include hyp

theorem continuous_centeredKernel (μ : Measure (Torus d)) [IsProbabilityMeasure μ] :
    Continuous (Function.uncurry (centeredKernel W μ)) := by
  have hc : Continuous (convMeas W μ) := cont_integral_right hyp.continuous_W μ
  show Continuous fun p : Torus d × Torus d =>
    W p.1 p.2 - convMeas W μ p.1 - convMeas W μ p.2 + interE W μ μ
  exact ((hyp.continuous_W.sub (hc.comp continuous_fst)).sub (hc.comp continuous_snd)).add
    continuous_const

theorem centeredKernel_symm_coerc (μ : Measure (Torus d)) (x y : Torus d) :
    centeredKernel W μ x y = centeredKernel W μ y x := by
  unfold centeredKernel; rw [hyp.symm x y]; ring

/-- `2 J(ρ) = K(ρ-μ, ρ-μ)`. -/
theorem two_Jfun_eq_bForm (μ ρ : Measure (Torus d)) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ρ] : 2 * Jfun W μ ρ = bForm (centeredKernel W μ) μ ρ := by
  have hc := continuous_centeredKernel hyp μ
  have h0 : ∀ y, ∫ x, centeredKernel W μ x y ∂μ = 0 := fun y => by
    simp_rw [centeredKernel_symm_coerc hyp μ _ y]; exact integral_centeredKernel hyp μ y
  have e1 : interE (centeredKernel W μ) μ ρ = 0 := by simp only [interE, h0, integral_zero]
  have e2 : interE (centeredKernel W μ) μ μ = 0 := by simp only [interE, h0, integral_zero]
  have e3 : interE (centeredKernel W μ) ρ μ = 0 := by
    unfold interE
    rw [integral_integral_swap (f := fun y x => centeredKernel W μ x y)
      (integrable_of_continuous (hc.comp continuous_swap))]
    simp only [integral_centeredKernel hyp μ, integral_zero]
  simp only [bForm, Jfun, e1, e2, e3]; ring

/-- A minimizer charges every nonzero continuous function. -/
theorem bcf_eq_zero_of_sq {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
    (u : Torus d →ᵇ ℝ) (h0 : ∫ x, u x * u x ∂(μ : Measure (Torus d)) = 0) : u = 0 := by
  set μm := (μ : Measure (Torus d))
  obtain ⟨hpm, hppos, hp1⟩ := elDensity_props hyp μm
  have hμp : μm = densMeasure (elDens V W μm) := minimizer_eq_elDensity hyp hμ
  have hae : (fun x => u x * u x) =ᵐ[μm] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun x => mul_self_nonneg _) ((u * u).integrable μm)).mp h0
  have hac : haar d ≪ μm := by
    rw [hμp]
    exact withDensity_absolutelyContinuous' (ENNReal.measurable_ofReal.comp hpm).aemeasurable
      (Eventually.of_forall fun x => by simp [hppos x])
  have hc : Continuous fun x => u x * u x := u.continuous.mul u.continuous
  have heq := (Continuous.ae_eq_iff_eq (μ := haar d) hc continuous_const).mp (hac.ae_le hae)
  ext x
  exact mul_self_eq_zero.mp (congrFun heq x)

/-- **Lemma 4.2, small entropy.** -/
theorem small_entropy_coercive {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
    {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ ≤ 1)
    (hσ : ∀ h, MemL20 μ h → σ * ∫ x, h x ^ 2 ∂(μ : Measure (Torus d)) ≤ secondVar W μ h) :
    ∃ δ > 0, ∀ ρ : Measure (Torus d), IsProbabilityMeasure ρ →
      klDiv ρ (μ : Measure (Torus d)) ≠ ⊤ → (klDiv ρ (μ : Measure (Torus d))).toReal ≤ δ →
        σ / 2 * (klDiv ρ (μ : Measure (Torus d))).toReal ≤
          (klDiv ρ (μ : Measure (Torus d))).toReal + Jfun W μ ρ := by
  set μm := (μ : Measure (Torus d)) with hμm
  set K := centeredKernel W μm with hKdef
  have hK : Continuous (Function.uncurry K) := continuous_centeredKernel hyp μm
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
  obtain ⟨m, e, he0, heo, hα⟩ := exists_orthonormal_features μm (bcf_eq_zero_of_sq hyp hμ) u hu0
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
  refine ⟨δ, by positivity, fun ρ hρ hKρ hHδ => ?_⟩
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
  have hw20 : MemL20 μm (fun x => w x) := by
    refine ⟨MemLp.of_bound hwc.aestronglyMeasurable (s * E)
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hwb x), hw0⟩
  have hsv : secondVar W μm (fun x => w x) = S2 + quadF K μm (fun x => w x) := by
    have hT : ∀ x, Top W μm (fun x => w x) x = ∫ y, K x y * w y ∂μm := fun x =>
      Top_eq_integral hyp μm hw20 x
    have hTc : Continuous fun x => ∫ y, K x y * w y ∂μm :=
      cont_integral_right (cont_kernel_mul hK hwc) μm
    unfold secondVar quadF
    simp only [hT, mul_add]
    have i1 : Integrable (fun x => w x * w x) μm := integrable_of_continuous (hwc.mul hwc)
    have i2 : Integrable (fun x => w x * ∫ y, K x y * w y ∂μm) μm :=
      integrable_of_continuous (hwc.mul hTc)
    rw [integral_add i1 i2]
    rw [← hw2]; congr 1; congr 1; funext x; ring
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
    have h1 := hσ (fun x => w x) hw20
    rw [hw2, hsv, quadF_sub hK hKMc μm hwc, hquadM] at h1
    have h2 := abs_quadF_le hDc hD μm hwc
    rw [hw2] at h2
    have h3 := le_abs_self (quadF (fun x y => K x y - KM x y) μm fun x => w x)
    rw [hε] at h2
    linarith
  -- (4.17): `2J ≥ X - 2εH`
  have hJlow : X - σ / 8 * (2 * H) ≤ 2 * Jfun W μm ρ := by
    rw [two_Jfun_eq_bForm hyp μm ρ, bForm_sub hK hKMc μm ρ, hbM]
    have h2 := abs_bForm_le hDc hD μm ρ hKρ
    have h3 := neg_abs_le (bForm (fun x y => K x y - KM x y) μm ρ)
    rw [hε, ← hHdef] at h2
    linarith
  have := coercive_algebra hσ0 hσ1 hH0 hs0' hE0 hss.symm hs16 hent hXlow hJlow
  linarith

end main

end SharpLSI
