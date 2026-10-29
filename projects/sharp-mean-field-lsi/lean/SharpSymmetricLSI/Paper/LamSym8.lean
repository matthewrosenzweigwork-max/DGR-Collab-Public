import SharpSymmetricLSI.Paper.LamSym7
import SharpSymmetricLSI.Paper.LamSym1
import SharpSymmetricLSI.Paper.LamSym2
import SharpSymmetricLSI.Paper.GroundT5
import SharpSymmetricLSI.Paper.ForceApprox4
import SharpSymmetricLSI.Paper.GaussLaw11
import SharpSymmetricLSI.Paper.TestEnergy4
import SharpSymmetricLSI.Paper.TestEnergy8
import SharpSymmetricLSI.Paper.GaussForm16
import SharpSymmetricLSI.Paper.Prop21Conclusion
import SharpSymmetricLSI.Paper.CenteredEntropy
import SharpSymmetricLSI.Statements.R19_Lemma_5_2
import SharpSymmetricLSI.Statements.R02_Prop_2_1
import SharpSymmetricLSI.Statements.R23_Reference_Spectrum

/-!
# (2.8) (lane s42): the linear tests, and `λ_N^sym → λ_G`

* `gibbs_lintegral_exp_le`: moving an `exp(a Y²)` moment from `μ^{⊗N}` to `P_N` (Hölder against
  the `L^p(μ^{⊗N})` bound of the centered Gibbs density, R19), at the cost `a ↦ a/q`.
* `htests_linTest`: the finite linear tests `f_N = ∑_{i<n} v_i Z_{N,i}` (Paper/LamSym1–2, with
  the `C¹` representatives `e^C_j`) satisfy the hypothesis `htests` of `lamSym_tendsto_of`.
* `lamSym_tendsto_of'`: (2.8) with only the compactness property (2.5)–(2.7) (as
  `CompactnessProperty'`) and the Gaussian Poincaré inequality (8.10) as hypotheses.
-/

open MeasureTheory Filter Topology ProbabilityTheory Finset Real
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-- **Moment transfer** from `μ^{⊗N}` to `P_N`. -/
theorem gibbs_lintegral_exp_le (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)}
    (hμ : IsMinimizer V W μ) {p : ℝ} (hp : 1 < p) (N : ℕ) {Bp : ℝ}
    (hBp : ∫ X, (rexp (-Ucentered W μ N X) / centeredPartition W μ N) ^ p
      ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))) ≤ Bp)
    {Y : Config N d → ℝ} (hYm : AEMeasurable Y (Measure.pi fun _ : Fin N => (μ : Measure (Torus d))))
    {a : ℝ} (ha : 0 < a) :
    ∫⁻ X, ENNReal.ofReal (rexp (a / p.conjExponent * Y X ^ 2)) ∂gibbs V W N ≤
      ENNReal.ofReal Bp ^ (1 / p) * (∫⁻ X, ENNReal.ofReal (rexp (a * Y X ^ 2))
        ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d)))) ^ (1 / p.conjExponent) := by
  set μN := Measure.pi fun _ : Fin N => (μ : Measure (Torus d))
  set q := p.conjExponent
  have hpq : p.HolderConjugate q := Real.HolderConjugate.conjExponent hp
  have hq0 : 0 < q := hpq.symm.pos
  have hp0 : 0 < p := hpq.pos
  set ρ : Config N d → ℝ := fun X => rexp (-Ucentered W μ N X) / centeredPartition W μ N
  have hK := centeredPartition_pos hyp (μ : Measure (Torus d)) N
  have hρm : Measurable ρ :=
    ((measurable_Ucentered hyp (μ : Measure (Torus d)) N).neg.exp).div_const _
  have hρ0 : ∀ X, 0 ≤ ρ X := fun X => div_nonneg (exp_pos _).le hK.le
  obtain ⟨BU, hBU⟩ := Ucentered_bdd hyp (μ : Measure (Torus d)) N
  have hρb : ∀ X, ρ X ≤ rexp BU / centeredPartition W μ N := fun X =>
    div_le_div_of_nonneg_right (exp_le_exp.mpr (by linarith [(abs_le.mp (hBU X)).1])) hK.le
  rw [gibbs_eq_centered_aux hyp hμ N,
    lintegral_withDensity_eq_lintegral_mul_non_measurable _
      (f := fun X => ENNReal.ofReal (ρ X)) (ENNReal.measurable_ofReal.comp hρm) (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  have hgm : AEMeasurable (fun X => ENNReal.ofReal (rexp (a / q * Y X ^ 2))) μN :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      (measurable_exp.comp_aemeasurable ((hYm.pow_const 2).const_mul _))
  refine (ENNReal.lintegral_mul_le_Lp_mul_Lq μN hpq
    (ENNReal.measurable_ofReal.comp hρm).aemeasurable hgm).trans ?_
  refine mul_le_mul' (ENNReal.rpow_le_rpow ?_ (by positivity)) (le_of_eq ?_)
  · have e1 : (fun X => ENNReal.ofReal (ρ X) ^ p) = fun X => ENNReal.ofReal (ρ X ^ p) := by
      funext X; rw [ENNReal.ofReal_rpow_of_nonneg (hρ0 X) hp0.le]
    simp only [Function.comp_apply]
    rw [e1, ← ofReal_integral_eq_lintegral_ofReal _ (Eventually.of_forall fun X => by
      have := hρ0 X; positivity)]
    · exact ENNReal.ofReal_le_ofReal hBp
    · haveI : IsProbabilityMeasure μN := by infer_instance
      refine Integrable.of_bound (hρm.pow_const p).aestronglyMeasurable
        ((rexp BU / centeredPartition W μ N) ^ p) (Eventually.of_forall fun X => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (hρ0 X) _)]
      exact Real.rpow_le_rpow (hρ0 X) (hρb X) hp0.le
  · congr 1
    refine lintegral_congr fun X => ?_
    rw [ENNReal.ofReal_rpow_of_nonneg (exp_pos _).le hq0.le, ← Real.exp_mul]
    congr 2
    field_simp

/-- **The linear tests discharge `htests`.** -/
theorem htests_linTest (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (hr : 0 < rStar V W)
    {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
    {e : ℕ → Torus d → ℝ} {lam : ℕ → ℝ} (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam)
    {C : ℕ → ℕ → ℝ} (hC : IsInverseOfIPlus (Tmat W μ e) C)
    {γ : Measure (ℕ → ℝ)} (hγ : IsCenteredGaussianCov γ C) :
    ∀ (n : ℕ) (v : ℕ → ℝ), 0 < ∑ i ∈ range n, ∑ j ∈ range n, v i * C i j * v j →
      ∃ f : (N : ℕ) → Config N d → ℝ,
        (∀ᶠ N in atTop, MemH1C (gibbs V W N) (f N) ∧ IsSymmetric (f N)) ∧
        Tendsto (fun N => var (gibbs V W N) (f N)) atTop
          (𝓝 (ENNReal.ofReal (∑ i ∈ range n, ∑ j ∈ range n, v i * C i j * v j))) ∧
        Tendsto (fun N => energy V W N (f N)) atTop
          (𝓝 (ENNReal.ofReal (∑ i ∈ range n, lamShift lam i * v i ^ 2))) := by
  set μm := (μ : Measure (Torus d))
  have h21 := prop21Conclusion_of_equilibrium (prop_equilibrium hd hyp hr) hμ
  obtain ⟨Cp, p, hp, hCp⟩ := reference_entropy hd hyp hr hμ
  have hpart : ∃ B p : ℝ, 1 < p ∧ ∀ N : ℕ, 1 ≤ N →
      |Real.log (centeredPartition W μ N)| ≤ B ∧
      ∫ X, (rexp (-Ucentered W μ N X) / centeredPartition W μ N) ^ p
        ∂Measure.pi (fun _ : Fin N => μm) ≤ B :=
    ⟨Cp, p, hp, fun N hN => ⟨(hCp N hN).2.1, (hCp N hN).2.2⟩⟩
  have hpart' : ∃ Bp p : ℝ, 1 < p ∧ ∀ N : ℕ, 1 ≤ N →
      ∫ X, (rexp (-Ucentered W μ N X) / centeredPartition W μ N) ^ p
        ∂Measure.pi (fun _ : Fin N => μm) ≤ Bp := ⟨Cp, p, hp, fun N hN => (hCp N hN).2.2⟩
  obtain ⟨Q, hQ⟩ := exists_secondChaos_Tmat hyp hμ he
  obtain ⟨-, -, hγi, hlaw⟩ := gaussian_limit_law_of hyp h21 he hQ hC hpart
  rw [eq_of_isCenteredGaussianCov hγi hγ] at hlaw
  obtain ⟨eC, heC⟩ := exists_c1_reps hd hyp hr hμ he
  have hφ : ∀ j, ContDiff ℝ 1 (eC j ∘ liftT) := fun j => (heC j).1
  have heCh : ∀ j, eC j =ᵐ[haar d] e j := fun j => (heC j).2.1
  have heCμ : ∀ j, eC j =ᵐ[μm] e j := fun j => (heC j).2.2
  have hac := minimizer_ac hyp hμ
  have hP : ∀ N, IsProbabilityMeasure (gibbs V W N) := fun N => gibbs_isProbabilityMeasure hyp N
  have hPac : ∀ N, gibbs V W N ≪ Measure.pi (fun _ : Fin N => μm) := fun N => by
    rw [gibbs_eq_centered_aux hyp hμ N]; exact withDensity_absolutelyContinuous _ _
  have hcent : ∀ j, ∫ x, eC (j + 1) x ∂μm = 0 := fun j => by
    rw [integral_congr_ae (heCμ (j + 1))]
    have := he.orthonormal (j + 1) 0
    rw [he.zero] at this
    simpa using this
  intro n v hQpos
  set vF : Fin n → ℝ := fun i => v i
  refine ⟨fun N => linTest eC N n vF, Eventually.of_forall fun N =>
    ⟨memH1C_linTest hyp hμ hφ N n vF, linTest_symm eC N n vF⟩, ?_, ?_⟩
  · -- the variance
    have hae : ∀ N, linTest eC N n vF =ᵐ[gibbs V W N] linStat e N n v := fun N => by
      refine (hPac N).ae_le ?_
      filter_upwards [zC_ae_eq_fluct hac heCh N n] with X hX
      simp only [linTest, linCLM_apply, hX, linStat, vF]
      exact (Finset.sum_range fun i => v i * fluct e N i X).symm
    have hL2 : ∀ N, MemLp (linStat e N n v) 2 (gibbs V W N) := fun N =>
      (memLp_of_memH1C hyp (memH1C_linTest hyp hμ hφ N n vF)).ae_eq (hae N)
    obtain ⟨a, ha, hmom⟩ := exp_moment_linTest hφ vF hcent
    have hmom' : ∃ a' : ℝ, 0 < a' ∧ ∃ B : ℝ≥0∞, B ≠ ⊤ ∧ ∀ᶠ N in atTop,
        ∫⁻ X, ENNReal.ofReal (rexp (a' * linStat e N n v X ^ 2)) ∂gibbs V W N ≤ B := by
      refine ⟨a / p.conjExponent, div_pos ha (Real.HolderConjugate.conjExponent hp).symm.pos,
        ENNReal.ofReal Cp ^ (1 / p) * gaussSqConst ^ (1 / p.conjExponent), ?_, ?_⟩
      · exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by positivity)
          ENNReal.ofReal_ne_top) (ENNReal.rpow_ne_top_of_nonneg (by
            have := (Real.HolderConjugate.conjExponent hp).symm.pos; positivity)
            gaussSqConst_ne_top)
      · filter_upwards [eventually_ge_atTop 1] with N hN
        have hYm : AEMeasurable (linTest eC N n vF) (Measure.pi fun _ : Fin N => μm) :=
          ((linCLM vF).continuous.measurable.comp (measurable_pi_iff.2 fun i =>
            measurable_const.mul (Finset.measurable_sum _ fun l _ =>
              (measurable_of_contDiff (hφ _)).comp (measurable_pi_apply l)))).aemeasurable
        rw [← lintegral_congr_ae (by
          filter_upwards [hae N] with X hX; rw [hX] :
          (fun X => ENNReal.ofReal (rexp (a / p.conjExponent * linTest eC N n vF X ^ 2))) =ᵐ[
            gibbs V W N] fun X => ENNReal.ofReal (rexp (a / p.conjExponent * linStat e N n v X ^ 2)))]
        refine (gibbs_lintegral_exp_le hyp hμ hp N (hCp N hN).2.2 hYm ha).trans ?_
        exact mul_le_mul' le_rfl (ENNReal.rpow_le_rpow (hmom N hN)
          (by have := (Real.HolderConjugate.conjExponent hp).symm.pos; positivity))
    have hvar := tendsto_var_linStat hyp hγ hlaw n v hQpos.le (Eventually.of_forall hL2) hmom'
    refine hvar.congr fun N => ?_
    show evariance _ _ = evariance _ _
    exact (evariance_congr (hae N)).symm
  · -- the energy
    refine tendsto_energy_linStat hyp hμ he hφ heCh hpart' n v (Eventually.of_forall fun N => ?_)
    refine (hPac N).ae_le ?_
    filter_upwards [gradSqC_linTest_ae hyp hμ hφ N n vF] with X hX
    rw [hX]
    simp only [vF]
    rw [← Finset.sum_range fun i => ∑ j : Fin n, v i * v j * mobA eC N X i j]
    exact Finset.sum_congr rfl fun i _ =>
      (Finset.sum_range fun j => v i * v j * mobA eC N X i j).symm

/-- **(2.8): `λ_N^sym → λ_G`**, from the compactness property (2.5)–(2.7) and the Gaussian
Poincaré inequality (8.10). -/
theorem lamSym_tendsto_of' (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (hr : 0 < rStar V W)
    {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
    {e : ℕ → Torus d → ℝ} {lam : ℕ → ℝ} (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam)
    {C : ℕ → ℕ → ℝ} (hC : IsInverseOfIPlus (Tmat W μ e) C)
    {γ : Measure (ℕ → ℝ)} (hγ : IsCenteredGaussianCov γ C)
    (hcomp : CompactnessProperty' V W γ (gaussForm (lamShift lam) γ))
    (hP : ∀ f : (ℕ → ℝ) → ℝ, MemLp f 2 γ →
      var γ f ≤ gaussForm (lamShift lam) γ f / lamG (lamShift lam) C) :
    lamG (lamShift lam) C ≤ liminf (fun N => lamSym V W N) atTop ∧
    limsup (fun N => lamSym V W N) atTop ≤ lamG (lamShift lam) C ∧
    Tendsto (fun N => lamSym V W N) atTop (𝓝 (lamG (lamShift lam) C)) := by
  haveI := hγ.1
  have h21 := prop21Conclusion_of_equilibrium (prop_equilibrium hd hyp hr) hμ
  obtain ⟨σ, hσ0, hσ⟩ := secOp_ge_of_prop21 hyp he h21
  have hT := Tmat_symm hyp hμ he
  have hS := (hasSum_Tmat_sq hyp hμ he).summable
  have hlam : ∀ i, 0 < lamShift lam i := fun i =>
    ((ref_spectrum hd hyp hr hμ).2 e lam he).1 (i + 1) (by omega)
  exact lamSym_tendsto_of hyp hσ0 (fun i j => C_symm_of_secOp hT hS hσ0 hσ hC i j)
    (quadC_nonneg hT hS hσ0 hσ hC) (quadC_le hT hS hσ0 hσ hC) (fun j => (hC j).1) hlam hcomp hP
    (htests_linTest hd hyp hr hμ he hC hγ)

end SharpLSI
