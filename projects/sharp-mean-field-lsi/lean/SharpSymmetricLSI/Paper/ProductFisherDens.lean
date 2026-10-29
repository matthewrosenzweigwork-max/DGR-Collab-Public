import SharpSymmetricLSI.Paper.ProductFisherGrad
import SharpSymmetricLSI.Paper.R37Particle
import SharpSymmetricLSI.Paper.H1Config

/-!
# (2.11): `√(dν_N/dP_N)`, `H¹` membership and `4ℰ_N = I` (Phase 3, lane D; R6)

`ν_N = P_N.withDensity (Z_N ∏ ρ(xᵢ) e^{H_N})`, so `√(dν_N/dP_N) = √Z_N exp(Φ/2)` a.e.; hence
`f_N ∈ H¹(P_N)`, `I(ν_N|P_N) = 4ℰ_N(f_N) = ∫ |∇Φ|² dν_N`.
-/

open MeasureTheory Set Filter Topology InformationTheory
open scoped ENNReal ContDiff

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ} {N : ℕ}

/-- `dν_N/dP_N = Z_N ∏ ρ(xᵢ) e^{H_N}`. -/
noncomputable def densNP (V : Torus d → ℝ) (W : Torus d → Torus d → ℝ) (ρ : Torus d → ℝ) (N : ℕ)
    (X : Config N d) : ℝ≥0∞ :=
  ENNReal.ofReal (partitionFn V W N * (∏ i, ρ (X i)) * Real.exp (hamiltonian V W N X))

theorem partitionFn_pos (hyp : Hyp V W KV KW) (N : ℕ) : 0 < partitionFn V W N := by
  unfold partitionFn
  exact integral_exp_pos (integrable_of_continuous (Real.continuous_exp.comp
    (continuous_hamiltonian hyp N).neg))

theorem measurable_densNP (hyp : Hyp V W KV KW) {ρ : Torus d → ℝ} (hρm : Measurable ρ) :
    Measurable (densNP V W ρ N) :=
  ENNReal.measurable_ofReal.comp ((measurable_const.mul (Finset.measurable_prod _ fun i _ =>
    hρm.comp (measurable_pi_apply i))).mul
      (Real.continuous_exp.comp (continuous_hamiltonian hyp N)).measurable)

theorem productState_eq_withDensity (hyp : Hyp V W KV KW) {ρ : Torus d → ℝ} (hρm : Measurable ρ)
    (hρ0 : ∀ x, 0 ≤ ρ x) (hρi : Integrable ρ (haar d)) :
    Measure.pi (fun _ : Fin N => densMeasure ρ) = (gibbs V W N).withDensity (densNP V W ρ N) := by
  have hZ := partitionFn_pos hyp N
  have hfm : Measurable fun X : Config N d =>
      ENNReal.ofReal (Real.exp (-hamiltonian V W N X) / partitionFn V W N) :=
    ENNReal.measurable_ofReal.comp ((Real.continuous_exp.comp
      (continuous_hamiltonian hyp N).neg).measurable.div_const _)
  have hmul := withDensity_mul (volume : Measure (Config N d)) hfm (measurable_densNP hyp hρm)
  rw [densMeasure, pi_withDensity_ofReal hρm hρ0 hρi, gibbs, ← hmul]
  congr 1
  funext X
  simp only [Pi.mul_apply, densNP]
  rw [← ENNReal.ofReal_mul (div_nonneg (Real.exp_pos _).le hZ.le)]
  congr 1
  have : Real.exp (-hamiltonian V W N X) * Real.exp (hamiltonian V W N X) = 1 := by
    rw [← Real.exp_add]; simp
  symm
  calc _ = (∏ i, ρ (X i)) * (Real.exp (-hamiltonian V W N X) * Real.exp (hamiltonian V W N X)) *
        (partitionFn V W N / partitionFn V W N) := by ring
    _ = _ := by rw [this, div_self hZ.ne']; ring

theorem rnDeriv_productState (hyp : Hyp V W KV KW) {ρ : Torus d → ℝ} (hρm : Measurable ρ)
    (hρ0 : ∀ x, 0 ≤ ρ x) (hρi : Integrable ρ (haar d)) :
    (Measure.pi fun _ : Fin N => densMeasure ρ).rnDeriv (gibbs V W N) =ᵐ[gibbs V W N]
      densNP V W ρ N := by
  have := gibbs_isProbabilityMeasure hyp N
  rw [productState_eq_withDensity hyp hρm hρ0 hρi]
  exact Measure.rnDeriv_withDensity _ (measurable_densNP hyp hρm)

theorem sqrt_densNP (hyp : Hyp V W KV KW) {ρ : Torus d → ℝ} (hpos : ∀ x, 0 < ρ x) (X : Config N d) :
    Real.sqrt (densNP V W ρ N X).toReal =
      Real.sqrt (partitionFn V W N) * Real.exp (PhiF V W ρ N (flat X) / 2) := by
  have hZ := partitionFn_pos hyp N
  have hp : 0 < ∏ i, ρ (X i) := Finset.prod_pos fun i _ => hpos _
  set Φ := hamiltonian V W N X + ∑ i, Real.log (ρ (X i)) with hΦ
  have e : partitionFn V W N * (∏ i, ρ (X i)) * Real.exp (hamiltonian V W N X) =
      partitionFn V W N * (Real.exp (Φ / 2) * Real.exp (Φ / 2)) := by
    rw [← Real.exp_add, show Φ / 2 + Φ / 2 = Φ by ring, hΦ, Real.exp_add, Real.exp_sum,
      Finset.prod_congr rfl fun i _ => Real.exp_log (hpos (X i))]
    ring
  rw [densNP, e, ENNReal.toReal_ofReal (by positivity), Real.sqrt_mul hZ.le,
    Real.sqrt_mul_self (Real.exp_pos _).le, PhiF_flat hyp]

/-- **(2.11), first step**: `f_N ∈ H¹(P_N)`, `I(ν_N|P_N) = 4ℰ_N(f_N) = ∫ |∇Φ|² dν_N`. -/
theorem fisher_productState (hyp : Hyp V W KV KW) {ρ : Torus d → ℝ} (hs : IsSmoothT ρ)
    (hpos : ∀ x, 0 < ρ x) (h1 : ∫ x, ρ x ∂haar d = 1) :
    MemH1C (gibbs V W N) (sqrtDens (Measure.pi fun _ : Fin N => densMeasure ρ) (gibbs V W N)) ∧
    fisherInfoC (Measure.pi fun _ : Fin N => densMeasure ρ) (gibbs V W N) =
      4 * energy V W N (sqrtDens (Measure.pi fun _ : Fin N => densMeasure ρ) (gibbs V W N)) ∧
    fisherInfoC (Measure.pi fun _ : Fin N => densMeasure ρ) (gibbs V W N) =
      ENNReal.ofReal (∫ X, sqNorm (gPhi V W ρ N (flat X))
        ∂(Measure.pi fun _ : Fin N => densMeasure ρ)) := by
  set P := gibbs V W N with hP
  set ν := Measure.pi fun _ : Fin N => densMeasure ρ with hν
  have hPp := gibbs_isProbabilityMeasure hyp N
  have hρc : Continuous ρ := hs.continuous
  have hρm : Measurable ρ := hρc.measurable
  have hρ0 : ∀ x, 0 ≤ ρ x := fun x => (hpos x).le
  have hρi : Integrable ρ (haar d) := integrable_of_continuous hρc
  haveI := isProbabilityMeasure_densMeasure' hρ0 h1
  have hZ := partitionFn_pos hyp N
  set c := Real.sqrt (partitionFn V W N)
  set ũ : UnitAddTorus (Fin N × Fin d) → ℝ := fun y => c * Real.exp (PhiF V W ρ N y / 2) with hũdef
  set gũ : UnitAddTorus (Fin N × Fin d) → Fin N × Fin d → ℝ :=
    fun y p => c * (Real.exp (PhiF V W ρ N y / 2) / 2 * gPhi V W ρ N y p) with hgũdef
  have hνP : ν = P.withDensity (densNP V W ρ N) := productState_eq_withDensity hyp hρm hρ0 hρi
  have hνac : ν ≪ P := by rw [hνP]; exact withDensity_absolutelyContinuous _ _
  have hrn := rnDeriv_productState (N := N) hyp hρm hρ0 hρi
  have hfP : ∀ᵐ X ∂P, sqrtDens ν P X = ũ (flat X) := by
    filter_upwards [hrn] with X hX
    simp only [sqrtDens, hũdef]
    rw [hX, sqrt_densNP hyp hpos]
  have hfvol : ∀ᵐ X ∂(volume : Measure (Config N d)), sqrtDens ν P X = ũ (flat X) :=
    (gibbs_ac hyp N).2.ae_le hfP
  have hflat : (sqrtDens ν P ∘ unflat) =ᵐ[volume] ũ := by
    rw [← map_flat_volume N]
    exact ae_map_flat_of_ae (p := fun y => (sqrtDens ν P ∘ unflat) y = ũ y) hfvol
  have hũ : IsWeakGrad ũ gũ := isWeakGrad_expPhi (N := N) hyp hs hpos c
  have hu : IsWeakGrad (sqrtDens ν P ∘ unflat) gũ := hũ.congr_ae hflat.symm
  have hwg := weakGrad_ae_eq hu
  obtain ⟨B, hB⟩ := PhiF_bdd (N := N) hyp hs hpos
  obtain ⟨Cg, hCg⟩ := gPhi_bdd (N := N) hyp hs hpos
  have hc0 : 0 ≤ c := Real.sqrt_nonneg _
  have hũb : ∀ y, |ũ y| ≤ c * Real.exp (B / 2) := fun y => by
    simp only [hũdef, abs_mul, abs_of_nonneg hc0, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith [(abs_le.mp (hB y)).2]))
      hc0
  have hgũb : ∀ y p, |gũ y p| ≤ c * (Real.exp (B / 2) / 2 * Cg) := fun y p => by
    simp only [hgũdef, abs_mul, abs_of_nonneg hc0, abs_div, abs_of_pos (Real.exp_pos _),
      abs_two]
    refine mul_le_mul_of_nonneg_left (mul_le_mul ?_ (hCg y p) (abs_nonneg _) (by positivity)) hc0
    exact div_le_div_of_nonneg_right (Real.exp_le_exp.mpr (by linarith [(abs_le.mp (hB y)).2]))
      (by norm_num)
  set Cs := Fintype.card (Fin N × Fin d) * (c * (Real.exp (B / 2) / 2 * Cg)) ^ 2
  have hsqb : ∀ y, sqNorm (gũ y) ≤ Cs := fun y => by
    unfold sqNorm
    calc ∑ p, gũ y p ^ 2 ≤ ∑ _p : Fin N × Fin d, (c * (Real.exp (B / 2) / 2 * Cg)) ^ 2 :=
          Finset.sum_le_sum fun p _ => by
            rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hgũb y p) 2
      _ = Cs := by simp [Cs]
  have hac := (gibbs_map_flat_ac hyp N).1
  have hH1 : MemH1C P (sqrtDens ν P) := by
    refine ⟨⟨gũ, hu⟩, ?_, ?_⟩
    · refine MemLp.of_bound (hu.aestronglyMeasurable_fun.mono_ac hac) (c * Real.exp (B / 2)) ?_
      filter_upwards [hac.ae_le hflat] with y hy
      rw [Real.norm_eq_abs, hy]; exact hũb y
    · refine MemLp.of_bound ((Real.continuous_sqrt.comp_aestronglyMeasurable
        (isWeakGrad_weakGrad ⟨gũ, hu⟩).aestronglyMeasurable_sqNorm).mono_ac hac)
        (Real.sqrt Cs) ?_
      filter_upwards [hac.ae_le hwg] with y hy
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), hy]
      exact Real.sqrt_le_sqrt (hsqb y)
  have hfish := fisherInfoC_eq hyp hνac
  rw [if_pos hH1] at hfish
  refine ⟨hH1, hfish, ?_⟩
  rw [hfish, energy_eq hyp ⟨gũ, hu⟩]
  -- reduce to an integral over `ν`
  have hS : AEStronglyMeasurable (fun X : Config N d => sqNorm (gPhi V W ρ N (flat X))) ν := by
    have h0 := (isWeakGrad_PhiF (N := N) hyp hs hpos).aestronglyMeasurable_sqNorm
    have hmp : MeasurePreserving (flat : Config N d → UnitAddTorus (Fin N × Fin d)) volume volume :=
      ⟨measurable_flat, map_flat_volume N⟩
    have h2 := h0.comp_measurePreserving hmp
    have hνvol : ν ≪ volume := by
      rw [hν, densMeasure, pi_withDensity_ofReal hρm hρ0 hρi]
      exact withDensity_absolutelyContinuous _ _
    exact h2.mono_ac hνvol
  have hSb : ∀ X : Config N d, |sqNorm (gPhi V W ρ N (flat X))| ≤
      Fintype.card (Fin N × Fin d) * Cg ^ 2 := fun X => by
    rw [abs_of_nonneg (sqNorm_nonneg _)]
    unfold sqNorm
    calc ∑ p, gPhi V W ρ N (flat X) p ^ 2 ≤ ∑ _p : Fin N × Fin d, Cg ^ 2 :=
          Finset.sum_le_sum fun p _ => by
            rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hCg _ p) 2
      _ = _ := by simp
  have hSi : Integrable (fun X : Config N d => sqNorm (gPhi V W ρ N (flat X))) ν :=
    Integrable.of_bound hS _ (Eventually.of_forall fun X => by rw [Real.norm_eq_abs]; exact hSb X)
  rw [ofReal_integral_eq_lintegral_ofReal hSi (Eventually.of_forall fun X => sqNorm_nonneg _)]
  have e1 : ∫⁻ y, ENNReal.ofReal (sqNorm (weakGrad (sqrtDens ν P ∘ unflat) y)) ∂(P.map flat) =
      ∫⁻ y, ENNReal.ofReal (sqNorm (gũ y)) ∂(P.map flat) :=
    lintegral_congr_ae (by filter_upwards [hac.ae_le hwg] with y hy; rw [hy])
  have hgm : AEMeasurable (fun y => ENNReal.ofReal (sqNorm (gũ y))) (P.map flat) :=
    (ENNReal.measurable_ofReal.comp_aemeasurable hũ.aestronglyMeasurable_sqNorm.aemeasurable).mono_ac
      hac
  rw [e1, lintegral_map' hgm measurable_flat.aemeasurable]
  have e2 : ∀ X : Config N d, ENNReal.ofReal (sqNorm (gũ (flat X))) =
      densNP V W ρ N X * ENNReal.ofReal (sqNorm (gPhi V W ρ N (flat X)) / 4) := fun X => by
    have hd : (densNP V W ρ N X).toReal = c ^ 2 * Real.exp (PhiF V W ρ N (flat X) / 2) ^ 2 := by
      have := sqrt_densNP (N := N) hyp hpos X
      rw [← Real.sq_sqrt (ENNReal.toReal_nonneg : 0 ≤ (densNP V W ρ N X).toReal), this]
      ring
    have hfin : densNP V W ρ N X = ENNReal.ofReal (densNP V W ρ N X).toReal := by
      rw [ENNReal.ofReal_toReal]; exact ENNReal.ofReal_ne_top
    rw [hfin, ← ENNReal.ofReal_mul ENNReal.toReal_nonneg, hd]
    congr 1
    simp only [sqNorm, hgũdef]
    rw [Finset.sum_div, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    ring
  simp_rw [e2]
  have hw := lintegral_withDensity_eq_lintegral_mul₀' (measurable_densNP hyp hρm).aemeasurable
    (g := fun X => ENNReal.ofReal (sqNorm (gPhi V W ρ N (flat X)) / 4))
    (by rw [← hνP]; exact (ENNReal.measurable_ofReal.comp_aemeasurable
      (hS.aemeasurable.div_const 4)))
  simp only [Pi.mul_apply] at hw
  rw [← hw, ← hνP, ← lintegral_const_mul' _ _ (by norm_num)]
  refine lintegral_congr fun X => ?_
  rw [show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by norm_num, ← ENNReal.ofReal_mul (by norm_num)]
  congr 1; ring

end SharpLSI
