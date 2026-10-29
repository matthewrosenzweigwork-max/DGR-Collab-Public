import FullLabeledLSI.Paper.Sec3RecFisher1
import SharpSymmetricLSI.Paper.ProductFisherDens

/-!
# Fisher information of products with nonidentical factors, II: density and the identity
`I(ν|P_N) = ∫ |∇Φ|² dν` for `ν = ⊗ᵢ ρᵢ`.
-/

noncomputable section
open MeasureTheory Set Filter Topology InformationTheory
open scoped ENNReal ContDiff

namespace SharpLSI.FL

open SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ} {N : ℕ}

/-- `dν_N/dP_N = Z_N ∏ ρᵢ(xᵢ) e^{H_N}`. -/
def densNPG (V : Torus d → ℝ) (W : Torus d → Torus d → ℝ) (ρs : Fin N → Torus d → ℝ)
    (X : Config N d) : ℝ≥0∞ :=
  ENNReal.ofReal (partitionFn V W N * (∏ i, ρs i (X i)) * Real.exp (hamiltonian V W N X))

theorem measurable_densNPG (hyp : Hyp V W KV KW) {ρs : Fin N → Torus d → ℝ}
    (hρm : ∀ i, Measurable (ρs i)) : Measurable (densNPG V W ρs) :=
  ENNReal.measurable_ofReal.comp ((measurable_const.mul (Finset.measurable_prod _ fun i _ =>
    (hρm i).comp (measurable_pi_apply i))).mul
      (Real.continuous_exp.comp (continuous_hamiltonian hyp N)).measurable)

theorem productState_eq_withDensity_gen (hyp : Hyp V W KV KW) {ρs : Fin N → Torus d → ℝ}
    (hρm : ∀ i, Measurable (ρs i)) (hρ0 : ∀ i x, 0 ≤ ρs i x)
    (hρi : ∀ i, Integrable (ρs i) (haar d)) :
    Measure.pi (fun i : Fin N => densMeasure (ρs i)) =
      (gibbs V W N).withDensity (densNPG V W ρs) := by
  have hZ := partitionFn_pos hyp N
  have hfm : Measurable fun X : Config N d =>
      ENNReal.ofReal (Real.exp (-hamiltonian V W N X) / partitionFn V W N) :=
    ENNReal.measurable_ofReal.comp ((Real.continuous_exp.comp
      (continuous_hamiltonian hyp N).neg).measurable.div_const _)
  have hmul := withDensity_mul (volume : Measure (Config N d)) hfm (measurable_densNPG hyp hρm)
  unfold densMeasure
  rw [pi_withDensity_ofReal_gen hρm hρ0 hρi, gibbs, ← hmul]
  congr 1
  funext X
  simp only [Pi.mul_apply, densNPG]
  rw [← ENNReal.ofReal_mul (div_nonneg (Real.exp_pos _).le hZ.le)]
  congr 1
  have : Real.exp (-hamiltonian V W N X) * Real.exp (hamiltonian V W N X) = 1 := by
    rw [← Real.exp_add]; simp
  symm
  calc _ = (∏ i, ρs i (X i)) * (Real.exp (-hamiltonian V W N X) * Real.exp (hamiltonian V W N X)) *
        (partitionFn V W N / partitionFn V W N) := by ring
    _ = _ := by rw [this, div_self hZ.ne']; ring

theorem rnDeriv_productState_gen (hyp : Hyp V W KV KW) {ρs : Fin N → Torus d → ℝ}
    (hρm : ∀ i, Measurable (ρs i)) (hρ0 : ∀ i x, 0 ≤ ρs i x)
    (hρi : ∀ i, Integrable (ρs i) (haar d)) :
    (Measure.pi fun i : Fin N => densMeasure (ρs i)).rnDeriv (gibbs V W N) =ᵐ[gibbs V W N]
      densNPG V W ρs := by
  have := gibbs_isProbabilityMeasure hyp N
  rw [productState_eq_withDensity_gen hyp hρm hρ0 hρi]
  exact Measure.rnDeriv_withDensity _ (measurable_densNPG hyp hρm)

theorem sqrt_densNPG (hyp : Hyp V W KV KW) {ρs : Fin N → Torus d → ℝ} (hpos : ∀ i x, 0 < ρs i x)
    (X : Config N d) :
    Real.sqrt (densNPG V W ρs X).toReal =
      Real.sqrt (partitionFn V W N) * Real.exp (PhiFG V W ρs (flat X) / 2) := by
  have hZ := partitionFn_pos hyp N
  have hp : 0 < ∏ i, ρs i (X i) := Finset.prod_pos fun i _ => hpos _ _
  set Φ := hamiltonian V W N X + ∑ i, Real.log (ρs i (X i)) with hΦ
  have e : partitionFn V W N * (∏ i, ρs i (X i)) * Real.exp (hamiltonian V W N X) =
      partitionFn V W N * (Real.exp (Φ / 2) * Real.exp (Φ / 2)) := by
    rw [← Real.exp_add, show Φ / 2 + Φ / 2 = Φ by ring, hΦ, Real.exp_add, Real.exp_sum,
      Finset.prod_congr rfl fun i _ => Real.exp_log (hpos i (X i))]
    ring
  rw [densNPG, e, ENNReal.toReal_ofReal (by positivity), Real.sqrt_mul hZ.le,
    Real.sqrt_mul_self (Real.exp_pos _).le, PhiFG_flat hyp]

/-- **(2.11), first step**: `f_N ∈ H¹(P_N)`, `I(ν_N|P_N) = 4ℰ_N(f_N) = ∫ |∇Φ|² dν_N`. -/
theorem fisher_productState_gen (hyp : Hyp V W KV KW) {ρs : Fin N → Torus d → ℝ}
    (hs : ∀ i, IsSmoothT (ρs i)) (hpos : ∀ i x, 0 < ρs i x) (h1 : ∀ i, ∫ x, ρs i x ∂haar d = 1) :
    MemH1C (gibbs V W N) (sqrtDens (Measure.pi fun i : Fin N => densMeasure (ρs i)) (gibbs V W N)) ∧
    fisherInfoC (Measure.pi fun i : Fin N => densMeasure (ρs i)) (gibbs V W N) =
      4 * energy V W N (sqrtDens (Measure.pi fun i : Fin N => densMeasure (ρs i)) (gibbs V W N)) ∧
    fisherInfoC (Measure.pi fun i : Fin N => densMeasure (ρs i)) (gibbs V W N) =
      ENNReal.ofReal (∫ X, sqNorm (gPhiG V W ρs (flat X))
        ∂(Measure.pi fun i : Fin N => densMeasure (ρs i))) := by
  set P := gibbs V W N with hP
  set ν := Measure.pi fun i : Fin N => densMeasure (ρs i) with hν
  have hPp := gibbs_isProbabilityMeasure hyp N
  have hρc : ∀ i, Continuous (ρs i) := fun i => (hs i).continuous
  have hρm : ∀ i, Measurable (ρs i) := fun i => (hρc i).measurable
  have hρ0 : ∀ i x, 0 ≤ ρs i x := fun i x => (hpos i x).le
  have hρi : ∀ i, Integrable (ρs i) (haar d) := fun i => integrable_of_continuous (hρc i)
  have : ∀ i, IsProbabilityMeasure (densMeasure (ρs i)) := fun i =>
    isProbabilityMeasure_densMeasure' (hρ0 i) (h1 i)
  have hZ := partitionFn_pos hyp N
  set c := Real.sqrt (partitionFn V W N)
  set ũ : UnitAddTorus (Fin N × Fin d) → ℝ := fun y => c * Real.exp (PhiFG V W ρs y / 2) with hũdef
  set gũ : UnitAddTorus (Fin N × Fin d) → Fin N × Fin d → ℝ :=
    fun y p => c * (Real.exp (PhiFG V W ρs y / 2) / 2 * gPhiG V W ρs y p) with hgũdef
  have hνP : ν = P.withDensity (densNPG V W ρs) := productState_eq_withDensity_gen hyp hρm hρ0 hρi
  have hνac : ν ≪ P := by rw [hνP]; exact withDensity_absolutelyContinuous _ _
  have hrn := rnDeriv_productState_gen hyp hρm hρ0 hρi
  have hfP : ∀ᵐ X ∂P, sqrtDens ν P X = ũ (flat X) := by
    filter_upwards [hrn] with X hX
    simp only [sqrtDens, hũdef]
    rw [hX, sqrt_densNPG hyp hpos]
  have hfvol : ∀ᵐ X ∂(volume : Measure (Config N d)), sqrtDens ν P X = ũ (flat X) :=
    (gibbs_ac hyp N).2.ae_le hfP
  have hflat : (sqrtDens ν P ∘ unflat) =ᵐ[volume] ũ := by
    rw [← map_flat_volume N]
    exact ae_map_flat_of_ae (p := fun y => (sqrtDens ν P ∘ unflat) y = ũ y) hfvol
  have hũ : IsWeakGrad ũ gũ := isWeakGrad_expPhiG hyp hs hpos c
  have hu : IsWeakGrad (sqrtDens ν P ∘ unflat) gũ := hũ.congr_ae hflat.symm
  have hwg := weakGrad_ae_eq hu
  obtain ⟨B, hB⟩ := PhiFG_bdd hyp hs hpos
  obtain ⟨Cg, hCg⟩ := gPhiG_bdd hyp hs hpos
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
  have hS : AEStronglyMeasurable (fun X : Config N d => sqNorm (gPhiG V W ρs (flat X))) ν := by
    have h0 := (isWeakGrad_PhiFG hyp hs hpos).aestronglyMeasurable_sqNorm
    have hmp : MeasurePreserving (flat : Config N d → UnitAddTorus (Fin N × Fin d)) volume volume :=
      ⟨measurable_flat, map_flat_volume N⟩
    have h2 := h0.comp_measurePreserving hmp
    have hνvol : ν ≪ volume := by
      rw [hν]
      unfold densMeasure
      rw [pi_withDensity_ofReal_gen hρm hρ0 hρi]
      exact withDensity_absolutelyContinuous _ _
    exact h2.mono_ac hνvol
  have hSb : ∀ X : Config N d, |sqNorm (gPhiG V W ρs (flat X))| ≤
      Fintype.card (Fin N × Fin d) * Cg ^ 2 := fun X => by
    rw [abs_of_nonneg (sqNorm_nonneg _)]
    unfold sqNorm
    calc ∑ p, gPhiG V W ρs (flat X) p ^ 2 ≤ ∑ _p : Fin N × Fin d, Cg ^ 2 :=
          Finset.sum_le_sum fun p _ => by
            rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hCg _ p) 2
      _ = _ := by simp
  have hSi : Integrable (fun X : Config N d => sqNorm (gPhiG V W ρs (flat X))) ν :=
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
      densNPG V W ρs X * ENNReal.ofReal (sqNorm (gPhiG V W ρs (flat X)) / 4) := fun X => by
    have hd : (densNPG V W ρs X).toReal = c ^ 2 * Real.exp (PhiFG V W ρs (flat X) / 2) ^ 2 := by
      have := sqrt_densNPG hyp hpos X
      rw [← Real.sq_sqrt (ENNReal.toReal_nonneg : 0 ≤ (densNPG V W ρs X).toReal), this]
      ring
    have hfin : densNPG V W ρs X = ENNReal.ofReal (densNPG V W ρs X).toReal := by
      rw [ENNReal.ofReal_toReal]; exact ENNReal.ofReal_ne_top
    rw [hfin, ← ENNReal.ofReal_mul ENNReal.toReal_nonneg, hd]
    congr 1
    simp only [sqNorm, hgũdef]
    rw [Finset.sum_div, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    ring
  simp_rw [e2]
  have hw := lintegral_withDensity_eq_lintegral_mul₀' (measurable_densNPG hyp hρm).aemeasurable
    (g := fun X => ENNReal.ofReal (sqNorm (gPhiG V W ρs (flat X)) / 4))
    (by rw [← hνP]; exact (ENNReal.measurable_ofReal.comp_aemeasurable
      (hS.aemeasurable.div_const 4)))
  simp only [Pi.mul_apply] at hw
  rw [← hw, ← hνP, ← lintegral_const_mul' _ _ (by norm_num)]
  refine lintegral_congr fun X => ?_
  rw [show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by norm_num, ← ENNReal.ofReal_mul (by norm_num)]
  congr 1; ring


end SharpLSI.FL
