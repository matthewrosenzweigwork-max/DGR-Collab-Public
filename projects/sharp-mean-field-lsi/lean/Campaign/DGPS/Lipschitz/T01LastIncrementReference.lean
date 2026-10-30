import DGPS.Lipschitz.T01ReferenceLSI
import DGPS.Lipschitz.T01ConditionalInformation

/-!
# The actual last-increment reference entropy bound

The conditional score cancellation uses the current Lipschitz frozen potential and the factual
score data of the regularized law. The actual frozen reference LSI and finite joint entropy
then bound every last increment by the averaged relative score energy.
-/

open MeasureTheory Filter Topology InformationTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace DGPS.Lipschitz

open SharpLSI SharpLSI.FL

section

variable {d N : ℕ} {ν : Measure (Config N d)} {Q : Config N d → ℝ} {c C : ℝ}
  {GQ : UnitAddTorus (Fin N × Fin d) → Fin N × Fin d → ℝ}
  {s : Fin N → Fin d → Config N d → ℝ}
  {bF : Torus d → Torus d → Fin d → ℝ} {bΔ : Torus d → Fin d → ℝ} {Bb : ℝ}

/-- Conditional score cancellation for the actual direct-Lipschitz frozen potential. -/
theorem actual_condScore_ae_eq (J : InteractionData d) (hJ : LipschitzData J)
    (μ : ProbabilityMeasure (Torus d)) [IsFiniteMeasure ν]
    (hS : ScoreData J.V J.W (μ : Measure (Torus d)) ν Q c C GQ s bF bΔ Bb)
    {S : Finset (Fin N)} {i : Fin N} (hi : i ∉ S) (k : Fin d) :
    (fun X => gradCondS Q GQ S i (restrictS S X) (X i) k / condDensS Q S i (restrictS S X) (X i) +
        lipGrad (PhiMF J.V J.W (μ : Measure (Torus d))) (X i) k) =ᵐ[ν]
      condExp (revSigma S i) ν (fun Y => s i k Y - Gpart bF bΔ N Y i k) := by
  classical
  have hQ := hS.dens
  have hGi : Integrable (fun y => GQ y (i, k)) volume := (hS.gradL2 _).integrable one_le_two
  have hle : revSigma S i ≤ (inferInstance : MeasurableSpace (Config N d)) :=
    ((measurable_restrictS S).prodMk (measurable_pi_apply i)).comap_le
  have h1 := score_ae_eq_condExp hQ hi hS.eq hS.gradM k hGi
  obtain ⟨L0, hL0, hΦ⟩ := lipschitz_equilibriumPotential J hJ
  have hΦL : TorusLipschitzWith L0 (PhiMF J.V J.W μ) := hΦ (μ : Measure (Torus d))
  let L : ℝ≥0 := Real.toNNReal (L0 * Real.sqrt d)
  have hL : LipschitzWith L (PhiMF J.V J.W μ ∘ liftT) :=
    DGPS.RelativeFisher.lipschitzWith_comp_lift hΦL
  have hΦc : Continuous (PhiMF J.V J.W μ) := frozenPotential_continuous J μ
  have hLm : Measurable fun x => lipGrad (PhiMF J.V J.W (μ : Measure (Torus d))) x k :=
    measurable_lipGrad (hΦc) k
  set Lf : Config N d → ℝ := fun X => lipGrad (PhiMF J.V J.W (μ : Measure (Torus d))) (X i) k with hLf
  have hLfm : Measurable Lf := hLm.comp (measurable_pi_apply i)
  have hLf𝒢 : StronglyMeasurable[revSigma S i] Lf :=
    (hLm.comp (measurable_snd.comp
      (comap_measurable (fun X : Config N d => (restrictS S X, X i))))).stronglyMeasurable
  have hLfi : Integrable Lf ν :=
    Integrable.of_bound hLfm.aestronglyMeasurable (L : ℝ) (Eventually.of_forall fun X => by
      rw [Real.norm_eq_abs]; exact abs_lipGrad_le hL (X i) k)
  have hsi : Integrable (s i k) ν := by
    have : MemLp (s i k) 2 ν :=
      (memLp_two_iff_integrable_sq (hS.sM i k).aestronglyMeasurable).mpr (hS.sL2 i k)
    exact this.integrable one_le_two
  have hGp : Integrable (fun Y => Gpart bF bΔ N Y i k) ν :=
    Integrable.of_bound (measurable_Gpart hS.force i k).aestronglyMeasurable
      ((N : ℝ)⁻¹ * ((N : ℝ) * Bb + Bb)) (Eventually.of_forall fun X => by
        rw [Real.norm_eq_abs]; exact abs_Gpart_le hS.force X i k)
  have hsG : Integrable (fun Y => s i k Y - Gpart bF bΔ N Y i k) ν := hsi.sub hGp
  have hF : (fun Y : Config N d => GQ (flat Y) (i, k) / Q Y) =ᵐ[ν]
      fun Y => (s i k Y - Gpart bF bΔ N Y i k) - Lf Y := by
    filter_upwards [hS.score] with X hX
    exact hX i k
  have h2 := condExp_congr_ae (m := revSigma S i) hF
  have h3 : ν[fun Y => s i k Y - Gpart bF bΔ N Y i k - Lf Y | revSigma S i] =ᵐ[ν]
      ν[fun Y => s i k Y - Gpart bF bΔ N Y i k | revSigma S i] - ν[Lf | revSigma S i] :=
    condExp_sub hsG hLfi (revSigma S i)
  have h4 : ν[Lf | revSigma S i] = Lf := condExp_of_stronglyMeasurable hle hLf𝒢 hLfi
  filter_upwards [h1, h2, h3] with X a b c
  rw [a, b]
  simp only [Pi.sub_apply] at c
  rw [c, h4]
  simp only [hLf]
  ring

private theorem actual_integral_klDiv_condLawS_le (J : InteractionData d) (hJ : LipschitzData J)
    (μ : ProbabilityMeasure (Torus d)) [IsProbabilityMeasure ν]
    (hS : ScoreData J.V J.W (μ : Measure (Torus d)) ν Q c C GQ s bF bΔ Bb) {A : ℝ} (hA0 : 0 < A)
    (hA : RefLSI J.V J.W (μ : Measure (Torus d)) A) {S : Finset (Fin N)} {i : Fin N} (hi : i ∉ S) :
    ∫ X, (klDiv (condLawS ν S i (restrictS S X)) (μ : Measure (Torus d))).toReal ∂ν ≤
      A * ∫ X, ∑ k : Fin d, (s i k X - Gpart bF bΔ N X i k) ^ 2 ∂ν := by
  classical
  have hΦc : Continuous (PhiMF J.V J.W μ) := frozenPotential_continuous J μ
  have hQ := hS.dens
  have hν := hS.eq
  have hle : revSigma S i ≤ (inferInstance : MeasurableSpace (Config N d)) :=
    ((measurable_restrictS S).prodMk (measurable_pi_apply i)).comap_le
  have hGm : ∀ k, Measurable fun X : Config N d => Gpart bF bΔ N X i k := fun k =>
    measurable_Gpart hS.force i k
  have hD : ∀ k, MemLp (fun Y => s i k Y - Gpart bF bΔ N Y i k) 2 ν := fun k => by
    have h1 : MemLp (s i k) 2 ν :=
      (memLp_two_iff_integrable_sq (hS.sM i k).aestronglyMeasurable).mpr (hS.sL2 i k)
    have h2 : MemLp (fun Y => Gpart bF bΔ N Y i k) 2 ν :=
      MemLp.of_bound (hGm k).aestronglyMeasurable ((N : ℝ)⁻¹ * ((N : ℝ) * Bb + Bb))
        (Eventually.of_forall fun X => by
          rw [Real.norm_eq_abs]; exact abs_Gpart_le hS.force X i k)
    exact h1.sub h2
  set T : ℝ := ∫ X, ∑ k : Fin d, (s i k X - Gpart bF bΔ N X i k) ^ 2 ∂ν with hT
  have hT0 : 0 ≤ T := integral_nonneg fun X => Finset.sum_nonneg fun k _ => sq_nonneg _
  set Rf : (S → Torus d) → Torus d → ℝ := fun a x => ∑ k : Fin d,
    (gradCondS Q GQ S i a x k / condDensS Q S i a x +
      lipGrad (PhiMF J.V J.W (μ : Measure (Torus d))) x k) ^ 2 with hRf
  have hRm : Measurable (Function.uncurry Rf) := by
    unfold Function.uncurry
    refine Finset.measurable_sum _ fun k _ => Measurable.pow_const ?_ 2
    exact ((measurable_gradCondS hQ (S := S) (i := i) hS.gradM k).div
      (measurable_condDensS hQ S i)).add
      ((measurable_lipGrad (hΦc) k).comp measurable_snd)
  have hFm : Measurable (Function.uncurry fun a x => ENNReal.ofReal (Rf a x)) :=
    ENNReal.measurable_ofReal.comp hRm
  -- the reference LSI on a.e. slice
  have hb : ∀ᵐ X ∂ν, ∀ i' ∈ Sᶜ, IsBddH1Dens (condDensS Q S i' (restrictS S X))
      (gradCondS Q GQ S i' (restrictS S X)) (c / C) (C / c) := by
    rw [hν]; exact ae_restrictS_of_ae_volume S hQ.meas (ae_isBddH1Dens_condDensS hS S)
  have h1 : ∀ᵐ X ∂ν, klDiv (condLawS ν S i (restrictS S X)) (μ : Measure (Torus d)) ≤
      ENNReal.ofReal A * ∫⁻ x, ENNReal.ofReal (condDensS Q S i (restrictS S X) x *
        Rf (restrictS S X) x) ∂haar d := by
    filter_upwards [hb, condLawS_ae_eq_X hQ hi hν] with X hX hcl
    rw [hcl]
    have hX' := hX i (Finset.mem_compl.mpr hi)
    exact hA hX'.meas hX'.grad
      (fun k => (measurable_gradCondS hQ (S := S) (i := i) hS.gradM k).of_uncurry_left)
      hX'.grad_L2 hX'.pos hX'.ge hX'.le hX'.int_one
  have hρ0 : ∀ a x, 0 ≤ condDensS Q S i a x := fun a x =>
    ((div_pos hQ.pos (hQ.pos.trans_le ((hQ.lower 0).trans (hQ.upper 0)))).le).trans
      (condDensS_bounds hQ S i a x).1
  have h2 : ∫⁻ X, klDiv (condLawS ν S i (restrictS S X)) (μ : Measure (Torus d)) ∂ν ≤
      ENNReal.ofReal A * ∫⁻ X, ENNReal.ofReal (Rf (restrictS S X) (X i)) ∂ν := by
    calc _ ≤ ∫⁻ X, ENNReal.ofReal A * ∫⁻ x, ENNReal.ofReal (condDensS Q S i (restrictS S X) x *
            Rf (restrictS S X) x) ∂haar d ∂ν := lintegral_mono_ae h1
      _ = ENNReal.ofReal A * ∫⁻ X, ∫⁻ x, ENNReal.ofReal (condDensS Q S i (restrictS S X) x) *
            ENNReal.ofReal (Rf (restrictS S X) x) ∂haar d ∂ν := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          congr 1
          refine lintegral_congr fun X => lintegral_congr fun x => ?_
          rw [ENNReal.ofReal_mul (hρ0 _ _)]
      _ = _ := by
          rw [← lintegral_pair_eq_lintegral_condDensS hQ hν hi
            (F := fun a x => ENNReal.ofReal (Rf a x)) hFm]
  -- score identity and conditional Jensen
  have hsc : ∀ᵐ X ∂ν, ∀ k, gradCondS Q GQ S i (restrictS S X) (X i) k /
      condDensS Q S i (restrictS S X) (X i) + lipGrad (PhiMF J.V J.W (μ : Measure (Torus d))) (X i) k =
      condExp (revSigma S i) ν (fun Y => s i k Y - Gpart bF bΔ N Y i k) X :=
    ae_all_iff.mpr fun k => actual_condScore_ae_eq J hJ μ hS hi k
  have hEi : ∀ k, Integrable (fun X => (condExp (revSigma S i) ν
      (fun Y => s i k Y - Gpart bF bΔ N Y i k) X) ^ 2) ν := fun k =>
    (MemLp.condExp (m := revSigma S i) one_le_two (hD k)).integrable_sq
  have hEJ : ∀ k, ∫ X, (condExp (revSigma S i) ν
      (fun Y => s i k Y - Gpart bF bΔ N Y i k) X) ^ 2 ∂ν ≤
      ∫ X, (s i k X - Gpart bF bΔ N X i k) ^ 2 ∂ν := fun k =>
    integral_sq_condExp_le hle (hD k)
  have hDi : ∀ k, Integrable (fun X => (s i k X - Gpart bF bΔ N X i k) ^ 2) ν := fun k =>
    (hD k).integrable_sq
  have h3 : ∫⁻ X, ENNReal.ofReal (Rf (restrictS S X) (X i)) ∂ν ≤ ENNReal.ofReal T := by
    have e1 : ∫⁻ X, ENNReal.ofReal (Rf (restrictS S X) (X i)) ∂ν =
        ∫⁻ X, ENNReal.ofReal (∑ k, (condExp (revSigma S i) ν
          (fun Y => s i k Y - Gpart bF bΔ N Y i k) X) ^ 2) ∂ν := by
      refine lintegral_congr_ae ?_
      filter_upwards [hsc] with X hX
      congr 1
      exact Finset.sum_congr rfl fun k _ => by rw [hX k]
    rw [e1, ← ofReal_integral_eq_lintegral_ofReal (integrable_finsetSum _ fun k _ => hEi k)
      (Eventually.of_forall fun X => Finset.sum_nonneg fun k _ => sq_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [integral_finsetSum _ fun k _ => hEi k, hT, integral_finsetSum _ fun k _ => hDi k]
    exact Finset.sum_le_sum fun k _ => hEJ k
  have h4 : ∫⁻ X, klDiv (condLawS ν S i (restrictS S X)) (μ : Measure (Torus d)) ∂ν ≤
      ENNReal.ofReal (A * T) := by
    rw [ENNReal.ofReal_mul hA0.le]
    exact h2.trans (mul_le_mul' le_rfl h3)
  have hm := measurable_klDiv_condLawS ν (μ : Measure (Torus d)) S i
  have hfin : (∫⁻ X, klDiv (condLawS ν S i (restrictS S X))
      (μ : Measure (Torus d)) ∂ν) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top h4
  rw [integral_toReal hm.aemeasurable (ae_lt_top hm hfin)]
  calc _ ≤ (ENNReal.ofReal (A * T)).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top h4
    _ = A * T := ENNReal.toReal_ofReal (mul_nonneg hA0.le hT0)

/-- A fixed reference LSI constant controls every particle number and score law. -/
theorem actual_last_increment_reference_bound_of_refLSI (J : InteractionData d)
    (hJ : LipschitzData J) (μ : ProbabilityMeasure (Torus d)) [IsProbabilityMeasure ν]
    (hS : ScoreData J.V J.W (μ : Measure (Torus d)) ν Q c C GQ s bF bΔ Bb)
    (hH : klDiv ν (Measure.pi fun _ : Fin N => (μ : Measure (Torus d))) ≠ ⊤)
    {Aref : ℝ} (hA0 : 0 < Aref) (hA : RefLSI J.V J.W (μ : Measure (Torus d)) Aref) :
    ∀ j : ℕ, j < N → (hRev ν (μ : Measure (Torus d)) j).toReal ≤
      Aref * ((N : ℝ)⁻¹ * ∑ i, ∫ X, ∑ k : Fin d,
        (s i k X - Gpart bF bΔ N X i k) ^ 2 ∂ν) := by
  intro j hj
  rw [hRev_toReal_eq_of_finite_entropy ν (μ : Measure (Torus d)) hH hj]
  calc
    _ ≤ avg1R N j (fun _ i => Aref * ∫ X, ∑ k : Fin d,
        (s i k X - Gpart bF bΔ N X i k) ^ 2 ∂ν) :=
      avg1R_mono_E hj _ _ fun S _ i hi =>
        actual_integral_klDiv_condLawS_le J hJ μ hS hA0 hA (Finset.mem_compl.mp hi)
    _ = Aref * avg1R N j (fun _ i => ∫ X, ∑ k : Fin d,
        (s i k X - Gpart bF bΔ N X i k) ^ 2 ∂ν) := avg1R_const_mul' N j Aref _
    _ = _ := by
      rw [avg1R_const_S N j hj (fun i => ∫ X, ∑ k : Fin d,
        (s i k X - Gpart bF bΔ N X i k) ^ 2 ∂ν)]


/-- The actual reference LSI controls each last-increment information, on the genuine score data. -/
theorem actual_last_increment_reference_bound (J : InteractionData d) (hJ : LipschitzData J)
    (μ : ProbabilityMeasure (Torus d))
    (hfix : (frozenGibbs J μ).measure = (μ : Measure (Torus d))) [IsProbabilityMeasure ν]
    (hS : ScoreData J.V J.W (μ : Measure (Torus d)) ν Q c C GQ s bF bΔ Bb)
    (hH : klDiv ν (Measure.pi fun _ : Fin N => (μ : Measure (Torus d))) ≠ ⊤) :
    ∃ Aref : ℝ, 0 < Aref ∧ ∀ j : ℕ, j < N →
      (hRev ν (μ : Measure (Torus d)) j).toReal ≤
        Aref * ((N : ℝ)⁻¹ * ∑ i, ∫ X, ∑ k : Fin d,
          (s i k X - Gpart bF bΔ N X i k) ^ 2 ∂ν) := by
  obtain ⟨Aref, hA0, hA⟩ := exists_actual_refLSI J hJ μ hfix
  exact ⟨Aref, hA0, actual_last_increment_reference_bound_of_refLSI J hJ μ hS hH hA0 hA⟩

/-- The conditional mean-field score square is integrable for every unrevealed-label average. -/
theorem actual_meanfield_score_square_integrable {V : Torus d → ℝ}
    {W : Torus d → Torus d → ℝ} {μ : Measure (Torus d)} [IsProbabilityMeasure ν]
    (hS : ScoreData V W μ ν Q c C GQ s bF bΔ Bb)
    (S : Finset (Fin N)) (hS1 : 1 ≤ Sᶜ.card) (i : Fin N) :
    Integrable (fun X => ∑ k : Fin d,
      (condExp (revSigma S i) ν (fun Y => s i k Y - Gpart bF bΔ N Y i k) X +
        BS bF ν S X (X i) k) ^ 2) ν := by
  have hsm : ∀ k, MemLp (fun Y => s i k Y - Gpart bF bΔ N Y i k) 2 ν := by
    intro k
    have hs : MemLp (s i k) 2 ν :=
      (memLp_two_iff_integrable_sq (hS.sM i k).aestronglyMeasurable).2 (hS.sL2 i k)
    have hG : MemLp (fun Y => Gpart bF bΔ N Y i k) 2 ν :=
      MemLp.of_bound (measurable_Gpart hS.force i k).aestronglyMeasurable
        ((N : ℝ)⁻¹ * ((N : ℝ) * Bb + Bb)) (Eventually.of_forall fun X => by
          rw [Real.norm_eq_abs]
          exact abs_Gpart_le hS.force X i k)
    exact hs.sub hG
  have hBS : ∀ k, MemLp (fun X => BS bF ν S X (X i) k) 2 ν := fun k =>
    MemLp.of_bound (measurable_BS_comp hS.force ν S i k).aestronglyMeasurable Bb
      (Eventually.of_forall fun X => by
        rw [Real.norm_eq_abs]
        exact abs_BS_le hS.force ν S hS1 X (X i) k)
  exact integrable_finsetSum _ fun k _ =>
    (((hsm k).condExp one_le_two).add (hBS k)).integrable_sq

end

end DGPS.Lipschitz
