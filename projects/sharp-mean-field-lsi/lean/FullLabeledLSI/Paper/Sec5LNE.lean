import FullLabeledLSI.Paper.Sec5LNB
import FullLabeledLSI.Paper.Sec5LNC

/-!
# Large-N assembly E: L3, reference LSI
-/

open MeasureTheory Filter Topology InformationTheory ProbabilityTheory
open scoped ENNReal

namespace SharpLSI.FL

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-! ## 5. L3: every `h_j` is bounded by the relative score -/

section L3
variable {N : ℕ} {ν : Measure (Config N d)} {Q : Config N d → ℝ} {c C : ℝ}
  {GQ : UnitAddTorus (Fin N × Fin d) → Fin N × Fin d → ℝ} {s : Fin N → Fin d → Config N d → ℝ}
  {bF : Torus d → Torus d → Fin d → ℝ} {bΔ : Torus d → Fin d → ℝ} {Bb : ℝ}

/-- `avg1R` is monotone in the (relevant part of the) function. -/
theorem avg1R_mono_E {N j : ℕ} (hj : j < N) (F G : Finset (Fin N) → Fin N → ℝ)
    (h : ∀ S ∈ (Finset.univ : Finset (Fin N)).powersetCard j, ∀ i ∈ Sᶜ, F S i ≤ G S i) :
    avg1R N j F ≤ avg1R N j G := by
  have _ := hj
  unfold avg1R
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine Finset.sum_le_sum fun S hS => mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact Finset.sum_le_sum fun i hi => h S hS i hi

/-- The reference LSI constant: `exists_klDiv_le_reference` restated with `RefLSI`
(PROVED by `exact`; the two statements are definitionally equal). -/
theorem exists_refLSI (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)}
    (hμ : IsMinimizer V W μ) : ∃ A : ℝ, 0 < A ∧ RefLSI V W (μ : Measure (Torus d)) A :=
  exists_klDiv_le_reference hyp hμ

/-- **Per `(S,i)`:** `E_ν H(ρ_{S,i}(X_S)|μ) ≤ A E_ν |s_i - G_i|²`.
Proof: reference LSI `hA` for the slice `ρ_{S,i}(a)` (a.e. `a`, `ae_isBddH1Dens_condDensS`) gives
`H(ρ|μ) ≤ A ∫ρ|g/ρ + ∇Φ|²`; integrate in `ν` and use `lintegral_pair_eq_lintegral_condDensS`
(`F(a,x) = |g/ρ + ∇Φ|²(a,x)`), `condScore_ae_eq` (`g/ρ + ∇Φ = E[s - G|𝒢]`), and
`SharpLSI.integral_sq_condExp_le`.  Same structure as `hCond_le_sG` (Defective24).  ~90 lines. -/
theorem integral_klDiv_condLawS_le (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)}
    (hμ : IsMinimizer V W μ) [IsProbabilityMeasure ν]
    (hS : ScoreData V W (μ : Measure (Torus d)) ν Q c C GQ s bF bΔ Bb) {A : ℝ} (hA0 : 0 < A)
    (hA : RefLSI V W (μ : Measure (Torus d)) A) {S : Finset (Fin N)} {i : Fin N} (hi : i ∉ S) :
    ∫ X, (klDiv (condLawS ν S i (restrictS S X)) (μ : Measure (Torus d))).toReal ∂ν ≤
      A * ∫ X, ∑ k : Fin d, (s i k X - Gpart bF bΔ N X i k) ^ 2 ∂ν := by
  classical
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
      lipGrad (PhiMF V W (μ : Measure (Torus d))) x k) ^ 2 with hRf
  have hRm : Measurable (Function.uncurry Rf) := by
    unfold Function.uncurry
    refine Finset.measurable_sum _ fun k _ => Measurable.pow_const ?_ 2
    exact ((measurable_gradCondS hQ (S := S) (i := i) hS.gradM k).div
      (measurable_condDensS hQ S i)).add
      ((measurable_lipGrad (continuous_PhiMF hyp) k).comp measurable_snd)
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
      condDensS Q S i (restrictS S X) (X i) + lipGrad (PhiMF V W (μ : Measure (Torus d))) (X i) k =
      condExp (revSigma S i) ν (fun Y => s i k Y - Gpart bF bΔ N Y i k) X :=
    ae_all_iff.mpr fun k => condScore_ae_eq hyp hμ hS hi k
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
  by_cases hm : AEStronglyMeasurable
      (fun X => (klDiv (condLawS ν S i (restrictS S X)) (μ : Measure (Torus d))).toReal) ν
  · rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun X => ENNReal.toReal_nonneg) hm]
    calc _ ≤ (ENNReal.ofReal (A * T)).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top
            ((lintegral_mono fun X => ENNReal.ofReal_toReal_le).trans h4)
      _ = A * T := ENNReal.toReal_ofReal (mul_nonneg hA0.le hT0)
  · rw [integral_non_aestronglyMeasurable hm]
    exact mul_nonneg hA0.le hT0

/-- **L3.  Every level:** `h_j ≤ A (1/N) Σ_i E_ν|s_i - G_i|²` (`j < N`).
Proof: `hRev_toReal_eq`, `integral_klDiv_condLawS_le` for each `(S,i)`, monotonicity of `avg1R`, and
`avg1R_const_S` for the `S`-independent function `i ↦ ∫|s_i - G_i|²`.  ~30 lines. -/
theorem hRev_toReal_le (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)}
    (hμ : IsMinimizer V W μ) [IsProbabilityMeasure ν]
    (hS : ScoreData V W (μ : Measure (Torus d)) ν Q c C GQ s bF bΔ Bb) {A : ℝ} (hA0 : 0 < A)
    (hA : RefLSI V W (μ : Measure (Torus d)) A) {j : ℕ} (hj : j < N) :
    (hRev ν (μ : Measure (Torus d)) j).toReal ≤
      A * ((N : ℝ)⁻¹ * ∑ i, ∫ X, ∑ k : Fin d, (s i k X - Gpart bF bΔ N X i k) ^ 2 ∂ν) := by
  rw [hRev_toReal_eq hyp hμ hS hj]
  calc _ ≤ avg1R N j (fun _ i => A * ∫ X, ∑ k : Fin d,
          (s i k X - Gpart bF bΔ N X i k) ^ 2 ∂ν) :=
        avg1R_mono_E hj _ _ fun S _ i hi =>
          integral_klDiv_condLawS_le hyp hμ hS hA0 hA (Finset.mem_compl.mp hi)
    _ = A * avg1R N j (fun _ i => ∫ X, ∑ k : Fin d,
          (s i k X - Gpart bF bΔ N X i k) ^ 2 ∂ν) := avg1R_const_mul' N j A _
    _ = _ := by rw [avg1R_const_S N j hj (fun i => ∫ X, ∑ k : Fin d,
          (s i k X - Gpart bF bΔ N X i k) ^ 2 ∂ν)]

/-- **`Σ_i E|s_i - G_i|² ≤ 2 I + 2 E|∇U_N|²`.**  `(a-b)² ≤ 2a² + 2b²`; `Σ_i Σ_k Gpart² = gradSqC (Ucentered)`
ν-a.e. (`hS.G_ae`, `ν ≪ volume`); `hGG` says the lintegral of `gradSqC` is finite (supplied by
`reference_all_aux`); convert with `integral_eq_lintegral_of_nonneg_ae`.  ~50 lines. -/
theorem sum_sG_le (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)}
    (hμ : IsMinimizer V W μ) [IsProbabilityMeasure ν]
    (hS : ScoreData V W (μ : Measure (Torus d)) ν Q c C GQ s bF bΔ Bb)
    (hGG : ∫⁻ X, ENNReal.ofReal (gradSqC (Ucentered W (μ : Measure (Torus d)) N) X) ∂ν ≠ ⊤) :
    ∑ i, ∫ X, ∑ k : Fin d, (s i k X - Gpart bF bΔ N X i k) ^ 2 ∂ν ≤
      2 * fisherS ν s + 2 * (∫⁻ X, ENNReal.ofReal
        (gradSqC (Ucentered W (μ : Measure (Torus d)) N) X) ∂ν).toReal := by
  classical
  have hGm : ∀ i k, Measurable fun X : Config N d => Gpart bF bΔ N X i k := fun i k =>
    measurable_Gpart hS.force i k
  have hGi : ∀ i k, Integrable (fun X => Gpart bF bΔ N X i k ^ 2) ν := fun i k =>
    Integrable.of_bound ((hGm i k).pow_const 2).aestronglyMeasurable
      (((N : ℝ)⁻¹ * ((N : ℝ) * Bb + Bb)) ^ 2) (Eventually.of_forall fun X => by
        rw [Real.norm_eq_abs, abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (abs_Gpart_le hS.force X i k) 2)
  have hsi : ∀ i k, Integrable (fun X => s i k X ^ 2) ν := hS.sL2
  have hDi : ∀ i k, Integrable (fun X => (s i k X - Gpart bF bΔ N X i k) ^ 2) ν := fun i k => by
    refine Integrable.mono' (((hsi i k).add (hGi i k)).const_mul 2)
      (((hS.sM i k).sub (hGm i k)).pow_const 2).aestronglyMeasurable
      (Eventually.of_forall fun X => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    simp only [Pi.add_apply]
    nlinarith [sq_nonneg (s i k X + Gpart bF bΔ N X i k)]
  have hper : ∀ i, ∫ X, ∑ k : Fin d, (s i k X - Gpart bF bΔ N X i k) ^ 2 ∂ν ≤
      2 * ∑ k, ∫ X, s i k X ^ 2 ∂ν + 2 * ∫ X, ∑ k : Fin d, Gpart bF bΔ N X i k ^ 2 ∂ν := by
    intro i
    have hA1 : Integrable (fun X => ∑ k : Fin d, s i k X ^ 2) ν :=
      integrable_finsetSum _ fun k _ => hsi i k
    have hA2 : Integrable (fun X => ∑ k : Fin d, Gpart bF bΔ N X i k ^ 2) ν :=
      integrable_finsetSum _ fun k _ => hGi i k
    calc _ ≤ ∫ X, (2 * ∑ k : Fin d, s i k X ^ 2 + 2 * ∑ k : Fin d, Gpart bF bΔ N X i k ^ 2) ∂ν := by
          refine integral_mono (integrable_finsetSum _ fun k _ => hDi i k)
            ((hA1.const_mul 2).add (hA2.const_mul 2)) fun X => ?_
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_le_sum fun k _ => ?_
          nlinarith [sq_nonneg (s i k X + Gpart bF bΔ N X i k)]
      _ = _ := by
          rw [integral_add (hA1.const_mul 2) (hA2.const_mul 2), integral_const_mul,
            integral_const_mul, integral_finsetSum _ fun k _ => hsi i k]
  have hG : ∑ i, ∫ X, ∑ k : Fin d, Gpart bF bΔ N X i k ^ 2 ∂ν =
      (∫⁻ X, ENNReal.ofReal (gradSqC (Ucentered W (μ : Measure (Torus d)) N) X) ∂ν).toReal := by
    rw [← integral_finsetSum _ fun i _ => integrable_finsetSum _ fun k _ => hGi i k]
    have hnn : 0 ≤ᵐ[ν] fun X => ∑ i, ∑ k : Fin d, Gpart bF bΔ N X i k ^ 2 :=
      Eventually.of_forall fun X => Finset.sum_nonneg fun i _ =>
        Finset.sum_nonneg fun k _ => sq_nonneg _
    have hmeas : AEStronglyMeasurable (fun X => ∑ i, ∑ k : Fin d, Gpart bF bΔ N X i k ^ 2) ν :=
      (Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun k _ =>
        (hGm i k).pow_const 2).aestronglyMeasurable
    rw [integral_eq_lintegral_of_nonneg_ae hnn hmeas]
    congr 1
    refine lintegral_congr_ae ?_
    have hac : ν ≪ (volume : Measure (Config N d)) := by
      rw [hS.eq]; exact withDensity_absolutelyContinuous _ _
    filter_upwards [hac.ae_le hS.G_ae] with X hX
    congr 1
    unfold gradSqC
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by rw [hX i k]
  calc _ ≤ ∑ i, (2 * ∑ k, ∫ X, s i k X ^ 2 ∂ν + 2 * ∫ X, ∑ k : Fin d, Gpart bF bΔ N X i k ^ 2 ∂ν) :=
        Finset.sum_le_sum fun i _ => hper i
    _ = 2 * fisherS ν s + 2 * ∑ i, ∫ X, ∑ k : Fin d, Gpart bF bΔ N X i k ^ 2 ∂ν := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        rfl
    _ = _ := by rw [hG]

end L3


end SharpLSI.FL
