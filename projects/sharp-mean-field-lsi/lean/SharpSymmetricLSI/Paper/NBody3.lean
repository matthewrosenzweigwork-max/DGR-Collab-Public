import SharpSymmetricLSI.Paper.NBody2

/-!
# The N-body eigen-identity in `H¹(μ^{⊗N})` (Phase 3, lane D; R29 groundwork)

`∫ ∑ₖ ∇_{(i,k)}Ψ · ∂_{(i,k)}T_c dμ^{⊗N} = λ_{c i} ∫ Ψ T_c dμ^{⊗N}` for every `Ψ ∈ H¹(μ^{⊗N})`, by
approximating `Ψ ∘ unflat` with its Fourier partial sums (`μ^{⊗N}` is comparable to Haar measure).
-/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-- `L²` convergence gives convergence of inner products. -/
theorem tendsto_integral_mul_of_L2 {α : Type*} [MeasurableSpace α] {P : Measure α}
    [IsProbabilityMeasure P] {f : ℕ → α → ℝ} {f0 g : α → ℝ} (hf : ∀ n, MemLp (f n) 2 P)
    (hf0 : MemLp f0 2 P) (hg : MemLp g 2 P)
    (h : Tendsto (fun n => ∫ x, (f n x - f0 x) ^ 2 ∂P) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, f n x * g x ∂P) atTop (𝓝 (∫ x, f0 x * g x ∂P)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hb : ∀ n, ‖∫ x, f n x * g x ∂P - ∫ x, f0 x * g x ∂P‖ ≤
      Real.sqrt (∫ x, (f n x - f0 x) ^ 2 ∂P) * Real.sqrt (∫ x, g x ^ 2 ∂P) := fun n => by
    have hi1 : Integrable (fun x => f n x * g x) P := (hf n).integrable_mul hg
    have hi2 : Integrable (fun x => f0 x * g x) P := hf0.integrable_mul hg
    rw [← integral_sub hi1 hi2, Real.norm_eq_abs]
    have hd : MemLp (fun x => f n x - f0 x) 2 P := (hf n).sub hf0
    calc |∫ x, (f n x * g x - f0 x * g x) ∂P| ≤ ∫ x, |f n x - f0 x| * |g x| ∂P := by
          refine (abs_integral_le_integral_abs).trans (le_of_eq (integral_congr_ae
            (Eventually.of_forall fun x => ?_)))
          simp only; rw [← sub_mul, abs_mul]
      _ ≤ _ := by
          have := integral_mul_le_Lp_mul_Lq_of_nonneg (p := 2) (q := 2) Real.HolderConjugate.two_two
            (Eventually.of_forall fun x => abs_nonneg (f n x - f0 x))
            (Eventually.of_forall fun x => abs_nonneg (g x)) (by rw [ENNReal.ofReal_ofNat]; exact hd.abs)
            (by rw [ENNReal.ofReal_ofNat]; exact hg.abs)
          simp only [Real.rpow_two, sq_abs, one_div] at this
          rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, one_div]
          exact this
  refine squeeze_zero (fun n => norm_nonneg _) hb ?_
  have := ((Real.continuous_sqrt.tendsto 0).comp h).mul_const (Real.sqrt (∫ x, g x ^ 2 ∂P))
  simpa using this

section main
variable (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
include hyp hμ

/-- `μ^{⊗N}` (flattened) is comparable to Haar measure. -/
theorem minimizer_pi_comparison (N : ℕ) : ∃ a b : ℝ, 0 < a ∧ 0 < b ∧
    (volume : Measure (UnitAddTorus (Fin N × Fin d))) ≤
      ENNReal.ofReal a • (Measure.pi fun _ : Fin N => (μ : Measure (Torus d))).map flat ∧
    (Measure.pi fun _ : Fin N => (μ : Measure (Torus d))).map flat ≤
      ENNReal.ofReal b • (volume : Measure (UnitAddTorus (Fin N × Fin d))) := by
  obtain ⟨c, C, L, hc, hb⟩ := elDensity_bounds hyp
  have hρ := (hb (μ : Measure (Torus d)) inferInstance).1
  have hLip := (hb (μ : Measure (Torus d)) inferInstance).2
  set ρ := elDens V W (μ : Measure (Torus d))
  have hρm : Measurable ρ := hLip.continuous.measurable
  have hC : 0 < C := lt_of_lt_of_le hc ((hρ 0).1.trans (hρ 0).2)
  have hρi : Integrable ρ (haar d) :=
    Integrable.of_bound hρm.aestronglyMeasurable C (Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg (hc.le.trans (hρ x).1)]; exact (hρ x).2)
  have hpi : Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))) =
      (volume : Measure (Config N d)).withDensity (fun X => ENNReal.ofReal (∏ i, ρ (X i))) := by
    rw [minimizer_eq_elDensity hyp hμ]
    exact pi_withDensity_ofReal hρm (fun x => hc.le.trans (hρ x).1) hρi
  have hprod : ∀ X : Config N d, c ^ N ≤ ∏ i, ρ (X i) ∧ ∏ i, ρ (X i) ≤ C ^ N := fun X => by
    constructor
    · calc c ^ N = ∏ _i : Fin N, c := by simp
        _ ≤ ∏ i, ρ (X i) := Finset.prod_le_prod₀ (fun _ _ => hc.le) fun i _ => (hρ _).1
    · calc ∏ i, ρ (X i) ≤ ∏ _i : Fin N, C :=
            Finset.prod_le_prod₀ (fun i _ => hc.le.trans (hρ _).1) fun i _ => (hρ _).2
        _ = C ^ N := by simp
  have hmeas : Measurable (flat (N := N) (d := d)) := measurable_flat
  refine ⟨(1 / c) ^ N, C ^ N, by positivity, by positivity, Measure.le_iff.mpr fun t ht => ?_,
    Measure.le_iff.mpr fun t ht => ?_⟩
  · rw [Measure.smul_apply, smul_eq_mul, Measure.map_apply hmeas ht, hpi,
      withDensity_apply _ (hmeas ht)]
    have hv : (volume : Measure (UnitAddTorus (Fin N × Fin d))) t = volume (flat ⁻¹' t) := by
      rw [← map_flat_volume N, Measure.map_apply hmeas ht]
    rw [hv]
    calc volume (flat ⁻¹' t) = ENNReal.ofReal ((1 / c) ^ N) * (ENNReal.ofReal (c ^ N) *
          volume (flat ⁻¹' t)) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), ← mul_pow, one_div_mul_cancel
            hc.ne', one_pow, ENNReal.ofReal_one, one_mul]
      _ ≤ _ := by
          gcongr
          rw [← setLIntegral_const]
          exact lintegral_mono fun X => ENNReal.ofReal_le_ofReal (hprod X).1
  · rw [Measure.smul_apply, smul_eq_mul, Measure.map_apply hmeas ht, hpi,
      withDensity_apply _ (hmeas ht)]
    have hv : (volume : Measure (UnitAddTorus (Fin N × Fin d))) t = volume (flat ⁻¹' t) := by
      rw [← map_flat_volume N, Measure.map_apply hmeas ht]
    rw [hv, ← setLIntegral_const]
    exact lintegral_mono fun X => ENNReal.ofReal_le_ofReal (hprod X).2

/-- **The N-body eigen-identity** for `Ψ ∈ H¹(μ^{⊗N})` and a tensor `T_c`. -/
theorem eigen_tensor_H1 {e : ℕ → Torus d → ℝ} {lam : ℕ → ℝ}
    (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam) {N : ℕ} {Ψ : Config N d → ℝ}
    (hΨ : MemH1C (Measure.pi fun _ : Fin N => (μ : Measure (Torus d))) Ψ) (c : Fin N → ℕ)
    (i : Fin N) :
    ∫ X, ∑ k, weakGradC Ψ X i k * tensorGrad e c i k X
        ∂(Measure.pi fun _ : Fin N => (μ : Measure (Torus d))) =
      lam (c i) * ∫ X, Ψ X * ∏ j, e (c j) (X j)
        ∂(Measure.pi fun _ : Fin N => (μ : Measure (Torus d))) := by
  set μm := (μ : Measure (Torus d))
  set P := Measure.pi fun _ : Fin N => μm
  set P' := P.map flat
  have : IsProbabilityMeasure P' :=
    (Measure.isProbabilityMeasure_map_iff measurable_flat.aemeasurable).mpr inferInstance
  obtain ⟨a, b, ha0, hb0, ha, hb⟩ := minimizer_pi_comparison hyp hμ (N := N)
  have hac : μm ≪ haar d := minimizer_ac hyp hμ
  set u : UnitAddTorus (Fin N × Fin d) → ℝ := Ψ ∘ unflat
  have huH : MemH1 P' u := hΨ
  have huV : MemLp u 2 volume := memLp_vol ha huH
  set g := weakGrad u
  have hw : IsWeakGrad u g := isWeakGrad_weakGrad huH.1
  have hgV : ∀ p, MemLp (fun y => g y p) 2 volume := memLp_grad_vol ha hb huH
  -- pull back along `flat`
  have hpull : ∀ h : UnitAddTorus (Fin N × Fin d) → ℝ, MemLp h 2 volume →
      MemLp (fun X => h (flat X)) 2 P := fun h hh =>
    (measurableEmbedding_flat.memLp_map_measure_iff).mp
      (hh.of_measure_le_smul ENNReal.ofReal_ne_top hb)
  have hint_pull : ∀ h : UnitAddTorus (Fin N × Fin d) → ℝ, MemLp h 2 volume →
      ∫ X, h (flat X) ^ 2 ∂P ≤ b * ∫ y, h y ^ 2 := fun h hh => by
    have e1 : ∫ X, h (flat X) ^ 2 ∂P = ∫ y, h y ^ 2 ∂P' :=
      (integral_map measurable_flat.aemeasurable
        ((hh.of_measure_le_smul ENNReal.ofReal_ne_top hb).aestronglyMeasurable.pow 2)).symm
    rw [e1]
    exact integral_le_smul_of_le hb0.le hb (fun y => sq_nonneg _) hh.integrable_sq
  -- the partial sums
  set Fs : ℕ → UnitAddTorus (Fin N × Fin d) → ℝ := fun R => psum (cf u) R
  have hFs : ∀ R, ContDiff ℝ 1 (Fs R ∘ liftT) := fun R => (contDiff_psum _ R).of_le (by simp)
  have hcg : ∀ R Y p, cgrad (Fs R) Y p = psum (cf fun y => g y p) R Y := fun R Y p => by
    unfold cgrad
    rw [fderiv_psum, liftT_secT]
    congr 1
    funext k
    exact (mFourierCoeff_grad hw (huV.integrable one_le_two)
      (fun q => (hgV q).integrable one_le_two) k p).symm
  have hsm := fun R => eigen_tensor_smooth_i hac he (hFs R) c i
  -- convergences
  have hT : MemLp (fun X : Config N d => ∏ j, e (c j) (X j)) 2 P :=
    memLp_prod_eval fun j => he.memLp _
  have htg : ∀ k, MemLp (tensorGrad e c i k) 2 P := fun k => by
    unfold tensorGrad
    refine memLp_prod_eval (f := fun j => (Function.update (fun j => e (c j)) i
      (fun x => weakGrad (e (c i)) x k)) j) fun j => ?_
    by_cases hj : j = i
    · subst hj; rw [Function.update_self]; exact memLp_grad_comp hac (he.memH1 _) k
    · rw [Function.update_of_ne hj]; exact he.memLp _
  have hconvF : Tendsto (fun R => ∫ X, (Fs R (flat X) - Ψ X) ^ 2 ∂P) atTop (𝓝 0) := by
    refine squeeze_zero (fun R => integral_nonneg fun _ => sq_nonneg _) (fun R =>
      hint_pull (fun y => Fs R y - u y) ((memLp_psum _ R 2).sub huV)) ?_
    have := (tendsto_psum_sq huV).const_mul b
    simpa using this
  have hconvG : ∀ k, Tendsto (fun R => ∫ X, (cgrad (Fs R) (flat X) (i, k) -
      weakGradC Ψ X i k) ^ 2 ∂P) atTop (𝓝 0) := fun k => by
    have e : ∀ R, ∫ X, (cgrad (Fs R) (flat X) (i, k) - weakGradC Ψ X i k) ^ 2 ∂P =
        ∫ X, (psum (cf fun y => g y (i, k)) R (flat X) - g (flat X) (i, k)) ^ 2 ∂P := fun R => by
      congr 1; funext X; rw [hcg]; rfl
    simp_rw [e]
    refine squeeze_zero (fun R => integral_nonneg fun _ => sq_nonneg _) (fun R =>
      hint_pull (fun y => psum (cf fun y => g y (i, k)) R y - g y (i, k))
        ((memLp_psum _ R 2).sub (hgV _))) ?_
    have := (tendsto_psum_sq (hgV (i, k))).const_mul b
    simpa using this
  have hL : Tendsto (fun R => ∫ X, ∑ k, cgrad (Fs R) (flat X) (i, k) * tensorGrad e c i k X ∂P)
      atTop (𝓝 (∫ X, ∑ k, weakGradC Ψ X i k * tensorGrad e c i k X ∂P)) := by
    have hcgL : ∀ R k, MemLp (fun X => cgrad (Fs R) (flat X) (i, k)) 2 P := fun R k => by
      have e : (fun X : Config N d => cgrad (Fs R) (flat X) (i, k)) =
          fun X => psum (cf fun y => g y (i, k)) R (flat X) := funext fun X => hcg R _ _
      rw [e]; exact hpull _ (memLp_psum _ R 2)
    have hwgL : ∀ k, MemLp (fun X => weakGradC Ψ X i k) 2 P := fun k => hpull _ (hgV (i, k))
    have h1 : ∀ R, ∫ X, ∑ k, cgrad (Fs R) (flat X) (i, k) * tensorGrad e c i k X ∂P =
        ∑ k, ∫ X, cgrad (Fs R) (flat X) (i, k) * tensorGrad e c i k X ∂P := fun R =>
      integral_finsetSum _ fun k _ => (hcgL R k).integrable_mul (htg k)
    simp_rw [h1]
    rw [integral_finsetSum (f := fun k X => weakGradC Ψ X i k * tensorGrad e c i k X) _
      fun k _ => (hwgL k).integrable_mul (htg k)]
    exact tendsto_finsetSum _ fun k _ =>
      tendsto_integral_mul_of_L2 (fun R => hcgL R k) (hwgL k) (htg k) (hconvG k)
  have hR : Tendsto (fun R => lam (c i) * ∫ X, Fs R (flat X) * ∏ j, e (c j) (X j) ∂P) atTop
      (𝓝 (lam (c i) * ∫ X, Ψ X * ∏ j, e (c j) (X j) ∂P)) :=
    (tendsto_integral_mul_of_L2 (fun R => hpull _ (memLp_psum _ R 2)) (hpull _ huV) hT
      hconvF).const_mul _
  exact tendsto_nhds_unique (hL.congr fun R => hsm R) hR

end main

end SharpLSI
