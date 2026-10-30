import FullLabeledLSI.Paper.Prop23SchroB
import FullLabeledLSI.Paper.Prop23SchroC
import FullLabeledLSI.Infra.SpectralEnergy
import DGPS.Lipschitz.T01ReferenceEigenbasis

/-!
# The finite-rank ground-state identity under explicit reference bounds

This extracts the differential argument from `FormLiminf2`--`FormLiminf4` and
`Prop23SchroB`. The reference eigen-equation and the two measure bounds replace the
old semiconvex package. No particle lower bound is assumed.
-/

open MeasureTheory Filter Topology Real
open scoped ENNReal

namespace DGPS.Lipschitz.GroundState

open SharpLSI SharpLSI.FL

variable {d : ℕ} {μ : ProbabilityMeasure (Torus d)}
  {e eC : ℕ → Torus d → ℝ} {lam : ℕ → ℝ}

section Eigen

variable (hac : (μ : Measure (Torus d)) ≪ haar d)
  (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam)
  (hφ : ∀ j, ContDiff ℝ 1 (eC j ∘ liftT)) (heC : ∀ j, eC j =ᵐ[haar d] e j)
include hac he hφ heC

/-- The weak eigenvalue equation for a `C¹` test function, with the `C¹` representatives. -/
theorem eigen_C1 (i : ℕ) {ψ : Torus d → ℝ} (hψ : ContDiff ℝ 1 (ψ ∘ liftT)) :
    ∫ y, ∑ k, cgrad ψ y k * cgrad (eC i) y k ∂(μ : Measure (Torus d)) =
      lam i * ∫ y, eC i y * ψ y ∂(μ : Measure (Torus d)) := by
  have hw : ∀ m, ∀ᵐ x ∂(μ : Measure (Torus d)), weakGrad (e m) x = fun k => cgrad (eC m) x k :=
    fun m => hac.ae_le (weakGrad_ae_eq ((isWeakGrad_of_contDiff (hφ m)).congr_ae (heC m)))
  have hψw : ∀ᵐ x ∂(μ : Measure (Torus d)), weakGrad ψ x = fun k => cgrad ψ x k :=
    hac.ae_le (weakGrad_ae_eq (isWeakGrad_of_contDiff hψ))
  have hP : IsProbabilityMeasure (μ : Measure (Torus d)) := inferInstance
  have hH1 : SharpLSI.MemH1 (μ : Measure (Torus d)) ψ := memH1_of_contDiff_ac hac hψ
  have h := he.eigen i ψ hH1
  have h1 : ∫ y, ∑ k, cgrad ψ y k * cgrad (eC i) y k ∂(μ : Measure (Torus d)) =
      ∫ x, ∑ k, weakGrad (e i) x k * weakGrad ψ x k ∂(μ : Measure (Torus d)) := by
    refine integral_congr_ae ?_
    filter_upwards [hw i, hψw] with x h1 h2
    rw [h1, h2]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  have h2 : ∫ y, eC i y * ψ y ∂(μ : Measure (Torus d)) = ∫ x, e i x * ψ x ∂(μ : Measure (Torus d)) := by
    refine integral_congr_ae ?_
    filter_upwards [hac.ae_le (heC i)] with x hx
    rw [hx]
  rw [h1, h, h2]

/-- **The eigenvalue equation in the variable `X_l`** (smooth case). -/
theorem eigen_slice_smooth {N : ℕ} (l : Fin N) (i : ℕ) {Φ : UnitAddTorus (Fin N × Fin d) → ℝ}
    (hΦ : ContDiff ℝ 1 (Φ ∘ liftT)) :
    ∫ X, ∑ k, cgrad Φ (flat X) (l, k) * cgrad (eC i) (X l) k
        ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))) =
      lam i * ∫ X, eC i (X l) * Φ (flat X) ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))) := by
  set μm := (μ : Measure (Torus d))
  obtain ⟨CΦ, hCΦ⟩ := exists_bound_cgrad hΦ
  obtain ⟨BΦ, hBΦ⟩ := exists_bound_of_contDiff hΦ
  obtain ⟨Ce, hCe⟩ := exists_bound_cgrad (hφ i)
  obtain ⟨Be, hBe⟩ := exists_bound_of_contDiff (hφ i)
  have hmΦ : Measurable Φ := measurable_of_contDiff hΦ
  have hgm : Measurable fun X : Config N d =>
      ∑ k, cgrad Φ (flat X) (l, k) * cgrad (eC i) (X l) k :=
    Finset.measurable_sum _ fun k _ => ((measurable_cgrad hΦ (l, k)).comp measurable_flat).mul
      ((measurable_cgrad (hφ i) k).comp (measurable_pi_apply l))
  have hfm : Measurable fun X : Config N d => eC i (X l) * Φ (flat X) :=
    ((measurable_of_contDiff (hφ i)).comp (measurable_pi_apply l)).mul (hmΦ.comp measurable_flat)
  have hgi : Integrable (fun X : Config N d => ∑ k, cgrad Φ (flat X) (l, k) * cgrad (eC i) (X l) k)
      (Measure.pi fun _ : Fin N => μm) :=
    integrable_of_bdd hgm (C := d * (|CΦ| * |Ce|)) fun X => by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ k, |cgrad Φ (flat X) (l, k) * cgrad (eC i) (X l) k| ≤ ∑ _k : Fin d, |CΦ| * |Ce| :=
            Finset.sum_le_sum fun k _ => by
              rw [abs_mul]
              exact mul_le_mul ((hCΦ _ _).trans (le_abs_self _)) ((hCe _ _).trans (le_abs_self _))
                (abs_nonneg _) (abs_nonneg _)
        _ = d * (|CΦ| * |Ce|) := by simp
  have hfi : Integrable (fun X : Config N d => eC i (X l) * Φ (flat X))
      (Measure.pi fun _ : Fin N => μm) :=
    integrable_of_bdd hfm (C := |Be| * |BΦ|) fun X => by
      rw [abs_mul]
      exact mul_le_mul ((hBe _).trans (le_abs_self _)) ((hBΦ _).trans (le_abs_self _))
        (abs_nonneg _) (abs_nonneg _)
  rw [integral_update_resample μm l hgi, integral_update_resample μm l hfi, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun X => ?_)
  simp only [Function.update_self]
  have hs := eigen_C1 hac he hφ heC i (contDiff_sliceF hΦ X l)
  simp only [cgrad_sliceF hΦ X l] at hs
  exact hs

end Eigen

section Density

variable {Cu : ℝ}
  (hup : (μ : Measure (Torus d)) ≤ ENNReal.ofReal Cu • (haar d))
include hup

theorem integrable_pi_comp {N : ℕ} {B : UnitAddTorus (Fin N × Fin d) → ℝ} (hB : Integrable B volume)
    {c : Config N d → ℝ} (hc : Measurable c) {Cc : ℝ} (hCc : ∀ X, |c X| ≤ Cc) :
    Integrable (fun X => B (flat X) * c X) (Measure.pi fun _ : Fin N => (μ : Measure (Torus d))) := by
  let C : ℝ≥0∞ := ENNReal.ofReal Cu ^ N
  have hC : C ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  have hle : Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))) ≤
      C • (volume : Measure (Config N d)) :=
    SharpLSI.FL.Spectral.pi_le_smul_pi hup N
  have hmp : MeasurePreserving (flat : Config N d → UnitAddTorus (Fin N × Fin d)) volume volume :=
    ⟨measurable_flat, map_flat_volume N⟩
  have h1 : Integrable (fun X => B (flat X)) (volume : Measure (Config N d)) :=
    (hmp.integrable_comp hB.aestronglyMeasurable).2 hB
  have h2 := (h1.smul_measure hC).mono_measure hle
  exact h2.mul_bdd hc.aestronglyMeasurable (Eventually.of_forall fun X => by
    rw [Real.norm_eq_abs]; exact hCc X)

/-- Transfer of `L¹(vol)` convergence on `𝕋^{N×d}` to integrals under `μ^{⊗N}` against bounded
weights. -/
theorem tendsto_integral_pi_of_L1 {N : ℕ} {A : ℕ → UnitAddTorus (Fin N × Fin d) → ℝ}
    {A0 : UnitAddTorus (Fin N × Fin d) → ℝ} (hA : ∀ n, Integrable (A n) volume)
    (hA0 : Integrable A0 volume) (hlim : Tendsto (fun n => ∫⁻ y, ‖A n y - A0 y‖ₑ) atTop (𝓝 0))
    {c : Config N d → ℝ} (hc : Measurable c) {Cc : ℝ} (hCc : ∀ X, |c X| ≤ Cc) :
    Tendsto (fun n => ∫ X, A n (flat X) * c X ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))))
      atTop (𝓝 (∫ X, A0 (flat X) * c X ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))))) := by
  let C : ℝ≥0∞ := ENNReal.ofReal Cu ^ N
  have hC : C ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  have hle : Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))) ≤
      C • (volume : Measure (Config N d)) :=
    SharpLSI.FL.Spectral.pi_le_smul_pi hup N
  have hmp : MeasurePreserving (flat : Config N d → UnitAddTorus (Fin N × Fin d)) volume volume :=
    ⟨measurable_flat, map_flat_volume N⟩
  have hint : ∀ {B : UnitAddTorus (Fin N × Fin d) → ℝ}, Integrable B volume →
      Integrable (fun X => B (flat X) * c X) (Measure.pi fun _ : Fin N => (μ : Measure (Torus d))) :=
    fun {B} hB => by
      have h1 : Integrable (fun X => B (flat X)) (volume : Measure (Config N d)) :=
        (hmp.integrable_comp hB.aestronglyMeasurable).2 hB
      have h2 := (h1.smul_measure hC).mono_measure hle
      exact h2.mul_bdd hc.aestronglyMeasurable (Eventually.of_forall fun X => by
        rw [Real.norm_eq_abs]; exact hCc X)
  refine tendsto_integral_of_L1 _ (hint hA0).aestronglyMeasurable (Eventually.of_forall fun n => hint (hA n)) ?_
  have hCc0 : 0 ≤ Cc := (abs_nonneg _).trans (hCc 0)
  have hbound : ∀ n, ∫⁻ X, ‖A n (flat X) * c X - A0 (flat X) * c X‖ₑ
      ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))) ≤
      C * ENNReal.ofReal Cc * ∫⁻ y, ‖A n y - A0 y‖ₑ := fun n => by
    calc ∫⁻ X, ‖A n (flat X) * c X - A0 (flat X) * c X‖ₑ
          ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d)))
        ≤ ∫⁻ X, ENNReal.ofReal Cc * ‖A n (flat X) - A0 (flat X)‖ₑ
          ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))) := by
          refine lintegral_mono fun X => ?_
          rw [← sub_mul, enorm_mul, mul_comm]
          gcongr
          rw [Real.enorm_eq_ofReal_abs]
          exact ENNReal.ofReal_le_ofReal (hCc X)
      _ ≤ ∫⁻ X, ENNReal.ofReal Cc * ‖A n (flat X) - A0 (flat X)‖ₑ ∂(C • volume) :=
          lintegral_mono' hle le_rfl
      _ = C * (ENNReal.ofReal Cc * ∫⁻ X, ‖A n (flat X) - A0 (flat X)‖ₑ ∂volume) := by
          rw [lintegral_smul_measure, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, smul_eq_mul]
      _ = C * ENNReal.ofReal Cc * ∫⁻ y, ‖A n y - A0 y‖ₑ := by
          rw [mul_assoc, hmp.lintegral_comp_emb (flatEquiv N d).measurableEmbedding
            (fun y => ‖A n y - A0 y‖ₑ)]
  have h0 : Tendsto (fun n => C * ENNReal.ofReal Cc * ∫⁻ y, ‖A n y - A0 y‖ₑ) atTop (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul (a := C * ENNReal.ofReal Cc) hlim
      (Or.inr (ENNReal.mul_ne_top hC ENNReal.ofReal_ne_top))
    rwa [mul_zero] at this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h0 (fun _ => bot_le) hbound

end Density

private theorem ae_pi_of_ae_volume
    (hac : (μ : Measure (Torus d)) ≪ haar d) {N : ℕ}
    {p : UnitAddTorus (Fin N × Fin d) → Prop}
    (h : ∀ᵐ y ∂(volume : Measure (UnitAddTorus (Fin N × Fin d))), p y) :
    ∀ᵐ X ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))), p (flat X) := by
  have hmp : MeasurePreserving (flat : Config N d → UnitAddTorus (Fin N × Fin d)) volume volume :=
    ⟨measurable_flat, map_flat_volume N⟩
  exact (pi_ac_volume hac N).ae_le (hmp.quasiMeasurePreserving.ae h)

section EigenSlice

variable {Cu : ℝ}
  (hup : (μ : Measure (Torus d)) ≤ ENNReal.ofReal Cu • (haar d))
  (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam)
  (hφ : ∀ j, ContDiff ℝ 1 (eC j ∘ liftT)) (heC : ∀ j, eC j =ᵐ[haar d] e j)
include hup he hφ heC

/-- **`∫ ∇_lΦ · ∇e_i(X_l) dμ^{⊗N} = λ_i ∫ e_i(X_l) Φ dμ^{⊗N}`** for `Φ ∈ W^{1,1}`. -/
theorem eigen_slice {N : ℕ} (l : Fin N) (i : ℕ) {Φ : UnitAddTorus (Fin N × Fin d) → ℝ}
    {G : UnitAddTorus (Fin N × Fin d) → Fin N × Fin d → ℝ} (hΦ : IsWeakGrad Φ G)
    (hΦi : Integrable Φ volume) (hGi : ∀ p, Integrable (fun y => G y p) volume) :
    ∫ X, ∑ k, G (flat X) (l, k) * cgrad (eC i) (X l) k
        ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))) =
      lam i * ∫ X, Φ (flat X) * eC i (X l) ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))) := by
  have hac : (μ : Measure (Torus d)) ≪ haar d :=
    Measure.absolutelyContinuous_of_le_smul hup
  set μm := (μ : Measure (Torus d))
  obtain ⟨F, Gs, hFs, hFw, hFm, hGm, hF1, hG1⟩ := exists_smooth_approx hΦ hΦi hGi
  have hF1' : ∀ n, ContDiff ℝ 1 (F n ∘ liftT) := fun n => (hFs n).of_le (by simp)
  obtain ⟨Ce, hCe⟩ := exists_bound_cgrad (hφ i)
  obtain ⟨Be, hBe⟩ := exists_bound_of_contDiff (hφ i)
  have hcm : ∀ k : Fin d, Measurable fun X : Config N d => cgrad (eC i) (X l) k := fun k =>
    (measurable_cgrad (hφ i) k).comp (measurable_pi_apply l)
  have hem : Measurable fun X : Config N d => eC i (X l) :=
    (measurable_of_contDiff (hφ i)).comp (measurable_pi_apply l)
  -- the smooth approximants: classical gradient = `Gs n` a.e.
  have hGae : ∀ n, (fun y => cgrad (F n) y) =ᵐ[volume] Gs n := fun n =>
    (weakGrad_ae_eq (isWeakGrad_of_contDiff (hF1' n))).symm.trans (weakGrad_ae_eq (hFw n))
  have hFint : ∀ n, Integrable (F n) volume := fun n => by
    obtain ⟨B, hB⟩ := exists_bound_of_contDiff (hF1' n)
    exact integrable_of_bdd_meas (hFm n) hB
  have hGint : ∀ n p, Integrable (fun y => Gs n y p) volume := fun n p => by
    obtain ⟨B, hB⟩ := exists_bound_cgrad (hF1' n)
    refine (integrable_of_bdd_meas (measurable_cgrad (hF1' n) p) fun y => hB y p).congr ?_
    filter_upwards [hGae n] with y hy
    exact congrFun hy p
  -- the identity for each `n`
  have hn : ∀ n, ∑ k, ∫ X, Gs n (flat X) (l, k) * cgrad (eC i) (X l) k ∂Measure.pi (fun _ : Fin N => μm) =
      lam i * ∫ X, F n (flat X) * eC i (X l) ∂Measure.pi (fun _ : Fin N => μm) := fun n => by
    have h := eigen_slice_smooth hac he hφ heC l i (hF1' n)
    rw [← integral_finsetSum _ fun k _ => integrable_pi_comp hup (hGint n (l, k)) (hcm k)
      fun X => (hCe _ _)]
    have hae := ae_pi_of_ae_volume hac (hGae n)
    rw [← integral_congr_ae (hae.mono fun X hX =>
      Finset.sum_congr rfl fun k _ => by rw [← congrFun hX (l, k)]), h]
    congr 1
    exact integral_congr_ae (Eventually.of_forall fun X => mul_comm _ _)
  -- limits
  have hL : Tendsto (fun n => ∑ k, ∫ X, Gs n (flat X) (l, k) * cgrad (eC i) (X l) k
      ∂Measure.pi (fun _ : Fin N => μm)) atTop
      (𝓝 (∑ k, ∫ X, G (flat X) (l, k) * cgrad (eC i) (X l) k ∂Measure.pi (fun _ : Fin N => μm))) :=
    tendsto_finset_sum _ fun k _ => tendsto_integral_pi_of_L1 hup (fun n => hGint n (l, k))
      (hGi (l, k)) (hG1 (l, k)) (hcm k) fun X => hCe _ _
  have hR : Tendsto (fun n => lam i * ∫ X, F n (flat X) * eC i (X l)
      ∂Measure.pi (fun _ : Fin N => μm)) atTop
      (𝓝 (lam i * ∫ X, Φ (flat X) * eC i (X l) ∂Measure.pi (fun _ : Fin N => μm))) :=
    (tendsto_integral_pi_of_L1 hup hFint hΦi hF1 hem fun X => hBe _).const_mul _
  rw [integral_finsetSum _ fun k _ => integrable_pi_comp hup (hGi (l, k)) (hcm k)
    fun X => hCe _ _]
  exact tendsto_nhds_unique (hL.congr hn) hR

end EigenSlice

section Schrodinger

variable {W : Torus d → Torus d → ℝ} {Cu Cl : ℝ}
  (hup : (μ : Measure (Torus d)) ≤ ENNReal.ofReal Cu • (haar d))
  (hlow : haar d ≤ ENNReal.ofReal Cl • (μ : Measure (Torus d)))
  (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam)
  (hφ : ∀ j, ContDiff ℝ 1 (eC j ∘ liftT)) (heC : ∀ j, eC j =ᵐ[haar d] e j)
include hup hlow he hφ heC

theorem eigen_slice_sq_mul (A : FiniteRankApprox W (μ : Measure (Torus d)) e) (R : ℕ) {N : ℕ}
    (hN : 1 ≤ N) {Ψ : Config N d → ℝ} (hΨ : MemH1C (QN (μ : Measure (Torus d)) N) Ψ)
    (l : Fin N) (i : ℕ) :
    ∫ X, ∑ k : Fin d, (2 * Ψ X * weakGradC Ψ X l k) * TR A R (fun n => fluct eC N n X) i *
        cgrad (eC (i + 1)) (X l) k ∂QN (μ : Measure (Torus d)) N +
      ∫ X, Ψ X ^ 2 * ((N : ℝ) ^ (-(1 / 2 : ℝ)) * ∑ j ∈ A.s R, A.a R i j *
        ∑ k : Fin d, cgrad (eC (j + 1)) (X l) k * cgrad (eC (i + 1)) (X l) k)
          ∂QN (μ : Measure (Torus d)) N =
      lam (i + 1) * ∫ X, Ψ X ^ 2 * TR A R (fun n => fluct eC N n X) i * eC (i + 1) (X l)
        ∂QN (μ : Measure (Torus d)) N := by
  classical
  simp only [SharpLSI.FL.QN] at hΨ ⊢
  set P : Measure (Config N d) := Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))) with hP
  have : IsProbabilityMeasure (P.map flat) :=
    (Measure.isProbabilityMeasure_map_iff measurable_flat.aemeasurable).mpr inferInstance
  have huH : SharpLSI.MemH1 (P.map flat) (Ψ ∘ unflat) := hΨ
  have hdata := SharpLSI.FL.Spectral.h1_flat_data hlow hΨ
  have huV : MemLp (Ψ ∘ unflat) 2 volume := hdata.1
  have hw := isWeakGrad_weakGrad huH.1
  have hgV : ∀ p, MemLp (fun y => weakGrad (Ψ ∘ unflat) y p) 2 volume :=
    hdata.2
  have hsq := isWeakGrad_sq hw huV hgV
  set c : ℝ := (N : ℝ) ^ (-(1 / 2 : ℝ)) with hc
  obtain ⟨hhw, hhm, ⟨B, hB⟩, hghm, ⟨L, hL⟩⟩ :=
    blockSum_data (φ := fun j => eC (j + 1)) (fun j => hφ (j + 1)) (A.s R)
      (fun j => c * A.a R i j) N
  have hug : ∀ p, Integrable (fun y => 2 * (Ψ ∘ unflat) y * weakGrad (Ψ ∘ unflat) y p) volume :=
    fun p => ((huV.integrable_mul (hgV p)).const_mul 2).congr
      (Eventually.of_forall fun y => by simp only [Pi.mul_apply]; ring)
  have hprod := hsq.mul_lip huV.integrable_sq hug hhw hhm hB hghm hL
  have hbB : ∀ᵐ y : UnitAddTorus (Fin N × Fin d) ∂volume,
      ‖∑ j ∈ A.s R, c * A.a R i j * ∑ b : Fin N, eC (j + 1) (projBlock b y)‖ ≤ B :=
    Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hB y
  have hΦi := huV.integrable_sq.mul_bdd hhm.aestronglyMeasurable hbB
  have hGi : ∀ p, Integrable (fun y =>
      2 * (Ψ ∘ unflat) y * weakGrad (Ψ ∘ unflat) y p *
          (∑ j ∈ A.s R, c * A.a R i j * ∑ b : Fin N, eC (j + 1) (projBlock b y)) +
        (Ψ ∘ unflat) y ^ 2 * ∑ j ∈ A.s R, c * A.a R i j * cgrad (eC (j + 1)) (projBlock p.1 y) p.2)
      volume := fun p =>
    ((hug p).mul_bdd hhm.aestronglyMeasurable hbB).add
      (huV.integrable_sq.mul_bdd (hghm p).aestronglyMeasurable
        (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hL y p))
  have key := eigen_slice hup he hφ heC l (i + 1) hprod hΦi hGi
  -- `X`-level functions
  set hf : Config N d → ℝ := fun X => ∑ j ∈ A.s R, c * A.a R i j * ∑ b : Fin N, eC (j + 1) (X b) with hhf
  set ghf : Config N d → Fin d → ℝ := fun X k =>
    ∑ j ∈ A.s R, c * A.a R i j * cgrad (eC (j + 1)) (X l) k with hghf
  have key' : ∫ X, ∑ k : Fin d, ((2 * Ψ X * weakGradC Ψ X l k) * hf X + Ψ X ^ 2 * ghf X k) *
        cgrad (eC (i + 1)) (X l) k ∂P =
      lam (i + 1) * ∫ X, Ψ X ^ 2 * hf X * eC (i + 1) (X l) ∂P := key
  have hTR : ∀ X : Config N d, TR A R (fun n => fluct eC N n X) i = hf X := fun X => by
    simp only [TR, fluct, hhf, hc]
    exact Finset.sum_congr rfl fun j _ => by ring
  simp only [hTR]
  have hcgb : ∀ j k, BddF (fun x : Torus d => cgrad (eC j) x k) := fun j k =>
    ⟨(exists_bound_cgrad (hφ j)).choose, fun x => (exists_bound_cgrad (hφ j)).choose_spec x k⟩
  have hcgm : ∀ j k, Measurable (fun X : Config N d => cgrad (eC j) (X l) k) := fun j k =>
    (measurable_cgrad (hφ j) k).comp (measurable_pi_apply l)
  have hPsi : MemLp Ψ 2 P := memLp_of_memH1C_pi hΨ
  have hhfm : Measurable hf := hhm.comp measurable_flat
  have hhfb : BddF hf := ⟨B, fun X => hB (flat X)⟩
  have hA : ∀ k, Integrable (fun X => (2 * Ψ X * weakGradC Ψ X l k) * hf X *
      cgrad (eC (i + 1)) (X l) k) P := by
    intro k
    obtain ⟨C, hC⟩ := (hhfb.const_mul 2).mul ((hcgb (i + 1) k).comp (fun X : Config N d => X l))
    have h1 := (hPsi.integrable_mul (SharpLSI.FL.Spectral.memLp_grad_comp_flat hup hΨ (l, k))).mul_bdd
      ((hhfm.const_mul 2).mul (hcgm (i + 1) k)).aestronglyMeasurable
      (c := C) (Eventually.of_forall fun X => by rw [Real.norm_eq_abs]; exact hC X)
    refine h1.congr (Eventually.of_forall fun X => ?_)
    simp only [Pi.mul_apply, SharpLSI.weakGradC]
    ring
  have hT1 : Integrable (fun X => ∑ k : Fin d, (2 * Ψ X * weakGradC Ψ X l k) * hf X *
      cgrad (eC (i + 1)) (X l) k) P := integrable_finsetSum _ fun k _ => hA k
  have hT2 : Integrable (fun X => Ψ X ^ 2 * (c * ∑ j ∈ A.s R, A.a R i j *
      ∑ k : Fin d, cgrad (eC (j + 1)) (X l) k * cgrad (eC (i + 1)) (X l) k)) P := by
    obtain ⟨C, hC⟩ := (BddF.const_mul c (BddF.sum (A.s R) fun j _ => BddF.const_mul (A.a R i j)
      (BddF.sum (Finset.univ : Finset (Fin d)) fun k _ => BddF.mul
        ((hcgb (j + 1) k).comp (fun X : Config N d => X l))
        ((hcgb (i + 1) k).comp (fun X : Config N d => X l)))))
    exact hPsi.integrable_sq.mul_bdd
      (((Finset.measurable_sum _ fun j _ => (Finset.measurable_sum _ fun k _ =>
        (hcgm (j + 1) k).mul (hcgm (i + 1) k)).const_mul _).const_mul c).aestronglyMeasurable)
      (c := C) (Eventually.of_forall fun X => by rw [Real.norm_eq_abs]; exact hC X)
  have hsplit : ∀ X : Config N d, ∑ k : Fin d, ((2 * Ψ X * weakGradC Ψ X l k) * hf X +
        Ψ X ^ 2 * ghf X k) * cgrad (eC (i + 1)) (X l) k =
      ∑ k : Fin d, (2 * Ψ X * weakGradC Ψ X l k) * hf X * cgrad (eC (i + 1)) (X l) k +
        Ψ X ^ 2 * (c * ∑ j ∈ A.s R, A.a R i j *
          ∑ k : Fin d, cgrad (eC (j + 1)) (X l) k * cgrad (eC (i + 1)) (X l) k) := by
    intro X
    have e2 : ∑ k : Fin d, Ψ X ^ 2 * ghf X k * cgrad (eC (i + 1)) (X l) k =
        Ψ X ^ 2 * (c * ∑ j ∈ A.s R, A.a R i j *
          ∑ k : Fin d, cgrad (eC (j + 1)) (X l) k * cgrad (eC (i + 1)) (X l) k) := by
      simp only [hghf, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
    rw [← e2, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [← integral_add hT1 hT2]
  calc _ = ∫ X, ∑ k : Fin d, ((2 * Ψ X * weakGradC Ψ X l k) * hf X + Ψ X ^ 2 * ghf X k) *
        cgrad (eC (i + 1)) (X l) k ∂P := by
        refine integral_congr_ae (Eventually.of_forall fun X => ?_)
        exact (hsplit X).symm
    _ = _ := key'

omit hlow he heC in
/-- Integrability of the three families of terms in `eigen_slice_sq_mul`. -/
theorem slice_integrable (A : FiniteRankApprox W (μ : Measure (Torus d)) e) (R : ℕ) {N : ℕ}
    {Ψ : Config N d → ℝ} (hΨ : MemH1C (QN (μ : Measure (Torus d)) N) Ψ) (l : Fin N) (i : ℕ) :
    Integrable (fun X : Config N d => ∑ k : Fin d, (2 * Ψ X * weakGradC Ψ X l k) *
        TR A R (fun n => fluct eC N n X) i * cgrad (eC (i + 1)) (X l) k)
      (QN (μ : Measure (Torus d)) N) ∧
    Integrable (fun X : Config N d => Ψ X ^ 2 * ((N : ℝ) ^ (-(1 / 2 : ℝ)) * ∑ j ∈ A.s R, A.a R i j *
        ∑ k : Fin d, cgrad (eC (j + 1)) (X l) k * cgrad (eC (i + 1)) (X l) k))
      (QN (μ : Measure (Torus d)) N) ∧
    Integrable (fun X : Config N d => Ψ X ^ 2 * TR A R (fun n => fluct eC N n X) i * eC (i + 1) (X l))
      (QN (μ : Measure (Torus d)) N) := by
  classical
  obtain ⟨hTb, hTm⟩ := TR_fluct_bdd_meas hφ A R (N := N) i
  have hcgb : ∀ j k, BddF (fun x : Torus d => cgrad (eC j) x k) := fun j k =>
    ⟨(exists_bound_cgrad (hφ j)).choose, fun x => (exists_bound_cgrad (hφ j)).choose_spec x k⟩
  have hcgm : ∀ j k, Measurable (fun X : Config N d => cgrad (eC j) (X l) k) := fun j k =>
    (measurable_cgrad (hφ j) k).comp (measurable_pi_apply l)
  have hPsi : MemLp Ψ 2 (QN (μ : Measure (Torus d)) N) := memLp_of_memH1C_pi hΨ
  refine ⟨?_, ?_, ?_⟩
  · refine integrable_finsetSum _ fun k _ => ?_
    obtain ⟨C, hC⟩ := (hTb.const_mul 2).mul ((hcgb (i + 1) k).comp (fun X : Config N d => X l))
    have h1 := (hPsi.integrable_mul (SharpLSI.FL.Spectral.memLp_grad_comp_flat hup hΨ (l, k))).mul_bdd
      ((hTm.const_mul 2).mul (hcgm (i + 1) k)).aestronglyMeasurable
      (c := C) (Eventually.of_forall fun X => by rw [Real.norm_eq_abs]; exact hC X)
    refine h1.congr (Eventually.of_forall fun X => ?_)
    simp only [Pi.mul_apply, SharpLSI.weakGradC]
    ring
  · obtain ⟨C, hC⟩ := (BddF.const_mul ((N : ℝ) ^ (-(1 / 2 : ℝ))) (BddF.sum (A.s R) fun j _ =>
      BddF.const_mul (A.a R i j)
      (BddF.sum (Finset.univ : Finset (Fin d)) fun k _ => BddF.mul
        ((hcgb (j + 1) k).comp (fun X : Config N d => X l))
        ((hcgb (i + 1) k).comp (fun X : Config N d => X l)))))
    exact hPsi.integrable_sq.mul_bdd
      (((Finset.measurable_sum _ fun j _ => (Finset.measurable_sum _ fun k _ =>
        (hcgm (j + 1) k).mul (hcgm (i + 1) k)).const_mul _).const_mul _).aestronglyMeasurable)
      (c := C) (Eventually.of_forall fun X => by rw [Real.norm_eq_abs]; exact hC X)
  · have heb : BddF (eC (i + 1)) := ⟨_, (exists_bound_of_contDiff (hφ (i + 1))).choose_spec⟩
    obtain ⟨C, hC⟩ := hTb.mul (heb.comp (fun X : Config N d => X l))
    refine (hPsi.integrable_sq.mul_bdd (hTm.mul ((measurable_of_contDiff (hφ (i + 1))).comp
      (measurable_pi_apply l))).aestronglyMeasurable
      (c := C) (Eventually.of_forall fun X => by rw [Real.norm_eq_abs]; exact hC X)).congr
      (Eventually.of_forall fun X => ?_)
    simp only [Pi.mul_apply, Function.comp_apply]
    ring

/-- **The cross term** (E1, step 2): `∫ Ψ ∇Ψ·∇U_{N,R} dQ = ½ ∫ Ψ² (Z_NᵀΛ_R T_R Z_N - tr(T_R A_N)) dQ`.

Proof (about 60-80 lines): multiply `eigen_slice_sq_mul` by `N^{-1/2}`, sum over `l : Fin N` and
`i ∈ s_R` (`integral_finsetSum`; all integrands are integrable by boundedness of the `eC`, their
gradients, and `Ψ² ∈ L¹`, `Ψ ∂Ψ ∈ L¹`).  The first sum is `∫ ∑_{l,k} 2Ψ ∂Ψ gradURN` (definition of
`gradURN`), the second is `∫ Ψ² ∑_{ij} a_ij A_{N,ij}` (definition of `ANmat`; `N^{-1/2} N^{-1/2} = N⁻¹`),
the right side is `∑_i λ_{i+1} ∫ Ψ² (TZ)_i Z_i` (definition of `fluct eC`).  Divide by 2. -/
theorem cross_term_URN (A : FiniteRankApprox W (μ : Measure (Torus d)) e) (R : ℕ) {N : ℕ}
    (hN : 1 ≤ N) {Ψ : Config N d → ℝ} (hΨ : MemH1C (QN (μ : Measure (Torus d)) N) Ψ) :
    ∫ X, Ψ X * ∑ l, ∑ k, weakGradC Ψ X l k * gradURN A eC R N X l k
        ∂QN (μ : Measure (Torus d)) N =
      (1 / 2) * ∫ X, Ψ X ^ 2 *
        (∑ i ∈ A.s R, lam (i + 1) * fluct eC N i X * TR A R (fun n => fluct eC N n X) i
          - ∑ i ∈ A.s R, ∑ j ∈ A.s R, A.a R i j * ANmat eC N X i j)
        ∂QN (μ : Measure (Torus d)) N := by
  classical
  set c : ℝ := (N : ℝ) ^ (-(1 / 2 : ℝ)) with hc
  set P := QN (μ : Measure (Torus d)) N with hP
  have hcc : c * c = (N : ℝ)⁻¹ := prop23_rpow_half_mul_self N
  let T1 : Fin N → ℕ → Config N d → ℝ := fun l i X => ∑ k : Fin d, (2 * Ψ X * weakGradC Ψ X l k) *
    TR A R (fun n => fluct eC N n X) i * cgrad (eC (i + 1)) (X l) k
  let T2 : Fin N → ℕ → Config N d → ℝ := fun l i X => Ψ X ^ 2 * (c * ∑ j ∈ A.s R, A.a R i j *
    ∑ k : Fin d, cgrad (eC (j + 1)) (X l) k * cgrad (eC (i + 1)) (X l) k)
  let T3 : Fin N → ℕ → Config N d → ℝ := fun l i X =>
    Ψ X ^ 2 * TR A R (fun n => fluct eC N n X) i * eC (i + 1) (X l)
  have hI : ∀ l i, Integrable (T1 l i) P ∧ Integrable (T2 l i) P ∧ Integrable (T3 l i) P :=
    fun l i => slice_integrable hup hφ A R hΨ l i
  have hrel : ∀ (l : Fin N) (i : ℕ), c * ∫ X, T1 l i X ∂P =
      c * (lam (i + 1) * ∫ X, T3 l i X ∂P) - c * ∫ X, T2 l i X ∂P := fun l i => by
    have h : (∫ X, T1 l i X ∂P) + ∫ X, T2 l i X ∂P = lam (i + 1) * ∫ X, T3 l i X ∂P :=
      eigen_slice_sq_mul hup hlow he hφ heC A R hN hΨ l i
    linear_combination c * h
  -- pointwise identities
  have E1 : ∀ X : Config N d, Ψ X * ∑ l, ∑ k, weakGradC Ψ X l k * gradURN A eC R N X l k =
      (1 / 2) * ∑ l : Fin N, ∑ i ∈ A.s R, c * T1 l i X := by
    intro X
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [gradURN, T1, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring
  have E2 : ∀ X : Config N d, Ψ X ^ 2 *
      (∑ i ∈ A.s R, lam (i + 1) * fluct eC N i X * TR A R (fun n => fluct eC N n X) i
        - ∑ i ∈ A.s R, ∑ j ∈ A.s R, A.a R i j * ANmat eC N X i j) =
      ∑ l : Fin N, ∑ i ∈ A.s R, c * (lam (i + 1) * T3 l i X) -
        ∑ l : Fin N, ∑ i ∈ A.s R, c * T2 l i X := by
    intro X
    rw [mul_sub]
    congr 1
    · simp only [fluct, T3, ← hc]
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ => by ring
    · simp only [ANmat, T2, Finset.mul_sum, Finset.sum_mul]
      symm
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      refine Finset.sum_congr rfl fun l _ => ?_
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← hcc]
      ring
  have hsum : ∀ F : Fin N → ℕ → Config N d → ℝ, (∀ l i, Integrable (F l i) P) →
      ∫ X, ∑ l, ∑ i ∈ A.s R, F l i X ∂P = ∑ l, ∑ i ∈ A.s R, ∫ X, F l i X ∂P := fun F hF => by
    rw [integral_finsetSum _ fun l _ => integrable_finsetSum _ fun i _ => hF l i]
    exact Finset.sum_congr rfl fun l _ => integral_finsetSum _ fun i _ => hF l i
  have hsumI : ∀ F : Fin N → ℕ → Config N d → ℝ, (∀ l i, Integrable (F l i) P) →
      Integrable (fun X => ∑ l, ∑ i ∈ A.s R, F l i X) P := fun F hF =>
    integrable_finsetSum _ fun l _ => integrable_finsetSum _ fun i _ => hF l i
  have h1 : ∫ X, ∑ l, ∑ i ∈ A.s R, c * T1 l i X ∂P = ∑ l, ∑ i ∈ A.s R, c * ∫ X, T1 l i X ∂P := by
    rw [hsum (fun l i X => c * T1 l i X) fun l i => (hI l i).1.const_mul c]
    simp only [integral_const_mul]
  have h2 : ∫ X, ∑ l, ∑ i ∈ A.s R, c * T2 l i X ∂P = ∑ l, ∑ i ∈ A.s R, c * ∫ X, T2 l i X ∂P := by
    rw [hsum (fun l i X => c * T2 l i X) fun l i => (hI l i).2.1.const_mul c]
    simp only [integral_const_mul]
  have h3 : ∫ X, ∑ l, ∑ i ∈ A.s R, c * (lam (i + 1) * T3 l i X) ∂P =
      ∑ l, ∑ i ∈ A.s R, c * (lam (i + 1) * ∫ X, T3 l i X ∂P) := by
    rw [hsum (fun l i X => c * (lam (i + 1) * T3 l i X))
      fun l i => ((hI l i).2.2.const_mul (lam (i + 1))).const_mul c]
    simp only [integral_const_mul]
  have hE2 : ∫ X, Ψ X ^ 2 *
      (∑ i ∈ A.s R, lam (i + 1) * fluct eC N i X * TR A R (fun n => fluct eC N n X) i
        - ∑ i ∈ A.s R, ∑ j ∈ A.s R, A.a R i j * ANmat eC N X i j) ∂P =
      ∑ l, ∑ i ∈ A.s R, c * (lam (i + 1) * ∫ X, T3 l i X ∂P) -
        ∑ l, ∑ i ∈ A.s R, c * ∫ X, T2 l i X ∂P := by
    rw [integral_congr_ae (Eventually.of_forall E2), integral_sub
      (hsumI (fun l i X => c * (lam (i + 1) * T3 l i X))
        fun l i => ((hI l i).2.2.const_mul (lam (i + 1))).const_mul c)
      (hsumI (fun l i X => c * T2 l i X) fun l i => (hI l i).2.1.const_mul c), h3, h2]
  rw [hE2, integral_congr_ae (Eventually.of_forall E1), integral_const_mul, h1]
  congr 1
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => hrel l i

/-- **(E1) The Schrödinger identity** (eq:schrodinger) for `U_{N,R}`, every `Ψ ∈ H¹(Q_N)`:
`∫|∇Ψ + ½Ψ∇U_{N,R}|² dQ_N = ∫|∇Ψ|² dQ_N + ∫ V_{N,R} Ψ² dQ_N`.

Proof (about 60 lines): `weakGradC_URN_ae` (Replace; `hac := Measure.absolutelyContinuous_of_le_smul hup`) shows
`shEn μ Ψ (URN A R N)` is the `shEn`-integral with `gradURN` in place of `weakGradC (URN …)`;
`hasWeakGrad` and a uniform bound `|gradURN| ≤ L` from `exists_bound_of_contDiff`/`exists_bound_cgrad`
(NBody2:36-42, finite sums); `shEn_expand` (with `U := URN A R N`); `cross_term_URN` for the middle
term (after the a.e. replacement `weakGradC (URN) = gradURN`); `sum_gradURN_sq` for
`gradSqC (URN …) = ∑ (gradURN)² = (TZ)ᵀ A (TZ)` a.e.; combine:
`∫ gradSqC Ψ + ½ ∫ Ψ²(ZᵀΛTZ - tr TA) + ¼ ∫ Ψ² (TZ)ᵀA(TZ) = ∫ gradSqC Ψ + ∫ VNR Ψ²`
by the definition of `VNR` (`integral_add`, `integral_const_mul`, `ring`-level finite sum algebra;
all integrands bounded × `Ψ²`). -/
theorem schrodinger_identity (A : FiniteRankApprox W (μ : Measure (Torus d)) e) (R : ℕ) {N : ℕ}
    (hN : 1 ≤ N) {Ψ : Config N d → ℝ} (hΨ : MemH1C (QN (μ : Measure (Torus d)) N) Ψ) :
    shEn (μ : Measure (Torus d)) Ψ (URN A R N) ≠ ⊤ ∧
      (shEn (μ : Measure (Torus d)) Ψ (URN A R N)).toReal =
        (refEnergy (μ : Measure (Torus d)) Ψ).toReal +
          ∫ X, VNR A lam eC R N X * Ψ X ^ 2 ∂QN (μ : Measure (Torus d)) N := by
  classical
  have hac : (μ : Measure (Torus d)) ≪ haar d := Measure.absolutelyContinuous_of_le_smul hup
  have hae := weakGradC_URN_ae hac A hφ heC R hN
  obtain ⟨L, hL⟩ := gradURN_bdd hφ A R N
  have hU : HasWeakGrad (URN A R N ∘ unflat) := ⟨_, isWeakGrad_URN A hφ heC R hN⟩
  have hLae : ∀ᵐ X ∂QN (μ : Measure (Torus d)) N, ∀ (i : Fin N) (k : Fin d),
      |weakGradC (URN A R N) X i k| ≤ L := hae.mono fun X hX i k => by rw [hX i k]; exact hL X i k
  obtain ⟨hne, hval⟩ := shEn_expand hac hΨ hU hLae
  refine ⟨hne, ?_⟩
  rw [hval]
  have hmid : ∫ X, Ψ X * ∑ i, ∑ k, weakGradC Ψ X i k * weakGradC (URN A R N) X i k
        ∂QN (μ : Measure (Torus d)) N =
      ∫ X, Ψ X * ∑ l, ∑ k, weakGradC Ψ X l k * gradURN A eC R N X l k
        ∂QN (μ : Measure (Torus d)) N := by
    refine integral_congr_ae (hae.mono fun X hX => ?_)
    simp only [hX]
  have hsq : ∫ X, Ψ X ^ 2 * gradSqC (URN A R N) X ∂QN (μ : Measure (Torus d)) N =
      ∫ X, Ψ X ^ 2 * ∑ i ∈ A.s R, ∑ j ∈ A.s R, TR A R (fun n => fluct eC N n X) i *
        ANmat eC N X i j * TR A R (fun n => fluct eC N n X) j ∂QN (μ : Measure (Torus d)) N := by
    refine integral_congr_ae (hae.mono fun X hX => ?_)
    simp only [gradSqC, hX]
    rw [sum_gradURN_sq]
  rw [hmid, hsq, cross_term_URN hup hlow he hφ heC A R hN hΨ]
  -- integrability
  have hPsi : Integrable (fun X => Ψ X ^ 2) (QN (μ : Measure (Torus d)) N) :=
    (memLp_of_memH1C_pi hΨ).integrable_sq
  have hg1 : BM (fun X : Config N d => ∑ i ∈ A.s R, lam (i + 1) * fluct eC N i X *
        TR A R (fun n => fluct eC N n X) i
      - ∑ i ∈ A.s R, ∑ j ∈ A.s R, A.a R i j * ANmat eC N X i j) :=
    (BM.sum _ fun i _ => ((BM_fluct hφ N i).const_mul (lam (i + 1))).mul (BM_TR hφ A R i)).sub
      (BM.sum _ fun i _ => BM.sum _ fun j _ => (BM_ANmat hφ N i j).const_mul (A.a R i j))
  have hg2 : BM (fun X : Config N d => ∑ i ∈ A.s R, ∑ j ∈ A.s R, TR A R (fun n => fluct eC N n X) i *
        ANmat eC N X i j * TR A R (fun n => fluct eC N n X) j) :=
    BM.sum _ fun i _ => BM.sum _ fun j _ => ((BM_TR hφ A R i).mul (BM_ANmat hφ N i j)).mul (BM_TR hφ A R j)
  have hi1 := hPsi.mul_bdd hg1.2.aestronglyMeasurable
    (c := hg1.1.choose) (Eventually.of_forall fun X => by
      rw [Real.norm_eq_abs]; exact hg1.1.choose_spec X)
  have hi2 := hPsi.mul_bdd hg2.2.aestronglyMeasurable
    (c := hg2.1.choose) (Eventually.of_forall fun X => by
      rw [Real.norm_eq_abs]; exact hg2.1.choose_spec X)
  have hV : ∫ X, VNR A lam eC R N X * Ψ X ^ 2 ∂QN (μ : Measure (Torus d)) N =
      ∫ X, ((1 / 2) * (Ψ X ^ 2 * (∑ i ∈ A.s R, lam (i + 1) * fluct eC N i X *
        TR A R (fun n => fluct eC N n X) i
      - ∑ i ∈ A.s R, ∑ j ∈ A.s R, A.a R i j * ANmat eC N X i j)) +
        (1 / 4) * (Ψ X ^ 2 * ∑ i ∈ A.s R, ∑ j ∈ A.s R, TR A R (fun n => fluct eC N n X) i *
        ANmat eC N X i j * TR A R (fun n => fluct eC N n X) j)) ∂QN (μ : Measure (Torus d)) N := by
    refine integral_congr_ae (Eventually.of_forall fun X => ?_)
    simp only [VNR]
    ring
  rw [hV, integral_add (hi1.const_mul _) (hi2.const_mul _), integral_const_mul, integral_const_mul]
  ring

end Schrodinger

section FiniteRankLimit

variable {W : Torus d → Torus d → ℝ}
  (hac : (μ : Measure (Torus d)) ≪ haar d)
  (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam)
  (hφ : ∀ j, ContDiff ℝ 1 (eC j ∘ liftT)) (heC : ∀ j, eC j =ᵐ[haar d] e j)
include hac he hφ heC

/-- The exact Dirichlet matrix of the genuine reference eigenfunctions. -/
theorem sum_integral_cgrad_eC (a b : ℕ) :
    ∑ k : Fin d, ∫ x, cgrad (eC a) x k * cgrad (eC b) x k ∂(μ : Measure (Torus d)) =
      lam a * (if a = b then 1 else 0) := by
  obtain ⟨hm, B, hB⟩ := schroC_term_facts hφ a b
  have hI : ∀ k : Fin d, Integrable (fun x => cgrad (eC a) x k * cgrad (eC b) x k)
      (μ : Measure (Torus d)) := fun k =>
    Integrable.of_bound (hm k).aestronglyMeasurable B
      (Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hB x k)
  rw [← integral_finsetSum _ fun k _ => hI k]
  calc
    (∫ x, ∑ k, cgrad (eC a) x k * cgrad (eC b) x k ∂(μ : Measure (Torus d))) =
        ∫ x, ∑ k, cgrad (eC b) x k * cgrad (eC a) x k ∂(μ : Measure (Torus d)) := by
      simp only [mul_comm]
    _ = lam a * ∫ x, eC a x * eC b x ∂(μ : Measure (Torus d)) :=
      eigen_C1 hac he hφ heC a (hφ b)
    _ = _ := by
      congr 1
      rw [← he.orthonormal a b]
      have ha : eC a =ᵐ[(μ : Measure (Torus d))] e a := hac.ae_le (heC a)
      have hb : eC b =ᵐ[(μ : Measure (Torus d))] e b := hac.ae_le (heC b)
      exact integral_congr_ae (ha.mul hb)

theorem ANmat_moment (i j k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N →
      ∫ X, (ANmat eC N X i j - if i = j then lam (i + 1) else 0) ^ (2 * k)
          ∂QN (μ : Measure (Torus d)) N ≤ C * ((N : ℝ)⁻¹) ^ k := by
  obtain ⟨hSm, B, hB⟩ := schroC_S_facts hφ (i + 1) (j + 1)
  obtain ⟨hterm, Bt, hBt⟩ := schroC_term_facts hφ (i + 1) (j + 1)
  set c : ℝ := if i = j then lam (i + 1) else 0 with hc
  set S : Torus d → ℝ := fun x => ∑ m : Fin d,
    cgrad (eC (i + 1)) x m * cgrad (eC (j + 1)) x m with hS
  have hSint : Integrable S (μ : Measure (Torus d)) :=
    Integrable.of_bound hSm.aestronglyMeasurable B
      (Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hB x)
  have hSc : ∫ x, S x ∂(μ : Measure (Torus d)) = c := by
    simp only [hS]
    rw [integral_finsetSum]
    · rw [sum_integral_cgrad_eC hac he hφ heC (i + 1) (j + 1)]
      simp [hc]
    · intro m _
      exact Integrable.of_bound (hterm m).aestronglyMeasurable Bt
        (Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hBt x m)
  set g : Torus d → ℝ := fun x => S x - c with hg
  have hgm : Measurable g := hSm.sub_const c
  have hgB : ∀ x, |g x| ≤ |B| + |c| := fun x =>
    (abs_sub _ _).trans (add_le_add ((hB x).trans (le_abs_self _)) le_rfl)
  have hcent : ∫ x, g x ∂(μ : Measure (Torus d)) = 0 := by
    simp only [hg]
    rw [integral_sub hSint (integrable_const c), hSc]
    simp
  obtain ⟨C0, hC0, hCm⟩ := Sec6.sum_moment_bound k
  refine ⟨C0 * (|B| + |c|) ^ (2 * k), by positivity, fun N hN => ?_⟩
  have key := hCm (Torus d) (μ : Measure (Torus d)) N g (|B| + |c|) hgm
    (Eventually.of_forall hgB) hcent
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hid : ∀ X : Config N d, ANmat eC N X i j - c = (N : ℝ)⁻¹ * ∑ l, g (X l) := by
    intro X
    simp only [ANmat, hg, hS, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have hinv : ((N : ℝ)⁻¹) ^ k * (N : ℝ) ^ k = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hNpos.ne', one_pow]
  calc ∫ X, (ANmat eC N X i j - c) ^ (2 * k) ∂QN (μ : Measure (Torus d)) N
      = ∫ X, ((N : ℝ)⁻¹) ^ (2 * k) * (∑ l, g (X l)) ^ (2 * k)
          ∂QN (μ : Measure (Torus d)) N := by
        refine integral_congr_ae (Eventually.of_forall fun X => ?_)
        simp only [hid X, mul_pow]
    _ = ((N : ℝ)⁻¹) ^ (2 * k) * ∫ X, (∑ l, g (X l)) ^ (2 * k)
          ∂QN (μ : Measure (Torus d)) N := integral_const_mul _ _
    _ ≤ ((N : ℝ)⁻¹) ^ (2 * k) * (C0 * (N : ℝ) ^ k * (|B| + |c|) ^ (2 * k)) :=
        mul_le_mul_of_nonneg_left key (by positivity)
    _ = C0 * (|B| + |c|) ^ (2 * k) * (((N : ℝ)⁻¹) ^ k * (((N : ℝ)⁻¹) ^ k * (N : ℝ) ^ k)) := by
        rw [two_mul, pow_add]; ring
    _ = C0 * (|B| + |c|) ^ (2 * k) * ((N : ℝ)⁻¹) ^ k := by rw [hinv, mul_one]

/-- **Uniform moments of the fluctuation vector**: `sup_{N ≥ 1} E (Z_{N,n+1})^{2k} < ∞`.

Proof (about 40 lines): `eC (n+1)` is measurable, bounded, and `μ`-centered
(`he.orthonormal (n+1) 0`, `he.zero`, `eC =ᵐ[μ] e`, `minimizer_ac`); apply
`Sec6.fluct_moment_bound k` (lane 3, `Sec6MomentsZ.lean:267`). -/
theorem fluct_moment_eC (n k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N →
      ∫ X, (fluct eC N n X) ^ (2 * k) ∂QN (μ : Measure (Torus d)) N ≤ C := by
  obtain ⟨C0, hC0, hCm⟩ := Sec6.fluct_moment_bound k
  obtain ⟨B, hB⟩ := exists_bound_of_contDiff (hφ (n + 1))
  have hcent : ∫ x, eC (n + 1) x ∂(μ : Measure (Torus d)) = 0 := by
    have h1 : ∫ x, eC (n + 1) x ∂(μ : Measure (Torus d)) =
        ∫ x, e (n + 1) x ∂(μ : Measure (Torus d)) :=
      integral_congr_ae (hac.ae_le (heC (n + 1)))
    have h2 := he.orthonormal (n + 1) 0
    rw [he.zero] at h2
    simpa [h1] using h2
  refine ⟨C0 * B ^ (2 * k), mul_nonneg hC0 (by rw [pow_mul]; positivity), fun N hN => ?_⟩
  exact hCm (Torus d) (μ : Measure (Torus d)) N hN (eC (n + 1)) B
    (measurable_of_contDiff (hφ (n + 1))) (Eventually.of_forall hB) hcent

/-- **(E2) (eq:v-limit)**: for fixed `R` and every finite `q ≥ 1`,
`‖V_{N,R} - v_R(Z_N)‖_{L^q(Q_N)} → 0` as `N → ∞`.

Proof (about 120-160 lines): by `fluct eC N n =ᵐ[Q_N] fluct e N n` (`μ`-a.e. equality of
`eC j` and `e j` pulled back through the coordinate projections; `eLpNorm_congr_ae`) reduce to
`vR` at `fluct eC`; `VNR_sub_vR_eq` writes the difference as a finite sum of terms
`TZ_i D_ij TZ_j` and `a_ij D_ij`, `D_ij := ANmat - λδ`.  Choose `k` with `2k ≥ 3 q.toReal`; on
a probability space `‖·‖_q ≤ ‖·‖_{2k}`/Hölder: `‖TZ_i D_ij TZ_j‖_q ≤ ‖TZ_i‖_{3q} ‖D_ij‖_{3q} ‖TZ_j‖_{3q}`
(`eLpNorm_mul_le`/`MemLp.mul` with `HolderTriple`; or: `|x y z| ≤ (|x|³+|y|³+|z|³)/3`-type bound
avoided by the three-factor Hölder), `‖TZ_i‖_{3q} ≤ ∑_j |a_ij| ‖Z_j‖_{3q}` bounded uniformly in
`N` by `fluct_moment_eC`, and `‖D_ij‖_{2k} = (E D^{2k})^{1/2k} ≤ (C N^{-k})^{1/2k} → 0` by
`ANmat_moment`.  `eLpNorm_sum_le`/`eLpNorm_add_le` for the finite sums; `tendsto_finset_sum`. -/
theorem VNR_tendsto_vR (A : FiniteRankApprox W (μ : Measure (Torus d)) e) (R : ℕ) (q : ℝ≥0∞)
    (hq1 : 1 ≤ q) (hq : q ≠ ⊤) :
    Tendsto (fun N : ℕ => eLpNorm
        (fun X => VNR A lam eC R N X - vR A lam R (fun n => fluct e N n X)) q
        (QN (μ : Measure (Torus d)) N)) atTop (𝓝 0) := by
  have hmain := schroC_main (μ := (μ : Measure (Torus d))) (A.s R) (A.a R)
    (fun n N X => fluct eC N n X)
    (fun i j N X => ANmat eC N X i j - if i = j then lam (i + 1) else 0)
    (fun n N => (schroC_Z_facts (μ := (μ : Measure (Torus d))) hφ n N).1)
    (fun n N => (schroC_Z_facts (μ := (μ : Measure (Torus d))) hφ n N).2)
    (fun n k => by
      obtain ⟨C, -, hC⟩ := fluct_moment_eC hac he hφ heC n k
      exact ⟨C, hC⟩)
    (fun i j N => (schroC_D_facts (μ := (μ : Measure (Torus d))) hφ i j N).1)
    (fun i j N => (schroC_D_facts (μ := (μ : Measure (Torus d))) hφ i j N).2)
    (fun i j k => by
      obtain ⟨C, -, hC⟩ := ANmat_moment hac he hφ heC i j k
      exact ⟨C, hC⟩) q hq1 hq
  refine (tendsto_congr fun N => ?_).2 hmain
  exact eLpNorm_congr_ae (schroC_g_ae hac heC A R N)

/-- **(E2), consumer form** (what WP-F needs): `∫ Ψ² (V_{N,R} - v_R(Z_N)) dQ_N → 0` uniformly over
the `L^{2p}`-ball `∫|Ψ|^{2p} ≤ M` (in the application `Ψ = psiG f`, `p, M` from WP-A).

Proof (about 40 lines): `holder_sq_mul` (Replace) with `g := VNR - vR(Z)`, bound
`|∫ Ψ² g| ≤ ∫⁻ ofReal (Ψ² |g|) ≤ M^{1/p} ‖g‖_{p/(p-1)}` (toReal), and `VNR_tendsto_vR` with
`q := ofReal (p/(p-1))`. -/
theorem integral_VNR_sub_vR_small (A : FiniteRankApprox W (μ : Measure (Torus d)) e) (R : ℕ)
    {p : ℝ} (hp : 1 < p) (M : ℝ) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop, ∀ Ψ : Config N d → ℝ,
      AEStronglyMeasurable Ψ (QN (μ : Measure (Torus d)) N) →
      ∫⁻ X, ENNReal.ofReal (|Ψ X| ^ (2 * p)) ∂QN (μ : Measure (Torus d)) N ≤ ENNReal.ofReal M →
      |∫ X, Ψ X ^ 2 * (VNR A lam eC R N X - vR A lam R (fun n => fluct e N n X))
          ∂QN (μ : Measure (Torus d)) N| ≤ ε := by
  intro ε hε
  have hp1 : 0 < p - 1 := by linarith
  have hq1 : 1 ≤ ENNReal.ofReal (p / (p - 1)) :=
    ENNReal.one_le_ofReal.2 ((one_le_div hp1).2 (by linarith))
  have hT := VNR_tendsto_vR hac he hφ heC A R (ENNReal.ofReal (p / (p - 1))) hq1
    ENNReal.ofReal_ne_top
  have hLtop : ENNReal.ofReal M ^ (1 / p) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top
  have hT2 : Tendsto (fun N : ℕ => ENNReal.ofReal M ^ (1 / p) * eLpNorm
      (fun X => VNR A lam eC R N X - vR A lam R (fun n => fluct e N n X))
      (ENNReal.ofReal (p / (p - 1))) (QN (μ : Measure (Torus d)) N)) atTop
      (𝓝 (ENNReal.ofReal M ^ (1 / p) * 0)) :=
    ENNReal.Tendsto.const_mul hT (Or.inr hLtop)
  rw [mul_zero] at hT2
  have hev := (tendsto_order.1 hT2).2 (ENNReal.ofReal ε) (ENNReal.ofReal_pos.2 hε)
  filter_upwards [hev] with N hN Ψ hΨ hΨint
  have hFm := schroC_F_meas (A.s R) (A.a R) (fun n N X => fluct eC N n X)
    (fun i j N X => ANmat eC N X i j - if i = j then lam (i + 1) else 0)
    (fun n N => (schroC_Z_facts (μ := (μ : Measure (Torus d))) hφ n N).1)
    (fun i j N => (schroC_D_facts (μ := (μ : Measure (Torus d))) hφ i j N).1) N
  have hgm : AEMeasurable
      (fun X : Config N d => VNR A lam eC R N X - vR A lam R (fun n => fluct e N n X))
      (QN (μ : Measure (Torus d)) N) :=
    hFm.aemeasurable.congr (schroC_g_ae hac heC A R N).symm
  set g : Config N d → ℝ :=
    fun X => VNR A lam eC R N X - vR A lam R (fun n => fluct e N n X) with hg
  have h1 := schroC_holder_sq_mul (QN (μ : Measure (Torus d)) N) hp hΨ.aemeasurable hgm
  have h2 : ∫⁻ X, ENNReal.ofReal (Ψ X ^ 2 * |g X|) ∂QN (μ : Measure (Torus d)) N ≤
      ENNReal.ofReal ε :=
    h1.trans (le_of_lt (lt_of_le_of_lt (by gcongr) hN))
  have h3 : ∫ X, Ψ X ^ 2 * |g X| ∂QN (μ : Measure (Torus d)) N ≤ ε := by
    have hfm : AEStronglyMeasurable (fun X : Config N d => Ψ X ^ 2 * |g X|)
        (QN (μ : Measure (Torus d)) N) := (hΨ.pow 2).mul hgm.aestronglyMeasurable.norm
    rw [integral_eq_lintegral_of_nonneg_ae (f := fun X => Ψ X ^ 2 * |g X|)
      (Eventually.of_forall fun X => by positivity) hfm]
    exact ENNReal.toReal_le_of_le_ofReal hε.le h2
  calc |∫ X, Ψ X ^ 2 * g X ∂QN (μ : Measure (Torus d)) N|
      = ‖∫ X, Ψ X ^ 2 * g X ∂QN (μ : Measure (Torus d)) N‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ X, ‖Ψ X ^ 2 * g X‖ ∂QN (μ : Measure (Torus d)) N := norm_integral_le_integral_norm _
    _ = ∫ X, Ψ X ^ 2 * |g X| ∂QN (μ : Measure (Torus d)) N := by
        refine integral_congr_ae (Eventually.of_forall fun X => ?_)
        simp only [norm_mul, norm_pow, Real.norm_eq_abs, sq_abs]
    _ ≤ ε := h3

end FiniteRankLimit

end DGPS.Lipschitz.GroundState
