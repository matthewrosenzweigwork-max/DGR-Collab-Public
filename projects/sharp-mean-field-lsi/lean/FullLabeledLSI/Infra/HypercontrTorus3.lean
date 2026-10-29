import FullLabeledLSI.Infra.HypercontrTorus2
import FullLabeledLSI.Infra.HypercontrProduct
import FullLabeledLSI.Infra.HypercontrTensorLSI
import FullLabeledLSI.Defs.F05_FiniteRank
import SharpSymmetricLSI.Paper.Defective6

/-!
# The N-fold torus logarithmic Sobolev inequality and the product eigen-IBP

* `torus_lsi`: for `F ∈ C¹((𝕋^d)^N)` with `0 < c ≤ F ≤ B`,
  `Ent_{μ^{⊗N}}(F²) ≤ (2/a) ∫ |∇F|² dμ^{⊗N}` (classical product gradient), from the one-particle
  inequality `a ≤ r_LS(μ)` by tensorization (`Tensor.entR_pi_le`).
* `refEnergy_eq_gradPair`: `refEnergy μ F = ofReal ∫ |∇F|²` for `C¹` `F` (weak gradient = classical).
* `torus_eigen_ibp`: `(∑_l λ_{j_l}) ∫ F ∏ e_{j_m}(x_m) = ∫ ∇F · ∇(∏ e_{j_m})` for `C¹` `F`.
-/

open MeasureTheory SharpLSI

noncomputable section

namespace SharpLSI.FL.Gross

variable {N d : ℕ}

lemma dT_const_mul {g : Torus d → ℝ} (hg : C1T g) (c : ℝ) (k : Fin d) (y : Torus d) :
    dT (fun y => c * g y) k y = c * dT g k y := by
  have := dT_sum (Finset.univ : Finset Unit) (g := fun _ => g) (fun _ => c) (fun _ _ => hg) k y
  simpa using this

/-! ### Absolute continuity of product measures -/

theorem pi_absolutelyContinuous {α : Type*} [MeasurableSpace α] {μ ν : Measure α}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (h : μ ≪ ν) :
    ∀ N : ℕ, (Measure.pi fun _ : Fin N => μ) ≪ (Measure.pi fun _ : Fin N => ν)
  | 0 => by
    rw [Measure.pi_of_empty, Measure.pi_of_empty]
  | n + 1 => by
    have e1 := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) 0
    have e2 := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => ν) 0
    have hprod : μ.prod (Measure.pi fun _ : Fin n => μ) ≪ ν.prod (Measure.pi fun _ : Fin n => ν) :=
      h.prod (pi_absolutelyContinuous h n)
    rw [← e1.map_eq, ← e2.map_eq] at hprod
    refine Measure.AbsolutelyContinuous.mk fun s _ hs => ?_
    set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => α) 0
    have key : e ⁻¹' (e.symm ⁻¹' s) = s := by ext x; simp
    have h1 : (Measure.map e (Measure.pi fun _ : Fin (n + 1) => ν)) (e.symm ⁻¹' s) = 0 := by
      rw [MeasurableEquiv.map_apply, key]
      exact hs
    have h2 := hprod h1
    rw [MeasurableEquiv.map_apply, key] at h2
    exact h2

lemma ae_pi_of_ae_flat {mu : Measure (Torus d)} [IsProbabilityMeasure mu] (hac : mu ≪ volume)
    {P : UnitAddTorus (Fin N × Fin d) → Prop}
    (h : ∀ᵐ y ∂(volume : Measure (UnitAddTorus (Fin N × Fin d))), P y) :
    ∀ᵐ X ∂(Measure.pi fun _ : Fin N => mu), P (flat X) := by
  have hmp : MeasurePreserving (flat : Config N d → UnitAddTorus (Fin N × Fin d)) volume volume :=
    ⟨measurable_flat, map_flat_volume N⟩
  have h1 : ∀ᵐ X ∂(volume : Measure (Config N d)), P (flat X) := hmp.quasiMeasurePreserving.ae h
  exact (pi_absolutelyContinuous hac N).ae_le h1

/-! ### `C¹` closure properties on `Config N d` -/

lemma C1C.measurable {F : Config N d → ℝ} (hF : C1C F) : Measurable F := by
  have := (C1T.measurable hF).comp (measurable_flat (N := N) (d := d))
  exact this

lemma C1C.bounded {F : Config N d → ℝ} (hF : C1C F) : ∃ K, ∀ x, |F x| ≤ K := by
  obtain ⟨K, hK⟩ := C1T.bounded hF
  exact ⟨K, fun x => hK (flat x)⟩

lemma C1C.comp {F : Config N d → ℝ} (hF : C1C F) {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 1 ψ) :
    C1C (ψ ∘ F) := C1T.comp hF hψ

lemma C1C.eval {e : Torus d → ℝ} (he : C1T e) (i : Fin N) : C1C (fun X : Config N d => e (X i)) := by
  unfold C1C C1T
  have h1 : ((fun X : Config N d => e (X i)) ∘ unflat) ∘ liftT =
      (e ∘ liftT) ∘ (fun z : Fin N × Fin d → ℝ => fun k => z (i, k)) := by
    funext z
    simp only [Function.comp]
    congr 1
  rw [h1]
  exact ContDiff.comp he (contDiff_pi.mpr fun k => contDiff_apply ℝ ℝ (i, k))

lemma C1C.prod {ι : Type*} (s : Finset ι) {g : ι → Config N d → ℝ} (hg : ∀ i ∈ s, C1C (g i)) :
    C1C (fun X => ∏ i ∈ s, g i X) := by
  unfold C1C C1T at *
  have : ((fun X => ∏ i ∈ s, g i X) ∘ unflat) ∘ liftT =
      fun z => ∏ i ∈ s, ((g i ∘ unflat) ∘ liftT) z := rfl
  rw [this]
  exact contDiff_prod hg

lemma C1C.sum {ι : Type*} (s : Finset ι) {g : ι → Config N d → ℝ} (c : ι → ℝ)
    (hg : ∀ i ∈ s, C1C (g i)) : C1C (fun X => ∑ i ∈ s, c i * g i X) := by
  unfold C1C C1T at *
  have : ((fun X => ∑ i ∈ s, c i * g i X) ∘ unflat) ∘ liftT =
      fun z => ∑ i ∈ s, c i * ((g i ∘ unflat) ∘ liftT) z := rfl
  rw [this]
  exact ContDiff.sum fun i hi => (hg i hi).const_smul (c i)

/-! ### The energy as a classical integral -/

variable {mu : Measure (Torus d)} [IsProbabilityMeasure mu]

lemma ae_weakGrad_eq_dT_pi (hac : mu ≪ volume) {F : Config N d → ℝ} (hF : C1C F) :
    ∀ᵐ X ∂(Measure.pi fun _ : Fin N => mu),
      ∀ p, weakGrad (F ∘ unflat) (flat X) p = dT (F ∘ unflat) p (flat X) := by
  have h : ∀ᵐ y ∂(volume : Measure (UnitAddTorus (Fin N × Fin d))),
      ∀ p, weakGrad (F ∘ unflat) y p = dT (F ∘ unflat) p y := by
    filter_upwards [weakGrad_ae_eq_dT hF] with y hy p
    exact congrFun hy p
  exact ae_pi_of_ae_flat hac h

lemma gradPair_nonneg_self (F : Config N d → ℝ) (x : Config N d) : 0 ≤ gradPair F F x :=
  Finset.sum_nonneg fun p _ => mul_self_nonneg _

lemma refEnergy_eq_gradPair (hac : mu ≪ volume) {F : Config N d → ℝ} (hF : C1C F) :
    refEnergy mu F = ENNReal.ofReal (∫ X, gradPair F F X ∂(Measure.pi fun _ : Fin N => mu)) := by
  obtain ⟨K, hK⟩ := bounded_gradPair hF hF
  have hint : Integrable (fun X => gradPair F F X) (Measure.pi fun _ : Fin N => mu) :=
    Integrable.of_bound (measurable_gradPair hF hF).aestronglyMeasurable K
      (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hK x)
  rw [ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall (gradPair_nonneg_self F))]
  unfold refEnergy
  refine lintegral_congr_ae ?_
  filter_upwards [ae_weakGrad_eq_dT_pi hac hF] with X hX
  congr 1
  unfold gradSqC weakGradC gradPair
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  rw [hX (i, k)]; ring

/-! ### The torus LSI -/

theorem torus_lsi (hac : mu ≪ volume) {a : ℝ} (ha : 0 < a) (hrls : ENNReal.ofReal a ≤ rLS mu)
    {F : Config N d → ℝ} (hF : C1C F) {c B : ℝ} (hc : 0 < c) (hFc : ∀ x, c ≤ F x)
    (hFB : ∀ x, F x ≤ B) :
    entR (Measure.pi fun _ : Fin N => mu) (fun x => F x ^ 2) ≤
      2 / a * ∫ x, gradPair F F x ∂(Measure.pi fun _ : Fin N => mu) := by
  obtain ⟨K, hK⟩ := bounded_Gamma_slice hF hF
  have key := Tensor.entR_pi_le mu C1T (fun f => GammaT f f) (2 / a) (by positivity)
    (fun f hf _ ⟨c', hc', hfc'⟩ _ => classical_lsi hac ha hrls hf hc' hfc') N F hF.measurable hc
    hFc hFB (fun x i => C1T_sliceF hF x i)
    (fun i => measurable_Gamma_slice hF hF i) ⟨K, hK⟩
  refine key.trans (le_of_eq ?_)
  congr 1
  have hint : ∀ i, Integrable (fun x => GammaT (sliceF F x i) (sliceF F x i) (x i))
      (Measure.pi fun _ : Fin N => mu) := fun i => by
    refine Integrable.of_bound (measurable_Gamma_slice hF hF i).aestronglyMeasurable K
      (Filter.Eventually.of_forall fun x => ?_)
    simpa [Real.norm_eq_abs] using hK x i
  have hint' : ∀ i, Integrable (fun x => GammaT (Tensor.slice F x i) (Tensor.slice F x i) (x i))
      (Measure.pi fun _ : Fin N => mu) := hint
  rw [← integral_finsetSum _ fun i _ => hint' i]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  exact sum_slice_Gamma hF hF x

theorem torus_lsi_refEnergy (hac : mu ≪ volume) {a : ℝ} (ha : 0 < a)
    (hrls : ENNReal.ofReal a ≤ rLS mu) {F : Config N d → ℝ} (hF : C1C F) {c B : ℝ} (hc : 0 < c)
    (hFc : ∀ x, c ≤ F x) (hFB : ∀ x, F x ≤ B) :
    a * entR (Measure.pi fun _ : Fin N => mu) (fun x => F x ^ 2) ≤
      2 * (refEnergy mu F).toReal := by
  have h := torus_lsi hac ha hrls hF hc hFc hFB
  have hG0 : 0 ≤ ∫ x, gradPair F F x ∂(Measure.pi fun _ : Fin N => mu) :=
    integral_nonneg (gradPair_nonneg_self F)
  rw [refEnergy_eq_gradPair hac hF, ENNReal.toReal_ofReal hG0]
  rw [div_mul_eq_mul_div, le_div_iff₀ ha] at h
  linarith

end SharpLSI.FL.Gross

end
