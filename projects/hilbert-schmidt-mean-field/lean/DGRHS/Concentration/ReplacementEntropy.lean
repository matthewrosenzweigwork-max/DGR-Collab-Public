import DGRHS.Concentration.DeletionEntropy

noncomputable section
open MeasureTheory MeasureTheory.Measure
namespace DGRHS.Concentration

/-- The actual resampled-coordinate vector has the original finite-product law. -/
lemma measurePreserving_coordinate_splice {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Fin n → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)] (i : Fin n) :
    MeasurePreserving (fun p : (Fin n → Ω) × Ω ↦ Function.update p.1 i p.2)
      ((Measure.pi μ).prod (μ i)) (Measure.pi μ) := by
  cases n with
  | zero => exact i.elim0
  | succ n =>
    let e := MeasurableEquiv.piFinSuccAbove (fun _ ↦ Ω) i
    let ν := Measure.pi (fun j ↦ μ (i.succAbove j))
    have he := measurePreserving_piFinSuccAbove μ i
    have hr : MeasurePreserving (fun ω ↦ (e ω).2) (Measure.pi μ) ν := by
      simpa only [Function.comp_def, e, ν] using
        (measurePreserving_snd (μ := μ i) (ν := ν)).comp he
    have hp : MeasurePreserving
        (fun p : (Fin (n+1) → Ω) × Ω ↦ ((e p.1).2,p.2))
        ((Measure.pi μ).prod (μ i)) (ν.prod (μ i)) := by
      change MeasurePreserving (Prod.map (fun ω ↦ (e ω).2) id)
        ((Measure.pi μ).prod (μ i)) (ν.prod (μ i))
      exact hr.prod (MeasurePreserving.id (μ i))
    have hs := (measurePreserving_swap (μ := ν) (ν := μ i)).comp hp
    have h := (he.symm e).comp hs
    change MeasurePreserving (fun p : (Fin (n+1) → Ω) × Ω ↦
      e.symm (p.2,(e p.1).2)) ((Measure.pi μ).prod (μ i)) (Measure.pi μ) at h
    simpa only [e, pi_split_update] using h

lemma coordinate_splice_ae_bounded {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Fin n → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
    {Z : (Fin n → Ω) → ℝ} {B : ℝ}
    (hZ : AEStronglyMeasurable Z (Measure.pi μ))
    (hB : ∀ᵐ ω ∂Measure.pi μ, |Z ω| ≤ B) (i : Fin n) :
    AEStronglyMeasurable (fun p : (Fin n → Ω) × Ω ↦ Z (Function.update p.1 i p.2))
      ((Measure.pi μ).prod (μ i)) ∧
    (∀ᵐ p ∂((Measure.pi μ).prod (μ i)), |Z (Function.update p.1 i p.2)| ≤ B) := by
  have h := (measurePreserving_coordinate_splice μ i).quasiMeasurePreserving
  exact ⟨hZ.comp_quasiMeasurePreserving h, h.ae hB⟩

lemma bounded_positivePart {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f : Ω → ℝ} {B : ℝ} (hf : AEStronglyMeasurable f μ)
    (hB : ∀ᵐ x ∂μ, |f x| ≤ B) :
    AEStronglyMeasurable (fun x ↦ max (f x) 0) μ ∧
      (∀ᵐ x ∂μ, |max (f x) 0| ≤ |B|) := by
  refine ⟨hf.fun_sup aestronglyMeasurable_const, ?_⟩
  filter_upwards [hB] with x hx
  rw [abs_of_nonneg (le_max_right _ _)]
  exact max_le ((le_abs_self _).trans (hx.trans (le_abs_self _))) (abs_nonneg _)

lemma exponential_positive_pair_split (a b : ℝ) :
    (Real.exp a-Real.exp b)*(a-b) =
      (Real.exp a-Real.exp b)*max (a-b) 0 +
      (Real.exp b-Real.exp a)*max (b-a) 0 := by
  by_cases h : b ≤ a
  · rw [max_eq_left (sub_nonneg.mpr h), max_eq_right (sub_nonpos.mpr h)]
    ring
  · have hab := (le_of_not_ge h)
    rw [max_eq_right (sub_nonpos.mpr hab), max_eq_left (sub_nonneg.mpr hab)]
    ring

lemma exponential_positive_pair_bound (a b : ℝ) :
    (Real.exp a-Real.exp b)*max (a-b) 0 ≤ Real.exp a*(max (a-b) 0)^2 := by
  by_cases h : b ≤ a
  · rw [max_eq_left (sub_nonneg.mpr h)]
    have hexp : Real.exp a * Real.exp (b-a) = Real.exp b := by
      rw [← Real.exp_add]
      congr 1
      ring
    have ht := Real.add_one_le_exp (b-a)
    have hp := mul_le_mul_of_nonneg_left ht (Real.exp_pos a).le
    rw [hexp] at hp
    have hd : Real.exp a-Real.exp b ≤ Real.exp a*(a-b) := by nlinarith
    have hh := mul_le_mul_of_nonneg_right hd (sub_nonneg.mpr h)
    calc
      _ ≤ (Real.exp a*(a-b))*(a-b) := hh
      _ = _ := by ring
  · rw [max_eq_right (sub_nonpos.mpr (le_of_not_ge h))]
    simp

lemma max_scalar_mul_nonneg (lam t : ℝ) (hlam : 0 ≤ lam) :
    max (lam*t) 0 = lam*max t 0 := by
  by_cases ht : 0 ≤ t
  · rw [max_eq_left ht, max_eq_left (mul_nonneg hlam ht)]
  · rw [max_eq_right (le_of_not_ge ht), max_eq_right (mul_nonpos_of_nonneg_of_nonpos hlam (le_of_not_ge ht))]
    ring

lemma bounded_square {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f : Ω → ℝ} {B : ℝ} (hf : AEStronglyMeasurable f μ)
    (hB : ∀ᵐ x ∂μ, |f x| ≤ B) :
    AEStronglyMeasurable (fun x ↦ (f x)^2) μ ∧
      (∀ᵐ x ∂μ, |(f x)^2| ≤ |B|^2) := by
  refine ⟨hf.fun_pow 2, ?_⟩
  filter_upwards [hB] with x hx
  rw [pow_two, abs_mul, pow_two]
  exact mul_le_mul (hx.trans (le_abs_self B)) (hx.trans (le_abs_self B))
    (abs_nonneg _) (abs_nonneg _)

lemma bounded_weighted_pair_integrable {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Z : Ω → ℝ} {B : ℝ}
    (hZ : AEStronglyMeasurable Z μ) (hB : ∀ᵐ x ∂μ, |Z x| ≤ B) (lam : ℝ) :
    Integrable (fun p : Ω × Ω ↦ Real.exp (lam*Z p.1) * (max (Z p.1-Z p.2) 0)^2)
      (μ.prod μ) := by
  have hscale := scalar_mul_ae_bounded hZ hB lam
  have hf := bounded_exp_positive hscale.1 hscale.2
  have hd := difference_ae_bounded hZ.comp_fst hZ.comp_snd
    (quasiMeasurePreserving_fst.ae hB) (quasiMeasurePreserving_snd.ae hB)
  have hp := bounded_positivePart hd.1 hd.2
  have hsq := bounded_square hp.1 hp.2
  exact bounded_mul_integrable hf.measurable.comp_fst hsq.1
    (quasiMeasurePreserving_fst.ae (hf.bounds.mono fun _ hx ↦ abs_le_of_bounds hx.1 hx.2)) hsq.2

lemma bounded_positive_pair_integrable {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {U : Ω → ℝ} {B : ℝ}
    (hU : AEStronglyMeasurable U μ) (hB : ∀ᵐ x ∂μ, |U x| ≤ B) :
    Integrable (fun p : Ω × Ω ↦ (Real.exp (U p.1)-Real.exp (U p.2)) *
      max (U p.1-U p.2) 0) (μ.prod μ) := by
  have hf := bounded_exp_positive hU hB
  have hb := hf.bounds.mono fun _ hx ↦ abs_le_of_bounds hx.1 hx.2
  have hd := difference_ae_bounded hU.comp_fst hU.comp_snd
    (quasiMeasurePreserving_fst.ae hB) (quasiMeasurePreserving_snd.ae hB)
  have hp := bounded_positivePart hd.1 hd.2
  have hfd := difference_ae_bounded hf.measurable.comp_fst hf.measurable.comp_snd
    (quasiMeasurePreserving_fst.ae hb) (quasiMeasurePreserving_snd.ae hb)
  exact bounded_mul_integrable hfd.1 hp.1 hfd.2 hp.2

lemma bounded_exp_entropy_covariance {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {U : Ω → ℝ} {B : ℝ}
    (hU : AEStronglyMeasurable U μ) (hB : ∀ᵐ x ∂μ, |U x| ≤ B) :
    functionalEntropy μ (fun x ↦ Real.exp (U x)) ≤
      (∫ x, Real.exp (U x)*U x ∂μ) - (∫ x, Real.exp (U x) ∂μ)*(∫ x, U x ∂μ) := by
  have hOne : PositiveBounded μ (fun _ ↦ (1 : ℝ)) 1 1 :=
    ⟨aestronglyMeasurable_const, by norm_num, le_rfl,
      Filter.Eventually.of_forall fun _ ↦ ⟨le_rfl,le_rfl⟩⟩
  have hJ : (∫ x, U x ∂μ) ≤ Real.log (∫ x, Real.exp (U x) ∂μ) := by
    simpa [functionalEntropy_const] using bounded_variational hOne hU hB
  have hm := (bounded_exp_positive hU hB).integral_pos
  have h := mul_le_mul_of_nonneg_left hJ hm.le
  unfold functionalEntropy
  simp only [Real.log_exp]
  linarith

lemma bounded_exp_pair_covariance {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {U : Ω → ℝ} {B : ℝ}
    (hU : AEStronglyMeasurable U μ) (hB : ∀ᵐ x ∂μ, |U x| ≤ B) :
    (∫ x, Real.exp (U x)*U x ∂μ) - (∫ x, Real.exp (U x) ∂μ)*(∫ x, U x ∂μ) =
      ∫ p : Ω × Ω, (Real.exp (U p.1)-Real.exp (U p.2))*max (U p.1-U p.2) 0 ∂μ.prod μ := by
  let f := fun x ↦ Real.exp (U x)
  have hf := bounded_exp_positive hU hB
  have hUI := integrable_of_ae_abs_le hU hB
  have hFU : Integrable (fun x ↦ f x*U x) μ := bounded_mul_integrable hf.measurable hU
    (hf.bounds.mono fun _ hx ↦ abs_le_of_bounds hx.1 hx.2) hB
  have hA : Integrable (fun p : Ω × Ω ↦ f p.1*U p.1) (μ.prod μ) := by
    simpa only [mul_one] using hFU.mul_prod (integrable_const (1 : ℝ))
  have hB' : Integrable (fun p : Ω × Ω ↦ f p.2*U p.2) (μ.prod μ) := by
    simpa only [one_mul] using (integrable_const (1 : ℝ)).mul_prod hFU
  have hC : Integrable (fun p : Ω × Ω ↦ f p.1*U p.2) (μ.prod μ) := hf.integrable.mul_prod hUI
  have hD : Integrable (fun p : Ω × Ω ↦ U p.1*f p.2) (μ.prod μ) := hUI.mul_prod hf.integrable
  have hAI : (∫ p : Ω × Ω, f p.1*U p.1 ∂μ.prod μ) = ∫ x, f x*U x ∂μ := by
    rw [integral_prod _ hA]
    simp
  have hBI : (∫ p : Ω × Ω, f p.2*U p.2 ∂μ.prod μ) = ∫ x, f x*U x ∂μ := by
    rw [integral_prod_symm _ hB']
    simp
  have hCI : (∫ p : Ω × Ω, f p.1*U p.2 ∂μ.prod μ) = (∫ x, f x ∂μ)*(∫ x, U x ∂μ) := by
    rw [integral_prod _ hC]
    simp_rw [integral_const_mul]
    rw [integral_mul_const]
  have hDI : (∫ p : Ω × Ω, U p.1*f p.2 ∂μ.prod μ) = (∫ x, U x ∂μ)*(∫ x, f x ∂μ) := by
    rw [integral_prod _ hD]
    simp_rw [integral_const_mul]
    rw [integral_mul_const]
  let H := fun p : Ω × Ω ↦ (f p.1-f p.2)*(U p.1-U p.2)
  let K := fun p : Ω × Ω ↦ (f p.1-f p.2)*max (U p.1-U p.2) 0
  have hExpanded : Integrable (fun p : Ω × Ω ↦
      f p.1*U p.1+f p.2*U p.2-f p.1*U p.2-U p.1*f p.2) (μ.prod μ) :=
    ((hA.add hB').sub hC).sub hD
  have hEq : H =ᵐ[μ.prod μ] (fun p : Ω × Ω ↦
      f p.1*U p.1+f p.2*U p.2-f p.1*U p.2-U p.1*f p.2) :=
    Filter.Eventually.of_forall fun p ↦ by dsimp [H]; ring
  have _hH : Integrable H (μ.prod μ) := hExpanded.congr hEq.symm
  have hHI : (∫ p, H p ∂μ.prod μ) = 2*((∫ x, f x*U x ∂μ)-
      (∫ x, f x ∂μ)*(∫ x, U x ∂μ)) := by
    have hAB := integral_add hA hB'
    have hABC := integral_sub (hA.add hB') hC
    have hABCD := integral_sub ((hA.add hB').sub hC) hD
    simp only [Pi.add_apply, Pi.sub_apply] at hAB hABC hABCD
    rw [integral_congr_ae hEq, hABCD, hABC, hAB, hAI, hBI, hCI, hDI]
    ring
  have hK : Integrable K (μ.prod μ) := bounded_positive_pair_integrable hU hB
  have hKs : Integrable (fun p : Ω × Ω ↦ K p.swap) (μ.prod μ) := hK.swap
  have hSwap : (∫ p : Ω × Ω, K p.swap ∂μ.prod μ) = ∫ p, K p ∂μ.prod μ := integral_prod_swap K
  have hSplit : H =ᵐ[μ.prod μ] (fun p ↦ K p+K p.swap) :=
    Filter.Eventually.of_forall fun p ↦ by
      dsimp [H,K,f]
      exact exponential_positive_pair_split (U p.1) (U p.2)
  have hHS : (∫ p, H p ∂μ.prod μ) = 2*(∫ p, K p ∂μ.prod μ) := by
    rw [integral_congr_ae hSplit, integral_add hK hKs, hSwap]
    ring
  change _ = ∫ p, K p ∂μ.prod μ
  dsimp [f] at hHI
  linarith

lemma single_variable_positive_replacement_entropy {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {U : Ω → ℝ} {B : ℝ}
    (hU : AEStronglyMeasurable U μ) (hB : ∀ᵐ x ∂μ, |U x| ≤ B) :
    Integrable (fun p : Ω × Ω ↦ Real.exp (U p.1)*(max (U p.1-U p.2) 0)^2) (μ.prod μ) ∧
    functionalEntropy μ (fun x ↦ Real.exp (U x)) ≤
      ∫ p : Ω × Ω, Real.exp (U p.1)*(max (U p.1-U p.2) 0)^2 ∂μ.prod μ := by
  have hQ : Integrable (fun p : Ω × Ω ↦ Real.exp (U p.1)*(max (U p.1-U p.2) 0)^2) (μ.prod μ) := by
    simpa only [one_mul] using bounded_weighted_pair_integrable hU hB 1
  refine ⟨hQ, ?_⟩
  calc
    _ ≤ (∫ x, Real.exp (U x)*U x ∂μ) -
        (∫ x, Real.exp (U x) ∂μ)*(∫ x, U x ∂μ) := bounded_exp_entropy_covariance hU hB
    _ = ∫ p : Ω × Ω, (Real.exp (U p.1)-Real.exp (U p.2))*max (U p.1-U p.2) 0 ∂μ.prod μ :=
      bounded_exp_pair_covariance hU hB
    _ ≤ _ := integral_mono_ae (bounded_positive_pair_integrable hU hB) hQ
      (Filter.Eventually.of_forall fun p ↦ exponential_positive_pair_bound (U p.1) (U p.2))

lemma single_variable_replacement_entropy {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Z : Ω → ℝ} {B : ℝ}
    (hZ : AEStronglyMeasurable Z μ) (hB : ∀ᵐ x ∂μ, |Z x| ≤ B)
    (lam : ℝ) (hlam : 0 ≤ lam) :
    Integrable (fun p : Ω × Ω ↦ Real.exp (lam*Z p.1)*(max (Z p.1-Z p.2) 0)^2) (μ.prod μ) ∧
    functionalEntropy μ (fun x ↦ Real.exp (lam*Z x)) ≤
      lam^2 * (∫ p : Ω × Ω, Real.exp (lam*Z p.1)*(max (Z p.1-Z p.2) 0)^2 ∂μ.prod μ) := by
  have hs := scalar_mul_ae_bounded hZ hB lam
  have h := (single_variable_positive_replacement_entropy hs.1 hs.2).2
  have heq : (fun p : Ω × Ω ↦ Real.exp (lam*Z p.1)*
      (max (lam*Z p.1-lam*Z p.2) 0)^2) =ᵐ[μ.prod μ]
      (fun p ↦ lam^2 * (Real.exp (lam*Z p.1)*(max (Z p.1-Z p.2) 0)^2)) :=
    Filter.Eventually.of_forall fun p ↦ by
      dsimp only
      have hd : lam*Z p.1-lam*Z p.2 = lam*(Z p.1-Z p.2) := by ring
      rw [hd, max_scalar_mul_nonneg lam (Z p.1-Z p.2) hlam]
      ring
  rw [integral_congr_ae heq, integral_const_mul] at h
  exact ⟨bounded_weighted_pair_integrable hZ hB lam,h⟩

lemma bounded_spliced_pair_integrable {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Fin n → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
    {Z : (Fin n → Ω) → ℝ} {B : ℝ}
    (hZ : AEStronglyMeasurable Z (Measure.pi μ))
    (hB : ∀ᵐ ω ∂Measure.pi μ, |Z ω| ≤ B) (lam : ℝ) (i : Fin n) :
    Integrable (fun p : (Fin n → Ω) × Ω ↦ Real.exp (lam*Z p.1)*
      (max (Z p.1-Z (Function.update p.1 i p.2)) 0)^2)
      ((Measure.pi μ).prod (μ i)) := by
  have hr := coordinate_splice_ae_bounded μ hZ hB i
  have hs := scalar_mul_ae_bounded hZ hB lam
  have hf := bounded_exp_positive hs.1 hs.2
  have hd := difference_ae_bounded hZ.comp_fst hr.1 (quasiMeasurePreserving_fst.ae hB) hr.2
  have hp := bounded_positivePart hd.1 hd.2
  have hsq := bounded_square hp.1 hp.2
  exact bounded_mul_integrable hf.measurable.comp_fst hsq.1
    (quasiMeasurePreserving_fst.ae (hf.bounds.mono fun _ hx ↦ abs_le_of_bounds hx.1 hx.2)) hsq.2

lemma update_coordinate_overwrite {Ω : Type*} {n : ℕ} (ω : Fin n → Ω) (i : Fin n) (x y : Ω) :
    Function.update (Function.update ω i x) i y = Function.update ω i y := by
  classical
  funext j
  by_cases h : j = i
  · subst j
    simp
  · simp [Function.update, h]

/-- Replacement entropy with an actual independent fresh coordinate for each original coordinate. -/
theorem finite_product_replacement_entropy {Ω : Type*} [MeasurableSpace Ω] (n : ℕ)
    (μ : Fin n → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
    (Z : (Fin n → Ω) → ℝ) (B : ℝ)
    (hZ : AEStronglyMeasurable Z (Measure.pi μ))
    (hB : ∀ᵐ ω ∂Measure.pi μ, |Z ω| ≤ B) (lam : ℝ) (hlam : 0 ≤ lam) :
    functionalEntropy (Measure.pi μ) (fun ω ↦ Real.exp (lam*Z ω)) ≤
      lam^2 * (∑ i, ∫ p : (Fin n → Ω) × Ω, Real.exp (lam*Z p.1)*
        (max (Z p.1-Z (Function.update p.1 i p.2)) 0)^2 ∂((Measure.pi μ).prod (μ i))) := by
  let F := fun ω ↦ Real.exp (lam*Z ω)
  let G := fun i (p : (Fin n → Ω) × Ω) ↦ F p.1 * (max (Z p.1-Z (Function.update p.1 i p.2)) 0)^2
  let H := fun i ω ↦ ∫ y, G i (ω,y) ∂μ i
  have hs := scalar_mul_ae_bounded hZ hB lam
  have hf : PositiveBounded (Measure.pi μ) F (Real.exp (-abs (abs lam * abs B)))
      (Real.exp (abs (abs lam * abs B))) := bounded_exp_positive hs.1 hs.2
  have hG : ∀ i, Integrable (G i) ((Measure.pi μ).prod (μ i)) :=
    fun i ↦ bounded_spliced_pair_integrable μ hZ hB lam i
  have hH : ∀ i, Integrable (H i) (Measure.pi μ) := fun i ↦ (hG i).integral_prod_left
  have hc : ∀ i, (∫ ω, coordinateEntropy μ F i ω ∂Measure.pi μ) ≤
      lam^2 * (∫ p, G i p ∂((Measure.pi μ).prod (μ i))) := by
    intro i
    have hpoint : ∀ᵐ ω ∂Measure.pi μ, coordinateEntropy μ F i ω ≤
        lam^2 * (∫ x, H i (Function.update ω i x) ∂μ i) := by
      filter_upwards [coordinate_bounded_sections μ hZ hB i] with ω hω
      have h := single_variable_replacement_entropy hω.1 hω.2 lam hlam
      have heq : (fun p : Ω × Ω ↦ Real.exp (lam*Z (Function.update ω i p.1))*
          (max (Z (Function.update ω i p.1)-Z (Function.update ω i p.2)) 0)^2) =
          (fun p : Ω × Ω ↦ G i (Function.update ω i p.1,p.2)) := by
        funext p
        dsimp [G,F]
        rw [update_coordinate_overwrite]
      have hpair : Integrable (fun p : Ω × Ω ↦ G i (Function.update ω i p.1,p.2))
          ((μ i).prod (μ i)) := by simpa only [heq] using h.1
      have hi : (∫ p : Ω × Ω, Real.exp (lam*Z (Function.update ω i p.1))*
          (max (Z (Function.update ω i p.1)-Z (Function.update ω i p.2)) 0)^2 ∂(μ i).prod (μ i)) =
          ∫ x, H i (Function.update ω i x) ∂μ i := by
        rw [heq, integral_prod _ hpair]
      exact hi ▸ h.2
    have h := integral_mono_ae (coordinate_entropy_integrable μ hf i)
      ((coordinate_average_integrable μ (hH i) i).const_mul (lam^2)) hpoint
    rw [integral_const_mul, coordinate_integral_identity μ (hH i) i] at h
    have hOuter : (∫ ω, H i ω ∂Measure.pi μ) = ∫ p, G i p ∂((Measure.pi μ).prod (μ i)) :=
      (integral_prod _ (hG i)).symm
    rw [hOuter] at h
    exact h
  have ht := finite_product_entropy_tensorization n μ F _ _ hf
  calc
    _ ≤ ∑ i, lam^2 * (∫ p, G i p ∂((Measure.pi μ).prod (μ i))) :=
      ht.trans (Finset.sum_le_sum fun i _ ↦ hc i)
    _ = _ := by rw [Finset.mul_sum]

#print axioms DGRHS.Concentration.measurePreserving_coordinate_splice
#print axioms DGRHS.Concentration.bounded_exp_entropy_covariance
#print axioms DGRHS.Concentration.bounded_exp_pair_covariance
#print axioms DGRHS.Concentration.single_variable_replacement_entropy
#print axioms DGRHS.Concentration.bounded_spliced_pair_integrable
#print axioms DGRHS.Concentration.finite_product_replacement_entropy
#check @DGRHS.Concentration.finite_product_replacement_entropy
/-- The actual conditional positive replacement variance. -/
def coordinateReplacementVariance {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Fin n → Measure Ω) (Z : (Fin n → Ω) → ℝ) (i : Fin n) (ω : Fin n → Ω) : ℝ :=
  ∫ y, (max (Z ω-Z (Function.update ω i y)) 0)^2 ∂μ i

lemma bounded_spliced_square_integrable {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Fin n → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
    {Z : (Fin n → Ω) → ℝ} {B : ℝ}
    (hZ : AEStronglyMeasurable Z (Measure.pi μ))
    (hB : ∀ᵐ ω ∂Measure.pi μ, |Z ω| ≤ B) (i : Fin n) :
    Integrable (fun p : (Fin n → Ω) × Ω ↦
      (max (Z p.1-Z (Function.update p.1 i p.2)) 0)^2)
      ((Measure.pi μ).prod (μ i)) := by
  have hr := coordinate_splice_ae_bounded μ hZ hB i
  have hd := difference_ae_bounded hZ.comp_fst hr.1
    (quasiMeasurePreserving_fst.ae hB) hr.2
  have hp := bounded_positivePart hd.1 hd.2
  have hsq := bounded_square hp.1 hp.2
  exact integrable_of_ae_abs_le hsq.1 hsq.2

lemma coordinate_replacement_variance_integrable {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Fin n → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
    {Z : (Fin n → Ω) → ℝ} {B : ℝ}
    (hZ : AEStronglyMeasurable Z (Measure.pi μ))
    (hB : ∀ᵐ ω ∂Measure.pi μ, |Z ω| ≤ B) (i : Fin n) :
    Integrable (coordinateReplacementVariance μ Z i) (Measure.pi μ) := by
  exact (bounded_spliced_square_integrable μ hZ hB i).integral_prod_left

lemma weighted_coordinate_replacement_integrable {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Fin n → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
    {Z : (Fin n → Ω) → ℝ} {B : ℝ}
    (hZ : AEStronglyMeasurable Z (Measure.pi μ))
    (hB : ∀ᵐ ω ∂Measure.pi μ, |Z ω| ≤ B) (lam : ℝ) (i : Fin n) :
    Integrable (fun ω ↦ Real.exp (lam*Z ω)*coordinateReplacementVariance μ Z i ω)
      (Measure.pi μ) := by
  have h := (bounded_spliced_pair_integrable μ hZ hB lam i).integral_prod_left
  simpa only [coordinateReplacementVariance, integral_const_mul] using h

lemma weighted_replacement_variance_integrable {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Fin n → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
    {Z : (Fin n → Ω) → ℝ} {B : ℝ}
    (hZ : AEStronglyMeasurable Z (Measure.pi μ))
    (hB : ∀ᵐ ω ∂Measure.pi μ, |Z ω| ≤ B) (lam : ℝ) :
    Integrable (fun ω ↦ Real.exp (lam*Z ω)*(∑ i, coordinateReplacementVariance μ Z i ω))
      (Measure.pi μ) := by
  have h := integrable_finsetSum Finset.univ
    (fun i _ ↦ weighted_coordinate_replacement_integrable μ hZ hB lam i)
  exact h.congr (Filter.Eventually.of_forall fun ω ↦ by simp only [Finset.mul_sum])

/-- Actual conditional positive replacement variance; no concentration premise. -/
theorem finite_product_conditional_replacement_entropy {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (μ : Fin n → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
    (Z : (Fin n → Ω) → ℝ) (B : ℝ)
    (hZ : AEStronglyMeasurable Z (Measure.pi μ))
    (hB : ∀ᵐ ω ∂Measure.pi μ, |Z ω| ≤ B) (lam : ℝ) (hlam : 0 ≤ lam) :
    functionalEntropy (Measure.pi μ) (fun ω ↦ Real.exp (lam*Z ω)) ≤
      lam^2 * (∫ ω, Real.exp (lam*Z ω)*(∑ i, coordinateReplacementVariance μ Z i ω)
        ∂Measure.pi μ) := by
  have h := finite_product_replacement_entropy n μ Z B hZ hB lam hlam
  have hi : (∑ i, ∫ p : (Fin n → Ω) × Ω, Real.exp (lam*Z p.1)*
      (max (Z p.1-Z (Function.update p.1 i p.2)) 0)^2 ∂((Measure.pi μ).prod (μ i))) =
      ∫ ω, Real.exp (lam*Z ω)*(∑ i, coordinateReplacementVariance μ Z i ω) ∂Measure.pi μ := by
    calc
      _ = ∑ i, ∫ ω, Real.exp (lam*Z ω)*coordinateReplacementVariance μ Z i ω ∂Measure.pi μ := by
        apply Finset.sum_congr rfl
        intro i _
        rw [integral_prod _ (bounded_spliced_pair_integrable μ hZ hB lam i)]
        simp only [coordinateReplacementVariance, integral_const_mul]
      _ = ∫ ω, ∑ i, Real.exp (lam*Z ω)*coordinateReplacementVariance μ Z i ω ∂Measure.pi μ := by
        rw [integral_finsetSum Finset.univ
          (fun i _ ↦ weighted_coordinate_replacement_integrable μ hZ hB lam i)]
      _ = _ := by congr 1; funext ω; rw [Finset.mul_sum]
  rw [hi] at h
  exact h

lemma finite_product_replacement_entropy_zero {Ω : Type*} [MeasurableSpace Ω]
    (μ : Fin 0 → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
    (Z : (Fin 0 → Ω) → ℝ) (lam : ℝ) :
    functionalEntropy (Measure.pi μ) (fun ω ↦ Real.exp (lam*Z ω)) = 0 ∧
      (∫ ω, Real.exp (lam*Z ω)*(∑ i, coordinateReplacementVariance μ Z i ω) ∂Measure.pi μ) = 0 := by
  constructor
  · exact finite_product_entropy_zero μ _
  · simp

#print axioms DGRHS.Concentration.finite_product_conditional_replacement_entropy
#print axioms DGRHS.Concentration.weighted_replacement_variance_integrable
#check DGRHS.Concentration.finite_product_conditional_replacement_entropy

lemma coordinate_replacement_variance_nonneg {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Fin n → Measure Ω) (Z : (Fin n → Ω) → ℝ) (i : Fin n) (ω : Fin n → Ω) :
    0 ≤ coordinateReplacementVariance μ Z i ω := by
  exact integral_nonneg fun y ↦ sq_nonneg _

lemma coordinate_replacement_variance_const {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Fin n → Measure Ω) (z : ℝ) (i : Fin n) (ω : Fin n → Ω) :
    coordinateReplacementVariance μ (fun _ ↦ z) i ω = 0 := by
  simp [coordinateReplacementVariance]

lemma finite_product_replacement_entropy_parameter_zero {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Fin n → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)] (Z : (Fin n → Ω) → ℝ) :
    functionalEntropy (Measure.pi μ) (fun ω ↦ Real.exp (0*Z ω)) = 0 ∧
      (0 : ℝ)^2 * (∫ ω, Real.exp (0*Z ω)*(∑ i, coordinateReplacementVariance μ Z i ω)
        ∂Measure.pi μ) = 0 := by
  simp [functionalEntropy]

lemma finite_product_replacement_entropy_const {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Fin n → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)] (z lam : ℝ) :
    functionalEntropy (Measure.pi μ) (fun _ ↦ Real.exp (lam*z)) = 0 ∧
      (∫ ω, Real.exp (lam*z)*(∑ i, coordinateReplacementVariance μ (fun _ ↦ z) i ω)
        ∂Measure.pi μ) = 0 := by
  constructor
  · exact functionalEntropy_const (Measure.pi μ) _
  · simp [coordinate_replacement_variance_const]

end DGRHS.Concentration
