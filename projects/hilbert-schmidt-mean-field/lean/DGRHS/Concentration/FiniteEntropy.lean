import DGRHS.Concentration.Entropy
import Mathlib.MeasureTheory.Integral.Pi

noncomputable section
open MeasureTheory MeasureTheory.Measure
namespace DGRHS.Concentration

lemma PositiveBounded.comp_measurePreserving {Ω Ξ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ξ] {μ : Measure Ω} {ν : Measure Ξ}
    {f : Ξ → ℝ} {g : Ω → Ξ} {c C : ℝ}
    (hf : PositiveBounded ν f c C) (hg : MeasurePreserving g μ ν) :
    PositiveBounded μ (fun x ↦ f (g x)) c C :=
  ⟨hf.measurable.comp_quasiMeasurePreserving hg.quasiMeasurePreserving,
    hf.lower_pos, hf.lower_le_upper, hg.quasiMeasurePreserving.ae hf.bounds⟩

lemma functionalEntropy_comp_equiv {Ω Ξ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ξ] {μ : Measure Ω} {ν : Measure Ξ}
    {e : Ω ≃ᵐ Ξ} (he : MeasurePreserving e μ ν) (f : Ξ → ℝ) :
    functionalEntropy μ (fun x ↦ f (e x)) = functionalEntropy ν f := by
  unfold functionalEntropy
  rw [he.integral_comp' (fun x ↦ f x * Real.log (f x)), he.integral_comp' f]

/-- Actual one-coordinate entropy, retaining a full product-space argument. -/
def coordinateEntropy {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Fin n → Measure Ω) (f : (Fin n → Ω) → ℝ) (i : Fin n) (ω : Fin n → Ω) : ℝ :=
  functionalEntropy (μ i) (fun x ↦ f (Function.update ω i x))

lemma pi_split_update {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (i : Fin (n+1)) (ω : Fin (n+1) → Ω) (x : Ω) :
    (MeasurableEquiv.piFinSuccAbove (fun _ ↦ Ω) i).symm
      (x, ((MeasurableEquiv.piFinSuccAbove (fun _ ↦ Ω) i) ω).2) =
      Function.update ω i x := by
  change Fin.insertNth i x (Fin.removeNth i ω) = Function.update ω i x
  exact Fin.insertNth_removeNth i x ω

lemma pi_split_zero {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (x : Ω) (ω : Fin n → Ω) :
    (MeasurableEquiv.piFinSuccAbove (fun _ ↦ Ω) (0 : Fin (n+1))).symm (x,ω) =
      Fin.cons x ω := by
  change Fin.insertNth 0 x ω = Fin.cons (α := fun _ ↦ Ω) x ω
  exact Fin.insertNth_zero' x ω

lemma coordinate_sections_positive {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Fin n → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
    {f : (Fin n → Ω) → ℝ} {c C : ℝ} (hf : PositiveBounded (Measure.pi μ) f c C)
    (i : Fin n) : ∀ᵐ ω ∂Measure.pi μ,
      PositiveBounded (μ i) (fun x ↦ f (Function.update ω i x)) c C := by
  cases n with
  | zero => exact i.elim0
  | succ n =>
    let e := MeasurableEquiv.piFinSuccAbove (fun _ ↦ Ω) i
    have he := measurePreserving_piFinSuccAbove μ i
    have hg := hf.comp_measurePreserving (he.symm e)
    have hs := hg.sections_left
    have hp := he.quasiMeasurePreserving.ae (quasiMeasurePreserving_snd.ae hs)
    simpa only [e, pi_split_update] using hp

lemma coordinate_entropy_integrable {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Fin n → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
    {f : (Fin n → Ω) → ℝ} {c C : ℝ} (hf : PositiveBounded (Measure.pi μ) f c C)
    (i : Fin n) : Integrable (coordinateEntropy μ f i) (Measure.pi μ) := by
  change Integrable (fun ω ↦ functionalEntropy (μ i)
    (fun x ↦ f (Function.update ω i x))) (Measure.pi μ)
  cases n with
  | zero => exact i.elim0
  | succ n =>
    let e := MeasurableEquiv.piFinSuccAbove (fun _ ↦ Ω) i
    have he := measurePreserving_piFinSuccAbove μ i
    have hg := hf.comp_measurePreserving (he.symm e)
    have hq := section_entropy_integrable_left hg
    have hqp : Integrable (fun p : Ω × (Fin n → Ω) ↦
        functionalEntropy (μ i) (fun x ↦ f (e.symm (x,p.2))))
        ((μ i).prod (Measure.pi fun j ↦ μ (i.succAbove j))) := by
      simpa only [one_mul, Function.comp_def] using (integrable_const (1 : ℝ)).mul_prod hq
    have h := he.integrable_comp_of_integrable hqp
    simpa only [e, Function.comp_def, pi_split_update, coordinateEntropy] using h

lemma pi_cons_integral {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Fin (n+1) → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
    {g : (Fin (n+1) → Ω) → ℝ} (hg : Integrable g (Measure.pi μ)) :
    (∫ ω, g ω ∂Measure.pi μ) =
      ∫ a, ∫ v, g (Fin.cons a v) ∂Measure.pi (fun j ↦ μ j.succ) ∂μ 0 := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ ↦ Ω) (0 : Fin (n+1))
  have he := (measurePreserving_piFinSuccAbove μ 0).symm e
  have h := he.integrable_comp_of_integrable hg
  have hi := integral_prod (fun p ↦ g (e.symm p)) h
  rw [he.integral_comp' g] at hi
  simpa only [e, pi_split_zero, Fin.zero_succAbove] using hi

#print axioms DGRHS.Concentration.coordinate_entropy_integrable

lemma pi_split_zero_apply {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (p : Ω × (Fin n → Ω)) :
    (MeasurableEquiv.piFinSuccAbove (fun _ ↦ Ω) (0 : Fin (n+1))).symm p =
      Fin.cons p.1 p.2 := by
  rcases p with ⟨a,v⟩
  exact pi_split_zero a v


lemma coordinate_bounded_sections {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Fin n → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
    {f : (Fin n → Ω) → ℝ} {B : ℝ} (hf : AEStronglyMeasurable f (Measure.pi μ))
    (hb : ∀ᵐ ω ∂Measure.pi μ, |f ω| ≤ B) (i : Fin n) : ∀ᵐ ω ∂Measure.pi μ,
      AEStronglyMeasurable (fun x ↦ f (Function.update ω i x)) (μ i) ∧
      (∀ᵐ x ∂μ i, |f (Function.update ω i x)| ≤ B) := by
  cases n with
  | zero => exact i.elim0
  | succ n =>
    let e := MeasurableEquiv.piFinSuccAbove (fun _ ↦ Ω) i
    have he := measurePreserving_piFinSuccAbove μ i
    have hm := hf.comp_quasiMeasurePreserving (he.symm e).quasiMeasurePreserving
    have hh := (he.symm e).quasiMeasurePreserving.ae hb
    have hs : ∀ᵐ v ∂Measure.pi (fun j ↦ μ (i.succAbove j)),
        AEStronglyMeasurable (fun x ↦ f (e.symm (x,v))) (μ i) ∧
        (∀ᵐ x ∂μ i, |f (e.symm (x,v))| ≤ B) := by
      filter_upwards [hm.prod_swap.prodMk_left,
        ae_ae_of_ae_prod ((measurePreserving_swap
          (μ := Measure.pi fun j ↦ μ (i.succAbove j)) (ν := μ i)).quasiMeasurePreserving.ae hh)] with v hv hb
      exact ⟨hv,hb⟩
    have h := he.quasiMeasurePreserving.ae (quasiMeasurePreserving_snd.ae hs)
    simpa only [e, pi_split_update] using h


lemma coordinate_average_integrable {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Fin n → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
    {g : (Fin n → Ω) → ℝ} (hg : Integrable g (Measure.pi μ)) (i : Fin n) :
    Integrable (fun ω ↦ ∫ x, g (Function.update ω i x) ∂μ i) (Measure.pi μ) := by
  cases n with
  | zero => exact i.elim0
  | succ n =>
    let e := MeasurableEquiv.piFinSuccAbove (fun _ ↦ Ω) i
    have he := measurePreserving_piFinSuccAbove μ i
    have hgp := (he.symm e).integrable_comp_of_integrable hg
    have hq := hgp.integral_prod_right
    have hqp : Integrable (fun p : Ω × (Fin n → Ω) ↦
        ∫ x, g (e.symm (x,p.2)) ∂μ i)
        ((μ i).prod (Measure.pi fun j ↦ μ (i.succAbove j))) := by
      simpa only [one_mul, Function.comp_def] using (integrable_const (1 : ℝ)).mul_prod hq
    have h := he.integrable_comp_of_integrable hqp
    simpa only [e, Function.comp_def, pi_split_update] using h

lemma coordinate_integral_identity {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Fin n → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
    {g : (Fin n → Ω) → ℝ} (hg : Integrable g (Measure.pi μ)) (i : Fin n) :
    (∫ ω, ∫ x, g (Function.update ω i x) ∂μ i ∂Measure.pi μ) =
      ∫ ω, g ω ∂Measure.pi μ := by
  cases n with
  | zero => exact i.elim0
  | succ n =>
    let e := MeasurableEquiv.piFinSuccAbove (fun _ ↦ Ω) i
    have he := measurePreserving_piFinSuccAbove μ i
    have hgp := (he.symm e).integrable_comp_of_integrable hg
    have hq := hgp.integral_prod_right
    have hqp : Integrable (fun p : Ω × (Fin n → Ω) ↦
        ∫ x, g (e.symm (x,p.2)) ∂μ i)
        ((μ i).prod (Measure.pi fun j ↦ μ (i.succAbove j))) := by
      simpa only [one_mul, Function.comp_def] using (integrable_const (1 : ℝ)).mul_prod hq
    calc
      _ = ∫ p : Ω × (Fin n → Ω), ∫ x, g (e.symm (x,p.2)) ∂μ i
          ∂((μ i).prod (Measure.pi fun j ↦ μ (i.succAbove j))) := by
        simpa only [e, pi_split_update] using he.integral_comp'
          (fun p : Ω × (Fin n → Ω) ↦ ∫ x, g (e.symm (x,p.2)) ∂μ i)
      _ = ∫ v, ∫ x, g (e.symm (x,v)) ∂μ i ∂Measure.pi (fun j ↦ μ (i.succAbove j)) := by
        rw [integral_prod _ hqp]
        simp
      _ = ∫ p, g (e.symm p) ∂((μ i).prod (Measure.pi fun j ↦ μ (i.succAbove j))) :=
        (integral_prod_symm _ hgp).symm
      _ = ∫ ω, g ω ∂Measure.pi μ := (he.symm e).integral_comp' g


lemma coordinate_average_positive {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Fin n → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
    {f : (Fin n → Ω) → ℝ} {c C : ℝ} (hf : PositiveBounded (Measure.pi μ) f c C)
    (i : Fin n) : PositiveBounded (Measure.pi μ)
      (fun ω ↦ ∫ x, f (Function.update ω i x) ∂μ i) c C := by
  refine ⟨(coordinate_average_integrable μ hf.integrable i).aestronglyMeasurable,
    hf.lower_pos, hf.lower_le_upper, ?_⟩
  exact (coordinate_sections_positive μ hf i).mono fun _ hω ↦ hω.integral_bounds

#print axioms DGRHS.Concentration.coordinate_average_positive

theorem finite_product_entropy_tensorization {Ω : Type*} [MeasurableSpace Ω] (n : ℕ) :
    ∀ (μ : Fin n → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
      (f : (Fin n → Ω) → ℝ) (c C : ℝ), PositiveBounded (Measure.pi μ) f c C →
    functionalEntropy (Measure.pi μ) f ≤
      ∑ i, ∫ ω, coordinateEntropy μ f i ω ∂Measure.pi μ := by
  induction n with
  | zero =>
    intro μ _ f c C hf
    have hfconst : f = fun _ ↦ f (fun i ↦ i.elim0) := by
      funext ω
      congr 1
      funext i
      exact i.elim0
    rw [hfconst, functionalEntropy_const]
    simp
  | succ n ih =>
    intro μ _ f c C hf
    let ν : Fin n → Measure Ω := fun j ↦ μ j.succ
    let e := MeasurableEquiv.piFinSuccAbove (fun _ ↦ Ω) (0 : Fin (n+1))
    have he := (measurePreserving_piFinSuccAbove μ 0).symm e
    let g : Ω × (Fin n → Ω) → ℝ := fun p ↦ f (Fin.cons p.1 p.2)
    have hg : PositiveBounded ((μ 0).prod (Measure.pi ν)) g c C := by
      simpa only [e, pi_split_zero_apply, Fin.zero_succAbove, g] using hf.comp_measurePreserving he
    have hEnt : functionalEntropy ((μ 0).prod (Measure.pi ν)) g =
        functionalEntropy (Measure.pi μ) f := by
      simpa only [e, pi_split_zero_apply, Fin.zero_succAbove, g] using functionalEntropy_comp_equiv he f
    have ht : ∀ j : Fin n, Integrable
        (fun p : Ω × (Fin n → Ω) ↦ coordinateEntropy μ f j.succ (Fin.cons p.1 p.2))
        ((μ 0).prod (Measure.pi ν)) := by
      intro j
      simpa only [e, Function.comp_def, pi_split_zero_apply, Fin.zero_succAbove] using
        he.integrable_comp_of_integrable (coordinate_entropy_integrable μ hf j.succ)
    have hsum : Integrable (fun a ↦ ∑ j : Fin n,
        ∫ v, coordinateEntropy μ f j.succ (Fin.cons a v) ∂Measure.pi ν) (μ 0) :=
      integrable_finsetSum _ (fun j _ ↦ (ht j).integral_prod_left)
    have hrow : ∀ᵐ a ∂μ 0, functionalEntropy (Measure.pi ν) (fun v ↦ g (a,v)) ≤
        ∑ j : Fin n, ∫ v, coordinateEntropy μ f j.succ (Fin.cons a v) ∂Measure.pi ν := by
      filter_upwards [hg.sections_right] with a ha
      simpa only [coordinateEntropy, g, Fin.cons_update] using ih ν (fun v ↦ g (a,v)) c C ha
    have hrowInt := integral_mono_ae (section_entropy_integrable_right hg) hsum hrow
    rw [integral_finsetSum _ (fun j _ ↦ (ht j).integral_prod_left)] at hrowInt
    have htail : (∫ a, functionalEntropy (Measure.pi ν) (fun v ↦ g (a,v)) ∂μ 0) ≤
        ∑ j : Fin n, ∫ ω, coordinateEntropy μ f j.succ ω ∂Measure.pi μ := by
      calc
        _ ≤ ∑ j : Fin n, ∫ a, ∫ v,
            coordinateEntropy μ f j.succ (Fin.cons a v) ∂Measure.pi ν ∂μ 0 := hrowInt
        _ = _ := by
          apply Finset.sum_congr rfl
          intro j _
          exact (pi_cons_integral μ (coordinate_entropy_integrable μ hf j.succ)).symm
    have hhead : (∫ v, functionalEntropy (μ 0) (fun a ↦ g (a,v)) ∂Measure.pi ν) =
        ∫ ω, coordinateEntropy μ f 0 ω ∂Measure.pi μ := by
      rw [pi_cons_integral μ (coordinate_entropy_integrable μ hf 0)]
      simp [coordinateEntropy, g, Fin.update_cons_zero, ν]
    have htwo := two_factor_entropy_tensorization hg
    rw [hEnt, hhead] at htwo
    rw [Fin.sum_univ_succ]
    linarith

#print axioms DGRHS.Concentration.finite_product_entropy_tensorization


theorem finite_product_entropy_tensorization_of_ae_bounds {Ω : Type*}
    [MeasurableSpace Ω] (n : ℕ) (μ : Fin n → Measure Ω)
    [∀ i, IsProbabilityMeasure (μ i)] (F : (Fin n → Ω) → ℝ) (c C : ℝ)
    (hF : AEStronglyMeasurable F (Measure.pi μ)) (hc : 0 < c)
    (hbounds : ∀ᵐ ω ∂Measure.pi μ, c ≤ F ω ∧ F ω ≤ C) :
    functionalEntropy (Measure.pi μ) F ≤
      ∑ i, ∫ ω, functionalEntropy (μ i) (fun x ↦ F (Function.update ω i x)) ∂Measure.pi μ := by
  have hFI : Integrable F (Measure.pi μ) := integrable_of_ae_abs_le hF
    (hbounds.mono fun _ hx ↦ abs_le_of_bounds hx.1 hx.2)
  have hL : c ≤ ∫ ω, F ω ∂Measure.pi μ := by
    simpa using integral_mono_ae (integrable_const c) hFI (hbounds.mono fun _ hx ↦ hx.1)
  have hU : (∫ ω, F ω ∂Measure.pi μ) ≤ C := by
    simpa using integral_mono_ae hFI (integrable_const C) (hbounds.mono fun _ hx ↦ hx.2)
  exact finite_product_entropy_tensorization n μ F c C ⟨hF,hc,hL.trans hU,hbounds⟩

lemma finite_product_entropy_zero {Ω : Type*} [MeasurableSpace Ω]
    (μ : Fin 0 → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)] (F : (Fin 0 → Ω) → ℝ) :
    functionalEntropy (Measure.pi μ) F = 0 := by
  have hF : F = fun _ ↦ F (fun i ↦ i.elim0) := by
    funext ω
    congr 1
    funext i
    exact i.elim0
  rw [hF, functionalEntropy_const]

lemma finite_product_entropy_one {Ω : Type*} [MeasurableSpace Ω]
    (μ : Fin 1 → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
    (F : (Fin 1 → Ω) → ℝ) (c C : ℝ) (hF : PositiveBounded (Measure.pi μ) F c C) :
    functionalEntropy (Measure.pi μ) F ≤
      ∫ ω, functionalEntropy (μ 0) (fun x ↦ F (Function.update ω 0 x)) ∂Measure.pi μ := by
  simpa [Fin.sum_univ_succ, coordinateEntropy] using
    finite_product_entropy_tensorization 1 μ F c C hF

#print axioms DGRHS.Concentration.coordinate_bounded_sections
#print axioms DGRHS.Concentration.coordinate_average_integrable
#print axioms DGRHS.Concentration.coordinate_integral_identity
#print axioms DGRHS.Concentration.finite_product_entropy_tensorization_of_ae_bounds
#print axioms DGRHS.Concentration.finite_product_entropy_zero
#print axioms DGRHS.Concentration.finite_product_entropy_one
#check @DGRHS.Concentration.finite_product_entropy_tensorization_of_ae_bounds
#check @DGRHS.Concentration.coordinate_bounded_sections
#check @DGRHS.Concentration.coordinate_entropy_integrable
#check @DGRHS.Concentration.coordinate_average_integrable
#check @DGRHS.Concentration.coordinate_integral_identity

end DGRHS.Concentration
