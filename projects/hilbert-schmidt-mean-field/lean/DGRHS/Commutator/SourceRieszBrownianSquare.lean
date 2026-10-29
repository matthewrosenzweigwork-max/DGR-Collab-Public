import DGRHS.Commutator.SourceRieszBrownianStepMartingale

/-! Conditional square identities and the actual Brownian compensated square
in a supplied full filtration. Neither the martingale nor its compensator is
an input. This is the quadratic part of the elementary-integral construction;
it does not yet identify the completed particle-gradient integral. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
namespace DGRHS.Commutator
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

lemma sourceRiesz_conditional_square_add
    (P : Measure Ω) [IsProbabilityMeasure P] (m : MeasurableSpace Ω) (hm : m≤mΩ)
    (X Y : Ω→ℝ) (hX : StronglyMeasurable[m] X)
    (hXL : MemLp X 2 P) (hYL : MemLp Y 2 P)
    (hY0 : (P[Y | m])=ᵐ[P] (fun _=>0)) :
    (P[fun ω=>(X ω+Y ω)^2 | m])=ᵐ[P]
      (fun ω=>X ω^2+(P[fun v=>Y v^2 | m]) ω) := by
  have hXY : Integrable (X*Y) P := hXL.integrable_mul hYL
  have hYi := hYL.integrable (by norm_num : (1:ℝ≥0∞)≤2)
  have hp := condExp_mul_of_stronglyMeasurable_left hX hXY hYi
  have hex : (fun ω=>(X ω+Y ω)^2)=X^2+(2:ℝ) • (X*Y)+Y^2 := by
    funext ω
    simp only [Pi.add_apply,Pi.smul_apply,Pi.mul_apply,Pi.pow_apply,smul_eq_mul]
    ring
  rw [hex]
  have h1 := condExp_add (hXL.integrable_sq.add (hXY.const_mul 2)) hYL.integrable_sq m
  have h2 := condExp_add hXL.integrable_sq (hXY.const_mul 2) m
  have h3 := condExp_smul (2:ℝ) (X*Y) m (μ:=P)
  have h4 : (P[X^2 | m])=X^2 :=
    condExp_of_stronglyMeasurable hm (hX.pow 2) hXL.integrable_sq
  change (P[X^2+(2:ℝ) • (X*Y)+Y^2 | m])=ᵐ[P]
    (P[X^2+(2:ℝ) • (X*Y) | m])+(P[Y^2 | m]) at h1
  change (P[X^2+(2:ℝ) • (X*Y) | m])=ᵐ[P]
    (P[X^2 | m])+(P[(2:ℝ) • (X*Y) | m]) at h2
  filter_upwards [h1,h2,h3,hp,hY0] with ω he1 he2 he3 heP he0
  simp only [Pi.add_apply,Pi.smul_apply,Pi.mul_apply,Pi.pow_apply,smul_eq_mul] at *
  rw [he1,he2,he3,heP,he0,h4]
  simp only [Pi.pow_apply,mul_zero,add_zero]
  rfl

theorem sourceRiesz_brownian_compensated_square
    (P : Measure Ω) [IsProbabilityMeasure P] (F : Filtration ℝ≥0 mΩ)
    (B : ℝ≥0→Ω→ℝ) (hB : IsPreBrownianReal B P)
    (hBa : StronglyAdapted F B)
    (hind : ∀ s t,s≤t →
      Indep (MeasurableSpace.comap (fun ω=>B t ω-B s ω) (borel ℝ)) (F s) P) :
    Martingale (fun t ω=>(B t ω)^2-(t:ℝ)) F P := by
  have hL2 (t) : MemLp (B t) 2 P := (hB.hasLaw_eval t).hasGaussianLaw.memLp_two
  have hBm (t) : Measurable (B t) := ((hBa t).mono (F.le t)).measurable
  refine ⟨fun t=>(hBa t).pow 2 |>.sub stronglyMeasurable_const,?_⟩
  intro s t hst
  obtain ⟨hΔ,hΔ0,hΔ2⟩ := sourceRiesz_brownian_increment_conditional P F B hB hBm s t hst (hind s t hst)
  have hh := sourceRiesz_conditional_square_add P (F s) (F.le s) (B s)
    (fun ω=>B t ω-B s ω) (hBa s) (hL2 s) hΔ hΔ0
  have he : (fun ω=>(B s ω+(B t ω-B s ω))^2)=(fun ω=>(B t ω)^2) := by
    funext ω
    congr 1
    ring
  rw [he] at hh
  have hs := condExp_sub (hL2 t).integrable_sq (integrable_const (t:ℝ)) (F s)
  rw [condExp_const (F.le s)] at hs
  change (P[fun ω=>(B t ω)^2-(t:ℝ) | F s])=ᵐ[P]
    (fun ω=>(P[fun ω=>(B t ω)^2 | F s]) ω-(t:ℝ)) at hs
  filter_upwards [hs,hh,hΔ2] with ω h1 h2 h3
  rw [h1,h2,h3]
  ring

end DGRHS.Commutator
#check @DGRHS.Commutator.sourceRiesz_conditional_square_add
#print axioms DGRHS.Commutator.sourceRiesz_conditional_square_add
#check @DGRHS.Commutator.sourceRiesz_brownian_compensated_square
#print axioms DGRHS.Commutator.sourceRiesz_brownian_compensated_square
