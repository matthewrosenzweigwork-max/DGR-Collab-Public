import DGRHS.Commutator.SourceRieszBrownianSquare

/-! Adapted increment pairings in the supplied full filtration. This is the
scalar elementary Ito isometry mechanism; it uses conditional independence,
not independence of stochastic integrals with random adapted coefficients.
The proof follows the elementary conditioning route recorded in the preserved
Apache-2.0 MathFin PointwiseBracket/ItoIsometryAdapted sources. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
namespace DGRHS.Commutator
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

lemma sourceRiesz_brownian_mean_adapted_increment
    (P : Measure Ω) [IsProbabilityMeasure P] (F : Filtration ℝ≥0 mΩ)
    (B : ℝ≥0→Ω→ℝ) (hB : IsPreBrownianReal B P) (hBm : ∀ r,Measurable (B r))
    (s t : ℝ≥0) (hst : s≤t)
    (hind : Indep (MeasurableSpace.comap (fun ω=>B t ω-B s ω) (borel ℝ)) (F s) P)
    (Z : Ω→ℝ) (hZ : StronglyMeasurable[F s] Z) (hZL : MemLp Z 2 P) :
    Integrable (fun ω=>Z ω*(B t ω-B s ω)) P ∧
      (∫ ω,Z ω*(B t ω-B s ω) ∂P)=0 := by
  obtain ⟨hΔ,hΔ0,_⟩ := sourceRiesz_brownian_increment_conditional P F B hB hBm s t hst hind
  have hi := hZL.integrable_mul hΔ
  have he := condExp_mul_of_stronglyMeasurable_left hZ hi
    (hΔ.integrable (by norm_num : (1:ℝ≥0∞)≤2))
  change (P[fun ω=>Z ω*(B t ω-B s ω) | F s])=ᵐ[P]
    (fun ω=>Z ω*(P[fun v=>B t v-B s v | F s]) ω) at he
  have hz : (P[fun ω=>Z ω*(B t ω-B s ω) | F s])=ᵐ[P] (fun _=>0) := by
    filter_upwards [he,hΔ0] with ω hh h0
    simpa only [h0,mul_zero] using hh
  refine ⟨hi,?_⟩
  rw [←integral_condExp (F.le s),integral_congr_ae hz,integral_zero]

lemma sourceRiesz_brownian_mean_bounded_increment_square
    (P : Measure Ω) [IsProbabilityMeasure P] (F : Filtration ℝ≥0 mΩ)
    (B : ℝ≥0→Ω→ℝ) (hB : IsPreBrownianReal B P) (hBm : ∀ r,Measurable (B r))
    (s t : ℝ≥0) (hst : s≤t)
    (hind : Indep (MeasurableSpace.comap (fun ω=>B t ω-B s ω) (borel ℝ)) (F s) P)
    (Z : Ω→ℝ) (hZ : StronglyMeasurable[F s] Z) (K : ℝ)
    (hb : ∀ᵐ ω ∂P,‖Z ω‖≤K) :
    Integrable (fun ω=>Z ω*(B t ω-B s ω)^2) P ∧
      (∫ ω,Z ω*(B t ω-B s ω)^2 ∂P)=(∫ ω,Z ω ∂P)*((t:ℝ)-(s:ℝ)) := by
  obtain ⟨hΔ,_,hΔ2⟩ := sourceRiesz_brownian_increment_conditional P F B hB hBm s t hst hind
  have hi := hΔ.integrable_sq.bdd_mul (hZ.mono (F.le s)).aestronglyMeasurable hb
  have he := condExp_stronglyMeasurable_mul_of_bound (F.le s) hZ hΔ.integrable_sq K hb
  change (P[fun ω=>Z ω*(B t ω-B s ω)^2 | F s])=ᵐ[P]
    (fun ω=>Z ω*(P[fun v=>(B t v-B s v)^2 | F s]) ω) at he
  have hz : (P[fun ω=>Z ω*(B t ω-B s ω)^2 | F s])=ᵐ[P]
      (fun ω=>Z ω*((t:ℝ)-(s:ℝ))) := by
    filter_upwards [he,hΔ2] with ω hh h2
    simpa only [h2] using hh
  refine ⟨hi,?_⟩
  rw [←integral_condExp (F.le s),integral_congr_ae hz,integral_mul_const]

theorem sourceRiesz_brownian_common_start_pairing_ordered
    (P : Measure Ω) [IsProbabilityMeasure P] (F : Filtration ℝ≥0 mΩ)
    (B : ℝ≥0→Ω→ℝ) (hB : IsPreBrownianReal B P) (hBa : StronglyAdapted F B)
    (hind : ∀ s t,s≤t →
      Indep (MeasurableSpace.comap (fun ω=>B t ω-B s ω) (borel ℝ)) (F s) P)
    (a b c : ℝ≥0) (hab : a≤b) (hbc : b≤c)
    (Z : Ω→ℝ) (hZ : StronglyMeasurable[F a] Z) (K : ℝ)
    (hb : ∀ᵐ ω ∂P,‖Z ω‖≤K) :
    Integrable (fun ω=>Z ω*(B b ω-B a ω)*(B c ω-B a ω)) P ∧
      (∫ ω,Z ω*(B b ω-B a ω)*(B c ω-B a ω) ∂P)=
        (∫ ω,Z ω ∂P)*((b:ℝ)-(a:ℝ)) := by
  have hBm (r) : Measurable (B r) := ((hBa r).mono (F.le r)).measurable
  have hZb : StronglyMeasurable[F b] (fun ω=>Z ω*(B b ω-B a ω)) :=
    (hZ.mono (F.mono hab)).mul ((hBa b).sub ((hBa a).mono (F.mono hab)))
  have hZL : MemLp (fun ω=>Z ω*(B b ω-B a ω)) 2 P :=
    sourceRiesz_memLp_bounded_mul P Z _ (hZ.mono (F.le a)).aestronglyMeasurable
      (hB.hasLaw_sub b a).hasGaussianLaw.memLp_two K hb
  obtain ⟨hiz,hz⟩ := sourceRiesz_brownian_mean_adapted_increment P F B hB hBm b c hbc
    (hind b c hbc) _ hZb hZL
  obtain ⟨his,hs⟩ := sourceRiesz_brownian_mean_bounded_increment_square P F B hB hBm a b hab
    (hind a b hab) Z hZ K hb
  have he : (fun ω=>Z ω*(B b ω-B a ω)*(B c ω-B a ω))=
      (fun ω=>Z ω*(B b ω-B a ω)^2)+
      (fun ω=>Z ω*(B b ω-B a ω)*(B c ω-B b ω)) := by
    funext ω
    simp only [Pi.add_apply]
    ring
  rw [he]
  refine ⟨his.add hiz,?_⟩
  change (∫ ω,Z ω*(B b ω-B a ω)^2+Z ω*(B b ω-B a ω)*(B c ω-B b ω) ∂P)=_
  rw [integral_add his hiz,hs,hz,add_zero]

theorem sourceRiesz_brownian_common_start_pairing
    (P : Measure Ω) [IsProbabilityMeasure P] (F : Filtration ℝ≥0 mΩ)
    (B : ℝ≥0→Ω→ℝ) (hB : IsPreBrownianReal B P) (hBa : StronglyAdapted F B)
    (hind : ∀ s t,s≤t →
      Indep (MeasurableSpace.comap (fun ω=>B t ω-B s ω) (borel ℝ)) (F s) P)
    (a b c : ℝ≥0) (hab : a≤b) (hac : a≤c)
    (Z : Ω→ℝ) (hZ : StronglyMeasurable[F a] Z) (K : ℝ)
    (hb : ∀ᵐ ω ∂P,‖Z ω‖≤K) :
    Integrable (fun ω=>Z ω*(B b ω-B a ω)*(B c ω-B a ω)) P ∧
      (∫ ω,Z ω*(B b ω-B a ω)*(B c ω-B a ω) ∂P)=
        (∫ ω,Z ω ∂P)*((min b c:ℝ≥0)-(a:ℝ)) := by
  rcases le_total b c with hbc | hcb
  · simpa only [min_eq_left hbc] using
      sourceRiesz_brownian_common_start_pairing_ordered P F B hB hBa hind a b c hab hbc Z hZ K hb
  · have he : (fun ω=>Z ω*(B b ω-B a ω)*(B c ω-B a ω))=
        (fun ω=>Z ω*(B c ω-B a ω)*(B b ω-B a ω)) := by
      funext ω
      ring
    rw [he,min_eq_right hcb]
    exact sourceRiesz_brownian_common_start_pairing_ordered P F B hB hBa hind a c b hac hcb Z hZ K hb

end DGRHS.Commutator
#check @DGRHS.Commutator.sourceRiesz_brownian_mean_adapted_increment
#print axioms DGRHS.Commutator.sourceRiesz_brownian_mean_adapted_increment
#check @DGRHS.Commutator.sourceRiesz_brownian_mean_bounded_increment_square
#print axioms DGRHS.Commutator.sourceRiesz_brownian_mean_bounded_increment_square
#check @DGRHS.Commutator.sourceRiesz_brownian_common_start_pairing_ordered
#print axioms DGRHS.Commutator.sourceRiesz_brownian_common_start_pairing_ordered
#check @DGRHS.Commutator.sourceRiesz_brownian_common_start_pairing
#print axioms DGRHS.Commutator.sourceRiesz_brownian_common_start_pairing
