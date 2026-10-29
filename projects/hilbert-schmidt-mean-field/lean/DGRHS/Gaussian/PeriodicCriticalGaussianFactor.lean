import DGRHS.Gaussian.PeriodicGaussianPairCoordinates
import DGRHS.Gaussian.PeriodicFirstShellBesselProduct
import DGRHS.Gaussian.PeriodicHalfGaussianMoment

/-! Exact critical first-shell moment under the actual Gaussian law.
The genuine product law and proper half-Gaussian factor produce the scalar
radial moment to the dimension power, with no factorization assumption. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Classical BigOperators
namespace DGRHS.Periodic
open DGRHS.Gaussian
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

lemma periodic_critical_sqrt_coefficient (N : ℕ) (hN : 1≤N) :
    Real.sqrt (periodicStabilityThreshold ι/N)*Real.sqrt (2*(periodicStabilityThreshold ι)⁻¹)*Real.sqrt 2 =
      2/Real.sqrt (N:ℝ) := by
  have hb : 0<periodicStabilityThreshold ι := periodicStabilityThreshold_pos
  have hn : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hs : (Real.sqrt (periodicStabilityThreshold ι/N)*Real.sqrt (2*(periodicStabilityThreshold ι)⁻¹)*Real.sqrt 2)^2 =
      (2/Real.sqrt (N:ℝ))^2 := by
    simp only [mul_pow,div_pow]
    rw [Real.sq_sqrt (div_nonneg hb.le hn.le),Real.sq_sqrt (by positivity),
      Real.sq_sqrt (by norm_num : (0:ℝ)≤2),Real.sq_sqrt hn.le]
    field_simp
  have hl : 0≤Real.sqrt (periodicStabilityThreshold ι/N)*Real.sqrt (2*(periodicStabilityThreshold ι)⁻¹)*Real.sqrt 2 := by positivity
  have hr : 0≤2/Real.sqrt (N:ℝ) := by positivity
  nlinarith

lemma periodic_complex_pair_norm (a b : ℝ) :
    ‖(a:ℂ)+(b:ℂ)*Complex.I‖=Real.sqrt (a^2+b^2) := by
  rw [Complex.norm_def]
  congr 1
  simp [Complex.normSq_apply,pow_two]

lemma periodicFirstShellNormalizer_critical_scaled (N : ℕ) (hN : 1≤N)
    (w : ι → ℝ × ℝ) :
    periodicFirstShellNormalizer (Real.sqrt (periodicStabilityThreshold ι/N))
      (fun q => Real.sqrt 2*periodicPairCoordinates w q) =
      ∏ i : ι,periodicBesselI0 (2*Real.sqrt ((w i).1^2+(w i).2^2)/Real.sqrt (N:ℝ)) := by
  rw [periodicFirstShellNormalizer_bessel_product]
  apply Finset.prod_congr rfl
  intro i _
  congr 1
  simp only [periodicPairCoordinates,Bool.false_eq_true,↓reduceIte]
  have he : ((Real.sqrt 2*(w i).1:ℝ):ℂ)+((Real.sqrt 2*(w i).2:ℝ):ℂ)*Complex.I =
      (Real.sqrt 2:ℂ)*(((w i).1:ℂ)+((w i).2:ℂ)*Complex.I) := by push_cast;ring
  rw [he,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),
    periodic_complex_pair_norm,←mul_assoc,periodic_critical_sqrt_coefficient N hN]
  ring

lemma periodicFirstShellNormalizer_stronglyMeasurable (t : ℝ) :
    StronglyMeasurable (periodicFirstShellNormalizer (ι := ι) t) := by
  have he : periodicFirstShellNormalizer (ι := ι) t = fun z => ∏ j : ι,periodicBesselI0
      ((t*Real.sqrt (2*(periodicStabilityThreshold ι)⁻¹))*
        ‖(z (j,false):ℂ)+(z (j,true):ℂ)*Complex.I‖) := funext (periodicFirstShellNormalizer_bessel_product t)
  rw [he]
  apply Measurable.stronglyMeasurable
  apply Finset.measurable_prod
  intro j _
  exact stronglyMeasurable_periodicBesselI0.measurable.comp (by fun_prop)

/-- The exact moment appearing in the genuine full-partition lower bound. -/
theorem periodic_critical_gaussian_normalizer_factor (N : ℕ) (hN : 1≤N) :
    (∫⁻ z,ENNReal.ofReal (periodicFirstShellNormalizer (Real.sqrt (periodicStabilityThreshold ι/N)) z^N)
      ∂finiteStandardGaussian (ι × Bool)) =
      ENNReal.ofReal ((∫ p : ℝ × ℝ,(periodicBesselI0
        (2*Real.sqrt (p.1^2+p.2^2)/Real.sqrt (N:ℝ)))^N
        ∂(gaussianReal 0 (1/2)).prod (gaussianReal 0 (1/2)))^(Fintype.card ι)) := by
  let H := fun p : ℝ × ℝ => (periodicBesselI0 (2*Real.sqrt (p.1^2+p.2^2)/Real.sqrt (N:ℝ)))^N
  let ν := (gaussianReal 0 (1/2)).prod (gaussianReal 0 (1/2))
  have hp := periodicHalfGaussian_coordinates_preserving (ι := ι)
  have hm := ((periodicFirstShellNormalizer_stronglyMeasurable (ι := ι)
    (Real.sqrt (periodicStabilityThreshold ι/N))).measurable.pow_const N).ennreal_ofReal
  rw [←hp.map_eq,lintegral_map' hm.aemeasurable hp.aemeasurable]
  have he : (fun w : ι → ℝ × ℝ => ENNReal.ofReal
      (periodicFirstShellNormalizer (Real.sqrt (periodicStabilityThreshold ι/N))
        (fun q => Real.sqrt 2*periodicPairCoordinates w q)^N)) =
      fun w => ENNReal.ofReal (∏ i : ι,H (w i)) := by
    funext w
    rw [periodicFirstShellNormalizer_critical_scaled N hN,Finset.prod_pow]
  change (∫⁻ w : ι → ℝ × ℝ,ENNReal.ofReal
      (periodicFirstShellNormalizer (Real.sqrt (periodicStabilityThreshold ι/N))
        (fun q => Real.sqrt 2*periodicPairCoordinates w q)^N) ∂Measure.pi (fun _ => ν))=_
  rw [he,←ofReal_integral_eq_lintegral_ofReal
    (Integrable.fintype_prod (fun _ : ι => periodic_halfGaussian_Bessel_integrable N hN))
    (Eventually.of_forall fun w => Finset.prod_nonneg (fun i _ => pow_nonneg (periodicBesselI0_pos _).le N)),
    integral_fintype_prod_eq_pow H]

end DGRHS.Periodic
#print axioms DGRHS.Periodic.periodic_critical_sqrt_coefficient
#print axioms DGRHS.Periodic.periodic_complex_pair_norm
#print axioms DGRHS.Periodic.periodicFirstShellNormalizer_critical_scaled
#print axioms DGRHS.Periodic.periodicFirstShellNormalizer_stronglyMeasurable
#print axioms DGRHS.Periodic.periodic_critical_gaussian_normalizer_factor
#check @DGRHS.Periodic.periodic_critical_gaussian_normalizer_factor
