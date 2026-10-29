/- Genuine finite vectors under the SAME quadratic tilt, obtained from the
actual scalar readout laws. Correlations and null covariance directions remain. -/
import DGRHS.Gaussian.HilbertTiltedScalarLaw
import DGRHS.Gaussian.IndexedGaussianTuple
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators InnerProductSpace
namespace DGRHS.Gaussian
variable {ι H : Type*} [Countable ι] [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] [CompleteSpace H]

lemma indexedGaussian_tuple_under_ac_gaussian_readouts {m : ℕ}
    (b : HilbertBasis ι ℝ H) (f : ι → ℕ) (hf : Function.Injective f)
    (P : Measure (ℕ → ℝ)) (hac : P ≪ IsonormalProcess.iidStdGaussian)
    (q : H → ℝ)
    (hmap : ∀ v, P.map (indexedGaussianIsometry b f hf v) = gaussianReal 0 (Real.toNNReal (q v)))
    (v : Fin m → H) :
    HasGaussianLaw (fun ω k => indexedGaussianIsometry b f hf (v k) ω) P := by
  classical
  let W := indexedGaussianIsometry b f hf
  let X : (ℕ → ℝ) → (Fin m → ℝ) := fun ω k => W (v k) ω
  have hm : AEMeasurable X P := by
    apply aemeasurable_pi_iff.mpr
    intro k
    exact (Lp.aestronglyMeasurable (W (v k))).aemeasurable.mono_ac hac
  have hgauss : IsGaussian (P.map X) := by
    apply isGaussian_of_map_eq_gaussianReal
    intro L
    let z : H := ∑ k, L (Pi.single k 1) • v k
    have hz : (W z : Lp ℝ 2 IsonormalProcess.iidStdGaussian) =
        ∑ k, L (Pi.single k 1) • W (v k) := by
      dsimp only [z]
      rw [map_sum]
      simp_rw [map_smul]
    have hcoeff : ∀ k : Fin m,
        ((L (Pi.single k 1) • W (v k) : Lp ℝ 2 IsonormalProcess.iidStdGaussian) : (ℕ → ℝ) → ℝ) =ᵐ[IsonormalProcess.iidStdGaussian]
          fun ω => L (Pi.single k 1) * W (v k) ω := by
      intro k
      filter_upwards [Lp.coeFn_smul (L (Pi.single k 1)) (W (v k))] with ω hω
      rw [hω]
      rfl
    have hsum : (W z : (ℕ → ℝ) → ℝ) =ᵐ[IsonormalProcess.iidStdGaussian]
        fun ω => ∑ k, L (Pi.single k 1) * W (v k) ω := by
      rw [hz]
      apply (IsonormalProcess.coeFn_lp_finset_sum
        (fun k => L (Pi.single k 1) • W (v k)) Finset.univ).trans
      filter_upwards [ae_all_iff.mpr hcoeff] with ω hω
      exact Finset.sum_congr rfl (fun k _ => hω k)
    have hLX : (fun ω => L (X ω)) =ᵐ[P] (W z : (ℕ → ℝ) → ℝ) := by
      filter_upwards [hac.ae_le hsum] with ω hω
      rw [hω]
      have he : L (X ω) = ∑ k, (X ω k) • L (Pi.single k 1) := by
        conv_lhs => rw [pi_eq_sum_univ' (X ω)]
        rw [map_sum]
        simp only [map_smul]
      rw [he]
      apply Finset.sum_congr rfl
      intro k _
      dsimp [X]
      simp only [smul_eq_mul,mul_comm]
    refine ⟨0,Real.toNNReal (q z),?_⟩
    rw [AEMeasurable.map_map_of_aemeasurable L.continuous.measurable.aemeasurable hm]
    change P.map (fun ω => L (X ω)) = _
    rw [Measure.map_congr hLX]
    exact hmap z
  exact { aemeasurable := hm, isGaussian_map := hgauss }

/-- Full finite joint Gaussian law with the true inverse, including empty tuples. -/
theorem exists_hilbert_tilted_gaussian_vectors (T : H →L[ℝ] H)
    (hT : T.toLinearMap.IsSymmetric) (b : HilbertBasis ι ℝ H) (a : ι → ℝ)
    (he : ∀ i, T (b i) = a i • b i) (β : ℝ) (ha : Summable (fun i => (a i)^2))
    (hm : ∀ i, 0 < 1+β*a i) (f : ι → ℕ) (hf : Function.Injective f) :
    ∃ R : H →L[ℝ] H,
      (∀ v, R v + β • T (R v) = v) ∧
      (∀ v, R (v + β • T v) = v) ∧
      (∀ v, (IsonormalProcess.iidStdGaussian.tilted
        (fun ω => -(β/2)*centeredGaussianChaos a f ω)).map
          (indexedGaussianIsometry b f hf v) = gaussianReal 0 (Real.toNNReal (inner ℝ v (R v)))) ∧
      ∀ (m : ℕ) (v : Fin m → H), HasGaussianLaw
        (fun ω k => indexedGaussianIsometry b f hf (v k) ω)
        (IsonormalProcess.iidStdGaussian.tilted (fun ω => -(β/2)*centeredGaussianChaos a f ω)) := by
  obtain ⟨R,hR1,hR2,hRc,hmap⟩ := exists_hilbert_tilted_gaussian_readouts T hT b a he β ha hm f hf
  refine ⟨R,hR1,hR2,hmap,fun m v => ?_⟩
  exact indexedGaussian_tuple_under_ac_gaussian_readouts b f hf _
    (tilted_absolutelyContinuous _ _) (fun v => inner ℝ v (R v)) hmap v
end DGRHS.Gaussian
#print axioms DGRHS.Gaussian.indexedGaussian_tuple_under_ac_gaussian_readouts
#print axioms DGRHS.Gaussian.exists_hilbert_tilted_gaussian_vectors
#check @DGRHS.Gaussian.exists_hilbert_tilted_gaussian_vectors
