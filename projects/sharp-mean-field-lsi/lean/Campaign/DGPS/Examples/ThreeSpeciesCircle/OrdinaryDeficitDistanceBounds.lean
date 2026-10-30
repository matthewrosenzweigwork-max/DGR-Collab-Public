import DGPS.Examples.ThreeSpeciesCircle.OrdinaryOptimizers

/-! Original Haar square-root H1 distance is quantitatively controlled by the
actual relative Fisher information, with a constant fixed before competitors. -/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal

namespace DGPS.Examples.ThreeSpeciesCircle

/-- Every fixed original root has a genuine global H1-distance bound in terms
of the competitor's relative Fisher information. No local stability, compactness,
positive root representative or norm-equivalence estimate is an input. -/
theorem ordinary_originalH1_information_bound (h : ℝ) (σ : AbsoluteDensity 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ ρ : AbsoluteDensity 1,
      ((eLpNorm (fun x => ρ.sqrt x - σ.sqrt x) 2 (haar 1)).toReal +
        (eLpNorm (fun x => weakGradient ρ.sqrt ρ.sqrt_mem x -
          weakGradient σ.sqrt σ.sqrt_mem x) 2 (haar 1)).toReal) ^ 2 ≤
      K * (1 + (ordinaryFisher h ρ).toReal) := by
  let J := DGPS.Analysis.circleFisherInformation σ
  have hJ : 0 ≤ J := circleFisherInformation_nonneg σ
  let K := 10 + 2 * logGradBound h ^ 2 + J
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K, hK, fun ρ => ?_⟩
  let G := weakGradient ρ.sqrt ρ.sqrt_mem
  let S := weakGradient σ.sqrt σ.sqrt_mem
  have hρ := isWeakGradient_weakGradient ρ.sqrt_mem
  have hσ := isWeakGradient_weakGradient σ.sqrt_mem
  have hu : MemLp (fun x => ρ.sqrt x - σ.sqrt x) 2 (haar 1) :=
    ρ.memLp_sqrt.sub σ.memLp_sqrt
  have hg : MemLp (fun x => G x - S x) 2 (haar 1) := hρ.memLp_grad.sub hσ.memLp_grad
  let A := (eLpNorm (fun x => ρ.sqrt x - σ.sqrt x) 2 (haar 1)).toReal
  let B := (eLpNorm (fun x => G x - S x) 2 (haar 1)).toReal
  have hA : A ^ 2 = ∫ x, (ρ.sqrt x - σ.sqrt x) ^ 2 ∂haar 1 := by
    dsimp only [A]
    rw [toReal_eLpNorm_two hu, Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _)]
  have hB : B ^ 2 = ∫ x, ‖G x - S x‖ ^ 2 ∂haar 1 := by
    dsimp only [B]
    rw [toReal_eLpNorm_two_vec hg, Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _)]
  have hA4 : A ^ 2 ≤ 4 := by
    rw [hA]
    have hm := integral_mono hu.integrable_sq
      ((ρ.memLp_sqrt.integrable_sq.const_mul 2).add
        (σ.memLp_sqrt.integrable_sq.const_mul 2))
      (fun x => show (ρ.sqrt x - σ.sqrt x) ^ 2 ≤
        2 * ρ.sqrt x ^ 2 + 2 * σ.sqrt x ^ 2 by
          nlinarith [sq_nonneg (ρ.sqrt x + σ.sqrt x)])
    change (∫ x, (ρ.sqrt x - σ.sqrt x) ^ 2 ∂haar 1) ≤
      ∫ x, 2 * ρ.sqrt x ^ 2 + 2 * σ.sqrt x ^ 2 ∂haar 1 at hm
    rw [integral_add (ρ.memLp_sqrt.integrable_sq.const_mul 2)
      (σ.memLp_sqrt.integrable_sq.const_mul 2), integral_const_mul, integral_const_mul,
      ρ.mass_one, σ.mass_one] at hm
    norm_num at hm ⊢
    exact hm
  have hBg : B ^ 2 ≤ 2 * (∫ x, ‖G x‖ ^ 2 ∂haar 1) +
      2 * (∫ x, ‖S x‖ ^ 2 ∂haar 1) := by
    rw [hB]
    have hGi : Integrable (fun x => ‖G x‖ ^ 2) (haar 1) := hρ.memLp_grad.norm.integrable_sq
    have hSi : Integrable (fun x => ‖S x‖ ^ 2) (haar 1) := hσ.memLp_grad.norm.integrable_sq
    have hpoint (x : Torus 1) : ‖G x - S x‖ ^ 2 ≤ 2 * ‖G x‖ ^ 2 + 2 * ‖S x‖ ^ 2 := by
      have hn := norm_sub_le (G x) (S x)
      have hs := pow_le_pow_left₀ (norm_nonneg _) hn 2
      nlinarith [sq_nonneg (‖G x‖ - ‖S x‖)]
    have hm := integral_mono hg.norm.integrable_sq
      ((hGi.const_mul 2).add (hSi.const_mul 2)) hpoint
    change (∫ x, ‖G x - S x‖ ^ 2 ∂haar 1) ≤
      ∫ x, 2 * ‖G x‖ ^ 2 + 2 * ‖S x‖ ^ 2 ∂haar 1 at hm
    rw [integral_add (hGi.const_mul 2) (hSi.const_mul 2), integral_const_mul,
      integral_const_mul] at hm
    exact hm
  have hdist : (A + B) ^ 2 ≤ 8 + DGPS.Analysis.circleFisherInformation ρ + J := by
    have hρI := circleFisher_eq_four_mul ρ
    have hσI := circleFisher_eq_four_mul σ
    change J = 4 * ∫ x, ‖S x‖ ^ 2 ∂haar 1 at hσI
    change DGPS.Analysis.circleFisherInformation ρ =
      4 * ∫ x, ‖G x‖ ^ 2 ∂haar 1 at hρI
    nlinarith [sq_nonneg (A - B)]
  have h2fin : 2 * ordinaryFisher h ρ ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num) (str025_fisher_ne_top h ρ)
  have hRfin : 2 * ordinaryFisher h ρ + ENNReal.ofReal (2 * logGradBound h ^ 2) ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨h2fin, ENNReal.ofReal_ne_top⟩
  have hIm := ENNReal.toReal_mono hRfin (fisher_le_two_ordinary h ρ)
  rw [ENNReal.toReal_ofReal (circleFisherInformation_nonneg ρ),
    ENNReal.toReal_add h2fin ENNReal.ofReal_ne_top, ENNReal.toReal_mul,
    ENNReal.toReal_ofNat, ENNReal.toReal_ofReal (by positivity)] at hIm
  change (A + B) ^ 2 ≤ K * (1 + (ordinaryFisher h ρ).toReal)
  dsimp only [K]
  have hI0 : 0 ≤ (ordinaryFisher h ρ).toReal := ENNReal.toReal_nonneg
  nlinarith [mul_nonneg (add_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
    (sq_nonneg (logGradBound h))) hJ)
      (show 0 ≤ (ordinaryFisher h ρ).toReal from ENNReal.toReal_nonneg)]

end DGPS.Examples.ThreeSpeciesCircle
