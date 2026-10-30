import DGPS.Examples.ThreeSpeciesCircle.OrdinaryOptimizers

/-! Strong convergence of the actual relative score, and hence of the original
Haar weak gradient, from uniform root convergence and convergence of relative Fisher. -/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal

namespace DGPS.Examples.ThreeSpeciesCircle

private theorem fourier_norm_strong {f : ℕ → Torus 1 → ℝ} {F : Torus 1 → ℝ}
    (hf : ∀ n, MemLp (f n) 2 (haar 1)) (hF : MemLp F 2 (haar 1))
    (hc : ∀ k, Tendsto (fun n => fourierCoeff (f n) k) atTop (𝓝 (fourierCoeff F k)))
    (hE : Tendsto (fun n => ∫ x, f n x ^ 2 ∂haar 1) atTop (𝓝 (∫ x, F x ^ 2 ∂haar 1))) :
    Tendsto (fun n => ∫ x, (f n x - F x) ^ 2 ∂haar 1) atTop (𝓝 0) := by
  classical
  let a := fun n k => ‖fourierCoeff (f n) k‖ ^ 2
  let b := fun k => ‖fourierCoeff F k‖ ^ 2
  let d := fun n k => ‖fourierCoeff (f n) k - fourierCoeff F k‖ ^ 2
  have ha n : HasSum (a n) (∫ x, f n x ^ 2 ∂haar 1) := hasSum_sq_fourierCoeff (hf n)
  have hb : HasSum b (∫ x, F x ^ 2 ∂haar 1) := hasSum_sq_fourierCoeff hF
  have hd n : HasSum (d n) (∫ x, (f n x - F x) ^ 2 ∂haar 1) := by
    convert hasSum_sq_fourierCoeff ((hf n).sub hF) using 1
    funext k
    change ‖fourierCoeff (f n) k - fourierCoeff F k‖ ^ 2 =
      ‖fourierCoeff (fun x => f n x - F x) k‖ ^ 2
    rw [fourierCoeff_sub' (hf n) hF]
  have hpoint (n : ℕ) (k : Fin 1 → ℤ) : d n k ≤ 2 * a n k + 2 * b k := by
    have h := norm_sub_le (fourierCoeff (f n) k) (fourierCoeff F k)
    have hs := pow_le_pow_left₀ (norm_nonneg _) h 2
    dsimp only [a, b, d]
    nlinarith [sq_nonneg (‖fourierCoeff (f n) k‖ - ‖fourierCoeff F k‖)]
  apply tendsto_order.2
  constructor
  · intro c hc0
    exact Eventually.of_forall fun n => hc0.trans_le (integral_nonneg fun _ => sq_nonneg _)
  · intro ε hε
    have hevent : ∀ᶠ s : Finset (Fin 1 → ℤ) in atTop,
        (∫ x, F x ^ 2 ∂haar 1) - ε / 8 < ∑ k ∈ s, b k :=
      hb.eventually (lt_mem_nhds (by linarith))
    obtain ⟨s, hs⟩ := eventually_atTop.1 hevent
    have hsmall : (∫ x, F x ^ 2 ∂haar 1) - ∑ k ∈ s, b k < ε / 8 := by
      linarith [hs s le_rfl]
    have htailA n : (∑' k : {k // k ∉ s}, a n k) =
        (∫ x, f n x ^ 2 ∂haar 1) - ∑ k ∈ s, a n k := by
      have h := (ha n).summable.sum_add_tsum_subtype_compl s
      rw [(ha n).tsum_eq] at h
      linarith
    have htailB : (∑' k : {k // k ∉ s}, b k) =
        (∫ x, F x ^ 2 ∂haar 1) - ∑ k ∈ s, b k := by
      have h := hb.summable.sum_add_tsum_subtype_compl s
      rw [hb.tsum_eq] at h
      linarith
    have hestimate n : (∫ x, (f n x - F x) ^ 2 ∂haar 1) ≤
        (∑ k ∈ s, d n k) +
          2 * ((∫ x, f n x ^ 2 ∂haar 1) - ∑ k ∈ s, a n k) +
          2 * ((∫ x, F x ^ 2 ∂haar 1) - ∑ k ∈ s, b k) := by
      have hsplit := (hd n).summable.sum_add_tsum_subtype_compl s
      rw [(hd n).tsum_eq] at hsplit
      have htail : (∑' k : {k // k ∉ s}, d n k) ≤
          2 * (∑' k : {k // k ∉ s}, a n k) + 2 * (∑' k : {k // k ∉ s}, b k) := by
        calc _ ≤ ∑' k : {k // k ∉ s}, (2 * a n k + 2 * b k) :=
            ((hd n).summable.subtype _).tsum_le_tsum (fun k => hpoint n k)
              ((((ha n).summable.subtype _).mul_left 2).add
                ((hb.summable.subtype _).mul_left 2))
          _ = _ := by
            have hsa : Summable (fun k : {k // k ∉ s} => 2 * a n k) := by
              simpa only [Function.comp_apply] using
                (((ha n).summable.subtype (fun k => k ∉ s)).mul_left 2)
            have hsb : Summable (fun k : {k // k ∉ s} => 2 * b k) := by
              simpa only [Function.comp_apply] using
                ((hb.summable.subtype (fun k => k ∉ s)).mul_left 2)
            rw [hsa.tsum_add hsb, tsum_mul_left, tsum_mul_left]
      rw [htailA, htailB] at htail
      linarith
    have hlowA : Tendsto (fun n => ∑ k ∈ s, a n k) atTop (𝓝 (∑ k ∈ s, b k)) :=
      tendsto_finsetSum s fun k _ => (hc k).norm.pow 2
    have hlowD : Tendsto (fun n => ∑ k ∈ s, d n k) atTop (𝓝 0) := by
      have hkd (k : Fin 1 → ℤ) : Tendsto (fun n => d n k) atTop (𝓝 0) := by
        simpa [d] using ((hc k).sub
          (tendsto_const_nhds (x := fourierCoeff F k))).norm.pow 2
      simpa using tendsto_finsetSum s (fun k _ => hkd k)
    have hU := (hlowD.add ((hE.sub hlowA).const_mul 2)).add
      (tendsto_const_nhds (x := 2 * ((∫ x, F x ^ 2 ∂haar 1) - ∑ k ∈ s, b k)))
    have hu : ∀ᶠ n in atTop,
        (∑ k ∈ s, d n k) +
          2 * ((∫ x, f n x ^ 2 ∂haar 1) - ∑ k ∈ s, a n k) +
          2 * ((∫ x, F x ^ 2 ∂haar 1) - ∑ k ∈ s, b k) < ε :=
      hU.eventually (gt_mem_nhds (by linarith))
    exact hu.mono fun n hn => (hestimate n).trans_lt hn

/-- Actual relative Fisher convergence and a.e. uniform root convergence imply
strong convergence of the original root and its original Haar weak gradient.
The bounded fixed reference drift is removed only after the relative-score norm
has been upgraded to strong convergence. -/
theorem ordinaryFisher_strong_h1_of_uniform (h : ℝ)
    (ρ : ℕ → AbsoluteDensity 1) (ρL : AbsoluteDensity 1)
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0))
    (hae : ∀ n, ∀ᵐ x ∂haar 1, |(ρ n).sqrt x - ρL.sqrt x| ≤ ε n)
    (hI : Tendsto (fun n => (ordinaryFisher h (ρ n)).toReal) atTop
      (𝓝 (ordinaryFisher h ρL).toReal)) :
    Tendsto (fun n =>
      (eLpNorm (fun x => (ρ n).sqrt x - ρL.sqrt x) 2 (haar 1)).toReal +
      (eLpNorm (fun x => weakGradient (ρ n).sqrt (ρ n).sqrt_mem x -
        weakGradient ρL.sqrt ρL.sqrt_mem x) 2 (haar 1)).toReal) atTop (𝓝 0) := by
  let S := fun σ : AbsoluteDensity 1 => fun x =>
    2 * weakGradient σ.sqrt σ.sqrt_mem x 0 - σ.sqrt x * logScore h x
  have hSm (σ : AbsoluteDensity 1) : MemLp (S σ) 2 (haar 1) :=
    ((memLp_coord (isWeakGradient_weakGradient σ.sqrt_mem).memLp_grad 0).const_mul 2).sub
      (memLp_mul_logScore h σ.memLp_sqrt)
  have hIeq (σ : AbsoluteDensity 1) : (ordinaryFisher h σ).toReal =
      ∫ x, S σ x ^ 2 ∂haar 1 := by
    rw [ordinaryFisher_eq, ENNReal.toReal_ofReal (integral_nonneg fun _ => sq_nonneg _)]
  have hc : ∀ k, Tendsto (fun n => fourierCoeff (S (ρ n)) k) atTop
      (𝓝 (fourierCoeff (S ρL) k)) := by
    intro k
    have hu := tendsto_fourierCoeff_of_ae_bound
      (fun n => (ρ n).memLp_sqrt) ρL.memLp_sqrt hε hae k
    have hv : Tendsto (fun n => fourierCoeff (fun x => (ρ n).sqrt x * logScore h x) k)
        atTop (𝓝 (fourierCoeff (fun x => ρL.sqrt x * logScore h x) k)) := by
      refine tendsto_fourierCoeff_of_ae_bound
        (fun n => memLp_mul_logScore h (ρ n).memLp_sqrt)
        (memLp_mul_logScore h ρL.memLp_sqrt)
        (ε := fun n => |ε n| * logGradBound h) ?_ (fun n => ?_) k
      · simpa using hε.abs.mul_const (logGradBound h)
      · filter_upwards [hae n, abs_logScore_le h] with x hx hs
        rw [← sub_mul, abs_mul]
        exact mul_le_mul (hx.trans (le_abs_self _)) hs (abs_nonneg _) (abs_nonneg _)
    have hid (σ : AbsoluteDensity 1) : fourierCoeff (S σ) k =
        2 * (2 * Real.pi * Complex.I * (k 0 : ℂ) * fourierCoeff σ.sqrt k) -
          fourierCoeff (fun x => σ.sqrt x * logScore h x) k := by
      dsimp only [S]
      have hG := isWeakGradient_weakGradient σ.sqrt_mem
      rw [fourierCoeff_sub' ((memLp_coord hG.memLp_grad 0).const_mul 2)
        (memLp_mul_logScore h σ.memLp_sqrt), fourierCoeff_const_mul,
        fourierCoeff_weakGradient hG 0 k]
      simp
    simp_rw [hid]
    exact ((hu.const_mul _).const_mul _).sub hv
  have hScore : Tendsto (fun n => ∫ x, (S (ρ n) x - S ρL x) ^ 2 ∂haar 1)
      atTop (𝓝 0) := by
    apply fourier_norm_strong (fun n => hSm (ρ n)) (hSm ρL) hc
    simpa only [hIeq] using hI
  have hRoot : Tendsto (fun n => ∫ x, ((ρ n).sqrt x - ρL.sqrt x) ^ 2 ∂haar 1)
      atTop (𝓝 0) := by
    refine squeeze_zero (fun _ => integral_nonneg fun _ => sq_nonneg _) (fun n => ?_)
      (by simpa using hε.pow 2)
    have hu : Integrable (fun x => ((ρ n).sqrt x - ρL.sqrt x) ^ 2) (haar 1) := by
      simpa only [Pi.sub_apply] using ((ρ n).memLp_sqrt.sub ρL.memLp_sqrt).integrable_sq
    calc _ ≤ ∫ _x, ε n ^ 2 ∂haar 1 :=
        integral_mono_ae hu
          (integrable_const _) ((hae n).mono fun x hx => by
            change ((ρ n).sqrt x - ρL.sqrt x) ^ 2 ≤ ε n ^ 2
            exact sq_le_sq.mpr (hx.trans (le_abs_self (ε n))))
      _ = ε n ^ 2 := by simp
  let G := fun n x => weakGradient (ρ n).sqrt (ρ n).sqrt_mem x -
    weakGradient ρL.sqrt ρL.sqrt_mem x
  have hGm n : MemLp (G n) 2 (haar 1) :=
    (isWeakGradient_weakGradient (ρ n).sqrt_mem).memLp_grad.sub
      (isWeakGradient_weakGradient ρL.sqrt_mem).memLp_grad
  have hGradBound n : (∫ x, ‖G n x‖ ^ 2 ∂haar 1) ≤
      (1 / 2 : ℝ) * (∫ x, (S (ρ n) x - S ρL x) ^ 2 ∂haar 1) +
        (1 / 2 : ℝ) * logGradBound h ^ 2 *
          (∫ x, ((ρ n).sqrt x - ρL.sqrt x) ^ 2 ∂haar 1) := by
    have hs : Integrable (fun x => (S (ρ n) x - S ρL x) ^ 2) (haar 1) := by
      simpa only [Pi.sub_apply] using ((hSm (ρ n)).sub (hSm ρL)).integrable_sq
    have hu : Integrable (fun x => ((ρ n).sqrt x - ρL.sqrt x) ^ 2) (haar 1) := by
      simpa only [Pi.sub_apply] using ((ρ n).memLp_sqrt.sub ρL.memLp_sqrt).integrable_sq
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_add (hs.const_mul _) (hu.const_mul _)]
    apply integral_mono_ae (hGm n).norm.integrable_sq
      ((hs.const_mul _).add (hu.const_mul _))
    filter_upwards [abs_logScore_le h] with x hx
    have hlog : logScore h x ^ 2 ≤ logGradBound h ^ 2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hx 2
    have halg : (G n x 0) ^ 2 =
        ((S (ρ n) x - S ρL x) + ((ρ n).sqrt x - ρL.sqrt x) * logScore h x) ^ 2 / 4 := by
      dsimp only [G, S]
      simp only [PiLp.sub_apply]
      ring
    rw [tangent1_norm, sq_abs, halg]
    change ((S (ρ n) x - S ρL x) + ((ρ n).sqrt x - ρL.sqrt x) * logScore h x) ^ 2 / 4 ≤
      (1 / 2 : ℝ) * (S (ρ n) x - S ρL x) ^ 2 +
        (1 / 2 : ℝ) * logGradBound h ^ 2 * ((ρ n).sqrt x - ρL.sqrt x) ^ 2
    nlinarith [sq_nonneg ((S (ρ n) x - S ρL x) -
      ((ρ n).sqrt x - ρL.sqrt x) * logScore h x),
      mul_nonneg (sq_nonneg ((ρ n).sqrt x - ρL.sqrt x)) (sub_nonneg.mpr hlog)]
  have hGrad : Tendsto (fun n => ∫ x, ‖G n x‖ ^ 2 ∂haar 1) atTop (𝓝 0) := by
    refine squeeze_zero (fun _ => integral_nonneg fun _ => sq_nonneg _) hGradBound ?_
    simpa using (hScore.const_mul (1 / 2 : ℝ)).add
      (hRoot.const_mul ((1 / 2 : ℝ) * logGradBound h ^ 2))
  have hRnorm : Tendsto (fun n =>
      (eLpNorm (fun x => (ρ n).sqrt x - ρL.sqrt x) 2 (haar 1)).toReal) atTop (𝓝 0) := by
    convert hRoot.sqrt using 1
    · funext n
      exact toReal_eLpNorm_two ((ρ n).memLp_sqrt.sub ρL.memLp_sqrt)
    · simp
  have hGnorm : Tendsto (fun n => (eLpNorm (G n) 2 (haar 1)).toReal) atTop (𝓝 0) := by
    convert hGrad.sqrt using 1
    · funext n
      exact toReal_eLpNorm_two_vec (hGm n)
    · simp
  simpa only [zero_add] using hRnorm.add hGnorm

end DGPS.Examples.ThreeSpeciesCircle
