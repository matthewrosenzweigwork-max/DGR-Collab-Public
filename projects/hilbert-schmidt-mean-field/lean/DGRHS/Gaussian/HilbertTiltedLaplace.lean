/- Development draft. Actual uniform integrability and shared-process
linear tilt at the single strict Hilbert-Schmidt threshold, including zero modes. -/
import DGRHS.Gaussian.FiniteTiltedLaplace
import DGRHS.Gaussian.IndexedGaussianLaw
import DGRHS.Kernel.DiagonalResolvent
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators InnerProductSpace
namespace DGRHS.Gaussian
variable {ι H : Type*} [Countable ι] [NormedAddCommGroup H] [InnerProductSpace ℝ H]

set_option maxHeartbeats 800000 in
lemma tiltedDiagonalPartial_Lq_bound (β p δ : ℝ) (hp : 0 < p) (hδ : 0 < δ)
    (a t : ι → ℝ) (hm : ∀ i, δ ≤ 1+p*β*a i)
    (ha : Summable (fun i => (a i)^2)) (ht : Summable (fun i => (t i)^2))
    (f : ι → ℕ) (hf : Function.Injective f) (s : Finset ι) :
    MemLp (tiltedDiagonalPartialExp β a t f s) (ENNReal.ofReal p) IsonormalProcess.iidStdGaussian ∧
    eLpNorm (tiltedDiagonalPartialExp β a t f s) (ENNReal.ofReal p) IsonormalProcess.iidStdGaussian ≤
      ENNReal.ofReal (Real.exp (((∑' i, |DGRHS.Kernel.regularizedLog (p*β*a i)|)+
        (p^2/δ)*(∑' i, (t i)^2))/(2*p))) := by
  have hi := tiltedDiagonalPartial_Lq_exact β p hp a t
    (fun i => hδ.trans_le (hm i)) f hf s
  have hsq : Summable (fun i => (p*β*a i)^2) := by
    have heq : (fun i => (p*β*a i)^2) = (fun i => (p*β)^2*(a i)^2) := by
      funext i
      ring
    rw [heq]
    exact ha.mul_left ((p*β)^2)
  have hlog : Summable (fun i => |DGRHS.Kernel.regularizedLog (p*β*a i)|) := by
    simpa only [Real.norm_eq_abs] using (DGRHS.Kernel.summable_regularizedLog hsq).norm
  have hsumlog : -(∑ i ∈ s, DGRHS.Kernel.regularizedLog (p*β*a i)) ≤
      ∑' i, |DGRHS.Kernel.regularizedLog (p*β*a i)| := by
    calc
      _ ≤ ∑ i ∈ s, |DGRHS.Kernel.regularizedLog (p*β*a i)| := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_le_sum (fun i _ => neg_le_abs _)
      _ ≤ _ := hlog.sum_le_tsum s (fun i _ => abs_nonneg _)
  have hsumt : (∑ i ∈ s, (p*t i)^2/(1+p*β*a i)) ≤ (p^2/δ)*(∑' i, (t i)^2) := by
    calc
      _ ≤ ∑ i ∈ s, (p^2/δ)*(t i)^2 := Finset.sum_le_sum (fun i _ => by
        have hd := div_le_div_of_nonneg_left (sq_nonneg (p*t i)) hδ (hm i)
        calc
          _ ≤ (p*t i)^2/δ := hd
          _ = _ := by ring)
      _ = (p^2/δ)*(∑ i ∈ s, (t i)^2) := (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (ht.sum_le_tsum s (fun i _ => sq_nonneg _))
        (div_nonneg (sq_nonneg p) hδ.le)
  refine ⟨hi.1, ?_⟩
  rw [hi.2]
  exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr
    (div_le_div_of_nonneg_right (add_le_add hsumlog hsumt) (by positivity)))

omit [Countable ι] in
lemma summable_basis_coeff_sq (b : HilbertBasis ι ℝ H) (v : H) :
    Summable (fun i => (b.repr v i)^2) := by
  simpa only [b.repr_apply_apply, pow_two, real_inner_comm] using
    b.summable_inner_mul_inner v v

omit [Countable ι] in
lemma summable_tilted_basis_coeff (b : HilbertBasis ι ℝ H) (v : H)
    (β : ℝ) (a : ι → ℝ) (ha : Summable (fun i => (a i)^2))
    (hm : ∀ i, 0 < 1+β*a i) :
    Summable (fun i => (b.repr v i)^2/(1+β*a i)) := by
  obtain ⟨δ,hδ,hmargin⟩ := DGRHS.Kernel.exists_uniform_spectral_margin β a ha hm
  apply Summable.of_nonneg_of_le
    (fun i => div_nonneg (sq_nonneg _) (hm i).le)
    (fun i => div_le_div_of_nonneg_left (sq_nonneg _) hδ (hmargin i))
  exact (summable_basis_coeff_sq b v).div_const δ

omit [Countable ι] in
lemma tendstoInMeasure_tiltedDiagonalPartial (b : HilbertBasis ι ℝ H) (v : H)
    (β : ℝ) (a : ι → ℝ) (ha : Summable (fun i => (a i)^2))
    (f : ι → ℕ) (hf : Function.Injective f) {ss : ℕ → Finset ι}
    (hss : Tendsto ss atTop atTop) :
    TendstoInMeasure IsonormalProcess.iidStdGaussian
      (fun n => tiltedDiagonalPartialExp β a (fun i => b.repr v i) f (ss n)) atTop
      (fun ω => Real.exp (indexedGaussianIsometry b f hf v ω-(β/2)*centeredGaussianChaos a f ω)) := by
  let Z : ℕ → Lp ℝ 2 IsonormalProcess.iidStdGaussian := fun n =>
    indexedLpPartialSum b f v (ss n) - (β/2) • ∑ i ∈ ss n, centeredChaosTerm a f i
  let z : Lp ℝ 2 IsonormalProcess.iidStdGaussian :=
    indexedGaussianIsometry b f hf v - (β/2) • centeredGaussianChaos a f
  have hz : Tendsto Z atTop (𝓝 z) :=
    (tendsto_indexedLpPartialSum b f hf v hss).sub
      ((tendsto_Lp_centeredGaussianChaos a f hf ha hss).const_smul (β/2))
  have hraw : ∀ n, (Z n : (ℕ → ℝ) → ℝ) =ᵐ[IsonormalProcess.iidStdGaussian]
      (fun ω => ∑ i ∈ ss n, (b.repr v i*ω (f i)+(β*a i/2)*(1-(ω (f i))^2))) := by
    intro n
    filter_upwards [Lp.coeFn_sub (indexedLpPartialSum b f v (ss n))
        ((β/2) • ∑ i ∈ ss n, centeredChaosTerm a f i),
      Lp.coeFn_smul (β/2) (∑ i ∈ ss n, centeredChaosTerm a f i),
      coeFn_indexedLpPartialSum b f v (ss n), coeFn_centeredChaos_sum a f (ss n)]
      with ω h1 h2 h3 h4
    change (indexedLpPartialSum b f v (ss n) - (β/2) • ∑ i ∈ ss n, centeredChaosTerm a f i) ω = _
    rw [h1, Pi.sub_apply, h2, Pi.smul_apply, h3, h4, smul_eq_mul]
    unfold indexedPartialEvaluation
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  have hlim : (z : (ℕ → ℝ) → ℝ) =ᵐ[IsonormalProcess.iidStdGaussian]
      (fun ω => indexedGaussianIsometry b f hf v ω-(β/2)*centeredGaussianChaos a f ω) := by
    filter_upwards [Lp.coeFn_sub (indexedGaussianIsometry b f hf v)
        ((β/2) • centeredGaussianChaos a f),
      Lp.coeFn_smul (β/2) (centeredGaussianChaos a f)] with ω h1 h2
    rw [h1, Pi.sub_apply, h2, Pi.smul_apply, smul_eq_mul]
  have ht := tendstoInMeasure_continuous_real_comp
    (fun n => Lp.aestronglyMeasurable (Z n)) (tendstoInMeasure_of_tendsto_Lp hz)
    Real.exp Real.continuous_exp
  exact ht.congr (fun n => (hraw n).fun_comp Real.exp) (hlim.fun_comp Real.exp)

end DGRHS.Gaussian
#print axioms DGRHS.Gaussian.tiltedDiagonalPartial_Lq_bound
#print axioms DGRHS.Gaussian.summable_basis_coeff_sq
#print axioms DGRHS.Gaussian.summable_tilted_basis_coeff
#print axioms DGRHS.Gaussian.tendstoInMeasure_tiltedDiagonalPartial
#check @DGRHS.Gaussian.tendstoInMeasure_tiltedDiagonalPartial
