import DGRHS.Commutator.SourceRieszTruncatedTransportKernelGaussianWidening

/-! Actual scale-dependent Gaussian derivatives and repeated transport contraction.
The widened scale is exactly twice the original scale. -/
noncomputable section
open scoped NNReal
namespace DGRHS.Commutator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma contDiff_sourceRieszGaussianScale (n : ℕ) (t : ℝ) :
    ContDiff ℝ n (sourceRieszGaussianScale t : E→ℝ) := by
  have hnorm : ContDiff ℝ n (fun y : E=>‖y‖^2) := by
    simpa only [id_eq] using (contDiff_id : ContDiff ℝ n (id : E→E)).norm_sq ℝ
  exact (hnorm.neg.div_const (2*t^2)).exp

lemma sourceRieszGaussian_iteratedFDeriv_scale_bound (n : ℕ) (t : ℝ) (ht : 0<t) (z : E) :
    ‖iteratedFDeriv ℝ n (sourceRieszGaussianScale t) z‖ ≤
      (t⁻¹)^n*‖iteratedFDeriv ℝ n (sourceRieszGaussianScale 1) (t⁻¹ • z)‖ := by
  let g : E→L[ℝ] E := t⁻¹ • ContinuousLinearMap.id ℝ E
  have hg : ∀ y : E,g y=t⁻¹ • y := by intro y;rfl
  have he : sourceRieszGaussianScale t=(sourceRieszGaussianScale 1 ∘ g : E→ℝ) := by
    ext y
    simp only [Function.comp_apply,hg,sourceRieszGaussianScale,norm_smul,
      Real.norm_eq_abs,abs_of_pos (inv_pos.mpr ht)]
    congr 1
    field_simp
  have hgn : ‖g‖≤t⁻¹ := by
    dsimp [g]
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr ht)]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (ContinuousLinearMap.norm_id_le (𝕜:=ℝ) (E:=E)) (inv_nonneg.mpr ht.le)
  rw [he,g.iteratedFDeriv_comp_right (contDiff_sourceRieszGaussianScale n 1) z le_rfl]
  have h := (iteratedFDeriv ℝ n (sourceRieszGaussianScale 1) (g z)).norm_compContinuousLinearMap_le (fun _=>g)
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] at h
  calc
    _ ≤ ‖iteratedFDeriv ℝ n (sourceRieszGaussianScale 1) (g z)‖*‖g‖^n := h
    _ ≤ ‖iteratedFDeriv ℝ n (sourceRieszGaussianScale 1) (g z)‖*(t⁻¹)^n := by gcongr
    _ = _ := by rw [hg];ring

lemma sourceRieszGaussian_iteratedFDeriv_weighted_bound (n : ℕ) (t : ℝ) (ht : 0<t) (z : E) :
    ‖z‖^n*‖iteratedFDeriv ℝ n (sourceRieszGaussianScale t) z‖ ≤
      sourceRieszGaussianDerivativeConstant n*Real.exp (-‖z‖^2/(8*t^2)) := by
  have hscaled := sourceRieszGaussian_iteratedFDeriv_scale_bound n t ht z
  have hu : ‖t⁻¹ • z‖=t⁻¹*‖z‖ := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr ht)]
  have h := sourceRieszGaussian_iteratedFDeriv_widened_bound n (t⁻¹ • z)
  have hex : -‖t⁻¹ • z‖^2/8 = -‖z‖^2/(8*t^2) := by rw [hu];field_simp
  rw [hex] at h
  calc
    _ ≤ ‖z‖^n*((t⁻¹)^n*‖iteratedFDeriv ℝ n (sourceRieszGaussianScale 1) (t⁻¹ • z)‖) := mul_le_mul_of_nonneg_left hscaled (by positivity)
    _ = ‖t⁻¹ • z‖^n*‖iteratedFDeriv ℝ n (sourceRieszGaussianScale 1) (t⁻¹ • z)‖ := by rw [hu,mul_pow];ring
    _ ≤ (max 1 ‖t⁻¹ • z‖)^n*‖iteratedFDeriv ℝ n (sourceRieszGaussianScale 1) (t⁻¹ • z)‖ := by gcongr;exact le_max_right _ _
    _ ≤ _ := h

lemma sourceRieszGaussian_iteratedFDeriv_unweighted_bound (n : ℕ) (t : ℝ) (ht : 0<t) (z : E) :
    ‖iteratedFDeriv ℝ n (sourceRieszGaussianScale t) z‖ ≤
      (t⁻¹)^n*sourceRieszGaussianDerivativeConstant n*Real.exp (-‖z‖^2/(8*t^2)) := by
  have h := sourceRieszGaussian_iteratedFDeriv_widened_bound n (t⁻¹ • z)
  have hu : ‖t⁻¹ • z‖=t⁻¹*‖z‖ := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr ht)]
  have hex : -‖t⁻¹ • z‖^2/8 = -‖z‖^2/(8*t^2) := by rw [hu];field_simp
  rw [hex] at h
  have hnorm : ‖iteratedFDeriv ℝ n (sourceRieszGaussianScale 1) (t⁻¹ • z)‖≤sourceRieszGaussianDerivativeConstant n*Real.exp (-‖z‖^2/(8*t^2)) := by
    calc
      _ = 1*‖iteratedFDeriv ℝ n (sourceRieszGaussianScale 1) (t⁻¹ • z)‖ := by ring
      _ ≤ (max 1 ‖t⁻¹ • z‖)^n*‖iteratedFDeriv ℝ n (sourceRieszGaussianScale 1) (t⁻¹ • z)‖ := mul_le_mul_of_nonneg_right (one_le_pow₀ (le_max_left _ _)) (norm_nonneg _)
      _ ≤ _ := h
  exact (sourceRieszGaussian_iteratedFDeriv_scale_bound n t ht z).trans
    (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hnorm (by positivity : 0≤(t⁻¹)^n))

lemma sourceRieszGaussian_all_order_transport_bound (n : ℕ) (t : ℝ) (ht : 0<t)
    {K : ℝ≥0} {v : E→E} (hv : LipschitzWith K v) (x y : E) :
    |iteratedFDeriv ℝ n (sourceRieszGaussianScale t) (x-y) (fun _=>v x-v y)| ≤
      sourceRieszGaussianDerivativeConstant n*(K:ℝ)^n*Real.exp (-‖x-y‖^2/(8*t^2)) := by
  have hxy : ‖v x-v y‖≤(K:ℝ)*‖x-y‖ := by simpa only [dist_eq_norm] using hv.dist_le_mul x y
  have h := (iteratedFDeriv ℝ n (sourceRieszGaussianScale t) (x-y)).le_opNorm (fun _=>v x-v y)
  simp only [Real.norm_eq_abs,Finset.prod_const,Finset.card_univ,Fintype.card_fin] at h
  calc
    _ ≤ ‖iteratedFDeriv ℝ n (sourceRieszGaussianScale t) (x-y)‖*‖v x-v y‖^n := h
    _ ≤ ‖iteratedFDeriv ℝ n (sourceRieszGaussianScale t) (x-y)‖*((K:ℝ)*‖x-y‖)^n := by gcongr
    _ = (K:ℝ)^n*(‖x-y‖^n*‖iteratedFDeriv ℝ n (sourceRieszGaussianScale t) (x-y)‖) := by rw [mul_pow];ring
    _ ≤ (K:ℝ)^n*(sourceRieszGaussianDerivativeConstant n*Real.exp (-‖x-y‖^2/(8*t^2))) := mul_le_mul_of_nonneg_left (sourceRieszGaussian_iteratedFDeriv_weighted_bound n t ht (x-y)) (by positivity)
    _ = _ := by ring

end DGRHS.Commutator
#check @DGRHS.Commutator.contDiff_sourceRieszGaussianScale
#print axioms DGRHS.Commutator.contDiff_sourceRieszGaussianScale
#check @DGRHS.Commutator.sourceRieszGaussian_iteratedFDeriv_scale_bound
#print axioms DGRHS.Commutator.sourceRieszGaussian_iteratedFDeriv_scale_bound
#check @DGRHS.Commutator.sourceRieszGaussian_iteratedFDeriv_weighted_bound
#print axioms DGRHS.Commutator.sourceRieszGaussian_iteratedFDeriv_weighted_bound
#check @DGRHS.Commutator.sourceRieszGaussian_iteratedFDeriv_unweighted_bound
#print axioms DGRHS.Commutator.sourceRieszGaussian_iteratedFDeriv_unweighted_bound
#check @DGRHS.Commutator.sourceRieszGaussian_all_order_transport_bound
#print axioms DGRHS.Commutator.sourceRieszGaussian_all_order_transport_bound
