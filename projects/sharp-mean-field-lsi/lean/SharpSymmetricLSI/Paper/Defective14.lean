import SharpSymmetricLSI.Paper.Defective11
import SharpSymmetricLSI.Paper.Defective13
import SharpSymmetricLSI.Paper.GroundT4

/-!
# R03 (Proposition 2.2), part 14: the regularized law `ν = f² P_N / ‖f‖²` as a density

For `f ∈ H¹(P_N)` and `n`, with `u = ψ_n(f)² = psiSqR n ∘ f` and the Gibbs density `ℓ = e^{-H_N}/Z_N`:
`sqMeasure P_N (regF n f) = Q · Leb` with `Q = u ℓ / ∫ u dP_N` (`sqMeasure_regF_eq`), `Q` is bounded
above and below (`Qreg_bounds`), and `∇Q = (u' (f) ∇f ℓ + u ∇ℓ) / ∫ u dP_N` (`isWeakGrad_Qreg`).
-/

open MeasureTheory Filter Topology InformationTheory
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-- The real Gibbs density `e^{-H_N}/Z_N`. -/
noncomputable def gibbsDensR (V : Torus d → ℝ) (W : Torus d → Torus d → ℝ) (N : ℕ) (X : Config N d) :
    ℝ :=
  Real.exp (-hamiltonian V W N X) / partitionFn V W N

/-- `u = ψ_n(f)²`. -/
noncomputable def uReg {N : ℕ} (n : ℕ) (f : Config N d → ℝ) (X : Config N d) : ℝ := psiSqR n (f X)

/-- `∫ u dP_N`. -/
noncomputable def Zreg (V : Torus d → ℝ) (W : Torus d → Torus d → ℝ) {N : ℕ} (n : ℕ)
    (f : Config N d → ℝ) : ℝ :=
  ∫ X, uReg n f X ∂gibbs V W N

/-- The Lebesgue density of `ν = u P_N / ∫ u dP_N`. -/
noncomputable def Qreg (V : Torus d → ℝ) (W : Torus d → Torus d → ℝ) {N : ℕ} (n : ℕ)
    (f : Config N d → ℝ) (X : Config N d) : ℝ :=
  uReg n f X * gibbsDensR V W N X / Zreg V W n f

theorem psiSqR_bounds (n : ℕ) (t : ℝ) :
    1 / ((n : ℝ) + 1) ^ 2 ≤ psiSqR n t ∧ psiSqR n t ≤ ((n : ℝ) + 2) ^ 2 := by
  rw [psiSqR_eq]
  have h1 := psiReg_ge n t
  have h2 := psiReg_le n t
  have h0 : 0 ≤ 1 / ((n : ℝ) + 1) := by positivity
  constructor
  · rw [show 1 / ((n : ℝ) + 1) ^ 2 = (1 / ((n : ℝ) + 1)) ^ 2 by rw [div_pow, one_pow]]
    exact pow_le_pow_left₀ h0 h1 2
  · exact pow_le_pow_left₀ (h0.trans h1) h2 2

section setup
variable (hyp : Hyp V W KV KW) {N : ℕ}
include hyp

theorem gibbs_eq_gibbsDensR :
    gibbs V W N = (volume : Measure (Config N d)).withDensity
      (fun X => ENNReal.ofReal (gibbsDensR V W N X)) := rfl

theorem measurable_gibbsDensR : Measurable (gibbsDensR V W N) :=
  (Real.measurable_exp.comp (continuous_hamiltonian hyp N).measurable.neg).div_const _

theorem gibbsDensR_bounds : ∃ c C : ℝ, 0 < c ∧ ∀ X, c ≤ gibbsDensR V W N X ∧ gibbsDensR V W N X ≤ C := by
  obtain ⟨B, hB⟩ := exists_bound_of_continuous (continuous_hamiltonian hyp N)
  have hZ : 0 < partitionFn V W N :=
    partition_pos_of_continuous (volume : Measure (Config N d)) (continuous_hamiltonian hyp N)
  refine ⟨Real.exp (-B) / partitionFn V W N, Real.exp B / partitionFn V W N, by positivity,
    fun X => ⟨?_, ?_⟩⟩
  · unfold gibbsDensR
    exact div_le_div_of_nonneg_right (Real.exp_le_exp.mpr (by linarith [(abs_le.mp (hB X)).2]))
      hZ.le
  · unfold gibbsDensR
    exact div_le_div_of_nonneg_right (Real.exp_le_exp.mpr (by linarith [(abs_le.mp (hB X)).1]))
      hZ.le

variable {f : Config N d → ℝ} (hf : MemH1C (gibbs V W N) f)
include hf

theorem measurable_uReg_ae (n : ℕ) : AEMeasurable (uReg n f) (gibbs V W N) :=
  (contDiff_psiSqR n).continuous.measurable.comp_aemeasurable
    (memLp_of_memH1C hyp hf).aestronglyMeasurable.aemeasurable

theorem Zreg_bounds (n : ℕ) :
    1 / ((n : ℝ) + 1) ^ 2 ≤ Zreg V W n f ∧ Zreg V W n f ≤ ((n : ℝ) + 2) ^ 2 := by
  haveI := gibbs_isProbabilityMeasure hyp N
  exact integral_mem_Icc (measurable_uReg_ae hyp hf n).aestronglyMeasurable
    (fun X => (psiSqR_bounds n (f X)).1) (fun X => (psiSqR_bounds n (f X)).2)

theorem Zreg_eq (n : ℕ) : Zreg V W n f = ∫ X, regF n f X ^ 2 ∂gibbs V W N := by
  unfold Zreg uReg regF; simp_rw [psiSqR_eq]

variable (hfm : Measurable f)
include hfm

theorem measurable_Qreg (n : ℕ) : Measurable (Qreg V W n f) :=
  (((contDiff_psiSqR n).continuous.measurable.comp hfm).mul (measurable_gibbsDensR hyp)).div_const _

theorem Qreg_bounds (n : ℕ) : ∃ c C : ℝ, 0 < c ∧ ∀ X, c ≤ Qreg V W n f X ∧ Qreg V W n f X ≤ C := by
  obtain ⟨c1, C1, hc1, h1⟩ := gibbsDensR_bounds hyp (N := N)
  obtain ⟨hZ1, hZ2⟩ := Zreg_bounds hyp hf n
  have hZ0 : 0 < Zreg V W n f := lt_of_lt_of_le (by positivity) hZ1
  refine ⟨1 / ((n : ℝ) + 1) ^ 2 * c1 / ((n : ℝ) + 2) ^ 2, ((n : ℝ) + 2) ^ 2 * C1 / (1 / ((n : ℝ) + 1) ^ 2),
    by positivity, fun X => ⟨?_, ?_⟩⟩
  · unfold Qreg uReg
    exact div_le_div₀ (mul_nonneg (psiSqR_pos n _).le (hc1.le.trans (h1 X).1))
      (mul_le_mul (psiSqR_bounds n (f X)).1 (h1 X).1 hc1.le
      (le_trans (by positivity) (psiSqR_bounds n (f X)).1)) hZ0 hZ2
  · unfold Qreg uReg
    exact div_le_div₀ (by nlinarith [(h1 X).1, (h1 X).2]) (mul_le_mul (psiSqR_bounds n (f X)).2 (h1 X).2
      (hc1.le.trans (h1 X).1) (by positivity)) (by positivity) hZ1

theorem sqMeasure_regF_eq (n : ℕ) :
    sqMeasure (gibbs V W N) (regF n f) =
      (volume : Measure (Config N d)).withDensity fun X => ENNReal.ofReal (Qreg V W n f X) := by
  obtain ⟨c1, C1, hc1, h1⟩ := gibbsDensR_bounds hyp (N := N)
  have hZ0 : 0 < Zreg V W n f := lt_of_lt_of_le (by positivity) (Zreg_bounds hyp hf n).1
  unfold sqMeasure
  rw [gibbs_eq_gibbsDensR hyp]
  have hm : Measurable fun X => ENNReal.ofReal (regF n f X ^ 2 / ∫ Y, regF n f Y ^ 2
      ∂(volume : Measure (Config N d)).withDensity fun X => ENNReal.ofReal (gibbsDensR V W N X)) :=
    ((((contDiff_psiReg n).continuous.measurable.comp hfm).pow_const 2).div_const _).ennreal_ofReal
  rw [← withDensity_mul _ ((measurable_gibbsDensR hyp).ennreal_ofReal) hm]
  congr 1
  funext X
  simp only [Pi.mul_apply]
  rw [← ENNReal.ofReal_mul (hc1.le.trans (h1 X).1), ← gibbs_eq_gibbsDensR hyp, ← Zreg_eq hyp hf n]
  congr 1
  unfold Qreg uReg regF
  rw [psiSqR_eq]; ring

end setup

section grad
variable (hyp : Hyp V W KV KW) {μ : Measure (Torus d)} [IsProbabilityMeasure μ] (hac : μ ≪ haar d)
  {N : ℕ} (hN : 1 ≤ N) {f : Config N d → ℝ} (hf : MemH1C (gibbs V W N) f)
include hyp hac hN hf

/-- The weak gradient of `Q ∘ unflat`. -/
noncomputable def GQreg (V : Torus d → ℝ) (W : Torus d → Torus d → ℝ) (μ : Measure (Torus d))
    (n : ℕ) (f : Config N d → ℝ) (g : UnitAddTorus (Fin N × Fin d) → Fin N × Fin d → ℝ)
    (y : UnitAddTorus (Fin N × Fin d)) (p : Fin N × Fin d) : ℝ :=
  (deriv (psiSqR n) (f (unflat y)) * g y p * gibbsDensR V W N (unflat y) +
    uReg n f (unflat y) * (-(gibbsDensR V W N (unflat y) *
      (gsG W μ N y p + lipGrad (PhiMF V W μ) (projBlock p.1 y) p.2)))) / Zreg V W n f

theorem isWeakGrad_Qreg {g : UnitAddTorus (Fin N × Fin d) → Fin N × Fin d → ℝ}
    (hw : IsWeakGrad (f ∘ unflat) g) (hgi : ∀ k, Integrable (fun y => g y k) volume) (n : ℕ) :
    IsWeakGrad (Qreg V W n f ∘ unflat) (GQreg V W μ n f g) := by
  obtain ⟨-, hi, -⟩ := memH1C_data hyp hf
  have hu := isWeakGrad_comp hw hi hgi (contDiff_psiSqR n) (abs_deriv_psiSqR_le n)
  have hui : Integrable (fun y => psiSqR n ((f ∘ unflat) y)) volume :=
    Integrable.of_bound ((contDiff_psiSqR n).continuous.measurable.comp_aemeasurable
      hi.aestronglyMeasurable.aemeasurable).aestronglyMeasurable (((n : ℝ) + 2) ^ 2)
      (Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (le_trans (by positivity) (psiSqR_bounds n _).1)]
        exact (psiSqR_bounds n _).2)
  have hugi : ∀ k, Integrable (fun y => deriv (psiSqR n) ((f ∘ unflat) y) * g y k)
      volume := fun k =>
    (hgi k).bdd_mul ((contDiff_psiSqR n).continuous_deriv le_rfl |>.measurable.comp_aemeasurable
      hi.aestronglyMeasurable.aemeasurable).aestronglyMeasurable
      (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact abs_deriv_psiSqR_le n _)
  have hℓ := (isWeakGrad_expNegH hyp hac hN (μ := μ)).cmul (1 / partitionFn V W N)
  obtain ⟨C, hC0, hC⟩ := exists_bound_gradH hyp hac hN (μ := μ)
  obtain ⟨B, hB⟩ := exists_bound_hamiltonian hyp hac (N := N)
  have hZ : 0 < partitionFn V W N :=
    partition_pos_of_continuous (volume : Measure (Config N d)) (continuous_hamiltonian hyp N)
  have hprod := hu.mul_lip hui hugi hℓ
    (((Real.measurable_exp.comp ((continuous_hamiltonian hyp N).measurable.comp
      measurable_unflat).neg).const_mul _))
    (B := 1 / partitionFn V W N * Real.exp B)
    (fun y => by
      rw [abs_mul, abs_of_pos (by positivity), abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith [(abs_le.mp (hB (unflat y))).1]))
        (by positivity))
    (fun p => ((((Real.measurable_exp.comp ((continuous_hamiltonian hyp N).measurable.comp
      measurable_unflat).neg).mul (measurable_gradH hyp hac hN p)).neg).const_mul _))
    (L := 1 / partitionFn V W N * (Real.exp B * C))
    (fun y p => by
      rw [abs_mul, abs_of_pos (by positivity), abs_neg, abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_left (mul_le_mul (Real.exp_le_exp.mpr (by
        linarith [(abs_le.mp (hB (unflat y))).1])) (hC y p) (abs_nonneg _) (Real.exp_pos _).le)
        (by positivity))
  have hfin := hprod.cmul (1 / Zreg V W n f)
  convert hfin using 1
  · funext y
    simp only [Function.comp_apply, Qreg, uReg, gibbsDensR]
    ring
  · funext y p
    simp only [GQreg, uReg, gibbsDensR, Function.comp_apply]
    ring

end grad


end SharpLSI
