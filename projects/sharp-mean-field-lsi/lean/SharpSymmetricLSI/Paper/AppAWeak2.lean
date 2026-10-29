import SharpSymmetricLSI.Paper.AppAWeak1

/-!
# The weak formulation (2): physical form and the transport bound

For `u` with `ρ_u ∈ H¹` (weak gradient `g`), the Fourier integrand of the weak formulation equals
`-∑ⱼ ∫ ∂ⱼφ (gⱼ + N_{u,j})` (`fourier_integrand_eq`). For `|∇φ| ≤ 1`:
`|∫φρ_t - ∫φρ_s| ≤ ∫_{(s,t]} ∫ |∇ρ_u + N_u| du` (`LinMild.abs_weak_le`).
-/

open MeasureTheory Set Filter Topology Complex UnitAddTorus
open scoped Real ENNReal ComplexConjugate

namespace SharpLSI

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem abs_sum_mul_le_sqrt (a b : ι → ℝ) :
    |∑ j, a j * b j| ≤ Real.sqrt (∑ j, a j ^ 2) * Real.sqrt (∑ j, b j ^ 2) := by
  rw [abs_le]
  constructor
  · have := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun j => -a j) b
    simp only [neg_sq, neg_mul, Finset.sum_neg_distrib] at this
    linarith
  · exact Real.sum_mul_le_sqrt_mul_sqrt Finset.univ a b

namespace LinMild

variable {ρ₀ : UnitAddTorus ι → ℝ} {ρ : ℝ → UnitAddTorus ι → ℝ}
  {N : ℝ → UnitAddTorus ι → ι → ℝ} {A : ℝ} (h : LinMild ρ₀ ρ N A)
include h

/-- The Fourier integrand in physical form. -/
theorem fourier_integrand_eq {T K : ℝ} (hK : ∀ t ∈ Icc 0 T, ∀ x, |ρ t x| ≤ K)
    {φ : UnitAddTorus ι → ℝ} (hφ : IsSmoothT φ) {u : ℝ} (hu : u ∈ Icc 0 T)
    {g : UnitAddTorus ι → ι → ℝ} (hg : IsWeakGrad (ρ u) g) (hg2 : ∀ j, MemLp (fun y => g y j) 2 volume) :
    ∑' n, conj (cf φ n) * (-(lamN n : ℂ) * cf (ρ u) n + modeB N T n u) =
      ((-∑ j, ∫ x, dpart_appA φ j x * (g x j + N u x j) : ℝ) : ℂ) := by
  have hsj := fun j => isSmoothT_dpart hφ j
  have hdj2 : ∀ j, MemLp (dpart_appA φ j) 2 volume := fun j =>
    memLp_of_continuous (continuous_of_isSmoothT (hsj j)) 2
  have hN2 : ∀ j, MemLp (fun x => N u x j) 2 volume := fun j =>
    memLp_of_abs_le (h.measurable_sectionN u j) (fun z => h.abs_N_le hK hu z j) 2
  have hgc : ∀ j n, cf (fun y => g y j) n = 2 * π * I * n j * cf (ρ u) n := fun j n =>
    mFourierCoeff_grad hg ((h.memLp_two_section hK hu).integrable one_le_two)
      (fun j => (hg2 j).integrable one_le_two) n j
  -- the two parts
  have hA : ∀ j, HasSum (fun n => conj (cf φ n) * ((4 * π ^ 2 * ((n j : ℝ)) ^ 2 : ℝ) : ℂ) * cf (ρ u) n)
      ((∫ x, dpart_appA φ j x * g x j : ℝ) : ℂ) := fun j => by
    have := hasSum_prod_cf_real (hdj2 j) (hg2 j)
    refine this.congr_fun fun n => ?_
    rw [cf_dpart_appA hφ, hgc, map_mul, map_mul, map_mul, map_mul, Complex.conj_I, Complex.conj_ofReal,
      map_ofNat, map_intCast]
    push_cast; ring_nf; rw [I_sq]; ring
  have hB : ∀ j, HasSum (fun n => conj (cf φ n) * (2 * π * I * n j) * cf (fun x => N u x j) n)
      (-((∫ x, dpart_appA φ j x * N u x j : ℝ) : ℂ)) := fun j => by
    have := (hasSum_prod_cf_real (hdj2 j) (hN2 j)).neg
    refine this.congr_fun fun n => ?_
    rw [cf_dpart_appA hφ, map_mul, map_mul, map_mul, map_mul, Complex.conj_I, Complex.conj_ofReal,
      map_ofNat, map_intCast]
    ring
  have hsum := (hasSum_sum fun j (_ : j ∈ Finset.univ) => (hA j).neg).add
    (hasSum_sum fun j (_ : j ∈ Finset.univ) => hB j)
  have hF : HasSum (fun n => conj (cf φ n) * (-(lamN n : ℂ) * cf (ρ u) n + modeB N T n u))
      ((∑ j, -((∫ x, dpart_appA φ j x * g x j : ℝ) : ℂ)) + ∑ j, -((∫ x, dpart_appA φ j x * N u x j : ℝ) : ℂ)) := by
    convert hsum using 1
    funext n
    simp only [modeB, if_pos hu, lamN]
    push_cast
    simp only [mul_add, neg_mul, Finset.sum_mul, mul_neg, Finset.mul_sum, ← Finset.sum_neg_distrib]
    congr 1
    · refine Finset.sum_congr rfl fun j _ => ?_; ring
    · refine Finset.sum_congr rfl fun j _ => ?_; ring
  rw [hF.tsum_eq]
  push_cast
  rw [← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have e : ∫ x, dpart_appA φ j x * (g x j + N u x j) =
      (∫ x, dpart_appA φ j x * g x j) + ∫ x, dpart_appA φ j x * N u x j := by
    rw [← integral_add (f := fun x => dpart_appA φ j x * g x j) (g := fun x => dpart_appA φ j x * N u x j)
      ((hdj2 j).integrable_mul (hg2 j)) ((hdj2 j).integrable_mul (hN2 j))]
    congr 1; funext x; ring
  rw [e]; push_cast; ring

/-- **The transport bound.** For smooth `φ` with `|∇φ| ≤ 1`,
`|∫φρ_t - ∫φρ_s| ≤ ∫_{(s,t]} F`, where `F u` bounds `∫ |∇ρ_u + N_u|` for every weak gradient. -/
theorem abs_weak_le {T K : ℝ} (hK0 : 0 ≤ K) (hK : ∀ t ∈ Icc 0 T, ∀ x, |ρ t x| ≤ K)
    {φ : UnitAddTorus ι → ℝ} (hφ : IsSmoothT φ) (hgr : ∀ y, ∑ j, dpart_appA φ j y ^ 2 ≤ 1)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (htT : t ≤ T) {F : ℝ → ℝ≥0∞}
    (hF : ∀ᵐ u ∂(volume.restrict (Ioc s t)), ∀ g : UnitAddTorus ι → ι → ℝ, IsWeakGrad (ρ u) g →
      (∀ j, MemLp (fun y => g y j) 2 volume) →
      ∫⁻ x, ENNReal.ofReal (Real.sqrt (∑ j, (g x j + N u x j) ^ 2)) ≤ F u) :
    ENNReal.ofReal |(∫ x, φ x * ρ t x) - ∫ x, φ x * ρ s x| ≤ ∫⁻ u in Ioc s t, F u := by
  have hT : 0 ≤ T := hs.trans (hst.trans htT)
  have hw := h.weak_form_fourier hK0 hK hφ hs hst htT
  have hae := ae_restrict_of_ae_restrict_of_subset (Ioc_subset_Ioc hs htT) (h.ae_isWeakGrad hK0 hK hT)
  have e : ∀ r : ℝ, ENNReal.ofReal |r| = ‖(r : ℂ)‖ₑ := fun r => by
    rw [← ofReal_norm_eq_enorm, Complex.norm_real, Real.norm_eq_abs]
  rw [e, hw]
  refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono_ae ?_)
  filter_upwards [hF, hae, ae_restrict_mem measurableSet_Ioc] with u hFu hgu hu
  obtain ⟨g, hg, hg2, -, -⟩ := hgu
  have huT : u ∈ Icc 0 T := ⟨hs.trans hu.1.le, hu.2.trans htT⟩
  rw [h.fourier_integrand_eq hK hφ huT hg hg2]
  refine le_trans ?_ (hFu g hg hg2)
  have hdj2 : ∀ j, MemLp (dpart_appA φ j) 2 volume := fun j =>
    memLp_of_continuous (continuous_of_isSmoothT (isSmoothT_dpart hφ j)) 2
  have hN2 : ∀ j, MemLp (fun x => N u x j) 2 volume := fun j =>
    memLp_of_abs_le (h.measurable_sectionN u j) (fun z => h.abs_N_le hK huT z j) 2
  have hint : ∀ j ∈ (Finset.univ : Finset ι),
      Integrable (fun x => dpart_appA φ j x * (g x j + N u x j)) := fun j _ =>
    (hdj2 j).integrable_mul ((hg2 j).add (hN2 j))
  rw [← integral_finsetSum _ hint]
  calc ‖((-∫ x, ∑ j, dpart_appA φ j x * (g x j + N u x j) : ℝ) : ℂ)‖ₑ
      = ‖∫ x, ∑ j, dpart_appA φ j x * (g x j + N u x j)‖ₑ := by
        rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, Complex.norm_real, norm_neg]
    _ ≤ ∫⁻ x, ‖∑ j, dpart_appA φ j x * (g x j + N u x j)‖ₑ := enorm_integral_le_lintegral_enorm _
    _ ≤ _ := lintegral_mono fun x => by
        rw [← ofReal_norm_eq_enorm, Real.norm_eq_abs]
        refine ENNReal.ofReal_le_ofReal ((abs_sum_mul_le_sqrt _ _).trans ?_)
        have h1 : Real.sqrt (∑ j, dpart_appA φ j x ^ 2) ≤ 1 :=
          (Real.sqrt_le_sqrt (hgr x)).trans_eq Real.sqrt_one
        exact mul_le_of_le_one_left (Real.sqrt_nonneg _) h1

end LinMild

end SharpLSI
