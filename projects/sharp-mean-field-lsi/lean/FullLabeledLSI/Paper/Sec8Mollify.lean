import FullLabeledLSI.Paper.Sec8Approx

/-!
# Section 8.5: smooth approximation of `H^1(P)` functions on a general torus

For a measure `P` on `UnitAddTorus ι` comparable to Lebesgue measure (`P ≤ c₁ vol`, `vol ≤ c₂ P`)
every `h ∈ H^1(P)` is the limit, in `L²(P)`, in Dirichlet energy and `P`-a.e., of smooth functions
(mollification).  General-index version of `Sec8.exists_smooth_seq`.
-/

open MeasureTheory Filter Topology SharpLSI
open scoped ENNReal ContDiff

namespace SharpLSI.FL
namespace Sec8

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem dirichlet_eq_sum_gen {P : Measure (UnitAddTorus ι)} (hP : P ≪ volume) {f : UnitAddTorus ι → ℝ}
    {g : UnitAddTorus ι → ι → ℝ} (hw : IsWeakGrad f g) :
    dirichlet P f = ∑ k, ∫⁻ x, ‖g x k‖ₑ ^ 2 ∂P := by
  unfold dirichlet
  have hae : weakGrad f =ᵐ[P] g := hP.ae_eq (weakGrad_ae_eq hw)
  rw [← lintegral_finsetSum']
  · refine lintegral_congr_ae ?_
    filter_upwards [hae] with x hx
    rw [hx]
    unfold sqNorm
    rw [ENNReal.ofReal_sum_of_nonneg fun k _ => sq_nonneg _]
    exact Finset.sum_congr rfl fun k _ => ofReal_sq_eq_enorm_sq _
  · exact fun k _ => (((hw.aestronglyMeasurable_grad k).aemeasurable.mono_ac hP).enorm.pow_const 2)

theorem exists_smooth_seq_gen {P : Measure (UnitAddTorus ι)} {c₁ c₂ : ℝ≥0∞} (hc₁ : c₁ ≠ ⊤)
    (hc₂ : c₂ ≠ ⊤) (hPle : P ≤ c₁ • volume) (hvle : volume ≤ c₂ • P)
    {h : UnitAddTorus ι → ℝ} (hh : MemH1 P h) :
    ∃ f : ℕ → UnitAddTorus ι → ℝ, (∀ n, IsSmoothT (f n)) ∧
      Tendsto (fun n => ∫⁻ x, ‖f n x - h x‖ₑ ^ 2 ∂P) atTop (𝓝 0) ∧
      Tendsto (fun n => dirichlet P (f n)) atTop (𝓝 (dirichlet P h)) ∧
      ∀ᵐ x ∂P, Tendsto (fun n => f n x) atTop (𝓝 (h x)) := by
  have hPac : P ≪ volume := Measure.absolutelyContinuous_of_le_smul hPle
  have hw := isWeakGrad_weakGrad hh.1
  set g := weakGrad h with hg
  have h2 : MemLp h 2 volume := hh.2.1.of_measure_le_smul hc₂ hvle
  have hgkP : ∀ k, MemLp (fun y => g y k) 2 P := fun k =>
    hh.2.2.of_le ((hw.aestronglyMeasurable_grad k).mono_ac hPac)
      (Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
        exact abs_le_sqrt_sqNorm _ k)
  have hgk : ∀ k, MemLp (fun y => g y k) 2 volume := fun k =>
    (hgkP k).of_measure_le_smul hc₂ hvle
  have hint : Integrable h volume := h2.integrable one_le_two
  have hgint : ∀ k, Integrable (fun y => g y k) volume := fun k => (hgk k).integrable one_le_two
  obtain ⟨ns, hns, hae⟩ := exists_subseq_moll_ae hint hgint
  have hae1 : ∀ᵐ y ∂(volume : Measure (UnitAddTorus ι)),
      Tendsto (fun j => moll (ns j) h y) atTop (𝓝 (h y)) := hae.mono fun y hy => hy.1
  have hae2 : ∀ k, ∀ᵐ y ∂(volume : Measure (UnitAddTorus ι)),
      Tendsto (fun j => moll (ns j) (fun z => g z k) y) atTop (𝓝 (g y k)) :=
    fun k => hae.mono fun y hy => hy.2 k
  have L0 := L2Tendsto_moll hint (lintegral_enorm_sq_ne_top h2) hae1
  have Lk := fun k => L2Tendsto_moll (hgint k) (lintegral_enorm_sq_ne_top (hgk k)) (hae2 k)
  refine ⟨fun j => moll (ns j) h, fun j => moll_comp_liftT_contDiff (ns j) hint,
    L2Tendsto.of_le_smul hc₁ hPle L0, ?_, hPac.ae_le hae1⟩
  have hdir : ∀ j, dirichlet P (moll (ns j) h) =
      ∑ k, ∫⁻ x, ‖moll (ns j) (fun z => g z k) x‖ₑ ^ 2 ∂P := fun j =>
    dirichlet_eq_sum_gen hPac (isWeakGrad_moll hw hint (ns j))
  show Tendsto (fun j => dirichlet P (moll (ns j) h)) atTop _
  simp_rw [hdir]
  rw [dirichlet_eq_sum_gen hPac hw]
  refine tendsto_finsetSum _ fun k _ => ?_
  exact (L2Tendsto.of_le_smul hc₁ hPle (Lk k)).tendsto_lintegral_sq
    (fun j => ((measurable_moll _ (hgint k)).aemeasurable.mono_ac hPac))
    ((hw.aestronglyMeasurable_grad k).aemeasurable.mono_ac hPac)
    (hPac.ae_le (hae2 k)) (lintegral_enorm_sq_ne_top (hgkP k))

end Sec8
end SharpLSI.FL
