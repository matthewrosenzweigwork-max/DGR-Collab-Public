import FullLabeledLSI.Infra.HypercontrHybrid2

/-!
# Measure-theoretic glue for the hybrid moment bound

Almost-everywhere replacement of `e` by its `C¹` representatives `eC`, measurability of the hybrid
polynomial, and the iterated form of integrals against `hybMeasure = μ^{⊗N} ⊗ γ_J^{⊗N}`.
-/

open MeasureTheory SharpLSI
open scoped ENNReal

noncomputable section

namespace SharpLSI.FL.Hyb

open SharpLSI.FL.Gross

variable {d N J : ℕ} {mu : Measure (Torus d)} [IsProbabilityMeasure mu] {e eC : ℕ → Torus d → ℝ}

lemma measurable_hybFactor (hC1 : ∀ j, C1T (eC j)) (B : Finset (Fin N)) (i : Fin N)
    (m : Fin (J + 1)) :
    Measurable (hybFactor eC B i m : Config N d × (Fin N → Fin J → ℝ) → ℝ) := by
  unfold hybFactor
  by_cases hi : i ∈ B
  · simp only [hi, if_true]
    exact (hC1 m).measurable.comp ((measurable_pi_apply i).comp measurable_fst)
  · simp only [hi, if_false]
    by_cases hm : (m : ℕ) = 0
    · simp only [hm, dif_pos]; exact measurable_const
    · simp only [hm, dif_neg, not_false_eq_true]
      exact (measurable_pi_apply _).comp ((measurable_pi_apply i).comp measurable_snd)

lemma measurable_hybPoly (hC1 : ∀ j, C1T (eC j)) (c : (Fin N → Fin (J + 1)) → ℝ)
    (B : Finset (Fin N)) : Measurable (hybPoly eC c B : Config N d × (Fin N → Fin J → ℝ) → ℝ) := by
  unfold hybPoly
  exact Finset.measurable_sum _ fun j _ =>
    measurable_const.mul (Finset.measurable_prod _ fun i _ => measurable_hybFactor hC1 B i (j i))

/-- For every `y`, the `x`-slice of `hybPoly e` equals that of `hybPoly eC` for `μ^{⊗N}`-a.e. `x`. -/
lemma ae_hybPoly_slice (hae : ∀ j, eC j =ᵐ[mu] e j) (c : (Fin N → Fin (J + 1)) → ℝ)
    (B : Finset (Fin N)) (y : Fin N → Fin J → ℝ) :
    ∀ᵐ x ∂(Measure.pi fun _ : Fin N => mu), hybPoly e c B (x, y) = hybPoly eC c B (x, y) := by
  have h : ∀ᵐ x ∂(Measure.pi fun _ : Fin N => mu), ∀ i : Fin N, ∀ m : ℕ,
      eC m (x i) = e m (x i) :=
    (ae_all_iff).2 fun i => (ae_all_iff).2 fun m => ae_pi_coord (hae m) i
  filter_upwards [h] with x hx
  unfold hybPoly hybFactor
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases hi : i ∈ B
  · simp only [hi, if_true]; exact (hx i (j i)).symm
  · simp only [hi, if_false]

lemma ae_hybPoly (hae : ∀ j, eC j =ᵐ[mu] e j) (c : (Fin N → Fin (J + 1)) → ℝ)
    (B : Finset (Fin N)) :
    ∀ᵐ ω ∂(hybMeasure mu N J), hybPoly e c B ω = hybPoly eC c B ω := by
  have h : ∀ᵐ ω ∂(hybMeasure mu N J), ∀ i : Fin N, ∀ m : ℕ, eC m (ω.1 i) = e m (ω.1 i) := by
    have h1 : ∀ᵐ x ∂(Measure.pi fun _ : Fin N => mu), ∀ i : Fin N, ∀ m : ℕ, eC m (x i) = e m (x i) :=
      (ae_all_iff).2 fun i => (ae_all_iff).2 fun m => ae_pi_coord (hae m) i
    exact measurePreserving_fst.quasiMeasurePreserving.ae h1
  filter_upwards [h] with ω hω
  unfold hybPoly hybFactor
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases hi : i ∈ B
  · simp only [hi, if_true]; exact (hω i (j i)).symm
  · simp only [hi, if_false]

/-- The integral of a power of the hybrid polynomial as an iterated integral (`y` outside, `x` inside). -/
lemma lintegral_hyb_split (hC1 : ∀ j, C1T (eC j)) (hae : ∀ j, eC j =ᵐ[mu] e j)
    (c : (Fin N → Fin (J + 1)) → ℝ) (B : Finset (Fin N)) (n : ℕ) :
    ∫⁻ ω, ENNReal.ofReal ((hybPoly e c B ω) ^ n) ∂(hybMeasure mu N J) =
      ∫⁻ y, ∫⁻ x, ENNReal.ofReal ((hybPoly e c B (x, y)) ^ n) ∂(Measure.pi fun _ : Fin N => mu)
        ∂(Measure.pi fun _ : Fin N => Measure.pi fun _ : Fin J => ProbabilityTheory.gaussianReal 0 1) := by
  have hm : Measurable (fun ω : Config N d × (Fin N → Fin J → ℝ) =>
      ENNReal.ofReal ((hybPoly eC c B ω) ^ n)) :=
    ENNReal.measurable_ofReal.comp ((measurable_hybPoly hC1 c B).pow_const n)
  calc ∫⁻ ω, ENNReal.ofReal ((hybPoly e c B ω) ^ n) ∂(hybMeasure mu N J)
      = ∫⁻ ω, ENNReal.ofReal ((hybPoly eC c B ω) ^ n) ∂(hybMeasure mu N J) :=
        lintegral_congr_ae ((ae_hybPoly hae c B).mono fun ω hω => by beta_reduce; rw [hω])
    _ = ∫⁻ y, ∫⁻ x, ENNReal.ofReal ((hybPoly eC c B (x, y)) ^ n)
          ∂(Measure.pi fun _ : Fin N => mu)
          ∂(Measure.pi fun _ : Fin N => Measure.pi fun _ : Fin J => ProbabilityTheory.gaussianReal 0 1) :=
        lintegral_prod_symm _ hm.aemeasurable
    _ = _ := by
        refine lintegral_congr fun y => ?_
        exact lintegral_congr_ae ((ae_hybPoly_slice hae c B y).mono fun x hx => by beta_reduce; rw [hx])

end SharpLSI.FL.Hyb

end
