import SharpSymmetricLSI.Paper.Defective8
import SharpSymmetricLSI.Paper.GroundT3
import SharpSymmetricLSI.Paper.AdmFinite
import SharpSymmetricLSI.Paper.ProductFisherGrad

/-!
# R03 (Proposition 2.2), part 11: the weak gradient of the Gibbs density

`H_N = U_N + ∑ᵢ Φ(Xᵢ) - const` with `Φ = V + W * μ` (`hamiltonian_eq_U`). With `∇U_N = gsG` (GroundT3)
and `∇Φ = lipGrad Φ` (Lipschitz), the Gibbs density `ℓ = e^{-H_N}/Z_N` has the bounded weak gradient
`-ℓ (gsG + lipGrad Φ(Xᵢ))` (`isWeakGrad_gibbsDens`).
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-- The mean-field potential `Φ = V + W * μ`. -/
noncomputable def PhiMF (V : Torus d → ℝ) (W : Torus d → Torus d → ℝ) (μ : Measure (Torus d))
    (x : Torus d) : ℝ :=
  V x + convMeas W μ x

section phi
variable (hyp : Hyp V W KV KW) {μ : Measure (Torus d)} [IsProbabilityMeasure μ] (hac : μ ≪ haar d)
include hyp

theorem continuous_convMeas' : Continuous (convMeas W μ) := by
  have h := continuous_parametric_integral_of_continuous (μ := μ) (f := W)
    (s := Set.univ) hyp.continuous_W isCompact_univ
  simp only [Measure.restrict_univ] at h
  exact h

theorem continuous_PhiMF : Continuous (PhiMF V W μ) :=
  hyp.continuous_V.add (continuous_convMeas' hyp)

include hac in
theorem lipschitz_PhiMF : ∃ L : ℝ≥0, LipschitzWith L (PhiMF V W μ ∘ liftT) := by
  obtain ⟨L, hL⟩ := lipschitz_convDens hyp (integrable_densOf μ)
  have e : PhiMF V W μ ∘ liftT = (V ∘ liftT) + (convDens W (densOf μ) ∘ liftT) := by
    funext x; simp [PhiMF, convMeas_eq_convDens hac]
  rw [e]
  exact ⟨_, (lipschitz_V hyp).add hL⟩

include hac in
theorem isWeakGrad_PhiMF : IsWeakGrad (PhiMF V W μ) (lipGrad (PhiMF V W μ)) := by
  obtain ⟨L, hL⟩ := lipschitz_PhiMF hyp hac
  exact isWeakGrad_lipGrad (continuous_PhiMF hyp) hL

end phi

section sumPhi
variable (hyp : Hyp V W KV KW) {μ : Measure (Torus d)} [IsProbabilityMeasure μ] (hac : μ ≪ haar d)
  {N : ℕ}
include hyp hac

theorem integrable_PhiMF : Integrable (PhiMF V W μ) (haar d) :=
  (continuous_PhiMF hyp).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem integrable_lipGrad_PhiMF (k : Fin d) :
    Integrable (fun x => lipGrad (PhiMF V W μ) x k) (haar d) := by
  obtain ⟨L, hL⟩ := lipschitz_PhiMF hyp hac
  exact Integrable.of_bound (measurable_lipGrad (continuous_PhiMF hyp) k).aestronglyMeasurable L
    (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact abs_lipGrad_le hL x k)

/-- `∇ ∑ᵢ Φ(Xᵢ)`, block by block. -/
theorem isWeakGrad_sumPhi_finset (s : Finset (Fin N)) :
    IsWeakGrad (fun y : UnitAddTorus (Fin N × Fin d) => ∑ i ∈ s, PhiMF V W μ (projBlock i y))
      (fun y p => if p.1 ∈ s then lipGrad (PhiMF V W μ) (projBlock p.1 y) p.2 else 0) := by
  induction s using Finset.induction_on with
  | empty =>
    convert isWeakGrad_const (ι := Fin N × Fin d) 0 using 1
    · funext y; simp
    · funext y p; simp
  | insert i s hi ih =>
    have h1 := isWeakGrad_comp_projBlock i (isWeakGrad_PhiMF hyp hac) (integrable_PhiMF hyp hac)
      (integrable_lipGrad_PhiMF hyp hac)
    convert h1.add ih using 1
    · funext y; rw [Finset.sum_insert hi]
    · funext y p
      by_cases hp : p.1 = i
      · subst hp; simp [hi]
      · simp [hp, Finset.mem_insert]

theorem isWeakGrad_sumPhi :
    IsWeakGrad (fun y : UnitAddTorus (Fin N × Fin d) => ∑ i, PhiMF V W μ (projBlock i y))
      (fun y p => lipGrad (PhiMF V W μ) (projBlock p.1 y) p.2) := by
  simpa using isWeakGrad_sumPhi_finset hyp hac (N := N) Finset.univ

end sumPhi

section ham
variable (hyp : Hyp V W KV KW) {μ : Measure (Torus d)} [IsProbabilityMeasure μ] (hac : μ ≪ haar d)
  {N : ℕ} (hN : 1 ≤ N)
include hyp hac hN

/-- `∇H_N = gsG + ∇Φ(Xᵢ)`. -/
theorem isWeakGrad_hamiltonian :
    IsWeakGrad (fun y => hamiltonian V W N (unflat y))
      (fun y p => gsG W μ N y p + lipGrad (PhiMF V W μ) (projBlock p.1 y) p.2) := by
  have h := ((isWeakGrad_gsU hyp hac hN (μ := μ)).add (isWeakGrad_sumPhi hyp hac (N := N))).sub_const
    (N * interE W μ μ / 2)
  convert h using 1
  funext y
  rw [hamiltonian_eq_U μ N (unflat y)]
  rfl

omit hN in
theorem exists_bound_hamiltonian : ∃ B, ∀ X : Config N d, |hamiltonian V W N X| ≤ B := by
  obtain ⟨B, hB⟩ := exists_bound_of_continuous (continuous_hamiltonian hyp N)
  exact ⟨B, hB⟩

theorem exists_bound_gradH : ∃ C, 0 ≤ C ∧ ∀ y p,
    |gsG W μ N y p + lipGrad (PhiMF V W μ) (projBlock p.1 y) p.2| ≤ C := by
  obtain ⟨C1, hC1, h1⟩ := exists_bound_gsG hyp hac (μ := μ) (N := N)
  obtain ⟨L, hL⟩ := lipschitz_PhiMF hyp hac
  refine ⟨C1 + L, by positivity, fun y p => (abs_add_le _ _).trans (add_le_add (h1 y p) ?_)⟩
  exact abs_lipGrad_le hL _ _

theorem measurable_gradH (p : Fin N × Fin d) :
    Measurable fun y => gsG W μ N y p + lipGrad (PhiMF V W μ) (projBlock p.1 y) p.2 :=
  (measurable_gsG hyp hac p).add ((measurable_lipGrad (continuous_PhiMF hyp) p.2).comp
    (measurable_projBlock p.1))

/-- **`∇e^{-H_N} = -e^{-H_N} ∇H_N`.** -/
theorem isWeakGrad_expNegH :
    IsWeakGrad (fun y => Real.exp (-hamiltonian V W N (unflat y)))
      (fun y p => -(Real.exp (-hamiltonian V W N (unflat y)) *
        (gsG W μ N y p + lipGrad (PhiMF V W μ) (projBlock p.1 y) p.2))) := by
  obtain ⟨B, hB⟩ := exists_bound_hamiltonian hyp hac (N := N)
  obtain ⟨C, hC0, hC⟩ := exists_bound_gradH hyp hac hN (μ := μ)
  have hHm : Measurable fun y : UnitAddTorus (Fin N × Fin d) => hamiltonian V W N (unflat y) :=
    (continuous_hamiltonian hyp N).measurable.comp measurable_unflat
  have h2 := (isWeakGrad_hamiltonian hyp hac hN).cmul 2
  have hi : Integrable (fun y : UnitAddTorus (Fin N × Fin d) => 2 * hamiltonian V W N (unflat y)) volume :=
    Integrable.of_bound (hHm.const_mul 2).aestronglyMeasurable (2 * B) (Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_mul, abs_two]; exact mul_le_mul_of_nonneg_left (hB _) zero_le_two)
  have hgi : ∀ p, Integrable (fun y => 2 * (gsG W μ N y p +
      lipGrad (PhiMF V W μ) (projBlock p.1 y) p.2)) volume := fun p =>
    Integrable.of_bound ((measurable_gradH hyp hac hN p).const_mul 2).aestronglyMeasurable (2 * C)
      (Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_mul, abs_two]; exact mul_le_mul_of_nonneg_left (hC _ _) zero_le_two)
  have h := isWeakGrad_exp_neg_half h2 hi hgi (B := 2 * B) fun y => by
    rw [abs_mul, abs_two]; exact mul_le_mul_of_nonneg_left (hB _) zero_le_two
  convert h using 1
  · funext y; congr 1; ring
  · funext y p
    rw [show -(2 * hamiltonian V W N (unflat y)) / 2 = -hamiltonian V W N (unflat y) by ring]
    ring

end ham

end SharpLSI
