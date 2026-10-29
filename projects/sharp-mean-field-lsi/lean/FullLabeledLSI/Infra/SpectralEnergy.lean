import FullLabeledLSI.Infra.SpectralCalc
import SharpSymmetricLSI.Paper.UpperApprox
import SharpSymmetricLSI.Paper.RefSpectrum3

/-!
# Spectral calculus for the reference semigroup, stage 2: the energy side

Manuscript Section 6.3.  With `Q = μ^{⊗N}`, `Λ_j = ∑_i λ_{j_i}`, `c_j(Ψ) = ∫ Ψ E_j dQ`:

* (S3, smooth case) for `C¹` `Φ` and every finite `T`: `∑_{j∈T} Λ_j c_j(Φ)² ≤ ∫ |∇Φ|² dQ`
  (`sum_Lam_coeff_sq_le_of_C1`), by the eigen-IBP and the energy formula for the finite combination
  `∑_{j∈T} c_j E_j`.
* (P1) `∫ (S_t Ψ - Ψ)² ≤ t · ℰ⁰(Ψ)` and (P3) `ℰ⁰(F_cut) ≤ ℰ⁰(Ψ)`, from the Bessel inequality for the
  energy `∑_j Λ_j c_j(Ψ)² ≤ ℰ⁰(Ψ)`.
-/

open MeasureTheory SharpLSI Filter Topology
open scoped ENNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace SharpLSI.FL.Spectral

/-! ### The smooth case -/

section Smooth

variable {N d : ℕ} {mu : Measure (Torus d)} [IsProbabilityMeasure mu] {e eC : ℕ → Torus d → ℝ}
  {lam : ℕ → ℝ}

/-- `E e j` and `Mtensor eC j` agree `Q`-a.e. when `eC j = e j` `μ`-a.e. -/
lemma E_ae_Mtensor (hae : ∀ j, eC j =ᵐ[mu] e j) (j : Fin N → ℕ) :
    E e j =ᵐ[Q mu N] Gross.Mtensor eC j := by
  have h : ∀ᵐ X ∂(Q mu N), ∀ i : Fin N, e (j i) (X i) = eC (j i) (X i) :=
    ae_all_iff.2 fun i => Gross.ae_pi_coord (p := fun x => e (j i) x = eC (j i) x)
      (hae (j i)).symm i
  filter_upwards [h] with X hX
  exact Finset.prod_congr rfl fun i _ => hX i

lemma coeff_eq_integral_Mtensor (hae : ∀ j, eC j =ᵐ[mu] e j) (Φ : Config N d → ℝ)
    (j : Fin N → ℕ) :
    coeff mu e j Φ = ∫ X, Φ X * Gross.Mtensor eC j X ∂(Q mu N) := by
  unfold coeff
  refine integral_congr_ae ?_
  filter_upwards [E_ae_Mtensor hae j] with X hX
  rw [hX]

/-- **ID1.** `Λ_j · c_j(Φ) = ∫ ∇Φ · ∇(M_j) dQ` for `C¹` `Φ`. -/
lemma Lam_mul_coeff_eq (hac : mu ≪ volume) (hca : volume ≪ mu) (hb : IsRefEigenbasis mu e lam)
    (hC1 : ∀ j, Gross.C1T (eC j)) (hae : ∀ j, eC j =ᵐ[mu] e j) (j : Fin N → ℕ)
    {Φ : Config N d → ℝ} (hΦ : Gross.C1C Φ) :
    Lam lam j * coeff mu e j Φ = ∫ X, Gross.gradPair Φ (Gross.Mtensor eC j) X ∂(Q mu N) := by
  rw [coeff_eq_integral_Mtensor hae]
  exact Gross.torus_eigen_ibp hac hca hb hC1 hae j hΦ

lemma integrable_gradPair {F G : Config N d → ℝ} (hF : Gross.C1C F) (hG : Gross.C1C G) :
    Integrable (Gross.gradPair F G) (Q mu N) := by
  obtain ⟨K, hK⟩ := Gross.bounded_gradPair hF hG
  exact Gross.integrable_of_bdd (Gross.measurable_gradPair hF hG) hK

/-- **Orthogonality of the gradients**: the energy of the finite combination `∑_{j∈T} c_j M_j`. -/
lemma integral_gradPair_comb (hac : mu ≪ volume) (hca : volume ≪ mu)
    (hb : IsRefEigenbasis mu e lam) (hC1 : ∀ j, Gross.C1T (eC j))
    (hae : ∀ j, eC j =ᵐ[mu] e j) (hlam : ∀ m, 0 ≤ lam m) (T : Finset (Fin N → ℕ))
    (c : (Fin N → ℕ) → ℝ) :
    ∫ X, Gross.gradPair (fun X => ∑ j ∈ T, c j * Gross.Mtensor eC j X)
        (fun X => ∑ j ∈ T, c j * Gross.Mtensor eC j X) X ∂(Q mu N) =
      ∑ j ∈ T, Lam lam j * c j ^ 2 := by
  have hPC : Gross.C1C (fun X : Config N d => ∑ j ∈ T, c j * Gross.Mtensor eC j X) :=
    Gross.C1C.sum T c fun j _ => Gross.C1C_Mtensor hC1 j
  have h1 := (Gross.torus_energy_formula hac hca hb hC1 hae T c
    (F := fun X : Config N d => ∑ j ∈ T, c j * ∏ i, e (j i) (X i)) (fun X => rfl)).2
  have h2 : refEnergy mu (fun X : Config N d => ∑ j ∈ T, c j * ∏ i, e (j i) (X i)) =
      refEnergy mu (fun X : Config N d => ∑ j ∈ T, c j * Gross.Mtensor eC j X) := by
    refine Gross.refEnergy_congr hac hPC ?_
    filter_upwards [Gross.ae_poly_eq_volume hca hae T c] with X hX
    rw [hX]
    unfold Gross.uFun Gross.MT Gross.Mtensor
    exact Finset.sum_coe_sort T (fun j => c j * ∏ i, eC (j i) (X i))
  have h3 := Gross.refEnergy_eq_gradPair hac hPC
  rw [h2, h3] at h1
  have h4 : 0 ≤ ∫ X, Gross.gradPair (fun X : Config N d => ∑ j ∈ T, c j * Gross.Mtensor eC j X)
      (fun X : Config N d => ∑ j ∈ T, c j * Gross.Mtensor eC j X) X ∂(Q mu N) :=
    integral_nonneg (Gross.gradPair_nonneg_self _)
  have h5 : 0 ≤ ∑ j ∈ T, Lam lam j * c j ^ 2 :=
    Finset.sum_nonneg fun j _ => mul_nonneg (Lam_nonneg hlam j) (sq_nonneg _)
  have h6 : ∑ j ∈ T, (∑ i, lam (j i)) * c j ^ 2 = ∑ j ∈ T, Lam lam j * c j ^ 2 := rfl
  rw [h6] at h1
  exact (ENNReal.ofReal_eq_ofReal_iff h4 h5).1 h1

/-- **(S3, smooth case)** Bessel inequality for the energy of a `C¹` function. -/
theorem sum_Lam_coeff_sq_le_of_C1 (hac : mu ≪ volume) (hca : volume ≪ mu)
    (hb : IsRefEigenbasis mu e lam) (hC1 : ∀ j, Gross.C1T (eC j))
    (hae : ∀ j, eC j =ᵐ[mu] e j) (hlam : ∀ m, 0 ≤ lam m) (T : Finset (Fin N → ℕ))
    {Φ : Config N d → ℝ} (hΦ : Gross.C1C Φ) :
    ∑ j ∈ T, Lam lam j * coeff mu e j Φ ^ 2 ≤ ∫ X, Gross.gradPair Φ Φ X ∂(Q mu N) := by
  have hM : ∀ j : Fin N → ℕ, Gross.C1C (Gross.Mtensor eC j) := fun j => Gross.C1C_Mtensor hC1 j
  set c : (Fin N → ℕ) → ℝ := fun j => coeff mu e j Φ with hc
  set P : Config N d → ℝ := fun X => ∑ j ∈ T, c j * Gross.Mtensor eC j X with hP
  have hPC : Gross.C1C P := Gross.C1C.sum T c fun j _ => hM j
  have h1 : ∫ X, Gross.gradPair Φ P X ∂(Q mu N) = ∑ j ∈ T, Lam lam j * c j ^ 2 := by
    have e1 : ∀ X, Gross.gradPair Φ P X =
        ∑ j ∈ T, c j * Gross.gradPair Φ (Gross.Mtensor eC j) X := fun X =>
      Gross.gradPair_sum_right T c (fun j _ => hM j) X
    simp_rw [e1]
    rw [integral_finsetSum _ fun j _ => (integrable_gradPair hΦ (hM j)).const_mul (c j)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul, ← Lam_mul_coeff_eq hac hca hb hC1 hae j hΦ]
    ring
  have h2 := integral_gradPair_comb hac hca hb hC1 hae hlam T c
  have h3 : ∀ X, 2 * Gross.gradPair Φ P X ≤ Gross.gradPair Φ Φ X + Gross.gradPair P P X := by
    intro X
    unfold Gross.gradPair
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun p _ => by
      nlinarith [sq_nonneg (Gross.dT (Φ ∘ unflat) p (flat X) - Gross.dT (P ∘ unflat) p (flat X))]
  have h4 : 2 * ∫ X, Gross.gradPair Φ P X ∂(Q mu N) ≤
      (∫ X, Gross.gradPair Φ Φ X ∂(Q mu N)) + ∫ X, Gross.gradPair P P X ∂(Q mu N) := by
    rw [← integral_const_mul, ← integral_add (integrable_gradPair hΦ hΦ)
      (integrable_gradPair hPC hPC)]
    exact integral_mono ((integrable_gradPair hΦ hPC).const_mul 2)
      ((integrable_gradPair hΦ hΦ).add (integrable_gradPair hPC hPC)) h3
  rw [h1] at h4
  rw [h2] at h4
  linarith

lemma toReal_refEnergy_of_C1 (hac : mu ≪ volume) {Φ : Config N d → ℝ} (hΦ : Gross.C1C Φ) :
    (refEnergy mu Φ).toReal = ∫ X, Gross.gradPair Φ Φ X ∂(Q mu N) := by
  rw [Gross.refEnergy_eq_gradPair hac hΦ,
    ENNReal.toReal_ofReal (integral_nonneg (Gross.gradPair_nonneg_self _))]

end Smooth

/-! ### Consequences of the Bessel inequality for the energy -/

section Consequences

variable {N d : ℕ} {mu : Measure (Torus d)} [IsProbabilityMeasure mu] {e eC : ℕ → Torus d → ℝ}
  {lam : ℕ → ℝ}

lemma exp_neg_sub_one_sq_le {x : ℝ} (hx : 0 ≤ x) : (Real.exp (-x) - 1) ^ 2 ≤ x := by
  have h1 : -x + 1 ≤ Real.exp (-x) := Real.add_one_le_exp (-x)
  have h2 : 0 < Real.exp (-x) := Real.exp_pos _
  have h3 : Real.exp (-x) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  nlinarith

/-- **(P1)** `∫ (S_t Ψ - Ψ)² ≤ t · E` as soon as `∑ Λ_j c_j² ≤ E`. -/
theorem integral_Sfun_sub_sq_le (hb : IsRefEigenbasis mu e lam) (hlam : ∀ m, 0 ≤ lam m) {t : ℝ}
    (ht : 0 ≤ t) {Ψ : Config N d → ℝ} (hΨ : MemLp Ψ 2 (Q mu N)) {E : ℝ}
    (hsum : Summable (fun j : Fin N → ℕ => Lam lam j * coeff mu e j Ψ ^ 2))
    (hle : ∑' j : Fin N → ℕ, Lam lam j * coeff mu e j Ψ ^ 2 ≤ E) :
    ∫ X, (Sfun hb t Ψ X - Ψ X) ^ 2 ∂(Q mu N) ≤ t * E := by
  have h1 := hasSum_Sfun_sub_sq hb hlam ht hΨ
  have h2 := hsum.hasSum.mul_left t
  have h3 : ∫ X, (Sfun hb t Ψ X - Ψ X) ^ 2 ∂(Q mu N) ≤
      t * ∑' j : Fin N → ℕ, Lam lam j * coeff mu e j Ψ ^ 2 := by
    refine hasSum_le (fun j => ?_) h1 h2
    have hx : 0 ≤ t * Lam lam j := mul_nonneg ht (Lam_nonneg hlam j)
    have := exp_neg_sub_one_sq_le hx
    calc ((Real.exp (-(t * Lam lam j)) - 1) * coeff mu e j Ψ) ^ 2
        = (Real.exp (-(t * Lam lam j)) - 1) ^ 2 * coeff mu e j Ψ ^ 2 := by ring
      _ ≤ (t * Lam lam j) * coeff mu e j Ψ ^ 2 :=
          mul_le_mul_of_nonneg_right this (sq_nonneg _)
      _ = t * (Lam lam j * coeff mu e j Ψ ^ 2) := by ring
  exact h3.trans (mul_le_mul_of_nonneg_left hle ht)

/-- **(P3)** `ℰ⁰(F_cut) ≤ ℰ⁰(Ψ)` as soon as `∑ Λ_j c_j² ≤ (ℰ⁰(Ψ)).toReal` and `ℰ⁰(Ψ) < ∞`. -/
theorem refEnergy_Fcut_le (hac : mu ≪ volume) (hca : volume ≪ mu)
    (hb : IsRefEigenbasis mu e lam) (hC1 : ∀ j, Gross.C1T (eC j))
    (hae : ∀ j, eC j =ᵐ[mu] e j) (hlam : ∀ m, 0 ≤ lam m) {t : ℝ} (ht : 0 ≤ t) (L : ℝ)
    {Ψ : Config N d → ℝ}
    (hsum : Summable (fun j : Fin N → ℕ => Lam lam j * coeff mu e j Ψ ^ 2))
    (hle : ∑' j : Fin N → ℕ, Lam lam j * coeff mu e j Ψ ^ 2 ≤ (refEnergy mu Ψ).toReal)
    (hfin : refEnergy mu Ψ ≠ ⊤) :
    refEnergy mu (Fcut mu e lam t L Ψ) ≤ refEnergy mu Ψ := by
  have h1 := (Gross.torus_energy_formula hac hca hb hC1 hae (Tset lam N L)
    (fun j => Real.exp (-(t * Lam lam j)) * coeff mu e j Ψ)
    (F := Fcut mu e lam t L Ψ) (fun X => rfl)).2
  rw [h1]
  conv_rhs => rw [← ENNReal.ofReal_toReal hfin]
  refine ENNReal.ofReal_le_ofReal ?_
  refine le_trans ?_ hle
  have h2 : ∑ j ∈ Tset lam N L, (∑ i, lam (j i)) *
      (Real.exp (-(t * Lam lam j)) * coeff mu e j Ψ) ^ 2 ≤
      ∑ j ∈ Tset lam N L, Lam lam j * coeff mu e j Ψ ^ 2 := by
    refine Finset.sum_le_sum fun j _ => ?_
    have hL := Lam_nonneg hlam j
    have h3 : Real.exp (-(t * Lam lam j)) ^ 2 ≤ 1 := by
      have h4 : Real.exp (-(t * Lam lam j)) ≤ 1 :=
        Real.exp_le_one_iff.2 (neg_nonpos.2 (mul_nonneg ht hL))
      have h5 := Real.exp_pos (-(t * Lam lam j))
      nlinarith
    calc (∑ i, lam (j i)) * (Real.exp (-(t * Lam lam j)) * coeff mu e j Ψ) ^ 2
        = Lam lam j * (Real.exp (-(t * Lam lam j)) ^ 2 * coeff mu e j Ψ ^ 2) := by
          unfold Lam; ring
      _ ≤ Lam lam j * (1 * coeff mu e j Ψ ^ 2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h3 (sq_nonneg _)) hL
      _ = Lam lam j * coeff mu e j Ψ ^ 2 := by ring
  refine h2.trans ?_
  exact hsum.sum_le_tsum _ fun j _ => mul_nonneg (Lam_nonneg hlam j) (sq_nonneg _)

/-- `eLpNorm` form of (P1): `‖Ψ - S_t Ψ‖₂² ≤ t · E`. -/
theorem eLpNorm_sub_Sfun_sq_le (hb : IsRefEigenbasis mu e lam) (hlam : ∀ m, 0 ≤ lam m) {t : ℝ}
    (ht : 0 ≤ t) {Ψ : Config N d → ℝ} (hΨ : MemLp Ψ 2 (Q mu N)) {E : ℝ}
    (hsum : Summable (fun j : Fin N → ℕ => Lam lam j * coeff mu e j Ψ ^ 2))
    (hle : ∑' j : Fin N → ℕ, Lam lam j * coeff mu e j Ψ ^ 2 ≤ E) :
    eLpNorm (fun X => Ψ X - Sfun hb t Ψ X) 2 (Q mu N) ^ 2 ≤ ENNReal.ofReal (t * E) := by
  have hD : MemLp (fun X => Ψ X - Sfun hb t Ψ X) 2 (Q mu N) := hΨ.sub (Sfun_memLp hb t hΨ)
  have h1 := integral_Sfun_sub_sq_le hb hlam ht hΨ hsum hle
  have h2 : eLpNorm (fun X => Ψ X - Sfun hb t Ψ X) 2 (Q mu N) =
      ENNReal.ofReal ‖hD.toLp (fun X => Ψ X - Sfun hb t Ψ X)‖ := by
    rw [← eLpNorm_coe_eq_ofReal_norm, eLpNorm_congr_ae hD.coeFn_toLp]
  rw [h2, ← ENNReal.ofReal_pow (norm_nonneg _), norm_toLp_sq hD]
  refine ENNReal.ofReal_le_ofReal (le_trans (le_of_eq ?_) h1)
  exact integral_congr_ae (Filter.Eventually.of_forall fun X => by ring)

end Consequences

/-! ### The `C¹` case: Bessel inequality, (P1) and (P3) -/

section C1Case

variable {N d : ℕ} {mu : Measure (Torus d)} [IsProbabilityMeasure mu] {e eC : ℕ → Torus d → ℝ}
  {lam : ℕ → ℝ}

lemma summable_tsum_le_of_sum_le {ι : Type*} {f : ι → ℝ} (hf : ∀ i, 0 ≤ f i) {E : ℝ}
    (h : ∀ T : Finset ι, ∑ i ∈ T, f i ≤ E) : Summable f ∧ ∑' i, f i ≤ E :=
  have hs : Summable f := summable_of_sum_le hf h
  ⟨hs, hs.tsum_le_of_sum_le h⟩

lemma memLp_two_of_C1C {Φ : Config N d → ℝ} (hΦ : Gross.C1C Φ) : MemLp Φ 2 (Q mu N) := by
  obtain ⟨K, hK⟩ := hΦ.bounded
  exact MemLp.of_bound hΦ.measurable.aestronglyMeasurable K
    (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hK x)

/-- **(S3 for `C¹`)** Summability and the Bessel inequality for the energy. -/
theorem bessel_energy_of_C1 (hac : mu ≪ volume) (hca : volume ≪ mu)
    (hb : IsRefEigenbasis mu e lam) (hC1 : ∀ j, Gross.C1T (eC j))
    (hae : ∀ j, eC j =ᵐ[mu] e j) (hlam0 : lam 0 = 0) {Φ : Config N d → ℝ}
    (hΦ : Gross.C1C Φ) :
    Summable (fun j : Fin N → ℕ => Lam lam j * coeff mu e j Φ ^ 2) ∧
      ∑' j : Fin N → ℕ, Lam lam j * coeff mu e j Φ ^ 2 ≤ (refEnergy mu Φ).toReal := by
  have hlam := lam_nonneg_of_ref hb hlam0
  rw [toReal_refEnergy_of_C1 hac hΦ]
  exact summable_tsum_le_of_sum_le (fun j => mul_nonneg (Lam_nonneg hlam j) (sq_nonneg _))
    fun T => sum_Lam_coeff_sq_le_of_C1 hac hca hb hC1 hae hlam T hΦ

/-- **(P1 for `C¹`)** -/
theorem integral_Sfun_sub_sq_le_of_C1 (hac : mu ≪ volume) (hca : volume ≪ mu)
    (hb : IsRefEigenbasis mu e lam) (hC1 : ∀ j, Gross.C1T (eC j))
    (hae : ∀ j, eC j =ᵐ[mu] e j) (hlam0 : lam 0 = 0) {t : ℝ} (ht : 0 ≤ t)
    {Φ : Config N d → ℝ} (hΦ : Gross.C1C Φ) :
    ∫ X, (Sfun hb t Φ X - Φ X) ^ 2 ∂(Q mu N) ≤ t * (refEnergy mu Φ).toReal := by
  obtain ⟨hs, hle⟩ := bessel_energy_of_C1 hac hca hb hC1 hae hlam0 hΦ
  exact integral_Sfun_sub_sq_le hb (lam_nonneg_of_ref hb hlam0) ht (memLp_two_of_C1C hΦ) hs hle

/-- **(P3 for `C¹`)** -/
theorem refEnergy_Fcut_le_of_C1 (hac : mu ≪ volume) (hca : volume ≪ mu)
    (hb : IsRefEigenbasis mu e lam) (hC1 : ∀ j, Gross.C1T (eC j))
    (hae : ∀ j, eC j =ᵐ[mu] e j) (hlam0 : lam 0 = 0) {t : ℝ} (ht : 0 ≤ t) (L : ℝ)
    {Φ : Config N d → ℝ} (hΦ : Gross.C1C Φ) :
    refEnergy mu (Fcut mu e lam t L Φ) ≤ refEnergy mu Φ := by
  obtain ⟨hs, hle⟩ := bessel_energy_of_C1 hac hca hb hC1 hae hlam0 hΦ
  refine refEnergy_Fcut_le hac hca hb hC1 hae (lam_nonneg_of_ref hb hlam0) ht L hs hle ?_
  rw [Gross.refEnergy_eq_gradPair hac hΦ]
  exact ENNReal.ofReal_ne_top

end C1Case

/-! ### Density comparison between `Q = μ^{⊗N}` and Haar measure -/

section Density

lemma pi_le_smul_pi {α : Type*} [MeasurableSpace α] {μ ν : Measure α} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {c : ℝ≥0∞} (h : μ ≤ c • ν) :
    ∀ N : ℕ, (Measure.pi fun _ : Fin N => μ) ≤ c ^ N • (Measure.pi fun _ : Fin N => ν)
  | 0 => by
    rw [pow_zero, one_smul, Measure.pi_of_empty, Measure.pi_of_empty]
  | n + 1 => by
    have ih := pi_le_smul_pi h n
    have e1 := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) 0
    have e2 := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => ν) 0
    have hprod : μ.prod (Measure.pi fun _ : Fin n => μ) ≤
        (c • ν).prod (c ^ n • Measure.pi fun _ : Fin n => ν) := Measure.prod_mono h ih
    rw [Measure.prod_smul_left, Measure.prod_smul_right, smul_smul, ← pow_succ'] at hprod
    have hμ' := (MeasurePreserving.symm _ e1).map_eq
    have hν' := (MeasurePreserving.symm _ e2).map_eq
    have key := Measure.map_mono hprod
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => α) 0).symm.measurable
    rw [Measure.map_smul _ (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => α) 0).symm.measurable.aemeasurable, hν', hμ'] at key
    exact key

variable {N d : ℕ} {mu : Measure (Torus d)} [IsProbabilityMeasure mu]

lemma map_flat_pi_le {Cu : ℝ} (hup : mu ≤ ENNReal.ofReal Cu • (volume : Measure (Torus d)))
    (N : ℕ) :
    (Q mu N).map flat ≤
      ENNReal.ofReal Cu ^ N • (volume : Measure (UnitAddTorus (Fin N × Fin d))) := by
  have h := pi_le_smul_pi hup N
  calc (Q mu N).map flat
      ≤ (ENNReal.ofReal Cu ^ N • Measure.pi fun _ : Fin N => (volume : Measure (Torus d))).map
          flat := Measure.map_mono h measurable_flat
    _ = ENNReal.ofReal Cu ^ N • (volume : Measure (Config N d)).map flat := by
        rw [Measure.map_smul _ measurable_flat.aemeasurable]; rfl
    _ = _ := by rw [map_flat_volume N]

lemma vol_le_map_flat_pi {Cl : ℝ} (hlow : (volume : Measure (Torus d)) ≤ ENNReal.ofReal Cl • mu)
    (N : ℕ) :
    (volume : Measure (UnitAddTorus (Fin N × Fin d))) ≤
      ENNReal.ofReal Cl ^ N • (Q mu N).map flat := by
  have h := pi_le_smul_pi hlow N
  calc (volume : Measure (UnitAddTorus (Fin N × Fin d)))
      = (volume : Measure (Config N d)).map flat := (map_flat_volume N).symm
    _ ≤ (ENNReal.ofReal Cl ^ N • Q mu N).map flat := Measure.map_mono h measurable_flat
    _ = _ := Measure.map_smul _ measurable_flat.aemeasurable

lemma lintegral_flat_le {Cu : ℝ} (hup : mu ≤ ENNReal.ofReal Cu • (volume : Measure (Torus d)))
    (N : ℕ) (F : UnitAddTorus (Fin N × Fin d) → ℝ≥0∞) :
    ∫⁻ X, F (flat X) ∂(Q mu N) ≤
      ENNReal.ofReal Cu ^ N * ∫⁻ y, F y ∂(volume : Measure (UnitAddTorus (Fin N × Fin d))) := by
  calc ∫⁻ X, F (flat X) ∂(Q mu N)
      = ∫⁻ y, F y ∂((Q mu N).map flat) :=
        (lintegral_map_equiv F (flatEquiv N d)).symm
    _ ≤ ∫⁻ y, F y ∂(ENNReal.ofReal Cu ^ N • (volume : Measure (UnitAddTorus (Fin N × Fin d)))) :=
        lintegral_mono' (map_flat_pi_le hup N) le_rfl
    _ = _ := by rw [lintegral_smul_measure, smul_eq_mul]

end Density

/-! ### Smooth approximation of `H¹(Q)` functions -/

section H1Approx

variable {N d : ℕ} {mu : Measure (Torus d)} [IsProbabilityMeasure mu]

lemma ac_map_flat {Cu : ℝ} (hup : mu ≤ ENNReal.ofReal Cu • (volume : Measure (Torus d))) :
    (Q mu N).map flat ≪ (volume : Measure (UnitAddTorus (Fin N × Fin d))) :=
  Measure.absolutelyContinuous_of_le_smul (map_flat_pi_le hup N)

lemma lintegral_enorm_sq_ne_top {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    (hf : MemLp f 2 μ) : ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ ≠ ⊤ := by
  have h := hf.integrable_sq.hasFiniteIntegral
  simp only [HasFiniteIntegral, enorm_pow] at h
  exact h.ne

/-- `L²` bounds for the function and its weak gradient on the flat torus. -/
lemma h1_flat_data {Cl : ℝ} (hlow : (volume : Measure (Torus d)) ≤ ENNReal.ofReal Cl • mu)
    {Ψ : Config N d → ℝ} (hH : MemH1C (Q mu N) Ψ) :
    MemLp (Ψ ∘ unflat) 2 (volume : Measure (UnitAddTorus (Fin N × Fin d))) ∧
      ∀ p, MemLp (fun y => weakGrad (Ψ ∘ unflat) y p) 2
        (volume : Measure (UnitAddTorus (Fin N × Fin d))) := by
  have hne : ENNReal.ofReal Cl ^ N ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  have hle := vol_le_map_flat_pi (mu := mu) hlow N
  refine ⟨MemLp.of_measure_le_smul hne hle hH.2.1, fun p => ?_⟩
  have hs := MemLp.of_measure_le_smul hne hle hH.2.2
  exact hs.of_le ((isWeakGrad_weakGrad hH.1).aestronglyMeasurable_grad p)
    (Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      exact abs_le_sqrt_sqNorm _ p)

lemma memLp_of_H1 {Ψ : Config N d → ℝ} (hH : MemH1C (Q mu N) Ψ) : MemLp Ψ 2 (Q mu N) :=
  (memLp_map_measure_iff hH.2.1.aestronglyMeasurable measurable_flat.aemeasurable).1 hH.2.1

lemma memLp_grad_comp_flat {Cu : ℝ} (hup : mu ≤ ENNReal.ofReal Cu • (volume : Measure (Torus d)))
    {Ψ : Config N d → ℝ} (hH : MemH1C (Q mu N) Ψ) (p : Fin N × Fin d) :
    MemLp (fun X : Config N d => weakGrad (Ψ ∘ unflat) (flat X) p) 2 (Q mu N) := by
  have hac := ac_map_flat (mu := mu) (N := N) hup
  have hsm : AEStronglyMeasurable (fun y => weakGrad (Ψ ∘ unflat) y p) ((Q mu N).map flat) :=
    ((isWeakGrad_weakGrad hH.1).aestronglyMeasurable_grad p).mono_ac hac
  have hs : MemLp (fun y => weakGrad (Ψ ∘ unflat) y p) 2 ((Q mu N).map flat) :=
    hH.2.2.of_le hsm (Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      exact abs_le_sqrt_sqNorm _ p)
  exact (memLp_map_measure_iff hs.aestronglyMeasurable measurable_flat.aemeasurable).1 hs

lemma gradSqC_eq_sum (Ψ : Config N d → ℝ) (X : Config N d) :
    gradSqC Ψ X = ∑ p : Fin N × Fin d, weakGrad (Ψ ∘ unflat) (flat X) p ^ 2 := by
  unfold gradSqC weakGradC
  rw [Fintype.sum_prod_type]

/-- The reference energy of an `H¹(Q)` function as a real sum of integrals. -/
lemma refEnergy_eq_ofReal_sum {Cu : ℝ}
    (hup : mu ≤ ENNReal.ofReal Cu • (volume : Measure (Torus d)))
    {Ψ : Config N d → ℝ} (hH : MemH1C (Q mu N) Ψ) :
    refEnergy mu Ψ = ENNReal.ofReal
      (∑ p : Fin N × Fin d, ∫ X, weakGrad (Ψ ∘ unflat) (flat X) p ^ 2 ∂(Q mu N)) := by
  have hint : ∀ p : Fin N × Fin d, Integrable (fun X : Config N d =>
      weakGrad (Ψ ∘ unflat) (flat X) p ^ 2) (Q mu N) := fun p =>
    (memLp_grad_comp_flat hup hH p).integrable_sq
  have hsum : Integrable (fun X => ∑ p : Fin N × Fin d, weakGrad (Ψ ∘ unflat) (flat X) p ^ 2)
      (Q mu N) := integrable_finsetSum _ fun p _ => hint p
  rw [← integral_finsetSum _ fun p _ => hint p,
    ofReal_integral_eq_lintegral_ofReal hsum (Eventually.of_forall fun X =>
      Finset.sum_nonneg fun p _ => sq_nonneg _)]
  unfold refEnergy
  refine lintegral_congr fun X => ?_
  rw [gradSqC_eq_sum]

lemma refEnergy_ne_top_of_H1 {Cu : ℝ}
    (hup : mu ≤ ENNReal.ofReal Cu • (volume : Measure (Torus d)))
    {Ψ : Config N d → ℝ} (hH : MemH1C (Q mu N) Ψ) : refEnergy mu Ψ ≠ ⊤ := by
  rw [refEnergy_eq_ofReal_sum hup hH]; exact ENNReal.ofReal_ne_top

lemma toReal_refEnergy_eq_sum {Cu : ℝ}
    (hup : mu ≤ ENNReal.ofReal Cu • (volume : Measure (Torus d)))
    {Ψ : Config N d → ℝ} (hH : MemH1C (Q mu N) Ψ) :
    (refEnergy mu Ψ).toReal =
      ∑ p : Fin N × Fin d, ∫ X, weakGrad (Ψ ∘ unflat) (flat X) p ^ 2 ∂(Q mu N) := by
  rw [refEnergy_eq_ofReal_sum hup hH, ENNReal.toReal_ofReal]
  exact Finset.sum_nonneg fun p _ => integral_nonneg fun X => sq_nonneg _

/-! #### Mollification: `C¹` property and classical gradient -/

lemma C1T_moll {ι : Type*} [Fintype ι] [DecidableEq ι] (n : ℕ) {u : UnitAddTorus ι → ℝ}
    (hu : Integrable u volume) : Gross.C1T (moll n u) :=
  (moll_comp_liftT_contDiff n hu).of_le (by simp)

lemma dT_moll {ι : Type*} [Fintype ι] [DecidableEq ι] {f : UnitAddTorus ι → ℝ}
    {g : UnitAddTorus ι → ι → ℝ} (h : IsWeakGrad f g) (n : ℕ) (k : ι) (y : UnitAddTorus ι) :
    Gross.dT (moll n f) k y = moll n (fun z => g z k) y := by
  unfold Gross.dT
  rw [moll_comp_liftT, fderiv_mollL_of_isWeakGrad h n (secT y) k]
  rfl

/-- The mollification, viewed as a function on `Config N d`. -/
def mollC (n : ℕ) (u : UnitAddTorus (Fin N × Fin d) → ℝ) : Config N d → ℝ :=
  fun X => moll n u (flat X)

lemma C1C_mollC (n : ℕ) {u : UnitAddTorus (Fin N × Fin d) → ℝ} (hu : Integrable u volume) :
    Gross.C1C (mollC n u) := C1T_moll n hu

lemma gradPair_mollC {u : UnitAddTorus (Fin N × Fin d) → ℝ}
    {g : UnitAddTorus (Fin N × Fin d) → Fin N × Fin d → ℝ} (h : IsWeakGrad u g) (n : ℕ)
    (X : Config N d) :
    Gross.gradPair (mollC n u) (mollC n u) X =
      ∑ p : Fin N × Fin d, moll n (fun z => g z p) (flat X) ^ 2 := by
  unfold Gross.gradPair
  refine Finset.sum_congr rfl fun p _ => ?_
  have := dT_moll h n p (flat X)
  change Gross.dT (moll n u) p (flat X) * Gross.dT (moll n u) p (flat X) = _
  rw [this]; ring

lemma memLp_two_comp_flat_of_C1T {f : UnitAddTorus (Fin N × Fin d) → ℝ} (hf : Gross.C1T f) :
    MemLp (fun X : Config N d => f (flat X)) 2 (Q mu N) := by
  obtain ⟨K, hK⟩ := hf.bounded
  exact MemLp.of_bound (hf.measurable.comp measurable_flat).aestronglyMeasurable K
    (Eventually.of_forall fun X => by simpa [Real.norm_eq_abs] using hK (flat X))

/-! #### Transfer of `L²(Haar)` convergence to `L²(Q)` -/

lemma tendsto_integral_sq_flat {Cu : ℝ}
    (hup : mu ≤ ENNReal.ofReal Cu • (volume : Measure (Torus d)))
    {v : ℕ → UnitAddTorus (Fin N × Fin d) → ℝ} {w : UnitAddTorus (Fin N × Fin d) → ℝ}
    (hv : ∀ n, Measurable (v n)) (hw : AEMeasurable w volume)
    (hL : Tendsto (fun n => ∫⁻ y, ‖v n y - w y‖ₑ ^ 2) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ X, (v n (flat X) - w (flat X)) ^ 2 ∂(Q mu N)) atTop (𝓝 0) := by
  have hac := ac_map_flat (mu := mu) (N := N) hup
  have hmeas : ∀ n, AEStronglyMeasurable (fun X : Config N d => (v n (flat X) - w (flat X)) ^ 2)
      (Q mu N) := fun n => by
    have h1 : AEMeasurable (fun y => (v n y - w y) ^ 2) volume :=
      ((hv n).aemeasurable.sub hw).pow_const 2
    exact (h1.mono_ac hac).comp_aemeasurable measurable_flat.aemeasurable |>.aestronglyMeasurable
  have hK : Tendsto (fun n => ENNReal.ofReal Cu ^ N * ∫⁻ y, ‖v n y - w y‖ₑ ^ 2) atTop (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal Cu ^ N) hL
      (Or.inr (ENNReal.pow_ne_top ENNReal.ofReal_ne_top))
    rwa [mul_zero] at this
  have hKr : Tendsto (fun n => (ENNReal.ofReal Cu ^ N * ∫⁻ y, ‖v n y - w y‖ₑ ^ 2).toReal)
      atTop (𝓝 0) := by
    have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hK
    rw [ENNReal.toReal_zero] at h
    exact h
  have hev : ∀ᶠ n in atTop, ENNReal.ofReal Cu ^ N * ∫⁻ y, ‖v n y - w y‖ₑ ^ 2 ≠ ⊤ :=
    hK.eventually_ne ENNReal.zero_ne_top
  refine squeeze_zero' (Eventually.of_forall fun n => integral_nonneg fun X => sq_nonneg _) ?_ hKr
  filter_upwards [hev] with n hn
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun X => sq_nonneg _) (hmeas n)]
  refine ENNReal.toReal_mono hn ?_
  simp only [ofReal_sq_eq_enorm_sq]
  exact lintegral_flat_le hup N (fun y => ‖v n y - w y‖ₑ ^ 2)

lemma integral_sq_le_trick {α : Type*} [MeasurableSpace α] {μ : Measure α} {f g : α → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) {δ : ℝ} (hδ : 0 < δ) :
    ∫ x, f x ^ 2 ∂μ ≤ (1 + δ) * ∫ x, g x ^ 2 ∂μ + (1 + 1 / δ) * ∫ x, (f x - g x) ^ 2 ∂μ := by
  have hfg : Integrable (fun x => (f x - g x) ^ 2) μ := (hf.sub hg).integrable_sq
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_add (hg.integrable_sq.const_mul _) (hfg.const_mul _)]
  refine integral_mono hf.integrable_sq
    ((hg.integrable_sq.const_mul _).add (hfg.const_mul _)) fun x => ?_
  have h1 : 0 ≤ (δ * g x - (f x - g x)) ^ 2 / δ := by positivity
  have h2 : (δ * g x - (f x - g x)) ^ 2 / δ =
      δ * g x ^ 2 - 2 * g x * (f x - g x) + (f x - g x) ^ 2 / δ := by
    field_simp
    ring
  have h3 : (f x - g x) ^ 2 / δ = 1 / δ * (f x - g x) ^ 2 := by ring
  show f x ^ 2 ≤ (1 + δ) * g x ^ 2 + (1 + 1 / δ) * (f x - g x) ^ 2
  nlinarith [h1, h2, h3]

end H1Approx

/-! ### The Bessel inequality for the energy of an `H¹(Q)` function -/

section H1Main

variable {N d : ℕ} {mu : Measure (Torus d)} [IsProbabilityMeasure mu] {e eC : ℕ → Torus d → ℝ}
  {lam : ℕ → ℝ}

lemma tendsto_coeff_of_L2 (hb : IsRefEigenbasis mu e lam) {Φ : ℕ → Config N d → ℝ}
    {Ψ : Config N d → ℝ} (hΦ : ∀ n, MemLp (Φ n) 2 (Q mu N)) (hΨ : MemLp Ψ 2 (Q mu N))
    (hL : Tendsto (fun n => ∫ X, (Φ n X - Ψ X) ^ 2 ∂(Q mu N)) atTop (𝓝 0))
    (j : Fin N → ℕ) :
    Tendsto (fun n => coeff mu e j (Φ n)) atTop (𝓝 (coeff mu e j Ψ)) := by
  have hEj : MemLp (E e j) 2 (Q mu N) := tensor_memLp mu e (ref_memLp hb) N j
  have hE1 : ∫ ω, E e j ω * E e j ω ∂(Q mu N) = 1 := by
    have := tensor_orthonormal mu e hb.orthonormal N j j
    simpa using this
  have hsq : ∀ n, |coeff mu e j (Φ n) - coeff mu e j Ψ| ≤
      Real.sqrt (∫ X, (Φ n X - Ψ X) ^ 2 ∂(Q mu N)) := by
    intro n
    apply Real.abs_le_sqrt
    have h1 : coeff mu e j (Φ n) - coeff mu e j Ψ =
        ∫ X, (Φ n X - Ψ X) * E e j X ∂(Q mu N) := by
      unfold coeff
      have hi1 : Integrable (fun ω => Φ n ω * E e j ω) (Q mu N) := (hΦ n).integrable_mul hEj
      have hi2 : Integrable (fun ω => Ψ ω * E e j ω) (Q mu N) := hΨ.integrable_mul hEj
      rw [← integral_sub hi1 hi2]
      exact integral_congr_ae (Eventually.of_forall fun X => by ring)
    rw [h1]
    exact sq_integral_mul_le ((hΦ n).sub hΨ) hEj hE1
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_)
    (by simpa using (Real.continuous_sqrt.tendsto 0).comp hL)
  rw [Real.dist_eq]
  exact hsq n

/-- **Smooth approximation of `H¹(Q)` functions.**  There are `C¹` functions `Φ n` with
`Φ n → Ψ` in `L²(Q)` and `limsup ∫ |∇Φ n|² dQ ≤ ℰ⁰(Ψ)` (mollification on the flat torus). -/
theorem exists_C1_approx {Cu Cl : ℝ} (hup : mu ≤ ENNReal.ofReal Cu • (volume : Measure (Torus d)))
    (hlow : (volume : Measure (Torus d)) ≤ ENNReal.ofReal Cl • mu)
    {Ψ : Config N d → ℝ} (hH : MemH1C (Q mu N) Ψ) :
    ∃ Φ : ℕ → Config N d → ℝ, (∀ n, Gross.C1C (Φ n)) ∧
      Tendsto (fun n => ∫ X, (Φ n X - Ψ X) ^ 2 ∂(Q mu N)) atTop (𝓝 0) ∧
      ∀ ε > 0, ∀ᶠ n in atTop,
        ∫ X, Gross.gradPair (Φ n) (Φ n) X ∂(Q mu N) ≤ (refEnergy mu Ψ).toReal + ε := by
  classical
  have hw : IsWeakGrad (Ψ ∘ unflat) (weakGrad (Ψ ∘ unflat)) := isWeakGrad_weakGrad hH.1
  obtain ⟨hu2, hg2⟩ := h1_flat_data hlow hH
  have hu1 : Integrable (Ψ ∘ unflat) volume := hu2.integrable (by norm_num)
  have hg1 : ∀ p, Integrable (fun y => weakGrad (Ψ ∘ unflat) y p) volume := fun p =>
    (hg2 p).integrable (by norm_num)
  obtain ⟨ns, hns, hae⟩ := exists_subseq_moll_ae hu1 hg1
  have hLu : Tendsto (fun j => ∫⁻ y, ‖moll (ns j) (Ψ ∘ unflat) y - (Ψ ∘ unflat) y‖ₑ ^ 2)
      atTop (𝓝 0) :=
    L2Tendsto_moll hu1 (lintegral_enorm_sq_ne_top hu2) (hae.mono fun y hy => hy.1)
  have hLg : ∀ p, Tendsto (fun j => ∫⁻ y, ‖moll (ns j) (fun z => weakGrad (Ψ ∘ unflat) z p) y -
      weakGrad (Ψ ∘ unflat) y p‖ₑ ^ 2) atTop (𝓝 0) := fun p =>
    L2Tendsto_moll (u := fun z => weakGrad (Ψ ∘ unflat) z p) (hg1 p)
      (lintegral_enorm_sq_ne_top (hg2 p)) (hae.mono fun y hy => hy.2 p)
  refine ⟨fun n => mollC (ns n) (Ψ ∘ unflat), fun n => C1C_mollC _ hu1, ?_, ?_⟩
  · exact tendsto_integral_sq_flat (N := N) (mu := mu) hup
      (v := fun j => moll (ns j) (Ψ ∘ unflat)) (w := Ψ ∘ unflat)
      (fun j => measurable_moll _ hu1) hu2.aestronglyMeasurable.aemeasurable hLu
  · intro ε hε
    have hDp : ∀ p : Fin N × Fin d, Tendsto (fun n => ∫ X,
        (moll (ns n) (fun z => weakGrad (Ψ ∘ unflat) z p) (flat X) -
          weakGrad (Ψ ∘ unflat) (flat X) p) ^ 2 ∂(Q mu N)) atTop (𝓝 0) := fun p =>
      tendsto_integral_sq_flat (N := N) (mu := mu) hup
        (v := fun j => moll (ns j) (fun z => weakGrad (Ψ ∘ unflat) z p))
        (w := fun y => weakGrad (Ψ ∘ unflat) y p) (fun j => measurable_moll _ (hg1 p))
        (hg2 p).aestronglyMeasurable.aemeasurable (hLg p)
    obtain ⟨Dn, hDn⟩ : ∃ D : ℕ → ℝ, D = fun n => ∑ p : Fin N × Fin d, ∫ X,
        (moll (ns n) (fun z => weakGrad (Ψ ∘ unflat) z p) (flat X) -
          weakGrad (Ψ ∘ unflat) (flat X) p) ^ 2 ∂(Q mu N) := ⟨_, rfl⟩
    have hDsum : Tendsto Dn atTop (𝓝 0) := by
      rw [hDn]
      have := tendsto_finsetSum Finset.univ fun p _ => hDp p
      simpa using this
    obtain ⟨Eψ, hEψdef⟩ : ∃ E : ℝ, E = (refEnergy mu Ψ).toReal := ⟨_, rfl⟩
    have hEψ : 0 ≤ Eψ := by rw [hEψdef]; exact ENNReal.toReal_nonneg
    obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = ε / (2 * (Eψ + 1)) := ⟨_, rfl⟩
    have hδpos : 0 < δ := by rw [hδ]; positivity
    have hδE : δ * Eψ ≤ ε / 2 := by
      have h1 : δ * (Eψ + 1) = ε / 2 := by rw [hδ]; field_simp
      nlinarith
    have hev : ∀ᶠ n in atTop, (1 + 1 / δ) * Dn n < ε / 2 := by
      have h := hDsum.const_mul (1 + 1 / δ)
      rw [mul_zero] at h
      exact h.eventually (gt_mem_nhds (by linarith))
    filter_upwards [hev] with n hn
    have hamem : ∀ p : Fin N × Fin d, MemLp (fun X : Config N d =>
        moll (ns n) (fun z => weakGrad (Ψ ∘ unflat) z p) (flat X)) 2 (Q mu N) := fun p =>
      memLp_two_comp_flat_of_C1T (C1T_moll _ (hg1 p))
    have hbmem := memLp_grad_comp_flat hup hH
    have h1 : ∫ X, Gross.gradPair (mollC (ns n) (Ψ ∘ unflat)) (mollC (ns n) (Ψ ∘ unflat)) X
        ∂(Q mu N) = ∑ p : Fin N × Fin d, ∫ X,
          moll (ns n) (fun z => weakGrad (Ψ ∘ unflat) z p) (flat X) ^ 2 ∂(Q mu N) := by
      rw [← integral_finsetSum _ fun p _ => (hamem p).integrable_sq]
      exact integral_congr_ae (Eventually.of_forall fun X => gradPair_mollC hw (ns n) X)
    have h2 : ∀ p : Fin N × Fin d, ∫ X, moll (ns n) (fun z => weakGrad (Ψ ∘ unflat) z p)
        (flat X) ^ 2 ∂(Q mu N) ≤
        (1 + δ) * ∫ X, weakGrad (Ψ ∘ unflat) (flat X) p ^ 2 ∂(Q mu N) +
          (1 + 1 / δ) * ∫ X, (moll (ns n) (fun z => weakGrad (Ψ ∘ unflat) z p) (flat X) -
            weakGrad (Ψ ∘ unflat) (flat X) p) ^ 2 ∂(Q mu N) := fun p =>
      integral_sq_le_trick (hamem p) (hbmem p) hδpos
    have h3 := Finset.sum_le_sum (fun p (_ : p ∈ (Finset.univ : Finset (Fin N × Fin d))) => h2 p)
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      ← toReal_refEnergy_eq_sum hup hH, ← hEψdef] at h3
    have h4 : ∑ p : Fin N × Fin d, ∫ X, (moll (ns n) (fun z => weakGrad (Ψ ∘ unflat) z p)
        (flat X) - weakGrad (Ψ ∘ unflat) (flat X) p) ^ 2 ∂(Q mu N) = Dn n := by
      rw [hDn]
    rw [h4] at h3
    rw [h1, ← hEψdef]
    nlinarith

/-- **(S3) Bessel inequality for the energy of an `H¹(Q)` function**:
`∑_j Λ_j c_j(Ψ)² ≤ ℰ⁰(Ψ)`. -/
theorem bessel_energy_of_H1 {Cu Cl : ℝ}
    (hup : mu ≤ ENNReal.ofReal Cu • (volume : Measure (Torus d)))
    (hlow : (volume : Measure (Torus d)) ≤ ENNReal.ofReal Cl • mu)
    (hb : IsRefEigenbasis mu e lam) (hC1 : ∀ j, Gross.C1T (eC j))
    (hae : ∀ j, eC j =ᵐ[mu] e j) (hlam0 : lam 0 = 0) {Ψ : Config N d → ℝ}
    (hH : MemH1C (Q mu N) Ψ) :
    Summable (fun j : Fin N → ℕ => Lam lam j * coeff mu e j Ψ ^ 2) ∧
      ∑' j : Fin N → ℕ, Lam lam j * coeff mu e j Ψ ^ 2 ≤ (refEnergy mu Ψ).toReal := by
  have hac : mu ≪ volume := Measure.absolutelyContinuous_of_le_smul hup
  have hca : volume ≪ mu := Measure.absolutelyContinuous_of_le_smul hlow
  have hlam := lam_nonneg_of_ref hb hlam0
  obtain ⟨Φ, hΦC, hΦL, hΦE⟩ := exists_C1_approx hup hlow hH
  have hΨ := memLp_of_H1 hH
  have key : ∀ T : Finset (Fin N → ℕ),
      ∑ j ∈ T, Lam lam j * coeff mu e j Ψ ^ 2 ≤ (refEnergy mu Ψ).toReal := by
    intro T
    have hlim : Tendsto (fun n => ∑ j ∈ T, Lam lam j * coeff mu e j (Φ n) ^ 2) atTop
        (𝓝 (∑ j ∈ T, Lam lam j * coeff mu e j Ψ ^ 2)) :=
      tendsto_finsetSum T fun j _ =>
        ((tendsto_coeff_of_L2 hb (fun n => memLp_two_of_C1C (hΦC n)) hΨ hΦL j).pow 2).const_mul _
    refine le_of_forall_pos_le_add fun ε hε => ?_
    refine le_of_tendsto hlim ?_
    filter_upwards [hΦE ε hε] with n hn
    exact (sum_Lam_coeff_sq_le_of_C1 hac hca hb hC1 hae hlam T (hΦC n)).trans hn
  exact summable_tsum_le_of_sum_le (fun j => mul_nonneg (Lam_nonneg hlam j) (sq_nonneg _)) key

/-- **(P1)** `∫ (S_t Ψ - Ψ)² ≤ t · ℰ⁰(Ψ)` for `Ψ ∈ H¹(Q)`. -/
theorem integral_Sfun_sub_sq_le_of_H1 {Cu Cl : ℝ}
    (hup : mu ≤ ENNReal.ofReal Cu • (volume : Measure (Torus d)))
    (hlow : (volume : Measure (Torus d)) ≤ ENNReal.ofReal Cl • mu)
    (hb : IsRefEigenbasis mu e lam) (hC1 : ∀ j, Gross.C1T (eC j))
    (hae : ∀ j, eC j =ᵐ[mu] e j) (hlam0 : lam 0 = 0) {t : ℝ} (ht : 0 ≤ t)
    {Ψ : Config N d → ℝ} (hH : MemH1C (Q mu N) Ψ) :
    ∫ X, (Sfun hb t Ψ X - Ψ X) ^ 2 ∂(Q mu N) ≤ t * (refEnergy mu Ψ).toReal := by
  obtain ⟨hs, hle⟩ := bessel_energy_of_H1 hup hlow hb hC1 hae hlam0 hH
  exact integral_Sfun_sub_sq_le hb (lam_nonneg_of_ref hb hlam0) ht (memLp_of_H1 hH) hs hle

/-- **(P1, `eLpNorm` form)** `‖Ψ - S_t Ψ‖₂² ≤ t · ℰ⁰(Ψ)` for `Ψ ∈ H¹(Q)`. -/
theorem eLpNorm_sub_Sfun_sq_le_of_H1 {Cu Cl : ℝ}
    (hup : mu ≤ ENNReal.ofReal Cu • (volume : Measure (Torus d)))
    (hlow : (volume : Measure (Torus d)) ≤ ENNReal.ofReal Cl • mu)
    (hb : IsRefEigenbasis mu e lam) (hC1 : ∀ j, Gross.C1T (eC j))
    (hae : ∀ j, eC j =ᵐ[mu] e j) (hlam0 : lam 0 = 0) {t : ℝ} (ht : 0 ≤ t)
    {Ψ : Config N d → ℝ} (hH : MemH1C (Q mu N) Ψ) :
    eLpNorm (fun X => Ψ X - Sfun hb t Ψ X) 2 (Q mu N) ^ 2 ≤
      ENNReal.ofReal (t * (refEnergy mu Ψ).toReal) := by
  obtain ⟨hs, hle⟩ := bessel_energy_of_H1 hup hlow hb hC1 hae hlam0 hH
  exact eLpNorm_sub_Sfun_sq_le hb (lam_nonneg_of_ref hb hlam0) ht (memLp_of_H1 hH) hs hle

/-- **(P3)** `ℰ⁰(F_cut) ≤ ℰ⁰(Ψ)` for `Ψ ∈ H¹(Q)`. -/
theorem refEnergy_Fcut_le_of_H1 {Cu Cl : ℝ}
    (hup : mu ≤ ENNReal.ofReal Cu • (volume : Measure (Torus d)))
    (hlow : (volume : Measure (Torus d)) ≤ ENNReal.ofReal Cl • mu)
    (hb : IsRefEigenbasis mu e lam) (hC1 : ∀ j, Gross.C1T (eC j))
    (hae : ∀ j, eC j =ᵐ[mu] e j) (hlam0 : lam 0 = 0) {t : ℝ} (ht : 0 ≤ t) (L : ℝ)
    {Ψ : Config N d → ℝ} (hH : MemH1C (Q mu N) Ψ) :
    refEnergy mu (Fcut mu e lam t L Ψ) ≤ refEnergy mu Ψ := by
  obtain ⟨hs, hle⟩ := bessel_energy_of_H1 hup hlow hb hC1 hae hlam0 hH
  exact refEnergy_Fcut_le (Measure.absolutelyContinuous_of_le_smul hup)
    (Measure.absolutelyContinuous_of_le_smul hlow) hb hC1 hae (lam_nonneg_of_ref hb hlam0) ht L hs
    hle (refEnergy_ne_top_of_H1 hup hH)

end H1Main

/-! ### The case `μ = ρ m` with `c ≤ ρ ≤ C` (`GoodDens`) -/

section GoodDensCase

variable {N d : ℕ} {e eC : ℕ → Torus d → ℝ} {lam : ℕ → ℝ} {ρ : Torus d → ℝ} {c C : ℝ}
  [IsProbabilityMeasure (densMeasure ρ)]

/-- **(S3)** for the reference measure `ρ m` with `GoodDens ρ c C` (as delivered by `refSetup`). -/
theorem bessel_energy_of_goodDens (hρ : GoodDens ρ c C)
    (hb : IsRefEigenbasis (densMeasure ρ) e lam) (hC1 : ∀ j, Gross.C1T (eC j))
    (hae : ∀ j, eC j =ᵐ[densMeasure ρ] e j) (hlam0 : lam 0 = 0) {Ψ : Config N d → ℝ}
    (hH : MemH1C (Q (densMeasure ρ) N) Ψ) :
    Summable (fun j : Fin N → ℕ => Lam lam j * coeff (densMeasure ρ) e j Ψ ^ 2) ∧
      ∑' j : Fin N → ℕ, Lam lam j * coeff (densMeasure ρ) e j Ψ ^ 2 ≤
        (refEnergy (densMeasure ρ) Ψ).toReal := by
  exact bessel_energy_of_H1 hρ.le_smul hρ.haar_le_smul hb hC1 hae hlam0 hH

/-- **(P1)** for `μ = ρ m`. -/
theorem integral_Sfun_sub_sq_le_of_goodDens (hρ : GoodDens ρ c C)
    (hb : IsRefEigenbasis (densMeasure ρ) e lam) (hC1 : ∀ j, Gross.C1T (eC j))
    (hae : ∀ j, eC j =ᵐ[densMeasure ρ] e j) (hlam0 : lam 0 = 0) {t : ℝ} (ht : 0 ≤ t)
    {Ψ : Config N d → ℝ} (hH : MemH1C (Q (densMeasure ρ) N) Ψ) :
    ∫ X, (Sfun hb t Ψ X - Ψ X) ^ 2 ∂(Q (densMeasure ρ) N) ≤
      t * (refEnergy (densMeasure ρ) Ψ).toReal := by
  exact integral_Sfun_sub_sq_le_of_H1 hρ.le_smul hρ.haar_le_smul hb hC1 hae hlam0 ht hH

/-- **(P3)** for `μ = ρ m`. -/
theorem refEnergy_Fcut_le_of_goodDens (hρ : GoodDens ρ c C)
    (hb : IsRefEigenbasis (densMeasure ρ) e lam) (hC1 : ∀ j, Gross.C1T (eC j))
    (hae : ∀ j, eC j =ᵐ[densMeasure ρ] e j) (hlam0 : lam 0 = 0) {t : ℝ} (ht : 0 ≤ t) (L : ℝ)
    {Ψ : Config N d → ℝ} (hH : MemH1C (Q (densMeasure ρ) N) Ψ) :
    refEnergy (densMeasure ρ) (Fcut (densMeasure ρ) e lam t L Ψ) ≤ refEnergy (densMeasure ρ) Ψ := by
  exact refEnergy_Fcut_le_of_H1 hρ.le_smul hρ.haar_le_smul hb hC1 hae hlam0 ht L hH

end GoodDensCase

end SharpLSI.FL.Spectral

end
