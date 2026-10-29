import FullLabeledLSI.Infra.HypercontrTorus6

/-!
# Hypercontractivity of spectral polynomials on `(𝕋^d)^N` and the energy formula

* `gross_torus`: for `F` in the range of the spectral projection (`InSpectralRange e lam L F`) and
  `q ≥ 2`, `‖F‖_{L^q(μ^{⊗N})} ≤ (q-1)^{L/(2a)} ‖F‖_{L²(μ^{⊗N})}`.
* `torus_energy_formula`: `∫ F² = ∑ c_j²` and `ℰ⁰(F) = ∑ (∑_i λ_{j_i}) c_j²` for
  `F = ∑_{j∈T} c_j ∏_i e_{j_i}(X_i)`.
-/

open MeasureTheory SharpLSI

noncomputable section

namespace SharpLSI.FL.Gross

lemma ae_pi_coord {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {p : α → Prop} (h : ∀ᵐ x ∂μ, p x) {N : ℕ} (i : Fin N) :
    ∀ᵐ X ∂(Measure.pi fun _ : Fin N => μ), p (X i) :=
  (measurePreserving_eval (fun _ : Fin N => μ) i).quasiMeasurePreserving.ae h

variable {N d : ℕ} {mu : Measure (Torus d)} [IsProbabilityMeasure mu]
  {e : ℕ → Torus d → ℝ} {eC : ℕ → Torus d → ℝ} {lam : ℕ → ℝ}

/-- Almost everywhere agreement of the spectral polynomial built from `e` and from `eC`. -/
lemma ae_poly_eq {μ : Measure (Torus d)} [IsProbabilityMeasure μ] (hae : ∀ j, eC j =ᵐ[μ] e j)
    (T : Finset (Fin N → ℕ)) (c : (Fin N → ℕ) → ℝ) :
    ∀ᵐ X ∂(Measure.pi fun _ : Fin N => μ),
      ∑ j ∈ T, c j * ∏ i, e (j i) (X i) = uFun (MT eC T) (fun k : T => c k.1) X := by
  have h : ∀ᵐ X ∂(Measure.pi fun _ : Fin N => μ), ∀ j : T, ∀ i : Fin N,
      e (j.1 i) (X i) = eC (j.1 i) (X i) :=
    (ae_all_iff).2 fun j => (ae_all_iff).2 fun i => ae_pi_coord (hae (j.1 i)).symm i
  filter_upwards [h] with X hX
  unfold uFun MT Mtensor
  rw [← Finset.sum_coe_sort T]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  exact Finset.prod_congr rfl fun i _ => hX k i

lemma ae_poly_eq_volume (hca : volume ≪ mu) (hae : ∀ j, eC j =ᵐ[mu] e j)
    (T : Finset (Fin N → ℕ)) (c : (Fin N → ℕ) → ℝ) :
    ∀ᵐ X ∂(volume : Measure (Config N d)),
      ∑ j ∈ T, c j * ∏ i, e (j i) (X i) = uFun (MT eC T) (fun k : T => c k.1) X := by
  have h : ∀ᵐ X ∂(volume : Measure (Config N d)), ∀ j : T, ∀ i : Fin N,
      e (j.1 i) (X i) = eC (j.1 i) (X i) :=
    (ae_all_iff).2 fun j => (ae_all_iff).2 fun i =>
      ae_pi_coord (μ := (volume : Measure (Torus d))) (hca.ae_le (hae (j.1 i)).symm) i
  filter_upwards [h] with X hX
  unfold uFun MT Mtensor
  rw [← Finset.sum_coe_sort T]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  exact Finset.prod_congr rfl fun i _ => hX k i

lemma hortho_MT (hb : IsRefEigenbasis mu e lam) (hae : ∀ j, eC j =ᵐ[mu] e j)
    (T : Finset (Fin N → ℕ)) (k l : T) :
    ∫ X, MT eC T k X * MT eC T l X ∂(Measure.pi fun _ : Fin N => mu) = if k = l then 1 else 0 := by
  have := Spectral.tensor_orthonormal mu eC (classical_orth hb hae) N k.1 l.1
  simp only [Subtype.ext_iff]
  exact this

/-- **Hypercontractivity of spectral polynomials on `(𝕋^d)^N`.** -/
theorem gross_torus (hac : mu ≪ volume) (hca : volume ≪ mu) (hb : IsRefEigenbasis mu e lam)
    (hC1 : ∀ j, C1T (eC j)) (hae : ∀ j, eC j =ᵐ[mu] e j) {a : ℝ} (ha : 0 < a)
    (hrls : ENNReal.ofReal a ≤ rLS mu) {L : ℝ} {F : Config N d → ℝ}
    (hF : InSpectralRange e lam L F) {q : ℝ} (hq : 2 ≤ q) :
    eLpNorm F (ENNReal.ofReal q) (Measure.pi fun _ : Fin N => mu) ≤
      ENNReal.ofReal ((q - 1) ^ (L / (2 * a))) * eLpNorm F 2 (Measure.pi fun _ : Fin N => mu) := by
  obtain ⟨T, c, hT, hFe⟩ := hF
  have hH := torus_grossHyp hac hca hb hC1 hae ha hrls T
  have hFu : F =ᵐ[Measure.pi fun _ : Fin N => mu] uFun (MT eC T) (fun k : T => c k.1) := by
    filter_upwards [ae_poly_eq hae T c] with X hX
    rw [hFe X, hX]
  have key := poly_moment_bound hH (fun k l => hortho_MT hb hae T k l) (fun k : T => c k.1)
    (L := L) (fun k _ => hT k.1 k.2) hq
  rw [eLpNorm_congr_ae hFu, eLpNorm_congr_ae (p := 2) hFu]
  exact key

/-- `ℰ⁰` only depends on the a.e. class (for classes with a `C¹` representative). -/
lemma refEnergy_congr (hac : mu ≪ volume) {F u : Config N d → ℝ} (hu : C1C u)
    (h : ∀ᵐ X ∂(volume : Measure (Config N d)), F X = u X) : refEnergy mu F = refEnergy mu u := by
  have h1 : ∀ᵐ y ∂(volume : Measure (UnitAddTorus (Fin N × Fin d))),
      (u ∘ unflat) y = (F ∘ unflat) y := by
    have := (measurePreserving_unflat N).quasiMeasurePreserving.ae h
    filter_upwards [this] with y hy
    exact hy.symm
  have h2 := (weakGrad_congr_ae ⟨_, isWeakGrad_of_contDiff hu⟩ h1).2
  have h3 : ∀ᵐ X ∂(Measure.pi fun _ : Fin N => mu),
      ∀ p, weakGrad (F ∘ unflat) (flat X) p = weakGrad (u ∘ unflat) (flat X) p :=
    ae_pi_of_ae_flat hac (P := fun y => ∀ p, weakGrad (F ∘ unflat) y p = weakGrad (u ∘ unflat) y p)
      (by filter_upwards [h2] with y hy p; exact congrFun hy p)
  unfold refEnergy
  refine lintegral_congr_ae ?_
  filter_upwards [h3] with X hX
  unfold gradSqC weakGradC
  simp only [hX]

lemma memLp_MT (hC1 : ∀ j, C1T (eC j)) (T : Finset (Fin N → ℕ)) (k : T) (n : ℕ) :
    MemLp (MT eC T k) n (Measure.pi fun _ : Fin N => mu) := by
  obtain ⟨K, hK⟩ := (C1C_Mtensor hC1 k.1).bounded
  exact MemLp.of_bound (C1C_Mtensor hC1 k.1).measurable.aestronglyMeasurable K
    (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs, MT] using hK x)

lemma integral_u_MT (hb : IsRefEigenbasis mu e lam) (hC1 : ∀ j, C1T (eC j))
    (hae : ∀ j, eC j =ᵐ[mu] e j) (T : Finset (Fin N → ℕ)) (c' : T → ℝ) (k : T) :
    ∫ X, uFun (MT eC T) c' X * MT eC T k X ∂(Measure.pi fun _ : Fin N => mu) = c' k := by
  have hM : ∀ k : T, C1C (MT eC T k) := fun k => C1C_Mtensor hC1 k.1
  have hint : ∀ l : T, Integrable (fun X => c' l * (MT eC T l X * MT eC T k X))
      (Measure.pi fun _ : Fin N => mu) := fun l =>
    ((hM l).mul (hM k)).integrable.const_mul (c' l)
  have e1 : ∀ X, uFun (MT eC T) c' X * MT eC T k X =
      ∑ l : T, c' l * (MT eC T l X * MT eC T k X) := fun X => by
    unfold uFun; rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun l _ => by ring
  simp_rw [e1]
  rw [integral_finsetSum _ fun l _ => hint l]
  simp_rw [integral_const_mul, hortho_MT hb hae T]
  simp

/-- **Energy formula** for spectral polynomials: `‖F‖₂² = ∑ c_j²` and
`ℰ⁰(F) = ∑ (∑_i λ_{j_i}) c_j²`. -/
theorem torus_energy_formula (hac : mu ≪ volume) (hca : volume ≪ mu)
    (hb : IsRefEigenbasis mu e lam) (hC1 : ∀ j, C1T (eC j)) (hae : ∀ j, eC j =ᵐ[mu] e j)
    (T : Finset (Fin N → ℕ)) (c : (Fin N → ℕ) → ℝ) {F : Config N d → ℝ}
    (hFe : ∀ X, F X = ∑ j ∈ T, c j * ∏ i, e (j i) (X i)) :
    (∫ X, F X ^ 2 ∂(Measure.pi fun _ : Fin N => mu) = ∑ j ∈ T, c j ^ 2) ∧
      refEnergy mu F = ENNReal.ofReal (∑ j ∈ T, (∑ i, lam (j i)) * c j ^ 2) := by
  set Q := Measure.pi fun _ : Fin N => mu with hQ
  set c' : T → ℝ := fun k => c k.1 with hc'
  set u := uFun (MT eC T) c' with hu
  have hu1 : C1C u := C1C_uFun_MT T hC1 c'
  have hM : ∀ k : T, C1C (MT eC T k) := fun k => C1C_Mtensor hC1 k.1
  have hFu : F =ᵐ[Q] u := by
    filter_upwards [ae_poly_eq hae T c] with X hX
    rw [hFe X, hX]
  have hFuv : ∀ᵐ X ∂(volume : Measure (Config N d)), F X = u X := by
    filter_upwards [ae_poly_eq_volume hca hae T c] with X hX
    rw [hFe X, hX]
  have hMmem : ∀ k : T, ∀ n : ℕ, MemLp (MT eC T k) n Q := fun k n => memLp_MT hC1 T k n
  constructor
  · have h1 : ∫ X, F X ^ 2 ∂Q = ∫ X, u X ^ 2 ∂Q :=
      integral_congr_ae (hFu.mono fun X hX => by simp [hX])
    rw [h1, integral_uFun_sq hMmem (hortho_MT hb hae T) c']
    exact Finset.sum_coe_sort T (fun j => c j ^ 2)
  · rw [refEnergy_congr hac hu1 hFuv, refEnergy_eq_gradPair hac hu1]
    congr 1
    -- `∫ ∇u · ∇u = ∑ ν_k c_k²`
    have hGi : ∀ k : T, Integrable (fun X => gradPair u (MT eC T k) X) Q := fun k => by
      obtain ⟨K, hK⟩ := bounded_gradPair hu1 (hM k)
      exact integrable_of_bdd (measurable_gradPair hu1 (hM k)) hK
    have e1 : ∫ X, gradPair u u X ∂Q = ∑ k : T, c' k * ∫ X, gradPair u (MT eC T k) X ∂Q := by
      calc ∫ X, gradPair u u X ∂Q
          = ∫ X, ∑ k : T, c' k * gradPair u (MT eC T k) X ∂Q :=
            integral_congr_ae (Filter.Eventually.of_forall fun X =>
              gradPair_sum_right (F := u) Finset.univ c' (g := MT eC T) (fun k _ => hM k) X)
        _ = ∑ k : T, ∫ X, c' k * gradPair u (MT eC T k) X ∂Q :=
            integral_finsetSum _ fun k _ => (hGi k).const_mul (c' k)
        _ = _ := Finset.sum_congr rfl fun k _ => integral_const_mul _ _
    have e2 : ∀ k : T, ∫ X, gradPair u (MT eC T k) X ∂Q = nuT lam T k * c' k := fun k => by
      have h : (∑ m, lam (k.1 m)) * ∫ X, u X * MT eC T k X ∂Q =
          ∫ X, gradPair u (MT eC T k) X ∂Q := torus_eigen_ibp hac hca hb hC1 hae k.1 hu1
      rw [integral_u_MT hb hC1 hae T c' k] at h
      exact h.symm
    rw [e1]
    simp_rw [e2]
    rw [← Finset.sum_coe_sort T (fun j => (∑ i, lam (j i)) * c j ^ 2)]
    exact Finset.sum_congr rfl fun k _ => by simp only [nuT, hc']; ring

end SharpLSI.FL.Gross

end
