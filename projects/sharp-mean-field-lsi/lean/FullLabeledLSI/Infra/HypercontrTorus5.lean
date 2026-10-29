import FullLabeledLSI.Infra.HypercontrTorus4
import FullLabeledLSI.Infra.HypercontrGross
import FullLabeledLSI.Infra.SpectralTensor

/-!
# The pure-torus instance of Gross's lemma

For `μ` equivalent to Haar measure with a reference eigenbasis `(e, lam)`, `C¹` representatives `eC`,
and `a > 0` with `ofReal a ≤ r_LS(μ)`, the family `M_j = ∏_m eC (j m) (X m)` (`j ∈ T`, `T` finite),
`ν_j = ∑_m lam (j m)`, `G c = |∇ u_c|²` satisfies `GrossHyp` for `P = μ^{⊗N}`.
-/

open MeasureTheory SharpLSI

noncomputable section

namespace SharpLSI.FL.Gross

variable {N d : ℕ}

lemma integrable_of_bdd {α : Type*} [MeasurableSpace α] {P : Measure α} [IsFiniteMeasure P]
    {f : α → ℝ} (hm : Measurable f) {K : ℝ} (hK : ∀ x, |f x| ≤ K) : Integrable f P :=
  Integrable.of_bound hm.aestronglyMeasurable K
    (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hK x)

lemma C1C.mul {F G : Config N d → ℝ} (hF : C1C F) (hG : C1C G) : C1C (fun X => F X * G X) := by
  unfold C1C C1T at *
  exact ContDiff.mul hF hG

lemma C1C.integrable {mu : Measure (Torus d)} [IsProbabilityMeasure mu] {F : Config N d → ℝ}
    (hF : C1C F) : Integrable F (Measure.pi fun _ : Fin N => mu) := by
  obtain ⟨K, hK⟩ := hF.bounded
  exact integrable_of_bdd hF.measurable hK

lemma gradPair_comp_comp {u : Config N d → ℝ} (hu : C1C u) {ψ φ : ℝ → ℝ}
    (hψ : ContDiff ℝ 1 ψ) (hφ : ContDiff ℝ 1 φ) (X : Config N d) :
    gradPair (ψ ∘ u) (φ ∘ u) X = deriv ψ (u X) * deriv φ (u X) * gradPair u u X := by
  unfold gradPair
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  have h1 := dT_comp (f := u ∘ unflat) hu hψ p (flat X)
  have h2 := dT_comp (f := u ∘ unflat) hu hφ p (flat X)
  have e1 : (ψ ∘ u) ∘ unflat = ψ ∘ (u ∘ unflat) := rfl
  have e2 : (φ ∘ u) ∘ unflat = φ ∘ (u ∘ unflat) := rfl
  rw [e1, e2, h1, h2]
  have : (u ∘ unflat) (flat X) = u X := rfl
  rw [this]; ring

lemma gradPair_sum_right {F : Config N d → ℝ} {ι : Type*} (s : Finset ι) {g : ι → Config N d → ℝ}
    (c : ι → ℝ) (hg : ∀ i ∈ s, C1C (g i)) (X : Config N d) :
    gradPair F (fun X => ∑ i ∈ s, c i * g i X) X = ∑ i ∈ s, c i * gradPair F (g i) X := by
  unfold gradPair
  have h : ∀ p, dT ((fun X => ∑ i ∈ s, c i * g i X) ∘ unflat) p (flat X) =
      ∑ i ∈ s, c i * dT (g i ∘ unflat) p (flat X) := fun p =>
    dT_sum s c (g := fun i => g i ∘ unflat) (fun i hi => hg i hi) p (flat X)
  simp_rw [h, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact Finset.sum_congr rfl fun p _ => by ring

section Instance

variable (eC : ℕ → Torus d → ℝ) (lam : ℕ → ℝ) (T : Finset (Fin N → ℕ))

/-- The family of tensor eigenfunctions indexed by `T`. -/
def MT : T → Config N d → ℝ := fun j X => Mtensor eC j.1 X

/-- Their energies `ν_j = ∑_m λ_{j m}`. -/
def nuT : T → ℝ := fun j => ∑ m, lam (j.1 m)

/-- The weights `G c = |∇ u_c|²`. -/
def GT : (T → ℝ) → Config N d → ℝ :=
  fun c X => gradPair (uFun (MT eC T) c) (uFun (MT eC T) c) X

variable {eC}

lemma C1C_uFun_MT (hC1 : ∀ j, C1T (eC j)) (c : T → ℝ) : C1C (uFun (MT eC T) c) :=
  C1C.sum Finset.univ c fun k _ => C1C_Mtensor hC1 k.1

variable {mu : Measure (Torus d)} [IsProbabilityMeasure mu]

/-- The integration by parts identity for the tensor family. -/
theorem torus_ibp (hac : mu ≪ volume) (hca : volume ≪ mu) {e : ℕ → Torus d → ℝ}
    (hb : IsRefEigenbasis mu e lam) (hC1 : ∀ j, C1T (eC j)) (hae : ∀ j, eC j =ᵐ[mu] e j)
    (c : T → ℝ) {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 1 ψ) :
    ∫ X, ψ (uFun (MT eC T) c X) * Afun (MT eC T) (nuT lam T) c X ∂(Measure.pi fun _ : Fin N => mu) =
      ∫ X, deriv ψ (uFun (MT eC T) c X) * GT eC T c X ∂(Measure.pi fun _ : Fin N => mu) := by
  set Q := Measure.pi fun _ : Fin N => mu with hQ
  set u := uFun (MT eC T) c with hu
  have hu1 : C1C u := C1C_uFun_MT T hC1 c
  have hF : C1C (ψ ∘ u) := hu1.comp hψ
  have hM : ∀ k : T, C1C (MT eC T k) := fun k => C1C_Mtensor hC1 k.1
  -- left side
  have hA : ∀ X, Afun (MT eC T) (nuT lam T) c X = ∑ k : T, (nuT lam T k * c k) * MT eC T k X := fun X => rfl
  have hint : ∀ k : T, Integrable (fun X => (ψ ∘ u) X * MT eC T k X) Q := fun k =>
    (hF.mul (hM k)).integrable
  have e1 : ∫ X, ψ (u X) * Afun (MT eC T) (nuT lam T) c X ∂Q =
      ∑ k : T, (nuT lam T k * c k) * ∫ X, (ψ ∘ u) X * MT eC T k X ∂Q := by
    simp_rw [hA, Finset.mul_sum]
    rw [integral_finsetSum _ fun k _ => by
      have := (hint k).const_mul (nuT lam T k * c k)
      refine this.congr (Filter.Eventually.of_forall fun X => ?_)
      simp only [Function.comp]; ring]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
    simp only [Function.comp]; ring
  have e2 : ∀ k : T, nuT lam T k * ∫ X, (ψ ∘ u) X * MT eC T k X ∂Q =
      ∫ X, gradPair (ψ ∘ u) (MT eC T k) X ∂Q := fun k =>
    torus_eigen_ibp hac hca hb hC1 hae k.1 hF
  have hGi : ∀ k : T, Integrable (fun X => gradPair (ψ ∘ u) (MT eC T k) X) Q := fun k => by
    obtain ⟨K, hK⟩ := bounded_gradPair hF (hM k)
    exact integrable_of_bdd (measurable_gradPair hF (hM k)) hK
  have e3 : ∑ k : T, (nuT lam T k * c k) * ∫ X, (ψ ∘ u) X * MT eC T k X ∂Q =
      ∫ X, gradPair (ψ ∘ u) u X ∂Q := by
    calc ∑ k : T, (nuT lam T k * c k) * ∫ X, (ψ ∘ u) X * MT eC T k X ∂Q
        = ∑ k : T, c k * ∫ X, gradPair (ψ ∘ u) (MT eC T k) X ∂Q :=
          Finset.sum_congr rfl fun k _ => by rw [← e2 k]; ring
      _ = ∑ k : T, ∫ X, c k * gradPair (ψ ∘ u) (MT eC T k) X ∂Q :=
          Finset.sum_congr rfl fun k _ => (integral_const_mul _ _).symm
      _ = ∫ X, ∑ k : T, c k * gradPair (ψ ∘ u) (MT eC T k) X ∂Q :=
          (integral_finsetSum _ fun k _ => (hGi k).const_mul (c k)).symm
      _ = ∫ X, gradPair (ψ ∘ u) u X ∂Q :=
          integral_congr_ae (Filter.Eventually.of_forall fun X =>
            (gradPair_sum_right (F := ψ ∘ u) Finset.univ c (g := MT eC T)
              (fun k _ => hM k) X).symm)
  rw [e1, e3]
  refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
  have hid : deriv (fun s : ℝ => s) (u X) = 1 := by simp
  have h3 := gradPair_comp_comp hu1 hψ (contDiff_id) X
  have h4 : gradPair (ψ ∘ u) (id ∘ u) X = gradPair (ψ ∘ u) u X := rfl
  simp only [GT]
  rw [← hu]
  rw [h4] at h3
  rw [h3]
  simp [hid]

end Instance

end SharpLSI.FL.Gross

end
