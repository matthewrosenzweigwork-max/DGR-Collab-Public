import FullLabeledLSI.Infra.HypercontrTorus3

/-!
# Eigen-IBP on `(𝕋^d)^N` for tensor eigenfunctions

`Mtensor eC j X = ∏_m eC (j m) (X m)`. For every `F ∈ C¹((𝕋^d)^N)`:
`(∑_m λ_{j_m}) ∫ F · Mtensor j dμ^{⊗N} = ∫ ∇F · ∇(Mtensor j) dμ^{⊗N}` (the classical product gradient).
-/

open MeasureTheory SharpLSI

noncomputable section

namespace SharpLSI.FL.Gross

variable {N d : ℕ}

/-- The tensor product `∏_m eC (j m) (X m)`. -/
def Mtensor (eC : ℕ → Torus d → ℝ) (j : Fin N → ℕ) (X : Config N d) : ℝ := ∏ m, eC (j m) (X m)

lemma C1C_Mtensor {eC : ℕ → Torus d → ℝ} (hC1 : ∀ j, C1T (eC j)) (j : Fin N → ℕ) :
    C1C (Mtensor eC j) :=
  C1C.prod Finset.univ fun m _ => C1C.eval (hC1 (j m)) m

lemma sliceF_Mtensor (eC : ℕ → Torus d → ℝ) (j : Fin N → ℕ) (x : Config N d) (l : Fin N) :
    sliceF (Mtensor eC j) x l =
      fun y => (∏ m ∈ Finset.univ.erase l, eC (j m) (x m)) * eC (j l) y := by
  funext y
  unfold sliceF Mtensor
  rw [← Finset.mul_prod_erase Finset.univ (fun m => eC (j m) (Function.update x l y m))
    (Finset.mem_univ l), Function.update_self, mul_comm]
  congr 1
  refine Finset.prod_congr rfl fun m hm => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hm)]

lemma GammaT_const_mul_right {f g : Torus d → ℝ} (hg : C1T g) (R : ℝ) (y : Torus d) :
    GammaT f (fun y => R * g y) y = R * GammaT f g y := by
  unfold GammaT
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [dT_const_mul hg]; ring

lemma GammaT_slice_Mtensor {eC : ℕ → Torus d → ℝ} (hC1 : ∀ j, C1T (eC j)) (j : Fin N → ℕ)
    (F : Config N d → ℝ) (x : Config N d) (l : Fin N) :
    GammaT (sliceF F x l) (eC (j l)) (x l) * ∏ m ∈ Finset.univ.erase l, eC (j m) (x m) =
      GammaT (sliceF F x l) (sliceF (Mtensor eC j) x l) (x l) := by
  rw [sliceF_Mtensor, GammaT_const_mul_right (hC1 (j l)), mul_comm]

variable {mu : Measure (Torus d)} [IsProbabilityMeasure mu]

theorem torus_eigen_ibp (hac : mu ≪ volume) (hca : volume ≪ mu) {e : ℕ → Torus d → ℝ}
    {lam : ℕ → ℝ} (hb : IsRefEigenbasis mu e lam) {eC : ℕ → Torus d → ℝ}
    (hC1 : ∀ j, C1T (eC j)) (hae : ∀ j, eC j =ᵐ[mu] e j) (j : Fin N → ℕ) {F : Config N d → ℝ}
    (hF : C1C F) :
    (∑ l, lam (j l)) * ∫ X, F X * Mtensor eC j X ∂(Measure.pi fun _ : Fin N => mu) =
      ∫ X, gradPair F (Mtensor eC j) X ∂(Measure.pi fun _ : Fin N => mu) := by
  have hM := C1C_Mtensor hC1 j
  obtain ⟨K1, hK1⟩ := bounded_Gamma_slice hF hM
  have hΓeq : ∀ x l, GammaT (sliceF F x l) (eC (j l)) (x l) *
      ∏ m ∈ Finset.univ.erase l, eC (j m) (x m) =
      GammaT (sliceF F x l) (sliceF (Mtensor eC j) x l) (x l) := fun x l =>
    GammaT_slice_Mtensor hC1 j F x l
  -- measurability and boundedness of the pairing with a single eigenfunction
  have hΓm : ∀ l, Measurable fun x : Config N d => GammaT (sliceF F x l) (eC (j l)) (x l) := by
    intro l
    have : (fun x : Config N d => GammaT (sliceF F x l) (eC (j l)) (x l)) =
        fun x => ∑ k, dT (F ∘ unflat) (l, k) (flat x) * dT (eC (j l)) k (x l) := by
      funext x; unfold GammaT
      exact Finset.sum_congr rfl fun k _ => by rw [dT_sliceF hF x l k]
    rw [this]
    exact Finset.measurable_sum _ fun k _ =>
      ((hF.dT_measurable (l, k)).comp measurable_flat).mul
        (((hC1 (j l)).dT_measurable k).comp (measurable_pi_apply l))
  have hΓb : ∀ l, ∃ K, ∀ x : Config N d, |GammaT (sliceF F x l) (eC (j l)) (x l)| ≤ K := by
    intro l
    choose Kf hKf using fun p => hF.dT_bounded p
    choose Ke hKe using fun k => (hC1 (j l)).dT_bounded k
    refine ⟨∑ k, Kf (l, k) * Ke k, fun x => ?_⟩
    unfold GammaT
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [dT_sliceF hF x l k, abs_mul]
    exact mul_le_mul (hKf (l, k) (flat x)) (hKe k (x l)) (abs_nonneg _)
      ((abs_nonneg _).trans (hKf (l, k) (flat x)))
  have key := Product.eigen_ibp (μ := mu) (N := N) C1T (fun f g => GammaT f g)
    (fun m => eC (j m)) (fun m => lam (j m))
    (fun m => (hC1 (j m)).measurable) (fun m => (hC1 (j m)).bounded)
    (fun m φ hφ => by
      have h := classical_eigen hac hca hb hC1 hae (j m) hφ
      show ∫ y, GammaT φ (eC (j m)) y ∂mu = _
      rw [GammaT_comm φ (eC (j m))]
      exact h)
    F hF.measurable hF.bounded (fun x l => C1T_sliceF hF x l) hΓm hΓb
  have hint : ∀ l, Integrable (fun x : Config N d =>
      GammaT (sliceF F x l) (sliceF (Mtensor eC j) x l) (x l))
      (Measure.pi fun _ : Fin N => mu) := fun l => by
    refine Integrable.of_bound (measurable_Gamma_slice hF hM l).aestronglyMeasurable K1
      (Filter.Eventually.of_forall fun x => ?_)
    simpa [Real.norm_eq_abs] using hK1 x l
  have e1 : ∀ l, ∫ x, GammaT (fun y => F (Function.update x l y)) (eC (j l)) (x l) *
      ∏ m ∈ Finset.univ.erase l, eC (j m) (x m) ∂(Measure.pi fun _ : Fin N => mu) =
      ∫ x, GammaT (sliceF F x l) (sliceF (Mtensor eC j) x l) (x l)
        ∂(Measure.pi fun _ : Fin N => mu) := fun l =>
    integral_congr_ae (Filter.Eventually.of_forall fun x => hΓeq x l)
  have hsum : ∑ l, ∫ x, GammaT (fun y => F (Function.update x l y)) (eC (j l)) (x l) *
      ∏ m ∈ Finset.univ.erase l, eC (j m) (x m) ∂(Measure.pi fun _ : Fin N => mu) =
      ∫ X, gradPair F (Mtensor eC j) X ∂(Measure.pi fun _ : Fin N => mu) := by
    rw [Finset.sum_congr rfl fun l _ => e1 l, ← integral_finsetSum _ fun l _ => hint l]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => sum_slice_Gamma hF hM x)
  exact key.trans hsum

end SharpLSI.FL.Gross

end
