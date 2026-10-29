import FullLabeledLSI.Infra.HypercontrTorus5

/-!
# The pure-torus Gross lemma: `GrossHyp` for tensor eigenfunctions, hypercontractivity of spectral
polynomials and the energy formula
-/

open MeasureTheory SharpLSI

noncomputable section

namespace SharpLSI.FL.Gross

variable {N d : ℕ} {mu : Measure (Torus d)} [IsProbabilityMeasure mu]
  {eC : ℕ → Torus d → ℝ} {lam : ℕ → ℝ} {T : Finset (Fin N → ℕ)}

/-- The logarithmic Sobolev field of the instance. -/
theorem torus_lsi_field (hac : mu ≪ volume) {a : ℝ} (ha : 0 < a)
    (hrls : ENNReal.ofReal a ≤ rLS mu) (hC1 : ∀ j, C1T (eC j)) (c : T → ℝ) {ε r : ℝ}
    (hε : 0 < ε) (hr : 1 ≤ r) :
    entR (Measure.pi fun _ : Fin N => mu)
        (fun ω => (uFun (MT eC T) c ω ^ 2 + ε ^ 2) ^ r) ≤
      2 / a * (r ^ 2 * ∫ ω, uFun (MT eC T) c ω ^ 2 * (uFun (MT eC T) c ω ^ 2 + ε ^ 2) ^ (r - 2) *
        GT eC T c ω ∂(Measure.pi fun _ : Fin N => mu)) := by
  set Q := Measure.pi fun _ : Fin N => mu with hQ
  set u := uFun (MT eC T) c with hu
  have hu1 : C1C u := C1C_uFun_MT T hC1 c
  set ψ : ℝ → ℝ := fun s => (s ^ 2 + ε ^ 2) ^ (r / 2) with hψdef
  have hψ : ContDiff ℝ 1 ψ :=
    ContDiff.rpow_const_of_ne ((contDiff_id.pow 2).add contDiff_const)
      (fun s => by positivity)
  have hdψ : ∀ s, deriv ψ s = r * s * (s ^ 2 + ε ^ 2) ^ (r / 2 - 1) := by
    intro s
    have hb : 0 < s ^ 2 + ε ^ 2 := by positivity
    have h1 : HasDerivAt (fun s : ℝ => s ^ 2 + ε ^ 2) (2 * s) s := by
      simpa using (hasDerivAt_pow 2 s).add_const (ε ^ 2)
    have h2 := h1.rpow_const (p := r / 2) (Or.inl hb.ne')
    rw [h2.deriv]; ring
  have hF : C1C (ψ ∘ u) := hu1.comp hψ
  obtain ⟨K, hK⟩ := hu1.bounded
  have hc0 : 0 < (ε ^ 2) ^ (r / 2) := by positivity
  have hFc : ∀ X, (ε ^ 2) ^ (r / 2) ≤ (ψ ∘ u) X := fun X =>
    Real.rpow_le_rpow (by positivity) (by nlinarith [sq_nonneg (u X)]) (by linarith)
  have hFB : ∀ X, (ψ ∘ u) X ≤ (K ^ 2 + ε ^ 2) ^ (r / 2) := fun X => by
    refine Real.rpow_le_rpow (by positivity) ?_ (by linarith)
    have := hK X
    nlinarith [sq_abs (u X), abs_nonneg (u X)]
  have key := torus_lsi hac ha hrls hF hc0 hFc hFB
  have hsq : (fun X => (ψ ∘ u) X ^ 2) = fun ω => (u ω ^ 2 + ε ^ 2) ^ r := by
    funext X
    simp only [Function.comp, hψdef]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    congr 1; push_cast; ring
  rw [hsq] at key
  refine key.trans (le_of_eq ?_)
  congr 1
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
  have h1 := gradPair_comp_comp hu1 hψ hψ X
  have e1 : gradPair (ψ ∘ u) (ψ ∘ u) X = deriv ψ (u X) * deriv ψ (u X) * gradPair u u X := h1
  rw [e1, hdψ]
  have hb : 0 < u X ^ 2 + ε ^ 2 := by positivity
  have h2 : ((u X ^ 2 + ε ^ 2) ^ (r / 2 - 1)) * ((u X ^ 2 + ε ^ 2) ^ (r / 2 - 1)) =
      (u X ^ 2 + ε ^ 2) ^ (r - 2) := by
    rw [← Real.rpow_add hb]; congr 1; ring
  show r * u X * (u X ^ 2 + ε ^ 2) ^ (r / 2 - 1) * (r * u X * (u X ^ 2 + ε ^ 2) ^ (r / 2 - 1)) *
      gradPair u u X = r ^ 2 * (u X ^ 2 * (u X ^ 2 + ε ^ 2) ^ (r - 2) * gradPair u u X)
  rw [← h2]; ring

/-- **The torus instance of `GrossHyp`.** -/
theorem torus_grossHyp (hac : mu ≪ volume) (hca : volume ≪ mu) {e : ℕ → Torus d → ℝ}
    (hb : IsRefEigenbasis mu e lam) (hC1 : ∀ j, C1T (eC j)) (hae : ∀ j, eC j =ᵐ[mu] e j)
    {a : ℝ} (ha : 0 < a) (hrls : ENNReal.ofReal a ≤ rLS mu) (T : Finset (Fin N → ℕ)) :
    GrossHyp (Measure.pi fun _ : Fin N => mu) (MT eC T) (nuT lam T) (GT eC T) a where
  ha := ha
  memLp := fun k n => by
    obtain ⟨K, hK⟩ := (C1C_Mtensor hC1 k.1).bounded
    exact MemLp.of_bound (C1C_Mtensor hC1 k.1).measurable.aestronglyMeasurable K
      (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs, MT] using hK x)
  G_nonneg := fun c ω => gradPair_nonneg_self _ ω
  G_memLp := fun c => by
    have hu1 := C1C_uFun_MT T hC1 c
    obtain ⟨K, hK⟩ := bounded_gradPair hu1 hu1
    exact MemLp.of_bound (measurable_gradPair hu1 hu1).aestronglyMeasurable K
      (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs, GT] using hK x)
  ibp := fun c ψ hψ _ => torus_ibp lam T hac hca hb hC1 hae c hψ
  lsi := fun c ε r hε hr => torus_lsi_field hac ha hrls hC1 c hε hr

end SharpLSI.FL.Gross

end
