import FullLabeledLSI.Infra.SpectralCut
import FullLabeledLSI.Infra.SpectralMarkov

/-!
# The cut package without the `L^s` contraction hypothesis

`cut_package` takes the `L^s` contraction `‖S_tΨ‖_s ≤ ‖Ψ‖_s` (P5) as a hypothesis; the Markov
property of the reference heat semigroup (`SpectralMarkov`) discharges it.
-/

open MeasureTheory SharpLSI
open scoped ENNReal

noncomputable section

namespace SharpLSI.FL.Spectral

variable {d N : ℕ} {mu : Measure (Torus d)} [IsProbabilityMeasure mu] {e eC : ℕ → Torus d → ℝ}
  {lam : ℕ → ℝ}

/-- **The cut package** (final form): the `L^s`-contraction hypothesis of `cut_package` is
discharged by `eLpNorm_Sfun_le_rpow'` (the Markov property of the semigroup). -/
theorem cut_package_p5 {Cu Cl : ℝ} (hup : mu ≤ ENNReal.ofReal Cu • (volume : Measure (Torus d)))
    (hlow : (volume : Measure (Torus d)) ≤ ENNReal.ofReal Cl • mu)
    (hb : IsRefEigenbasis mu e lam) (hC1 : ∀ j, Gross.C1T (eC j))
    (hae : ∀ j, eC j =ᵐ[mu] e j) {a : ℝ} (ha : 0 < a) (hrls : ENNReal.ofReal a ≤ rLS mu)
    (hlam0 : lam 0 = 0) (hd : 1 ≤ d)
    (hgrow : ∃ c : ℝ, 0 < c ∧ ∀ j : ℕ, 1 ≤ j → c * (j : ℝ) ^ (2 / (d : ℝ)) ≤ lam j)
    {s Bs t : ℝ} (hs : 2 ≤ s) (ht : 0 < t) (L : ℝ) {Ψ : Config N d → ℝ}
    (hH : MemH1C (Q mu N) Ψ) (hΨs : MemLp Ψ (ENNReal.ofReal s) (Q mu N))
    (hBs : eLpNorm Ψ (ENNReal.ofReal s) (Q mu N) ≤ ENNReal.ofReal Bs) :
    CutPackage mu e lam a s Bs t L Ψ (Sfun hb t Ψ) (Fcut mu e lam t L Ψ) := by
  have hac : mu ≪ volume := Measure.absolutelyContinuous_of_le_smul hup
  have hca : volume ≪ mu := Measure.absolutelyContinuous_of_le_smul hlow
  have hΨ2 : MemLp Ψ 2 (Q mu N) := memLp_of_H1 hH
  exact cut_package hup hlow hb hC1 hae ha hrls hlam0 hd hgrow hs ht L hH hΨs hBs
    (eLpNorm_Sfun_le_rpow' hac hca hb hC1 hae ha hrls hlam0 hs ht.le hΨ2 hΨs).2

end SharpLSI.FL.Spectral

end
