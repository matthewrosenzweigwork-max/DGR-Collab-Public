import DGPS.Frontier.STR029.T24
import DGPS.Frontier.STR029.T63

/-!
# STR029.26-s4: an optimizer's scaled chart point is a reduced root

The full Euler equation from STR029.62 and the value equation from STR029.63
annihilate the three components computed in STR029.24.

## R5 notes

This worker-authored bridge preserves the saved STR029.26 split statement. It is
not a frozen specification and remains subject to the external statement review.
The rate is the physical quotient divided by the angular normalization, minus one.
-/

open scoped ContDiff
open Filter Topology
open DGPS.Analysis.PeriodicHolder
open MeasureTheory Set
open DGPS.Circle.AngularNormalization
open scoped ENNReal
open DGPS DGPS.Examples.ThreeSpeciesCircle

namespace DGPS.Frontier.STR029

theorem s4_kfun_zero_STR02926
    {U : Set Par_STR02916} {V : Set E_STR02969} {ψ : Par_STR02916 → E_STR02969}
    {O : Set (ℝ × (Fin 3 → ℝ))} {E : ℝ × (Fin 3 → ℝ) → ℝ}
    (hU : IsOpen U) (hψ : ContDiffOn ℝ ∞ ψ U) (hψV : ∀ p ∈ U, ψ p ∈ V)
    (hgr : ∀ p ∈ U, ∀ w ∈ V, Rpar_STR02916 p w = 0 ↔ w = ψ p)
    (hO : IsOpen O) (hE : ContDiffOn ℝ ∞ E O)
    (hEf : ∀ (h : ℝ) (z : Fin 3 → ℝ), (h, z) ∈ O → h ≠ 0 →
      E (h, z) = Fred_STR02956 ψ (h * z 0, h * z 1) (h, h ^ 2 * z 2) / h ^ 4)
    (h : ℝ) (hh : h ≠ 0) (z : Fin 3 → ℝ) (hz : (h, z) ∈ O)
    (hzU : ptPar_STR02923 h z ∈ U)
    (ρ : AbsoluteDensity 1) (hpos : 0 < ordinaryEntropy h ρ)
    (hopt : ∀ ρ' : AbsoluteDensity 1, 0 < ordinaryEntropy h ρ' →
      ordinaryFisher h ρ / (2 * ordinaryEntropy h ρ) ≤
        ordinaryFisher h ρ' / (2 * ordinaryEntropy h ρ'))
    (a b : ℝ) (w : ℝ → ℝ)
    (hae : ∀ᵐ θ ∂angHaar, ρ.density (angEquiv.symm θ) = rhoT_STR02901 h (uT_STR02901 a b w) (angSec θ))
    (hC2 : IsC2Alpha_STR02901 (1 / 2) w) (hInE : InE_STR02901 w)
    (wE : E_STR02969) (hwE : (wE : PeriodicC2_STR02969).val = w)
    (hwEψ : wE = ψ (a, b, h, rateSTR02963 h ρ))
    (hzdef : z = ![a / h, b / h, rateSTR02963 h ρ / h ^ 2]) :
    Kfun_STR02923 E (h, z) = 0 := by
  have ha : h * z 0 = a := by
    rw [hzdef]
    dsimp
    field_simp [hh]
  have hb : h * z 1 = b := by
    rw [hzdef]
    dsimp
    field_simp [hh]
  have hr : h ^ 2 * z 2 = rateSTR02963 h ρ := by
    rw [hzdef]
    dsimp
    field_simp [hh]
  have hchart : chartU_STR02924 ψ h z = uT_STR02901 a b w := by
    unfold chartU_STR02924
    rw [ha, hb, hr, ← hwEψ, hwE]
  obtain ⟨-, hgrad, -⟩ :=
    str029_62_global_optimizer_positive_chart_fully_critical
      h ρ hpos hopt a b w hC2 hInE hae _ rfl
  have hgrad' : ∀ t, gradG_STR02950 h (rateSTR02963 h ρ) (uT_STR02901 a b w) t = 0 := by
    rw [rate_eq_STR02963]
    exact hgrad
  have hJ := jchart_zero_STR02963 h ρ hpos a b w hC2 hae
  obtain ⟨k0, k1, k2⟩ := kfun_STR02924 hU hψ hψV hgr hO hE hEf h hh z hz hzU
  rw [hr, hchart] at k0 k1 k2
  funext i
  fin_cases i
  · simpa [hgrad', meanT_STR02901] using k0
  · simpa [hgrad', meanT_STR02901] using k1
  · simpa [hJ] using k2

end DGPS.Frontier.STR029
