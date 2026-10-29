import DGPS.Frontier.STR029.T26s1

/-!
# STR029.26-s2: transport the angular weak domain to periodic functions

The statement is the saved STR029.26-s2 interface. Smooth periodic tests descend to the circle,
and coercion to the circle gives periodic representatives of the function and weak derivative.

## R5 notes

This bridge was not a separate frozen specification unit. Its signature is preserved from the
saved split plan and requires external statement review. The angular function is replaced by its
pointwise maximum with zero before pulling back. The domain's almost-everywhere nonnegativity
makes this an almost-everywhere change, so the weak derivative, normalization, entropy and Fisher
information are preserved. No classical differentiability or pointwise nonnegativity is assumed
of the original angular representative.
-/

open scoped ContDiff ENNReal
open MeasureTheory Set Filter Topology
open DGPS.Circle.AngularNormalization

namespace DGPS.Frontier.STR029

theorem angularWD_to_periodicWD_STR02926 {g D : AngCircle → ℝ}
    (hder : IsAngularWeakDeriv g D) :
    IsPeriodicWeakDerivative_STR02933 (fun t : ℝ => g (t : AngCircle))
      (fun t : ℝ => D (t : AngCircle)) := by
  refine ⟨⟨?_, memLp_coe_STR02926 hder.memLp⟩,
    ⟨?_, memLp_coe_STR02926 hder.memLp_deriv⟩, ?_⟩
  · intro t
    show g ((t + 2 * Real.pi : ℝ) : AngCircle) = g (t : AngCircle)
    rw [AddCircle.coe_add_period]
  · intro t
    show D ((t + 2 * Real.pi : ℝ) : AngCircle) = D (t : AngCircle)
    rw [AddCircle.coe_add_period]
  · intro φ hφ
    let ψ : AngCircle → ℝ := hφ.2.lift
    have hlift : (fun t : ℝ => ψ (t : AngCircle)) = φ :=
      funext fun t => hφ.2.lift_coe t
    have hψ : IsSmoothAngular ψ := by
      change ContDiff ℝ ∞ (fun t : ℝ => ψ (t : AngCircle))
      rw [hlift]
      exact hφ.1
    have hsec : ∀ θ, φ (angSec θ) = ψ θ := by
      intro θ
      calc
        φ (angSec θ) = ψ ((angSec θ : ℝ) : AngCircle) := (hφ.2.lift_coe _).symm
        _ = ψ θ := by rw [coe_angSec_STR02962]
    have hderiv : ∀ θ, angDeriv ψ θ = deriv φ (angSec θ) := by
      intro θ
      unfold angDeriv
      rw [hlift]
    have hleft : ∫ θ, g θ * angDeriv ψ θ ∂angHaar =
        normInt_STR02904 (fun t : ℝ => g (t : AngCircle) * deriv φ t) := by
      simp_rw [hderiv]
      simpa only [coe_angSec_STR02962, normInt_STR02904] using
        integral_angSec_STR02962 (fun t : ℝ => g (t : AngCircle) * deriv φ t)
    have hright : ∫ θ, D θ * ψ θ ∂angHaar =
        normInt_STR02904 (fun t : ℝ => D (t : AngCircle) * φ t) := by
      simpa only [coe_angSec_STR02962, hsec, normInt_STR02904] using
        integral_angSec_STR02962 (fun t : ℝ => D (t : AngCircle) * φ t)
    have hIBP := hder.ibp ψ hψ
    rw [hleft, hright] at hIBP
    rw [normInt_eq_STR02935, normInt_eq_STR02935]
    linarith

theorem s2_angular_to_angDom_STR02926 (h : ℝ) (g : AngCircle → ℝ)
    (hg : AngDomain_STR02901 h g) (hpos : 0 < angEntropy_STR02901 h g) :
    ∃ G d : ℝ → ℝ, angDom_STR02911 h G d ∧
      ENNReal.ofReal (angQuot_STR02911 h G d) = angQuot_STR02901 h g := by
  obtain ⟨D, hD⟩ := hg.1
  let g0 : AngCircle → ℝ := fun θ => max (g θ) 0
  have hgg0 : g =ᵐ[angHaar] g0 := by
    filter_upwards [hg.2.1] with θ hθ
    exact (max_eq_left hθ).symm
  have hD0 := isAngularWeakDeriv_congr_STR02962 hgg0 hD
  let G : ℝ → ℝ := fun t => g0 (t : AngCircle)
  let d : ℝ → ℝ := fun t => D (t : AngCircle)
  have hder : IsPeriodicWeakDerivative_STR02933 G d := angularWD_to_periodicWD_STR02926 hD0
  have hG0 : ∀ t, 0 ≤ G t := fun t => le_max_right _ _
  have hGsec : (fun θ => G (angSec θ)) = g0 := by
    funext θ
    exact congrArg g0 (coe_angSec_STR02962 θ)
  have hnorm : normInt_STR02904 (fun t => G t ^ 2 * qT_STR02904 h t) = 1 := by
    have htransfer : ∫ θ, G (angSec θ) ^ 2 * qAng_STR02901 h θ ∂angHaar =
        normInt_STR02904 (fun t => G t ^ 2 * qT_STR02904 h t) := by
      simp_rw [qAng_eq_qT_STR02962]
      exact integral_angSec_STR02962 (fun t => G t ^ 2 * qT_STR02904 h t)
    rw [← htransfer]
    calc
      ∫ θ, G (angSec θ) ^ 2 * qAng_STR02901 h θ ∂angHaar =
          ∫ θ, g θ ^ 2 * qAng_STR02901 h θ ∂angHaar := by
            refine integral_congr_ae ?_
            filter_upwards [hgg0] with θ hθ
            rw [congrFun hGsec θ, ← hθ]
      _ = 1 := hg.2.2
  have hent : angEnt_STR02911 h G = angEntropy_STR02901 h g := by
    rw [← angEntropy_angSec_STR02926, hGsec]
    exact (angEntropy_congr_STR02962 h hgg0).symm
  have hGpos : 0 < angEnt_STR02911 h G := by rw [hent]; exact hpos
  refine ⟨G, d, ⟨hG0, hder, hnorm, hGpos⟩, ?_⟩
  rw [← (s1_angDom_to_angular_STR02926 h G d hG0 hder hnorm).2.2 hGpos, hGsec]
  unfold angQuot_STR02901
  rw [← angFisher_congr_STR02962 h hgg0, ← angEntropy_congr_STR02962 h hgg0]

end DGPS.Frontier.STR029
