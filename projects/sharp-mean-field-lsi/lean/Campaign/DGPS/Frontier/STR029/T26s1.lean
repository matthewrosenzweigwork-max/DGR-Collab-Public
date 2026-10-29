import DGPS.Frontier.STR029.T11
import DGPS.Frontier.STR029.T62

/-!
# STR029.26-s1: transport the periodic weak domain to the angular circle

The statement is the saved STR029.26-s1 interface. The proof transfers the measure and smooth
periodic tests explicitly, then identifies the normalization, entropy and Fisher quotient.

## R5 notes

This bridge was not a separate frozen specification unit. Its signature is preserved from the
saved split plan and requires external statement review. The auxiliary weak-derivative implication
uses the periodicity and interval L2 hypotheses recorded in the real-line domain; no equivalence
for arbitrary nonperiodic functions is asserted. Angular Haar is normalized, whereas the interval
L2 measure is unnormalized Lebesgue measure. All derivatives are in the angular variable.
-/

open scoped ContDiff ENNReal
open MeasureTheory Set Filter Topology
open DGPS.Circle.AngularNormalization
open DGPS.Examples.ThreeSpeciesCircle

namespace DGPS.Frontier.STR029

theorem measurePreserving_angSec_volume_STR02926 :
    MeasurePreserving angSec (volume : Measure AngCircle)
      (volume.restrict (Ioc 0 (2 * Real.pi))) := by
  convert
    (measurePreserving_subtype_coe (measurableSet_Ioc (a := (0 : ℝ)) (b := 0 + 2 * Real.pi))).comp
      (AddCircle.measurePreserving_equivIoc (2 * Real.pi) (a := 0)) using 1 <;>
    first | rfl | simp only [zero_add]

theorem memLp_angSec_STR02926 {f : ℝ → ℝ} {p : ℝ≥0∞}
    (hf : MemLp f p (volume.restrict (Ioc 0 (2 * Real.pi)))) :
    MemLp (fun θ => f (angSec θ)) p angHaar := by
  have hv := hf.comp_measurePreserving measurePreserving_angSec_volume_STR02926
  rw [AddCircle.volume_eq_smul_haarAddCircle] at hv
  have hi := hv.smul_measure (c := (ENNReal.ofReal (2 * Real.pi))⁻¹) (by finiteness)
  rwa [smul_smul, ENNReal.inv_mul_cancel (by positivity) ENNReal.ofReal_ne_top, one_smul] at hi

theorem memLp_coe_STR02926 {f : AngCircle → ℝ} {p : ℝ≥0∞} (hf : MemLp f p angHaar) :
    MemLp (fun t : ℝ => f (t : AngCircle)) p (volume.restrict (Ioc 0 (2 * Real.pi))) := by
  have hv : MemLp f p (volume : Measure AngCircle) := by
    rw [AddCircle.volume_eq_smul_haarAddCircle]
    exact hf.smul_measure ENNReal.ofReal_ne_top
  simpa only [zero_add, Function.comp_def] using
    hv.comp_measurePreserving (AddCircle.measurePreserving_mk (2 * Real.pi) 0)

theorem periodicWD_to_angularWD_STR02926 {G d : ℝ → ℝ}
    (hder : IsPeriodicWeakDerivative_STR02933 G d) :
    IsAngularWeakDeriv (fun θ => G (angSec θ)) (fun θ => d (angSec θ)) := by
  refine ⟨memLp_angSec_STR02926 hder.1.2, memLp_angSec_STR02926 hder.2.1.2, ?_⟩
  intro ψ hψ
  have hper : Function.Periodic (fun t : ℝ => ψ (t : AngCircle)) (2 * Real.pi) := by
    intro t
    show ψ ((t + 2 * Real.pi : ℝ) : AngCircle) = ψ (t : AngCircle)
    rw [AddCircle.coe_add_period]
  have hIBP := hder.2.2 (fun t : ℝ => ψ (t : AngCircle)) ⟨hψ, hper⟩
  rw [normInt_eq_STR02935, normInt_eq_STR02935] at hIBP
  have hleft : ∫ θ, G (angSec θ) * angDeriv ψ θ ∂angHaar =
      normInt_STR02904 (fun t => G t * deriv (fun s : ℝ => ψ (s : AngCircle)) t) :=
    integral_angSec_STR02962 (fun t => G t * deriv (fun s : ℝ => ψ (s : AngCircle)) t)
  have hright : ∫ θ, d (angSec θ) * ψ θ ∂angHaar =
      normInt_STR02904 (fun t => d t * ψ (t : AngCircle)) := by
    simpa only [coe_angSec_STR02962, normInt_STR02904] using
      integral_angSec_STR02962 (fun t => d t * ψ (t : AngCircle))
  rw [hleft, hright]
  linarith

theorem angEntropy_angSec_STR02926 (h : ℝ) (G : ℝ → ℝ) :
    angEntropy_STR02901 h (fun θ => G (angSec θ)) = angEnt_STR02911 h G := by
  unfold angEntropy_STR02901 angEnt_STR02911
  simp_rw [qAng_eq_qT_STR02962]
  exact integral_angSec_STR02962
    (fun t => G t ^ 2 * Real.log (G t ^ 2) * qT_STR02904 h t)

theorem angFisher_angSec_STR02926 (h : ℝ) {G d : ℝ → ℝ}
    (hder : IsPeriodicWeakDerivative_STR02933 G d) :
    angFisher_STR02901 h (fun θ => G (angSec θ)) =
      ENNReal.ofReal (4 * normInt_STR02904 (fun t => d t ^ 2 * qT_STR02904 h t)) := by
  have hwd := periodicWD_to_angularWD_STR02926 hder
  have hint : Integrable (fun θ => d (angSec θ) ^ 2 * qAng_STR02901 h θ) angHaar := by
    refine hwd.memLp_deriv.integrable_sq.mul_bdd
      (c := Real.exp (2 * |h|)) (measurable_qAng_STR02901 h).aestronglyMeasurable ?_
    exact ae_of_all _ fun θ => by
      rw [Real.norm_eq_abs, abs_of_pos (qAng_pos_STR02901 h θ)]
      exact referenceDensity_le h _
  have hpt : ∀ θ, ENNReal.ofReal (qAng_STR02901 h θ) * ‖d (angSec θ)‖ₑ ^ 2 =
      ENNReal.ofReal (d (angSec θ) ^ 2 * qAng_STR02901 h θ) := by
    intro θ
    rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _),
      ← ENNReal.ofReal_mul (qAng_pos_STR02901 h θ).le, sq_abs, mul_comm]
  have hnn : 0 ≤ᵐ[angHaar] (fun θ => d (angSec θ) ^ 2 * qAng_STR02901 h θ) :=
    ae_of_all _ fun θ => mul_nonneg (sq_nonneg _) (qAng_pos_STR02901 h θ).le
  rw [angFisher_eq_STR02901 h hwd, lintegral_congr hpt,
    ← ofReal_integral_eq_lintegral_ofReal hint hnn]
  have hint_eq : ∫ θ, d (angSec θ) ^ 2 * qAng_STR02901 h θ ∂angHaar =
      normInt_STR02904 (fun t => d t ^ 2 * qT_STR02904 h t) := by
    simp_rw [qAng_eq_qT_STR02962]
    exact integral_angSec_STR02962 (fun t => d t ^ 2 * qT_STR02904 h t)
  rw [hint_eq, ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]

theorem s1_angDom_to_angular_STR02926 (h : ℝ) (G d : ℝ → ℝ)
    (hG0 : ∀ t, 0 ≤ G t)
    (hder : IsPeriodicWeakDerivative_STR02933 G d)
    (hnorm : normInt_STR02904 (fun t => G t ^ 2 * qT_STR02904 h t) = 1) :
    AngDomain_STR02901 h (fun θ => G (angSec θ)) ∧
      angEntropy_STR02901 h (fun θ => G (angSec θ)) = angEnt_STR02911 h G ∧
      (0 < angEnt_STR02911 h G →
        angQuot_STR02901 h (fun θ => G (angSec θ)) =
          ENNReal.ofReal (angQuot_STR02911 h G d)) := by
  refine ⟨⟨⟨_, periodicWD_to_angularWD_STR02926 hder⟩,
    ae_of_all _ fun θ => hG0 (angSec θ), ?_⟩, angEntropy_angSec_STR02926 h G, ?_⟩
  · calc
      ∫ θ, G (angSec θ) ^ 2 * qAng_STR02901 h θ ∂angHaar =
          normInt_STR02904 (fun t => G t ^ 2 * qT_STR02904 h t) := by
            simp_rw [qAng_eq_qT_STR02962]
            exact integral_angSec_STR02962 (fun t => G t ^ 2 * qT_STR02904 h t)
      _ = 1 := hnorm
  · intro hpos
    rw [angQuot_STR02901, angFisher_angSec_STR02926 h hder, angEntropy_angSec_STR02926]
    exact ofReal_quot_STR02962 _ hpos

end DGPS.Frontier.STR029
