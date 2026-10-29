/- Adapted locally from the owner-supplied September 27 BecknerOnofri archive.
See D11Imported/PROVENANCE.md and SOURCE_ADAPTATIONS.json for exact member hashes. -/
import DGRHS.Gaussian.D11Imported.ReciprocalGaussian
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.MeanValue

/-! The reciprocal Gaussian integral satisfies its differential equation by
dominated differentiation. The domination stays away from parameter zero;
continuity at zero will supply the Gaussian initial value. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace DGRHS.Gaussian.D11Imported.ReciprocalGaussian

lemma kernel_antitone {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (x : ℝ) :
    kernel b x ≤ kernel a x := by
  unfold kernel
  apply Real.exp_le_exp.mpr
  have hsq : a^2 ≤ b^2 := sq_le_sq₀ ha (ha.trans hab) |>.mpr hab
  have h := div_le_div_of_nonneg_right hsq (sq_nonneg x)
  simp only [div_pow] at *
  linarith

lemma kernel_hasDerivAt (a x : ℝ) :
    HasDerivAt (fun b => kernel b x) ((-2*a/x^2)*kernel a x) a := by
  have h := ((hasDerivAt_const a (-x^2)).sub
    (((hasDerivAt_id a).div_const x).pow 2)).exp
  convert h using 1 <;> dsimp [kernel] <;> ring

lemma kernel_derivative_bound {a b x : ℝ} (ha : 0 < a)
    (hb : b ∈ Ioo (a/2) (2*a)) (hx : 0 < x) :
    ‖(-2*b/x^2)*kernel b x‖ ≤ (4*a/x^2)*kernel (a/2) x := by
  have hb0 : 0 < b := by linarith [hb.1]
  rw [norm_mul, Real.norm_eq_abs, abs_of_neg (div_neg_of_neg_of_pos
    (by nlinarith : -2*b<0) (sq_pos_of_pos hx)),
    Real.norm_eq_abs, abs_of_pos (kernel_pos b x)]
  have hc : -(-2*b/x^2) ≤ 4*a/x^2 := by
    rw [← neg_div]
    apply div_le_div_of_nonneg_right _ (sq_nonneg x)
    nlinarith [hb.2]
  exact mul_le_mul hc (kernel_antitone (by linarith) hb.1.le x)
    (kernel_pos b x).le (by positivity)

lemma mass_hasDerivAt {a : ℝ} (ha : 0 < a) :
    HasDerivAt mass (-2*mass a) a := by
  have hbound : IntegrableOn (fun x : ℝ => (4*a/x^2)*kernel (a/2) x) (Ioi 0) := by
    have he : (fun x : ℝ => (4*a/x^2)*kernel (a/2) x) =
        (fun x : ℝ => 8*((a/2/x^2)*kernel (a/2) x)) := by funext x; ring
    rw [he]
    exact (weighted_integrable (by linarith : 0<a/2)).const_mul 8
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Ioo (a/2) (2*a)) (bound := fun x : ℝ => (4*a/x^2)*kernel (a/2) x)
    (F := kernel) (F' := fun b x => (-2*b/x^2)*kernel b x)
    (μ := volume.restrict (Ioi (0:ℝ))) (x₀ := a)
    (isOpen_Ioo.mem_nhds (by constructor <;> linarith))
    (Eventually.of_forall (fun b => (kernel_measurable b).aestronglyMeasurable))
    (kernel_integrable a)
    (by unfold kernel; exact Measurable.aestronglyMeasurable (by fun_prop))
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx b hb
      exact kernel_derivative_bound ha hb hx)
    hbound
    (ae_of_all _ (fun x b _ => kernel_hasDerivAt b x))
  have he : (∫ x in Ioi (0:ℝ), (-2*a/x^2)*kernel a x) = -2*mass a := by
    calc
      _ = ∫ x in Ioi (0:ℝ), (-2)*((a/x^2)*kernel a x) := by
        apply integral_congr_ae
        exact ae_of_all _ (fun x => by ring)
      _ = -2*mass a := by rw [integral_const_mul, weighted_integral ha]
  rw [he] at h
  exact h.2

lemma mass_continuous : Continuous mass := by
  apply continuous_of_dominated (F := kernel) (μ := volume.restrict (Ioi (0:ℝ)))
    (bound := fun x : ℝ => Real.exp (-x^2))
  · exact fun a => (kernel_measurable a).aestronglyMeasurable
  · exact fun a => ae_of_all _ (fun x => by
      rw [Real.norm_eq_abs, abs_of_pos (kernel_pos a x)]
      exact kernel_le_gaussian a x)
  · have hg : Integrable (fun x : ℝ => Real.exp (-x^2)) := by
      simpa using integrable_exp_neg_mul_sq (by norm_num : (0:ℝ)<1)
    exact hg.integrableOn
  · exact ae_of_all _ (fun x => by unfold kernel; fun_prop)

lemma mass_zero : mass 0 = Real.sqrt Real.pi/2 := by
  simpa [mass, kernel] using integral_gaussian_Ioi (1:ℝ)

lemma mass_formula {a : ℝ} (ha : 0 ≤ a) :
    mass a = Real.sqrt Real.pi/2 * Real.exp (-2*a) := by
  let f : ℝ → ℝ := fun a => Real.exp (2*a)*mass a
  have hd (b : ℝ) (hb : b ∈ Ioi (0:ℝ)) : HasDerivAt f 0 b := by
    have h := (((hasDerivAt_id b).const_mul 2).exp).mul (mass_hasDerivAt hb)
    convert h using 1 <;> first | rfl | ring
  have hc : Continuous f := (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul mass_continuous
  have he : EqOn f (fun _ => f 1) (Ioi 0) := by
    intro b hb
    apply isOpen_Ioi.is_const_of_deriv_eq_zero (convex_Ioi (0:ℝ)).isPreconnected
      (fun x hx => (hd x hx).differentiableAt.differentiableWithinAt)
      (fun x hx => (hd x hx).deriv) hb (by norm_num : (1:ℝ) ∈ Ioi 0)
  have he' := he.closure hc continuous_const
  rw [closure_Ioi] at he'
  have ha' := he' ha
  have h0 := he' (show (0:ℝ) ∈ Ici 0 by simp)
  have heq : Real.exp (2*a)*mass a = Real.sqrt Real.pi/2 := by
    calc
      _ = f 0 := ha'.trans h0.symm
      _ = Real.sqrt Real.pi/2 := by simp [f, mass_zero]
  have heinv : Real.exp (-2*a)*Real.exp (2*a) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  calc
    mass a = Real.exp (-2*a)*(Real.exp (2*a)*mass a) := by rw [← mul_assoc, heinv, one_mul]
    _ = Real.sqrt Real.pi/2 * Real.exp (-2*a) := by rw [heq, mul_comm]

#print axioms mass_formula
end DGRHS.Gaussian.D11Imported.ReciprocalGaussian
