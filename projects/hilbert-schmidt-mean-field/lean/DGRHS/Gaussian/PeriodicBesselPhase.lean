import DGRHS.Gaussian.PeriodicBesselCircle

/-! Actual native AddCircle-to-Circle homeomorphism constructs the phase.
Native primary source Mathlib.Analysis.SpecialFunctions.Complex.Circle,
pinned SHA d63cf63b6eea1b5fe73a314d61f18056d7b3fcaa419b298a28e6a8ebc614214a
(guest source read request 8d43e5ad9af541fc827b42d7e521242f).
No supplied rotation identity. -/
noncomputable section
open MeasureTheory Filter
open scoped ComplexConjugate
namespace DGRHS.Periodic

lemma periodicBessel_circle_linear_pair (a b t : ℝ) :
    (∫ x : UnitAddCircle,Real.exp (t*(a*(fourier 1 x).re+b*(fourier 1 x).im))
      ∂AddCircle.haarAddCircle) =
      periodicBesselI0 (t*‖(a:ℂ)+(b:ℂ)*Complex.I‖) := by
  let z : ℂ := (a:ℂ)+(b:ℂ)*Complex.I
  let r : ℝ := ‖z‖
  by_cases hz : z=0
  · have ha : a=0 := by simpa [z] using congrArg Complex.re hz
    have hb : b=0 := by simpa [z] using congrArg Complex.im hz
    simp [ha,hb,periodicBesselI0]
  · have hr : 0 < r := norm_pos_iff.mpr hz
    let c : Circle := ⟨z/(r:ℂ),by
      apply mem_sphere_zero_iff_norm.mpr
      rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr]
      exact div_self hr.ne'⟩
    obtain ⟨θ,hθ⟩ := (AddCircle.homeomorphCircle (by norm_num : (1:ℝ)≠0)).surjective c
    have hc : fourier 1 θ=z/(r:ℂ) := by
      rw [fourier_one]
      exact congrArg (fun q : Circle => (q:ℂ))
        ((AddCircle.homeomorphCircle_apply (by norm_num : (1:ℝ)≠0) θ).symm.trans hθ)
    have hphase (x : UnitAddCircle) : a*(fourier 1 x).re+b*(fourier 1 x).im =
        r*(fourier 1 (x-θ)).re := by
      have hf : fourier 1 (x-θ)=fourier 1 x*conj (fourier 1 θ) := by
        simp only [fourier_apply,one_zsmul,sub_eq_add_neg,AddCircle.toCircle_add,
          AddCircle.toCircle_neg,Circle.coe_mul,Circle.coe_inv_eq_conj]
      rw [hf,hc]
      have hdiv : z/(r:ℂ)=((a/r:ℝ):ℂ)+((b/r:ℝ):ℂ)*Complex.I := by
        dsimp [z]
        push_cast
        field_simp
        <;> ring
      rw [hdiv]
      simp only [Complex.mul_re,Complex.mul_im,Complex.conj_re,Complex.conj_im,Complex.add_re,
        Complex.add_im,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,
        mul_zero,mul_one,sub_zero,zero_add,add_zero]
      field_simp
      <;> ring
    calc
      _ = ∫ x : UnitAddCircle,Real.exp ((t*r)*(fourier 1 (x-θ)).re)
          ∂AddCircle.haarAddCircle := by
        apply integral_congr_ae
        exact Eventually.of_forall fun x => by
          change Real.exp (t*(a*(fourier 1 x).re+b*(fourier 1 x).im)) =
            Real.exp ((t*r)*(fourier 1 (x-θ)).re)
          rw [hphase]; congr 1; ring
      _ = ∫ x : UnitAddCircle,Real.exp ((t*r)*(fourier 1 x).re)
          ∂AddCircle.haarAddCircle :=
        integral_sub_right_eq_self (fun x : UnitAddCircle => Real.exp ((t*r)*(fourier 1 x).re)) θ
      _ = _ := rfl

end DGRHS.Periodic
#print axioms DGRHS.Periodic.periodicBessel_circle_linear_pair

#check @DGRHS.Periodic.periodicBessel_circle_linear_pair
