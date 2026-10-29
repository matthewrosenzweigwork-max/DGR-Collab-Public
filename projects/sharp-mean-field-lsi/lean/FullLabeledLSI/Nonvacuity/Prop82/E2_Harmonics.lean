import FullLabeledLSI.Nonvacuity.Prop82.E1_Calculus
import SharpSymmetricLSI.Paper.CosineDissipation
import SharpSymmetricLSI.Paper.CosineExpansion
import SharpSymmetricLSI.Paper.CosineTest

/-!
# Lane E, part 2: first and second harmonics, the heat-direction family, force energy

* eigen-relations `D (D h) = -λ h` for `gCos`, `sCos` (λ = a) and `c2`, `gCos * sCos` (λ = 4a);
* the family `rhoS ρ s = ρ + s ρ''`, its smoothness, mass, and its moments;
* closed form of the force energy: `forceEnergy ρ = (a/2) (firstMode ρ - momNum ρ)`.
-/

open MeasureTheory InformationTheory Filter Topology
open scoped ENNReal Real ContDiff

namespace SharpLSI.FL.Prop82.HeatE

open SharpLSI

/-! ### Lifts of the harmonics -/

theorem gCos_lift : gCos ∘ liftT = fun z : Fin 1 → Real => Real.cos (2 * Real.pi * z 0) := by
  funext z
  exact gCos_coe (liftT z) (z 0) rfl

theorem sCos_lift : sCos ∘ liftT = fun z : Fin 1 → Real => Real.sin (2 * Real.pi * z 0) := by
  funext z
  exact expT_im_coe (liftT z) (z 0) rfl

theorem gCos_smooth : IsSmoothT gCos := by
  unfold IsSmoothT
  rw [gCos_lift]
  exact Real.contDiff_cos.comp (contDiff_const.mul (contDiff_apply Real Real 0))

theorem sCos_smooth : IsSmoothT sCos := by
  unfold IsSmoothT
  rw [sCos_lift]
  exact Real.contDiff_sin.comp (contDiff_const.mul (contDiff_apply Real Real 0))

theorem gCos_secT (x : Torus 1) : gCos x = Real.cos (2 * Real.pi * secT x 0) := by
  have := congrFun gCos_lift (secT x)
  simpa [liftT_secT] using this

theorem sCos_secT (x : Torus 1) : sCos x = Real.sin (2 * Real.pi * secT x 0) := by
  have := congrFun sCos_lift (secT x)
  simpa [liftT_secT] using this

theorem gCos_sq_add_sCos_sq (x : Torus 1) : gCos x ^ 2 + sCos x ^ 2 = 1 := by
  rw [gCos_secT, sCos_secT]
  exact Real.cos_sq_add_sin_sq _

theorem fderiv_gCos_lift (z : Fin 1 → Real) :
    fderiv Real (gCos ∘ liftT) z (Pi.single 0 1) = -(2 * Real.pi) * Real.sin (2 * Real.pi * z 0) := by
  rw [gCos_lift]
  have := fderiv_trig_lift 1 0 z
  simp only [mul_one, mul_zero, add_zero] at this
  rw [this]; ring

theorem fderiv_sCos_lift (z : Fin 1 → Real) :
    fderiv Real (sCos ∘ liftT) z (Pi.single 0 1) = 2 * Real.pi * Real.cos (2 * Real.pi * z 0) := by
  rw [sCos_lift]
  have := fderiv_trig_lift 0 1 z
  simp only [mul_one, mul_zero, zero_add, neg_zero] at this
  rw [this]; ring

/-! ### Derivatives of the harmonics -/

theorem dpart_gCos (x : Torus 1) : dpart gCos 0 x = -(2 * Real.pi) * sCos x := by
  unfold dpart
  rw [fderiv_gCos_lift, sCos_secT]

theorem dpart_sCos (x : Torus 1) : dpart sCos 0 x = 2 * Real.pi * gCos x := by
  unfold dpart
  rw [fderiv_sCos_lift, gCos_secT]

theorem dpart2_gCos (x : Torus 1) : dpart (dpart gCos 0) 0 x = -aCos * gCos x := by
  have h : dpart gCos 0 = fun y => -(2 * Real.pi) * sCos y := funext dpart_gCos
  rw [h, dpart_const_mul' _ sCos_smooth, dpart_sCos]
  unfold aCos
  ring

theorem dpart2_sCos (x : Torus 1) : dpart (dpart sCos 0) 0 x = -aCos * sCos x := by
  have h : dpart sCos 0 = fun y => 2 * Real.pi * gCos y := funext dpart_sCos
  rw [h, dpart_const_mul' _ gCos_smooth, dpart_gCos]
  unfold aCos
  ring

theorem c2_eq_mul : c2 = fun y => 2 * (gCos y * gCos y) - 1 := by
  funext y
  rw [c2_apply]
  ring

theorem c2_smooth : IsSmoothT c2 := by
  rw [c2_eq_mul]
  exact smooth_sub (smooth_const_mul 2 (smooth_mul gCos_smooth gCos_smooth)) (smooth_const 1)

theorem gs_smooth : IsSmoothT (fun y => gCos y * sCos y) := smooth_mul gCos_smooth sCos_smooth

theorem dpart_c2 (x : Torus 1) : dpart c2 0 x = -(8 * Real.pi) * (gCos x * sCos x) := by
  rw [c2_eq_mul, dpart_sub' (smooth_const_mul 2 (smooth_mul gCos_smooth gCos_smooth))
    (smooth_const 1), dpart_const_mul' 2 (smooth_mul gCos_smooth gCos_smooth),
    dpart_mul' gCos_smooth gCos_smooth, dpart_const, dpart_gCos]
  ring

theorem dpart_gs (x : Torus 1) :
    dpart (fun y => gCos y * sCos y) 0 x = 2 * Real.pi * c2 x := by
  rw [dpart_mul' gCos_smooth sCos_smooth, dpart_gCos, dpart_sCos, c2_apply]
  have := gCos_sq_add_sCos_sq x
  linear_combination (-2 * Real.pi) * this

theorem dpart2_c2 (x : Torus 1) : dpart (dpart c2 0) 0 x = -(4 * aCos) * c2 x := by
  have h : dpart c2 0 = fun y => -(8 * Real.pi) * (gCos y * sCos y) := funext dpart_c2
  rw [h, dpart_const_mul' _ gs_smooth, dpart_gs]
  unfold aCos
  ring

theorem dpart2_gs (x : Torus 1) :
    dpart (dpart (fun y => gCos y * sCos y) 0) 0 x = -(4 * aCos) * (gCos x * sCos x) := by
  have h : dpart (fun y => gCos y * sCos y) 0 = fun y => 2 * Real.pi * c2 y :=
    funext dpart_gs
  rw [h, dpart_const_mul' _ c2_smooth, dpart_c2]
  unfold aCos
  ring

/-! ### The heat-direction family -/

/-- `ρ_s = ρ + s ρ''` (physical second derivative). -/
noncomputable def rhoS (rho : Torus 1 → Real) (s : Real) : Torus 1 → Real :=
  fun x => rho x + s * dpart (dpart rho 0) 0 x

theorem rhoS_zero (rho : Torus 1 → Real) : rhoS rho 0 = rho := by
  funext x
  simp [rhoS]

theorem smooth_rhoS {rho : Torus 1 → Real} (hrho : IsSmoothT rho) (s : Real) :
    IsSmoothT (rhoS rho s) :=
  smooth_add hrho (smooth_const_mul s (smooth_dpart2 hrho))

theorem integral_rhoS {rho : Torus 1 → Real} (hrho : IsSmoothT rho) (s : Real) :
    ∫ x, rhoS rho s x ∂haar 1 = ∫ x, rho x ∂haar 1 := by
  unfold rhoS
  rw [integral_add (smooth_integrable hrho)
    ((smooth_integrable (smooth_dpart2 hrho)).const_mul s), integral_const_mul,
    integral_dpart2_zero hrho]
  ring

theorem dpart_rhoS {rho : Torus 1 → Real} (hrho : IsSmoothT rho) (s : Real) (x : Torus 1) :
    dpart (rhoS rho s) 0 x = dpart rho 0 x + s * dpart (dpart (dpart rho 0) 0) 0 x := by
  unfold rhoS
  rw [dpart_add' hrho (smooth_const_mul s (smooth_dpart2 hrho)),
    dpart_const_mul' s (smooth_dpart2 hrho)]

/-- Lower bound for `ρ_s` for small `s`: `m / 2`. -/
theorem rhoS_lower {rho : Torus 1 → Real} (hrho : SmoothProbability rho) :
    ∃ m s0 : Real, 0 < m ∧ 0 < s0 ∧ (∀ x, m ≤ rho x) ∧
      ∀ s, |s| ≤ s0 → ∀ x, m / 2 ≤ rhoS rho s x := by
  obtain ⟨m, M, hm, hmrho, hrhoM⟩ :=
    Sec8.exists_pos_bounds (smooth_continuous hrho.smooth) hrho.positive
  obtain ⟨B, hB⟩ := SharpLSI.exists_bound_of_continuous
    (smooth_continuous (smooth_dpart2 hrho.smooth))
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB (Classical.arbitrary _))
  refine ⟨m, m / (2 * (B + 1)), hm, by positivity, hmrho, fun s hs x => ?_⟩
  have h1 : |s * dpart (dpart rho 0) 0 x| ≤ m / 2 := by
    rw [abs_mul]
    calc |s| * |dpart (dpart rho 0) 0 x| ≤ m / (2 * (B + 1)) * B :=
          mul_le_mul hs (hB x) (abs_nonneg _) (by positivity)
      _ ≤ m / 2 := by
          rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
  have := (abs_le.mp h1).1
  unfold rhoS
  linarith [hmrho x]

theorem smoothProbability_rhoS {rho : Torus 1 → Real} (hrho : SmoothProbability rho)
    {m s0 : Real} (hm : 0 < m)
    (hlow : ∀ s, |s| ≤ s0 → ∀ x, m / 2 ≤ rhoS rho s x) {s : Real} (hs : |s| ≤ s0) :
    SmoothProbability (rhoS rho s) where
  smooth := smooth_rhoS hrho.smooth s
  positive := fun x => lt_of_lt_of_le (by positivity) (hlow s hs x)
  mass := by rw [integral_rhoS hrho.smooth, hrho.mass]

/-! ### Moments -/

noncomputable def momC (rho : Torus 1 → Real) : Real := ∫ x, gCos x * rho x ∂haar 1
noncomputable def momS (rho : Torus 1 → Real) : Real := ∫ x, sCos x * rho x ∂haar 1
noncomputable def mom2c (rho : Torus 1 → Real) : Real := ∫ x, c2 x * rho x ∂haar 1
noncomputable def mom2s (rho : Torus 1 → Real) : Real :=
  ∫ x, (gCos x * sCos x) * rho x ∂haar 1

/-- The numerator of `alignedSecondMoment` (the definition in `Assembly.lean` divides this by
`firstMode`; there `momC`, `momS` are `cosMoment`, `sinMoment`, definitionally). -/
noncomputable def momNum (rho : Torus 1 → Real) : Real :=
  ∫ x, rho x * ((momC rho ^ 2 - momS rho ^ 2) * c2 x +
    4 * momC rho * momS rho * gCos x * sCos x) ∂haar 1

theorem smooth_numerand {rho : Torus 1 → Real} (hrho : IsSmoothT rho) (K1 K2 : Real) :
    IsSmoothT (fun x => rho x * (K1 * c2 x + K2 * gCos x * sCos x)) :=
  smooth_mul hrho (smooth_add (smooth_const_mul K1 c2_smooth)
    (smooth_mul (smooth_const_mul K2 gCos_smooth) sCos_smooth))

theorem momNum_eq {rho : Torus 1 → Real} (hrho : IsSmoothT rho) :
    momNum rho = (momC rho ^ 2 - momS rho ^ 2) * mom2c rho + 4 * momC rho * momS rho * mom2s rho := by
  unfold momNum mom2c mom2s
  have e : ∀ x, rho x * ((momC rho ^ 2 - momS rho ^ 2) * c2 x +
      4 * momC rho * momS rho * gCos x * sCos x) =
      (momC rho ^ 2 - momS rho ^ 2) * (c2 x * rho x) +
        4 * momC rho * momS rho * ((gCos x * sCos x) * rho x) := by
    intro x; ring
  simp_rw [e]
  rw [integral_add
    ((smooth_integrable (smooth_mul c2_smooth hrho)).const_mul _)
    ((smooth_integrable (smooth_mul gs_smooth hrho)).const_mul _),
    integral_const_mul, integral_const_mul]

/-- An eigenfunction of `D D` with eigenvalue `-λ` evolves linearly under the heat-direction
family: `∫ h ρ_s = (1 - λ s) ∫ h ρ`. -/
theorem integral_eig_rhoS {h rho : Torus 1 → Real} (hh : IsSmoothT h) (hrho : IsSmoothT rho)
    {lam : Real} (heig : ∀ x, dpart (dpart h 0) 0 x = -lam * h x) (s : Real) :
    ∫ x, h x * rhoS rho s x ∂haar 1 = (1 - lam * s) * ∫ x, h x * rho x ∂haar 1 := by
  have e : ∀ x, h x * rhoS rho s x =
      h x * rho x + s * (h x * dpart (dpart rho 0) 0 x) := by
    intro x; unfold rhoS; ring
  simp_rw [e]
  rw [integral_add (smooth_integrable (smooth_mul hh hrho))
    ((smooth_integrable (smooth_mul hh (smooth_dpart2 hrho))).const_mul s),
    integral_const_mul, integral_mul_dpart2 hh hrho]
  have e2 : ∫ x, dpart (dpart h 0) 0 x * rho x ∂haar 1 = -lam * ∫ x, h x * rho x ∂haar 1 := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [heig x]
    ring
  rw [e2]
  ring

theorem momC_rhoS {rho : Torus 1 → Real} (hrho : IsSmoothT rho) (s : Real) :
    momC (rhoS rho s) = (1 - aCos * s) * momC rho := by
  have := integral_eig_rhoS gCos_smooth hrho dpart2_gCos s
  simpa [momC, dpart2_gCos, neg_mul] using this

theorem momS_rhoS {rho : Torus 1 → Real} (hrho : IsSmoothT rho) (s : Real) :
    momS (rhoS rho s) = (1 - aCos * s) * momS rho := by
  have := integral_eig_rhoS sCos_smooth hrho dpart2_sCos s
  simpa [momS, dpart2_sCos, neg_mul] using this

theorem mom2c_rhoS {rho : Torus 1 → Real} (hrho : IsSmoothT rho) (s : Real) :
    mom2c (rhoS rho s) = (1 - 4 * aCos * s) * mom2c rho := by
  have := integral_eig_rhoS c2_smooth hrho (lam := 4 * aCos) dpart2_c2 s
  simpa [mom2c] using this

theorem mom2s_rhoS {rho : Torus 1 → Real} (hrho : IsSmoothT rho) (s : Real) :
    mom2s (rhoS rho s) = (1 - 4 * aCos * s) * mom2s rho := by
  have := integral_eig_rhoS gs_smooth hrho (lam := 4 * aCos) dpart2_gs s
  simpa [mom2s] using this

theorem firstMode_eq_mom {rho : Torus 1 → Real} (hrho : IsSmoothT rho) :
    firstMode rho = momC rho ^ 2 + momS rho ^ 2 := by
  rw [firstMode_eq (smooth_integrable hrho)]
  rfl

theorem firstMode_rhoS {rho : Torus 1 → Real} (hrho : IsSmoothT rho) (s : Real) :
    firstMode (rhoS rho s) = (1 - aCos * s) ^ 2 * firstMode rho := by
  rw [firstMode_eq_mom (smooth_rhoS hrho s), firstMode_eq_mom hrho, momC_rhoS hrho,
    momS_rhoS hrho]
  ring

theorem momNum_rhoS {rho : Torus 1 → Real} (hrho : IsSmoothT rho) (s : Real) :
    momNum (rhoS rho s) = (1 - aCos * s) ^ 2 * (1 - 4 * aCos * s) * momNum rho := by
  rw [momNum_eq (smooth_rhoS hrho s), momNum_eq hrho, momC_rhoS hrho, momS_rhoS hrho,
    mom2c_rhoS hrho, mom2s_rhoS hrho]
  ring

/-! ### Force energy -/

theorem forceEnergy_closed {rho : Torus 1 → Real} (hrho : SmoothProbability rho) :
    forceEnergy rho = aCos / 2 * (firstMode rho - momNum rho) := by
  have hGc : ContDiff Real 1 (gConv rho ∘ liftT) :=
    (contDiff_gConv_lift hrho.mass).of_le le_top
  have hgrad : ∀ᵐ x ∂haar 1, weakGrad (gConv rho) x 0 =
      2 * Real.pi * (-momC rho * sCos x + momS rho * gCos x) := by
    filter_upwards [weakGrad_ae_eq_of_contDiff hGc] with x hx
    rw [hx]
    simp only
    rw [gConv_lift hrho.mass, fderiv_trig_lift, ← sCos_secT, ← gCos_secT]
    rfl
  have hq := firstMode_eq_mom hrho.smooth
  have hpt : ∀ x, rho x * (2 * Real.pi * (-momC rho * sCos x + momS rho * gCos x)) ^ 2 =
      aCos / 2 * (firstMode rho * rho x -
        rho x * ((momC rho ^ 2 - momS rho ^ 2) * c2 x +
          4 * momC rho * momS rho * gCos x * sCos x)) := by
    intro x
    have hcs := gCos_sq_add_sCos_sq x
    have hc2 := c2_apply x
    rw [hq, hc2]
    unfold aCos
    linear_combination (4 * Real.pi ^ 2 * rho x * momC rho ^ 2) * hcs
  have hi : Integrable (fun x => rho x * ((momC rho ^ 2 - momS rho ^ 2) * c2 x +
      4 * momC rho * momS rho * gCos x * sCos x)) (haar 1) :=
    smooth_integrable (smooth_numerand hrho.smooth _ _)
  unfold forceEnergy
  calc (∫ x, rho x * weakGrad (gConv rho) x 0 ^ 2 ∂haar 1)
      = ∫ x, rho x * (2 * Real.pi * (-momC rho * sCos x + momS rho * gCos x)) ^ 2 ∂haar 1 := by
        refine integral_congr_ae ?_
        filter_upwards [hgrad] with x hx
        rw [hx]
    _ = ∫ x, aCos / 2 * (firstMode rho * rho x -
        rho x * ((momC rho ^ 2 - momS rho ^ 2) * c2 x +
          4 * momC rho * momS rho * gCos x * sCos x)) ∂haar 1 := by
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        exact hpt x
    _ = aCos / 2 * (firstMode rho - momNum rho) := by
        rw [integral_const_mul, integral_sub ((smooth_integrable hrho.smooth).const_mul _) hi,
          integral_const_mul, hrho.mass]
        unfold momNum
        ring

end SharpLSI.FL.Prop82.HeatE
