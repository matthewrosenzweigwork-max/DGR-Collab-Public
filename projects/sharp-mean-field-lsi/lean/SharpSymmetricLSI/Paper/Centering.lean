import SharpSymmetricLSI.Paper.MinimizerCompact

/-!
# Section 4.3: centering identities (4.14), (4.15) (Phase 3, lane D; R17)
-/

noncomputable section
open MeasureTheory InformationTheory Filter Real
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

section fubini
variable (hyp : Hyp V W KV KW) (μ : Measure (Torus d)) [IsProbabilityMeasure μ]
include hyp

theorem measurable_convMeas : Measurable (convMeas W μ) :=
  (hyp.continuous_W.measurable.stronglyMeasurable.integral_prod_right (ν := μ)
    (f := fun x y => W x y)).measurable

theorem integral_convMeas : ∫ y, convMeas W μ y ∂μ = interE W μ μ := by
  obtain ⟨BW, hBW⟩ := exists_bound_of_continuous (X := Torus d × Torus d) hyp.continuous_W
  have hint : Integrable (Function.uncurry W) (μ.prod μ) :=
    integrable_of_bdd hyp.continuous_W.measurable fun q => hBW q
  unfold convMeas interE
  exact integral_integral_swap hint

/-- `∫ K(x,y) dμ(y) = 0`. -/
theorem integral_centeredKernel (x : Torus d) : ∫ y, centeredKernel W μ x y ∂μ = 0 := by
  obtain ⟨BW, hBW⟩ := exists_bound_of_continuous (X := Torus d × Torus d) hyp.continuous_W
  have hW : Integrable (fun y => W x y) μ :=
    integrable_of_bdd (hyp.continuous_W.measurable.comp measurable_prodMk_left) fun y => hBW (x, y)
  have hw : Integrable (convMeas W μ) μ :=
    integrable_of_bdd (measurable_convMeas hyp μ) fun y => abs_integral_le_of_bdd fun z => hBW (y, z)
  unfold centeredKernel
  rw [integral_add (f := fun y => W x y - convMeas W μ x - convMeas W μ y)
      (g := fun _ => interE W μ μ) ((hW.sub (integrable_const _)).sub hw) (integrable_const _),
    integral_sub (f := fun y => W x y - convMeas W μ x) (g := convMeas W μ)
      (hW.sub (integrable_const _)) hw,
    integral_sub (f := fun y => W x y) (g := fun _ => convMeas W μ x) hW (integrable_const _),
    integral_convMeas hyp μ]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  unfold convMeas; ring

/-- `T h = ∫ K(·,y) h(y) dμ(y)` on `L²_0(μ)`. -/
theorem Top_eq_integral {h : Torus d → ℝ} (hh : MemL20 μ h) (x : Torus d) :
    Top W μ h x = ∫ y, centeredKernel W μ x y * h y ∂μ := by
  obtain ⟨BW, hBW⟩ := exists_bound_of_continuous (X := Torus d × Torus d) hyp.continuous_W
  have hi : Integrable h μ := hh.1.integrable one_le_two
  have hwb : ∀ y, |convMeas W μ y| ≤ BW := fun y => abs_integral_le_of_bdd fun z => hBW (y, z)
  have bm : ∀ {g : Torus d → ℝ}, Measurable g → ∀ C, (∀ y, |g y| ≤ C) →
      Integrable (fun y => g y * h y) μ := fun {g} hg C hC =>
    Integrable.mono' (hi.abs.const_mul C) (hg.aestronglyMeasurable.mul hi.aestronglyMeasurable)
      (Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_mul]; exact mul_le_mul_of_nonneg_right (hC y) (abs_nonneg _))
  have hWm : Measurable fun y => W x y := hyp.continuous_W.measurable.comp measurable_prodMk_left
  have i1 := bm hWm BW fun y => hBW (x, y)
  have i2 := bm (measurable_convMeas hyp μ) BW hwb
  -- the double integral
  have hdouble : ∫ x', (∫ y, W x' y * h y ∂μ) ∂μ = ∫ y, convMeas W μ y * h y ∂μ := by
    have hint : Integrable (Function.uncurry fun x' y => W x' y * h y) (μ.prod μ) := by
      refine Integrable.mono' ((integrable_const (1 : ℝ)).mul_prod hi.abs |>.const_mul BW) ?_
        (Eventually.of_forall fun q => ?_)
      · exact hyp.continuous_W.measurable.aestronglyMeasurable.mul (hi.aestronglyMeasurable.aemeasurable.comp_snd (μ := μ)).aestronglyMeasurable
      · simp only [Function.uncurry, Real.norm_eq_abs, abs_mul, one_mul]
        exact mul_le_mul_of_nonneg_right (hBW q) (abs_nonneg _)
    rw [integral_integral_swap hint]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only
    rw [integral_mul_const]
    unfold convMeas
    congr 1
    exact integral_congr_ae (Eventually.of_forall fun z => by simp only; rw [hyp.symm])
  unfold Top centeredKernel
  rw [hdouble]
  have e : ∀ y, (W x y - convMeas W μ x - convMeas W μ y + interE W μ μ) * h y =
      W x y * h y - convMeas W μ y * h y + (interE W μ μ - convMeas W μ x) * h y := fun y => by ring
  simp_rw [e]
  rw [integral_add (f := fun y => W x y * h y - convMeas W μ y * h y)
      (g := fun y => (interE W μ μ - convMeas W μ x) * h y) (i1.sub i2) (hi.const_mul _),
    integral_sub (f := fun y => W x y * h y) (g := fun y => convMeas W μ y * h y) i1 i2,
    integral_const_mul, hh.2, mul_zero, add_zero]

end fubini

/-- Relative entropy against a tilted reference measure. -/
theorem klDiv_tilted {α : Type*} [MeasurableSpace α] {ρ ν : Measure α} [IsProbabilityMeasure ρ]
    [IsProbabilityMeasure ν] {f : α → ℝ} (hfm : Measurable f) {B : ℝ} (hfB : ∀ x, |f x| ≤ B)
    (h : klDiv ρ ν ≠ ⊤) :
    klDiv ρ (ν.tilted f) ≠ ⊤ ∧
      (klDiv ρ (ν.tilted f)).toReal = (klDiv ρ ν).toReal - ∫ x, f x ∂ρ + log (∫ x, exp (f x) ∂ν) := by
  obtain ⟨hac, hint⟩ := klDiv_ne_top_iff.mp h
  have hfρ : Integrable f ρ := integrable_of_bdd hfm hfB
  have hfν : Integrable (fun x => exp (f x)) ν := integrable_of_bdd (measurable_exp.comp hfm)
    (C := exp B) fun x => by
      rw [abs_of_pos (exp_pos _)]; exact exp_le_exp.mpr ((le_abs_self _).trans (hfB x))
  haveI : IsProbabilityMeasure (ν.tilted f) := isProbabilityMeasure_tilted hfν
  have hac' : ρ ≪ ν.tilted f := hac.trans (absolutelyContinuous_tilted hfν)
  refine ⟨klDiv_ne_top hac' (integrable_llr_tilted_right hac hfρ hint hfν), ?_⟩
  rw [toReal_klDiv_of_measure_eq hac' (by simp), toReal_klDiv_of_measure_eq hac (by simp),
    integral_llr_tilted_right hac hfρ hfν hint]

section gap
variable (hyp : Hyp V W KV KW)
include hyp

/-- **(4.15)**: `G(ρ) = H(ρ|μ) + J(ρ)`. -/
theorem gap_eq_aux {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
    (ρ : ProbabilityMeasure (Torus d)) :
    gap V W ρ = ((klDiv (ρ : Measure (Torus d)) (μ : Measure (Torus d)) : ENNReal) : EReal) +
      ((Jfun W μ ρ : ℝ) : EReal) := by
  set μm := (μ : Measure (Torus d))
  set ρm := (ρ : Measure (Torus d))
  obtain ⟨BV, hBV⟩ := exists_bound_of_continuous hyp.continuous_V
  obtain ⟨BW, hBW⟩ := exists_bound_of_continuous (X := Torus d × Torus d) hyp.continuous_W
  set Φ : Torus d → ℝ := fun x => V x + convMeas W μm x with hΦ
  have hΦb : ∀ x, |-Φ x| ≤ BV + BW := fun x => by
    rw [abs_neg]; exact abs_potential_le hBV (fun x y => hBW (x, y)) μm x
  have hΦb' : ∀ x, |Φ x| ≤ BV + BW := fun x => by have := hΦb x; rwa [abs_neg] at this
  have hΦm : Measurable Φ := hyp.continuous_V.measurable.add (measurable_convMeas hyp μm)
  -- `μ` is the tilted measure
  have hμt : μm = (haar d).tilted (fun x => -Φ x) := by
    rw [show μm = densMeasure (elDens V W μm) from minimizer_eq_elDensity hyp hμ]
    unfold densMeasure Measure.tilted elDens
    congr 1; funext x
    simp only [hΦ, neg_add']
  have hei : Integrable (fun x => exp (-Φ x)) (haar d) := integrable_of_bdd
    (measurable_exp.comp hΦm.neg) (C := exp (BV + BW)) fun x => by
      rw [abs_of_pos (exp_pos _)]; exact exp_le_exp.mpr ((le_abs_self _).trans (hΦb x))
  have hhaar : haar d = μm.tilted Φ := by
    rw [hμt, tilted_tilted hei]
    have : (fun x => -Φ x) + Φ = 0 := by funext x; simp
    rw [this, tilted_zero]
  set Z := ∫ x, exp (-Φ x) ∂haar d
  have hwμ := integral_convMeas hyp μm
  -- `H(μ|m) = -∫Φ dμ - log Z`
  have hμH : klDiv μm (haar d) ≠ ⊤ := minimizer_klDiv_ne_top hμ
  have hμid := (klDiv_tilted (ρ := μm) (ν := haar d) (f := fun x => -Φ x) hΦm.neg hΦb hμH).2
  rw [← hμt, klDiv_self, ENNReal.toReal_zero] at hμid
  -- `J(ρ)`
  have hJ : Jfun W μm ρm = interE W ρm ρm / 2 - ∫ x, convMeas W μm x ∂ρm + interE W μm μm / 2 := by
    have hWi : ∀ y, Integrable (fun x => W x y) ρm := fun y =>
      integrable_of_bdd (hyp.continuous_W.measurable.comp measurable_prodMk_right) fun x => hBW (x, y)
    have hwb : ∀ y, |convMeas W μm y| ≤ BW := fun y => abs_integral_le_of_bdd fun z => hBW (y, z)
    have hwi : Integrable (convMeas W μm) ρm := integrable_of_bdd (measurable_convMeas hyp μm) hwb
    have inner : ∀ y, ∫ x, centeredKernel W μm x y ∂ρm =
        ∫ x, W x y ∂ρm - ∫ x, convMeas W μm x ∂ρm - convMeas W μm y + interE W μm μm := fun y => by
      unfold centeredKernel
      rw [integral_add (f := fun x => W x y - convMeas W μm x - convMeas W μm y)
          (g := fun _ => interE W μm μm) (((hWi y).sub hwi).sub (integrable_const _))
          (integrable_const _),
        integral_sub (f := fun x => W x y - convMeas W μm x) (g := fun _ => convMeas W μm y)
          ((hWi y).sub hwi) (integrable_const _),
        integral_sub (hWi y) hwi]
      simp
    unfold Jfun interE
    simp_rw [inner]
    have hWy : Integrable (fun y => ∫ x, W x y ∂ρm) ρm :=
      integrable_of_bdd ((StronglyMeasurable.integral_prod_left (μ := ρm) (f := W)
        hyp.continuous_W.measurable.stronglyMeasurable).measurable) fun y => abs_integral_le_of_bdd fun x => hBW (x, y)
    rw [integral_add (f := fun y => ∫ x, W x y ∂ρm - ∫ x, convMeas W μm x ∂ρm - convMeas W μm y)
        (g := fun _ => interE W μm μm) ((hWy.sub (integrable_const _)).sub hwi)
        (integrable_const _),
      integral_sub (f := fun y => ∫ x, W x y ∂ρm - ∫ x, convMeas W μm x ∂ρm)
        (g := convMeas W μm) (hWy.sub (integrable_const _)) hwi,
      integral_sub hWy (integrable_const _)]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    unfold interE; ring
  -- `F* = F(μ)`
  have hFs : Fstar V W = freeEnergy V W μm := hμ.symm
  unfold gap
  rw [hFs, freeEnergy_eq _ hμH]
  by_cases hρH : klDiv ρm (haar d) = ⊤
  · rw [freeEnergy_top _ hρH]
    have hρμ : klDiv ρm μm = ⊤ := by
      by_contra hne
      have := (klDiv_tilted (ρ := ρm) (ν := μm) hΦm hΦb' hne).1
      rw [← hhaar] at this
      exact this hρH
    rw [hρμ]
    simp
  · obtain ⟨hne, hid⟩ := klDiv_tilted (ρ := ρm) (ν := haar d) (f := fun x => -Φ x) hΦm.neg hΦb hρH
    rw [← hμt] at hne hid
    rw [freeEnergy_eq _ hρH, ← EReal.coe_ennreal_toReal hne, ← EReal.coe_sub, ← EReal.coe_add,
      hid, hJ]
    congr 1
    have hΦρ : ∫ x, -Φ x ∂ρm = -(∫ x, V x ∂ρm + ∫ x, convMeas W μm x ∂ρm) := by
      rw [integral_neg, integral_add (integrable_of_bdd hyp.continuous_V.measurable hBV)
        (integrable_of_bdd (measurable_convMeas hyp μm) fun y => abs_integral_le_of_bdd
          fun z => hBW (y, z))]
    have hΦμ : ∫ x, -Φ x ∂μm = -(∫ x, V x ∂μm + ∫ x, convMeas W μm x ∂μm) := by
      rw [integral_neg, integral_add (integrable_of_bdd hyp.continuous_V.measurable hBV)
        (integrable_of_bdd (measurable_convMeas hyp μm) fun y => abs_integral_le_of_bdd
          fun z => hBW (y, z))]
    rw [hΦρ]
    rw [hΦμ, hwμ] at hμid
    unfold energyMF potE
    linarith

end gap

theorem hamiltonian_eq_U (μ : Measure (Torus d)) (N : ℕ) (X : Config N d) :
    hamiltonian V W N X = Ucentered W μ N X + ∑ i, (V (X i) + convMeas W μ (X i)) -
      N * interE W μ μ / 2 := by
  unfold hamiltonian Ucentered centeredKernel
  rcases Nat.eq_zero_or_pos N with h | h
  · subst h; simp
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast h.ne'
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  rw [← Finset.mul_sum]
  field_simp
  ring

section gibbs
variable (hyp : Hyp V W KV KW)
include hyp

theorem measurable_Ucentered (μ : Measure (Torus d)) [IsProbabilityMeasure μ] (N : ℕ) :
    Measurable (Ucentered W μ N) := by
  unfold Ucentered
  refine measurable_const.mul (Finset.measurable_sum _ fun i _ => Finset.measurable_sum _
    fun j _ => ?_)
  have hp : Measurable fun X : Config N d => (X i, X j) := by fun_prop
  have h1 : Measurable fun X : Config N d => W (X i) (X j) := hyp.continuous_W.measurable.comp hp
  have h2 := (measurable_convMeas hyp μ).comp
    (measurable_pi_apply i : Measurable fun X : Config N d => X i)
  have h3 := (measurable_convMeas hyp μ).comp
    (measurable_pi_apply j : Measurable fun X : Config N d => X j)
  unfold centeredKernel
  exact ((h1.sub h2).sub h3).add measurable_const

/-- **(4.15)**: `dP_N = K_N⁻¹ e^{-U_N} dμ^{⊗N}`. -/
theorem gibbs_eq_centered_aux {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ) (N : ℕ) :
    gibbs V W N = (Measure.pi (fun _ : Fin N => (μ : Measure (Torus d)))).withDensity
      (fun X => ENNReal.ofReal (exp (-Ucentered W μ N X) / centeredPartition W μ N)) := by
  set μm := (μ : Measure (Torus d))
  obtain ⟨hqm, hqpos, hq1⟩ := elDensity_props hyp μm
  set q := elDens V W μm
  have hμq : μm = densMeasure q := minimizer_eq_elDensity hyp hμ
  have hpi : Measure.pi (fun _ : Fin N => μm) =
      (volume : Measure (Config N d)).withDensity (fun X => ENNReal.ofReal (∏ i, q (X i))) := by
    rw [hμq]
    exact pi_withDensity_ofReal hqm (fun x => (hqpos x).le) (integrable_of_integral_eq_one' hq1)
  obtain ⟨BV, hBV⟩ := exists_bound_of_continuous hyp.continuous_V
  obtain ⟨BW, hBW⟩ := exists_bound_of_continuous (X := Torus d × Torus d) hyp.continuous_W
  set Φ : Torus d → ℝ := fun x => V x + convMeas W μm x with hΦ
  have hΦm : Measurable Φ := hyp.continuous_V.measurable.add (measurable_convMeas hyp μm)
  set Z := ∫ y, exp (-Φ y) ∂haar d with hZ
  have hei : Integrable (fun x => exp (-Φ x)) (haar d) := integrable_of_bdd
    (measurable_exp.comp hΦm.neg) (C := exp (BV + BW)) fun x => by
      rw [abs_of_pos (exp_pos _)]
      have h : |Φ x| ≤ BV + BW := abs_potential_le hBV (fun x y => hBW (x, y)) μm x
      exact exp_le_exp.mpr (by linarith [neg_le_abs (Φ x)])
  have hZpos : 0 < Z := integral_exp_pos hei
  have hq : ∀ x, q x = exp (-Φ x) / Z := fun x => by
    simp only [q, elDens, hΦ, hZ, neg_add']
  set I := interE W μm μm
  have hprod : ∀ X : Config N d, (∏ i, q (X i)) * exp (-Ucentered W μm N X) =
      exp (-hamiltonian V W N X) * (exp (-(N * I / 2)) / Z ^ N) := fun X => by
    simp_rw [hq]
    rw [Finset.prod_div_distrib, ← exp_sum, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      hamiltonian_eq_U μm N X]
    rw [div_mul_eq_mul_div, ← exp_add, mul_div_assoc', mul_comm (exp _), ← exp_add]
    congr 2
    simp only [Finset.sum_neg_distrib, hΦ]
    ring
  set c := exp (-(N * I / 2)) / Z ^ N
  have hc : 0 < c := by positivity
  have hH := continuous_hamiltonian hyp N
  have hK : centeredPartition W μm N = partitionFn V W N * c := by
    unfold centeredPartition partitionFn
    have hpm : Measurable fun X : Config N d => ∏ i, q (X i) :=
      Finset.measurable_prod _ fun i _ => hqm.comp (measurable_pi_apply i)
    rw [hpi, integral_withDensity_eq_integral_toReal_smul₀
      (f := fun X : Config N d => ENNReal.ofReal (∏ i, q (X i)))
      (ENNReal.measurable_ofReal.comp hpm).aemeasurable
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    simp only [smul_eq_mul, ENNReal.toReal_ofReal (Finset.prod_nonneg fun i _ => (hqpos _).le)]
    simp_rw [hprod]
    rw [integral_mul_const]
  have hZN := partitionFn_pos hyp N
  have hpm' : Measurable fun X : Config N d => ∏ i, q (X i) :=
    Finset.measurable_prod _ fun i _ => hqm.comp (measurable_pi_apply i)
  rw [hpi, ← withDensity_mul _ (f := fun X : Config N d => ENNReal.ofReal (∏ i, q (X i)))
    (g := fun X => ENNReal.ofReal (exp (-Ucentered W μm N X) / centeredPartition W μm N))
    (ENNReal.measurable_ofReal.comp hpm') (ENNReal.measurable_ofReal.comp
      ((measurable_exp.comp (measurable_Ucentered hyp μm N).neg).div_const _))]
  unfold gibbs
  congr 1
  funext X
  simp only [Pi.mul_apply]
  rw [← ENNReal.ofReal_mul (Finset.prod_nonneg fun i _ => (hqpos _).le), hK, ← mul_div_assoc,
    hprod]
  congr 1
  field_simp

end gibbs

end SharpLSI
