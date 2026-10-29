import DGPS.Lipschitz.MeanFieldEnergy
import DGPS.Lipschitz.WeakChainRule
import DGPS.Basic.SquareRootHeatRecovery

/-!
# Free energy dissipation: regularised entropy identity (LIP030, sub-lemmas)

* `entReg δ`: the `C²` extension to `ℝ` of `r ↦ (r+δ) log (r+δ)` (`r ≥ 0`), with
  `deriv (deriv (entReg δ)) = entReg2 δ`, `entReg2 δ r = 1/(r+δ)` for `r ≥ 0`.
* `regularised_free_energy_identity`: for the global flow, with the flux `J = A + K` of
  `exists_setting`, the regularised entropy chain rule and the two potential-energy
  identities (all against the same flux).
* `DissipationSlice` and the `δ → 0` slice lemmas: for fixed time, with `J = A + ρ a`, the
  pointwise identity, monotone/dominated convergence in `δ`, and `√ρ ∈ H¹` with
  `‖2∇√ρ + √ρ a‖² = ‖J‖²/ρ` whenever `∫ ‖J‖²/ρ < ∞`.
-/

open MeasureTheory Set Filter Topology
open scoped Real RealInnerProductSpace ENNReal

namespace DGPS.Lipschitz

theorem glue_hasDerivAt (p q p' q' : ℝ → ℝ) (hp : ∀ r, 0 ≤ r → HasDerivAt p (p' r) r)
    (hq : ∀ r, r ≤ 0 → HasDerivAt q (q' r) r) (h0 : p 0 = q 0) (h0' : p' 0 = q' 0) (r : ℝ) :
    HasDerivAt (fun r => if 0 ≤ r then p r else q r) (if 0 ≤ r then p' r else q' r) r := by
  rcases lt_trichotomy r 0 with hr | hr | hr
  · have : (fun r => if 0 ≤ r then p r else q r) =ᶠ[nhds r] q := by
      filter_upwards [Iio_mem_nhds hr] with x hx
      simp [not_le.mpr (show x < 0 from hx)]
    simpa [not_le.mpr hr] using (hq r hr.le).congr_of_eventuallyEq this
  · subst hr
    have h1 : HasDerivWithinAt (fun r => if 0 ≤ r then p r else q r) (p' 0) (Ici 0) 0 := by
      refine ((hp 0 le_rfl).hasDerivWithinAt).congr (fun x hx => ?_) (by simp)
      simp [show 0 ≤ x from hx]
    have h2 : HasDerivWithinAt (fun r => if 0 ≤ r then p r else q r) (p' 0) (Iic 0) 0 := by
      rw [h0']
      refine ((hq 0 le_rfl).hasDerivWithinAt).congr (fun x hx => ?_) (by simp [h0])
      by_cases hx0 : 0 ≤ x
      · have : x = 0 := le_antisymm hx hx0
        subst this; simp [h0]
      · simp [hx0]
    have := h1.union h2
    rw [Ici_union_Iic, hasDerivWithinAt_univ] at this
    simpa using this
  · have : (fun r => if 0 ≤ r then p r else q r) =ᶠ[nhds r] p := by
      filter_upwards [Ioi_mem_nhds hr] with x hx
      simp [show 0 ≤ x from hx.le]
    simpa [hr.le] using (hp r hr.le).congr_of_eventuallyEq this

/-- Second-order regularisation of `(r+δ) log (r+δ)`. -/
noncomputable def entReg (δ : ℝ) (r : ℝ) : ℝ :=
  if 0 ≤ r then (r + δ) * Real.log (r + δ)
  else δ * Real.log δ + (Real.log δ + 1) * r + r ^ 2 / (2 * δ)

noncomputable def entReg1 (δ : ℝ) (r : ℝ) : ℝ :=
  if 0 ≤ r then Real.log (r + δ) + 1 else Real.log δ + 1 + r / δ

noncomputable def entReg2 (δ : ℝ) (r : ℝ) : ℝ :=
  if 0 ≤ r then (r + δ)⁻¹ else δ⁻¹

theorem hasDerivAt_entReg {δ : ℝ} (hδ : 0 < δ) (r : ℝ) :
    HasDerivAt (entReg δ) (entReg1 δ r) r := by
  have := glue_hasDerivAt (fun r => (r + δ) * Real.log (r + δ))
    (fun r => δ * Real.log δ + (Real.log δ + 1) * r + r ^ 2 / (2 * δ))
    (fun r => Real.log (r + δ) + 1) (fun r => Real.log δ + 1 + r / δ)
    (fun r hr => by
      have hpos : r + δ ≠ 0 := by linarith
      have h1 : HasDerivAt (fun r => r + δ) 1 r := (hasDerivAt_id r).add_const δ
      have := h1.mul (h1.log hpos)
      convert this using 1
      field_simp)
    (fun r _ => by
      have := (((hasDerivAt_id r).const_mul (Real.log δ + 1)).const_add (δ * Real.log δ)).add
        (((hasDerivAt_id r).pow 2).div_const (2 * δ))
      convert this using 1
      · funext x; simp [Pi.add_apply]
      · simp; field_simp)
    (by simp) (by simp) r
  exact this

theorem hasDerivAt_entReg1 {δ : ℝ} (hδ : 0 < δ) (r : ℝ) :
    HasDerivAt (entReg1 δ) (entReg2 δ r) r := by
  have := glue_hasDerivAt (fun r => Real.log (r + δ) + 1)
    (fun r => Real.log δ + 1 + r / δ)
    (fun r => (r + δ)⁻¹) (fun _ => δ⁻¹)
    (fun r hr => by
      have hpos : r + δ ≠ 0 := by linarith
      have h1 : HasDerivAt (fun r => r + δ) 1 r := (hasDerivAt_id r).add_const δ
      have := (h1.log hpos).add_const 1
      convert this using 1
      simp)
    (fun r _ => by
      have := ((hasDerivAt_id r).div_const δ).const_add (Real.log δ + 1)
      simpa using this)
    (by simp) (by simp) r
  exact this

theorem continuous_entReg2 {δ : ℝ} (hδ : 0 < δ) : Continuous (entReg2 δ) := by
  have : ∀ r, HasDerivAt (entReg1 δ) (entReg2 δ r) r := hasDerivAt_entReg1 hδ
  unfold entReg2
  refine continuous_if_le continuous_const continuous_id ?_ ?_ ?_
  · exact (continuousOn_of_forall_continuousAt fun r hr => by
      have : r + δ ≠ 0 := by have : (0:ℝ) ≤ r := hr; linarith
      exact (continuousAt_id.add continuousAt_const).inv₀ this)
  · exact continuousOn_const
  · intro r hr; simp [hr]

theorem contDiff_entReg {δ : ℝ} (hδ : 0 < δ) : ContDiff ℝ 2 (entReg δ) := by
  have hd : deriv (entReg δ) = entReg1 δ := funext fun r => (hasDerivAt_entReg hδ r).deriv
  have hd1 : deriv (entReg1 δ) = entReg2 δ := funext fun r => (hasDerivAt_entReg1 hδ r).deriv
  rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl, contDiff_succ_iff_deriv]
  refine ⟨fun r => (hasDerivAt_entReg hδ r).differentiableAt, by simp, ?_⟩
  rw [hd, show (1 : WithTop ℕ∞) = 0 + 1 from rfl, contDiff_succ_iff_deriv]
  refine ⟨fun r => (hasDerivAt_entReg1 hδ r).differentiableAt, by simp, ?_⟩
  rw [hd1]
  exact contDiff_zero.mpr (continuous_entReg2 hδ)

theorem deriv_deriv_entReg {δ : ℝ} (hδ : 0 < δ) : deriv (deriv (entReg δ)) = entReg2 δ := by
  have hd : deriv (entReg δ) = entReg1 δ := funext fun r => (hasDerivAt_entReg hδ r).deriv
  rw [hd]
  exact funext fun r => (hasDerivAt_entReg1 hδ r).deriv

theorem entReg_eq_of_nonneg {δ r : ℝ} (hr : 0 ≤ r) : entReg δ r = (r + δ) * Real.log (r + δ) := by
  simp [entReg, hr]

theorem entReg2_eq_of_nonneg {δ r : ℝ} (hr : 0 ≤ r) : entReg2 δ r = (r + δ)⁻¹ := by
  simp [entReg2, hr]

theorem entReg2_le {δ : ℝ} (hδ : 0 < δ) (r : ℝ) : entReg2 δ r ≤ δ⁻¹ := by
  unfold entReg2
  split_ifs with hr
  · exact inv_anti₀ hδ (by linarith)
  · exact le_rfl

theorem entReg2_nonneg {δ : ℝ} (hδ : 0 < δ) (r : ℝ) : 0 ≤ entReg2 δ r := by
  unfold entReg2
  split_ifs with hr
  · exact inv_nonneg.mpr (by linarith)
  · exact inv_nonneg.mpr hδ.le

section Identity

variable {d : ℕ} {G : Torus d → Tangent d} {B : Torus d → Torus d → Tangent d} {g b : ℝ}

/-- **LIP030, step 1.**  Regularised free energy identity: the `C²` entropy `entReg δ`, the
potential `V` and the interaction `W` all evolve against the same flux `J = A + K`. -/
theorem regularised_free_energy_identity
    (h : MeanFieldData G B g b) {ρ0 : L2s d} {u : ℝ → L2s d} (hu : IsGlobalProbFlow h ρ0 u)
    {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ}
    (hV : IsWeakGradient V G)
    (hWc : Continuous fun p : Torus d × Torus d => W p.1 p.2)
    (hsym : ∀ x y, W x y = W y x)
    (hWB : ∀ᵐ y ∂haar d, IsWeakGradientLp ∞ (fun x => W x y) (fun x => B x y))
    {T : ℝ} (hT : 0 ≤ T) :
    ∃ A K : ℝ × Torus d → Tangent d, Measurable A ∧ MemLp A 2 (tmeas d T) ∧
      Measurable K ∧ MemLp K 2 (tmeas d T) ∧
      lip026c_Setting T (fun t => ⇑(u t)) (fun r x => A (r, x)) (fun r x => A (r, x) + K (r, x)) ∧
      (∀ᵐ r ∂(volume.restrict (Icc (0 : ℝ) T)),
        IsWeakGradient (⇑(u r)) (fun x => A (r, x))) ∧
      (∀ᵐ r ∂(volume.restrict (Icc (0 : ℝ) T)),
        (fun x => K (r, x)) =ᵐ[haar d] fun x => u r x • (G x + ∫ y, u r y • B x y ∂haar d)) ∧
      ∀ δ : ℝ, 0 < δ → ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ T →
        (∫ x, entReg δ (u t x) ∂haar d - ∫ x, entReg δ (u s x) ∂haar d =
          -∫ r in s..t, ∫ x, entReg2 δ (u r x) * ⟪A (r, x), A (r, x) + K (r, x)⟫ ∂haar d) ∧
        (∫ x, V x * (u t x - u s x) ∂haar d =
          -∫ r in s..t, ∫ x, ⟪G x, A (r, x) + K (r, x)⟫ ∂haar d) ∧
        (1 / 2 * (∫ p, W p.1 p.2 * (u t p.1 * u t p.2) ∂(haar d).prod (haar d) -
            ∫ p, W p.1 p.2 * (u s p.1 * u s p.2) ∂(haar d).prod (haar d)) =
          -∫ r in s..t, ∫ x, ⟪∫ y, u r y • B x y ∂haar d, A (r, x) + K (r, x)⟫ ∂haar d) := by
  obtain ⟨M, S⟩ := hu.toMild hT
  obtain ⟨A, K, hAm, hA2, hKm, hK2, hKe, hSet⟩ := S.exists_setting
  refine ⟨A, K, hAm, hA2, hKm, hK2, hSet, hSet.grad, ?_, ?_⟩
  · filter_upwards [hKe, ae_restrict_mem measurableSet_Icc] with r hr hrI
    rw [S.uX_of_mem hrI] at hr
    exact hr.trans (nonlinearity_eq_original h (u r) (hu.nonneg r hrI.1) (hu.mass r hrI.1))
  intro δ hδ s t hs hst ht
  have hdiv := hSet.div
  have hJ2 : MemLp (fun p : ℝ × Torus d => A (p.1, p.2) + K (p.1, p.2)) 2 (tmeas d T) :=
    hA2.add hK2
  refine ⟨?_, ?_, ?_⟩
  · have := lip026c_chain_rule_C2 hSet (contDiff_entReg hδ) hs hst ht
    rwa [deriv_deriv_entReg hδ] at this
  · obtain ⟨-, hw⟩ := weakForm_H1 hdiv (fun t _ => Lp.memLp (u t)) hJ2 hV hs hst ht
    have e : ∫ x, V x * (u t x - u s x) ∂haar d =
        ∫ x, u t x * V x ∂haar d - ∫ x, u s x * V x ∂haar d := by
      have h5 := integral_sub ((Lp.memLp (u t)).integrable_mul hV.memLp)
        ((Lp.memLp (u s)).integrable_mul hV.memLp)
      simp only [Pi.mul_apply] at h5
      rw [← h5]
      exact integral_congr_ae (Eventually.of_forall fun x => by ring)
    rw [e, hw]
    congr 1
    refine intervalIntegral.integral_congr fun r _ => ?_
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    exact real_inner_comm _ _
  · have hcore := quad_chain_core (u := u) (J := fun r x => A (r, x) + K (r, x)) hdiv hJ2 S.cont
      hWc hsym h.measurable_B h.norm_B_le h.b_nonneg hWB hs hst ht
    have e : ∫ r in s..t, 2 * Fl B (u := u) (fun r x => A (r, x) + K (r, x)) r r =
        2 * ∫ r in s..t, ∫ x, ⟪∫ y, u r y • B x y ∂haar d, A (r, x) + K (r, x)⟫ ∂haar d := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun r _ => ?_
      show 2 * ∫ x, ⟪A (r, x) + K (r, x), Bc B (u r) x⟫ ∂haar d = _
      congr 1
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      exact real_inner_comm _ _
    rw [e] at hcore
    unfold quadE at hcore
    linarith

end Identity

section Slice

variable {d : ℕ}

theorem dissipation_pointwise_identity {δ ρ : ℝ} (hδ : 0 < δ) (hρ : 0 ≤ ρ) {A a : Tangent d}
    (h0 : ρ = 0 → A = 0) :
    entReg2 δ ρ * ⟪A, A + ρ • a⟫ + ⟪a, A + ρ • a⟫ =
      ‖A + ρ • a‖ ^ 2 / (ρ + δ) + δ / (ρ + δ) * ⟪a, A + ρ • a⟫ := by
  rw [entReg2_eq_of_nonneg hρ]
  rcases hρ.eq_or_lt with h | h
  · subst h
    simp [h0 rfl]
  · have hJ : ⟪A, A + ρ • a⟫ = ‖A + ρ • a‖ ^ 2 - ρ * ⟪a, A + ρ • a⟫ := by
      obtain ⟨J, hJ⟩ : ∃ J, J = A + ρ • a := ⟨_, rfl⟩
      have hA : A = J - ρ • a := by rw [hJ]; simp
      rw [← hJ, hA, inner_sub_left, inner_smul_left, real_inner_self_eq_norm_sq]
      simp
    rw [hJ]
    have : ρ + δ ≠ 0 := by positivity
    field_simp
    ring


/-- The data of one time slice: `ρ ≥ 0` in `H¹` with gradient `A`, flux `J = A + ρ a`
with `a` bounded. -/
structure DissipationSlice (ρ : Torus d → ℝ) (A J a : Torus d → Tangent d) (c : ℝ) : Prop where
  nonneg : ∀ᵐ x ∂haar d, 0 ≤ ρ x
  grad : IsWeakGradient ρ A
  memLp_J : MemLp J 2 (haar d)
  eq : ∀ᵐ x ∂haar d, J x = A x + ρ x • a x
  meas_a : AEStronglyMeasurable a (haar d)
  bound_a : ∀ᵐ x ∂haar d, ‖a x‖ ≤ c

/-- Sequence `δ_n = 1/(n+1)`. -/
noncomputable def dissDelta (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem dissDelta_pos (n : ℕ) : 0 < dissDelta n := by unfold dissDelta; positivity

theorem dissDelta_anti {m n : ℕ} (h : m ≤ n) : dissDelta n ≤ dissDelta m := by
  unfold dissDelta
  exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right h 1)

theorem tendsto_dissDelta : Tendsto dissDelta atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat

variable {ρ : Torus d → ℝ} {A J a : Torus d → Tangent d} {c : ℝ}

theorem DissipationSlice.zero_of_zero (S : DissipationSlice ρ A J a c) :
    ∀ᵐ x ∂haar d, ρ x = 0 → A x = 0 ∧ J x = 0 := by
  filter_upwards [lip026c_locality S.grad, S.eq] with x h1 h2 h3
  have hA := h1 h3
  exact ⟨hA, by simp [h2, hA, h3]⟩

theorem DissipationSlice.integrable_sq_J (S : DissipationSlice ρ A J a c) :
    Integrable (fun x => ‖J x‖ ^ 2) (haar d) :=
  (memLp_two_iff_integrable_sq_norm S.memLp_J.aestronglyMeasurable).1 S.memLp_J

theorem DissipationSlice.aesm_ρ (S : DissipationSlice ρ A J a c) : AEStronglyMeasurable ρ (haar d) :=
  S.grad.memLp.aestronglyMeasurable

theorem DissipationSlice.aemeas_M (S : DissipationSlice ρ A J a c) (δ : ℝ) :
    AEMeasurable (fun x => ‖J x‖ ^ 2 / (ρ x + δ)) (haar d) :=
  ((S.memLp_J.aestronglyMeasurable.norm.aemeasurable.pow_const 2).div
    (S.aesm_ρ.aemeasurable.add_const δ))

theorem DissipationSlice.integrable_M (S : DissipationSlice ρ A J a c) {δ : ℝ} (hδ : 0 < δ) :
    Integrable (fun x => ‖J x‖ ^ 2 / (ρ x + δ)) (haar d) := by
  refine Integrable.mono' (S.integrable_sq_J.const_mul δ⁻¹) (S.aemeas_M δ).aestronglyMeasurable ?_
  filter_upwards [S.nonneg] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_right (inv_anti₀ hδ (by linarith)) (by positivity)

theorem DissipationSlice.tendsto_M_pointwise (S : DissipationSlice ρ A J a c) :
    ∀ᵐ x ∂haar d, Tendsto (fun n => ‖J x‖ ^ 2 / (ρ x + dissDelta n)) atTop (𝓝 (‖J x‖ ^ 2 / ρ x)) := by
  filter_upwards [S.nonneg, S.zero_of_zero] with x hx hz
  rcases hx.eq_or_lt with h | h
  · have := (hz h.symm).2
    simp [this]
  · exact tendsto_const_nhds.div (by simpa using tendsto_const_nhds.add tendsto_dissDelta) h.ne'

theorem DissipationSlice.monotone_M (S : DissipationSlice ρ A J a c) :
    ∀ᵐ x ∂haar d, Monotone fun n => ENNReal.ofReal (‖J x‖ ^ 2 / (ρ x + dissDelta n)) := by
  filter_upwards [S.nonneg] with x hx m n hmn
  refine ENNReal.ofReal_le_ofReal ?_
  have h1 : 0 < ρ x + dissDelta n := by have := dissDelta_pos n; linarith
  exact div_le_div_of_nonneg_left (by positivity) h1 (by linarith [dissDelta_anti hmn])

theorem DissipationSlice.tendsto_lintegral_M (S : DissipationSlice ρ A J a c) :
    Tendsto (fun n => ∫⁻ x, ENNReal.ofReal (‖J x‖ ^ 2 / (ρ x + dissDelta n)) ∂haar d) atTop
      (𝓝 (∫⁻ x, ENNReal.ofReal (‖J x‖ ^ 2 / ρ x) ∂haar d)) := by
  refine lintegral_tendsto_of_tendsto_of_monotone
    (fun n => (S.aemeas_M (dissDelta n)).ennreal_ofReal) S.monotone_M ?_
  filter_upwards [S.tendsto_M_pointwise] with x hx
  exact (ENNReal.tendsto_ofReal hx)


theorem DissipationSlice.integrable_inner (S : DissipationSlice ρ A J a c) :
    Integrable (fun x => ⟪a x, J x⟫) (haar d) := by
  have hc : 0 ≤ c := by
    obtain ⟨x, hx⟩ := S.bound_a.exists
    exact (norm_nonneg _).trans hx
  refine Integrable.mono' ((S.memLp_J.integrable one_le_two).norm.const_mul c)
    (S.meas_a.inner S.memLp_J.aestronglyMeasurable) ?_
  filter_upwards [S.bound_a] with x hx
  rw [Real.norm_eq_abs]
  calc |⟪a x, J x⟫| ≤ ‖a x‖ * ‖J x‖ := abs_real_inner_le_norm _ _
    _ ≤ c * ‖J x‖ := mul_le_mul_of_nonneg_right hx (norm_nonneg _)

theorem DissipationSlice.integrable_R (S : DissipationSlice ρ A J a c) {δ : ℝ} (hδ : 0 < δ) :
    Integrable (fun x => δ / (ρ x + δ) * ⟪a x, J x⟫) (haar d) := by
  refine Integrable.mono' S.integrable_inner.norm
    (((aemeasurable_const.div (S.aesm_ρ.aemeasurable.add_const δ)).aestronglyMeasurable).mul
      (S.meas_a.inner S.memLp_J.aestronglyMeasurable)) ?_
  filter_upwards [S.nonneg] with x hx
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  refine mul_le_of_le_one_left (norm_nonneg _) ?_
  rw [div_le_one (by positivity)]
  linarith

theorem DissipationSlice.tendsto_R (S : DissipationSlice ρ A J a c) :
    Tendsto (fun n => ∫ x, dissDelta n / (ρ x + dissDelta n) * ⟪a x, J x⟫ ∂haar d) atTop (𝓝 0) := by
  have h := tendsto_integral_of_dominated_convergence (μ := haar d)
    (F := fun n x => dissDelta n / (ρ x + dissDelta n) * ⟪a x, J x⟫) (f := fun _ => (0 : ℝ))
    (fun x => ‖⟪a x, J x⟫‖)
    (fun n => (((aemeasurable_const.div (S.aesm_ρ.aemeasurable.add_const (dissDelta n))
      ).aestronglyMeasurable).mul (S.meas_a.inner S.memLp_J.aestronglyMeasurable)))
    S.integrable_inner.norm ?_ ?_
  · simpa using h
  · intro n
    filter_upwards [S.nonneg] with x hx
    have := dissDelta_pos n
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    refine mul_le_of_le_one_left (norm_nonneg _) ?_
    rw [div_le_one (by positivity)]
    linarith
  · filter_upwards [S.nonneg, S.zero_of_zero] with x hx hz
    rcases hx.eq_or_lt with h | h
    · have := (hz h.symm).2
      simp [this]
    · have h1 : Tendsto (fun n => dissDelta n / (ρ x + dissDelta n)) atTop (𝓝 (0 / (ρ x + 0))) :=
        tendsto_dissDelta.div (by simpa using tendsto_const_nhds.add tendsto_dissDelta) (by simpa using h.ne')
      simpa using h1.mul_const ⟪a x, J x⟫

theorem DissipationSlice.integral_pointwise (S : DissipationSlice ρ A J a c) {δ : ℝ} (hδ : 0 < δ) :
    ∫ x, (entReg2 δ (ρ x) * ⟪A x, J x⟫ + ⟪a x, J x⟫) ∂haar d =
      ∫ x, ‖J x‖ ^ 2 / (ρ x + δ) ∂haar d + ∫ x, δ / (ρ x + δ) * ⟪a x, J x⟫ ∂haar d := by
  rw [← integral_add (S.integrable_M hδ) (S.integrable_R hδ)]
  refine integral_congr_ae ?_
  filter_upwards [S.nonneg, S.zero_of_zero, S.eq] with x hx hz he
  rw [he]
  have := dissipation_pointwise_identity (a := a x) hδ hx (fun h => (hz h).1)
  simpa [he] using this


theorem DissipationSlice.integrable_Q (S : DissipationSlice ρ A J a c)
    (hfin : ∫⁻ x, ENNReal.ofReal (‖J x‖ ^ 2 / ρ x) ∂haar d ≠ ⊤) :
    Integrable (fun x => ‖J x‖ ^ 2 / ρ x) (haar d) := by
  refine ⟨(S.aemeas_M 0).aestronglyMeasurable.congr (by simp), ?_⟩
  unfold HasFiniteIntegral
  refine lt_of_le_of_lt (le_of_eq ?_) (lt_top_iff_ne_top.2 hfin)
  refine lintegral_congr_ae ?_
  filter_upwards [S.nonneg] with x hx
  rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (by positivity)]

theorem DissipationSlice.sqrt_H1 (S : DissipationSlice ρ A J a c)
    (hfin : ∫⁻ x, ENNReal.ofReal (‖J x‖ ^ 2 / ρ x) ∂haar d ≠ ⊤) :
    ∃ w : Torus d → Tangent d, IsWeakGradient (fun x => Real.sqrt (ρ x)) w ∧
      ∀ᵐ x ∂haar d, ‖(2 : ℝ) • w x + Real.sqrt (ρ x) • a x‖ ^ 2 = ‖J x‖ ^ 2 / ρ x := by
  have hc : 0 ≤ c := by
    obtain ⟨x, hx⟩ := S.bound_a.exists
    exact (norm_nonneg _).trans hx
  have hQ := S.integrable_Q hfin
  have hρi : Integrable ρ (haar d) := S.grad.memLp.integrable one_le_two
  set w : Torus d → Tangent d := fun x => (2 * Real.sqrt (ρ x))⁻¹ • A x with hw
  have hAm : AEStronglyMeasurable A (haar d) := S.grad.memLp_grad.aestronglyMeasurable
  have hsm : AEStronglyMeasurable (fun x => Real.sqrt (ρ x)) (haar d) :=
    Real.continuous_sqrt.comp_aestronglyMeasurable S.aesm_ρ
  have hwm : AEStronglyMeasurable w (haar d) :=
    (((hsm.const_mul 2).aemeasurable.inv.aestronglyMeasurable).smul hAm)
  -- pointwise facts
  have hnormw : ∀ x, ‖w x‖ ^ 2 = ‖A x‖ ^ 2 / (4 * ρ x) ∨ ρ x < 0 := by
    intro x
    rcases lt_or_ge (ρ x) 0 with h | h
    · exact Or.inr h
    · left
      simp only [hw, norm_smul, Real.norm_eq_abs, mul_pow]
      rw [abs_of_nonneg (by positivity), inv_pow, mul_pow, Real.sq_sqrt h]
      field_simp
      ring
  have hbd : ∀ᵐ x ∂haar d, ‖w x‖ ^ 2 ≤ (1 / 2) * (‖J x‖ ^ 2 / ρ x) + (c ^ 2 / 2) * ρ x := by
    filter_upwards [S.nonneg, S.zero_of_zero, S.eq, S.bound_a] with x hx hz he ha
    rcases hx.eq_or_lt with h | h
    · have hA := (hz h.symm).1
      simp [hw, hA, ← h]
    · rcases hnormw x with h1 | h1
      · rw [h1]
        have hA : A x = J x - ρ x • a x := by rw [he]; simp
        have h2 : ‖A x‖ ^ 2 ≤ 2 * ‖J x‖ ^ 2 + 2 * (ρ x) ^ 2 * c ^ 2 := by
          have : ‖A x‖ ≤ ‖J x‖ + ρ x * c := by
            rw [hA]
            refine (norm_sub_le _ _).trans ?_
            rw [norm_smul, Real.norm_of_nonneg hx]
            exact add_le_add_right (mul_le_mul_of_nonneg_left ha hx) _
          nlinarith [norm_nonneg (A x), norm_nonneg (J x), mul_nonneg hx hc,
            sq_nonneg (‖J x‖ - ρ x * c)]
        rw [div_le_iff₀ (by positivity)]
        have e : (1 / 2 * (‖J x‖ ^ 2 / ρ x) + c ^ 2 / 2 * ρ x) * (4 * ρ x) =
            2 * ‖J x‖ ^ 2 + 2 * ρ x ^ 2 * c ^ 2 := by
          field_simp
          ring
        rw [e]; exact h2
      · exact absurd h1 (not_lt.2 hx)
  have hwL2 : MemLp w 2 (haar d) := by
    refine (memLp_two_iff_integrable_sq_norm hwm).2 ?_
    refine Integrable.mono' ((hQ.const_mul (1 / 2)).add (hρi.const_mul (c ^ 2 / 2)))
      (hwm.norm.pow 2) ?_
    filter_upwards [hbd] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hx
  have hsqL2 : MemLp (fun x => Real.sqrt (ρ x)) 2 (haar d) := by
    refine (memLp_two_iff_integrable_sq_norm hsm).2 (hρi.congr ?_)
    filter_upwards [S.nonneg] with x hx
    rw [Real.norm_eq_abs, sq_abs, Real.sq_sqrt hx]
  refine ⟨w, ?_, ?_⟩
  · have hn : ∀ n, IsWeakGradient (fun x => Real.sqrt (ρ x + dissDelta n))
        (fun x => (2 * Real.sqrt (ρ x + dissDelta n))⁻¹ • A x) := fun n =>
      WeakChainRule.isWeakGradient_sqrt_add (dissDelta_pos n) S.grad S.nonneg
    refine IsWeakGradient.of_tendsto_L1 hsqL2 hwL2 hn ?_ ?_
    · -- function convergence
      have := tendsto_lintegral_norm_of_dominated_convergence (μ := haar d)
        (F := fun n x => Real.sqrt (ρ x + dissDelta n)) (f := fun x => Real.sqrt (ρ x))
        (bound := fun x => Real.sqrt (ρ x) + 1)
        (fun n => (Real.continuous_sqrt.comp_aestronglyMeasurable
          (S.aesm_ρ.add aestronglyMeasurable_const)))
        ((hsqL2.integrable one_le_two).add (integrable_const _)).hasFiniteIntegral ?_ ?_
      · exact this.congr fun n => lintegral_congr fun x => ofReal_norm _
      · intro n
        filter_upwards [S.nonneg] with x hx
        have h1 : Real.sqrt (ρ x + dissDelta n) ≤ Real.sqrt (ρ x) + Real.sqrt (dissDelta n) := by
          have hd := (dissDelta_pos n).le
          refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
          nlinarith [Real.sq_sqrt hx, Real.sq_sqrt hd,
            mul_nonneg (Real.sqrt_nonneg (ρ x)) (Real.sqrt_nonneg (dissDelta n))]
        have h2 : Real.sqrt (dissDelta n) ≤ 1 := by
          rw [Real.sqrt_le_one]
          unfold dissDelta
          rw [div_le_one (by positivity)]
          have : (0:ℝ) ≤ n := Nat.cast_nonneg n
          linarith
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
        linarith
      · exact Eventually.of_forall fun x => (Real.continuous_sqrt.tendsto _).comp
          (by simpa using tendsto_const_nhds.add tendsto_dissDelta)
    · intro j
      have hwi : Integrable (fun x => ‖w x‖) (haar d) := (hwL2.integrable one_le_two).norm
      have := tendsto_lintegral_norm_of_dominated_convergence (μ := haar d)
        (F := fun n x => ((2 * Real.sqrt (ρ x + dissDelta n))⁻¹ • A x) j) (f := fun x => (w x) j)
        (bound := fun x => ‖w x‖)
        (fun n => (memLp_coord (hn n).memLp_grad j).aestronglyMeasurable)
        hwi.hasFiniteIntegral ?_ ?_
      · exact this.congr fun n => lintegral_congr fun x => ofReal_norm _
      · intro n
        filter_upwards [S.nonneg, S.zero_of_zero] with x hx hz
        rcases hx.eq_or_lt with h | h
        · have hA := (hz h.symm).1
          simp [hw, hA]
        · calc ‖((2 * Real.sqrt (ρ x + dissDelta n))⁻¹ • A x) j‖
              ≤ ‖(2 * Real.sqrt (ρ x + dissDelta n))⁻¹ • A x‖ := PiLp.norm_apply_le _ j
            _ ≤ ‖w x‖ := by
              rw [norm_smul, hw]
              simp only [norm_smul]
              refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
              have hs : 0 < Real.sqrt (ρ x) := Real.sqrt_pos.2 h
              rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
                abs_of_nonneg (by positivity)]
              refine inv_anti₀ (by positivity) ?_
              have : Real.sqrt (ρ x) ≤ Real.sqrt (ρ x + dissDelta n) :=
                Real.sqrt_le_sqrt (by linarith [dissDelta_pos n])
              linarith
      · filter_upwards [S.nonneg, S.zero_of_zero] with x hx hz
        rcases hx.eq_or_lt with h | h
        · have hA := (hz h.symm).1
          simp [hw, hA]
        · have hs : 0 < Real.sqrt (ρ x) := Real.sqrt_pos.2 h
          have h1 : Tendsto (fun n => ρ x + dissDelta n) atTop (𝓝 (ρ x)) := by
            simpa using tendsto_const_nhds.add tendsto_dissDelta
          have hr : Tendsto (fun n => (2 * Real.sqrt (ρ x + dissDelta n))⁻¹) atTop
              (𝓝 (2 * Real.sqrt (ρ x))⁻¹) :=
            (((Real.continuous_sqrt.tendsto _).comp h1).const_mul 2).inv₀ (by positivity)
          have hv := hr.smul_const (A x)
          exact ((EuclideanSpace.proj j).continuous.tendsto _).comp hv
  · filter_upwards [S.nonneg, S.zero_of_zero, S.eq] with x hx hz he
    rcases hx.eq_or_lt with h | h
    · have hA := (hz h.symm).1
      have hJ := (hz h.symm).2
      simp [hw, hA, hJ, ← h]
    · have hs : 0 < Real.sqrt (ρ x) := Real.sqrt_pos.2 h
      have e1 : (2 : ℝ) • w x + Real.sqrt (ρ x) • a x = (Real.sqrt (ρ x))⁻¹ • J x := by
        simp only [hw, he, smul_add, smul_smul]
        have : Real.sqrt (ρ x) = (Real.sqrt (ρ x))⁻¹ * ρ x := by
          field_simp
          exact Real.sq_sqrt hx
        congr 1
        · congr 1; field_simp
        · rw [← this]
      rw [e1, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, inv_pow, Real.sq_sqrt hx]
      field_simp

end Slice

theorem ae_tendsto_of_eLpNorm_small {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : ℕ → α → ℝ} {g : α → ℝ}
    (h : ∀ k, eLpNorm (fun x => f k x - g x) 2 μ ≤ ENNReal.ofReal ((1 / 4 : ℝ) ^ k)) :
    ∀ᵐ x ∂μ, Tendsto (fun k => f k x) atTop (𝓝 (g x)) := by
  set S : ℕ → Set α := fun k => {x | ENNReal.ofReal ((1 / 2 : ℝ) ^ k) ≤ ‖f k x - g x‖ₑ} with hS
  have hSm : ∀ k, μ (S k) ≤ ENNReal.ofReal (((1 / 2 : ℝ) ^ k) ^ 2) := by
    intro k
    have h1 := meas_ge_le_mul_pow_eLpNorm_enorm μ (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num)
      (f := fun x => f k x - g x) (ε := ENNReal.ofReal ((1 / 2 : ℝ) ^ k))
      (by simp) (by simp)
    simp only [ENNReal.toReal_ofNat, ENNReal.rpow_ofNat] at h1
    refine h1.trans ?_
    have h2 : eLpNorm (fun x => f k x - g x) 2 μ ^ 2 ≤ ENNReal.ofReal ((1 / 4 : ℝ) ^ k) ^ 2 :=
      pow_le_pow_left' (h k) 2
    refine (mul_le_mul' le_rfl h2).trans (le_of_eq ?_)
    rw [← ENNReal.ofReal_inv_of_pos (by positivity), ← ENNReal.ofReal_pow (by positivity),
      ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [← mul_pow]
    congr 1
    rw [one_div, one_div, inv_pow, inv_pow, inv_inv]
    have : (4 : ℝ) = 2 * 2 := by norm_num
    rw [this, mul_pow]
    field_simp
  have hsum : ∑' k, μ (S k) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hSm)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity)]
    · exact ENNReal.ofReal_ne_top
    · have := summable_geometric_of_lt_one (r := (1/4 : ℝ)) (by norm_num) (by norm_num)
      refine this.congr fun k => ?_
      rw [← pow_mul, mul_comm, pow_mul]
      norm_num
  filter_upwards [ae_eventually_notMem hsum] with x hx
  rw [tendsto_iff_dist_tendsto_zero]
  have hb : ∀ᶠ k in atTop, dist (f k x) (g x) < (1 / 2 : ℝ) ^ k := by
    filter_upwards [hx] with k hk
    simp only [hS, Set.mem_ofPred_eq, not_le] at hk
    rw [Real.dist_eq]
    rw [← ofReal_norm, Real.norm_eq_abs] at hk
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (abs_nonneg _)).1 (by simpa using hk)
  refine squeeze_zero' (Eventually.of_forall fun k => dist_nonneg) (hb.mono fun k hk => hk.le) ?_
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)


section Approx

variable {d : ℕ}

noncomputable def Uapp (u : ℝ → L2s d) (N : ℕ) (p : ℝ × Torus d) : ℝ := u (tauN N p.1) p.2

theorem measurable_Uapp (u : ℝ → L2s d) (N : ℕ) : Measurable (Uapp u N) := by
  have hG : Measurable (fun q : Torus d × ℤ => (u ((q.2 : ℝ) / ((N : ℝ) + 1))) q.1) :=
    measurable_from_prod_countable_left (fun k => (Lp.stronglyMeasurable (u ((k : ℝ) / ((N : ℝ) + 1)))).measurable)
  have hf : Measurable fun p : ℝ × Torus d => (p.2, ⌊((N : ℝ) + 1) * p.1⌋) :=
    measurable_snd.prodMk (Int.measurable_floor.comp (measurable_const.mul measurable_fst))
  exact hG.comp hf

theorem exists_ae_approx {u : ℝ → L2s d} {T : ℝ} (hc : ContinuousOn u (Icc 0 T)) :
    ∃ N : ℕ → ℕ, ∀ r ∈ Icc (0 : ℝ) T, ∀ᵐ x ∂haar d,
      Tendsto (fun k => Uapp u (N k) (r, x)) atTop (𝓝 (u r x)) := by
  have huc := isCompact_Icc.uniformContinuousOn_of_continuous hc
  rw [Metric.uniformContinuousOn_iff] at huc
  have h1 : ∀ k : ℕ, ∃ N : ℕ, ∀ r ∈ Icc (0 : ℝ) T,
      ‖u (tauN N r) - u r‖ < (1 / 4 : ℝ) ^ k := by
    intro k
    obtain ⟨δ, hδ, hu⟩ := huc ((1 / 4 : ℝ) ^ k) (by positivity)
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
    refine ⟨N, fun r hr => ?_⟩
    have ht0 := tauN_nonneg N hr.1
    have htT : tauN N r ≤ T := (tauN_le N r).trans hr.2
    have := hu (tauN N r) ⟨ht0, htT⟩ r hr (by
      rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (by linarith [tauN_le N r])]
      linarith [lt_tauN N r])
    rwa [dist_eq_norm] at this
  choose N hN using h1
  refine ⟨N, fun r hr => ?_⟩
  refine ae_tendsto_of_eLpNorm_small (f := fun k x => Uapp u (N k) (r, x)) (g := u r) fun k => ?_
  have : (fun x => Uapp u (N k) (r, x) - u r x) =ᵐ[haar d] ⇑(u (tauN (N k) r) - u r) :=
    (Lp.coeFn_sub (u (tauN (N k) r)) (u r)).symm
  rw [eLpNorm_congr_ae this, ← Lp.enorm_def, ← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal (hN k r hr).le

theorem aesm_slice_integral {u : ℝ → L2s d} {T : ℝ} (hc : ContinuousOn u (Icc 0 T))
    {Φ : ℝ → ℝ} (hΦ : Continuous Φ) {C : ℝ} (hC : ∀ y, |Φ y| ≤ C)
    {ψ : ℝ × Torus d → ℝ} (hψ : Measurable ψ)
    (hψi : ∀ᵐ r ∂(volume.restrict (Icc (0 : ℝ) T)), Integrable (fun x => ψ (r, x)) (haar d)) :
    AEStronglyMeasurable (fun r => ∫ x, Φ (u r x) * ψ (r, x) ∂haar d)
      (volume.restrict (Icc (0 : ℝ) T)) := by
  obtain ⟨N, hN⟩ := exists_ae_approx hc
  refine aestronglyMeasurable_of_tendsto_ae (u := atTop)
    (f := fun k r => ∫ x, Φ (Uapp u (N k) (r, x)) * ψ (r, x) ∂haar d) (fun k => ?_) ?_
  · exact (((hΦ.measurable.comp (measurable_Uapp u (N k))).mul hψ).stronglyMeasurable
      |>.integral_prod_right' (ν := haar d)).aestronglyMeasurable
  · filter_upwards [hψi, ae_restrict_mem measurableSet_Icc] with r hr hrI
    refine tendsto_integral_of_dominated_convergence (fun x => C * |ψ (r, x)|) (fun k => ?_)
      (hr.abs.const_mul C) (fun k => ?_) ?_
    · exact ((hΦ.measurable.comp ((measurable_Uapp u (N k)).comp
        measurable_prodMk_left)).mul (hψ.comp measurable_prodMk_left)).aestronglyMeasurable
    · refine Eventually.of_forall fun x => ?_
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hC _) (abs_nonneg _)
    · filter_upwards [hN r hrI] with x hx
      exact ((hΦ.tendsto _).comp hx).mul_const _

end Approx

section DLipHelpers

variable {d : ℕ}

theorem coordPartial_heatOp_fderiv {t : ℝ} (ht : 0 < t) {f : Torus d → ℝ} (hf : Integrable f (haar d))
    (j : Fin d) (y : Torus d) :
    coordPartial j (heatOp t f) y =
      fderiv ℝ (fun u : Tangent d => heatOp t f (torusLift u.ofLp)) (secE y)
        (EuclideanSpace.single j 1) := by
  have hD := hasFDerivAt_Hl ht hf (secE y)
  have hT : HasFDerivAt (fun x : Fin d → ℝ => (WithLp.toLp 2 x : Tangent d))
      ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm : (Fin d → ℝ) →L[ℝ] Tangent d)
      (SharpLSI.secT y) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm.hasFDerivAt
  have hc := HasFDerivAt.comp (SharpLSI.secT y)
    (show HasFDerivAt (Hl t f) _ (WithLp.toLp 2 (SharpLSI.secT y)) from hD) hT
  unfold coordPartial
  have hfun : (heatOp t f ∘ torusLift) = (Hl t f ∘ fun x : Fin d → ℝ => (WithLp.toLp 2 x : Tangent d)) := rfl
  have hfun2 : (fun u : Tangent d => heatOp t f (torusLift u.ofLp)) = Hl t f := rfl
  rw [hfun, hc.fderiv, hfun2, hD.fderiv]
  rfl

theorem norm_smoothGrad_heatOp_le {t : ℝ} (ht : 0 < t) {f : Torus d → ℝ}
    (hf : TorusLipschitzWith 1 f) (y : Torus d) : ‖smoothGrad (heatOp t f) y‖ ≤ 1 := by
  have hfi : Integrable f (haar d) :=
    integrable_of_continuous_torus (continuous_of_torusLipschitz zero_le_one hf)
  set L := fderiv ℝ (fun u : Tangent d => heatOp t f (torusLift u.ofLp)) (secE y) with hL
  set G := smoothGrad (heatOp t f) y with hG
  have hGj : ∀ j, G j = L (EuclideanSpace.single j 1) := fun j => by
    rw [hG, smoothGrad_apply, coordPartial_heatOp_fderiv ht hfi]
  have hnorm : ‖G‖ ^ 2 = L G := by
    have e : G = ∑ j, G j • (EuclideanSpace.single j (1 : ℝ) : Tangent d) := by
      ext i; simp [Pi.single_apply]
    conv_rhs => rw [e]
    rw [tangent_norm_sq, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, smul_eq_mul, ← hGj]; ring
  have hLn : ‖L‖ ≤ 1 := ((periodized_heat_gradient_bounds ht).2.1 zero_le_one hf (secE y)).2
  rcases (norm_nonneg G).eq_or_lt with h0 | hpos
  · rw [← h0]; exact zero_le_one
  · have : ‖G‖ ^ 2 ≤ ‖L‖ * ‖G‖ := by
      rw [hnorm]; exact (le_abs_self _).trans (L.le_opNorm G)
    nlinarith



variable {d : ℕ} {ρ : Torus d → ℝ} {A J a : Torus d → Tangent d} {c : ℝ}

theorem DissipationSlice.integral_norm_le (S : DissipationSlice ρ A J a c)
    (hfin : ∫⁻ x, ENNReal.ofReal (‖J x‖ ^ 2 / ρ x) ∂haar d ≠ ⊤)
    (hmass : ∫ x, ρ x ∂haar d = 1) :
    ∫ x, ‖J x‖ ∂haar d ≤ Real.sqrt (∫ x, ‖J x‖ ^ 2 / ρ x ∂haar d) := by
  set Q := ∫ x, ‖J x‖ ^ 2 / ρ x ∂haar d with hQ
  have hQi := S.integrable_Q hfin
  have hρi : Integrable ρ (haar d) := S.grad.memLp.integrable one_le_two
  have hQ0 : 0 ≤ Q := integral_nonneg_of_ae (by
    filter_upwards [S.nonneg] with x hx
    have : 0 ≤ ρ x := hx
    positivity)
  have hJi : Integrable (fun x => ‖J x‖) (haar d) := (S.memLp_J.integrable one_le_two).norm
  have key : ∀ ε : ℝ, 0 < ε → ∫ x, ‖J x‖ ∂haar d ≤ Real.sqrt (Q + ε) := by
    intro ε hε
    set c := Real.sqrt (Q + ε) with hc
    have hcpos : 0 < c := Real.sqrt_pos.2 (by linarith)
    have hc2 : c ^ 2 = Q + ε := Real.sq_sqrt (by linarith)
    have hpt : ∀ᵐ x ∂haar d, ‖J x‖ ≤ 1 / 2 * ((‖J x‖ ^ 2 / ρ x) / c + ρ x * c) := by
      filter_upwards [S.nonneg, S.zero_of_zero] with x hx h0
      have hx' : 0 ≤ ρ x := hx
      rcases hx'.eq_or_lt with h | h
      · have := (h0 h.symm).2
        rw [this, ← h]; simp
      · have hm : 0 < ρ x * c := mul_pos h hcpos
        have e : (‖J x‖ ^ 2 / ρ x) / c + ρ x * c - 2 * ‖J x‖ = (‖J x‖ - ρ x * c) ^ 2 / (ρ x * c) := by
          field_simp
          ring
        have : 0 ≤ (‖J x‖ - ρ x * c) ^ 2 / (ρ x * c) := by positivity
        linarith
    calc ∫ x, ‖J x‖ ∂haar d
        ≤ ∫ x, 1 / 2 * ((‖J x‖ ^ 2 / ρ x) / c + ρ x * c) ∂haar d :=
          integral_mono_ae hJi (((hQi.div_const c).add (hρi.mul_const c)).const_mul _) hpt
      _ = 1 / 2 * (Q / c + c) := by
          rw [integral_const_mul, integral_add (hQi.div_const c) (hρi.mul_const c),
            integral_div, integral_mul_const, hmass, one_mul]
      _ ≤ c := by
          have : Q / c ≤ c := by
            rw [div_le_iff₀ hcpos]; nlinarith
          linarith
  have ht : Tendsto (fun ε : ℝ => Real.sqrt (Q + ε)) (𝓝[>] 0) (𝓝 (Real.sqrt Q)) := by
    have hcont : Continuous fun ε : ℝ => Real.sqrt (Q + ε) :=
      Real.continuous_sqrt.comp (continuous_const.add continuous_id)
    have := hcont.tendsto 0
    simp only [add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  exact ge_of_tendsto ht (eventually_nhdsWithin_of_forall fun ε hε => key ε hε)



variable {d : ℕ}

theorem tendsto_integral_mul_heatOp {f ψ : Torus d → ℝ} (hf : MemLp f 2 (haar d))
    (hψ : MemLp ψ 2 (haar d)) :
    Tendsto (fun t : ℝ => ∫ x, heatOp t f x * ψ x ∂haar d) (𝓝[>] 0)
      (𝓝 (∫ x, f x * ψ x ∂haar d)) := by
  have hD := tendsto_integral_sq_heatOp_sub hf
  have hC : Tendsto (fun t : ℝ => √((∫ y, (heatOp t f y - f y) ^ 2 ∂haar d) *
      ∫ x, ψ x ^ 2 ∂haar d)) (𝓝[>] 0) (𝓝 0) := by
    have := (hD.mul_const (∫ x, ψ x ^ 2 ∂haar d)).sqrt
    simpa using this
  rw [← tendsto_sub_nhds_zero_iff]
  refine squeeze_zero_norm' ?_ hC
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht : 0 < t := ht
  have hv := memLp_heatOp ht one_le_two (by simp) hf
  have e : ∫ x, heatOp t f x * ψ x ∂haar d - ∫ x, f x * ψ x ∂haar d =
      ∫ x, (heatOp t f x - f x) * ψ x ∂haar d := by
    have i1 : Integrable (fun x => heatOp t f x * ψ x) (haar d) := hv.integrable_mul hψ
    have i2 : Integrable (fun x => f x * ψ x) (haar d) := hf.integrable_mul hψ
    rw [← integral_sub i1 i2]
    simp_rw [sub_mul]
  rw [e, Real.norm_eq_abs]
  exact Real.abs_le_sqrt (cs_L2 (hv.sub hf) hψ)

variable {ρ : Torus d → ℝ} {A J a : Torus d → Tangent d} {c : ℝ}

theorem DissipationSlice.toReal_Q (S : DissipationSlice ρ A J a c) :
    (∫⁻ x, ENNReal.ofReal (‖J x‖ ^ 2 / ρ x) ∂haar d).toReal = ∫ x, ‖J x‖ ^ 2 / ρ x ∂haar d := by
  have hnn : 0 ≤ᵐ[haar d] fun x => ‖J x‖ ^ 2 / ρ x := by
    filter_upwards [S.nonneg] with x hx
    have : 0 ≤ ρ x := hx
    positivity
  exact (integral_eq_lintegral_of_nonneg_ae hnn
    ((S.aemeas_M 0).aestronglyMeasurable.congr (by simp))).symm

end DLipHelpers

section Assembly

variable {d : ℕ} {G : Torus d → Tangent d} {B : Torus d → Torus d → Tangent d} {g b : ℝ}

/-- Slices of an `L²` function on the time-space product are `L²` for a.e. time. -/
theorem ae_memLp_slice {T : ℝ} {F : ℝ × Torus d → Tangent d} (hF : Measurable F)
    (h2 : MemLp F 2 (tmeas d T)) :
    ∀ᵐ r ∂(volume.restrict (Icc (0 : ℝ) T)), MemLp (fun x => F (r, x)) 2 (haar d) := by
  have hi : Integrable (fun p => ‖F p‖ ^ 2) (tmeas d T) :=
    (memLp_two_iff_integrable_sq_norm hF.aestronglyMeasurable).1 h2
  filter_upwards [hi.prod_right_ae] with r hr
  exact (memLp_two_iff_integrable_sq_norm
    (hF.comp measurable_prodMk_left).aestronglyMeasurable).2 hr

/-- The time data of the dissipation identity. -/
structure DissData (h : MeanFieldData G B g b) (u : ℝ → L2s d) (T : ℝ)
    (A K : ℝ × Torus d → Tangent d) : Prop where
  T_nonneg : 0 ≤ T
  cont : ContinuousOn u (Icc 0 T)
  nonneg : ∀ r ∈ Icc (0 : ℝ) T, 0 ≤ᵐ[haar d] ⇑(u r)
  mass : ∀ r ∈ Icc (0 : ℝ) T, ∫ x, u r x ∂haar d = 1
  measA : Measurable A
  measK : Measurable K
  memA : MemLp A 2 (tmeas d T)
  memK : MemLp K 2 (tmeas d T)
  setting : lip026c_Setting T (fun t => ⇑(u t)) (fun r x => A (r, x)) (fun r x => A (r, x) + K (r, x))
  grad : ∀ᵐ r ∂(volume.restrict (Icc (0 : ℝ) T)), IsWeakGradient (⇑(u r)) (fun x => A (r, x))
  Ke : ∀ᵐ r ∂(volume.restrict (Icc (0 : ℝ) T)),
    (fun x => K (r, x)) =ᵐ[haar d] fun x => u r x • (G x + ∫ y, u r y • B x y ∂haar d)

variable {h : MeanFieldData G B g b} {u : ℝ → L2s d} {T : ℝ} {A K : ℝ × Torus d → Tangent d}

theorem DissData.measJ (D : DissData h u T A K) : Measurable fun p => A p + K p :=
  D.measA.add D.measK

theorem DissData.memJ (D : DissData h u T A K) : MemLp (fun p => A p + K p) 2 (tmeas d T) :=
  D.memA.add D.memK

theorem DissData.slice (D : DissData h u T A K) :
    ∀ᵐ r ∂(volume.restrict (Icc (0 : ℝ) T)),
      DissipationSlice (⇑(u r)) (fun x => A (r, x)) (fun x => A (r, x) + K (r, x))
        (fun x => G x + Bc B (u r) x) (g + b) := by
  filter_upwards [D.grad, D.Ke, ae_restrict_mem measurableSet_Icc,
    ae_memLp_slice D.measJ D.memJ] with r hr hK hrI hJ
  have hu1 : Integrable (⇑(u r)) (haar d) := integrable_L2s (u r)
  refine ⟨D.nonneg r hrI, hr, hJ, ?_, ?_, ?_⟩
  · filter_upwards [hK] with x hx
    rw [hx]
    rfl
  · exact (h.measurable_G.aestronglyMeasurable).add
      (stronglyMeasurable_Bc h.measurable_B (Lp.stronglyMeasurable (u r))).aestronglyMeasurable
  · refine Eventually.of_forall fun x => ?_
    have h1 := norm_Bc_le h.norm_B_le hu1 x
    have h2 : ∫ y, |u r y| ∂haar d = 1 :=
      (integral_congr_ae ((D.nonneg r hrI).mono fun y hy => abs_of_nonneg hy)).trans
        (D.mass r hrI)
    rw [h2, mul_one] at h1
    exact (norm_add_le _ _).trans (add_le_add (h.norm_G_le x) h1)

theorem integrable_inner_of_memLp2 {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {F1 F2 : α → Tangent d} (h1 : MemLp F1 2 μ) (h2 : MemLp F2 2 μ) :
    Integrable (fun p => ⟪F1 p, F2 p⟫) μ := by
  have i1 := (memLp_two_iff_integrable_sq_norm h1.aestronglyMeasurable).1 h1
  have i2 := (memLp_two_iff_integrable_sq_norm h2.aestronglyMeasurable).1 h2
  refine Integrable.mono' ((i1.add i2).const_mul 1)
    (h1.aestronglyMeasurable.inner h2.aestronglyMeasurable) (Eventually.of_forall fun p => ?_)
  rw [Real.norm_eq_abs]
  have := abs_real_inner_le_norm (F1 p) (F2 p)
  simp only [Pi.add_apply]
  nlinarith [sq_nonneg (‖F1 p‖ - ‖F2 p‖), norm_nonneg (F1 p), norm_nonneg (F2 p)]

theorem DissData.integrable_AJ (D : DissData h u T A K) :
    Integrable (fun p => ⟪A p, A p + K p⟫) (tmeas d T) :=
  integrable_inner_of_memLp2 D.memA D.memJ

theorem DissData.integrable_GJ (D : DissData h u T A K) :
    Integrable (fun p : ℝ × Torus d => ⟪G p.2, A p + K p⟫) (tmeas d T) := by
  refine Integrable.mono' ((D.memJ.integrable one_le_two).norm.const_mul g)
    ((h.measurable_G.comp measurable_snd).aestronglyMeasurable.inner
      D.memJ.aestronglyMeasurable) (Eventually.of_forall fun p => ?_)
  rw [Real.norm_eq_abs]
  exact (abs_real_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_right (h.norm_G_le _) (norm_nonneg _))

/-- Time-integrability of the three flux pairings. -/
theorem DissData.integrable_f2 (D : DissData h u T A K) :
    Integrable (fun r => ∫ x, ⟪G x, A (r, x) + K (r, x)⟫ ∂haar d)
      (volume.restrict (Icc (0 : ℝ) T)) :=
  D.integrable_GJ.integral_prod_left

theorem DissData.integrable_f3 (D : DissData h u T A K) :
    Integrable (fun r => ∫ x, ⟪∫ y, u r y • B x y ∂haar d, A (r, x) + K (r, x)⟫ ∂haar d)
      (volume.restrict (Icc (0 : ℝ) T)) := by
  have := integrable_Fd (B := B) (b := b) (u := u) (T := T) (J := fun r x => A (r, x) + K (r, x))
    h.measurable_B h.norm_B_le h.b_nonneg D.setting.div D.cont
  refine this.congr (Eventually.of_forall fun r => ?_)
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  exact real_inner_comm _ _

theorem DissData.integrable_f1 (D : DissData h u T A K) {δ : ℝ} (hδ : 0 < δ) :
    Integrable (fun r => ∫ x, entReg2 δ (u r x) * ⟪A (r, x), A (r, x) + K (r, x)⟫ ∂haar d)
      (volume.restrict (Icc (0 : ℝ) T)) := by
  have hmi : Integrable (fun r => ∫ x, ‖⟪A (r, x), A (r, x) + K (r, x)⟫‖ ∂haar d)
      (volume.restrict (Icc (0 : ℝ) T)) := D.integrable_AJ.norm.integral_prod_left
  have hψ : Measurable fun p : ℝ × Torus d => ⟪A p, A p + K p⟫ := D.measA.inner D.measJ
  have hψi := D.integrable_AJ.prod_right_ae
  refine Integrable.mono' (hmi.const_mul δ⁻¹) ?_ ?_
  · exact aesm_slice_integral D.cont (continuous_entReg2 hδ) (C := δ⁻¹)
      (fun y => by rw [abs_of_nonneg (entReg2_nonneg hδ y)]; exact entReg2_le hδ y) hψ hψi
  · filter_upwards [hψi] with r hr
    have := norm_integral_le_of_norm_le (hr.norm.const_mul δ⁻¹)
      (f := fun x => entReg2 δ (u r x) * ⟪A (r, x), A (r, x) + K (r, x)⟫) (μ := haar d)
      (Eventually.of_forall fun x => by
        rw [norm_mul, Real.norm_eq_abs (entReg2 δ _), abs_of_nonneg (entReg2_nonneg hδ _)]
        exact mul_le_mul_of_nonneg_right (entReg2_le hδ _) (norm_nonneg _))
    rwa [integral_const_mul] at this

/-- The slice functionals `M_δ(r) = ∫ ‖J_r‖²/(u_r+δ)` and `R_δ(r) = ∫ δ/(u_r+δ) ⟨a_r, J_r⟩`. -/
noncomputable def Mdel (u : ℝ → L2s d) (J : ℝ × Torus d → Tangent d) (δ r : ℝ) : ℝ :=
  ∫ x, ‖J (r, x)‖ ^ 2 / (u r x + δ) ∂haar d

noncomputable def Rdel (G : Torus d → Tangent d) (B : Torus d → Torus d → Tangent d)
    (u : ℝ → L2s d) (J : ℝ × Torus d → Tangent d) (δ r : ℝ) : ℝ :=
  ∫ x, δ / (u r x + δ) * ⟪G x + Bc B (u r) x, J (r, x)⟫ ∂haar d

theorem DissData.aesm_M (D : DissData h u T A K) {δ : ℝ} (hδ : 0 < δ) :
    AEStronglyMeasurable (Mdel u (fun p => A p + K p) δ) (volume.restrict (Icc (0 : ℝ) T)) := by
  have hψ : Measurable fun p : ℝ × Torus d => ‖A p + K p‖ ^ 2 := D.measJ.norm.pow_const 2
  have hψi : ∀ᵐ r ∂(volume.restrict (Icc (0 : ℝ) T)),
      Integrable (fun x => ‖A (r, x) + K (r, x)‖ ^ 2) (haar d) := by
    filter_upwards [ae_memLp_slice D.measJ D.memJ] with r hr
    exact (memLp_two_iff_integrable_sq_norm hr.aestronglyMeasurable).1 hr
  have := aesm_slice_integral D.cont (Φ := fun y => (max y 0 + δ)⁻¹)
    (by
      refine Continuous.inv₀ (by fun_prop) fun y => ?_
      have := le_max_right y 0
      exact ne_of_gt (by linarith)) (C := δ⁻¹) (fun y => by
      rw [abs_of_nonneg (by positivity)]
      exact inv_anti₀ hδ (by linarith [le_max_right y 0])) hψ hψi
  refine this.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
  refine integral_congr_ae ((D.nonneg r hr).mono fun x hx0 => ?_)
  have hx : 0 ≤ u r x := hx0
  show (max (u r x) 0 + δ)⁻¹ * ‖A (r, x) + K (r, x)‖ ^ 2 = ‖A (r, x) + K (r, x)‖ ^ 2 / (u r x + δ)
  rw [max_eq_left hx, inv_mul_eq_div]

theorem DissData.integrable_M (D : DissData h u T A K) {δ : ℝ} (hδ : 0 < δ) :
    Integrable (Mdel u (fun p => A p + K p) δ) (volume.restrict (Icc (0 : ℝ) T)) := by
  have hmi : Integrable (fun r => ∫ x, ‖A (r, x) + K (r, x)‖ ^ 2 ∂haar d)
      (volume.restrict (Icc (0 : ℝ) T)) :=
    ((memLp_two_iff_integrable_sq_norm D.memJ.aestronglyMeasurable).1 D.memJ).integral_prod_left
  refine Integrable.mono' (hmi.const_mul δ⁻¹) (D.aesm_M hδ) ?_
  filter_upwards [D.slice] with r S
  have := norm_integral_le_of_norm_le ((S.integrable_sq_J).const_mul δ⁻¹)
    (f := fun x => ‖A (r, x) + K (r, x)‖ ^ 2 / (u r x + δ)) (μ := haar d)
    (by
      filter_upwards [S.nonneg] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), div_eq_inv_mul]
      exact mul_le_mul_of_nonneg_right (inv_anti₀ hδ (by linarith)) (by positivity))
  rwa [integral_const_mul] at this

theorem DissData.slice_sum (D : DissData h u T A K) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᵐ r ∂(volume.restrict (Icc (0 : ℝ) T)),
      (∫ x, entReg2 δ (u r x) * ⟪A (r, x), A (r, x) + K (r, x)⟫ ∂haar d) +
        (∫ x, ⟪G x, A (r, x) + K (r, x)⟫ ∂haar d) +
        (∫ x, ⟪∫ y, u r y • B x y ∂haar d, A (r, x) + K (r, x)⟫ ∂haar d) =
      Mdel u (fun p => A p + K p) δ r + Rdel G B u (fun p => A p + K p) δ r := by
  filter_upwards [D.slice] with r S
  have hAJ : Integrable (fun x => ⟪A (r, x), A (r, x) + K (r, x)⟫) (haar d) :=
    integrable_inner_of_memLp2 S.grad.memLp_grad S.memLp_J
  have h1 : Integrable (fun x => entReg2 δ (u r x) * ⟪A (r, x), A (r, x) + K (r, x)⟫) (haar d) := by
    refine Integrable.mono' (hAJ.norm.const_mul δ⁻¹)
      (((continuous_entReg2 hδ).measurable.comp (Lp.stronglyMeasurable (u r)).measurable
        ).aestronglyMeasurable.mul hAJ.aestronglyMeasurable) (Eventually.of_forall fun x => ?_)
    rw [norm_mul, Real.norm_eq_abs (entReg2 δ _), abs_of_nonneg (entReg2_nonneg hδ _)]
    exact mul_le_mul_of_nonneg_right (entReg2_le hδ _) (norm_nonneg _)
  have h2 : Integrable (fun x => ⟪G x, A (r, x) + K (r, x)⟫) (haar d) := by
    refine Integrable.mono' ((S.memLp_J.integrable one_le_two).norm.const_mul g)
      (h.measurable_G.aestronglyMeasurable.inner S.memLp_J.aestronglyMeasurable)
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs]
    exact (abs_real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right (h.norm_G_le _) (norm_nonneg _))
  have h3 : Integrable (fun x => ⟪Bc B (u r) x, A (r, x) + K (r, x)⟫) (haar d) := by
    have := S.integrable_inner.sub h2
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.sub_apply, inner_add_left]
    ring
  have key := S.integral_pointwise hδ
  rw [integral_add h1 S.integrable_inner] at key
  have e : ∫ x, ⟪G x + Bc B (u r) x, A (r, x) + K (r, x)⟫ ∂haar d =
      (∫ x, ⟪G x, A (r, x) + K (r, x)⟫ ∂haar d) +
        ∫ x, ⟪Bc B (u r) x, A (r, x) + K (r, x)⟫ ∂haar d := by
    rw [← integral_add h2 h3]
    simp only [inner_add_left]
  rw [e] at key
  unfold Mdel Rdel
  rw [← key]
  show _ + _ + (∫ x, ⟪Bc B (u r) x, A (r, x) + K (r, x)⟫ ∂haar d) = _
  ring

theorem DissData.abs_R_le (D : DissData h u T A K) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᵐ r ∂(volume.restrict (Icc (0 : ℝ) T)),
      |Rdel G B u (fun p => A p + K p) δ r| ≤
        (g + b) * ∫ x, ‖A (r, x) + K (r, x)‖ ∂haar d := by
  filter_upwards [D.slice] with r S
  have hJ1 : Integrable (fun x => ‖A (r, x) + K (r, x)‖) (haar d) :=
    (S.memLp_J.integrable one_le_two).norm
  have := norm_integral_le_of_norm_le (hJ1.const_mul (g + b))
    (f := fun x => δ / (u r x + δ) * ⟪G x + Bc B (u r) x, A (r, x) + K (r, x)⟫) (μ := haar d)
    (by
      filter_upwards [S.nonneg, S.bound_a] with x hx hb
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have h1 : δ / (u r x + δ) ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith
      calc δ / (u r x + δ) * ‖⟪G x + Bc B (u r) x, A (r, x) + K (r, x)⟫‖
          ≤ 1 * ‖⟪G x + Bc B (u r) x, A (r, x) + K (r, x)⟫‖ :=
            mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
        _ ≤ (g + b) * ‖A (r, x) + K (r, x)‖ := by
            rw [one_mul, Real.norm_eq_abs]
            exact (abs_real_inner_le_norm _ _).trans
              (mul_le_mul_of_nonneg_right hb (norm_nonneg _)))
  rw [integral_const_mul] at this
  exact this

theorem tendsto_entReg_integral {f : Torus d → ℝ} (hf : AEStronglyMeasurable f (haar d))
    (hnn : 0 ≤ᵐ[haar d] f) {M : ℝ} (hM : ∀ᵐ x ∂haar d, |f x| ≤ M) :
    Tendsto (fun n => ∫ x, entReg (dissDelta n) (f x) ∂haar d) atTop
      (𝓝 (∫ x, f x * Real.log (f x) ∂haar d)) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (f := fun z : ℝ => z * Real.log z) (s := Icc 0 (max M 0 + 1)) Real.continuous_mul_log.continuousOn
  refine tendsto_integral_of_dominated_convergence (fun _ => C) (fun n => ?_) (integrable_const C)
    (fun n => ?_) ?_
  · exact ((contDiff_entReg (dissDelta_pos n)).continuous.comp_aestronglyMeasurable hf)
  · filter_upwards [hnn, hM] with x hx0 hx1
    have hx : 0 ≤ f x := hx0
    have hδ1 : dissDelta n ≤ 1 := by
      unfold dissDelta
      rw [div_le_one (by positivity)]
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    rw [entReg_eq_of_nonneg hx]
    refine hC _ ⟨by linarith [dissDelta_pos n], ?_⟩
    have := (le_abs_self (f x)).trans hx1
    have := le_max_left M 0
    linarith
  · filter_upwards [hnn] with x hx0
    have hx : 0 ≤ f x := hx0
    have : Tendsto (fun n => f x + dissDelta n) atTop (𝓝 (f x + 0)) :=
      tendsto_const_nhds.add tendsto_dissDelta
    rw [add_zero] at this
    have h2 := (Real.continuous_mul_log.tendsto (f x)).comp this
    refine h2.congr fun n => ?_
    simp [entReg_eq_of_nonneg hx]

theorem DissData.integrable_R (D : DissData h u T A K) {δ : ℝ} (hδ : 0 < δ) :
    Integrable (Rdel G B u (fun p => A p + K p) δ) (volume.restrict (Icc (0 : ℝ) T)) := by
  have := ((D.integrable_f1 hδ).add D.integrable_f2).add D.integrable_f3 |>.sub (D.integrable_M hδ)
  refine this.congr ?_
  filter_upwards [D.slice_sum hδ] with r hr
  simp only [Pi.sub_apply, Pi.add_apply]
  linarith

theorem DissData.integrable_bound_R (D : DissData h u T A K) :
    Integrable (fun r => (g + b) * ∫ x, ‖A (r, x) + K (r, x)‖ ∂haar d)
      (volume.restrict (Icc (0 : ℝ) T)) :=
  ((D.memJ.integrable one_le_two).norm.integral_prod_left).const_mul (g + b)

theorem DissData.tendsto_R_integral (D : DissData h u T A K) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (ht : t ≤ T) :
    Tendsto (fun n => ∫ r in s..t, Rdel G B u (fun p => A p + K p) (dissDelta n) r) atTop
      (𝓝 0) := by
  have hsub : Ioc s t ⊆ Icc 0 T := fun r hr => ⟨hs.trans hr.1.le, hr.2.trans ht⟩
  have hmono : (volume.restrict (Ioc s t)) ≤ (volume.restrict (Icc (0 : ℝ) T)) :=
    Measure.restrict_mono hsub le_rfl
  simp only [intervalIntegral.integral_of_le hst]
  have := tendsto_integral_of_dominated_convergence (μ := volume.restrict (Ioc s t))
    (F := fun n r => Rdel G B u (fun p => A p + K p) (dissDelta n) r) (f := fun _ => (0 : ℝ))
    (fun r => (g + b) * ∫ x, ‖A (r, x) + K (r, x)‖ ∂haar d)
    (fun n => ((D.integrable_R (dissDelta_pos n)).aestronglyMeasurable.mono_measure hmono))
    (D.integrable_bound_R.mono_measure hmono) ?_ ?_
  · simpa using this
  · intro n
    have := ae_restrict_of_ae_restrict_of_subset hsub (D.abs_R_le (dissDelta_pos n))
    filter_upwards [this] with r hr
    rwa [Real.norm_eq_abs]
  · have := ae_restrict_of_ae_restrict_of_subset hsub D.slice
    filter_upwards [this] with r S
    exact S.tendsto_R

/-- The slice dissipation `Q(r) = ∫ ‖J_r‖²/u_r ∈ [0, ∞]`. -/
noncomputable def Qdis (u : ℝ → L2s d) (J : ℝ × Torus d → Tangent d) (r : ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (‖J (r, x)‖ ^ 2 / u r x) ∂haar d

theorem DissData.slice_Q (D : DissData h u T A K) :
    ∀ᵐ r ∂(volume.restrict (Icc (0 : ℝ) T)),
      (∀ n, ENNReal.ofReal (Mdel u (fun p => A p + K p) (dissDelta n) r) =
        ∫⁻ x, ENNReal.ofReal (‖A (r, x) + K (r, x)‖ ^ 2 / (u r x + dissDelta n)) ∂haar d) ∧
      Monotone (fun n => ENNReal.ofReal (Mdel u (fun p => A p + K p) (dissDelta n) r)) ∧
      Qdis u (fun p => A p + K p) r =
        ⨆ n, ENNReal.ofReal (Mdel u (fun p => A p + K p) (dissDelta n) r) := by
  filter_upwards [D.slice] with r S
  have e : ∀ n, ENNReal.ofReal (Mdel u (fun p => A p + K p) (dissDelta n) r) =
      ∫⁻ x, ENNReal.ofReal (‖A (r, x) + K (r, x)‖ ^ 2 / (u r x + dissDelta n)) ∂haar d := by
    intro n
    unfold Mdel
    refine ofReal_integral_eq_lintegral_ofReal (S.integrable_M (dissDelta_pos n)) ?_
    filter_upwards [S.nonneg] with x hx0
    have hx : 0 ≤ u r x := hx0
    have := dissDelta_pos n
    positivity
  have hmono : Monotone (fun n => ENNReal.ofReal (Mdel u (fun p => A p + K p) (dissDelta n) r)) := by
    intro m n hmn
    simp only [e]
    exact lintegral_mono_ae (by
      filter_upwards [S.monotone_M] with x hx
      exact hx hmn)
  refine ⟨e, hmono, ?_⟩
  have ht : Tendsto (fun n => ENNReal.ofReal (Mdel u (fun p => A p + K p) (dissDelta n) r)) atTop
      (𝓝 (Qdis u (fun p => A p + K p) r)) := by
    simp only [e]
    exact S.tendsto_lintegral_M
  exact tendsto_nhds_unique ht (tendsto_atTop_iSup hmono)

theorem DissData.aemeas_Q (D : DissData h u T A K) :
    AEMeasurable (Qdis u (fun p => A p + K p)) (volume.restrict (Icc (0 : ℝ) T)) := by
  have : AEMeasurable (fun r => ⨆ n, ENNReal.ofReal (Mdel u (fun p => A p + K p) (dissDelta n) r))
      (volume.restrict (Icc (0 : ℝ) T)) :=
    AEMeasurable.iSup fun n => (D.aesm_M (dissDelta_pos n)).aemeasurable.ennreal_ofReal
  refine this.congr ?_
  filter_upwards [D.slice_Q] with r hr
  exact hr.2.2.symm

theorem DissData.nonneg_M (D : DissData h u T A K) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᵐ r ∂(volume.restrict (Icc (0 : ℝ) T)), 0 ≤ Mdel u (fun p => A p + K p) δ r := by
  filter_upwards [D.slice, ae_restrict_mem measurableSet_Icc] with r S hr
  unfold Mdel
  refine integral_nonneg_of_ae ?_
  filter_upwards [S.nonneg] with x hx0
  have hx : 0 ≤ u r x := hx0
  show 0 ≤ ‖A (r, x) + K (r, x)‖ ^ 2 / (u r x + δ)
  positivity

theorem DissData.tendsto_lintegral_Q (D : DissData h u T A K) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (ht : t ≤ T) :
    Tendsto (fun n => ENNReal.ofReal (∫ r in s..t, Mdel u (fun p => A p + K p) (dissDelta n) r))
      atTop (𝓝 (∫⁻ r in Ioc s t, Qdis u (fun p => A p + K p) r)) := by
  have hsub : Ioc s t ⊆ Icc 0 T := fun r hr => ⟨hs.trans hr.1.le, hr.2.trans ht⟩
  have hmono : (volume.restrict (Ioc s t)) ≤ (volume.restrict (Icc (0 : ℝ) T)) :=
    Measure.restrict_mono hsub le_rfl
  have e : ∀ n, ENNReal.ofReal (∫ r in s..t, Mdel u (fun p => A p + K p) (dissDelta n) r) =
      ∫⁻ r in Ioc s t, ENNReal.ofReal (Mdel u (fun p => A p + K p) (dissDelta n) r) := by
    intro n
    rw [intervalIntegral.integral_of_le hst]
    exact ofReal_integral_eq_lintegral_ofReal
      ((D.integrable_M (dissDelta_pos n)).mono_measure hmono)
      (ae_restrict_of_ae_restrict_of_subset hsub (D.nonneg_M (dissDelta_pos n)))
  simp only [e]
  have hae := ae_restrict_of_ae_restrict_of_subset hsub D.slice_Q
  have hQ : ∫⁻ r in Ioc s t, Qdis u (fun p => A p + K p) r =
      ⨆ n, ∫⁻ r in Ioc s t, ENNReal.ofReal (Mdel u (fun p => A p + K p) (dissDelta n) r) := by
    rw [← lintegral_iSup' (fun n => ((D.aesm_M (dissDelta_pos n)).aemeasurable.ennreal_ofReal.mono_measure hmono))
      (by
        filter_upwards [hae] with r hr
        exact hr.2.1)]
    exact lintegral_congr_ae (by
      filter_upwards [hae] with r hr
      exact hr.2.2)
  rw [hQ]
  refine tendsto_atTop_iSup fun m n hmn => lintegral_mono_ae ?_
  filter_upwards [hae] with r hr
  exact hr.2.1 hmn

theorem DissData.delta_identity (D : DissData h u T A K) {δ : ℝ} (hδ : 0 < δ)
    {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (ht : t ≤ T)
    (hVs : Integrable (fun x => V x * u s x) (haar d))
    (hVt : Integrable (fun x => V x * u t x) (haar d))
    (hE : ∫ x, entReg δ (u t x) ∂haar d - ∫ x, entReg δ (u s x) ∂haar d =
      -∫ r in s..t, ∫ x, entReg2 δ (u r x) * ⟪A (r, x), A (r, x) + K (r, x)⟫ ∂haar d)
    (hV : ∫ x, V x * (u t x - u s x) ∂haar d =
      -∫ r in s..t, ∫ x, ⟪G x, A (r, x) + K (r, x)⟫ ∂haar d)
    (hW : 1 / 2 * (quadE W (u t) - quadE W (u s)) =
      -∫ r in s..t, ∫ x, ⟪∫ y, u r y • B x y ∂haar d, A (r, x) + K (r, x)⟫ ∂haar d) :
    (∫ x, entReg δ (u t x) ∂haar d + ∫ x, V x * u t x ∂haar d + 1 / 2 * quadE W (u t)) -
      (∫ x, entReg δ (u s x) ∂haar d + ∫ x, V x * u s x ∂haar d + 1 / 2 * quadE W (u s)) =
    -∫ r in s..t, (Mdel u (fun p => A p + K p) δ r + Rdel G B u (fun p => A p + K p) δ r) := by
  have hsub : Ioc s t ⊆ Icc 0 T := fun r hr => ⟨hs.trans hr.1.le, hr.2.trans ht⟩
  have ii : ∀ {f : ℝ → ℝ}, Integrable f (volume.restrict (Icc (0 : ℝ) T)) →
      IntervalIntegrable f volume s t := fun hf =>
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hst).2
      (IntegrableOn.mono_set (show IntegrableOn _ (Icc (0 : ℝ) T) volume from hf) hsub)
  have hVd : ∫ x, V x * (u t x - u s x) ∂haar d = ∫ x, V x * u t x ∂haar d - ∫ x, V x * u s x ∂haar d := by
    rw [← integral_sub hVt hVs]
    exact integral_congr_ae (Eventually.of_forall fun x => by ring)
  rw [hVd] at hV
  have hsum : ∫ r in s..t, (Mdel u (fun p => A p + K p) δ r + Rdel G B u (fun p => A p + K p) δ r) =
      (∫ r in s..t, ∫ x, entReg2 δ (u r x) * ⟪A (r, x), A (r, x) + K (r, x)⟫ ∂haar d) +
      (∫ r in s..t, ∫ x, ⟪G x, A (r, x) + K (r, x)⟫ ∂haar d) +
      (∫ r in s..t, ∫ x, ⟪∫ y, u r y • B x y ∂haar d, A (r, x) + K (r, x)⟫ ∂haar d) := by
    rw [← intervalIntegral.integral_add (ii (D.integrable_f1 hδ)) (ii D.integrable_f2),
      ← intervalIntegral.integral_add ((ii (D.integrable_f1 hδ)).add (ii D.integrable_f2))
        (ii D.integrable_f3)]
    rw [intervalIntegral.integral_of_le hst, intervalIntegral.integral_of_le hst]
    refine setIntegral_congr_ae measurableSet_Ioc ?_
    have h2 := (ae_restrict_iff' (measurableSet_Ioc (a := s) (b := t))).1
      (ae_restrict_of_ae_restrict_of_subset hsub (D.slice_sum hδ))
    filter_upwards [h2] with r hr hrm
    exact (hr hrm).symm
  rw [hsum]
  linarith

/-- The free energy `F(f) = ∫ f log f + ∫ V f + ½ ∬ W f f`. -/
noncomputable def freeEnergy (V : Torus d → ℝ) (W : Torus d → Torus d → ℝ) (f : Torus d → ℝ) : ℝ :=
  ∫ x, f x * Real.log (f x) ∂haar d + ∫ x, V x * f x ∂haar d + 1 / 2 * quadE W f

/-- The identity hypotheses of `regularised_free_energy_identity`, for all `δ`. -/
def RegIdentity (u : ℝ → L2s d) (G : Torus d → Tangent d) (B : Torus d → Torus d → Tangent d)
    (V : Torus d → ℝ) (W : Torus d → Torus d → ℝ) (A K : ℝ × Torus d → Tangent d) (T : ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ T →
    (∫ x, entReg δ (u t x) ∂haar d - ∫ x, entReg δ (u s x) ∂haar d =
      -∫ r in s..t, ∫ x, entReg2 δ (u r x) * ⟪A (r, x), A (r, x) + K (r, x)⟫ ∂haar d) ∧
    (∫ x, V x * (u t x - u s x) ∂haar d =
      -∫ r in s..t, ∫ x, ⟪G x, A (r, x) + K (r, x)⟫ ∂haar d) ∧
    (1 / 2 * (∫ p, W p.1 p.2 * (u t p.1 * u t p.2) ∂(haar d).prod (haar d) -
        ∫ p, W p.1 p.2 * (u s p.1 * u s p.2) ∂(haar d).prod (haar d)) =
      -∫ r in s..t, ∫ x, ⟪∫ y, u r y • B x y ∂haar d, A (r, x) + K (r, x)⟫ ∂haar d)

theorem DissData.tendsto_M_integral (D : DissData h u T A K) {V : Torus d → ℝ}
    {W : Torus d → Torus d → ℝ}
    (hVint : ∀ t ∈ Icc (0 : ℝ) T, Integrable (fun x => V x * u t x) (haar d))
    (H : RegIdentity u G B V W A K T) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ T) :
    Tendsto (fun n => ∫ r in s..t, Mdel u (fun p => A p + K p) (dissDelta n) r) atTop
      (𝓝 (freeEnergy V W (u s) - freeEnergy V W (u t))) := by
  obtain ⟨M, hM⟩ := D.setting.bdd
  have hsI : s ∈ Icc (0 : ℝ) T := ⟨hs, hst.trans ht⟩
  have htI : t ∈ Icc (0 : ℝ) T := ⟨hs.trans hst, ht⟩
  have hsub : Ioc s t ⊆ Icc 0 T := fun r hr => ⟨hs.trans hr.1.le, hr.2.trans ht⟩
  have ii : ∀ {f : ℝ → ℝ}, Integrable f (volume.restrict (Icc (0 : ℝ) T)) →
      IntervalIntegrable f volume s t := fun hf =>
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hst).2
      (IntegrableOn.mono_set (show IntegrableOn _ (Icc (0 : ℝ) T) volume from hf) hsub)
  have hE : ∀ τ ∈ Icc (0 : ℝ) T, Tendsto (fun n => ∫ x, entReg (dissDelta n) (u τ x) ∂haar d)
      atTop (𝓝 (∫ x, u τ x * Real.log (u τ x) ∂haar d)) := fun τ hτ =>
    tendsto_entReg_integral (Lp.aestronglyMeasurable (u τ)) (D.nonneg τ hτ) (hM τ hτ)
  have hF : ∀ n, ∫ r in s..t, Mdel u (fun p => A p + K p) (dissDelta n) r =
      (∫ x, entReg (dissDelta n) (u s x) ∂haar d + ∫ x, V x * u s x ∂haar d +
        1 / 2 * quadE W (u s)) -
      (∫ x, entReg (dissDelta n) (u t x) ∂haar d + ∫ x, V x * u t x ∂haar d +
        1 / 2 * quadE W (u t)) -
      ∫ r in s..t, Rdel G B u (fun p => A p + K p) (dissDelta n) r := by
    intro n
    obtain ⟨h1, h2, h3⟩ := H (dissDelta n) (dissDelta_pos n) s t hs hst ht
    have := D.delta_identity (dissDelta_pos n) hs hst ht (hVint s hsI) (hVint t htI) h1 h2 h3
    rw [intervalIntegral.integral_add (ii (D.integrable_M (dissDelta_pos n)))
      (ii (D.integrable_R (dissDelta_pos n)))] at this
    linarith
  simp only [hF]
  have hR := D.tendsto_R_integral hs hst ht
  have hlim := ((((hE s hsI).add_const (∫ x, V x * u s x ∂haar d)).add_const
    (1 / 2 * quadE W (u s))).sub (((hE t htI).add_const (∫ x, V x * u t x ∂haar d)).add_const
    (1 / 2 * quadE W (u t)))).sub hR
  simpa [freeEnergy] using hlim

theorem DissData.lintegral_Q (D : DissData h u T A K) {V : Torus d → ℝ}
    {W : Torus d → Torus d → ℝ}
    (hVint : ∀ t ∈ Icc (0 : ℝ) T, Integrable (fun x => V x * u t x) (haar d))
    (H : RegIdentity u G B V W A K T) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ T) :
    0 ≤ freeEnergy V W (u s) - freeEnergy V W (u t) ∧
    ∫⁻ r in Ioc s t, Qdis u (fun p => A p + K p) r =
      ENNReal.ofReal (freeEnergy V W (u s) - freeEnergy V W (u t)) := by
  have hsub : Ioc s t ⊆ Icc 0 T := fun r hr => ⟨hs.trans hr.1.le, hr.2.trans ht⟩
  have hlim := D.tendsto_M_integral hVint H hs hst ht
  have hnn : 0 ≤ freeEnergy V W (u s) - freeEnergy V W (u t) := by
    refine ge_of_tendsto hlim (Eventually.of_forall fun n => ?_)
    rw [intervalIntegral.integral_of_le hst]
    exact integral_nonneg_of_ae (ae_restrict_of_ae_restrict_of_subset hsub
      (D.nonneg_M (dissDelta_pos n)))
  refine ⟨hnn, ?_⟩
  exact tendsto_nhds_unique (D.tendsto_lintegral_Q hs hst ht)
    (ENNReal.tendsto_ofReal hlim)

theorem DissData.slice_bound (D : DissData h u T A K) :
    ∀ᵐ r ∂(volume.restrict (Icc (0 : ℝ) T)),
      Qdis u (fun p => A p + K p) r < ⊤ → ∀ ψ : Torus d → Tangent d, (∀ x, ‖ψ x‖ ≤ 1) →
        ‖∫ x, ⟪A (r, x) + K (r, x), ψ x⟫ ∂haar d‖ ≤
          Real.sqrt ((Qdis u (fun p => A p + K p) r).toReal) := by
  filter_upwards [D.slice, ae_restrict_mem measurableSet_Icc] with r S hrI hQ ψ hψ
  have hJi : Integrable (fun x => ‖A (r, x) + K (r, x)‖) (haar d) :=
    (S.memLp_J.integrable one_le_two).norm
  have h1 : ‖∫ x, ⟪A (r, x) + K (r, x), ψ x⟫ ∂haar d‖ ≤ ∫ x, ‖A (r, x) + K (r, x)‖ ∂haar d := by
    refine norm_integral_le_of_norm_le hJi (Eventually.of_forall fun x => ?_)
    refine (norm_inner_le_norm _ _).trans ?_
    calc ‖A (r, x) + K (r, x)‖ * ‖ψ x‖ ≤ ‖A (r, x) + K (r, x)‖ * 1 :=
          mul_le_mul_of_nonneg_left (hψ x) (norm_nonneg _)
      _ = _ := mul_one _
  refine h1.trans ?_
  have h2 := S.integral_norm_le hQ.ne (D.mass r hrI)
  rw [← S.toReal_Q] at h2
  exact h2

theorem DissData.smooth_test_bound (D : DissData h u T A K) {φ : Torus d → ℝ}
    (hφ : IsSmoothPeriodic φ) (hb : ∀ x, ‖smoothGrad φ x‖ ≤ 1) {s t : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) (ht : t ≤ T)
    (hlt : ∀ᵐ r ∂(volume.restrict (Icc (0 : ℝ) T)), Qdis u (fun p => A p + K p) r < ⊤)
    (hg : IntervalIntegrable (fun r => Real.sqrt ((Qdis u (fun p => A p + K p) r).toReal))
      volume s t) :
    |∫ x, u t x * φ x ∂haar d - ∫ x, u s x * φ x ∂haar d| ≤
      ∫ r in s..t, Real.sqrt ((Qdis u (fun p => A p + K p) r).toReal) := by
  obtain ⟨-, hw⟩ := weakForm_H1 D.setting.div (fun t _ => Lp.memLp (u t)) D.memJ
    hφ.isWeakGradient hs hst ht
  rw [hw, abs_neg]
  have hae := (ae_restrict_iff' measurableSet_Icc).1 (D.slice_bound.and hlt)
  have := intervalIntegral.norm_integral_le_of_norm_le hst (f := fun r => ∫ x, ⟪A (r, x) + K (r, x), smoothGrad φ x⟫ ∂haar d)
    (g := fun r => Real.sqrt ((Qdis u (fun p => A p + K p) r).toReal)) ?_ hg
  · simpa [Real.norm_eq_abs] using this
  · filter_upwards [hae] with r hr hrI
    have hrI' : r ∈ Icc (0 : ℝ) T := ⟨hs.trans hrI.1.le, hrI.2.trans ht⟩
    obtain ⟨hr1, hr2⟩ := hr hrI'
    exact hr1 hr2 _ hb

theorem DissData.lip_bound (D : DissData h u T A K) {f : Torus d → ℝ}
    (hf : TorusLipschitzWith 1 f) {s t : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) (ht : t ≤ T)
    (hlt : ∀ᵐ r ∂(volume.restrict (Icc (0 : ℝ) T)), Qdis u (fun p => A p + K p) r < ⊤)
    (hg : IntervalIntegrable (fun r => Real.sqrt ((Qdis u (fun p => A p + K p) r).toReal))
      volume s t) :
    |∫ x, u t x * f x ∂haar d - ∫ x, u s x * f x ∂haar d| ≤
      ∫ r in s..t, Real.sqrt ((Qdis u (fun p => A p + K p) r).toReal) := by
  have hfc := continuous_of_torusLipschitz zero_le_one hf
  have hfi : Integrable f (haar d) := integrable_of_continuous_torus hfc
  have hf2 : MemLp f 2 (haar d) := memLp_two_of_continuous hfc
  have hδ : Tendsto dissDelta atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_dissDelta, Eventually.of_forall dissDelta_pos⟩
  have hT : ∀ τ : ℝ, Tendsto (fun n => ∫ x, u τ x * heatOp (dissDelta n) f x ∂haar d) atTop
      (𝓝 (∫ x, u τ x * f x ∂haar d)) := by
    intro τ
    have := (tendsto_integral_mul_heatOp hf2 (Lp.memLp (u τ))).comp hδ
    simp only [mul_comm] at this ⊢
    exact this
  have hlim := ((hT t).sub (hT s)).abs
  refine le_of_tendsto' hlim fun n => ?_
  exact D.smooth_test_bound (isSmoothPeriodic_heatOp (dissDelta_pos n) hfi)
    (fun x => norm_smoothGrad_heatOp_le (dissDelta_pos n) hf x) hs hst ht hlt hg

theorem DissData.main (D : DissData h u T A K) {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ}
    (hVint : ∀ t ∈ Icc (0 : ℝ) T, Integrable (fun x => V x * u t x) (haar d))
    (H : RegIdentity u G B V W A K T) :
    ∃ Dd : ℝ → ℝ,
      (∀ᵐ r ∂(volume.restrict (Icc (0 : ℝ) T)), ∃ w : Torus d → Tangent d,
        IsWeakGradient (fun x => Real.sqrt (u r x)) w ∧
        Dd r = ∫ x, ‖(2 : ℝ) • w x + Real.sqrt (u r x) • (G x + ∫ y, u r y • B x y ∂haar d)‖ ^ 2
          ∂haar d) ∧
      (∀ r, 0 ≤ Dd r) ∧ AEStronglyMeasurable Dd (volume.restrict (Icc (0 : ℝ) T)) ∧
      Integrable Dd (volume.restrict (Icc (0 : ℝ) T)) ∧
      (∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ T →
        freeEnergy V W (u t) + ∫ r in s..t, Dd r = freeEnergy V W (u s)) ∧
      (∀ f : Torus d → ℝ, TorusLipschitzWith 1 f → ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ T →
        |∫ x, u t x * f x ∂haar d - ∫ x, u s x * f x ∂haar d| ≤
          ∫ r in s..t, Real.sqrt (Dd r)) := by
  have hT := D.T_nonneg
  have hfin : ∫⁻ r in Icc (0 : ℝ) T, Qdis u (fun p => A p + K p) r ≠ ⊤ := by
    obtain ⟨-, hQ⟩ := D.lintegral_Q hVint H le_rfl hT le_rfl
    rw [← setLIntegral_congr Ioc_ae_eq_Icc, hQ]
    exact ENNReal.ofReal_ne_top
  have hlt : ∀ᵐ r ∂(volume.restrict (Icc (0 : ℝ) T)), Qdis u (fun p => A p + K p) r < ⊤ :=
    ae_lt_top' D.aemeas_Q hfin
  refine ⟨fun r => (Qdis u (fun p => A p + K p) r).toReal, ?_, fun r => ENNReal.toReal_nonneg,
    D.aemeas_Q.ennreal_toReal.aestronglyMeasurable,
    integrable_toReal_of_lintegral_ne_top D.aemeas_Q hfin, ?_, ?_⟩
  · filter_upwards [D.slice, hlt] with r S hQ'
    obtain ⟨w, hw, hw2⟩ := S.sqrt_H1 hQ'.ne
    refine ⟨w, hw, ?_⟩
    have hnn : 0 ≤ᵐ[haar d] fun x => ‖A (r, x) + K (r, x)‖ ^ 2 / u r x := by
      filter_upwards [S.nonneg] with x hx
      have : 0 ≤ u r x := hx
      positivity
    have := integral_eq_lintegral_of_nonneg_ae hnn
      ((S.aemeas_M 0).aestronglyMeasurable.congr (by simp))
    show (∫⁻ x, ENNReal.ofReal (‖A (r, x) + K (r, x)‖ ^ 2 / u r x) ∂haar d).toReal = _
    rw [← this]
    exact integral_congr_ae (hw2.mono fun x hx => hx.symm)
  · intro s t hs hst ht
    obtain ⟨hnn, hQ⟩ := D.lintegral_Q hVint H hs hst ht
    have hsub : Ioc s t ⊆ Icc 0 T := fun r hr => ⟨hs.trans hr.1.le, hr.2.trans ht⟩
    have hmono : (volume.restrict (Ioc s t)) ≤ (volume.restrict (Icc (0 : ℝ) T)) :=
      Measure.restrict_mono hsub le_rfl
    have : ∫ r in s..t, (Qdis u (fun p => A p + K p) r).toReal =
        freeEnergy V W (u s) - freeEnergy V W (u t) := by
      rw [intervalIntegral.integral_of_le hst,
        integral_toReal (D.aemeas_Q.mono_measure hmono)
          (ae_restrict_of_ae_restrict_of_subset hsub hlt), hQ, ENNReal.toReal_ofReal hnn]
    rw [this]
    ring
  · intro f hf s t hs hst ht
    have hDi : Integrable (fun r => (Qdis u (fun p => A p + K p) r).toReal)
        (volume.restrict (Icc (0 : ℝ) T)) :=
      integrable_toReal_of_lintegral_ne_top D.aemeas_Q hfin
    have hsq : Integrable (fun r => Real.sqrt ((Qdis u (fun p => A p + K p) r).toReal))
        (volume.restrict (Icc (0 : ℝ) T)) := by
      refine Integrable.mono' (hDi.add (integrable_const (1 : ℝ)))
        (Real.continuous_sqrt.comp_aestronglyMeasurable
          D.aemeas_Q.ennreal_toReal.aestronglyMeasurable)
        (Eventually.of_forall fun r => ?_)
      have hx : 0 ≤ (Qdis u (fun p => A p + K p) r).toReal := ENNReal.toReal_nonneg
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), Pi.add_apply]
      nlinarith [Real.sq_sqrt hx, sq_nonneg (Real.sqrt (Qdis u (fun p => A p + K p) r).toReal - 1)]
    have hsub : Ioc s t ⊆ Icc 0 T := fun r hr => ⟨hs.trans hr.1.le, hr.2.trans ht⟩
    have hsq' : IntegrableOn
        (fun r => Real.sqrt ((Qdis u (fun p => A p + K p) r).toReal)) (Icc (0 : ℝ) T) volume := hsq
    have hg : IntervalIntegrable
        (fun r => Real.sqrt ((Qdis u (fun p => A p + K p) r).toReal)) volume s t :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hst).2 (hsq'.mono_set hsub)
    exact D.lip_bound hf hs hst ht hlt hg

/-- **LIP030, exact free energy dissipation identity** (parts 1 and 2).  For the global
probability flow `u` of the mean-field equation with drift `G + B ∗ u`, and `F = ∫ f log f +
∫ V f + ½ ∬ W f f`, there is a measurable integrable `D ≥ 0` on `[0,T]` such that
`F(u_t) + ∫_s^t D = F(u_s)` for all `0 ≤ s ≤ t ≤ T`; for a.e. `r`, `√u_r ∈ H¹` with weak gradient
`w` and `D r = ∫ ‖2 w + √u_r (G + B ∗ u_r)‖²`, the square-root dissipation. -/
theorem exact_free_energy_dissipation_identity_on_the_absolute_domain
    (h : MeanFieldData G B g b) {ρ0 : L2s d} {u : ℝ → L2s d} (hu : IsGlobalProbFlow h ρ0 u)
    {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ}
    (hV : IsWeakGradient V G)
    (hWc : Continuous fun p : Torus d × Torus d => W p.1 p.2)
    (hsym : ∀ x y, W x y = W y x)
    (hWB : ∀ᵐ y ∂haar d, IsWeakGradientLp ∞ (fun x => W x y) (fun x => B x y))
    {T : ℝ} (hT : 0 ≤ T) :
    ∃ Dd : ℝ → ℝ,
      (∀ᵐ r ∂(volume.restrict (Icc (0 : ℝ) T)), ∃ w : Torus d → Tangent d,
        IsWeakGradient (fun x => Real.sqrt (u r x)) w ∧
        Dd r = ∫ x, ‖(2 : ℝ) • w x + Real.sqrt (u r x) • (G x + ∫ y, u r y • B x y ∂haar d)‖ ^ 2
          ∂haar d) ∧
      (∀ r, 0 ≤ Dd r) ∧ AEStronglyMeasurable Dd (volume.restrict (Icc (0 : ℝ) T)) ∧
      Integrable Dd (volume.restrict (Icc (0 : ℝ) T)) ∧
      (∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ T →
        freeEnergy V W (u t) + ∫ r in s..t, Dd r = freeEnergy V W (u s)) ∧
      (∀ f : Torus d → ℝ, TorusLipschitzWith 1 f → ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ T →
        |∫ x, u t x * f x ∂haar d - ∫ x, u s x * f x ∂haar d| ≤
          ∫ r in s..t, Real.sqrt (Dd r)) := by
  obtain ⟨A, K, hAm, hA2, hKm, hK2, hSet, hgrad, hKe, hid⟩ :=
    regularised_free_energy_identity h hu hV hWc hsym hWB hT
  have hD : DissData h u T A K :=
    { T_nonneg := hT
      cont := hu.cont.mono fun r hr => hr.1
      nonneg := fun r hr => hu.nonneg r hr.1
      mass := fun r hr => hu.mass r hr.1
      measA := hAm
      measK := hKm
      memA := hA2
      memK := hK2
      setting := hSet
      grad := hgrad
      Ke := hKe }
  refine hD.main (fun t _ => ?_) hid
  have := (Lp.memLp (u t)).integrable_mul hV.memLp
  exact this.congr (Eventually.of_forall fun x => mul_comm _ _)

end Assembly

end DGPS.Lipschitz
