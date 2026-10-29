import SharpSymmetricLSI.Paper.H1Config

/-!
# Weak-gradient tensorization (Phase 2, I1, milestone 4)

For `h` on `𝕋^d` with weak gradient `g`, the function `y ↦ h(y_i)` on `𝕋^{N×d}` (`y_i` the
`i`-th block) has weak gradient `g(y_i)` in block `i` and `0` in the other blocks
(`isWeakGrad_comp_projBlock`). On configuration spaces: `X ↦ h(X i)` is in `H¹(P_N)` for
`h ∈ H¹(m)`, with `ℰ_N = ∫ |∇h(X i)|² dP_N` (`memH1C_comp_eval`, `energy_comp_eval`).
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

namespace SharpLSI

variable {N d : ℕ}

/-- The `i`-th block `y ↦ y_i` of `𝕋^{N×d}`. -/
def projBlock (i : Fin N) (y : UnitAddTorus (Fin N × Fin d)) : UnitAddTorus (Fin d) :=
  fun k => y (i, k)

theorem measurable_projBlock (i : Fin N) : Measurable (projBlock (d := d) i) :=
  measurable_pi_iff.mpr fun k => measurable_pi_apply (i, k)

theorem measurePreserving_projBlock (i : Fin N) :
    MeasurePreserving (projBlock (d := d) i) volume volume := by
  refine ⟨measurable_projBlock i, ?_⟩
  rw [← map_flat_volume N, Measure.map_map (measurable_projBlock i) measurable_flat]
  exact (measurePreserving_eval (fun _ : Fin N => (volume : Measure (Torus d))) i).map_eq

/-- The block projection on `ℝ^{N×d}`, as a continuous linear map. -/
noncomputable def projBlockL (i : Fin N) : (Fin N × Fin d → ℝ) →L[ℝ] (Fin d → ℝ) :=
  ContinuousLinearMap.pi fun k => ContinuousLinearMap.proj (i, k)

theorem projBlockL_apply (i : Fin N) (x : Fin N × Fin d → ℝ) :
    projBlockL i x = fun k => x (i, k) := rfl

theorem projBlock_liftT (i : Fin N) (x : Fin N × Fin d → ℝ) :
    projBlock i (liftT x) = liftT (projBlockL i x) := rfl

theorem projBlockL_single (i : Fin N) (p : Fin N × Fin d) :
    projBlockL i (Pi.single p 1) = if p.1 = i then Pi.single p.2 1 else 0 := by
  funext k
  simp only [projBlockL_apply]
  split_ifs with hp
  · obtain ⟨p1, p2⟩ := p
    simp only at hp; subst hp
    simp [Pi.single_apply, Prod.ext_iff, eq_comm]
  · obtain ⟨p1, p2⟩ := p
    simp only at hp
    simp [Pi.single_apply, Prod.ext_iff, Ne.symm hp]

theorem integrable_comp_projBlock (i : Fin N) {u : UnitAddTorus (Fin d) → ℝ}
    (hu : Integrable u volume) : Integrable (u ∘ projBlock i) volume :=
  (measurePreserving_projBlock i).integrable_comp_of_integrable hu

theorem lintegral_comp_projBlock (i : Fin N) {F : UnitAddTorus (Fin d) → ℝ≥0∞}
    (hF : AEMeasurable F volume) : ∫⁻ y, F (projBlock i y) = ∫⁻ x, F x := by
  rw [← lintegral_map' (by rwa [(measurePreserving_projBlock i).map_eq])
    (measurable_projBlock i).aemeasurable, (measurePreserving_projBlock i).map_eq]

/-- **Tensorization of weak gradients.** -/
theorem isWeakGrad_comp_projBlock (i : Fin N) {u : UnitAddTorus (Fin d) → ℝ}
    {g : UnitAddTorus (Fin d) → Fin d → ℝ} (h : IsWeakGrad u g) (hu : Integrable u volume)
    (hg : ∀ k, Integrable (fun x => g x k) volume) :
    IsWeakGrad (fun y => u (projBlock i y))
      (fun y p => if p.1 = i then g (projBlock i y) p.2 else 0) := by
  set F : ℕ → UnitAddTorus (Fin N × Fin d) → ℝ := fun n y => moll n u (projBlock i y) with hF
  set G : ℕ → UnitAddTorus (Fin N × Fin d) → Fin N × Fin d → ℝ :=
    fun n y p => if p.1 = i then moll n (fun x => g x p.2) (projBlock i y) else 0 with hG
  have hpair : ∀ n, IsWeakGrad (F n) (G n) := by
    intro n
    have hΨ : ContDiff ℝ ∞ (moll n u ∘ liftT) := moll_comp_liftT_contDiff n hu
    have hs : ContDiff ℝ 1 (F n ∘ liftT) := by
      have : F n ∘ liftT = (moll n u ∘ liftT) ∘ projBlockL i := by
        funext x; simp [hF, Function.comp, projBlock_liftT]
      rw [this]; exact (hΨ.of_le (by simp)).comp (projBlockL i).contDiff
    have hc := isWeakGrad_of_contDiff hs
    convert hc using 1
    funext y p
    have hd := (((hΨ.differentiable (by simp)) (projBlockL i (secT y))).hasFDerivAt).comp
      (secT y) (projBlockL i).hasFDerivAt
    rw [show F n ∘ liftT = (moll n u ∘ liftT) ∘ projBlockL i by
      funext x; simp [hF, Function.comp, projBlock_liftT], hd.fderiv]
    simp only [ContinuousLinearMap.comp_apply, projBlockL_single]
    by_cases hp : p.1 = i
    · simp only [hG, hp, ↓reduceIte]
      rw [moll_comp_liftT, fderiv_mollL_of_isWeakGrad h n _ p.2]
      have : liftT (projBlockL i (secT y)) = projBlock i y := by
        rw [← projBlock_liftT, liftT_secT]
      rw [← this]
      exact congrFun (moll_comp_liftT n (fun x => g x p.2)) _
    · simp [hG, hp]
  have hmeas_u := hu.aestronglyMeasurable
  refine isWeakGrad_of_tendsto hpair (fun n => integrable_comp_projBlock i (integrable_moll n hu))
    (fun n p => ?_) (integrable_comp_projBlock i hu) (fun p => ?_) ?_ (fun p => ?_)
  · by_cases hp : p.1 = i
    · simp only [hG, hp, ↓reduceIte]
      exact integrable_comp_projBlock i (integrable_moll n (hg p.2))
    · simp [hG, hp]
  · by_cases hp : p.1 = i
    · simp only [hp, ↓reduceIte]
      exact integrable_comp_projBlock i (hg p.2)
    · simp [hp]
  · refine (tendsto_moll hu).congr fun n => ?_
    exact (lintegral_comp_projBlock i (F := fun x => ‖moll n u x - u x‖ₑ)
      (((measurable_moll n hu).aestronglyMeasurable.sub hmeas_u).enorm)).symm
  · by_cases hp : p.1 = i
    · refine (tendsto_moll (hg p.2)).congr fun n => ?_
      simp only [hG, hp, ↓reduceIte]
      exact (lintegral_comp_projBlock i (F := fun x => ‖moll n (fun x => g x p.2) x - g x p.2‖ₑ)
        (((measurable_moll n (hg p.2)).aestronglyMeasurable.sub
          (hg p.2).aestronglyMeasurable).enorm)).symm
    · simp [hG, hp]

theorem sqNorm_block (i : Fin N) (v : Fin d → ℝ) :
    sqNorm (fun p : Fin N × Fin d => if p.1 = i then v p.2 else 0) = sqNorm v := by
  unfold sqNorm
  calc ∑ p : Fin N × Fin d, (if p.1 = i then v p.2 else 0) ^ 2
      = ∑ j : Fin N, ∑ k : Fin d, (if j = i then v k else 0) ^ 2 := Fintype.sum_prod_type _
    _ = ∑ k, v k ^ 2 := by simp [ite_pow, Finset.sum_ite_irrel]

/-! ### Configuration spaces -/

variable {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

theorem gibbs_map_flat_le (hyp : Hyp V W KV KW) (N : ℕ) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ (gibbs V W N).map flat ≤ C • (volume : Measure (UnitAddTorus (Fin N × Fin d))) := by
  obtain ⟨C, hC, hle⟩ := exists_gibbsDensity_upper hyp N
  refine ⟨C, hC, ?_⟩
  rw [← map_flat_volume N, ← Measure.map_smul]
  on_goal 2 => exact measurable_flat.aemeasurable
  refine Measure.map_mono ?_ measurable_flat
  rw [show gibbs V W N = (volume : Measure (Config N d)).withDensity
      (gibbsDensity volume (hamiltonian V W N)) from rfl, ← withDensity_const]
  exact withDensity_mono (Eventually.of_forall hle)

theorem memLp_gibbs_of_haar (hyp : Hyp V W KV KW) {u : UnitAddTorus (Fin N × Fin d) → ℝ}
    (hu : MemLp u 2 volume) : MemLp u 2 ((gibbs V W N).map flat) := by
  obtain ⟨C, hC, hle⟩ := gibbs_map_flat_le hyp N
  exact hu.of_measure_le_smul hC hle

theorem integrable_of_memH1_haar {ι : Type*} [Fintype ι] [DecidableEq ι] {h : UnitAddTorus ι → ℝ}
    (hh : MemH1 volume h) :
    Integrable h volume ∧ ∀ k, Integrable (fun x => weakGrad h x k) volume := by
  have hw := isWeakGrad_weakGrad hh.1
  refine ⟨memLp_one_iff_integrable.mp (hh.2.1.mono_exponent (by norm_num)), fun k => ?_⟩
  refine memLp_one_iff_integrable.mp (MemLp.mono_exponent ?_ (by norm_num : (1 : ℝ≥0∞) ≤ 2))
  refine hh.2.2.of_le (hw.aestronglyMeasurable_grad k) (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact abs_le_sqrt_sqNorm _ k

/-- `X ↦ h(X i)` is in `H¹(P_N)` for `h ∈ H¹(m)`. -/
theorem memH1C_comp_eval (hyp : Hyp V W KV KW) (i : Fin N) {h : Torus d → ℝ}
    (hh : MemH1 (haar d) h) : MemH1C (gibbs V W N) (fun X => h (X i)) := by
  have hw := isWeakGrad_weakGrad hh.1
  obtain ⟨hi, hgi⟩ := integrable_of_memH1_haar hh
  have hT := isWeakGrad_comp_projBlock (N := N) i hw hi hgi
  refine ⟨⟨_, hT⟩, memLp_gibbs_of_haar hyp
    (hh.2.1.comp_measurePreserving (measurePreserving_projBlock i)), ?_⟩
  refine memLp_gibbs_of_haar hyp ?_
  refine (hh.2.2.comp_measurePreserving (measurePreserving_projBlock (N := N) i)).ae_eq ?_
  filter_upwards [weakGrad_ae_eq hT] with y hy
  change Real.sqrt (sqNorm (weakGrad h (projBlock i y))) =
    Real.sqrt (sqNorm (weakGrad (fun y => h (projBlock i y)) y))
  rw [hy, sqNorm_block]

/-- `ℰ_N(h(X i)) = ∫ |∇h(X i)|² dP_N`. -/
theorem energy_comp_eval (hyp : Hyp V W KV KW) (i : Fin N) {h : Torus d → ℝ}
    (hh : MemH1 (haar d) h) :
    energy V W N (fun X => h (X i)) =
      ∫⁻ X, ENNReal.ofReal (sqNorm (weakGrad h (X i))) ∂gibbs V W N := by
  have hw := isWeakGrad_weakGrad hh.1
  obtain ⟨hi, hgi⟩ := integrable_of_memH1_haar hh
  have hT := isWeakGrad_comp_projBlock (N := N) i hw hi hgi
  have hac := (gibbs_map_flat_ac hyp N).1
  rw [energy_eq hyp ⟨_, hT⟩]
  have hm : AEMeasurable (fun y => ENNReal.ofReal (sqNorm (weakGrad h (projBlock i y))))
      ((gibbs V W N).map flat) :=
    (ENNReal.measurable_ofReal.comp_aemeasurable
      (hw.aestronglyMeasurable_sqNorm.comp_measurePreserving
        (measurePreserving_projBlock (N := N) i)).aemeasurable).mono_ac hac
  rw [lintegral_congr_ae (g := fun y => ENNReal.ofReal (sqNorm (weakGrad h (projBlock i y))))
    (by
      filter_upwards [hac.ae_le (weakGrad_ae_eq hT)] with y hy
      change ENNReal.ofReal (sqNorm (weakGrad (fun y => h (projBlock i y)) y)) = _
      rw [hy, sqNorm_block]),
    lintegral_map' hm measurable_flat.aemeasurable]
  rfl

end SharpLSI
