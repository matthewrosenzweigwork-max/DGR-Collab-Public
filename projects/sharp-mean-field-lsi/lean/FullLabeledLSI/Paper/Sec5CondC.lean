import FullLabeledLSI.Paper.Sec5CondA

/-!
# Conditional laws for a random subset, part C: weak gradients
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal

namespace SharpLSI.FL

variable {d N : ℕ}


/-! ### Reshaping and the index equivalence -/

section reshape

/-- A family of points of `𝕋^d` as a point of `𝕋^{ι × d}`. -/
def flatG {ι : Type*} (a : ι → Torus d) : UnitAddTorus (ι × Fin d) := fun p => a p.1 p.2

theorem measurable_flatG {ι : Type*} [Fintype ι] :
    Measurable (flatG (ι := ι) (d := d)) :=
  measurable_pi_iff.mpr fun p =>
    (measurable_pi_apply (X := fun _ : Fin d => UnitAddCircle) p.2).comp
      (measurable_pi_apply (X := fun _ : ι => Torus d) p.1)

/-- `flatG` as a measurable equivalence. -/
def flatGEquiv (ι : Type*) [Fintype ι] : (ι → Torus d) ≃ᵐ UnitAddTorus (ι × Fin d) where
  toFun := flatG
  invFun y i k := y (i, k)
  left_inv _ := rfl
  right_inv _ := rfl
  measurable_toFun := measurable_flatG
  measurable_invFun := measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun k =>
    measurable_pi_apply (i, k)

theorem measurePreserving_flatG {ι : Type*} [Fintype ι] :
    MeasurePreserving (flatG (ι := ι) (d := d)) volume volume := by
  refine ⟨measurable_flatG, ?_⟩
  symm
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.map_apply measurable_flatG (MeasurableSet.univ_pi hs)]
  have : (flatG : (ι → Torus d) → _) ⁻¹' Set.univ.pi s =
      Set.univ.pi fun i => Set.univ.pi fun k => s (i, k) := by
    ext X; simp [flatG, Set.mem_pi, Prod.forall]
  rw [this]
  change (Measure.pi fun _ : ι => Measure.pi fun _ : Fin d => (volume : Measure UnitAddCircle))
    (Set.univ.pi fun i => Set.univ.pi fun k => s (i, k)) = _
  rw [Measure.pi_pi]
  simp_rw [Measure.pi_pi]
  rw [← Fintype.prod_prod_type']

theorem integral_flatG_comp {ι : Type*} [Fintype ι] (g : UnitAddTorus (ι × Fin d) → ℝ) :
    ∫ z, g (flatG z) ∂(volume : Measure (ι → Torus d)) = ∫ y, g y :=
  measurePreserving_flatG.integral_comp (flatGEquiv ι).measurableEmbedding g

/-- The block index equivalence for `S`, `{i}` and the rest. -/
def idxEquivS {S : Finset (Fin N)} {i : Fin N} (hi : i ∉ S) :
    ((S × Fin d) ⊕ Fin d) ⊕ (RestIdx S i × Fin d) ≃ Fin N × Fin d where
  toFun s := match s with
    | Sum.inl (Sum.inl (a, k)) => (a.1, k)
    | Sum.inl (Sum.inr k) => (i, k)
    | Sum.inr (b, k) => (b.1, k)
  invFun q :=
    if h : q.1 ∈ S then Sum.inl (Sum.inl (⟨q.1, h⟩, q.2))
    else if h' : q.1 = i then Sum.inl (Sum.inr q.2)
    else Sum.inr (⟨q.1, h, h'⟩, q.2)
  left_inv s := by
    rcases s with ((⟨a, k⟩ | k) | ⟨b, k⟩)
    · simp [a.2]
    · simp [hi]
    · simp [b.2.1, b.2.2]
  right_inv q := by
    obtain ⟨k, l⟩ := q
    by_cases h : k ∈ S
    · simp [h]
    · by_cases h' : k = i
      · subst h'; simp [hi]
      · simp [h, h']

theorem reidx_idxEquivS_join {S : Finset (Fin N)} {i : Fin N} (hi : i ∉ S) (a : S → Torus d)
    (x : Torus d) (z : RestIdx S i → Torus d) :
    reidx (idxEquivS (d := d) hi) (join (join (flatG a) x) (flatG z)) =
      flat (assembleS S i a x z) := by
  funext ⟨k, l⟩
  by_cases h : k ∈ S
  · simp [reidx, idxEquivS, h, join, flatG, flat, assembleS]
  · by_cases h' : k = i
    · simp [reidx, idxEquivS, h', hi, join, flat, assembleS]
    · simp [reidx, idxEquivS, h, h', join, flatG, flat, assembleS]

end reshape

/-! ### (T4) Weak gradients of the conditional densities -/

/-- The `x`-gradient of the marginal density, `k`-th component. -/
noncomputable def gradMargS (GQ : UnitAddTorus (Fin N × Fin d) → Fin N × Fin d → ℝ)
    (S : Finset (Fin N)) (i : Fin N) (a : S → Torus d) (x : Torus d) (k : Fin d) : ℝ :=
  ∫ z, GQ (flat (assembleS S i a x z)) (i, k) ∂(volume : Measure (RestIdx S i → Torus d))

/-- The `x`-gradient of the conditional density: `gradMargS / ZcS` (`ZcS` does not depend on `x`). -/
noncomputable def gradCondS (Q : Config N d → ℝ)
    (GQ : UnitAddTorus (Fin N × Fin d) → Fin N × Fin d → ℝ)
    (S : Finset (Fin N)) (i : Fin N) (a : S → Torus d) (x : Torus d) (k : Fin d) : ℝ :=
  gradMargS GQ S i a x k / ZcS Q S i a

section grad
variable {Q : Config N d → ℝ} {c C : ℝ} (hQ : IsBddDens Q c C) {S : Finset (Fin N)} {i : Fin N}
  (hi : i ∉ S) {GQ : UnitAddTorus (Fin N × Fin d) → Fin N × Fin d → ℝ}
  (hQw : IsWeakGrad (Q ∘ unflat) GQ)

include hQ hi hQw in
/-- **For a.e. revealed values, `∇ₓ margQS = gradMargS`** (`SharpLSI.ae_isWeakGrad_margQ`). -/
theorem ae_isWeakGrad_margQS (hGi : ∀ p, Integrable (fun y => GQ y p) volume) :
    ∀ᵐ a ∂(volume : Measure (S → Torus d)), IsWeakGrad (margQS Q S i a) (gradMargS GQ S i a) := by
  have hQi : Integrable (Q ∘ unflat) volume :=
    Integrable.of_bound (hQ.meas.comp measurable_unflat).aestronglyMeasurable C
      (Eventually.of_forall fun y => by
        show ‖Q (unflat y)‖ ≤ C
        rw [Real.norm_eq_abs, abs_of_pos (hQ.pos.trans_le (hQ.lower _))]
        exact hQ.upper _)
  have hb := isWeakGrad_reidx (idxEquivS (d := d) hi) hQw hQi hGi
  have hbi : Integrable (fun y => (Q ∘ unflat) (reidx (idxEquivS (d := d) hi) y)) volume := integrable_comp_reidx (idxEquivS (d := d) hi) hQi
  have hbg : ∀ s, Integrable (fun y => GQ (reidx (idxEquivS (d := d) hi) y) ((idxEquivS (d := d) hi) s)) volume := fun s =>
    integrable_comp_reidx (idxEquivS (d := d) hi) (hGi ((idxEquivS (d := d) hi) s))
  have hm := isWeakGrad_marginal hb hbi hbg
  set M : UnitAddTorus ((S × Fin d) ⊕ Fin d) → ℝ :=
    fun w => ∫ zf, (Q ∘ unflat) (reidx (idxEquivS (d := d) hi) (join w zf)) with hM
  set GM : UnitAddTorus ((S × Fin d) ⊕ Fin d) → ((S × Fin d) ⊕ Fin d) → ℝ :=
    fun w s => ∫ zf, GQ (reidx (idxEquivS (d := d) hi) (join w zf)) ((idxEquivS (d := d) hi) (Sum.inl s)) with hGM
  have hMi : Integrable M volume := integrable_marginal hbi
  have hGMi : ∀ s, Integrable (fun w => GM w s) volume := fun s => integrable_marginal (hbg _)
  set τ := Equiv.sumComm (Fin d) (S × Fin d)
  have hm' := isWeakGrad_reidx τ hm hMi hGMi
  have hs := isWeakGrad_sliceSum hm' (integrable_comp_reidx τ hMi)
    (fun s => integrable_comp_reidx τ (hGMi (τ s)))
  filter_upwards [measurePreserving_flatG.quasiMeasurePreserving.ae hs] with a hp
  convert hp using 1
  · funext x
    rw [reidx_sumComm_join]
    simp only [hM, margQS]
    rw [← integral_flatG_comp]
    simp only [reidx_idxEquivS_join]
    rfl
  · funext x k
    rw [reidx_sumComm_join]
    simp only [hGM, gradMargS]
    rw [← integral_flatG_comp]
    simp only [reidx_idxEquivS_join]
    rfl

include hQ hi hQw in
/-- **For a.e. revealed values, `∇ₓ condDensS = gradCondS`** (`SharpLSI.ae_isWeakGrad_condDens`). -/
theorem ae_isWeakGrad_condDensS (hGi : ∀ p, Integrable (fun y => GQ y p) volume) :
    ∀ᵐ a ∂(volume : Measure (S → Torus d)),
      IsWeakGrad (condDensS Q S i a) (gradCondS Q GQ S i a) := by
  filter_upwards [ae_isWeakGrad_margQS hQ hi hQw hGi] with a hp
  convert hp.cmul (1 / ZcS Q S i a) using 1
  · funext x; unfold condDensS; ring
  · funext x k; unfold gradCondS; ring

theorem measurable_gradMargS (hGm : ∀ p, Measurable fun y => GQ y p) (k : Fin d) :
    Measurable (Function.uncurry fun (a : S → Torus d) (x : Torus d) => gradMargS GQ S i a x k) :=
  (((hGm (i, k)).comp measurable_flat).comp
    (measurable_assembleS S i)).stronglyMeasurable.integral_prod_right'.measurable

include hQ in
theorem measurable_gradCondS (hGm : ∀ p, Measurable fun y => GQ y p) (k : Fin d) :
    Measurable (Function.uncurry fun (a : S → Torus d) (x : Torus d) =>
      gradCondS Q GQ S i a x k) :=
  (measurable_gradMargS (S := S) (i := i) hGm k).div ((measurable_ZcS hQ S i).comp measurable_fst)

include hi in
/-- `gradMargS · k ∈ L²(haar)` for a.e. `a`, if `GQ_{(i,k)} ∈ L²` (`SharpLSI.ae_memLp_gradMarg`);
no hypothesis on `Q` is needed. -/
theorem ae_memLp_gradMargS (hGm : ∀ p, Measurable fun y => GQ y p)
    (hG2 : ∀ p, MemLp (fun y => GQ y p) 2 volume) :
    ∀ᵐ a ∂(volume : Measure (S → Torus d)), ∀ k,
      MemLp (fun x => gradMargS GQ S i a x k) 2 (haar d) := by
  rw [ae_all_iff]
  intro k
  set G := fun y => GQ y (i, k)
  have hGm' : Measurable G := hGm _
  have hG2' := hG2 (i, k)
  have hfin : ∫⁻ y, ENNReal.ofReal (G y ^ 2) ≠ ⊤ :=
    ((lintegral_ofReal_le_lintegral_enorm _).trans_lt hG2'.integrable_sq.hasFiniteIntegral).ne
  have hM := measurable_gradMargS (S := S) (i := i) hGm k
  have hle : ∫⁻ a, ∫⁻ x, ENNReal.ofReal (gradMargS GQ S i a x k ^ 2) ∂haar d ≤
      ∫⁻ y, ENNReal.ofReal (G y ^ 2) := by
    rw [← (measurePreserving_flat' N).lintegral_comp ((hGm'.pow_const 2).ennreal_ofReal),
      lintegral_assembleS hi (G := fun X => ENNReal.ofReal (G (flat X) ^ 2))
        (((hGm'.comp measurable_flat).pow_const 2).ennreal_ofReal)]
    refine lintegral_mono fun a => lintegral_mono fun x => ?_
    exact ofReal_sq_integral_le ((hGm'.comp measurable_flat).comp ((measurable_assembleS S i).comp
      ((measurable_const (a := (a, x))).prodMk measurable_id))).aestronglyMeasurable
  have hae := ae_lt_top' (hM.pow_const 2 |> fun h => ((h).ennreal_ofReal).lintegral_prod_right'.aemeasurable)
    (ne_top_of_le_ne_top hfin hle)
  filter_upwards [hae] with a hp
  refine (memLp_two_iff_integrable_sq (hM.of_uncurry_left).aestronglyMeasurable).mpr ?_
  exact (lintegral_ofReal_ne_top_iff_integrable ((hM.of_uncurry_left).pow_const 2
    |>.aestronglyMeasurable) (Eventually.of_forall fun x => sq_nonneg _)).mp hp.ne

include hi in
theorem ae_memLp_gradCondS (hGm : ∀ p, Measurable fun y => GQ y p)
    (hG2 : ∀ p, MemLp (fun y => GQ y p) 2 volume) :
    ∀ᵐ a ∂(volume : Measure (S → Torus d)), ∀ k,
      MemLp (fun x => gradCondS Q GQ S i a x k) 2 (haar d) := by
  filter_upwards [ae_memLp_gradMargS hi hGm hG2] with a ha k
  exact memLp_div_const (ha k) _

include hQ hi hQw in
/-- **`√ρ_{S,i} ∈ H¹(haar)`** for a.e. revealed values. -/
theorem ae_memH1_sqrt_condDensS (hGm : ∀ p, Measurable fun y => GQ y p)
    (hG2 : ∀ p, MemLp (fun y => GQ y p) 2 volume) :
    ∀ᵐ a ∂(volume : Measure (S → Torus d)),
      MemH1 (haar d) (fun x => Real.sqrt (condDensS Q S i a x)) := by
  have hGi : ∀ p, Integrable (fun y => GQ y p) volume := fun p =>
    (hG2 p).integrable one_le_two
  have hcC : c ≤ C := (hQ.lower 0).trans (hQ.upper 0)
  have hC : 0 < C := hQ.pos.trans_le hcC
  filter_upwards [ae_isWeakGrad_condDensS hQ hi hQw hGi, ae_memLp_gradCondS (Q := Q) hi hGm hG2]
    with a hp hp2
  exact memH1_sqrt_of_ge
    (show Measurable (condDensS Q S i a) from (measurable_condDensS hQ S i).of_uncurry_left)
    hp hp2 (div_pos hQ.pos hC) (fun x => (condDensS_bounds hQ S i a x).1)
    (fun x => (condDensS_bounds hQ S i a x).2)

end grad

end SharpLSI.FL
