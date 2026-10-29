import SharpSymmetricLSI.Paper.Defective15

/-!
# R03 (Proposition 2.2), part 16: the conditional densities of the regularized law

For `ν = Q · Leb` with `Q = Qreg n f`, `∇Q = GQreg n f g` and `j < N`, for a.e. past `p`:
* `ρ_p = condDens p` has the weak gradient `gradMarg p / Zc p` (`ae_isWeakGrad_condDens`);
* `gradMarg p · k ∈ L²` (`ae_memLp_gradMarg`);
* `D(ρ_p) = ∫ ρ_p |gradMarg/margQ + ∇V + b_{ρ_p}|²` (`ae_dissipation_condDens`).
-/

open MeasureTheory Filter Topology InformationTheory
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

theorem memLp_div_const {α : Type*} [MeasurableSpace α] {P : Measure α} {f : α → ℝ}
    {p : ℝ≥0∞} (hf : MemLp f p P) (c : ℝ) : MemLp (fun x => f x / c) p P := by
  have e : (fun x => f x / c) = fun x => c⁻¹ * f x := by funext x; ring
  rw [e]; exact hf.const_mul _

section condReg
variable (hyp : Hyp V W KV KW) {μ : Measure (Torus d)} [IsProbabilityMeasure μ] (hac : μ ≪ haar d)
  {N : ℕ} (hN : 1 ≤ N) {f : Config N d → ℝ} (hfm : Measurable f) (hf : MemH1C (gibbs V W N) f)
  {g : UnitAddTorus (Fin N × Fin d) → Fin N × Fin d → ℝ} (hw : IsWeakGrad (f ∘ unflat) g)
  (hgm : ∀ p, Measurable fun y => g y p) (hg2 : ∀ p, MemLp (fun y => g y p) 2 volume)
  (hgi : ∀ p, Integrable (fun y => g y p) volume) (n : ℕ) {j : ℕ} (hj : j < N)
include hyp hac hN hfm hf hw hgm hg2 hgi

theorem measurable_GQreg (p : Fin N × Fin d) : Measurable fun y => GQreg V W μ n f g y p := by
  have hmf : Measurable fun y : UnitAddTorus (Fin N × Fin d) => f (unflat y) := hfm.comp measurable_unflat
  have hmℓ : Measurable fun y : UnitAddTorus (Fin N × Fin d) => gibbsDensR V W N (unflat y) :=
    (measurable_gibbsDensR hyp).comp measurable_unflat
  unfold GQreg uReg
  exact (((((contDiff_psiSqR n).continuous_deriv le_rfl).measurable.comp hmf).mul (hgm p)).mul hmℓ |>.add
    (((contDiff_psiSqR n).continuous.measurable.comp hmf).mul
      (hmℓ.mul (measurable_gradH hyp hac hN p)).neg)).div_const _

theorem ae_isWeakGrad_condDens :
    ∀ᵐ p ∂(volume : Measure (Config j d)), IsWeakGrad (condDens hj (Qreg V W n f) p)
      (fun x k => gradMarg hj (GQreg V W μ n f g) p x k / Zc hj (Qreg V W n f) p) := by
  have h := ae_isWeakGrad_margQ hj (isWeakGrad_Qreg hyp hac hN hf hw hgi n)
    (integrable_Qreg hyp hac hN hfm hf n)
    (fun p => (memLp_GQreg hyp hac hN hfm hf n hg2 p).integrable one_le_two)
  filter_upwards [h] with p hp
  convert hp.cmul (1 / Zc hj (Qreg V W n f) p) using 1
  · funext x; unfold condDens; ring
  · funext x k; ring

theorem measurable_gradMarg (k : Fin d) :
    Measurable (Function.uncurry fun (p : Config j d) (x : Torus d) =>
      gradMarg hj (GQreg V W μ n f g) p x k) :=
  (((measurable_GQreg hyp hac hN hfm hf hw hgm hg2 hgi n (⟨j, hj⟩, k)).comp measurable_flat).comp
    (measurable_assemble hj)).stronglyMeasurable.integral_prod_right'.measurable

theorem ae_memLp_gradMarg :
    ∀ᵐ p ∂(volume : Measure (Config j d)), ∀ k,
      MemLp (fun x => gradMarg hj (GQreg V W μ n f g) p x k) 2 (haar d) := by
  rw [ae_all_iff]
  intro k
  set G := fun y => GQreg V W μ n f g y (⟨j, hj⟩, k)
  have hGm : Measurable G := measurable_GQreg hyp hac hN hfm hf hw hgm hg2 hgi n _
  have hG2 := memLp_GQreg hyp hac hN hfm hf n hg2 (⟨j, hj⟩, k)
  have hfin : ∫⁻ y, ENNReal.ofReal (G y ^ 2) ≠ ⊤ :=
    ((lintegral_ofReal_le_lintegral_enorm _).trans_lt hG2.integrable_sq.hasFiniteIntegral).ne
  have hM := measurable_gradMarg hyp hac hN hfm hf hw hgm hg2 hgi n hj k
  -- `∫∫ gradMarg² ≤ ∫ G² < ∞`
  have hle : ∫⁻ p, ∫⁻ x, ENNReal.ofReal (gradMarg hj (GQreg V W μ n f g) p x k ^ 2) ∂haar d ≤
      ∫⁻ y, ENNReal.ofReal (G y ^ 2) := by
    rw [← (measurePreserving_flat' N).lintegral_comp ((hGm.pow_const 2).ennreal_ofReal),
      lintegral_assemble hj (G := fun X => ENNReal.ofReal (G (flat X) ^ 2))
        (((hGm.comp measurable_flat).pow_const 2).ennreal_ofReal)]
    refine lintegral_mono fun p => lintegral_mono fun x => ?_
    exact ofReal_sq_integral_le ((hGm.comp measurable_flat).comp ((measurable_assemble hj).comp
      ((measurable_const (a := (p, x))).prodMk measurable_id))).aestronglyMeasurable
  have hae := ae_lt_top' (hM.pow_const 2 |> fun h => ((h).ennreal_ofReal).lintegral_prod_right'.aemeasurable)
    (ne_top_of_le_ne_top hfin hle)
  filter_upwards [hae] with p hp
  refine (memLp_two_iff_integrable_sq (hM.of_uncurry_left).aestronglyMeasurable).mpr ?_
  exact (lintegral_ofReal_ne_top_iff_integrable ((hM.of_uncurry_left).pow_const 2
    |>.aestronglyMeasurable) (Eventually.of_forall fun x => sq_nonneg _)).mp hp.ne

/-- **The dissipation of the conditional densities.** -/
theorem ae_dissipation_condDens :
    ∀ᵐ p ∂(volume : Measure (Config j d)),
      dissipation V W (condDens hj (Qreg V W n f) p) = ∫⁻ x, ENNReal.ofReal
        (condDens hj (Qreg V W n f) p x * ∑ k, (gradMarg hj (GQreg V W μ n f g) p x k /
          margQ hj (Qreg V W n f) p x + lipGrad V x k +
          bForceL W (condDens hj (Qreg V W n f) p) x k) ^ 2) ∂haar d := by
  obtain ⟨c, C, hc, hb⟩ := Qreg_bounds hyp hf hfm n
  have hQm := measurable_Qreg hyp hf hfm n
  have hQc : ∀ X, c ≤ Qreg V W n f X := fun X => (hb X).1
  have hQC : ∀ X, Qreg V W n f X ≤ C := fun X => (hb X).2
  have hC : 0 < C := hc.trans_le ((hQc (Classical.arbitrary _)).trans (hQC _))
  filter_upwards [ae_isWeakGrad_condDens hyp hac hN hfm hf hw hgm hg2 hgi n hj,
    ae_memLp_gradMarg hyp hac hN hfm hf hw hgm hg2 hgi n hj] with p hp hp2
  have hZ := (Zc_bounds hj hQm hQc hQC p).1
  have hZ0 : 0 < Zc hj (Qreg V W n f) p := hc.trans_le hZ
  rw [dissipation_eq_of_ge hyp (show Measurable (condDens hj (Qreg V W n f) p) from
      (measurable_condDens hj hQm).of_uncurry_left)
    hp (fun k => ((measurable_gradMarg hyp hac hN hfm hf hw hgm hg2 hgi n hj k).of_uncurry_left).div_const _)
    (fun k => memLp_div_const (hp2 k) _) (div_pos hc hC)
    (fun x => (condDens_bounds hj hQm hc hQc hQC p x).1)
    (fun x => (condDens_bounds hj hQm hc hQc hQC p x).2)
    (integral_condDens hj hQm hc hQc hQC p)]
  refine lintegral_congr fun x => ?_
  congr 2
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 3
  unfold condDens
  field_simp

end condReg

end SharpLSI
