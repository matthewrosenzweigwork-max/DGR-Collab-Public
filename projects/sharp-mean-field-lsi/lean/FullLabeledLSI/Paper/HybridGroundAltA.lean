import FullLabeledLSI.Paper.HybridLSIAlt
import FullLabeledLSI.Infra.SpectralSetup
import FullLabeledLSI.Infra.HypercontrTorus4
import FullLabeledLSI.Infra.HypercontrTorus7

/-!
# Hybrid inequality (7.17), alternative route, part A: the ground-state entropy identity (GS1)

On the flat space `W = μ^{⊗N} ⊗ γ_M` with the tilted measure `Z = μ^{⊗N} ⊗ (e^{-u}/κ) γ_M`:
`Ent_Z(h²) = Ent_W(a²) + ∫ a² u dW + log κ ∫ a² dW`, `h = √κ e^{u/2} a`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal ContDiff

noncomputable section

namespace SharpLSI.FL.HLA

open SharpLSI SharpLSI.FL.Gross

theorem entR_nonneg_prob {α : Type*} [MeasurableSpace α] {ρ : Measure α} [IsProbabilityMeasure ρ]
    {f : α → ℝ} (hf0 : ∀ x, 0 ≤ f x) (hi : Integrable f ρ)
    (hl : Integrable (fun x => f x * Real.log (f x)) ρ) : 0 ≤ entR ρ f := by
  have h := Real.convexOn_mul_log.map_integral_le Real.continuous_mul_log.continuousOn isClosed_Ici
    (Filter.Eventually.of_forall fun x => Set.mem_Ici.2 (hf0 x)) hi hl
  unfold entR
  linarith

section gs1
variable {N d M : ℕ} {ι : Type*} [Fintype ι]
  {c : ι → ℝ} {Y : ι → (Fin M → ℝ) → ℝ} {Xj : ι → Config N d → ℝ} {u : (Fin M → ℝ) → ℝ} {κ : ℝ}
  (hY : ∀ i, (Y i).HasTemperateGrowth) (hu : u.HasTemperateGrowth) (hX : ∀ i, C1C (Xj i))
  (hκ : 0 < κ) (P : Measure (Config N d)) [IsProbabilityMeasure P]

include hY hu hX hκ in
/-- **(GS1) The ground-state entropy identity** on the flat space. -/
theorem gs1_flat [hPt : IsProbabilityMeasure (tPt u κ)] :
    (ent (P.prod (tPt u κ)) (fun z => hh c Y Xj u κ z.1 z.2 ^ 2)).toReal =
      (ent (P.prod (gpi M)) (fun z => aF c Y Xj z.1 z.2 ^ 2)).toReal +
      ∫ z, aF c Y Xj z.1 z.2 ^ 2 * u z.2 ∂(P.prod (gpi M)) +
      Real.log κ * ∫ z, aF c Y Xj z.1 z.2 ^ 2 ∂(P.prod (gpi M)) := by
  set W : Measure (Config N d × (Fin M → ℝ)) := P.prod (gpi M) with hW
  set Z : Measure (Config N d × (Fin M → ℝ)) := P.prod (tPt u κ) with hZ
  have hZd : Z = W.withDensity (fun z => ENNReal.ofReal (wd u κ z.2)) := prod_tPt_eq hu P
  have hwm : Measurable fun z : Config N d × (Fin M → ℝ) => wd u κ z.2 :=
    (measurable_wd hu κ).comp measurable_snd
  have hw0 : ∀ z : Config N d × (Fin M → ℝ), 0 ≤ wd u κ z.2 := fun z => wd_nonneg hκ _
  have hZint : ∀ f : Config N d × (Fin M → ℝ) → ℝ, Integrable f Z ↔
      Integrable (fun z => wd u κ z.2 * f z) W := fun f => by
    rw [hZd]; exact integrable_wd hwm hw0
  have hma := meas_aF (c := c) hY hX
  have hmaq : Measurable fun z : Config N d × (Fin M → ℝ) => aF c Y Xj z.1 z.2 ^ 2 := hma.pow_const 2
  -- integrability under `W`
  have J1 : Integrable (fun z : Config N d × (Fin M → ℝ) => aF c Y Xj z.1 z.2 ^ 2) W :=
    integrable_prod_PBu (P := P) (f := fun x g => aF c Y Xj x g ^ 2) hmaq.aestronglyMeasurable
      ((pbu_aF hY hX).sq)
  have J2 : Integrable (fun z : Config N d × (Fin M → ℝ) =>
      aF c Y Xj z.1 z.2 ^ 2 * Real.log (aF c Y Xj z.1 z.2 ^ 2)) W := by
    have h2 : PBu (fun (x : Config N d) (g : Fin M → ℝ) => (aF c Y Xj x g ^ 2) ^ 2 + 1) :=
      ((pbu_aF hY hX).sq.sq).add (PBu.const 1)
    have hi := integrable_prod_PBu (P := P) (f := fun x g => (aF c Y Xj x g ^ 2) ^ 2 + 1)
      (((hma.pow_const 2).pow_const 2).add_const 1 |>.aestronglyMeasurable) h2
    refine hi.mono' ?_ (Eventually.of_forall fun z => ?_)
    · exact (Real.continuous_mul_log.measurable.comp (hma.pow_const 2)).aestronglyMeasurable
    · rw [Real.norm_eq_abs]
      exact abs_mul_log_le_sq_add_one (sq_nonneg _)
  have J3 : Integrable (fun z : Config N d × (Fin M → ℝ) => aF c Y Xj z.1 z.2 ^ 2 * u z.2) W := by
    have h3 : PBu (fun (x : Config N d) (g : Fin M → ℝ) => aF c Y Xj x g ^ 2 * u g) :=
      ((pbu_aF hY hX).sq).mul (PBu.of_tg hu)
    exact integrable_prod_PBu (P := P) (f := fun x g => aF c Y Xj x g ^ 2 * u g)
      (hmaq.mul (hu.1.continuous.measurable.comp measurable_snd)).aestronglyMeasurable h3
  have J4 := integrable_entropy_density (c := c) hY hu hX (κ := κ) P
  -- integrability under `Z`
  have I1 : Integrable (fun z : Config N d × (Fin M → ℝ) => hh c Y Xj u κ z.1 z.2 ^ 2) Z := by
    rw [hZint]
    refine J1.congr (Eventually.of_forall fun z => ?_)
    simp only
    rw [mul_comm (wd u κ z.2), hh_sq_mul_wd hκ]
  have I2 : Integrable (fun z : Config N d × (Fin M → ℝ) =>
      hh c Y Xj u κ z.1 z.2 ^ 2 * Real.log (hh c Y Xj u κ z.1 z.2 ^ 2)) Z := by
    rw [hZint]
    refine J4.congr (Eventually.of_forall fun z => ?_)
    simp only
    rw [mul_comm (wd u κ z.2), hh_sq_log_mul_wd hκ]
  -- the integrals
  have K1 : ∫ z, hh c Y Xj u κ z.1 z.2 ^ 2 ∂Z = ∫ z, aF c Y Xj z.1 z.2 ^ 2 ∂W := by
    rw [hZd, integral_wd hwm hw0]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only
    rw [mul_comm (wd u κ z.2), hh_sq_mul_wd hκ]
  have K2 : ∫ z, hh c Y Xj u κ z.1 z.2 ^ 2 * Real.log (hh c Y Xj u κ z.1 z.2 ^ 2) ∂Z =
      ∫ z, aF c Y Xj z.1 z.2 ^ 2 * (Real.log κ + u z.2 + Real.log (aF c Y Xj z.1 z.2 ^ 2)) ∂W := by
    rw [hZd, integral_wd hwm hw0]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only
    rw [mul_comm (wd u κ z.2), hh_sq_log_mul_wd hκ]
  have K3 : ∫ z, aF c Y Xj z.1 z.2 ^ 2 * (Real.log κ + u z.2 + Real.log (aF c Y Xj z.1 z.2 ^ 2)) ∂W =
      Real.log κ * ∫ z, aF c Y Xj z.1 z.2 ^ 2 ∂W + ∫ z, aF c Y Xj z.1 z.2 ^ 2 * u z.2 ∂W +
        ∫ z, aF c Y Xj z.1 z.2 ^ 2 * Real.log (aF c Y Xj z.1 z.2 ^ 2) ∂W := by
    have e : ∀ z : Config N d × (Fin M → ℝ), aF c Y Xj z.1 z.2 ^ 2 *
        (Real.log κ + u z.2 + Real.log (aF c Y Xj z.1 z.2 ^ 2)) =
        (Real.log κ * aF c Y Xj z.1 z.2 ^ 2 + aF c Y Xj z.1 z.2 ^ 2 * u z.2) +
          aF c Y Xj z.1 z.2 ^ 2 * Real.log (aF c Y Xj z.1 z.2 ^ 2) := fun z => by ring
    have Ia : Integrable (fun z : Config N d × (Fin M → ℝ) =>
        Real.log κ * aF c Y Xj z.1 z.2 ^ 2 + aF c Y Xj z.1 z.2 ^ 2 * u z.2) W :=
      (J1.const_mul _).add J3
    simp_rw [e]
    rw [integral_add Ia J2, integral_add (J1.const_mul _) J3, integral_const_mul]
  -- entropies
  have hentZ : ent Z (fun z => hh c Y Xj u κ z.1 z.2 ^ 2) =
      ENNReal.ofReal (entR Z (fun z => hh c Y Xj u κ z.1 z.2 ^ 2)) :=
    ent_eq_formula Z _ (fun z => sq_nonneg _) I1 I2
  have hentW : ent W (fun z => aF c Y Xj z.1 z.2 ^ 2) =
      ENNReal.ofReal (entR W (fun z => aF c Y Xj z.1 z.2 ^ 2)) :=
    ent_eq_formula W _ (fun z => sq_nonneg _) J1 J2
  have hZnn := entR_nonneg_prob (ρ := Z) (f := fun z => hh c Y Xj u κ z.1 z.2 ^ 2)
    (fun z => sq_nonneg _) I1 I2
  have hWnn := entR_nonneg_prob (ρ := W) (f := fun z => aF c Y Xj z.1 z.2 ^ 2)
    (fun z => sq_nonneg _) J1 J2
  rw [hentZ, hentW, ENNReal.toReal_ofReal hZnn, ENNReal.toReal_ofReal hWnn]
  unfold entR
  rw [K1, K2, K3]
  ring

end gs1

end SharpLSI.FL.HLA

end
