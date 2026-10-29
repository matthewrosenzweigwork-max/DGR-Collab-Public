import FullLabeledLSI.Paper.HybridGroundAltB

/-!
# Hybrid inequality (7.17), alternative route, part C: the flat inequality

`hyb_flat`: on the flat space `W = μ^{⊗N} ⊗ γ_M`, from the core inequality `core_lsi` for the tilted
measure, the entropy identity (GS1) and the Gaussian integration by parts (GS2):
`0 ≤ E + ∫ a² v dW - (ρ/2)(Ent_W(a²) + ∫ a² u dW + log κ ∫ a² dW)`
with `E = ∫ (Ex0 + Σ λ_k (∂_k a)²) dW` the unperturbed hybrid energy.
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open scoped ENNReal ContDiff

noncomputable section

namespace SharpLSI.FL.HLA

open SharpLSI SharpLSI.FL.Gross

section hybflat
variable {N d M : ℕ} {ι : Type*} [Fintype ι]
  {c : ι → ℝ} {Y : ι → (Fin M → ℝ) → ℝ} {Xj : ι → Config N d → ℝ} {u : (Fin M → ℝ) → ℝ} {κ : ℝ}
  (hY : ∀ i, (Y i).HasTemperateGrowth) (hu : u.HasTemperateGrowth) (hX : ∀ i, C1C (Xj i))
  (hκ : 0 < κ) {mu : Measure (Torus d)} [IsProbabilityMeasure mu]

include hY hu hX hκ in
/-- The two energy integrals under the tilted measure, as integrals under `W`. -/
theorem energy_tilt_eq_flat (lam' : Fin M → ℝ) :
    (∫ z, gradPair (fun x => hh c Y Xj u κ x z.2) (fun x => hh c Y Xj u κ x z.2) z.1
        ∂((Measure.pi fun _ : Fin N => mu).prod (tPt u κ)) +
      ∫ z, Eyy lam' (fun g => hh c Y Xj u κ z.1 g) z.2
        ∂((Measure.pi fun _ : Fin N => mu).prod (tPt u κ))) =
    ∫ z, Ex0 c Y Xj z.1 z.2 ∂((Measure.pi fun _ : Fin N => mu).prod (gpi M)) +
      ∫ z, Ey0 c Y Xj u lam' z.1 z.2 ∂((Measure.pi fun _ : Fin N => mu).prod (gpi M)) := by
  set P : Measure (Config N d) := Measure.pi fun _ : Fin N => mu with hP
  have hZd : P.prod (tPt u κ) = (P.prod (gpi M)).withDensity
      (fun z => ENNReal.ofReal (wd u κ z.2)) := prod_tPt_eq hu P
  have hwm : Measurable fun z : Config N d × (Fin M → ℝ) => wd u κ z.2 :=
    (measurable_wd hu κ).comp measurable_snd
  have hw0 : ∀ z : Config N d × (Fin M → ℝ), 0 ≤ wd u κ z.2 := fun z => wd_nonneg hκ _
  rw [hZd, integral_wd hwm hw0, integral_wd hwm hw0]
  congr 1
  · refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only
    rw [gradPair_hh hX, ← mul_assoc, mul_comm (wd u κ z.2), sF_sq_mul_wd hκ, one_mul]
  · refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only
    rw [← wd_mul_energy hY hu hκ lam' z.1 z.2]
    rfl

include hY hu hX hκ in
theorem hyb_flat (lam' : Fin M → ℝ) (hl0 : ∀ k, 0 ≤ lam' k)
    {ρ a0 : ℝ} (hρ : 0 ≤ ρ) (ha0 : 0 < a0) (hρa : ρ ≤ a0) (hac : mu ≪ volume)
    (hrls : ENNReal.ofReal a0 ≤ rLS mu) [hPt : IsProbabilityMeasure (tPt u κ)]
    (hgl : ∀ f : (Fin M → ℝ) → ℝ, ContDiff ℝ ∞ f → MemLp f 2 (tPt u κ) →
      Integrable (fun g => Eyy lam' f g) (tPt u κ) →
      ENNReal.ofReal (ρ / 2) * ent (tPt u κ) (fun g => f g ^ 2) ≤
        ENNReal.ofReal (∫ g, Eyy lam' f g ∂tPt u κ))
    (S : Matrix (Fin M) (Fin M) ℝ) (hS : Sᵀ = S)
    (hu_eq : ∀ g, u g = (g ⬝ᵥ (S *ᵥ g)) / 2) {Esum : ℝ}
    (hE : ∫ z, Ex0 c Y Xj z.1 z.2 ∂((Measure.pi fun _ : Fin N => mu).prod (gpi M)) +
        ∫ z, ∑ k, lam' k * daF c Y Xj z.1 z.2 k ^ 2
          ∂((Measure.pi fun _ : Fin N => mu).prod (gpi M)) = Esum) :
    0 ≤ Esum + ∫ z, aF c Y Xj z.1 z.2 ^ 2 * vflat S lam' z.2
          ∂((Measure.pi fun _ : Fin N => mu).prod (gpi M)) -
      ρ / 2 * ((ent ((Measure.pi fun _ : Fin N => mu).prod (gpi M))
          (fun z => aF c Y Xj z.1 z.2 ^ 2)).toReal +
        ∫ z, aF c Y Xj z.1 z.2 ^ 2 * u z.2 ∂((Measure.pi fun _ : Fin N => mu).prod (gpi M)) +
        Real.log κ * ∫ z, aF c Y Xj z.1 z.2 ^ 2
          ∂((Measure.pi fun _ : Fin N => mu).prod (gpi M))) := by
  have hcore := core_lsi (c := c) (Y := Y) (Xj := Xj) (u := u) (κ := κ) (mu := mu) hY hu hX hκ
    lam' hl0 hρ ha0 hρa hac hrls hgl
  rw [energy_tilt_eq_flat hY hu hX hκ lam', gs1_flat hY hu hX hκ] at hcore
  rw [ibp_energy S lam' hY hX hu _ hS hu_eq] at hcore
  linarith

end hybflat

end SharpLSI.FL.HLA

end
