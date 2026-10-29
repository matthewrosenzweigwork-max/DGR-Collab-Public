import SharpSymmetricLSI.Paper.ProductFisherMain

/-!
# (2.12): the product-state upper comparison (Phase 3, lane D; R6)

`r_N^sym ≤ 2ℰ_N(f_N)/Ent(f_N²) = I(ν_N|P_N)/(2H(ν_N|P_N))` with the symmetric representative
`f_N = √Z_N exp(Φ/2)` of `√(dν_N/dP_N)`; letting `N → ∞` with (2.10)–(2.11).
-/

open MeasureTheory Set Filter Topology InformationTheory
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ} {N : ℕ}

/-- The symmetric representative of `√(dν_N/dP_N)`. -/
noncomputable def fTil (V : Torus d → ℝ) (W : Torus d → Torus d → ℝ) (ρ : Torus d → ℝ) (N : ℕ)
    (X : Config N d) : ℝ :=
  Real.sqrt (partitionFn V W N) * Real.exp (PhiF V W ρ N (flat X) / 2)

theorem isSymmetric_fTil (hyp : Hyp V W KV KW) (ρ : Torus d → ℝ) :
    IsSymmetric (fTil V W ρ N) := by
  intro σ X
  simp only [fTil, PhiF_flat hyp, hamiltonian_perm]
  congr 4
  exact Equiv.sum_comp σ (fun i => Real.log (ρ (X i)))

theorem fTil_ae_eq (hyp : Hyp V W KV KW) {ρ : Torus d → ℝ} (hs : IsSmoothT ρ)
    (hpos : ∀ x, 0 < ρ x) :
    sqrtDens (Measure.pi fun _ : Fin N => densMeasure ρ) (gibbs V W N) =ᵐ[gibbs V W N]
      fTil V W ρ N := by
  have hρc : Continuous ρ := hs.continuous
  filter_upwards [rnDeriv_productState (N := N) hyp hρc.measurable (fun x => (hpos x).le)
    (integrable_of_continuous hρc)] with X hX
  simp only [sqrtDens, fTil]
  rw [hX, sqrt_densNP hyp hpos]

/-- `r_N^sym ≤ I(ν_N|P_N) / (2 H(ν_N|P_N))` when `H(ν_N|P_N) > 0`. -/
theorem rSym_le_fisher (hyp : Hyp V W KV KW) {ρ : Torus d → ℝ} (hs : IsSmoothT ρ)
    (hpos : ∀ x, 0 < ρ x) (h1 : ∫ x, ρ x ∂haar d = 1)
    (hK : 0 < klDiv (Measure.pi fun _ : Fin N => densMeasure ρ) (gibbs V W N)) :
    rSym V W N ≤ fisherInfoC (Measure.pi fun _ : Fin N => densMeasure ρ) (gibbs V W N) /
      (2 * klDiv (Measure.pi fun _ : Fin N => densMeasure ρ) (gibbs V W N)) := by
  have := gibbs_isProbabilityMeasure hyp N
  have := isProbabilityMeasure_densMeasure' (fun x => (hpos x).le) h1
  have hρc : Continuous ρ := hs.continuous
  have hνac : (Measure.pi fun _ : Fin N => densMeasure ρ) ≪ gibbs V W N := by
    rw [productState_eq_withDensity hyp hρc.measurable (fun x => (hpos x).le)
      (integrable_of_continuous hρc)]
    exact withDensity_absolutelyContinuous _ _
  obtain ⟨hH1, h4, -⟩ := fisher_productState (N := N) hyp hs hpos h1
  have hae := fTil_ae_eq (N := N) hyp hs hpos
  obtain ⟨hH1', hE⟩ := memH1C_congr_ae hyp hH1 hae
  have hent : ent (gibbs V W N) (fun X => fTil V W ρ N X ^ 2) =
      klDiv (Measure.pi fun _ : Fin N => densMeasure ρ) (gibbs V W N) := by
    rw [klDiv_eq_ent hνac]
    exact ent_congr_ae (hae.mono fun X hX => by simp only [hX])
  have hle : rSym V W N ≤ 2 * energy V W N (fTil V W ρ N) /
      ent (gibbs V W N) (fun X => fTil V W ρ N X ^ 2) :=
    iInf₂_le (fTil V W ρ N) ⟨hH1', isSymmetric_fTil hyp ρ, by rw [hent]; exact hK⟩
  refine hle.trans (le_of_eq ?_)
  rw [hent, hE, h4, show (4 : ℝ≥0∞) = 2 * 2 by norm_num, mul_assoc (2 : ℝ≥0∞) 2,
    ENNReal.mul_div_mul_left _ _ (by norm_num) (by norm_num)]

/-- **(2.12)**. -/
theorem upper_comparison_aux (hyp : Hyp V W KV KW) {ρ : Torus d → ℝ} (hs : IsSmoothT ρ)
    (hpos : ∀ x, 0 < ρ x) (h1 : ∫ x, ρ x ∂haar d = 1) (hG : 0 < gap V W (densMeasure ρ)) :
    limsup (fun N => rSym V W N) atTop ≤
      dissipation V W ρ / (2 * (gap V W (densMeasure ρ)).toENNReal) := by
  obtain ⟨hKid, hGt, hKlim⟩ := product_state_entropy_aux hyp hs hpos h1
  obtain ⟨hFid, hDt, hFlim⟩ := product_state_fisher_aux hyp hs hpos h1
  set g := (gap V W (densMeasure ρ)).toReal with hg
  set D := (dissipation V W ρ).toReal with hDdef
  have hgpos : 0 < g := by
    have hne : gap V W (densMeasure ρ) ≠ ⊥ := ne_bot_of_gt hG
    have : gap V W (densMeasure ρ) = (g : EReal) := (EReal.coe_toReal hGt hne).symm
    rw [this] at hG; exact_mod_cast hG
  set k : ℕ → ℝ := fun N => (klDiv (Measure.pi fun _ : Fin N => densMeasure ρ) (gibbs V W N)).toReal
  set i : ℕ → ℝ := fun N => (fisherInfoC (Measure.pi fun _ : Fin N => densMeasure ρ)
    (gibbs V W N)).toReal
  -- eventually `k N > 0`
  have hkev : ∀ᶠ N in atTop, 0 < k N / N := hKlim.eventually (lt_mem_nhds hgpos)
  -- the bound sequence
  set u : ℕ → ℝ≥0∞ := fun N => ENNReal.ofReal ((i N / N) / (2 * (k N / N))) with hu
  have hle : ∀ᶠ N in atTop, rSym V W N ≤ u N := by
    filter_upwards [hkev, eventually_ge_atTop 1] with N hk hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    have hkp : 0 < k N := by
      have := (div_pos_iff_of_pos_right hN0).mp hk; exact this
    have hKne := (hKid N hN).1
    have hFne := (hFid N hN).1
    have hKpos : 0 < klDiv (Measure.pi fun _ : Fin N => densMeasure ρ) (gibbs V W N) := by
      rw [← ENNReal.ofReal_toReal hKne]; exact ENNReal.ofReal_pos.mpr hkp
    refine (rSym_le_fisher hyp hs hpos h1 hKpos).trans (le_of_eq ?_)
    rw [← ENNReal.ofReal_toReal hKne, ← ENNReal.ofReal_toReal hFne, hu]
    simp only
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_div_of_pos (by positivity)]
    congr 1
    field_simp
    change i N * k N / k N = i N
    field_simp [hkp.ne']
  have hulim : Tendsto u atTop (𝓝 (ENNReal.ofReal (D / (2 * g)))) := by
    refine ENNReal.tendsto_ofReal ?_
    exact hFlim.div (hKlim.const_mul 2) (by positivity)
  have hL : ENNReal.ofReal (D / (2 * g)) =
      dissipation V W ρ / (2 * (gap V W (densMeasure ρ)).toENNReal) := by
    have hgE : (gap V W (densMeasure ρ)).toENNReal = ENNReal.ofReal g := by
      simp [EReal.toENNReal, hGt, hg]
    rw [hgE, ← ENNReal.ofReal_toReal hDt, show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp,
      ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_div_of_pos (by positivity)]
  rw [← hL, ← hulim.limsup_eq]
  exact limsup_le_limsup hle

end SharpLSI
