import DGPS.Examples.RoughBoundary.FreeEnergy

/-!
# RUF030: model specific global entropy coercivity

Source: `ROUGH_COUNTEREXAMPLE_RECONCILED_PROOF.md` section 3.7, (3.13).

For the selected rough-boundary features `U_{L,ε}` with potential `Ψ`, `κ = 11/6`, `h = 1/22`:
`a = inf_{0<|t|≤κ} Ψ(t)/|t|² > 0` and, with `G(ρ) = F(ρ m) - κ/2`,
`G(ρ) ≥ [2κa/(1+2κa)] H(ρ m | m)` for every probability measure `ρ m`, including infinite entropy,
and in the common family `a ≥ min {h/4, γ/(2κ²)}`, `γ` the annulus gap of RUF023.

Design choices (R5 notes).
* `G ≥ c H` is stated additively in `EReal`, `κ/2 + c * H ≤ F` (as in RUF027), where `c H = ⊤`
  when `H = ⊤` since `c > 0`; this is the extended-entropy reading of the packet.
* `a` is exhibited as the greatest lower bound (`IsGLB`) of the ratio `Ψ(t)/‖t‖²` on `0<‖t‖≤κ`.
* The common family is as in RUF026, but the `γ/2` closeness of `Ψ` to `Ψ∞` on `B̄_R` that
  RUF026 uses internally is not exported there.  `selection_with_gap` re-runs the RUF026 selection
  argument verbatim and keeps that closeness, with `γ` the `IsLeast` annulus minimum of RUF023
  over `1/352 ≤ ‖t‖ ≤ R`.
-/

open MeasureTheory InformationTheory Set Metric
open scoped ENNReal ContDiff

namespace DGPS.Examples.RoughBoundary.FreeEnergy

open DGPS.Examples.RoughBoundary.Feature DGPS.Examples.RoughBoundary.Landscape
open DGPS.Examples.RoughBoundary.ThreeState
open DGPS.Examples.RoughBoundary.Model (modelData kappa)
open DGPS.Examples.RoughBoundary.Semicontinuity (featurePotential)

/-- RUF026 with the closeness `|Ψ_U - Ψ∞| < γ/2` on `B̄_R` retained, `γ` the RUF023 annulus gap. -/
lemma selection_with_gap :
    ∃ R : ℝ, 2 * kappa0 < R ∧ ∃ γ : ℝ,
      IsLeast (orderPotential '' {t : E2 | (1 / 352 : ℝ) ≤ ‖t‖ ∧ ‖t‖ ≤ R}) γ ∧ 0 < γ ∧
      ∃ ε₀ L₀ : ℝ, 0 < ε₀ ∧ 1 ≤ L₀ ∧ 1 / ε₀ ≤ L₀ ∧
        (∀ L : ℝ, L₀ ≤ L → ∀ ε : ℝ, |ε| ≤ ε₀ → RoughLandscapeCertificate (Ufeat L ε) ∧
          ∀ t : E2, ‖t‖ ≤ R → |featurePotential kappa0 (Ufeat L ε) t - orderPotential t| < γ / 2) ∧
        ∃ L_fixed : ℝ, L₀ ≤ L_fixed ∧ 1 / L_fixed ≤ ε₀ := by
  obtain ⟨R, hR, η, hη, hloc⟩ := local_selection
  obtain ⟨γ, hγl, hγ, hglob⟩ := global_three_region_positivity_persists hR
  obtain ⟨hP1, hP2, hP3⟩ := compact_uniform_convergence_of_parameter_derivatives
  set η1 : ℝ := min η (γ / 2) with hη1def
  have hη10 : 0 < η1 := lt_min hη (by positivity)
  have hη1a : η1 ≤ η := min_le_left _ _
  have hη1b : η1 ≤ γ / 2 := min_le_right _ _
  obtain ⟨C, hC, hCb⟩ := hP2 2 R
  set S : ℝ := ⨆ z : Torus 1, |Spikes.gT z| with hSdef
  have hS : 0 ≤ S := Real.iSup_nonneg fun _ => abs_nonneg _
  have hCS : 0 ≤ C * S := mul_nonneg hC hS
  set ε₀ : ℝ := η1 / (4 * (C * S + 1)) with hε₀def
  have hε₀ : 0 < ε₀ := by positivity
  have hε₀b : C * ε₀ * S ≤ η1 / 4 := by
    have : C * ε₀ * S = C * S * η1 / (4 * (C * S + 1)) := by
      rw [hε₀def]; field_simp
    rw [this, div_le_iff₀ (by positivity)]
    nlinarith
  obtain ⟨L1, hL1⟩ := hP1 2 R (η1 / 4) (by positivity)
  have hmain : ∀ L : ℝ, max (max 1 (1 / ε₀)) L1 ≤ L → ∀ ε : ℝ, |ε| ≤ ε₀ →
      RoughLandscapeCertificate (Ufeat L ε) ∧ ∀ t : E2, ‖t‖ ≤ R →
        |Semicontinuity.featurePotential kappa0 (Ufeat L ε) t - orderPotential t| < γ / 2 := by
    intro L hL ε hε
    have hL1' : 1 ≤ L := (le_max_left _ _).trans ((le_max_left _ _).trans hL)
    have hLpos : 0 < L := lt_of_lt_of_le one_pos hL1'
    have hLL1 : L1 ≤ L := (le_max_right _ _).trans hL
    have hcd := hP3 L hLpos ε
    have hcd0 := hP3 L hLpos 0
    have hb1 := hCb L hLpos ε
    have hb0 := hL1 L hLL1
    have hε2 : C * |ε| * S ≤ η1 / 4 :=
      le_trans (by gcongr) hε₀b
    have hbsum := ckBound_add (hcd.sub hcd0) (hcd0.sub contDiff_logPartition) hb1 hb0
    have e : (fun t => Semicontinuity.featureLogPartition (Ufeat L ε) t - logPartition t) =
        fun t => (Semicontinuity.featureLogPartition (Ufeat L ε) t -
          Semicontinuity.featureLogPartition (Ufeat L 0) t) +
          (Semicontinuity.featureLogPartition (Ufeat L 0) t - logPartition t) :=
      funext fun t => by ring
    have hb : ckBound (closedBall (0 : E2) R) 2
        (fun t => Semicontinuity.featureLogPartition (Ufeat L ε) t - logPartition t)
        (η1 / 2) := by
      rw [e]
      exact ckBound_mono hbsum (by linarith)
    obtain ⟨hcont, hrot, hv, hd1, hd2, hc2⟩ :=
      perturbed_certificate hLpos ε hb le_rfl hcd
    have hmom := exact_shift_symmetries_and_feature_moments hLpos ε
    have hcl : ∀ t : E2, ‖t‖ ≤ R →
        |Semicontinuity.featurePotential kappa0 (Ufeat L ε) t - orderPotential t| < γ / 2 :=
      fun t ht => by
        have := hv t (mem_closedBall_zero_iff.2 ht)
        linarith
    obtain ⟨g1, g2, g3, g4⟩ := hglob (Ufeat L ε) (measurable_Ufeat hLpos ε)
      (fun y => (norm_Ufeat L ε y).le) hmom.1.2.2.1 hmom.1.2.2.2 hcl
    refine ⟨⟨hcont, hrot, g1, g2, g3, g4, hloc _ hc2 hrot (fun t ht => ?_) (fun t ht => ?_)
      (fun t ht => ?_)⟩, hcl⟩
    · exact (hv t ht).trans (by linarith)
    · exact (hd1 t ht).trans (by linarith)
    · exact (hd2 t ht).trans (by linarith)
  have hL0 : 1 ≤ max (max 1 (1 / ε₀)) L1 := (le_max_left _ _).trans (le_max_left _ _)
  have hL0pos : 0 < max (max 1 (1 / ε₀)) L1 := lt_of_lt_of_le one_pos hL0
  have hL0b : 1 / ε₀ ≤ max (max 1 (1 / ε₀)) L1 :=
    (le_max_right _ _).trans (le_max_left _ _)
  have hfix : 1 / max (max 1 (1 / ε₀)) L1 ≤ ε₀ := (one_div_le hL0pos hε₀).2 hL0b
  exact ⟨R, hR, γ, hγl, hγ, ε₀, max (max 1 (1 / ε₀)) L1, hε₀, hL0, hL0b, hmain,
    max (max 1 (1 / ε₀)) L1, le_rfl, hfix⟩

/-- Quadratic lower bound of the potential on `‖t‖ ≤ κ` from the neighbourhood of zero (RUF022) and
the annulus gap (RUF023). -/
lemma quadratic_bound_of_gap {Ψ : E2 → ℝ} {R γ : ℝ} (hRk : kappa0 ≤ R) (hγ : 0 < γ)
    (hgap : ∀ t : E2, (1 / 352 : ℝ) ≤ ‖t‖ → ‖t‖ ≤ R → γ ≤ orderPotential t)
    (hclose : ∀ t : E2, ‖t‖ ≤ R → |Ψ t - orderPotential t| < γ / 2)
    (hnear : ∀ t : E2, ‖t‖ ≤ (1 / 22 : ℝ) / 16 → (1 / 22 : ℝ) / 4 * ‖t‖ ^ 2 ≤ Ψ t) (t : E2)
    (ht : ‖t‖ ≤ kappa0) :
    min ((1 / 22 : ℝ) / 4) (γ / (2 * kappa0 ^ 2)) * ‖t‖ ^ 2 ≤ Ψ t := by
  have hk : 0 < kappa0 := kappa0_pos
  by_cases h1 : ‖t‖ ≤ (1 / 22 : ℝ) / 16
  · exact le_trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg _)) (hnear t h1)
  · push Not at h1
    have h2 := (abs_lt.1 (hclose t (ht.trans hRk))).1
    have h3 := hgap t (by linarith) (ht.trans hRk)
    have h4 : γ / 2 ≤ Ψ t := by linarith
    have h5 : ‖t‖ ^ 2 ≤ kappa0 ^ 2 := pow_le_pow_left₀ (norm_nonneg _) ht 2
    calc min ((1 / 22 : ℝ) / 4) (γ / (2 * kappa0 ^ 2)) * ‖t‖ ^ 2
        ≤ γ / (2 * kappa0 ^ 2) * ‖t‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg _)
      _ ≤ γ / (2 * kappa0 ^ 2) * kappa0 ^ 2 :=
          mul_le_mul_of_nonneg_left h5 (by positivity)
      _ = γ / 2 := by field_simp
      _ ≤ Ψ t := h4

lemma norm_meanFeature_le {L : ℝ} (ε : ℝ) (ν : ProbabilityMeasure (Torus 1)) :
    ‖meanFeature L ε (ν : Measure (Torus 1))‖ ≤ 1 := by
  have := norm_integral_le_of_norm_le_const (μ := (ν : Measure (Torus 1))) (f := Ufeat L ε)
    (C := 1) (Filter.Eventually.of_forall fun y => (norm_Ufeat L ε y).le)
  simpa [meanFeature] using this

/-- The coercivity inequality `κ/2 + c H ≤ F` with `c = 2κa/(1+2κa)`, for any `a > 0` with
`a ‖t‖² ≤ Ψ(t)` on `‖t‖ ≤ κ`. -/
lemma coercivity_inequality {L : ℝ} (hL : 0 < L) (ε : ℝ) {a : ℝ} (ha : 0 < a)
    (hbd : ∀ t : E2, ‖t‖ ≤ kappa → a * ‖t‖ ^ 2 ≤ featurePotential kappa0 (Ufeat L ε) t)
    (ν : ProbabilityMeasure (Torus 1)) :
    ((kappa / 2 : ℝ) : EReal) +
        ((2 * kappa * a / (1 + 2 * kappa * a) : ℝ) : EReal) *
          ((relativeEntropy (ν : Measure (Torus 1)) (DGPS.haar 1) : ℝ≥0∞) : EReal) ≤
      freeEnergy (modelData hL ε) ν := by
  have hk : 0 < kappa := kappa_pos
  have hD : 0 < 1 + 2 * kappa * a := by positivity
  have hc : 0 < 2 * kappa * a / (1 + 2 * kappa * a) := by positivity
  by_cases hH : relativeEntropy (ν : Measure (Torus 1)) (DGPS.haar 1) = ⊤
  · rw [freeEnergy_eq_entropy_sub hL ε ν, hH, EReal.coe_ennreal_top,
      EReal.coe_mul_top_of_pos hc, EReal.top_add_coe, EReal.coe_add_top]
  · set M := meanFeature L ε (ν : Measure (Torus 1)) with hM
    set h := (relativeEntropy (ν : Measure (Torus 1)) (DGPS.haar 1)).toReal with hh
    have h2 : freeEnergy (modelData hL ε) ν =
        ((kappa / 2 + (h - kappa / 2 * ‖M‖ ^ 2) : ℝ) : EReal) := by
      rw [freeEnergy_eq_entropy_sub hL ε ν, coe_eq_toReal hH, ← EReal.coe_add, ← EReal.coe_add]
      congr 1; ring
    have h1 : ((kappa / 2 + featurePotential kappa0 (Ufeat L ε) (kappa • M) : ℝ) : EReal) ≤
        freeEnergy (modelData hL ε) ν := by
      rw [freeEnergy_eq_gibbs' hL ε ν, EReal.coe_add]
      exact add_le_add le_rfl (le_add_of_nonneg_left (EReal.coe_ennreal_nonneg _))
    rw [h2, EReal.coe_le_coe_iff] at h1
    have hM1 : ‖M‖ ≤ 1 := norm_meanFeature_le ε ν
    have hn : ‖kappa • M‖ = kappa * ‖M‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hk]
    have hb := hbd (kappa • M) (by rw [hn]; nlinarith [norm_nonneg M])
    rw [hn] at hb
    have key : 2 * kappa * a / (1 + 2 * kappa * a) * h ≤ h - kappa / 2 * ‖M‖ ^ 2 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hD]
      nlinarith [sq_nonneg ‖M‖]
    rw [h2, coe_eq_toReal hH, ← EReal.coe_mul, ← EReal.coe_add, EReal.coe_le_coe_iff]
    linarith

/-- The packet statement for one feature `U_{L,ε}` and a gap constant `γ`. -/
def ModelEntropyCoercivity (L ε γ : ℝ) : Prop :=
  ∀ hL : 0 < L, ∃ a : ℝ,
    IsGLB ((fun t : E2 => featurePotential kappa0 (Ufeat L ε) t / ‖t‖ ^ 2) ''
      {t : E2 | 0 < ‖t‖ ∧ ‖t‖ ≤ kappa}) a ∧ 0 < a ∧
    min ((1 / 22 : ℝ) / 4) (γ / (2 * kappa ^ 2)) ≤ a ∧
    ∀ ν : ProbabilityMeasure (Torus 1),
      ((kappa / 2 : ℝ) : EReal) +
          ((2 * kappa * a / (1 + 2 * kappa * a) : ℝ) : EReal) *
            ((relativeEntropy (ν : Measure (Torus 1)) (DGPS.haar 1) : ℝ≥0∞) : EReal) ≤
        freeEnergy (modelData hL ε) ν

lemma modelEntropyCoercivity_of_bounds {L ε R γ : ℝ}
    (hcert : RoughLandscapeCertificate (Ufeat L ε)) (hRk : kappa0 ≤ R) (hγ : 0 < γ)
    (hgap : ∀ t : E2, (1 / 352 : ℝ) ≤ ‖t‖ → ‖t‖ ≤ R → γ ≤ orderPotential t)
    (hclose : ∀ t : E2, ‖t‖ ≤ R →
      |featurePotential kappa0 (Ufeat L ε) t - orderPotential t| < γ / 2) :
    ModelEntropyCoercivity L ε γ := by
  intro hL
  obtain ⟨-, -, hnn, -, -⟩ := hcert
  have hk : 0 < kappa := kappa_pos
  have hkeq : kappa = kappa0 := kappa_eq
  have hmeas := measurable_Ufeat hL ε
  have hmom := exact_shift_symmetries_and_feature_moments hL ε
  set c : ℝ := min ((1 / 22 : ℝ) / 4) (γ / (2 * kappa ^ 2)) with hcdef
  have hc : 0 < c := lt_min (by norm_num) (by positivity)
  have hbd : ∀ t : E2, ‖t‖ ≤ kappa → c * ‖t‖ ^ 2 ≤ featurePotential kappa0 (Ufeat L ε) t := by
    intro t ht
    rw [hcdef, hkeq]
    exact quadratic_bound_of_gap hRk hγ hgap hclose
      (fun t ht => (uniform_convex_neighborhood_of_zero hmeas (fun y => (norm_Ufeat L ε y).le)
        hmom.1.2.2.1 hmom.1.2.2.2).2.2.2.2.2.2 t ht) t (hkeq ▸ ht)
  set S : Set E2 := {t : E2 | 0 < ‖t‖ ∧ ‖t‖ ≤ kappa} with hS
  set f : E2 → ℝ := fun t => featurePotential kappa0 (Ufeat L ε) t / ‖t‖ ^ 2 with hf
  have hne : (f '' S).Nonempty := by
    refine ⟨f (kappa • vertex 0), kappa • vertex 0, ⟨?_, ?_⟩, rfl⟩
    · rw [norm_smul, norm_vertex, Real.norm_eq_abs, abs_of_pos hk, mul_one]; exact hk
    · rw [norm_smul, norm_vertex, Real.norm_eq_abs, abs_of_pos hk, mul_one]
  have hlb : ∀ x ∈ f '' S, c ≤ x := by
    rintro _ ⟨t, ⟨ht0, ht1⟩, rfl⟩
    rw [hf]
    exact (le_div_iff₀ (by positivity)).2 (hbd t ht1)
  have hglb : IsGLB (f '' S) (sInf (f '' S)) := isGLB_csInf hne ⟨c, hlb⟩
  have hca : c ≤ sInf (f '' S) := le_csInf hne hlb
  refine ⟨sInf (f '' S), hglb, lt_of_lt_of_le hc hca, hca, fun ν => ?_⟩
  have ha : 0 < sInf (f '' S) := lt_of_lt_of_le hc hca
  refine coercivity_inequality hL ε ha (fun t ht => ?_) ν
  by_cases h0 : t = 0
  · rw [h0]; simpa using hnn 0
  · have ht0 : 0 < ‖t‖ := norm_pos_iff.2 h0
    have := hglb.1 ⟨t, ⟨ht0, ht⟩, rfl⟩
    rw [hf] at this
    exact (le_div_iff₀ (by positivity)).1 this

/-- **RUF030.** In the common family of RUF026 (with `γ` the RUF023 annulus gap over
`1/352 ≤ ‖t‖ ≤ R`, `R > 2κ`), for every feature `U_{L,ε}` the infimum
`a = inf_{0<‖t‖≤κ} Ψ(t)/‖t‖²` is positive, at least `min {h/4, γ/(2κ²)}` with `h = 1/22`, and
`G(ρ) = F(ρ m) - κ/2 ≥ [2κa/(1+2κa)] H(ρ m | m)` for every probability measure, with value `⊤` on
the right (hence on the left) at infinite entropy. -/
theorem model_specific_global_entropy_coercivity :
    ∃ R : ℝ, 2 * kappa0 < R ∧ ∃ γ : ℝ,
      IsLeast (orderPotential '' {t : E2 | (1 / 352 : ℝ) ≤ ‖t‖ ∧ ‖t‖ ≤ R}) γ ∧ 0 < γ ∧
      ∃ ε₀ L₀ : ℝ, 0 < ε₀ ∧ 1 ≤ L₀ ∧ 1 / ε₀ ≤ L₀ ∧
        (∀ L : ℝ, L₀ ≤ L → ∀ ε : ℝ, |ε| ≤ ε₀ → ModelEntropyCoercivity L ε γ) ∧
        ∃ L_fixed : ℝ, L₀ ≤ L_fixed ∧ 1 / L_fixed ≤ ε₀ ∧
          ModelEntropyCoercivity L_fixed (1 / L_fixed) γ := by
  obtain ⟨R, hR, γ, hγl, hγ, ε₀, L₀, h1, h2, h3, hfam, L, h5, h6⟩ := selection_with_gap
  have hRk : kappa0 ≤ R := by linarith [kappa0_pos]
  have hgap : ∀ t : E2, (1 / 352 : ℝ) ≤ ‖t‖ → ‖t‖ ≤ R → γ ≤ orderPotential t :=
    fun t ha hb => hγl.2 ⟨t, ⟨ha, hb⟩, rfl⟩
  refine ⟨R, hR, γ, hγl, hγ, ε₀, L₀, h1, h2, h3, fun L hL ε hε => ?_, L, h5, h6, ?_⟩
  · exact modelEntropyCoercivity_of_bounds (hfam L hL ε hε).1 hRk hγ hgap (hfam L hL ε hε).2
  · have h7 : |1 / L| ≤ ε₀ := by
      rw [abs_of_pos (by have : 0 < L := by linarith
                         positivity)]
      exact h6
    exact modelEntropyCoercivity_of_bounds (hfam L h5 _ h7).1 hRk hγ hgap (hfam L h5 _ h7).2

end DGPS.Examples.RoughBoundary.FreeEnergy
