import FullLabeledLSI.Defs.F04_Reveal
import SharpSymmetricLSI.Paper.Sec5_2
import SharpSymmetricLSI.Paper.Occ5
import SharpSymmetricLSI.Paper.AppAPos5

/-!
# Lemma 5.1 helpers: entropy part (5.1)

For densities `f, g` (positive, bounded above and below, measurable) of probability measures
`μ = m.withDensity f`, `ν = m.withDensity g` with respect to a probability measure `m`:
`H(μ|ν) = ∫ f log(f/g) dm`.
-/

noncomputable section
open MeasureTheory InformationTheory Real
open scoped ENNReal

namespace SharpLSI.FL

section KL

variable {α : Type*} [MeasurableSpace α]

theorem integrable_of_integral_one {m : Measure α} {f : α → ℝ}
    (h : ∫ x, f x ∂m = 1) : Integrable f m := by
  by_contra h'
  rw [integral_undef h'] at h
  exact zero_ne_one h

/-- `log(f/g)` is bounded when `f, g` are bounded above and below by positive constants. -/
theorem bdd_log_div {f g : α → ℝ} (hf : ∃ c C : ℝ, 0 < c ∧ ∀ x, c ≤ f x ∧ f x ≤ C)
    (hg : ∃ c C : ℝ, 0 < c ∧ ∀ x, c ≤ g x ∧ g x ≤ C) :
    ∃ B : ℝ, ∀ x, |Real.log (f x / g x)| ≤ B := by
  obtain ⟨c, C, hc, h⟩ := hf
  obtain ⟨c', C', hc', h'⟩ := hg
  refine ⟨|Real.log c| + |Real.log C| + |Real.log c'| + |Real.log C'|, fun x => ?_⟩
  have hfx : 0 < f x := lt_of_lt_of_le hc (h x).1
  have hgx : 0 < g x := lt_of_lt_of_le hc' (h' x).1
  rw [Real.log_div hfx.ne' hgx.ne']
  have h1 : Real.log c ≤ Real.log (f x) := Real.log_le_log hc (h x).1
  have h2 : Real.log (f x) ≤ Real.log C := Real.log_le_log hfx (h x).2
  have h3 : Real.log c' ≤ Real.log (g x) := Real.log_le_log hc' (h' x).1
  have h4 : Real.log (g x) ≤ Real.log C' := Real.log_le_log hgx (h' x).2
  rw [abs_le]
  constructor <;> nlinarith [neg_abs_le (Real.log c), abs_nonneg (Real.log c), le_abs_self (Real.log C),
    abs_nonneg (Real.log C), neg_abs_le (Real.log c'), abs_nonneg (Real.log c'),
    le_abs_self (Real.log C'), abs_nonneg (Real.log C'), le_abs_self (Real.log c),
    neg_abs_le (Real.log C), le_abs_self (Real.log c'), neg_abs_le (Real.log C')]

theorem rnDeriv_dens {m : Measure α} [IsFiniteMeasure m] {f g : α → ℝ} (hf : Measurable f)
    (hg : Measurable g) (hf0 : ∀ x, 0 < f x) (hg0 : ∀ x, 0 < g x) :
    ((m.withDensity fun x => ENNReal.ofReal (f x)).rnDeriv
      (m.withDensity fun x => ENNReal.ofReal (g x))) =ᵐ[m] fun x => ENNReal.ofReal (f x / g x) := by
  have hgm : Measurable fun x => ENNReal.ofReal (g x) := hg.ennreal_ofReal
  have hg0' : ∀ᵐ x ∂m, ENNReal.ofReal (g x) ≠ 0 :=
    Filter.Eventually.of_forall fun x => by simpa using hg0 x
  have hgt : ∀ᵐ x ∂m, ENNReal.ofReal (g x) ≠ ⊤ := Filter.Eventually.of_forall fun x => by simp
  have h1 := Measure.rnDeriv_withDensity_right (m.withDensity fun x => ENNReal.ofReal (f x)) m
    hgm.aemeasurable hg0' hgt
  have h2 := Measure.rnDeriv_withDensity m hf.ennreal_ofReal
  filter_upwards [h1, h2] with x hx1 hx2
  rw [hx1, hx2, ← ENNReal.ofReal_inv_of_pos (hg0 x), ← ENNReal.ofReal_mul (inv_nonneg.2 (hg0 x).le)]
  congr 1
  ring

theorem klDiv_dens {m : Measure α} [IsProbabilityMeasure m] {f g : α → ℝ} (hf : Measurable f)
    (hg : Measurable g) (hfb : ∃ c C : ℝ, 0 < c ∧ ∀ x, c ≤ f x ∧ f x ≤ C)
    (hgb : ∃ c C : ℝ, 0 < c ∧ ∀ x, c ≤ g x ∧ g x ≤ C) (hf1 : ∫ x, f x ∂m = 1)
    (hg1 : ∫ x, g x ∂m = 1) :
    klDiv (m.withDensity fun x => ENNReal.ofReal (f x))
        (m.withDensity fun x => ENNReal.ofReal (g x)) =
      ENNReal.ofReal (∫ x, f x * Real.log (f x / g x) ∂m) := by
  obtain ⟨cf, Cf, hcf, hf'⟩ := hfb
  obtain ⟨cg, Cg, hcg, hg'⟩ := hgb
  have hf0 : ∀ x, 0 < f x := fun x => lt_of_lt_of_le hcf (hf' x).1
  have hg0 : ∀ x, 0 < g x := fun x => lt_of_lt_of_le hcg (hg' x).1
  set μ := m.withDensity fun x => ENNReal.ofReal (f x) with hμ
  set ν := m.withDensity fun x => ENNReal.ofReal (g x) with hν
  have hfi : Integrable f m := integrable_of_integral_one hf1
  have hgi : Integrable g m := integrable_of_integral_one hg1
  have hμu : μ Set.univ = 1 := by
    rw [hμ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hfi (Filter.Eventually.of_forall fun x => (hf0 x).le), hf1]
    simp
  have hνu : ν Set.univ = 1 := by
    rw [hν, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hgi (Filter.Eventually.of_forall fun x => (hg0 x).le), hg1]
    simp
  have : IsFiniteMeasure μ := ⟨by rw [hμu]; exact ENNReal.one_lt_top⟩
  have : IsFiniteMeasure ν := ⟨by rw [hνu]; exact ENNReal.one_lt_top⟩
  have hgm : Measurable fun x => ENNReal.ofReal (g x) := hg.ennreal_ofReal
  have hmν : m ≪ ν := withDensity_absolutelyContinuous' hgm.aemeasurable
    (Filter.Eventually.of_forall fun x => by simpa using hg0 x)
  have hac : μ ≪ ν := (withDensity_absolutelyContinuous m _).trans hmν
  have hrn := rnDeriv_dens (m := m) hf hg hf0 hg0
  have hllr : llr μ ν =ᵐ[m] fun x => Real.log (f x / g x) := by
    filter_upwards [hrn] with x hx
    show Real.log (μ.rnDeriv ν x).toReal = _
    rw [hx, ENNReal.toReal_ofReal (div_pos (hf0 x) (hg0 x)).le]
  have hllrμ : llr μ ν =ᵐ[μ] fun x => Real.log (f x / g x) :=
    (withDensity_absolutelyContinuous m _).ae_le hllr
  obtain ⟨B, hB⟩ := bdd_log_div ⟨cf, Cf, hcf, hf'⟩ ⟨cg, Cg, hcg, hg'⟩
  have hlm : Measurable fun x => Real.log (f x / g x) := (hf.div hg).log
  have hint : Integrable (llr μ ν) μ := by
    refine Integrable.of_bound (C := B) (measurable_llr μ ν).aestronglyMeasurable ?_
    filter_upwards [hllrμ] with x hx
    rw [hx, Real.norm_eq_abs]; exact hB x
  rw [klDiv_of_ac_of_integrable hac hint]
  congr 1
  have hμr : μ.real Set.univ = 1 := by simp [measureReal_def, hμu]
  have hνr : ν.real Set.univ = 1 := by simp [measureReal_def, hνu]
  rw [hμr, hνr, add_sub_cancel_right, integral_congr_ae hllrμ, hμ,
    integral_withDensity_eq_integral_toReal_smul hf.ennreal_ofReal
      (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [smul_eq_mul, ENNReal.toReal_ofReal (hf0 x).le]

/-- `∫ f log(f/g) ≥ 0` for probability densities (Gibbs' inequality). -/
theorem integral_klterm_nonneg {m : Measure α} {f g : α → ℝ} (hf0 : ∀ x, 0 < f x)
    (hg0 : ∀ x, 0 < g x) (hfi : Integrable f m) (hgi : Integrable g m)
    (hkl : Integrable (fun x => f x * Real.log (f x / g x)) m)
    (h : ∫ x, f x ∂m = ∫ x, g x ∂m) : 0 ≤ ∫ x, f x * Real.log (f x / g x) ∂m := by
  have h1 : ∫ x, (f x - g x) ∂m ≤ ∫ x, f x * Real.log (f x / g x) ∂m := by
    refine integral_mono (hfi.sub hgi) hkl fun x => ?_
    have hx := Real.log_le_sub_one_of_pos (div_pos (hg0 x) (hf0 x))
    have : Real.log (g x / f x) = - Real.log (f x / g x) := by
      rw [← Real.log_inv, inv_div]
    rw [this] at hx
    have hfx := hf0 x
    have : f x * (g x / f x) = g x := by field_simp
    nlinarith [mul_le_mul_of_nonneg_left hx hfx.le]
  rw [integral_sub hfi hgi, h, sub_self] at h1
  exact h1

end KL

section Perm

variable {d N : ℕ}

/-- The permutation average of a measure (the body of `SharpLSI.FL.permAvg`, which is defined in
the statement file S18). -/
def permAvgAux (ν : Measure (Config N d)) : Measure (Config N d) :=
  ((Nat.factorial N : ℝ≥0∞)⁻¹) • ∑ σ : Equiv.Perm (Fin N), ν.map (fun X => X ∘ σ)

/-- The permutation average of a density, `(N!)⁻¹ ∑_σ u(X ∘ σ)`. -/
def avgDens (u : Config N d → ℝ) (X : Config N d) : ℝ :=
  ((Nat.factorial N : ℝ))⁻¹ * ∑ σ : Equiv.Perm (Fin N), u (X ∘ σ)

theorem avgDens_symm (u : Config N d → ℝ) (τ : Equiv.Perm (Fin N)) (X : Config N d) :
    avgDens u (X ∘ τ) = avgDens u X := by
  unfold avgDens
  congr 1
  exact Fintype.sum_equiv (Equiv.mulLeft τ) _ _ fun σ => by
    simp only [Equiv.coe_mulLeft]
    rfl

theorem measurable_avgDens {u : Config N d → ℝ} (hu : Measurable u) : Measurable (avgDens u) := by
  unfold avgDens
  refine Measurable.const_mul (Finset.measurable_sum _ fun σ _ => hu.comp ?_) _
  exact (permEquiv (d := d) σ).measurable

theorem avgDens_bounds {u : Config N d → ℝ} {c C : ℝ} (h : ∀ x, c ≤ u x ∧ u x ≤ C) (x : Config N d) :
    c ≤ avgDens u x ∧ avgDens u x ≤ C := by
  have hN : (0 : ℝ) < (Nat.factorial N : ℝ) := by exact_mod_cast Nat.factorial_pos N
  have hc : Fintype.card (Equiv.Perm (Fin N)) = Nat.factorial N := by simp [Fintype.card_perm]
  unfold avgDens
  constructor
  · have : ∑ _σ : Equiv.Perm (Fin N), c ≤ ∑ σ : Equiv.Perm (Fin N), u (x ∘ σ) :=
      Finset.sum_le_sum fun σ _ => (h _).1
    simp only [Finset.sum_const, Finset.card_univ, hc, nsmul_eq_mul] at this
    rw [le_inv_mul_iff₀ hN]; linarith
  · have : ∑ σ : Equiv.Perm (Fin N), u (x ∘ σ) ≤ ∑ _σ : Equiv.Perm (Fin N), C :=
      Finset.sum_le_sum fun σ _ => (h _).2
    simp only [Finset.sum_const, Finset.card_univ, hc, nsmul_eq_mul] at this
    rw [inv_mul_le_iff₀ hN]; linarith

theorem integral_comp_perm_vol (σ : Equiv.Perm (Fin N)) (F : Config N d → ℝ) :
    ∫ X, F (X ∘ σ) ∂(volume : Measure (Config N d)) = ∫ X, F X ∂(volume : Measure (Config N d)) :=
  integral_comp_perm (volume : Measure (Torus d)) σ F

theorem integrable_bdd {F : Config N d → ℝ} (hF : Measurable F) {B : ℝ} (hB : ∀ x, |F x| ≤ B) :
    Integrable F (volume : Measure (Config N d)) :=
  Integrable.of_bound hF.aestronglyMeasurable B (Filter.Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs]; exact hB x)

/-- `∫ (u ∘ σ) h = ∫ u h` for a symmetric `h`, hence `∫ ū h = ∫ u h`. -/
theorem integral_avgDens_mul {u h : Config N d → ℝ} (hu : Measurable u) (hh : Measurable h)
    {Bu Bh : ℝ} (hBu : ∀ x, |u x| ≤ Bu) (hBh : ∀ x, |h x| ≤ Bh)
    (hs : ∀ (σ : Equiv.Perm (Fin N)) X, h (X ∘ σ) = h X) :
    ∫ X, avgDens u X * h X ∂(volume : Measure (Config N d)) =
      ∫ X, u X * h X ∂(volume : Measure (Config N d)) := by
  have hmσ : ∀ σ : Equiv.Perm (Fin N), Measurable fun X : Config N d => X ∘ σ := fun σ =>
    (permEquiv (d := d) σ).measurable
  have hterm : ∀ σ : Equiv.Perm (Fin N), Integrable (fun X : Config N d => u (X ∘ σ) * h X)
      volume := fun σ =>
    integrable_bdd ((hu.comp (hmσ σ)).mul hh) (B := Bu * Bh) fun x => by
      rw [abs_mul]; exact mul_le_mul (hBu _) (hBh _) (abs_nonneg _) ((abs_nonneg _).trans (hBu x))
  have e1 : ∀ X, avgDens u X * h X =
      ((Nat.factorial N : ℝ))⁻¹ * ∑ σ : Equiv.Perm (Fin N), u (X ∘ σ) * h X := fun X => by
    unfold avgDens; rw [mul_assoc, Finset.sum_mul]
  have e2 : ∀ σ : Equiv.Perm (Fin N), ∫ X, u (X ∘ σ) * h X ∂(volume : Measure (Config N d)) =
      ∫ X, u X * h X ∂(volume : Measure (Config N d)) := fun σ => by
    rw [← integral_comp_perm_vol σ (fun X => u X * h X)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
    simp only [hs σ X]
  simp_rw [e1]
  rw [integral_const_mul, integral_finsetSum _ fun σ _ => hterm σ]
  simp only [e2, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    nsmul_eq_mul]
  have hN : (Nat.factorial N : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos N).ne'
  field_simp

theorem permAvg_withDensity {u : Config N d → ℝ} (hu : Measurable u) (hu0 : ∀ x, 0 ≤ u x) :
    permAvgAux ((volume : Measure (Config N d)).withDensity fun X => ENNReal.ofReal (u X)) =
      (volume : Measure (Config N d)).withDensity fun X => ENNReal.ofReal (avgDens u X) := by
  have hmeas : ∀ σ : Equiv.Perm (Fin N), Measurable fun X : Config N d => u (X ∘ σ.symm) :=
    fun σ => hu.comp (permEquiv (d := d) σ.symm).measurable
  have hmap : ∀ σ : Equiv.Perm (Fin N),
      ((volume : Measure (Config N d)).withDensity fun X => ENNReal.ofReal (u X)).map
        (fun X => X ∘ σ) =
      (volume : Measure (Config N d)).withDensity fun X => ENNReal.ofReal (u (X ∘ σ.symm)) := by
    intro σ
    have := map_withDensity_equiv (permEquiv (d := d) σ) (volume : Measure (Config N d))
      (ρ := fun X => ENNReal.ofReal (u X)) hu.ennreal_ofReal
    have hm : (volume : Measure (Config N d)).map (permEquiv (d := d) σ) = volume :=
      pi_map_perm (volume : Measure (Torus d)) σ
    rw [hm] at this
    exact this
  ext s hs
  unfold permAvgAux
  simp only [Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply, hmap,
    withDensity_apply _ hs, smul_eq_mul]
  rw [← lintegral_finsetSum _ fun σ _ => (hmeas σ).ennreal_ofReal,
    ← lintegral_const_mul' _ _ (by simp [Nat.factorial_ne_zero])]
  refine lintegral_congr fun X => ?_
  unfold avgDens
  have hN : (0 : ℝ) < (Nat.factorial N : ℝ) := by exact_mod_cast Nat.factorial_pos N
  rw [ENNReal.ofReal_mul (inv_nonneg.2 hN.le), ENNReal.ofReal_sum_of_nonneg (fun σ _ => hu0 _),
    ENNReal.ofReal_inv_of_pos hN]
  congr 1
  · simp
  · exact (Fintype.sum_equiv (Equiv.inv _) _ _ fun σ => by simp)

theorem continuous_of_isSmoothC {u : Config N d → ℝ} (hu : IsSmoothC u) : Continuous u := by
  have h : Continuous (u ∘ unflat) := continuous_of_isSmoothT hu
  have hf : Continuous (flat : Config N d → UnitAddTorus (Fin N × Fin d)) :=
    continuous_pi fun p => (continuous_apply p.2).comp (continuous_apply p.1)
  exact h.comp hf

theorem bdd_of_cont_pos {f : Config N d → ℝ} (hf : Continuous f) (h0 : ∀ x, 0 < f x) :
    ∃ c C : ℝ, 0 < c ∧ ∀ x, c ≤ f x ∧ f x ≤ C := by
  obtain ⟨x0, -, hmin⟩ := isCompact_univ.exists_isMinOn (Set.univ_nonempty) hf.continuousOn
  obtain ⟨x1, -, hmax⟩ := isCompact_univ.exists_isMaxOn (Set.univ_nonempty) hf.continuousOn
  exact ⟨f x0, f x1, h0 x0, fun x => ⟨hmin (Set.mem_univ x), hmax (Set.mem_univ x)⟩⟩

theorem integral_eq_one_of_prob {f : Config N d → ℝ} (hf : Measurable f) (h0 : ∀ x, 0 < f x)
    (hP : IsProbabilityMeasure
      ((volume : Measure (Config N d)).withDensity fun X => ENNReal.ofReal (f X))) :
    ∫ x, f x ∂(volume : Measure (Config N d)) = 1 := by
  have h1 := hP.measure_univ
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h1
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun x => (h0 x).le)
    hf.aestronglyMeasurable, h1]
  simp

end Perm


section Main

variable {d N : ℕ}

/-- Entropy part (5.1) of Lemma 5.1. -/
theorem permAvg_klDiv (ν : Measure (Config N d)) [IsProbabilityMeasure ν]
    (hν : HasSmoothPosDensity ν) (p : Config N d → ℝ) (hp : ∀ X, 0 < p X)
    (hpL : ∃ L, LipschitzWith L p) (hps : IsSymmetric p)
    (hP1 : IsProbabilityMeasure ((volume : Measure (Config N d)).withDensity
      fun X => ENNReal.ofReal (p X))) :
    klDiv ν ((volume : Measure (Config N d)).withDensity fun X => ENNReal.ofReal (p X)) =
      klDiv (permAvgAux ν) ((volume : Measure (Config N d)).withDensity
        fun X => ENNReal.ofReal (p X)) + klDiv ν (permAvgAux ν) := by
  obtain ⟨u, hus, hu0, rfl⟩ := hν
  have huc : Continuous u := continuous_of_isSmoothC hus
  have hum : Measurable u := huc.measurable
  obtain ⟨L, hL⟩ := hpL
  have hpc : Continuous p := hL.continuous
  have hpm : Measurable p := hpc.measurable
  have hub := bdd_of_cont_pos huc hu0
  have hpb := bdd_of_cont_pos hpc hp
  obtain ⟨cu, Cu, hcu, hu'⟩ := hub
  have hu1 : ∫ x, u x ∂(volume : Measure (Config N d)) = 1 := integral_eq_one_of_prob hum hu0 ‹_›
  have hp1 : ∫ x, p x ∂(volume : Measure (Config N d)) = 1 := integral_eq_one_of_prob hpm hp hP1
  have hūm : Measurable (avgDens u) := measurable_avgDens hum
  have hū' := avgDens_bounds hu'
  have hū0 : ∀ x, 0 < avgDens u x := fun x => lt_of_lt_of_le hcu (hū' x).1
  have hūb : ∃ c C : ℝ, 0 < c ∧ ∀ x, c ≤ avgDens u x ∧ avgDens u x ≤ C := ⟨cu, Cu, hcu, hū'⟩
  have hu1b : ∃ c C : ℝ, 0 < c ∧ ∀ x, c ≤ u x ∧ u x ≤ C := ⟨cu, Cu, hcu, hu'⟩
  have hū1 : ∫ x, avgDens u x ∂(volume : Measure (Config N d)) = 1 := by
    have := integral_avgDens_mul (u := u) (h := fun _ => (1 : ℝ)) hum measurable_const
      (Bu := Cu) (Bh := 1) (fun x => by
        rw [abs_of_pos (hu0 x)]; exact (hu' x).2) (fun _ => by simp) (fun _ _ => rfl)
    simpa [hu1] using this
  rw [permAvg_withDensity hum fun x => (hu0 x).le]
  rw [klDiv_dens hum hpm hu1b hpb hu1 hp1, klDiv_dens hūm hpm hūb hpb hū1 hp1,
    klDiv_dens hum hūm hu1b hūb hu1 hū1]
  -- the three integrals
  have hlogm : Measurable fun x => Real.log (avgDens u x / p x) := (hūm.div hpm).log
  obtain ⟨B1, hB1⟩ := bdd_log_div hūb hpb
  obtain ⟨B2, hB2⟩ := bdd_log_div hu1b hūb
  obtain ⟨B3, hB3⟩ := bdd_log_div hu1b hpb
  have hsym : ∀ (σ : Equiv.Perm (Fin N)) X, Real.log (avgDens u (X ∘ σ) / p (X ∘ σ)) =
      Real.log (avgDens u X / p X) := fun σ X => by rw [avgDens_symm, hps]
  have hkey : ∫ x, u x * Real.log (avgDens u x / p x) ∂(volume : Measure (Config N d)) =
      ∫ x, avgDens u x * Real.log (avgDens u x / p x) ∂(volume : Measure (Config N d)) :=
    (integral_avgDens_mul hum hlogm (Bu := Cu) (Bh := B1) (fun x => by
        rw [abs_of_pos (hu0 x)]; exact (hu' x).2) hB1 hsym).symm
  have hsplit : ∀ x, u x * Real.log (u x / p x) =
      u x * Real.log (u x / avgDens u x) + u x * Real.log (avgDens u x / p x) := fun x => by
    rw [← mul_add, ← Real.log_mul (div_pos (hu0 x) (hū0 x)).ne' (div_pos (hū0 x) (hp x)).ne']
    congr 2
    have := (hū0 x).ne'; have := (hp x).ne'
    field_simp
  have hi1 : Integrable (fun x => u x * Real.log (u x / avgDens u x))
      (volume : Measure (Config N d)) :=
    integrable_bdd (hum.mul (hum.div hūm).log) (B := Cu * B2) fun x => by
      rw [abs_mul, abs_of_pos (hu0 x)]; exact mul_le_mul (hu' x).2 (hB2 x) (abs_nonneg _)
        (hcu.le.trans ((hu' x).1.trans (hu' x).2))
  have hi2 : Integrable (fun x => u x * Real.log (avgDens u x / p x))
      (volume : Measure (Config N d)) :=
    integrable_bdd (hum.mul hlogm) (B := Cu * B1) fun x => by
      rw [abs_mul, abs_of_pos (hu0 x)]; exact mul_le_mul (hu' x).2 (hB1 x) (abs_nonneg _)
        (hcu.le.trans ((hu' x).1.trans (hu' x).2))
  have hi3 : Integrable (fun x => avgDens u x * Real.log (avgDens u x / p x))
      (volume : Measure (Config N d)) :=
    integrable_bdd (hūm.mul hlogm) (B := Cu * B1) fun x => by
      rw [abs_mul, abs_of_pos (hū0 x)]; exact mul_le_mul (hū' x).2 (hB1 x) (abs_nonneg _)
        (hcu.le.trans ((hū' x).1.trans (hū' x).2))
  have hui : Integrable u (volume : Measure (Config N d)) := integrable_of_integral_one hu1
  have hūi : Integrable (avgDens u) (volume : Measure (Config N d)) :=
    integrable_of_integral_one hū1
  have hpi : Integrable p (volume : Measure (Config N d)) := integrable_of_integral_one hp1
  have hn1 : 0 ≤ ∫ x, u x * Real.log (u x / avgDens u x) ∂(volume : Measure (Config N d)) :=
    integral_klterm_nonneg hu0 hū0 hui hūi hi1 (by rw [hu1, hū1])
  have hn2 : 0 ≤ ∫ x, avgDens u x * Real.log (avgDens u x / p x)
      ∂(volume : Measure (Config N d)) :=
    integral_klterm_nonneg hū0 hp hūi hpi hi3 (by rw [hū1, hp1])
  rw [← ENNReal.ofReal_add hn2 hn1]
  congr 1
  simp_rw [hsplit]
  rw [integral_add hi1 hi2, hkey]
  ring

end Main

end SharpLSI.FL
