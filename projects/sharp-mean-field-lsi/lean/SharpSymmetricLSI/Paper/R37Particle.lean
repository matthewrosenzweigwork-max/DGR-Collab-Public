import SharpSymmetricLSI.Paper.R7Basic
import SharpSymmetricLSI.Defs.D14_Conditional

/-!
# R37 (Remark 8.1): the particle conjuncts (Phase 2, I1, milestone 7)

For a probability `ν ≪ P_N` with `f = √(dν/dP_N)`: `H(ν|P_N) = Ent_{P_N}(f²)` and
`I(ν|P_N) = 4ℰ_N(f)` (`⊤` off `H¹(P_N)`); conversely every `f ∈ H¹(P_N)` with
`Ent_{P_N}(f²) > 0` gives `ν = f² P_N/‖f‖²` with `0 < H(ν|P_N) < ⊤` (`ent_sq_lt_top`).
Symmetric `ν` have symmetric densities, and the symmetrization of `f` is a symmetric
representative. Hence the particle infima of Remark 8.1 are `2r_N^sym/β` and `2r_N^all/β`.
-/

open MeasureTheory InformationTheory Filter
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ}

/-! ### Rescaling (1.2) -/

theorem hyp_smul {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}
    (hyp : Hyp V W KV KW) {β : ℝ} (hβ : 0 < β) :
    Hyp (fun x => β * V x) (fun x y => β * W x y) (β * KV) (β * KW) where
  KV_nonneg := mul_nonneg hβ.le hyp.KV_nonneg
  KW_nonneg := mul_nonneg hβ.le hyp.KW_nonneg
  continuous_V := continuous_const.mul hyp.continuous_V
  continuous_W := continuous_const.mul hyp.continuous_W
  semiconvex_V φ hφ hφc hφ0 ξ := by
    have h := hyp.semiconvex_V φ hφ hφc hφ0 ξ
    simp_rw [mul_assoc β]
    rw [integral_const_mul]
    have := mul_le_mul_of_nonneg_left h hβ.le
    linarith
  semiconvex_W φ hφ hφc hφ0 ξ := by
    have h := hyp.semiconvex_W φ hφ hφc hφ0 ξ
    simp_rw [mul_assoc β]
    rw [integral_const_mul]
    have := mul_le_mul_of_nonneg_left h hβ.le
    linarith
  symm x y := by rw [hyp.symm]
  diag x := by rw [hyp.diag, mul_zero]

/-! ### `flat` as a measurable equivalence -/

theorem measurable_unflat {N : ℕ} :
    Measurable (unflat : UnitAddTorus (Fin N × Fin d) → Config N d) :=
  measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun k =>
    measurable_pi_apply (X := fun _ : Fin N × Fin d => UnitAddCircle) (i, k)

/-- `flat` as a measurable equivalence. -/
def flatEquiv (N d : ℕ) : Config N d ≃ᵐ UnitAddTorus (Fin N × Fin d) where
  toFun := flat
  invFun := unflat
  left_inv _ := rfl
  right_inv _ := rfl
  measurable_toFun := measurable_flat
  measurable_invFun := measurable_unflat

theorem measurableEmbedding_flat {N : ℕ} :
    MeasurableEmbedding (flat : Config N d → UnitAddTorus (Fin N × Fin d)) :=
  (flatEquiv N d).measurableEmbedding

/-! ### Almost-everywhere congruence for `H¹` -/

section Torus

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem IsWeakGrad.congr_ae {u v : UnitAddTorus ι → ℝ} {g : UnitAddTorus ι → ι → ℝ}
    (h : IsWeakGrad u g) (huv : u =ᵐ[volume] v) : IsWeakGrad v g where
  locInt := h.locInt.congr (ae_liftT_of_ae huv)
  locInt_grad := h.locInt_grad
  ibp φ hφ hφc k := by
    rw [← h.ibp φ hφ hφc k]
    refine integral_congr_ae ?_
    filter_upwards [ae_liftT_of_ae huv] with x hx
    rw [hx]

theorem weakGrad_congr_ae {u v : UnitAddTorus ι → ℝ} (hu : HasWeakGrad u)
    (huv : u =ᵐ[volume] v) : HasWeakGrad v ∧ weakGrad v =ᵐ[volume] weakGrad u := by
  have h := (isWeakGrad_weakGrad hu).congr_ae huv
  exact ⟨⟨_, h⟩, weakGrad_ae_eq h⟩

theorem memH1_congr_ae {Q : Measure (UnitAddTorus ι)} (hQ : Q ≪ volume) (hQ' : volume ≪ Q)
    {u v : UnitAddTorus ι → ℝ} (hu : MemH1 Q u) (huv : u =ᵐ[Q] v) :
    MemH1 Q v ∧ dirichlet Q v = dirichlet Q u := by
  obtain ⟨hg, hgg⟩ := weakGrad_congr_ae hu.1 (hQ'.ae_le huv)
  have hgg' := hQ.ae_le hgg
  refine ⟨⟨hg, hu.2.1.ae_eq huv, hu.2.2.ae_eq ?_⟩, ?_⟩
  · filter_upwards [hgg'] with y hy
    rw [hy]
  · unfold dirichlet
    refine lintegral_congr_ae ?_
    filter_upwards [hgg'] with y hy
    rw [hy]

end Torus

variable {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

theorem ae_flat_of_ae (hyp : Hyp V W KV KW) {N : ℕ} {p : UnitAddTorus (Fin N × Fin d) → Prop}
    (h : ∀ᵐ X ∂gibbs V W N, p (flat X)) : ∀ᵐ y ∂(volume : Measure (UnitAddTorus (Fin N × Fin d))),
      p y :=
  (gibbs_map_flat_ac hyp N).2.ae_le (measurableEmbedding_flat.ae_map_iff.mpr h)

theorem ae_map_flat_of_ae {N : ℕ} {P : Measure (Config N d)}
    {p : UnitAddTorus (Fin N × Fin d) → Prop} (h : ∀ᵐ X ∂P, p (flat X)) :
    ∀ᵐ y ∂(P.map flat), p y :=
  measurableEmbedding_flat.ae_map_iff.mpr h

theorem energy_eq_dirichlet (hyp : Hyp V W KV KW) {N : ℕ} {f : Config N d → ℝ}
    (hf : HasWeakGrad (f ∘ unflat)) :
    energy V W N f = dirichlet ((gibbs V W N).map flat) (f ∘ unflat) :=
  energy_eq hyp hf

/-- `H¹(P_N)` and `ℰ_N` depend only on the `P_N`-a.e. class. -/
theorem memH1C_congr_ae (hyp : Hyp V W KV KW) {N : ℕ} {f g : Config N d → ℝ}
    (hf : MemH1C (gibbs V W N) f) (hfg : f =ᵐ[gibbs V W N] g) :
    MemH1C (gibbs V W N) g ∧ energy V W N g = energy V W N f := by
  have h := memH1_congr_ae (gibbs_map_flat_ac hyp N).1 (gibbs_map_flat_ac hyp N).2 hf
    (ae_map_flat_of_ae (P := gibbs V W N) (p := fun y => (f ∘ unflat) y = (g ∘ unflat) y) hfg)
  exact ⟨h.1, by rw [energy_eq_dirichlet hyp h.1.1, energy_eq_dirichlet hyp hf.1, h.2]⟩

/-! ### Entropy -/

section Ent

variable {α : Type*} [MeasurableSpace α] {P : Measure α}

theorem ent_congr_ae {u v : α → ℝ} (huv : u =ᵐ[P] v) : ent P u = ent P v := by
  unfold ent
  have hi : Integrable u P ↔ Integrable v P := integrable_congr huv
  have hint : ∫ y, u y ∂P = ∫ y, v y ∂P := integral_congr_ae huv
  by_cases h : Integrable u P
  · rw [if_pos h, if_pos (hi.mp h), hint]
    refine lintegral_congr_ae ?_
    filter_upwards [huv] with x hx
    rw [hx]
  · rw [if_neg h, if_neg (fun h' => h (hi.mpr h'))]

theorem ent_eq_zero_of_integral_eq_zero {u : α → ℝ} (h : ∫ y, u y ∂P = 0) : ent P u = 0 ∨
    ¬ Integrable u P := by
  unfold ent
  by_cases hi : Integrable u P
  · left; rw [if_pos hi, h]; simp
  · right; exact hi

end Ent

/-! ### Permutation invariance -/

/-- `X ↦ X ∘ σ` as a measurable equivalence. -/
def permEquiv {N : ℕ} (σ : Equiv.Perm (Fin N)) : Config N d ≃ᵐ Config N d where
  toFun X := X ∘ σ
  invFun X := X ∘ σ.symm
  left_inv X := by funext i; simp
  right_inv X := by funext i; simp
  measurable_toFun := measurable_pi_iff.mpr fun i => measurable_pi_apply (σ i)
  measurable_invFun := measurable_pi_iff.mpr fun i => measurable_pi_apply (σ.symm i)

theorem permEquiv_apply {N : ℕ} (σ : Equiv.Perm (Fin N)) (X : Config N d) :
    permEquiv σ X = X ∘ σ := rfl

theorem permEquiv_symm_apply {N : ℕ} (σ : Equiv.Perm (Fin N)) (X : Config N d) :
    (permEquiv σ).symm X = X ∘ σ.symm := rfl

theorem volume_map_perm {N : ℕ} (σ : Equiv.Perm (Fin N)) :
    (volume : Measure (Config N d)).map (permEquiv σ) = volume := by
  symm
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.map_apply (permEquiv σ).measurable (MeasurableSet.univ_pi hs)]
  have : (permEquiv σ : Config N d → Config N d) ⁻¹' Set.univ.pi s =
      Set.univ.pi fun i => s (σ.symm i) := by
    ext X
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, permEquiv_apply,
      Function.comp_apply]
    exact ⟨fun h i => by simpa using h (σ.symm i), fun h i => by simpa using h (σ i)⟩
  rw [this, volume_pi_pi]
  exact Equiv.prod_comp σ.symm (fun i => volume (s i))

theorem hamiltonian_perm {N : ℕ} (σ : Equiv.Perm (Fin N)) (X : Config N d) :
    hamiltonian V W N (X ∘ σ) = hamiltonian V W N X := by
  unfold hamiltonian
  simp only [Function.comp_apply]
  rw [Equiv.sum_comp σ (fun i => V (X i))]
  congr 2
  rw [Equiv.sum_comp σ (fun i => ∑ j, W (X i) (X (σ j)))]
  exact Finset.sum_congr rfl fun i _ => Equiv.sum_comp σ (fun j => W (X i) (X j))

theorem map_withDensity_equiv {α : Type*} [MeasurableSpace α] (e : α ≃ᵐ α) (μ : Measure α)
    {ρ : α → ℝ≥0∞} (hρ : Measurable ρ) :
    (μ.withDensity ρ).map e = (μ.map e).withDensity (ρ ∘ e.symm) := by
  ext s hs
  rw [Measure.map_apply e.measurable hs, withDensity_apply _ (e.measurable hs),
    withDensity_apply _ hs, setLIntegral_map hs (hρ.comp e.symm.measurable) e.measurable]
  simp

theorem gibbs_map_perm (hyp : Hyp V W KV KW) {N : ℕ} (σ : Equiv.Perm (Fin N)) :
    (gibbs V W N).map (permEquiv σ) = gibbs V W N := by
  rw [show gibbs V W N = (volume : Measure (Config N d)).withDensity
      (gibbsDensity volume (hamiltonian V W N)) from rfl,
    map_withDensity_equiv _ _ (measurable_gibbsDensity _ (continuous_hamiltonian hyp N)),
    volume_map_perm]
  congr 1
  funext X
  simp only [Function.comp_apply, gibbsDensity, permEquiv_symm_apply, hamiltonian_perm]

theorem measurePreserving_perm (hyp : Hyp V W KV KW) {N : ℕ} (σ : Equiv.Perm (Fin N)) :
    MeasurePreserving (permEquiv σ) (gibbs V W N) (gibbs V W N) :=
  ⟨(permEquiv σ).measurable, gibbs_map_perm hyp σ⟩

/-- `X ↦ (N!)⁻¹ ∑_σ f(X ∘ σ)`. -/
noncomputable def symmetrize {N : ℕ} (f : Config N d → ℝ) (X : Config N d) : ℝ :=
  (Fintype.card (Equiv.Perm (Fin N)) : ℝ)⁻¹ * ∑ σ : Equiv.Perm (Fin N), f (X ∘ σ)

theorem isSymmetric_symmetrize {N : ℕ} (f : Config N d → ℝ) : IsSymmetric (symmetrize f) := by
  intro τ X
  unfold symmetrize
  congr 1
  exact Equiv.sum_comp (Equiv.mulLeft τ) (fun σ => f (X ∘ σ))

theorem measurable_symmetrize {N : ℕ} {f : Config N d → ℝ} (hf : Measurable f) :
    Measurable (symmetrize f) :=
  measurable_const.mul (Finset.measurable_sum _ fun σ _ => hf.comp (permEquiv σ).measurable)

theorem symmetrize_ae_eq {N : ℕ} {P : Measure (Config N d)} {f : Config N d → ℝ}
    (hf : ∀ σ : Equiv.Perm (Fin N), (fun X => f (X ∘ σ)) =ᵐ[P] f) : symmetrize f =ᵐ[P] f := by
  filter_upwards [ae_all_iff.mpr hf] with X hX
  unfold symmetrize
  simp_rw [hX]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
    inv_mul_cancel₀ (by exact_mod_cast Fintype.card_ne_zero), one_mul]

/-- A measurable representative, symmetric if `f` is. -/
theorem exists_measurable_rep (hyp : Hyp V W KV KW) {N : ℕ} {f : Config N d → ℝ}
    (hf : AEStronglyMeasurable f (gibbs V W N)) :
    ∃ g : Config N d → ℝ, Measurable g ∧ g =ᵐ[gibbs V W N] f ∧ (IsSymmetric f → IsSymmetric g) := by
  by_cases hs : IsSymmetric f
  · refine ⟨symmetrize (hf.mk f), measurable_symmetrize hf.stronglyMeasurable_mk.measurable,
      ?_, fun _ => isSymmetric_symmetrize _⟩
    have h1 : ∀ σ : Equiv.Perm (Fin N), (fun X => hf.mk f (X ∘ σ)) =ᵐ[gibbs V W N] f := by
      intro σ
      have := (measurePreserving_perm hyp σ).quasiMeasurePreserving.ae_eq_comp hf.ae_eq_mk.symm
      filter_upwards [this] with X hX
      simp only [Function.comp_apply, permEquiv_apply] at hX
      rw [hX, hs σ X]
    refine (symmetrize_ae_eq fun σ => ?_).trans hf.ae_eq_mk.symm
    exact (h1 σ).trans hf.ae_eq_mk
  · exact ⟨hf.mk f, hf.stronglyMeasurable_mk.measurable, hf.ae_eq_mk.symm, fun h => (hs h).elim⟩

/-! ### Densities, entropy and Fisher information -/

/-- `√(dν/dP)`. -/
noncomputable def sqrtDens {N : ℕ} (ν P : Measure (Config N d)) (X : Config N d) : ℝ :=
  Real.sqrt (ν.rnDeriv P X).toReal

theorem klDiv_eq_ent {N : ℕ} {ν P : Measure (Config N d)} [IsProbabilityMeasure ν]
    [IsProbabilityMeasure P] (hac : ν ≪ P) :
    klDiv ν P = ent P (fun X => sqrtDens ν P X ^ 2) := by
  simp_rw [sqrtDens, Real.sq_sqrt ENNReal.toReal_nonneg]
  rw [klDiv_eq_lintegral_klFun_of_ac hac, ent_normalized P Measure.integrable_toReal_rnDeriv
    (by rw [Measure.integral_toReal_rnDeriv hac]; simp)]

open Classical in
theorem fisherInfoC_eq (hyp : Hyp V W KV KW) {N : ℕ} {ν : Measure (Config N d)}
    [IsFiniteMeasure ν] (hac : ν ≪ gibbs V W N) :
    fisherInfoC ν (gibbs V W N) = if MemH1C (gibbs V W N) (sqrtDens ν (gibbs V W N)) then
      4 * energy V W N (sqrtDens ν (gibbs V W N)) else ⊤ := by
  have : IsProbabilityMeasure (gibbs V W N) := gibbs_isProbabilityMeasure hyp N
  set P := gibbs V W N with hP
  have hmap := measurableEmbedding_flat.rnDeriv_map ν P
  set u : UnitAddTorus (Fin N × Fin d) → ℝ :=
    fun y => Real.sqrt ((ν.map flat).rnDeriv (P.map flat) y).toReal with hu_def
  have hu : (sqrtDens ν P ∘ unflat) =ᵐ[P.map flat] u := by
    refine ae_map_flat_of_ae (p := fun y => (sqrtDens ν P ∘ unflat) y = u y) ?_
    filter_upwards [hmap] with X hX
    simp only [Function.comp_apply, hu_def, sqrtDens]
    rw [hX]; rfl
  have hac1 := (gibbs_map_flat_ac hyp N).1
  have hac2 := (gibbs_map_flat_ac hyp N).2
  unfold fisherInfoC fisherInfo
  have hac' : ν.map flat ≪ P.map flat := hac.map measurable_flat
  simp only [hac', true_and]
  by_cases hf : MemH1C P (sqrtDens ν P)
  · have hc := memH1_congr_ae hac1 hac2 hf hu
    rw [if_pos hc.1, if_pos hf, hc.2, energy_eq_dirichlet hyp hf.1]
  · have : ¬ MemH1 (P.map flat) u := fun h => hf (memH1_congr_ae hac1 hac2 h hu.symm).1
    rw [if_neg this, if_neg hf]

theorem sqrtDens_perm_ae (hyp : Hyp V W KV KW) {N : ℕ} {ν : Measure (Config N d)}
    [IsFiniteMeasure ν] (hν : IsSymmetricMeasure ν) (σ : Equiv.Perm (Fin N)) :
    (fun X => sqrtDens ν (gibbs V W N) (X ∘ σ)) =ᵐ[gibbs V W N] sqrtDens ν (gibbs V W N) := by
  have : IsProbabilityMeasure (gibbs V W N) := gibbs_isProbabilityMeasure hyp N
  have h := (permEquiv σ).measurableEmbedding.rnDeriv_map ν (gibbs V W N)
  rw [show ν.map (permEquiv σ) = ν from hν σ, gibbs_map_perm hyp σ] at h
  filter_upwards [h] with X hX
  simp only [sqrtDens]
  rw [← hX]; rfl

/-! ### The probability `f² P_N / ‖f‖²` -/

theorem integral_sq_pos_of_ent_pos (hyp : Hyp V W KV KW) {N : ℕ} {f : Config N d → ℝ}
    (hf : MemH1C (gibbs V W N) f) (hent : 0 < ent (gibbs V W N) (fun X => f X ^ 2)) :
    0 < ∫ X, f X ^ 2 ∂gibbs V W N := by
  rcases (integral_nonneg fun X => sq_nonneg (f X) : 0 ≤ ∫ X, f X ^ 2 ∂gibbs V W N).eq_or_lt
    with h | h
  · rcases ent_eq_zero_of_integral_eq_zero h.symm with h0 | hi
    · rw [h0] at hent; exact (lt_irrefl _ hent).elim
    · exact (hi (memLp_of_memH1C hyp hf).integrable_sq).elim
  · exact h

/-- `ν_g = g² P / ‖g‖²`. -/
noncomputable def sqMeasure {N : ℕ} (P : Measure (Config N d)) (g : Config N d → ℝ) :
    Measure (Config N d) :=
  P.withDensity fun X => ENNReal.ofReal (g X ^ 2 / ∫ Y, g Y ^ 2 ∂P)

theorem sqMeasure_props (hyp : Hyp V W KV KW) {N : ℕ} {g : Config N d → ℝ} (hgm : Measurable g)
    (hg : MemH1C (gibbs V W N) g) (hent : 0 < ent (gibbs V W N) (fun X => g X ^ 2)) :
    IsProbabilityMeasure (sqMeasure (gibbs V W N) g) ∧ sqMeasure (gibbs V W N) g ≪ gibbs V W N ∧
      klDiv (sqMeasure (gibbs V W N) g) (gibbs V W N) =
        ENNReal.ofReal (∫ Y, g Y ^ 2 ∂gibbs V W N)⁻¹ * ent (gibbs V W N) (fun X => g X ^ 2) ∧
      MemH1C (gibbs V W N) (sqrtDens (sqMeasure (gibbs V W N) g) (gibbs V W N)) ∧
      energy V W N (sqrtDens (sqMeasure (gibbs V W N) g) (gibbs V W N)) =
        ENNReal.ofReal (∫ Y, g Y ^ 2 ∂gibbs V W N)⁻¹ * energy V W N g ∧
      (IsSymmetric g → IsSymmetricMeasure (sqMeasure (gibbs V W N) g)) := by
  have : IsProbabilityMeasure (gibbs V W N) := gibbs_isProbabilityMeasure hyp N
  set P := gibbs V W N with hP
  set c := ∫ Y, g Y ^ 2 ∂P with hc_def
  have hc : 0 < c := integral_sq_pos_of_ent_pos hyp hg hent
  have hi : Integrable (fun X => g X ^ 2) P := (memLp_of_memH1C hyp hg).integrable_sq
  have hρm : Measurable fun X => ENNReal.ofReal (g X ^ 2 / c) :=
    ENNReal.measurable_ofReal.comp ((hgm.pow_const 2).div_const c)
  have hprob : IsProbabilityMeasure (sqMeasure P g) := by
    refine ⟨?_⟩
    rw [sqMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal (hi.div_const c)
        (ae_of_all _ fun X => div_nonneg (sq_nonneg _) hc.le), integral_div, div_self hc.ne',
      ENNReal.ofReal_one]
  have hac : sqMeasure P g ≪ P := withDensity_absolutelyContinuous _ _
  have hrn := Measure.rnDeriv_withDensity P hρm
  have hsd : sqrtDens (sqMeasure P g) P =ᵐ[P] fun X => (Real.sqrt c)⁻¹ * |g X| := by
    filter_upwards [hrn] with X hX
    simp only [sqrtDens]
    rw [show sqMeasure P g = P.withDensity fun X => ENNReal.ofReal (g X ^ 2 / c) from rfl, hX,
      ENNReal.toReal_ofReal (div_nonneg (sq_nonneg _) hc.le), Real.sqrt_div (sq_nonneg _),
      Real.sqrt_sq_eq_abs, div_eq_inv_mul]
  have hH1 : MemH1C P (fun X => (Real.sqrt c)⁻¹ * |g X|) :=
    memH1C_smul hyp (memH1C_abs hyp hg) _
  have hcong := memH1C_congr_ae hyp hH1 hsd.symm
  have hsq : ((Real.sqrt c)⁻¹) ^ 2 = c⁻¹ := by rw [inv_pow, Real.sq_sqrt hc.le]
  refine ⟨hprob, hac, ?_, hcong.1, ?_, ?_⟩
  · rw [klDiv_eq_ent hac, ← ent_const_mul P hi (inv_nonneg.mpr hc.le)]
    refine ent_congr_ae ?_
    filter_upwards [hsd] with X hX
    rw [hX, mul_pow, hsq, sq_abs]
  · rw [hcong.2, energy_smul hyp (memH1C_abs hyp hg), energy_abs hyp hg, hsq]
  · intro hs σ
    change (sqMeasure P g).map (permEquiv σ) = sqMeasure P g
    rw [show sqMeasure P g = P.withDensity fun X => ENNReal.ofReal (g X ^ 2 / c) from rfl,
      map_withDensity_equiv _ _ hρm, hP, gibbs_map_perm hyp]
    congr 1
    funext X
    simp only [Function.comp_apply, permEquiv_symm_apply, hs σ.symm X]

/-! ### The particle infima -/

theorem ratio_eq_of_memH1C (hyp : Hyp V W KV KW) {N : ℕ} {ν : Measure (Config N d)}
    [IsProbabilityMeasure ν] (hac : ν ≪ gibbs V W N)
    (hf : MemH1C (gibbs V W N) (sqrtDens ν (gibbs V W N))) (b : ℝ≥0∞) :
    b * fisherInfoC ν (gibbs V W N) / klDiv ν (gibbs V W N) =
      b * 2 * (2 * energy V W N (sqrtDens ν (gibbs V W N)) /
        ent (gibbs V W N) (fun X => sqrtDens ν (gibbs V W N) X ^ 2)) := by
  have : IsProbabilityMeasure (gibbs V W N) := gibbs_isProbabilityMeasure hyp N
  rw [fisherInfoC_eq hyp hac, if_pos hf, klDiv_eq_ent hac]
  simp only [div_eq_mul_inv]
  ring

theorem ratio_eq_top (hyp : Hyp V W KV KW) {β : ℝ} (hβ : 0 < β) {N : ℕ}
    {ν : Measure (Config N d)} [IsProbabilityMeasure ν] (hac : ν ≪ gibbs V W N)
    (hfin : klDiv ν (gibbs V W N) < ⊤) (hf : ¬ MemH1C (gibbs V W N) (sqrtDens ν (gibbs V W N))) :
    ENNReal.ofReal β⁻¹ * fisherInfoC ν (gibbs V W N) / klDiv ν (gibbs V W N) = ⊤ := by
  rw [fisherInfoC_eq hyp hac, if_neg hf, ENNReal.mul_top (by simp [hβ]),
    ENNReal.top_div_of_ne_top hfin.ne]

theorem scaled_ratio {a E H : ℝ≥0∞} (ha0 : a ≠ 0) (hat : a ≠ ⊤) :
    2 * (a * E) / (a * H) = 2 * E / H := by
  rw [mul_left_comm, ENNReal.mul_div_mul_left _ _ ha0 hat]

theorem rescale_inf {β : ℝ} (hβ : 0 < β) {α : Type*} (S : Set α) (R : α → ℝ≥0∞) :
    2 * (⨅ f ∈ S, R f) / ENNReal.ofReal β = ⨅ f ∈ S, ENNReal.ofReal β⁻¹ * 2 * R f := by
  have hb : ENNReal.ofReal β⁻¹ * 2 ≠ 0 := by simp [hβ]
  have hbt : ENNReal.ofReal β⁻¹ * 2 ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by norm_num)
  rw [div_eq_mul_inv, ← ENNReal.ofReal_inv_of_pos hβ, mul_comm, ← mul_assoc]
  simp_rw [ENNReal.mul_iInf_of_ne hb hbt]

/-- The measure built from `f`, as a competitor. -/
theorem exists_competitor (hyp : Hyp V W KV KW) {N : ℕ} {f : Config N d → ℝ}
    (hf : MemH1C (gibbs V W N) f) (hent : 0 < ent (gibbs V W N) (fun X => f X ^ 2)) (b : ℝ≥0∞) :
    ∃ ν : Measure (Config N d), IsProbabilityMeasure ν ∧ (IsSymmetric f → IsSymmetricMeasure ν) ∧
      ν ≪ gibbs V W N ∧ 0 < klDiv ν (gibbs V W N) ∧ klDiv ν (gibbs V W N) < ⊤ ∧
      b * fisherInfoC ν (gibbs V W N) / klDiv ν (gibbs V W N) =
        b * 2 * (2 * energy V W N f / ent (gibbs V W N) (fun X => f X ^ 2)) := by
  have : IsProbabilityMeasure (gibbs V W N) := gibbs_isProbabilityMeasure hyp N
  obtain ⟨g, hgm, hgf, hgs⟩ := exists_measurable_rep hyp (memLp_of_memH1C hyp hf).aestronglyMeasurable
  have hg := memH1C_congr_ae hyp hf hgf.symm
  have hentg : ent (gibbs V W N) (fun X => g X ^ 2) = ent (gibbs V W N) (fun X => f X ^ 2) :=
    ent_congr_ae (hgf.mono fun X hX => by simp only [hX])
  obtain ⟨hprob, hac, hkl, hH1, hen, hsym⟩ := sqMeasure_props hyp hgm hg.1 (hentg ▸ hent)
  have hc := integral_sq_pos_of_ent_pos hyp hg.1 (hentg ▸ hent)
  have ha0 : ENNReal.ofReal (∫ Y, g Y ^ 2 ∂gibbs V W N)⁻¹ ≠ 0 := by simp [hc]
  refine ⟨sqMeasure (gibbs V W N) g, hprob, fun hs => hsym (hgs hs), hac, ?_, ?_, ?_⟩
  · rw [hkl, hentg]; exact ENNReal.mul_pos ha0 hent.ne'
  · rw [hkl]; exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ent_sq_lt_top_aux hyp hg.1)
  · rw [ratio_eq_of_memH1C hyp hac hH1, ← klDiv_eq_ent hac, hkl, hen,
      scaled_ratio ha0 ENNReal.ofReal_ne_top, hg.2, hentg]

/-- `inf_ν β⁻¹ I(ν|P_N)/H(ν|P_N) = 2 r_N^all/β`. -/
theorem particle_inf_all (hyp : Hyp V W KV KW) {β : ℝ} (hβ : 0 < β) (N : ℕ) :
    (⨅ ν ∈ {ν : Measure (Config N d) | IsProbabilityMeasure ν ∧ ν ≪ gibbs V W N ∧
        0 < klDiv ν (gibbs V W N) ∧ klDiv ν (gibbs V W N) < ⊤},
      ENNReal.ofReal β⁻¹ * fisherInfoC ν (gibbs V W N) / klDiv ν (gibbs V W N)) =
      2 * rAll V W N / ENNReal.ofReal β := by
  rw [rAll, rescale_inf hβ]
  apply le_antisymm
  · refine le_iInf₂ fun f hf => ?_
    obtain ⟨ν, hprob, -, hac, hpos, hfin, heq⟩ := exists_competitor hyp hf.1 hf.2
      (ENNReal.ofReal β⁻¹)
    exact (iInf₂_le ν ⟨hprob, hac, hpos, hfin⟩).trans_eq heq
  · refine le_iInf₂ fun ν hν => ?_
    obtain ⟨hprob, hac, hpos, hfin⟩ := hν
    by_cases hf : MemH1C (gibbs V W N) (sqrtDens ν (gibbs V W N))
    · rw [ratio_eq_of_memH1C hyp hac hf]
      have : IsProbabilityMeasure (gibbs V W N) := gibbs_isProbabilityMeasure hyp N
      exact iInf₂_le (sqrtDens ν (gibbs V W N)) ⟨hf, by rwa [← klDiv_eq_ent hac]⟩
    · rw [ratio_eq_top hyp hβ hac hfin hf]; exact le_top

/-- `inf_ν β⁻¹ I(ν|P_N)/H(ν|P_N) = 2 r_N^sym/β` over symmetric `ν`. -/
theorem particle_inf_sym (hyp : Hyp V W KV KW) {β : ℝ} (hβ : 0 < β) (N : ℕ) :
    (⨅ ν ∈ {ν : Measure (Config N d) | IsProbabilityMeasure ν ∧ IsSymmetricMeasure ν ∧
        ν ≪ gibbs V W N ∧ 0 < klDiv ν (gibbs V W N) ∧ klDiv ν (gibbs V W N) < ⊤},
      ENNReal.ofReal β⁻¹ * fisherInfoC ν (gibbs V W N) / klDiv ν (gibbs V W N)) =
      2 * rSym V W N / ENNReal.ofReal β := by
  rw [rSym, rescale_inf hβ]
  apply le_antisymm
  · refine le_iInf₂ fun f hf => ?_
    obtain ⟨ν, hprob, hsym, hac, hpos, hfin, heq⟩ := exists_competitor hyp hf.1 hf.2.2
      (ENNReal.ofReal β⁻¹)
    exact (iInf₂_le ν ⟨hprob, hsym hf.2.1, hac, hpos, hfin⟩).trans_eq heq
  · refine le_iInf₂ fun ν hν => ?_
    obtain ⟨hprob, hsym, hac, hpos, hfin⟩ := hν
    have : IsProbabilityMeasure (gibbs V W N) := gibbs_isProbabilityMeasure hyp N
    by_cases hf : MemH1C (gibbs V W N) (sqrtDens ν (gibbs V W N))
    · rw [ratio_eq_of_memH1C hyp hac hf]
      set f := sqrtDens ν (gibbs V W N)
      have hfs : symmetrize f =ᵐ[gibbs V W N] f := symmetrize_ae_eq (sqrtDens_perm_ae hyp hsym)
      have hcong := memH1C_congr_ae hyp hf hfs.symm
      have hent : ent (gibbs V W N) (fun X => symmetrize f X ^ 2) =
          ent (gibbs V W N) (fun X => f X ^ 2) :=
        ent_congr_ae (hfs.mono fun X hX => by simp only [hX])
      rw [← hcong.2, ← hent]
      refine iInf₂_le (symmetrize f) ⟨hcong.1, isSymmetric_symmetrize f, ?_⟩
      rw [hent, ← klDiv_eq_ent hac]; exact hpos
    · rw [ratio_eq_top hyp hβ hac hfin hf]; exact le_top

theorem rAll_div_le_rSym_div {β : ℝ} (N : ℕ) :
    2 * rAll V W N / ENNReal.ofReal β ≤ 2 * rSym V W N / ENNReal.ofReal β := by
  gcongr
  exact le_iInf₂ fun f hf => iInf₂_le f ⟨hf.1, hf.2.2⟩

/-- The particle conjuncts of Remark 8.1. -/
theorem physical_convention_particle (hyp : Hyp V W KV KW) {β : ℝ} (hβ : 0 < β) :
    ∀ N : ℕ, 1 ≤ N →
      (⨅ ν ∈ {ν : Measure (Config N d) | IsProbabilityMeasure ν ∧ IsSymmetricMeasure ν ∧
          ν ≪ gibbs (fun x => β * V x) (fun x y => β * W x y) N ∧
          0 < klDiv ν (gibbs (fun x => β * V x) (fun x y => β * W x y) N) ∧
          klDiv ν (gibbs (fun x => β * V x) (fun x y => β * W x y) N) < ⊤},
        ENNReal.ofReal β⁻¹ * fisherInfoC ν (gibbs (fun x => β * V x) (fun x y => β * W x y) N) /
          klDiv ν (gibbs (fun x => β * V x) (fun x y => β * W x y) N)) =
        2 * rSym (fun x => β * V x) (fun x y => β * W x y) N / ENNReal.ofReal β ∧
      (⨅ ν ∈ {ν : Measure (Config N d) | IsProbabilityMeasure ν ∧
          ν ≪ gibbs (fun x => β * V x) (fun x y => β * W x y) N ∧
          0 < klDiv ν (gibbs (fun x => β * V x) (fun x y => β * W x y) N) ∧
          klDiv ν (gibbs (fun x => β * V x) (fun x y => β * W x y) N) < ⊤},
        ENNReal.ofReal β⁻¹ * fisherInfoC ν (gibbs (fun x => β * V x) (fun x y => β * W x y) N) /
          klDiv ν (gibbs (fun x => β * V x) (fun x y => β * W x y) N)) =
        2 * rAll (fun x => β * V x) (fun x y => β * W x y) N / ENNReal.ofReal β ∧
      2 * rAll (fun x => β * V x) (fun x y => β * W x y) N / ENNReal.ofReal β ≤
        2 * rSym (fun x => β * V x) (fun x y => β * W x y) N / ENNReal.ofReal β := fun N _ =>
  ⟨particle_inf_sym (hyp_smul hyp hβ) hβ N, particle_inf_all (hyp_smul hyp hβ) hβ N,
    rAll_div_le_rSym_div N⟩

end SharpLSI
