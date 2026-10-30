import DGPS.Examples.ThreeSpeciesCircle.InteractingDeficitExpansion
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Positive-gap endpoint selection for finite-species support reduction

At fixed three feature moments, the gap and dissipation are affine in the weights.
A zero-gap endpoint cannot simply be discarded: its nonnegative dissipation is
used below to select a positive-gap endpoint without increasing the quotient.
-/

open MeasureTheory
open scoped ENNReal

namespace DGPS.Examples.ThreeSpeciesCircle

/-- The endpoint step needed by nullspace weight elimination. Zero-gap endpoints
are handled using their nonnegative dissipation, with no lower bound on weights. -/
theorem affine_positiveGap_endpoint {t gL gR dL dR q : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) (hgL : 0 ≤ gL) (hgR : 0 ≤ gR)
    (hdL : 0 ≤ dL) (hdR : 0 ≤ dR)
    (hgap : 0 < (1 - t) * gL + t * gR)
    (hcost : (1 - t) * (dL - 2 * q * gL) + t * (dR - 2 * q * gR) ≤ 0) :
    (0 < gL ∧ dL - 2 * q * gL ≤ 0) ∨
      (0 < gR ∧ dR - 2 * q * gR ≤ 0) := by
  by_cases hL : 0 < gL
  · by_cases hcL : dL - 2 * q * gL ≤ 0
    · exact Or.inl ⟨hL, hcL⟩
    · have hleft : 0 < (1 - t) * (dL - 2 * q * gL) :=
        mul_pos (sub_pos.mpr ht1) (lt_of_not_ge hcL)
      have hcR : dR - 2 * q * gR < 0 := by
        by_contra hn
        have hr := mul_nonneg ht0.le (not_lt.mp hn)
        linarith
      have hR : 0 < gR := by
        by_contra hn
        have hz : gR = 0 := le_antisymm (not_lt.mp hn) hgR
        rw [hz] at hcR
        nlinarith
      exact Or.inr ⟨hR, hcR.le⟩
  · have hz : gL = 0 := le_antisymm (not_lt.mp hL) hgL
    have hR : 0 < gR := by
      rw [hz] at hgap
      nlinarith
    have hleft : 0 ≤ (1 - t) * (dL - 2 * q * gL) := by
      rw [hz]
      simpa only [mul_zero, sub_zero] using mul_nonneg (sub_nonneg.mpr ht1.le) hdL
    have hcR : dR - 2 * q * gR ≤ 0 := by
      by_contra hn
      have hr := mul_pos ht0 (lt_of_not_ge hn)
      linarith
    exact Or.inr ⟨hR, hcR⟩

/-- Actual finite-family dissipation is nonnegative also at zero gap. This statement
uses the actual ENNReal dissipation and imposes no stationarity or rate hypothesis. -/
theorem species_zeroGap_dissipation_nonneg {d : ℕ} (A : InteractionData d)
    (b : AbsoluteDrift A) (F : SpeciesFamily d) (_hgap : speciesGap A F = 0) :
    0 ≤ (speciesDissipation A b F).toReal := ENNReal.toReal_nonneg

/-- The positive-gap endpoint conclusion for the actual family functionals. The
segment identities are factual affine-weight identities, not a quotient bound premise. -/
theorem species_positiveGap_endpoint_of_affine {d : ℕ} (A : InteractionData d)
    (b : AbsoluteDrift A) (F FL FR : SpeciesFamily d) {t q : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) (hpos : 0 < speciesGap A F)
    (hgap : (speciesGap A F : ℝ) =
      (1 - t) * (speciesGap A FL : ℝ) + t * (speciesGap A FR : ℝ))
    (hdiss : (speciesDissipation A b F).toReal =
      (1 - t) * (speciesDissipation A b FL).toReal +
        t * (speciesDissipation A b FR).toReal)
    (hq : (speciesDissipation A b F).toReal = 2 * q * (speciesGap A F : ℝ)) :
    (0 < speciesGap A FL ∧
      (speciesDissipation A b FL).toReal ≤ 2 * q * (speciesGap A FL : ℝ)) ∨
    (0 < speciesGap A FR ∧
      (speciesDissipation A b FR).toReal ≤ 2 * q * (speciesGap A FR : ℝ)) := by
  have hposR : 0 < (speciesGap A F : ℝ) := hpos
  have hc : (1 - t) * ((speciesDissipation A b FL).toReal -
      2 * q * (speciesGap A FL : ℝ)) +
      t * ((speciesDissipation A b FR).toReal - 2 * q * (speciesGap A FR : ℝ)) = 0 := by
    rw [hgap] at hq
    rw [hdiss] at hq
    nlinarith
  obtain h | h := affine_positiveGap_endpoint ht0 ht1
    (speciesGap A FL).coe_nonneg (speciesGap A FR).coe_nonneg
    ENNReal.toReal_nonneg ENNReal.toReal_nonneg (by rw [← hgap]; exact hposR) hc.le
  · exact Or.inl ⟨h.1, by linarith [h.2]⟩
  · exact Or.inr ⟨h.1, by linarith [h.2]⟩


private theorem threeMoment_null_direction {ι : Type*} [Fintype ι]
    (a : ι → Fin 3 → ℝ) (hcard : 4 < Fintype.card ι) :
    ∃ v : ι → ℝ, (∑ i, v i = 0) ∧
      (∀ j, ∑ i, v i * a i j = 0) ∧ ∃ i, v i ≠ 0 := by
  classical
  let U : ι → Fin 4 → ℝ := fun i => Fin.cons 1 (a i)
  have hnot : ¬LinearIndependent ℝ U := by
    intro h
    have hc : Fintype.card ι ≤ 4 := by simpa only [Module.finrank_pi, Fintype.card_fin] using h.fintype_card_le_finrank
    omega
  obtain ⟨v, hv, i, hi⟩ := Fintype.not_linearIndependent_iff.mp hnot
  refine ⟨v, ?_, ?_, i, hi⟩
  · have h := congrArg (fun f : Fin 4 → ℝ => f 0) hv
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, U,
      Fin.cons_zero, mul_one, Pi.zero_apply] using h
  · intro j
    have h := congrArg (fun f : Fin 4 → ℝ => f j.succ) hv
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, U,
      Fin.cons_succ, Pi.zero_apply] using h

private theorem orient_direction {ι : Type*} [Fintype ι]
    (a : ι → Fin 3 → ℝ) (g c v : ι → ℝ)
    (hm : ∑ i, v i = 0) (ha : ∀ j, ∑ i, v i * a i j = 0)
    (hv : ∃ i, v i ≠ 0) :
    ∃ u : ι → ℝ, (∑ i, u i = 0) ∧
      (∀ j, ∑ i, u i * a i j = 0) ∧ (∃ i, u i ≠ 0) ∧
      ((∑ i, u i * c i) < 0 ∨
        (∑ i, u i * c i) = 0 ∧ 0 ≤ ∑ i, u i * g i) := by
  classical
  have hn : (∑ i, -v i = 0) ∧
      (∀ j, ∑ i, -v i * a i j = 0) ∧ ∃ i, -v i ≠ 0 := by
    refine ⟨by simp [hm], fun j => ?_, ?_⟩
    · simp only [neg_mul, Finset.sum_neg_distrib, ha j, neg_zero]
    · obtain ⟨i, hi⟩ := hv
      exact ⟨i, neg_ne_zero.mpr hi⟩
  by_cases hc : (∑ i, v i * c i) < 0
  · exact ⟨v, hm, ha, hv, Or.inl hc⟩
  by_cases hcp : 0 < ∑ i, v i * c i
  · refine ⟨fun i => -v i, hn.1, hn.2.1, hn.2.2, Or.inl ?_⟩
    simpa only [neg_mul, Finset.sum_neg_distrib] using neg_neg_of_pos hcp
  have hz : (∑ i, v i * c i) = 0 := le_antisymm (not_lt.mp hcp) (not_lt.mp hc)
  by_cases hg : 0 ≤ ∑ i, v i * g i
  · exact ⟨v, hm, ha, hv, Or.inr ⟨hz, hg⟩⟩
  · refine ⟨fun i => -v i, hn.1, hn.2.1, hn.2.2, Or.inr ⟨?_, ?_⟩⟩
    · simp only [neg_mul, Finset.sum_neg_distrib, hz, neg_zero]
    · simpa only [neg_mul, Finset.sum_neg_distrib] using (neg_nonneg.mpr (not_le.mp hg).le)

/-- Moving along a nonzero mass-zero direction reaches a nonnegative weight vector
with an actual zero coordinate. The original positive weights need no uniform lower bound. -/
private theorem weight_boundary {ι : Type*} [Fintype ι]
    (w u : ι → ℝ) (hw : ∀ i, 0 < w i) (hu : ∑ i, u i = 0)
    (hne : ∃ i, u i ≠ 0) :
    ∃ t : ℝ, 0 < t ∧ (∀ i, 0 ≤ w i + t * u i) ∧
      ∃ i, w i + t * u i = 0 := by
  classical
  obtain ⟨j, -, hj⟩ := Finset.exists_neg_of_sum_zero_of_exists_nonzero u hu
    (by obtain ⟨i, hi⟩ := hne; exact ⟨i, Finset.mem_univ i, hi⟩)
  let s := Finset.univ.filter fun i => u i < 0
  have hsn : s.Nonempty := ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩⟩
  obtain ⟨i, hi, hmin⟩ := s.exists_min_image (fun i => w i / (-u i)) hsn
  have hui : u i < 0 := (Finset.mem_filter.mp hi).2
  let t := w i / (-u i)
  have ht : 0 < t := div_pos (hw i) (neg_pos.mpr hui)
  refine ⟨t, ht, fun k => ?_, i, ?_⟩
  · by_cases hk : u k < 0
    · have htk : t ≤ w k / (-u k) :=
        hmin k (Finset.mem_filter.mpr ⟨Finset.mem_univ k, hk⟩)
      have hh := (le_div_iff₀ (neg_pos.mpr hk)).mp htk
      nlinarith
    · exact add_nonneg (hw k).le (mul_nonneg ht.le (not_lt.mp hk))
  · dsimp only [t]
    field_simp [hui.ne]
    <;> ring


/-- Remove genuine zero weights and reindex the surviving ORIGINAL densities into
an actual strict-positive SpeciesFamily. Every finite weighted statistic is retained. -/
private theorem positiveSupport_family {d : ℕ} {ι : Type*} [Fintype ι]
    (ρ : ι → AbsoluteDensity d) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hsum : ∑ i, w i = 1) :
    ∃ (G : SpeciesFamily d) (σ : Fin G.count → ι), Function.Injective σ ∧
      (G.count : ℕ) = (Finset.univ.filter fun i => 0 < w i).card ∧
      (∀ j, G.density j = ρ (σ j)) ∧
      ∀ L : AbsoluteDensity d → ℝ,
        ∑ j, G.weight j * L (G.density j) = ∑ i, w i * L (ρ i) := by
  classical
  let s := Finset.univ.filter fun i => 0 < w i
  have hs : s.Nonempty := by
    by_contra hn
    have hz : ∀ i, w i = 0 := by
      intro i
      have hp : ¬0 < w i := fun hi =>
        hn ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
      exact le_antisymm (not_lt.mp hp) (hw i)
    simp only [hz, Finset.sum_const_zero] at hsum
    norm_num at hsum
  letI : Nonempty s := ⟨⟨hs.choose, hs.choose_spec⟩⟩
  have hcard : 0 < Fintype.card s := Fintype.card_pos_iff.mpr inferInstance
  let e : Fin (Fintype.card s) ≃ s := (Fintype.equivFin s).symm
  let σ : Fin (Fintype.card s) → ι := fun j => (e j).val
  have hstat : ∀ f : ι → ℝ, ∑ j, w (σ j) * f (σ j) = ∑ i, w i * f i := by
    intro f
    calc
      _ = ∑ i : s, w i.val * f i.val := e.sum_comp (fun i : s => w i.val * f i.val)
      _ = ∑ i ∈ s, w i * f i := Finset.sum_coe_sort s (fun i => w i * f i)
      _ = _ := Finset.sum_subset (Finset.subset_univ s) fun i _ hi => by
        have hp : ¬0 < w i := fun h =>
          hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, h⟩)
        rw [le_antisymm (not_lt.mp hp) (hw i), zero_mul]
  let G : SpeciesFamily d :=
    { count := ⟨Fintype.card s, hcard⟩
      weight := fun j => w (σ j)
      weight_pos := fun j => (Finset.mem_filter.mp (e j).property).2
      weight_sum := by
        change (∑ j : Fin (Fintype.card s), w (σ j)) = 1
        have hh := hstat (fun _ => 1)
        simpa only [mul_one, hsum] using hh
      density := fun j => ρ (σ j) }
  refine ⟨G, σ, ?_, ?_, fun _ => rfl, fun L => hstat (fun i => L (ρ i))⟩
  · intro i j hij
    exact e.injective (Subtype.ext hij)
  · exact Fintype.card_coe s

private theorem momentC_barycenter (h : ℝ) (F : SpeciesFamily 1) :
    momC h (densityMeasure (barycenter F)) =
      ∑ i, F.weight i * momC h (densityMeasure (F.density i)) :=
  Structural.budget_integral_barycenter F (featureC_continuous h)

private theorem momentS_barycenter (h : ℝ) (F : SpeciesFamily 1) :
    momS h (densityMeasure (barycenter F)) =
      ∑ i, F.weight i * momS h (densityMeasure (F.density i)) :=
  Structural.budget_integral_barycenter F (featureS_continuous h)

private theorem momentB_barycenter (h : ℝ) (F : SpeciesFamily 1) :
    momB h (densityMeasure (barycenter F)) =
      ∑ i, F.weight i * momB h (densityMeasure (F.density i)) :=
  Structural.budget_integral_barycenter F (featureB_continuous h)

private theorem kernelMean_eq_of_moments (h : ℝ) (ρ τ : AbsoluteDensity 1)
    (hC : momC h (densityMeasure ρ) = momC h (densityMeasure τ))
    (hS : momS h (densityMeasure ρ) = momS h (densityMeasure τ))
    (hB : momB h (densityMeasure ρ) = momB h (densityMeasure τ)) :
    elementaryKernelMean h (densityMeasure ρ) = elementaryKernelMean h (densityMeasure τ) := by
  funext x
  unfold elementaryKernelMean
  rw [hC, hS, hB]

private noncomputable def fixedForceD (h ε : ℝ) (τ ρ : AbsoluteDensity 1) : ℝ :=
  (ordinaryFisher h ρ).toReal +
    2 * ε * (∫ x, ρ.density x * elementaryAK h (densityMeasure τ) x ∂haar 1) +
    ε ^ 2 * (∫ x, ρ.density x * (elementaryKprime h (densityMeasure τ) x) ^ 2 ∂haar 1)

private theorem fixedForceD_nonneg (h ε : ℝ) (b : AbsoluteDrift (modelData h ε))
    (τ ρ : AbsoluteDensity 1) : 0 ≤ fixedForceD h ε τ ρ :=
  (elementaryModel_oneSpecies_dissipation h ε b ρ τ).2

/-- Finite actual dissipation is a linear functional of the species weights when
those three moments, and hence the actual force, are held fixed. -/
private theorem dissipation_fixed_moments (h ε : ℝ) (b : AbsoluteDrift (modelData h ε))
    (F : SpeciesFamily 1) (τ : AbsoluteDensity 1)
    (hC : momC h (densityMeasure (barycenter F)) = momC h (densityMeasure τ))
    (hS : momS h (densityMeasure (barycenter F)) = momS h (densityMeasure τ))
    (hB : momB h (densityMeasure (barycenter F)) = momB h (densityMeasure τ)) :
    speciesDissipation (modelData h ε) b F =
      ENNReal.ofReal (∑ i, F.weight i * fixedForceD h ε τ (F.density i)) := by
  have hmean := kernelMean_eq_of_moments h (barycenter F) τ hC hS hB
  have hval (i : Fin F.count) : fixedForceD h ε (barycenter F) (F.density i) =
      fixedForceD h ε τ (F.density i) := by
    unfold fixedForceD elementaryAK elementaryKprime
    rw [hmean]
  calc
    _ = ∑ i, ENNReal.ofReal (F.weight i) *
        ENNReal.ofReal (fixedForceD h ε τ (F.density i)) := by
      unfold speciesDissipation
      refine Finset.sum_congr rfl fun i _ => ?_
      congr 1
      change (∫⁻ x, ENNReal.ofReal (‖(2 : ℝ) •
        weakGradient (F.density i).sqrt (F.density i).sqrt_mem x +
          (F.density i).sqrt x • b.force (barycenter F) x‖ ^ 2) ∂haar 1) = _
      rw [(elementaryModel_oneSpecies_dissipation h ε b (F.density i) (barycenter F)).1]
      exact congrArg ENNReal.ofReal (hval i)
    _ = _ := by
      rw [ENNReal.ofReal_sum_of_nonneg fun i _ =>
        mul_nonneg (F.weight_nonneg i) (fixedForceD_nonneg h ε b τ (F.density i))]
      exact Finset.sum_congr rfl fun i _ => (ENNReal.ofReal_mul (F.weight_nonneg i)).symm

private theorem gap_fixed_moments {h ε : ℝ} (hh : 0 < h) (hε : 0 < ε)
    (hεmax : ε < epsMax h) (F : SpeciesFamily 1) (τ : AbsoluteDensity 1)
    (hC : momC h (densityMeasure (barycenter F)) = momC h (densityMeasure τ))
    (hS : momS h (densityMeasure (barycenter F)) = momS h (densityMeasure τ))
    (hB : momB h (densityMeasure (barycenter F)) = momB h (densityMeasure τ)) :
    (speciesGap (modelData h ε) F : ℝ) = ∑ i, F.weight i *
      ((ordinaryEntropy h (F.density i)).toReal + ε / 2 * elementaryQ h (densityMeasure τ)) := by
  have hQ : elementaryQ h (densityMeasure (barycenter F)) = elementaryQ h (densityMeasure τ) := by
    rw [elementaryQ_moments, elementaryQ_moments, hC, hS, hB]
  rw [elementaryModel_speciesGap_expansion hh hε hεmax F, hQ]
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, F.weight_sum, one_mul]

private theorem speciesQuotient_eq_ofReal {d : ℕ} (A : InteractionData d)
    (b : AbsoluteDrift A) (F : SpeciesFamily d) (hG : 0 < speciesGap A F)
    (hD : speciesDissipation A b F ≠ ⊤) :
    speciesQuotient A b F = ENNReal.ofReal
      ((speciesDissipation A b F).toReal / (2 * (speciesGap A F : ℝ))) := by
  have hGr : (0 : ℝ) < (speciesGap A F : ℝ) := hG
  unfold speciesQuotient
  rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_mul (by norm_num),
    ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_toReal hD]
  simp

private theorem weight_elimination {ι : Type*} [Fintype ι]
    (a : ι → Fin 3 → ℝ) (w g d : ι → ℝ)
    (hw : ∀ i, 0 < w i) (hmass : ∑ i, w i = 1)
    (hd : ∀ i, 0 ≤ d i) (hcard : 4 < Fintype.card ι)
    (hgap : 0 < ∑ i, w i * g i) :
    ∃ w' : ι → ℝ, (∀ i, 0 ≤ w' i) ∧ (∑ i, w' i = 1) ∧
      (∀ j, ∑ i, w' i * a i j = ∑ i, w i * a i j) ∧
      (0 < ∑ i, w' i * g i) ∧
      (∑ i, w' i * d i) / (2 * ∑ i, w' i * g i) ≤
        (∑ i, w i * d i) / (2 * ∑ i, w i * g i) ∧
      ∃ i, w' i = 0 := by
  classical
  let G := ∑ i, w i * g i
  let D := ∑ i, w i * d i
  let q := D / (2 * G)
  let c : ι → ℝ := fun i => d i - 2 * q * g i
  have hD0 : 0 ≤ D := Finset.sum_nonneg fun i _ => mul_nonneg (hw i).le (hd i)
  have hG0 : 0 < G := hgap
  have hq : 0 ≤ q := div_nonneg hD0 (by positivity)
  have hcost : ∑ i, w i * c i = 0 := by
    have he : ∑ i, w i * c i = D - 2 * q * G := by
      dsimp only [c, D, G]
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [he]
    dsimp only [q]
    field_simp [hG0.ne']
    <;> ring
  obtain ⟨v, hvm, hva, hv⟩ := threeMoment_null_direction a hcard
  obtain ⟨u, hum, hua, hu, hdir⟩ := orient_direction a g c v hvm hva hv
  obtain ⟨t, ht, hwn, i0, hi0⟩ := weight_boundary w u hw hum hu
  let w' : ι → ℝ := fun i => w i + t * u i
  have hlin (f : ι → ℝ) : ∑ i, w' i * f i =
      (∑ i, w i * f i) + t * (∑ i, u i * f i) := by
    dsimp only [w']
    simp_rw [add_mul, mul_assoc]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hmass' : ∑ i, w' i = 1 := by
    dsimp only [w']
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hum, hmass, mul_zero, add_zero]
  have hmom : ∀ j, ∑ i, w' i * a i j = ∑ i, w i * a i j := by
    intro j
    rw [hlin, hua j, mul_zero, add_zero]
  have hD' : 0 ≤ ∑ i, w' i * d i :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hwn i) (hd i)
  have heCost : (∑ i, w' i * c i) =
      (∑ i, w' i * d i) - 2 * q * (∑ i, w' i * g i) := by
    dsimp only [c]
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hpair : 0 < (∑ i, w' i * g i) ∧ (∑ i, w' i * c i) ≤ 0 := by
    rcases hdir with hneg | ⟨hz, hgs⟩
    · have hcs : (∑ i, w' i * c i) < 0 := by
        rw [hlin, hcost, zero_add]
        exact mul_neg_of_pos_of_neg ht hneg
      refine ⟨?_, hcs.le⟩
      by_contra hn
      have hprod := mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hq)
        (not_lt.mp hn)
      rw [heCost] at hcs
      linarith
    · refine ⟨?_, ?_⟩
      · rw [hlin]
        exact add_pos_of_pos_of_nonneg hgap (mul_nonneg ht.le hgs)
      · rw [hlin, hcost, hz, mul_zero, add_zero]
  refine ⟨w', hwn, hmass', hmom, hpair.1, ?_, i0, hi0⟩
  apply (div_le_iff₀ (mul_pos two_pos hpair.1)).mpr
  change (∑ i, w' i * d i) ≤ q * (2 * ∑ i, w' i * g i)
  rw [heCost] at hpair
  linarith [hpair.2]

private theorem actual_one_weight_elimination {h ε : ℝ}
    (hh : 0 < h) (hε : 0 < ε) (hεmax : ε < epsMax h)
    (b : AbsoluteDrift (modelData h ε)) (F : SpeciesFamily 1)
    (hpos : 0 < speciesGap (modelData h ε) F) (hcount : 4 < (F.count : ℕ)) :
    ∃ G : SpeciesFamily 1, (G.count : ℕ) < (F.count : ℕ) ∧
      0 < speciesGap (modelData h ε) G ∧
      speciesQuotient (modelData h ε) b G ≤ speciesQuotient (modelData h ε) b F ∧
      ∃ σ : Fin G.count → Fin F.count, Function.Injective σ ∧
        (∀ i, G.density i = F.density (σ i)) ∧
        momC h (densityMeasure (barycenter G)) = momC h (densityMeasure (barycenter F)) ∧
        momS h (densityMeasure (barycenter G)) = momS h (densityMeasure (barycenter F)) ∧
        momB h (densityMeasure (barycenter G)) = momB h (densityMeasure (barycenter F)) := by
  classical
  let τ := barycenter F
  let a : Fin F.count → Fin 3 → ℝ := fun i j =>
    if j.val = 0 then momC h (densityMeasure (F.density i))
    else if j.val = 1 then momS h (densityMeasure (F.density i))
    else momB h (densityMeasure (F.density i))
  let gρ : AbsoluteDensity 1 → ℝ := fun ρ =>
    (ordinaryEntropy h ρ).toReal + ε / 2 * elementaryQ h (densityMeasure τ)
  let dρ : AbsoluteDensity 1 → ℝ := fixedForceD h ε τ
  let g : Fin F.count → ℝ := fun i => gρ (F.density i)
  let d : Fin F.count → ℝ := fun i => dρ (F.density i)
  have hd : ∀ i, 0 ≤ d i := fun i => fixedForceD_nonneg h ε b τ (F.density i)
  have hG : (speciesGap (modelData h ε) F : ℝ) = ∑ i, F.weight i * g i :=
    gap_fixed_moments hh hε hεmax F τ rfl rfl rfl
  have hD : speciesDissipation (modelData h ε) b F =
      ENNReal.ofReal (∑ i, F.weight i * d i) :=
    dissipation_fixed_moments h ε b F τ rfl rfl rfl
  have hDr : (speciesDissipation (modelData h ε) b F).toReal = ∑ i, F.weight i * d i := by
    rw [hD, ENNReal.toReal_ofReal (Finset.sum_nonneg fun i _ => mul_nonneg (F.weight_nonneg i) (hd i))]
  have hGs : 0 < ∑ i, F.weight i * g i := by rw [← hG]; exact hpos
  obtain ⟨w, hw, hmass, hmom, hGp, hquot, i0, hi0⟩ :=
    weight_elimination a F.weight g d F.weight_pos F.weight_sum hd
      (by simpa only [Fintype.card_fin] using hcount) hGs
  obtain ⟨G, σ, hσ, hGcount, hρ, hstat⟩ := positiveSupport_family F.density w hw hmass
  have hC : momC h (densityMeasure (barycenter G)) = momC h (densityMeasure τ) := by
    change momC h (densityMeasure (barycenter G)) = momC h (densityMeasure (barycenter F))
    rw [momentC_barycenter, hstat (fun ρ => momC h (densityMeasure ρ)), momentC_barycenter]
    simpa [a] using hmom (0 : Fin 3)
  have hS : momS h (densityMeasure (barycenter G)) = momS h (densityMeasure τ) := by
    change momS h (densityMeasure (barycenter G)) = momS h (densityMeasure (barycenter F))
    rw [momentS_barycenter, hstat (fun ρ => momS h (densityMeasure ρ)), momentS_barycenter]
    simpa [a] using hmom (1 : Fin 3)
  have hB : momB h (densityMeasure (barycenter G)) = momB h (densityMeasure τ) := by
    change momB h (densityMeasure (barycenter G)) = momB h (densityMeasure (barycenter F))
    rw [momentB_barycenter, hstat (fun ρ => momB h (densityMeasure ρ)), momentB_barycenter]
    simpa [a] using hmom (2 : Fin 3)
  have hG' : (speciesGap (modelData h ε) G : ℝ) = ∑ i, w i * g i := by
    calc
      _ = ∑ j, G.weight j * gρ (G.density j) := gap_fixed_moments hh hε hεmax G τ hC hS hB
      _ = _ := hstat gρ
  have hD' : speciesDissipation (modelData h ε) b G =
      ENNReal.ofReal (∑ i, w i * d i) := by
    calc
      _ = ENNReal.ofReal (∑ j, G.weight j * dρ (G.density j)) :=
        dissipation_fixed_moments h ε b G τ hC hS hB
      _ = _ := congrArg ENNReal.ofReal (hstat dρ)
  have hDr' : (speciesDissipation (modelData h ε) b G).toReal = ∑ i, w i * d i := by
    rw [hD', ENNReal.toReal_ofReal (Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (hd i))]
  have hGpos : 0 < speciesGap (modelData h ε) G := by
    change 0 < (speciesGap (modelData h ε) G : ℝ)
    rw [hG']
    exact hGp
  have hQ : speciesQuotient (modelData h ε) b G ≤ speciesQuotient (modelData h ε) b F := by
    have hDf : speciesDissipation (modelData h ε) b F ≠ ⊤ := by rw [hD]; exact ENNReal.ofReal_ne_top
    have hDg : speciesDissipation (modelData h ε) b G ≠ ⊤ := by rw [hD']; exact ENNReal.ofReal_ne_top
    rw [speciesQuotient_eq_ofReal _ _ G hGpos hDg, speciesQuotient_eq_ofReal _ _ F hpos hDf]
    apply ENNReal.ofReal_le_ofReal
    rw [hDr', hDr, hG', hG]
    exact hquot
  have hlt : (G.count : ℕ) < (F.count : ℕ) := by
    rw [hGcount]
    let s := Finset.univ.filter fun i => 0 < w i
    change s.card < (F.count : ℕ)
    have hn : i0 ∉ s := by simp only [s, Finset.mem_filter, Finset.mem_univ, true_and, hi0, lt_self_iff_false, not_false_eq_true]
    have hne : s ≠ Finset.univ := by
      intro hs
      apply hn
      rw [hs]
      exact Finset.mem_univ _
    have hslt : s ⊂ Finset.univ := Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ s, hne⟩
    have hc := Finset.card_lt_card hslt
    simpa only [Finset.card_univ, Fintype.card_fin] using hc
  exact ⟨G, hlt, hGpos, hQ, σ, hσ, hρ, hC, hS, hB⟩

/-- At most four ORIGINAL species suffice for the actual quotient. The original
and reduced dissipations are proved finite; no optimizer, attainment theorem or
uniform weight lower bound is assumed. -/
theorem finiteFeature_family_support_reduce_four {h ε : ℝ}
    (hh : 0 < h) (hε : 0 < ε) (hεmax : ε < epsMax h)
    (b : AbsoluteDrift (modelData h ε)) (F : SpeciesFamily 1)
    (hpos : 0 < speciesGap (modelData h ε) F) :
    ∃ G : SpeciesFamily 1, (G.count : ℕ) ≤ 4 ∧
      0 < speciesGap (modelData h ε) G ∧
      speciesQuotient (modelData h ε) b G ≤ speciesQuotient (modelData h ε) b F ∧
      ∃ σ : Fin G.count → Fin F.count, Function.Injective σ ∧
        (∀ i, G.density i = F.density (σ i)) ∧
        momC h (densityMeasure (barycenter G)) = momC h (densityMeasure (barycenter F)) ∧
        momS h (densityMeasure (barycenter G)) = momS h (densityMeasure (barycenter F)) ∧
        momB h (densityMeasure (barycenter G)) = momB h (densityMeasure (barycenter F)) := by
  classical
  have main : ∀ n : ℕ, ∀ F : SpeciesFamily 1, (F.count : ℕ) = n →
      0 < speciesGap (modelData h ε) F →
      ∃ G : SpeciesFamily 1, (G.count : ℕ) ≤ 4 ∧
        0 < speciesGap (modelData h ε) G ∧
        speciesQuotient (modelData h ε) b G ≤ speciesQuotient (modelData h ε) b F ∧
        ∃ σ : Fin G.count → Fin F.count, Function.Injective σ ∧
          (∀ i, G.density i = F.density (σ i)) ∧
          momC h (densityMeasure (barycenter G)) = momC h (densityMeasure (barycenter F)) ∧
          momS h (densityMeasure (barycenter G)) = momS h (densityMeasure (barycenter F)) ∧
          momB h (densityMeasure (barycenter G)) = momB h (densityMeasure (barycenter F)) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro F hn hpos
      by_cases hc : (F.count : ℕ) ≤ 4
      · exact ⟨F, hc, hpos, le_rfl, id, Function.injective_id, fun _ => rfl, rfl, rfl, rfl⟩
      · obtain ⟨G, hGc, hGpos, hGq, σ, hσ, hρ, hC, hS, hB⟩ :=
          actual_one_weight_elimination hh hε hεmax b F hpos (lt_of_not_ge hc)
        obtain ⟨H, hHc, hHpos, hHq, τ, hτ, hρ', hC', hS', hB'⟩ :=
          ih G.count (by omega) G rfl hGpos
        refine ⟨H, hHc, hHpos, hHq.trans hGq, σ ∘ τ, hσ.comp hτ, ?_,
          hC'.trans hC, hS'.trans hS, hB'.trans hB⟩
        intro i
        exact (hρ' i).trans (hρ (τ i))
  exact main F.count F rfl hpos

end DGPS.Examples.ThreeSpeciesCircle
