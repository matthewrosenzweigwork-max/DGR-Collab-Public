import SharpSymmetricLSI.Paper.ProductDissipation
import SharpSymmetricLSI.Paper.EntFinite
import SharpSymmetricLSI.Defs.D15_Forces

/-!
# (5.11), (5.12): the particle force (Phase 3, lane D; R20)

The minimizer `μ` has a density `ρ` (finite free energy), so `W*μ = W*ρ` has the bounded weak
gradient `β = ∫ ∇₁W(·,y) ρ(y) dy`. The centered kernel `K` then has first-variable gradient
`∇₁W(x,y) - β(x)` a.e., `½∇[K(x,x)] = -β`, and weak differentiation of the sum
`U_N = (2N)⁻¹ ∑ᵢⱼ K(xᵢ,xⱼ)` gives (5.12).
-/

noncomputable section
open MeasureTheory InformationTheory Filter
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-- A minimizer is absolutely continuous with respect to Haar measure. -/
theorem minimizer_ac (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)}
    (hμ : IsMinimizer V W μ) : (μ : Measure (Torus d)) ≪ haar d := by
  have hle : freeEnergy V W μ ≤ freeEnergy V W (haar d) := by
    unfold IsMinimizer at hμ
    rw [hμ]
    exact iInf_le (fun ρ : ProbabilityMeasure (Torus d) => freeEnergy V W ρ)
      ⟨haar d, inferInstance⟩
  have hF : freeEnergy V W μ ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ hle
    unfold freeEnergy
    simp only [klDiv_self, EReal.coe_ennreal_zero,
      zero_add]
    exact EReal.coe_ne_top _
  have hK : klDiv (μ : Measure (Torus d)) (haar d) ≠ ⊤ := by
    intro h
    apply hF
    unfold freeEnergy
    rw [h]
    simp
  exact (klDiv_ne_top_iff.mp hK).1

/-- The density of `μ`. -/
def densOf (μ : Measure (Torus d)) : Torus d → ℝ := fun x => (μ.rnDeriv (haar d) x).toReal

theorem measurable_densOf (μ : Measure (Torus d)) : Measurable (densOf μ) :=
  (Measure.measurable_rnDeriv _ _).ennreal_toReal

theorem integrable_densOf (μ : Measure (Torus d)) [IsFiniteMeasure μ] :
    Integrable (densOf μ) (haar d) :=
  Measure.integrable_toReal_rnDeriv

theorem integral_densOf_mul {μ : Measure (Torus d)} [IsFiniteMeasure μ] (hac : μ ≪ haar d) (f : Torus d → ℝ) :
    ∫ y, f y * densOf μ y ∂haar d = ∫ y, f y ∂μ := by
  rw [← integral_rnDeriv_smul hac]
  congr 1; funext y; simp only [densOf, smul_eq_mul]; ring

theorem integral_densOf_eq_one {μ : Measure (Torus d)} [IsProbabilityMeasure μ]
    (hac : μ ≪ haar d) : ∫ y, densOf μ y ∂haar d = 1 := by
  have := integral_densOf_mul hac (fun _ => 1)
  simpa using this

theorem convMeas_eq_convDens {μ : Measure (Torus d)} [IsFiniteMeasure μ] (hac : μ ≪ haar d) :
    convMeas W μ = convDens W (densOf μ) := by
  funext x; unfold convMeas convDens; rw [integral_densOf_mul hac]

/-- `β = ∇(W*μ)`, componentwise bounded and measurable. -/
theorem forceMean_props (hyp : Hyp V W KV KW) {μ : Measure (Torus d)} [IsProbabilityMeasure μ]
    (hac : μ ≪ haar d) :
    IsWeakGrad (convMeas W μ) (bForceL W (densOf μ)) ∧
    (∀ k, Measurable fun x => bForceL W (densOf μ) x k) ∧
    (∃ C, ∀ x k, |bForceL W (densOf μ) x k| ≤ C) ∧
    (∀ x k, bForceL W (densOf μ) x k = ∫ y, bGrad W x y k ∂μ) := by
  have hρm := measurable_densOf μ
  have hρi := integrable_densOf μ
  obtain ⟨Cb, hCb⟩ := bGrad_bdd hyp (W := W)
  refine ⟨?_, fun k => ?_, ⟨Cb, fun x k => ?_⟩, fun x k => integral_densOf_mul hac _⟩
  · rw [convMeas_eq_convDens hac]; exact isWeakGrad_convDens hyp hρm hρi
  · exact (((measurable_bGrad hyp (W := W) k).mul (hρm.comp measurable_snd)).stronglyMeasurable.integral_prod_right
      (ν := haar d) (f := fun x y => bGrad W x y k * densOf μ y)).measurable
  · rw [show bForceL W (densOf μ) x k = ∫ y, bGrad W x y k ∂μ from integral_densOf_mul hac _]
    refine (abs_integral_le_integral_abs).trans ?_
    calc ∫ y, |bGrad W x y k| ∂μ ≤ ∫ _, Cb ∂μ := integral_mono_of_nonneg
          (Eventually.of_forall fun _ => abs_nonneg _) (integrable_const Cb)
          (Eventually.of_forall fun y => hCb x y k)
      _ = Cb := by simp

/-- `w = W*μ` is bounded and integrable. -/
theorem convMeas_bdd (hyp : Hyp V W KV KW) (μ : Measure (Torus d)) [IsProbabilityMeasure μ] :
    ∃ B, ∀ x, |convMeas W μ x| ≤ B := by
  obtain ⟨BW, hBW⟩ := exists_bound_of_continuous (X := Torus d × Torus d) hyp.continuous_W
  refine ⟨BW, fun x => (abs_integral_le_integral_abs).trans ?_⟩
  calc ∫ y, |W x y| ∂μ ≤ ∫ _, BW ∂μ := integral_mono_of_nonneg
        (Eventually.of_forall fun _ => abs_nonneg _) (integrable_const BW)
        (Eventually.of_forall fun y => hBW (x, y))
    _ = BW := by simp

/-- `½ K(z,z) = -w(z) + W(μ,μ)/2` has weak gradient `-β`. -/
theorem isWeakGrad_diagK (hyp : Hyp V W KV KW) {μ : Measure (Torus d)} [IsProbabilityMeasure μ]
    (hac : μ ≪ haar d) :
    IsWeakGrad (fun z => centeredKernel W μ z z / 2) (fun z k => -bForceL W (densOf μ) z k) := by
  have h := ((forceMean_props hyp hac).1.cmul (-1)).add (isWeakGrad_const (interE W μ μ / 2))
  have e1 : (fun z => centeredKernel W μ z z / 2) =
      fun y => -1 * convMeas W μ y + interE W μ μ / 2 := by
    funext z; unfold centeredKernel; rw [hyp.diag]; ring
  have e2 : (fun z (k : Fin d) => -bForceL W (densOf μ) z k) =
      fun y k => -1 * bForceL W (densOf μ) y k + (0 : Torus d → Fin d → ℝ) y k := by
    funext z k; simp
  rw [e1, e2]; exact h

/-- The centered kernel as a function on `𝕋^{2×d}`. -/
def K2 (W : Torus d → Torus d → ℝ) (μ : Measure (Torus d)) (Y : UnitAddTorus (Fin 2 × Fin d)) :
    ℝ :=
  centeredKernel W μ (projBlock 0 Y) (projBlock 1 Y)

/-- Its weak gradient: `∇W - β` placed in the two blocks. -/
def gK (W : Torus d → Torus d → ℝ) (β : Torus d → Fin d → ℝ) (Y : UnitAddTorus (Fin 2 × Fin d))
    (q : Fin 2 × Fin d) : ℝ :=
  lipGrad (W2 W) Y q - (if q.1 = 0 then β (projBlock 0 Y) q.2 else 0) -
    (if q.1 = 1 then β (projBlock 1 Y) q.2 else 0)

theorem isWeakGrad_K2 (hyp : Hyp V W KV KW) {μ : Measure (Torus d)} [IsProbabilityMeasure μ]
    (hac : μ ≪ haar d) : IsWeakGrad (K2 W μ) (gK W (bForceL W (densOf μ))) := by
  obtain ⟨hw, hβm, ⟨Cβ, hCβ⟩, -⟩ := forceMean_props hyp hac
  obtain ⟨Bw, hBw⟩ := convMeas_bdd hyp μ
  have iw : Integrable (convMeas W μ) volume := Integrable.of_bound hw.aestronglyMeasurable_fun Bw
    (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hBw x)
  have iβ : ∀ k, Integrable (fun x => bForceL W (densOf μ) x k) volume := fun k =>
    Integrable.of_bound (hβm k).aestronglyMeasurable Cβ
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hCβ x k)
  have hW2 := isWeakGrad_lipGrad (continuous_W2 hyp) (lipschitz_W2 hyp)
  have h0 := isWeakGrad_comp_projBlock (N := 2) 0 hw iw iβ
  have h1 := isWeakGrad_comp_projBlock (N := 2) 1 hw iw iβ
  have h := ((hW2.add (h0.cmul (-1))).add (h1.cmul (-1))).add (isWeakGrad_const (interE W μ μ))
  have e1 : K2 W μ = fun Y => W2 W Y + -1 * convMeas W μ (projBlock 0 Y) +
      -1 * convMeas W μ (projBlock 1 Y) + interE W μ μ := by
    funext Y; unfold K2 centeredKernel; simp only [W2, Function.comp]
    rw [show W (unflat Y 0) (unflat Y 1) = W (projBlock 0 Y) (projBlock 1 Y) from rfl]; ring
  have e2 : gK W (bForceL W (densOf μ)) = fun Y q => lipGrad (W2 W) Y q +
      -1 * (if q.1 = 0 then bForceL W (densOf μ) (projBlock 0 Y) q.2 else 0) +
      -1 * (if q.1 = 1 then bForceL W (densOf μ) (projBlock 1 Y) q.2 else 0) +
      (0 : UnitAddTorus (Fin 2 × Fin d) → Fin 2 × Fin d → ℝ) Y q := by
    funext Y q; simp only [gK, Pi.zero_apply]; ring
  rw [e1, e2]; exact h

theorem bForce_eq_weakGrad_K2 (μ : Measure (Torus d)) (x y : Torus d) (k : Fin d) :
    bForce W μ x y k = weakGrad (K2 W μ) (pairFlat (x, y)) (0, k) := rfl

theorem gK_pairFlat (β : Torus d → Fin d → ℝ) (x y : Torus d) (k : Fin d) :
    gK W β (pairFlat (x, y)) (0, k) = bGrad W x y k - β x k := by
  simp only [gK, bGrad, pairFlat, if_neg (by decide : (0 : Fin 2) ≠ 1), sub_zero]
  rfl

/-- `b(x,y) = ∇₁W(x,y) - β(x)` for `(haar ⊗ haar)`-a.e. `(x,y)`. -/
theorem bForce_ae_prod (hyp : Hyp V W KV KW) {μ : Measure (Torus d)} [IsProbabilityMeasure μ]
    (hac : μ ≪ haar d) : ∀ᵐ p ∂(haar d).prod (haar d), ∀ k,
      bForce W μ p.1 p.2 k = bGrad W p.1 p.2 k - bForceL W (densOf μ) p.1 k := by
  have hae := weakGrad_ae_eq (isWeakGrad_K2 hyp hac)
  filter_upwards [measurePreserving_pairFlat.quasiMeasurePreserving.ae hae] with p hp k
  rw [bForce_eq_weakGrad_K2, hp, ← gK_pairFlat]

/-- (5.12), centering: `∫ b(x,y) dμ(y) = 0` for `μ`-a.e. `x`. -/
theorem bForce_centered (hyp : Hyp V W KV KW) {μ : Measure (Torus d)} [IsProbabilityMeasure μ]
    (hac : μ ≪ haar d) : ∀ᵐ x ∂μ, ∀ k, ∫ y, bForce W μ x y k ∂μ = 0 := by
  have hit := Measure.ae_ae_of_ae_prod (bForce_ae_prod hyp hac)
  obtain ⟨Cb, hCb⟩ := bGrad_bdd hyp (W := W)
  filter_upwards [hac.ae_le hit] with x hx k
  have hy : ∀ᵐ y ∂μ, bForce W μ x y k = bGrad W x y k - bForceL W (densOf μ) x k :=
    Filter.Eventually.mono (hac.ae_le hx) fun y hy => hy k
  have hbi : Integrable (fun y => bGrad W x y k) μ :=
    Integrable.of_bound ((measurable_bGrad hyp (W := W) k).comp measurable_prodMk_left
      ).aestronglyMeasurable Cb (Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs]; exact hCb x y k)
  rw [integral_congr_ae hy, integral_sub hbi (integrable_const _), integral_const,
    (forceMean_props hyp hac).2.2.2 x k]
  simp

variable {N : ℕ}

/-- The `(i,j)` summand of `U_N` on the flat torus. -/
def TU (W : Torus d → Torus d → ℝ) (μ : Measure (Torus d)) (i j : Fin N)
    (Y : UnitAddTorus (Fin N × Fin d)) : ℝ :=
  if i = j then -2 * convMeas W μ (projBlock i Y) + interE W μ μ else K2 W μ (projPair i j Y)

/-- Its weak gradient. -/
def GU (W : Torus d → Torus d → ℝ) (β : Torus d → Fin d → ℝ) (i j : Fin N)
    (Y : UnitAddTorus (Fin N × Fin d)) (p : Fin N × Fin d) : ℝ :=
  if i = j then (if p.1 = i then -2 * β (projBlock i Y) p.2 + 0 else 0)
  else pairGrad i j (gK W β) Y p

theorem isWeakGrad_TU (hyp : Hyp V W KV KW) {μ : Measure (Torus d)} [IsProbabilityMeasure μ]
    (hac : μ ≪ haar d) (i j : Fin N) :
    IsWeakGrad (TU W μ i j) (GU W (bForceL W (densOf μ)) i j) := by
  obtain ⟨hw, hβm, ⟨Cβ, hCβ⟩, -⟩ := forceMean_props hyp hac
  obtain ⟨Bw, hBw⟩ := convMeas_bdd hyp μ
  have iw : Integrable (convMeas W μ) volume := Integrable.of_bound hw.aestronglyMeasurable_fun Bw
    (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hBw x)
  have iβ : ∀ k, Integrable (fun x => bForceL W (densOf μ) x k) volume := fun k =>
    Integrable.of_bound (hβm k).aestronglyMeasurable Cβ
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hCβ x k)
  unfold TU GU
  by_cases hij : i = j
  · simp only [hij, if_true]
    have h1 := (hw.cmul (-2)).add (isWeakGrad_const (interE W μ μ))
    exact isWeakGrad_comp_projBlock j h1 ((iw.const_mul _).add (integrable_const _))
      fun k => ((iβ k).const_mul _).add (integrable_const _)
  · simp only [hij, if_false]
    have hK := isWeakGrad_K2 hyp hac
    obtain ⟨BW, hBW⟩ := exists_bound_of_continuous (X := Torus d × Torus d) hyp.continuous_W
    obtain ⟨Cb, hCb⟩ : ∃ C, ∀ Y q, |lipGrad (W2 W) Y q| ≤ C :=
      ⟨_, fun Y q => abs_lipGrad_le (lipschitz_W2 hyp) Y q⟩
    have iK : Integrable (K2 W μ) volume := by
      refine Integrable.of_bound hK.aestronglyMeasurable_fun (BW + Bw + Bw + |interE W μ μ|)
        (Eventually.of_forall fun Y => ?_)
      rw [Real.norm_eq_abs]
      unfold K2 centeredKernel
      have : |W (projBlock 0 Y) (projBlock 1 Y)| ≤ BW := hBW (projBlock 0 Y, projBlock 1 Y)
      have := hBw (projBlock 0 Y); have := hBw (projBlock 1 Y)
      have := abs_sub (W (projBlock 0 Y) (projBlock 1 Y) - convMeas W μ (projBlock 0 Y))
        (convMeas W μ (projBlock 1 Y))
      have := abs_sub (W (projBlock 0 Y) (projBlock 1 Y)) (convMeas W μ (projBlock 0 Y))
      have := abs_add_le (W (projBlock 0 Y) (projBlock 1 Y) - convMeas W μ (projBlock 0 Y) -
        convMeas W μ (projBlock 1 Y)) (interE W μ μ)
      linarith
    have igK : ∀ q, Integrable (fun Y => gK W (bForceL W (densOf μ)) Y q) volume := fun q => by
      refine Integrable.of_bound (hK.aestronglyMeasurable_grad q) (Cb + |Cβ| + |Cβ|)
        (Eventually.of_forall fun Y => ?_)
      rw [Real.norm_eq_abs]
      unfold gK
      have h1 := hCb Y q
      have h2 : |(if q.1 = 0 then bForceL W (densOf μ) (projBlock 0 Y) q.2 else 0)| ≤ |Cβ| := by
        split_ifs
        · exact (hCβ _ _).trans (le_abs_self _)
        · simp
      have h3 : |(if q.1 = 1 then bForceL W (densOf μ) (projBlock 1 Y) q.2 else 0)| ≤ |Cβ| := by
        split_ifs
        · exact (hCβ _ _).trans (le_abs_self _)
        · simp
      refine (abs_sub _ _).trans ?_
      linarith [abs_sub (lipGrad (W2 W) Y q)
        (if q.1 = 0 then bForceL W (densOf μ) (projBlock 0 Y) q.2 else 0)]
    exact isWeakGrad_comp_projPair hij hK iK igK

theorem Ucentered_unflat (hyp : Hyp V W KV KW) (μ : Measure (Torus d)) :
    Ucentered W μ N ∘ unflat = fun Y => 1 / (2 * (N : ℝ)) * ∑ i, ∑ j, TU W μ i j Y := by
  funext Y
  simp only [Function.comp, Ucentered, TU]
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs with h
  · subst h
    show centeredKernel W μ (projBlock i Y) (projBlock i Y) = _
    unfold centeredKernel; rw [hyp.diag]; ring
  · unfold K2
    congr 1

/-- The weak gradient of `U_N ∘ unflat`. -/
def GUsum (W : Torus d → Torus d → ℝ) (β : Torus d → Fin d → ℝ) (N : ℕ)
    (Y : UnitAddTorus (Fin N × Fin d)) (p : Fin N × Fin d) : ℝ :=
  1 / (2 * (N : ℝ)) * ∑ i, ∑ j, GU W β i j Y p

theorem isWeakGrad_Ucentered (hyp : Hyp V W KV KW) {μ : Measure (Torus d)}
    [IsProbabilityMeasure μ] (hac : μ ≪ haar d) :
    IsWeakGrad (Ucentered W μ N ∘ unflat) (GUsum W (bForceL W (densOf μ)) N) := by
  rw [Ucentered_unflat hyp]
  exact (isWeakGrad_finsetSum Finset.univ fun i _ =>
    isWeakGrad_finsetSum Finset.univ fun j _ => isWeakGrad_TU hyp hac i j).cmul _

theorem GUsum_flat (hyp : Hyp V W KV KW) (hN : 1 ≤ N) (β : Torus d → Fin d → ℝ)
    (X : Config N d) (i0 : Fin N) (k : Fin d) :
    GUsum W β N (flat X) (i0, k) = (N : ℝ)⁻¹ *
      ((∑ l ∈ Finset.univ.erase i0, (bGrad W (X i0) (X l) k - β (X i0) k)) + -β (X i0) k) := by
  set A : Fin N → ℝ := fun l => bGrad W (X i0) (X l) k - β (X i0) k with hA
  have hp : ∀ a b : Fin N, GU W β a b (flat X) (i0, k) =
      (if a = b then (if i0 = a then -2 * β (X i0) k else 0) else 0) +
      (if a = b then 0 else if i0 = a then A b else 0) +
      (if a = b then 0 else if i0 = b then A a else 0) := by
    intro a b
    unfold GU
    by_cases hab : a = b
    · subst hab
      by_cases h : i0 = a
      · subst h; simp [projBlock_flat]
      · simp [h]
    · simp only [hab, if_false, pairGrad, zero_add]
      by_cases hia : i0 = a
      · subst hia
        have hib : ¬ i0 = b := hab
        simp only [if_true, hib, if_false, add_zero, hA, gK, projPair_flat]
        simp [bGrad, projBlock_flat]
      · by_cases hib : i0 = b
        · subst hib
          simp only [hia, if_false, if_true, zero_add, hA, gK]
          rw [projPair_swap, show ((1 : Fin 2), k) = (Fin.rev 0, k) from rfl,
            lipGrad_W2_swap hyp, projPair_flat]
          simp [bGrad]
          rfl
        · simp [hia, hib]
  unfold GUsum
  simp_rw [hp, Finset.sum_add_distrib]
  have e0 : ∑ a : Fin N, ∑ b : Fin N,
      (if a = b then (if i0 = a then -2 * β (X i0) k else 0) else 0) = -2 * β (X i0) k := by
    rw [Finset.sum_eq_single i0]
    · rw [Finset.sum_eq_single i0] <;> simp_all [eq_comm]
    · intro a _ hai
      refine Finset.sum_eq_zero fun b _ => ?_
      simp [Ne.symm hai]
    · simp
  have e1 : ∑ a : Fin N, ∑ b : Fin N, (if a = b then 0 else if i0 = a then A b else 0) =
      ∑ j ∈ Finset.univ.erase i0, A j := by
    rw [Finset.sum_eq_single i0]
    · rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i0)]
      simp only [↓reduceIte, add_zero]
      refine Finset.sum_congr rfl fun j hj => ?_
      have : ¬ i0 = j := fun h => (Finset.mem_erase.mp hj).1 h.symm
      simp [this]
    · intro a _ hai
      refine Finset.sum_eq_zero fun b _ => ?_
      simp [Ne.symm hai]
    · simp
  have e2 : ∑ a : Fin N, ∑ b : Fin N, (if a = b then 0 else if i0 = b then A a else 0) =
      ∑ j ∈ Finset.univ.erase i0, A j := by
    rw [Finset.sum_comm]
    rw [Finset.sum_eq_single i0]
    · rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i0)]
      simp only [↓reduceIte, add_zero]
      refine Finset.sum_congr rfl fun j hj => ?_
      have : ¬ j = i0 := (Finset.mem_erase.mp hj).1
      simp [this]
    · intro b _ hbi
      refine Finset.sum_eq_zero fun a _ => ?_
      simp [Ne.symm hbi]
    · simp
  rw [e0, e1, e2]
  have hN0 : (N : ℝ) ≠ 0 := by
    have : (0 : ℝ) < N := by exact_mod_cast hN
    exact this.ne'
  field_simp
  ring

/-- **(5.11), (5.12).** -/
theorem particle_force_aux (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)}
    (hμ : IsMinimizer V W μ) :
    (∀ᵐ x ∂haar d, ∀ k, bDiag W μ x k = -weakGrad (convMeas W μ) x k) ∧
    (∀ᵐ x ∂(μ : Measure (Torus d)), ∀ k, ∫ y, bForce W μ x y k ∂(μ : Measure (Torus d)) = 0) ∧
    ∀ N : ℕ, 1 ≤ N → ∀ᵐ X ∂(volume : Measure (Config N d)), ∀ i k,
      weakGradC (Ucentered W μ N) X i k =
        (N : ℝ)⁻¹ * ((∑ l, if l ≠ i then bForce W μ (X i) (X l) k else 0) + bDiag W μ (X i) k) := by
  have hac := minimizer_ac hyp hμ
  set β := bForceL W (densOf (μ : Measure (Torus d))) with hβ
  have hw := (forceMean_props hyp hac).1
  have h1 := weakGrad_ae_eq (isWeakGrad_diagK hyp hac)
  have h2 := weakGrad_ae_eq hw
  have hdiag : ∀ᵐ x ∂haar d, ∀ k, bDiag W μ x k = -β x k := by
    filter_upwards [h1] with x hx k
    simp only [bDiag]; rw [congrFun hx k]
  refine ⟨?_, bForce_centered hyp hac, fun N hN => ?_⟩
  · filter_upwards [hdiag, h2] with x hx hx2 k
    rw [hx k, congrFun hx2 k]
  have hflat : MeasurePreserving (flat : Config N d → UnitAddTorus (Fin N × Fin d)) volume volume :=
    ⟨measurable_flat, map_flat_volume N⟩
  have hU := hflat.quasiMeasurePreserving.ae (weakGrad_ae_eq (isWeakGrad_Ucentered hyp hac
    (N := N)))
  have hK := weakGrad_ae_eq (isWeakGrad_K2 hyp hac)
  have hb : ∀ᵐ X ∂(volume : Measure (Config N d)), ∀ i l : Fin N, i ≠ l → ∀ k,
      bForce W μ (X i) (X l) k = bGrad W (X i) (X l) k - β (X i) k := by
    refine ae_all_iff.mpr fun i => ae_all_iff.mpr fun l => ?_
    by_cases hil : i = l
    · exact Eventually.of_forall fun X h => absurd hil h
    have := (((measurePreserving_projPair (d := d) hil).comp hflat).quasiMeasurePreserving.ae hK)
    filter_upwards [this] with X hX _ k
    simp only [Function.comp, projPair_flat] at hX
    rw [bForce_eq_weakGrad_K2, show pairFlat (X i, X l) = flat ![X i, X l] from rfl, hX,
      ← gK_pairFlat]
    rfl
  have hd : ∀ᵐ X ∂(volume : Measure (Config N d)), ∀ i k, bDiag W μ (X i) k = -β (X i) k := by
    refine ae_all_iff.mpr fun i => ?_
    have := ((measurePreserving_projBlock (d := d) i).comp hflat).quasiMeasurePreserving.ae
      (show ∀ᵐ x ∂(volume : Measure (Torus d)), ∀ k, bDiag W μ x k = -β x k from hdiag)
    filter_upwards [this] with X hX
    exact hX
  filter_upwards [hU, hb, hd] with X hX hbX hdX i k
  have e0 : weakGradC (Ucentered W μ N) X i k =
      weakGrad (Ucentered W μ N ∘ unflat) (flat X) (i, k) := rfl
  rw [e0, congrFun hX (i, k), GUsum_flat hyp hN, hdX i k]
  congr 2
  rw [← Finset.sum_filter, Finset.filter_ne']
  refine Finset.sum_congr rfl fun l hl => ?_
  rw [hbX i l (Ne.symm (Finset.mem_erase.mp hl).1) k]

end SharpLSI
