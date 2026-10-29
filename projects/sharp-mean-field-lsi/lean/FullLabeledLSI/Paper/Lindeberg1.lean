import FullLabeledLSI.Defs.F06_Hybrid
import SharpSymmetricLSI.Statements.R23_Reference_Spectrum
import SharpSymmetricLSI.Paper.Occ8
import SharpSymmetricLSI.Paper.GaussForm14
import SharpSymmetricLSI.Paper.ProductEntropy

/-!
# Lemma 7.1, part 1: label-wise form of the hybrid space, interfaces, and the transfer to a
# measurable bounded representative of the reference eigenbasis

* `lf`: the factor of the polynomial read at label `l` (pair form of `hybFactor`).
* `polyB`: the polynomial (7.1) on the hybrid space with an arbitrary set `B` of labels reading the
  torus coordinate (`hybEval = polyB (retained c δ)`).
* `HybridPolyMoment`: **interface** (manuscript (7.9), lane 3): polynomial moment bounds on every
  intermediate hybrid space.
* `GoodBasis`: the reference eigenbasis replaced by a measurable, bounded representative.
* `pairMeasure`: `μ_lab^{⊗N}` on `Fin N → 𝕋^d × ℝ^J`, `μ_lab = μ ⊗ γ_J`; it is `hybMeasure` carried
  through `ofPairs`. Pair-world quantities `pP`, `zP`, `IP`.
* identification of the two integrals of S26 with `IP … univ` and `IP … (retained c δ)`.
* transfer lemmas: the S26 integrals and `HybridPolyMoment` are unchanged when `e` is replaced by an
  a.e.-equal basis; existence of a `GoodBasis` representative for a reference eigenbasis.
-/

open MeasureTheory ProbabilityTheory

namespace SharpLSI.FL

variable {d : ℕ}

/-! ### The label factor, polynomial and fluctuation in label-wise form -/

/-- The factor at label `l` of the polynomial: `e_m(x_l)` if `l ∈ B`; `1` (`m = 0`) or `y_{l,m}`
(`m ≥ 1`) otherwise. The pair-form of `hybFactor`. -/
noncomputable def lf (e : ℕ → Torus d → ℝ) {N J : ℕ} (B : Finset (Fin N)) (l : Fin N)
    (m : Fin (J + 1)) (s : Torus d × (Fin J → ℝ)) : ℝ :=
  if l ∈ B then e m s.1 else if h : (m : ℕ) = 0 then 1 else s.2 ⟨(m : ℕ) - 1, by omega⟩

theorem hybFactor_eq_lf (e : ℕ → Torus d → ℝ) {N J : ℕ} (B : Finset (Fin N)) (l : Fin N)
    (m : Fin (J + 1)) (ω : Config N d × (Fin N → Fin J → ℝ)) :
    hybFactor e B l m ω = lf e B l m (ω.1 l, ω.2 l) := rfl

theorem lf_zero (e : ℕ → Torus d → ℝ) (he0 : e 0 = fun _ => 1) {N J : ℕ} (B : Finset (Fin N))
    (l : Fin N) (s : Torus d × (Fin J → ℝ)) : lf e B l 0 s = 1 := by
  unfold lf
  by_cases h : l ∈ B
  · simp [h, he0]
  · simp [h]

theorem lf_of_mem (e : ℕ → Torus d → ℝ) {N J : ℕ} {B : Finset (Fin N)} {l : Fin N}
    (hl : l ∈ B) (m : Fin (J + 1)) (s : Torus d × (Fin J → ℝ)) : lf e B l m s = e m s.1 := by
  simp [lf, hl]

theorem lf_of_not_mem_succ (e : ℕ → Torus d → ℝ) {N J : ℕ} {B : Finset (Fin N)} {l : Fin N}
    (hl : l ∉ B) (r : Fin J) (s : Torus d × (Fin J → ℝ)) : lf e B l r.succ s = s.2 r := by
  simp [lf, hl, Fin.val_succ]

theorem lf_congr (e : ℕ → Torus d → ℝ) {N J : ℕ} {B B' : Finset (Fin N)} {l : Fin N}
    (h : l ∈ B ↔ l ∈ B') : (lf e B l : Fin (J + 1) → _) = lf e B' l := by
  funext m s
  simp only [lf, h]

/-- The polynomial (7.1) on the hybrid space with the labels `B` reading the torus coordinate. -/
noncomputable def polyB (e : ℕ → Torus d → ℝ) {N J : ℕ} (c : (Fin N → Fin (J + 1)) → ℝ)
    (B : Finset (Fin N)) (ω : Config N d × (Fin N → Fin J → ℝ)) : ℝ :=
  ∑ j, c j * ∏ i, hybFactor e B i (j i) ω

theorem hybEval_eq_polyB (e : ℕ → Torus d → ℝ) {N J : ℕ} (c : (Fin N → Fin (J + 1)) → ℝ)
    (δ : ℝ) : hybEval e c δ = polyB e c (retained c δ) := rfl

/-- The pair-world polynomial. -/
noncomputable def pP (e : ℕ → Torus d → ℝ) {N J : ℕ} (c : (Fin N → Fin (J + 1)) → ℝ)
    (B : Finset (Fin N)) (ω : Fin N → Torus d × (Fin J → ℝ)) : ℝ :=
  ∑ j, c j * ∏ l, lf e B l (j l) (ω l)

/-- The pair-world low-influence fluctuation vector (7.10). -/
noncomputable def zP (e : ℕ → Torus d → ℝ) {N J : ℕ} (c : (Fin N → Fin (J + 1)) → ℝ) (δ : ℝ)
    (B : Finset (Fin N)) (ω : Fin N → Torus d × (Fin J → ℝ)) (m : Fin J) : ℝ :=
  (Real.sqrt (lowCount c δ))⁻¹ * ∑ l ∈ (retained c δ)ᶜ, lf e B l m.succ (ω l)

/-! ### Measures -/

/-- `μ ⊗ γ_J`, the law of one label `(x_l, y_l)`. -/
noncomputable def labelMeasure (μ : Measure (Torus d)) (J : ℕ) : Measure (Torus d × (Fin J → ℝ)) :=
  μ.prod (Measure.pi fun _ : Fin J => gaussianReal 0 1)

/-- `(μ ⊗ γ_J)^{⊗N}` on `Fin N → 𝕋^d × ℝ^J`. -/
noncomputable def pairMeasure (μ : Measure (Torus d)) (N J : ℕ) :
    Measure (Fin N → Torus d × (Fin J → ℝ)) :=
  Measure.pi fun _ : Fin N => labelMeasure μ J

/-- From the label-wise form to the hybrid space `Config N d × (Fin N → Fin J → ℝ)`. -/
def ofPairs {N J : ℕ} (ω : Fin N → Torus d × (Fin J → ℝ)) :
    Config N d × (Fin N → Fin J → ℝ) := (fun l => (ω l).1, fun l => (ω l).2)

instance labelMeasure_prob (μ : Measure (Torus d)) [IsProbabilityMeasure μ] (J : ℕ) :
    IsProbabilityMeasure (labelMeasure μ J) := by
  unfold labelMeasure; infer_instance

instance pairMeasure_prob (μ : Measure (Torus d)) [IsProbabilityMeasure μ] (N J : ℕ) :
    IsProbabilityMeasure (pairMeasure μ N J) := by
  unfold pairMeasure; infer_instance

theorem measurePreserving_ofPairs (μ : Measure (Torus d)) [IsProbabilityMeasure μ] (N J : ℕ) :
    MeasurePreserving (ofPairs (d := d) (N := N) (J := J)) (pairMeasure μ N J)
      (hybMeasure μ N J) := by
  have h := measurePreserving_arrowProdEquivProdArrow (Torus d) (Fin J → ℝ) (Fin N)
    (fun _ : Fin N => μ) (fun _ : Fin N => Measure.pi fun _ : Fin J => gaussianReal 0 1)
  exact h

theorem measurable_ofPairs {N J : ℕ} : Measurable (ofPairs (d := d) (N := N) (J := J)) :=
  (MeasurableEquiv.arrowProdEquivProdArrow (Torus d) (Fin J → ℝ) (Fin N)).measurable

/-- Integrals over the hybrid space are integrals over the label-wise space. -/
theorem integral_hyb_eq (μ : Measure (Torus d)) [IsProbabilityMeasure μ] (N J : ℕ)
    (g : Config N d × (Fin N → Fin J → ℝ) → ℝ) :
    ∫ ω, g ω ∂hybMeasure μ N J = ∫ ω', g (ofPairs ω') ∂pairMeasure μ N J := by
  have h := (measurePreserving_arrowProdEquivProdArrow (Torus d) (Fin J → ℝ) (Fin N)
    (fun _ : Fin N => μ) (fun _ : Fin N => Measure.pi fun _ : Fin J => gaussianReal 0 1))
  exact (h.integral_comp' (f := MeasurableEquiv.arrowProdEquivProdArrow (Torus d) (Fin J → ℝ)
    (Fin N)) g).symm

/-- Lower integrals over the hybrid space are lower integrals over the label-wise space. -/
theorem lintegral_hyb_eq (μ : Measure (Torus d)) [IsProbabilityMeasure μ] (N J : ℕ)
    (g : Config N d × (Fin N → Fin J → ℝ) → ENNReal) :
    ∫⁻ ω, g ω ∂hybMeasure μ N J = ∫⁻ ω', g (ofPairs ω') ∂pairMeasure μ N J := by
  have h := (measurePreserving_arrowProdEquivProdArrow (Torus d) (Fin J → ℝ) (Fin N)
    (fun _ : Fin N => μ) (fun _ : Fin N => Measure.pi fun _ : Fin J => gaussianReal 0 1))
  exact (h.lintegral_comp_emb (MeasurableEquiv.arrowProdEquivProdArrow (Torus d) (Fin J → ℝ)
    (Fin N)).measurableEmbedding g).symm

theorem polyB_ofPairs (e : ℕ → Torus d → ℝ) {N J : ℕ} (c : (Fin N → Fin (J + 1)) → ℝ)
    (B : Finset (Fin N)) (ω : Fin N → Torus d × (Fin J → ℝ)) :
    polyB e c B (ofPairs ω) = pP e c B ω := rfl

/-! ### The interfaces and the good basis -/

/-- **Interface (manuscript (7.9)).** Moments of the polynomials of spectral range `≤ L` on every
intermediate hybrid space are bounded by the `L²` norm of the coefficients. Delivered by lane 3
(Gross hypercontractivity); here a hypothesis. -/
def HybridPolyMoment (μ : Measure (Torus d)) (e : ℕ → Torus d → ℝ) (lam : ℕ → ℝ) (J : ℕ) :
    Prop :=
  ∀ (L : ℝ) (q : ℕ), ∃ K : ℝ, 0 ≤ K ∧ ∀ (N : ℕ) (B : Finset (Fin N))
    (c : (Fin N → Fin (J + 1)) → ℝ), SpectralCoeff lam L c →
      ∫⁻ ω, ENNReal.ofReal (|polyB e c B ω| ^ q) ∂hybMeasure μ N J ≤
        ENNReal.ofReal (K * Real.sqrt (∑ j, c j ^ 2) ^ q)

/-- A measurable, bounded, orthonormal system with `e 0 = 1`. -/
structure GoodBasis (μ : Measure (Torus d)) (e : ℕ → Torus d → ℝ) : Prop where
  zero : e 0 = fun _ => 1
  meas : ∀ j, Measurable (e j)
  bdd : ∀ j, ∃ C, ∀ x, |e j x| ≤ C
  orth : ∀ i j, ∫ x, e i x * e j x ∂μ = if i = j then 1 else 0

/-! ### Identification of the two integrals of S26 -/

/-- The label-wise integral `I(B)`. -/
noncomputable def IP (μ : Measure (Torus d)) (e : ℕ → Torus d → ℝ) {N J JR : ℕ}
    (c : (Fin N → Fin (J + 1)) → ℝ) (δ : ℝ) (hJ : JR ≤ J) (Φ : ℝ × (Fin JR → ℝ) → ℝ)
    (B : Finset (Fin N)) : ℝ :=
  ∫ ω, Φ (pP e c B ω, fun m => zP e c δ B ω (Fin.castLE hJ m)) ∂pairMeasure μ N J

theorem integral_orig_eq_IP (μ : Measure (Torus d)) [IsProbabilityMeasure μ]
    (e : ℕ → Torus d → ℝ) {N J JR : ℕ} (c : (Fin N → Fin (J + 1)) → ℝ) (δ : ℝ) (hJ : JR ≤ J)
    (Φ : ℝ × (Fin JR → ℝ) → ℝ) :
    ∫ X, Φ (polyEval e c X, fun m => Zlow e c δ X (Fin.castLE hJ m))
        ∂Measure.pi (fun _ : Fin N => μ) = IP μ e c δ hJ Φ Finset.univ := by
  have h1 : ∫ X, Φ (polyEval e c X, fun m => Zlow e c δ X (Fin.castLE hJ m))
        ∂Measure.pi (fun _ : Fin N => μ) =
      ∫ ω, Φ (polyEval e c ω.1, fun m => Zlow e c δ ω.1 (Fin.castLE hJ m)) ∂hybMeasure μ N J := by
    unfold hybMeasure
    rw [integral_fun_fst (fun X : Config N d => Φ (polyEval e c X, fun m => Zlow e c δ X (Fin.castLE hJ m)))]
    simp
  rw [h1, integral_hyb_eq]
  unfold IP
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  have hp : pP e c Finset.univ ω = polyEval e c (ofPairs ω).1 := by
    simp [pP, polyEval, ofPairs, lf]
  have hz : ∀ m : Fin J, zP e c δ Finset.univ ω m = Zlow e c δ (ofPairs ω).1 m := by
    intro m
    simp [zP, Zlow, ofPairs, lf]
  simp only [hp, hz]

theorem integral_hyb_eq_IP (μ : Measure (Torus d)) [IsProbabilityMeasure μ]
    (e : ℕ → Torus d → ℝ) {N J JR : ℕ} (c : (Fin N → Fin (J + 1)) → ℝ) (δ : ℝ) (hJ : JR ≤ J)
    (Φ : ℝ × (Fin JR → ℝ) → ℝ) :
    ∫ w, Φ (hybEval e c δ w, fun m => Glow c δ w (Fin.castLE hJ m)) ∂hybMeasure μ N J =
      IP μ e c δ hJ Φ (retained c δ) := by
  rw [integral_hyb_eq]
  unfold IP
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  have hp : pP e c (retained c δ) ω = hybEval e c δ (ofPairs ω) := rfl
  have hz : ∀ m : Fin J, zP e c δ (retained c δ) ω m = Glow c δ (ofPairs ω) m := by
    intro m
    unfold zP Glow
    congr 1
    refine Finset.sum_congr rfl fun l hl => ?_
    exact lf_of_not_mem_succ e (Finset.mem_compl.mp hl) m (ω l)
  simp only [hp, hz]

end SharpLSI.FL
