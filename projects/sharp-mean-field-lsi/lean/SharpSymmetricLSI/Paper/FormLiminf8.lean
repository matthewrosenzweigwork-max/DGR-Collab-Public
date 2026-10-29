import SharpSymmetricLSI.Paper.FormLiminf7

/-!
# R33 (8.20): the particle integration by parts (manuscript (8.15))

With `E = e^{-U_N}` and `φ` a cylinder, for `F ∈ W^{1,1}(𝕋^{N×d})` with weak gradient `g`:
`∫ E ∇F·∇φ(Z_N) dμ^{⊗N} = ∫ E F 𝓛 dμ^{⊗N}`,
`𝓛 = ∑_i [λ_i Z_i ∂_iφ - ∑_j ∂_j∂_iφ A_{ji} + ∂_iφ D_i]`, `D_i = N^{-1/2} ∑_l ∇_lU_N·∇e_i(X_l)`.
-/

open MeasureTheory Filter Topology Real
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-- `D_i = N^{-1/2} ∑_{l,k} ∂_{lk}U_N ∂_k e_i(X_l)`. -/
noncomputable def forceD (W : Torus d → Torus d → ℝ) (μ : Measure (Torus d)) (eC : ℕ → Torus d → ℝ)
    (N : ℕ) (i : ℕ) (X : Config N d) : ℝ :=
  (N : ℝ) ^ (-(1 / 2 : ℝ)) * ∑ l, ∑ k, gsG W μ N (flat X) (l, k) * cgrad (eC (i + 1)) (X l) k

/-- The particle generator applied to `-φ_N`, for a cylinder `φ`. -/
noncomputable def genL (W : Torus d → Torus d → ℝ) (μ : Measure (Torus d)) (eC : ℕ → Torus d → ℝ)
    (lam : ℕ → ℝ) (N : ℕ) (c : Cyl) (X : Config N d) : ℝ :=
  ∑ i : Fin c.J, (lam ((i : ℕ) + 1) * zC eC N c.J X i * cylD c i (zC eC N c.J X) -
    ∑ j : Fin c.J, fderiv ℝ (cylD c i) (zC eC N c.J X) (Pi.single j 1) * mobA eC N X j i +
    cylD c i (zC eC N c.J X) * forceD W μ eC N i X)

theorem sum3_comm {ι κ ρ : Type*} [Fintype ι] [Fintype κ] [Fintype ρ] (f : ι → κ → ρ → ℝ) :
    ∑ i, ∑ l, ∑ k, f i l k = ∑ l, ∑ k, ∑ i, f i l k := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun l _ => Finset.sum_comm

section
variable (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
  {e eC : ℕ → Torus d → ℝ} {lam : ℕ → ℝ} (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam)
  (hφ : ∀ j, ContDiff ℝ 1 (eC j ∘ liftT)) (heC : ∀ j, eC j =ᵐ[haar d] e j) {N : ℕ} (hN : 1 ≤ N)
  (c : Cyl)
include hyp hμ he hφ heC hN

omit hyp hμ he hφ heC hN in
/-- Pointwise: the left side regrouped. -/
theorem lhs_regroup (g : UnitAddTorus (Fin N × Fin d) → Fin N × Fin d → ℝ) (X : Config N d) :
    ∑ i : Fin c.J, (N : ℝ) ^ (-(1 / 2 : ℝ)) * ∑ l, ∑ k, g (flat X) (l, k) *
        multH W (μ : Measure (Torus d)) eC N c.J (cylD c i) (flat X) * cgrad (eC ((i : ℕ) + 1)) (X l) k =
      gsE W (μ : Measure (Torus d)) N (flat X) ^ 2 *
        ∑ p, g (flat X) p * gradZ eC N c.J c.φ (flat X) p := by
  unfold multH gradZ
  rw [Fintype.sum_prod_type]
  simp only [Finset.mul_sum]
  rw [sum3_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ =>
    Finset.sum_congr rfl fun i _ => ?_
  simp only [cylD]
  have : projBlock l (flat X) = X l := rfl
  rw [this, show unflat (flat X) = X from rfl]
  ring

omit hyp hμ he hφ heC in
/-- Pointwise: the right side regrouped. -/
theorem rhs_regroup (F : UnitAddTorus (Fin N × Fin d) → ℝ) (X : Config N d) :
    ∑ i : Fin c.J, (N : ℝ) ^ (-(1 / 2 : ℝ)) * ∑ l, (lam ((i : ℕ) + 1) *
        (F (flat X) * multH W (μ : Measure (Torus d)) eC N c.J (cylD c i) (flat X) *
          eC ((i : ℕ) + 1) (X l)) -
        F (flat X) * ∑ k, multG W (μ : Measure (Torus d)) eC N c.J (cylD c i) (flat X) (l, k) *
          cgrad (eC ((i : ℕ) + 1)) (X l) k) =
      gsE W (μ : Measure (Torus d)) N (flat X) ^ 2 * F (flat X) *
        genL W (μ : Measure (Torus d)) eC lam N c X := by
  set s : ℝ := (N : ℝ) ^ (-(1 / 2 : ℝ))
  set E := gsE W (μ : Measure (Torus d)) N (flat X)
  have hs2 : s ^ 2 = (N : ℝ)⁻¹ := rpow_neg_half_sq N
  have hu : unflat (flat X) = X := rfl
  have hpb : ∀ l, projBlock l (flat X) = X l := fun _ => rfl
  unfold genL
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [multG_eq, multH, hu]
  -- the three pieces
  have h1 : s * ∑ l, eC ((i : ℕ) + 1) (X l) = zC eC N c.J X i := rfl
  have h2 : s * ∑ l, ∑ k, gradZ eC N c.J (cylD c i) (flat X) (l, k) * cgrad (eC ((i : ℕ) + 1)) (X l) k =
      ∑ j : Fin c.J, fderiv ℝ (cylD c i) (zC eC N c.J X) (Pi.single j 1) * mobA eC N X j i := by
    unfold gradZ mobA
    simp only [hu, hpb, Finset.sum_mul, Finset.mul_sum]
    rw [← sum3_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ =>
      Finset.sum_congr rfl fun k _ => ?_
    rw [← hs2]
    ring
  have h3 : s * ∑ l, ∑ k, gsG W (μ : Measure (Torus d)) N (flat X) (l, k) *
      cgrad (eC ((i : ℕ) + 1)) (X l) k = forceD W (μ : Measure (Torus d)) eC N i X := rfl
  set ψ := cylD c i (zC eC N c.J X)
  set G := gsG W (μ : Measure (Torus d)) N (flat X)
  set gZ := gradZ eC N c.J (cylD c i) (flat X)
  set cc : Fin N → Fin d → ℝ := fun l k => cgrad (eC ((i : ℕ) + 1)) (X l) k
  set ee : Fin N → ℝ := fun l => eC ((i : ℕ) + 1) (X l)
  have hk : ∀ l, ∑ k, E ^ 2 * (gZ (l, k) - ψ * G (l, k)) * cc l k =
      E ^ 2 * ∑ k, gZ (l, k) * cc l k - E ^ 2 * ψ * ∑ k, G (l, k) * cc l k := fun l => by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  have e1 : ∑ l, (lam ((i : ℕ) + 1) * (F (flat X) * (ψ * E * E) * ee l) -
        F (flat X) * ∑ k, E ^ 2 * (gZ (l, k) - ψ * G (l, k)) * cc l k) =
      lam ((i : ℕ) + 1) * F (flat X) * ψ * E ^ 2 * ∑ l, ee l -
        F (flat X) * E ^ 2 * (∑ l, ∑ k, gZ (l, k) * cc l k) +
        F (flat X) * E ^ 2 * ψ * (∑ l, ∑ k, G (l, k) * cc l k) := by
    simp_rw [hk]
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun l _ => by ring
  rw [e1]
  have h1' : s * ∑ l, ee l = zC eC N c.J X i := h1
  have h2' : s * ∑ l, ∑ k, gZ (l, k) * cc l k =
      ∑ j : Fin c.J, fderiv ℝ (cylD c i) (zC eC N c.J X) (Pi.single j 1) * mobA eC N X j i := h2
  have h3' : s * ∑ l, ∑ k, G (l, k) * cc l k = forceD W (μ : Measure (Torus d)) eC N i X := h3
  rw [← h1', ← h2', ← h3']
  ring

/-- **The particle integration by parts** (manuscript (8.15)), in `μ^{⊗N}`-form with the weight
`E² = e^{-U_N}`. -/
theorem particle_ibp {F : UnitAddTorus (Fin N × Fin d) → ℝ}
    {g : UnitAddTorus (Fin N × Fin d) → Fin N × Fin d → ℝ} (hF : IsWeakGrad F g)
    (hFi : Integrable F volume) (hgi : ∀ p, Integrable (fun y => g y p) volume) :
    ∫ X, gsE W (μ : Measure (Torus d)) N (flat X) ^ 2 *
        ∑ p, g (flat X) p * gradZ eC N c.J c.φ (flat X) p
        ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))) =
      ∫ X, gsE W (μ : Measure (Torus d)) N (flat X) ^ 2 * F (flat X) *
        genL W (μ : Measure (Torus d)) eC lam N c X
        ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))) := by
  set μm := (μ : Measure (Torus d))
  set s : ℝ := (N : ℝ) ^ (-(1 / 2 : ℝ))
  have hP := fun i : Fin c.J => multH_props hyp hμ hφ hN (contDiff_cylD c i)
    (hasCompactSupport_cylD c i)
  choose hHw hHm hHB hGm hGL using hP
  choose BH hBH using hHB
  choose LG hLG using hGL
  have hc : ∀ (i : Fin c.J) (l : Fin N) (k : Fin d), Measurable fun X : Config N d =>
      cgrad (eC ((i : ℕ) + 1)) (X l) k := fun i l k =>
    (measurable_cgrad (hφ _) k).comp (measurable_pi_apply l)
  have hcb : ∀ i : ℕ, ∃ C, ∀ y k, |cgrad (eC i) y k| ≤ C := fun i => exists_bound_cgrad (hφ i)
  choose Cc hCc using hcb
  have heb : ∀ i : ℕ, ∃ C, ∀ y, |eC i y| ≤ C := fun i => exists_bound_of_contDiff (hφ i)
  choose Ce hCe using heb
  have hem : ∀ (i : Fin c.J) (l : Fin N), Measurable fun X : Config N d => eC ((i : ℕ) + 1) (X l) :=
    fun i l => (measurable_of_contDiff (hφ _)).comp (measurable_pi_apply l)
  -- integrability of the three families
  have iA : ∀ (i : Fin c.J) (l : Fin N), Integrable (fun X : Config N d => ∑ k, g (flat X) (l, k) *
      multH W μm eC N c.J (cylD c i) (flat X) * cgrad (eC ((i : ℕ) + 1)) (X l) k)
      (Measure.pi fun _ : Fin N => μm) := fun i l =>
    integrable_finsetSum _ fun k _ => integrable_pi_comp hyp hμ
      ((integrable_bdd_mul (hBH i) (hHm i).aestronglyMeasurable (hgi (l, k))).congr
        (Eventually.of_forall fun y => mul_comm _ _)) (hc i l k) fun X => hCc _ _ _
  have iB : ∀ (i : Fin c.J) (l : Fin N), Integrable (fun X : Config N d => F (flat X) *
      multH W μm eC N c.J (cylD c i) (flat X) * eC ((i : ℕ) + 1) (X l))
      (Measure.pi fun _ : Fin N => μm) := fun i l =>
    integrable_pi_comp hyp hμ ((integrable_bdd_mul (hBH i) (hHm i).aestronglyMeasurable hFi).congr
      (Eventually.of_forall fun y => mul_comm _ _)) (hem i l) fun X => hCe _ _
  have iC : ∀ (i : Fin c.J) (l : Fin N), Integrable (fun X : Config N d => F (flat X) *
      ∑ k, multG W μm eC N c.J (cylD c i) (flat X) (l, k) * cgrad (eC ((i : ℕ) + 1)) (X l) k)
      (Measure.pi fun _ : Fin N => μm) := fun i l => by
    have := integrable_finsetSum (μ := Measure.pi fun _ : Fin N => μm) Finset.univ
      fun k _ => integrable_pi_comp hyp hμ ((integrable_bdd_mul (fun y => hLG i y (l, k))
        (hGm i (l, k)).aestronglyMeasurable hFi).congr
        (Eventually.of_forall fun y => mul_comm _ _)) (hc i l k) fun X => hCc _ _ _
    refine this.congr (Eventually.of_forall fun X => ?_)
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  have iD : ∀ (i : Fin c.J) (l : Fin N), Integrable (fun X : Config N d =>
      lam ((i : ℕ) + 1) * (F (flat X) * multH W μm eC N c.J (cylD c i) (flat X) *
        eC ((i : ℕ) + 1) (X l)) - F (flat X) * ∑ k, multG W μm eC N c.J (cylD c i) (flat X) (l, k) *
        cgrad (eC ((i : ℕ) + 1)) (X l) k) (Measure.pi fun _ : Fin N => μm) := fun i l =>
    ((iB i l).const_mul _).sub (iC i l)
  -- the identity for each `(i, l)`
  have hil : ∀ (i : Fin c.J) (l : Fin N),
      ∫ X, ∑ k, g (flat X) (l, k) * multH W μm eC N c.J (cylD c i) (flat X) *
          cgrad (eC ((i : ℕ) + 1)) (X l) k ∂Measure.pi (fun _ : Fin N => μm) =
        ∫ X, (lam ((i : ℕ) + 1) * (F (flat X) * multH W μm eC N c.J (cylD c i) (flat X) *
          eC ((i : ℕ) + 1) (X l)) - F (flat X) * ∑ k, multG W μm eC N c.J (cylD c i) (flat X) (l, k) *
          cgrad (eC ((i : ℕ) + 1)) (X l) k) ∂Measure.pi (fun _ : Fin N => μm) := fun i l => by
    rw [integral_sub ((iB i l).const_mul _) (iC i l), integral_const_mul]
    exact ibp_mult hyp hμ he hφ heC l ((i : ℕ) + 1) hF hFi hgi (hHw i) (hHm i) (hBH i) (hGm i)
      (hLG i)
  -- assemble
  have hL : ∫ X, gsE W μm N (flat X) ^ 2 * ∑ p, g (flat X) p * gradZ eC N c.J c.φ (flat X) p
      ∂Measure.pi (fun _ : Fin N => μm) =
      ∑ i : Fin c.J, s * ∑ l, ∫ X, ∑ k, g (flat X) (l, k) * multH W μm eC N c.J (cylD c i) (flat X) *
          cgrad (eC ((i : ℕ) + 1)) (X l) k ∂Measure.pi (fun _ : Fin N => μm) := by
    rw [← integral_congr_ae (Eventually.of_forall fun X => lhs_regroup c g X)]
    rw [integral_finsetSum _ fun i _ => (integrable_finsetSum _ fun l _ => iA i l).const_mul _]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_const_mul, integral_finsetSum _ fun l _ => iA i l]
  have hR : ∫ X, gsE W μm N (flat X) ^ 2 * F (flat X) * genL W μm eC lam N c X
      ∂Measure.pi (fun _ : Fin N => μm) =
      ∑ i : Fin c.J, s * ∑ l, ∫ X, (lam ((i : ℕ) + 1) * (F (flat X) *
          multH W μm eC N c.J (cylD c i) (flat X) * eC ((i : ℕ) + 1) (X l)) -
          F (flat X) * ∑ k, multG W μm eC N c.J (cylD c i) (flat X) (l, k) *
          cgrad (eC ((i : ℕ) + 1)) (X l) k) ∂Measure.pi (fun _ : Fin N => μm) := by
    rw [← integral_congr_ae (Eventually.of_forall fun X => rhs_regroup hN c F X)]
    rw [integral_finsetSum _ fun i _ => (integrable_finsetSum _ fun l _ => iD i l).const_mul _]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_const_mul, integral_finsetSum _ fun l _ => iD i l]
  rw [hL, hR]
  exact Finset.sum_congr rfl fun i _ => by rw [Finset.sum_congr rfl fun l _ => hil i l]

end

end SharpLSI
