import FullLabeledLSI.Paper.Hybrid63AltE
import FullLabeledLSI.Paper.Hybrid63Defs

/-!
# Proposition 6.3, step R4b (7.21): removing the retained labels from the tilt

* `uR`, `vR` are quadratic forms on the modes in `A.s R` (up to a constant), and read only those.
* `est721`: for a quadratic form `quadFA s Qm`,
  `|∫ F² (quad Z_N - quad Z^low)| ≤ (∑|Q|) ((t/4) Mq + Kq (|B_N|/N)/(2t))` for every `t > 0`,
  uniformly in `N`, `c`, `δ`.
-/

open MeasureTheory ProbabilityTheory

noncomputable section

namespace SharpLSI.FL

variable {d : ℕ}

section quad
variable {W : Torus d → Torus d → ℝ} {μ : Measure (Torus d)} {e : ℕ → Torus d → ℝ}

theorem quadF_congr (s : Finset ℕ) (Q : ℕ → ℕ → ℝ) {z z' : ℕ → ℝ} (h : ∀ i ∈ s, z i = z' i) :
    quadFA s Q z = quadFA s Q z' := by
  unfold quadFA
  refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => ?_
  rw [h i hi, h j hj]

theorem uR_eq_quadA (A : FiniteRankApprox W μ e) (R : ℕ) (z : ℕ → ℝ) :
    uR A R z = quadFA (A.s R) (fun i j => A.a R i j / 2) z := by
  unfold uR quadFA
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- The matrix of the quadratic part of `v_R`. -/
def vQ (A : FiniteRankApprox W μ e) (lam : ℕ → ℝ) (R : ℕ) (i j : ℕ) : ℝ :=
  (1 / 4) * ∑ m ∈ A.s R, lam (m + 1) * A.a R m i * A.a R m j + (1 / 2) * lam (i + 1) * A.a R i j

theorem vR_eq_quad (A : FiniteRankApprox W μ e) (lam : ℕ → ℝ) (R : ℕ) (z : ℕ → ℝ) :
    vR A lam R z = quadFA (A.s R) (vQ A lam R) z -
      (1 / 2) * ∑ m ∈ A.s R, A.a R m m * lam (m + 1) := by
  unfold vR quadFA vQ
  have h1 : ∀ m, (∑ j ∈ A.s R, A.a R m j * z j) ^ 2 =
      ∑ i ∈ A.s R, ∑ j ∈ A.s R, A.a R m i * A.a R m j * z i * z j := by
    intro m
    rw [sq, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have h2 : (1 / 4) * ∑ m ∈ A.s R, lam (m + 1) * (∑ j ∈ A.s R, A.a R m j * z j) ^ 2 =
      ∑ i ∈ A.s R, ∑ j ∈ A.s R, ((1 / 4) * ∑ m ∈ A.s R, lam (m + 1) * A.a R m i * A.a R m j) *
        z i * z j := by
    simp_rw [h1, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun m _ => by ring
  have h3 : (1 / 2) * ∑ i ∈ A.s R, ∑ j ∈ A.s R, z i * lam (i + 1) * A.a R i j * z j =
      ∑ i ∈ A.s R, ∑ j ∈ A.s R, ((1 / 2) * lam (i + 1) * A.a R i j) * z i * z j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => by ring
  have h4 : ∑ i ∈ A.s R, ∑ j ∈ A.s R, ((1 / 4) * ∑ m ∈ A.s R, lam (m + 1) * A.a R m i * A.a R m j +
      (1 / 2) * lam (i + 1) * A.a R i j) * z i * z j =
      ∑ i ∈ A.s R, ∑ j ∈ A.s R, ((1 / 4) * ∑ m ∈ A.s R, lam (m + 1) * A.a R m i * A.a R m j) *
        z i * z j +
      ∑ i ∈ A.s R, ∑ j ∈ A.s R, ((1 / 2) * lam (i + 1) * A.a R i j) * z i * z j := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => by ring
  rw [h4, ← h2, ← h3]
  ring

theorem uR_congr (A : FiniteRankApprox W μ e) (R : ℕ) {z z' : ℕ → ℝ}
    (h : ∀ i ∈ A.s R, z i = z' i) : uR A R z = uR A R z' := by
  rw [uR_eq_quadA, uR_eq_quadA]; exact quadF_congr _ _ h

theorem vR_congr (A : FiniteRankApprox W μ e) (lam : ℕ → ℝ) (R : ℕ) {z z' : ℕ → ℝ}
    (h : ∀ i ∈ A.s R, z i = z' i) : vR A lam R z = vR A lam R z' := by
  rw [vR_eq_quad, vR_eq_quad]; rw [quadF_congr _ _ h]

end quad

/-- Integrals over the original space are integrals over the label-wise space. -/
theorem integral_Q_eq_pair (μ : Measure (Torus d)) [IsProbabilityMeasure μ] (N J : ℕ)
    (g : Config N d → ℝ) :
    ∫ X, g X ∂Measure.pi (fun _ : Fin N => μ) = ∫ w, g (ofPairs w).1 ∂pairMeasure μ N J := by
  have h1 : ∫ X, g X ∂Measure.pi (fun _ : Fin N => μ) =
      ∫ ω, g ω.1 ∂hybMeasure μ N J := by
    unfold hybMeasure
    rw [integral_fun_fst (fun X : Config N d => g X)]
    simp
  rw [h1, integral_hyb_eq]

section est
variable {μ : Measure (Torus d)} [IsProbabilityMeasure μ] {e : ℕ → Torus d → ℝ} {lam : ℕ → ℝ}
  {J : ℕ}

theorem est721 (hG : GoodBasis μ e) (hmom : HybridPolyMoment μ e lam J) (hlam0 : lam 0 = 0)
    (L B : ℝ) (s : Finset ℕ) (hs : ∀ i ∈ s, i < J) (Qm : ℕ → ℕ → ℝ) :
    ∃ Mq Kq : ℝ, 0 ≤ Mq ∧ 0 ≤ Kq ∧
      ∀ (N : ℕ) (c : (Fin N → Fin (J + 1)) → ℝ), SpectralCoeff lam L c → ∑ j, c j ^ 2 ≤ B ^ 2 →
        ∀ δ : ℝ, 0 < lowCount c δ → ∀ t : ℝ, 0 < t →
          |∫ X, polyEval e c X ^ 2 * (quadFA s Qm (fun n => fluct e N n X) -
              quadFA s Qm (zext (fun m : Fin J => Zlow e c δ X m)))
              ∂Measure.pi (fun _ : Fin N => μ)| ≤
            (∑ i ∈ s, ∑ j ∈ s, |Qm i j|) *
              ((t / 4) * Mq + Kq * (((retained c δ).card : ℝ) / N) / (2 * t)) := by
  obtain ⟨M8, M4, Kd, hM8, hM4, hKd, hmain⟩ := pair_moments hG hmom hlam0 L B
  refine ⟨M8 + M4, Kd, by positivity, hKd, ?_⟩
  intro N c hc hB δ hn t ht
  obtain ⟨hF, hZ⟩ := hmain N c hc hB δ hn
  rw [integral_Q_eq_pair μ N J]
  have he0 := hG.zero
  set Zn : ℕ → (Fin N → Torus d × (Fin J → ℝ)) → ℝ := fun n w =>
    if h : n < J then Zfp e N ⟨n, h⟩ w else 0 with hZn
  set Zl : ℕ → (Fin N → Torus d × (Fin J → ℝ)) → ℝ := fun n w =>
    if h : n < J then zP e c δ Finset.univ w ⟨n, h⟩ else 0 with hZl
  have hpt : ∀ w : Fin N → Torus d × (Fin J → ℝ),
      polyEval e c (ofPairs w).1 ^ 2 * (quadFA s Qm (fun n => fluct e N n (ofPairs w).1) -
        quadFA s Qm (zext (fun m : Fin J => Zlow e c δ (ofPairs w).1 m))) =
      pP e c Finset.univ w ^ 2 * (quadFA s Qm (fun n => Zn n w) - quadFA s Qm (fun n => Zl n w)) := by
    intro w
    have hp : pP e c Finset.univ w = polyEval e c (ofPairs w).1 := by
      simp [pP, polyEval, ofPairs, lf]
    have hz : ∀ m : Fin J, zP e c δ Finset.univ w m = Zlow e c δ (ofPairs w).1 m := by
      intro m
      simp [zP, Zlow, ofPairs, lf]
    rw [hp]
    congr 2
    · refine quadF_congr s Qm fun n hn' => ?_
      have := hs n hn'
      simp only [hZn, this, dite_true, fluct, Zfp, ofPairs]
    · refine quadF_congr s Qm fun n hn' => ?_
      have := hs n hn'
      simp only [hZl, this, dite_true, zext, hz]
  simp_rw [hpt]
  have hmeasZ : ∀ i ∈ s, Measurable (Zn i) := by
    intro i hi
    have := hs i hi
    simp only [hZn, this, dite_true]
    have := measurable_pP hG (Finset.univ : Finset (Fin N))
      (cZ Finset.univ ((N : ℝ) ^ (-(1 / 2 : ℝ))) ⟨i, hs i hi⟩)
    simpa only [← fun w => Zfp_eq_pP he0 (⟨i, hs i hi⟩ : Fin J) w] using this
  have hmeasZl : ∀ i ∈ s, Measurable (Zl i) := by
    intro i hi
    have := hs i hi
    simp only [hZl, this, dite_true]
    exact measurable_zP hG c δ Finset.univ _
  have key := quad_diff_bound (P := pairMeasure μ N J) (f := fun w => pP e c Finset.univ w)
    (Z := Zn) (Z' := Zl) s Qm (measurable_pP hG _ c) hmeasZ hmeasZl (M8 := M8) (M4 := M4)
    (κ := Kd * (((retained c δ).card : ℝ) / N)) hF.1 hF.2
    (fun i hi => by
      have := (hZ ⟨i, hs i hi⟩).1.1
      simpa [hZn, hZl, hs i hi] using this)
    (fun i hi => by
      have := (hZ ⟨i, hs i hi⟩).1.2
      simpa [hZn, hZl, hs i hi] using this)
    (fun i hi => by
      have := (hZ ⟨i, hs i hi⟩).2.1
      simpa [hZn, hZl, hs i hi] using this)
    (fun i hi => by
      have := (hZ ⟨i, hs i hi⟩).2.2
      simpa [hZn, hZl, hs i hi] using this) ht
  refine key.2.trans (le_of_eq ?_)
  ring

end est

end SharpLSI.FL

end
