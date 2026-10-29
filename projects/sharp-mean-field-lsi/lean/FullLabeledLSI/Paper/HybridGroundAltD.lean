import FullLabeledLSI.Paper.HybridGroundAltC

/-!
# Hybrid inequality (7.17), alternative route, part D: Gaussian monomials

`mono T g = ∏_{k ∈ T} g_k` on `Fin M → ℝ`: orthonormality in `L²(γ_M)`
(`integral_mono_mul`), its partial derivatives (`fderiv_mono_single`) and the weighted Dirichlet
form (`sum_energy_mono`). The Gaussian factor `Yf B j` of the hybrid polynomial is the monomial
`mono (TT B j)` (`Yf_eq_mono`).
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open scoped ENNReal ContDiff

noncomputable section

namespace SharpLSI.FL.HLA

open SharpLSI SharpLSI.FL.Gross

section mono
variable {M : ℕ}

/-- The multilinear monomial `∏_{k ∈ T} g_k`. -/
def mono (T : Finset (Fin M)) (g : Fin M → ℝ) : ℝ := ∏ k ∈ T, g k

theorem mono_mul_eq (T T' : Finset (Fin M)) (g : Fin M → ℝ) :
    mono T g * mono T' g =
      ∏ k, ((if k ∈ T then g k else 1) * (if k ∈ T' then g k else 1)) := by
  unfold mono
  rw [Finset.prod_mul_distrib]
  congr 1 <;> simp [Finset.prod_ite_mem]

theorem integral_gauss_ite (a b : Prop) [Decidable a] [Decidable b] :
    ∫ t : ℝ, ((if a then t else 1) * (if b then t else 1)) ∂gaussianReal 0 1 =
      if (a ↔ b) then 1 else 0 := by
  by_cases ha : a <;> by_cases hb : b <;> simp [ha, hb]
  simpa [sq] using integral_std_gaussian_sq

/-- **Orthonormality of the monomials.** -/
theorem integral_mono_mul (T T' : Finset (Fin M)) :
    ∫ g, mono T g * mono T' g ∂gpi M = if T = T' then 1 else 0 := by
  simp_rw [mono_mul_eq]
  rw [show gpi M = Measure.pi fun _ : Fin M => gaussianReal 0 1 from rfl,
    integral_fintype_prod_eq_prod (fun k (t : ℝ) => (if k ∈ T then t else 1) * (if k ∈ T' then t else 1))]
  simp_rw [integral_gauss_ite]
  rw [Finset.prod_boole]
  by_cases h : T = T'
  · subst h; simp
  · rw [if_neg h, if_neg]
    intro hall
    apply h
    ext k
    exact hall k (Finset.mem_univ k)

theorem hasFDerivAt_mono (T : Finset (Fin M)) (g : Fin M → ℝ) :
    HasFDerivAt (mono T) (∑ i ∈ T, (∏ j ∈ T.erase i, g j) •
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin M => ℝ) i)) g := by
  have h := HasFDerivAt.finsetProd (u := T) (g := fun i (g' : Fin M → ℝ) => g' i)
    (g' := fun i => (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin M => ℝ) i)) (x := g)
    (fun i _ => (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin M => ℝ) i).hasFDerivAt)
  exact h

theorem fderiv_mono_single (T : Finset (Fin M)) (l : Fin M) (g : Fin M → ℝ) :
    fderiv ℝ (mono T) g (Pi.single l 1) = if l ∈ T then mono (T.erase l) g else 0 := by
  rw [(hasFDerivAt_mono T g).fderiv]
  simp only [_root_.sum_apply, _root_.smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul,
    Pi.single_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq']
  rfl

theorem sum_energy_mono (w : Fin M → ℝ) (T T' : Finset (Fin M)) :
    ∑ l, w l * ∫ g, fderiv ℝ (mono T) g (Pi.single l 1) * fderiv ℝ (mono T') g (Pi.single l 1)
        ∂gpi M = if T = T' then ∑ l ∈ T, w l else 0 := by
  simp_rw [fderiv_mono_single]
  have h1 : ∀ l, ∫ g, (if l ∈ T then mono (T.erase l) g else 0) *
      (if l ∈ T' then mono (T'.erase l) g else 0) ∂gpi M =
      if l ∈ T ∧ l ∈ T' then (if T.erase l = T'.erase l then 1 else 0) else 0 := by
    intro l
    by_cases hT : l ∈ T <;> by_cases hT' : l ∈ T' <;> simp [hT, hT', integral_mono_mul]
  simp_rw [h1]
  by_cases h : T = T'
  · subst h
    simp [Finset.sum_ite_mem]
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases hc : l ∈ T ∧ l ∈ T' ∧ T.erase l = T'.erase l
    · exfalso
      apply h
      have := Finset.insert_erase hc.1
      rw [← this, hc.2.2, Finset.insert_erase hc.2.1]
    · simp only [mul_eq_zero]
      right
      by_cases h2 : l ∈ T ∧ l ∈ T'
      · rw [if_pos h2, if_neg]
        intro h3; exact hc ⟨h2.1, h2.2, h3⟩
      · rw [if_neg h2]

end mono

section yf
variable {N J : ℕ}

/-- The set of Gaussian coordinates used by the Gaussian factor `Yf B j`. -/
def TT (B : Finset (Fin N)) (j : Fin N → Fin (J + 1)) : Finset (Fin (N * J)) :=
  Finset.univ.filter fun k => flatLab k ∉ B ∧ (j (flatLab k) : ℕ) = (flatMode k : ℕ) + 1

theorem mem_TT {B : Finset (Fin N)} {j : Fin N → Fin (J + 1)} {k : Fin (N * J)} :
    k ∈ TT B j ↔ flatLab k ∉ B ∧ (j (flatLab k) : ℕ) = (flatMode k : ℕ) + 1 := by
  simp [TT]

theorem mem_TT_pair {B : Finset (Fin N)} {j : Fin N → Fin (J + 1)} (i : Fin N) (m : Fin J) :
    finProdFinEquiv (i, m) ∈ TT B j ↔ i ∉ B ∧ (j i : ℕ) = (m : ℕ) + 1 := by
  rw [mem_TT]
  simp [flatLab, flatMode]

theorem Yf_eq_mono (B : Finset (Fin N)) (j : Fin N → Fin (J + 1)) (g : Fin (N * J) → ℝ) :
    Yf B j g = mono (TT B j) g := by
  unfold Yf mono
  have h1 : ∏ k ∈ TT B j, g k = ∏ k, (if k ∈ TT B j then g k else 1) := by
    simp [Finset.prod_ite_mem]
  rw [h1, ← finProdFinEquiv.prod_comp, Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [mem_TT_pair]
  unfold yfac
  by_cases hi : i ∈ B
  · simp [hi]
  · by_cases h0 : (j i : ℕ) = 0
    · simp [hi, h0]
    · have hlt : (j i : ℕ) - 1 < J := by have := (j i).isLt; omega
      rw [Finset.prod_eq_single (⟨(j i : ℕ) - 1, hlt⟩ : Fin J)]
      · simp [hi, h0]
        omega
      · intro m _ hm
        have : ¬ (i ∉ B ∧ (j i : ℕ) = (m : ℕ) + 1) := by
          rintro ⟨-, h⟩
          apply hm
          ext
          simp only
          omega
        simp [this]
      · intro h; exact absurd (Finset.mem_univ _) h

theorem TT_eq_iff {B : Finset (Fin N)} {j j' : Fin N → Fin (J + 1)} :
    TT B j = TT B j' ↔ ∀ i, i ∉ B → j i = j' i := by
  constructor
  · intro h i hi
    by_cases h0 : (j i : ℕ) = 0
    · by_contra hne
      have h0' : (j' i : ℕ) ≠ 0 := fun h2 => hne (Fin.ext (by omega))
      have hlt : (j' i : ℕ) - 1 < J := by have := (j' i).isLt; omega
      have hm : finProdFinEquiv (i, (⟨(j' i : ℕ) - 1, hlt⟩ : Fin J)) ∈ TT B j' := by
        rw [mem_TT_pair]; refine ⟨hi, ?_⟩; simp only; omega
      rw [← h, mem_TT_pair] at hm
      simp only at hm
      omega
    · have hlt : (j i : ℕ) - 1 < J := by have := (j i).isLt; omega
      have hm : finProdFinEquiv (i, (⟨(j i : ℕ) - 1, hlt⟩ : Fin J)) ∈ TT B j := by
        rw [mem_TT_pair]; refine ⟨hi, ?_⟩; simp only; omega
      rw [h, mem_TT_pair] at hm
      simp only at hm
      exact Fin.ext (by omega)
  · intro h
    ext k
    rw [mem_TT, mem_TT]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, by rw [← h _ h1]; exact h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, by rw [h _ h1]; exact h2⟩

end yf

section sumTT
variable {N J : ℕ}

theorem sum_TT (lam : ℕ → ℝ) (hlam0 : lam 0 = 0) (B : Finset (Fin N)) (j : Fin N → Fin (J + 1)) :
    ∑ k ∈ TT B j, lam ((flatMode k : ℕ) + 1) = ∑ i, if i ∈ B then 0 else lam (j i) := by
  have h1 : ∑ k ∈ TT B j, lam ((flatMode k : ℕ) + 1) =
      ∑ k, (if k ∈ TT B j then lam ((flatMode k : ℕ) + 1) else 0) := by
    simp [Finset.sum_ite_mem]
  rw [h1, ← finProdFinEquiv.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [mem_TT_pair]
  by_cases hi : i ∈ B
  · simp [hi]
  · by_cases h0 : (j i : ℕ) = 0
    · have : j i = 0 := Fin.ext h0
      simp [hi, this, hlam0]
    · have hlt : (j i : ℕ) - 1 < J := by have := (j i).isLt; omega
      rw [Finset.sum_eq_single (⟨(j i : ℕ) - 1, hlt⟩ : Fin J)]
      · have e1 : (j i : ℕ) = (j i : ℕ) - 1 + 1 := by omega
        have e2 : (flatMode (finProdFinEquiv (i, (⟨(j i : ℕ) - 1, hlt⟩ : Fin J))) : ℕ) = (j i : ℕ) - 1 := by
          simp [flatMode]
        simp only [if_pos (show i ∉ B ∧ (j i : ℕ) = ((⟨(j i : ℕ) - 1, hlt⟩ : Fin J) : ℕ) + 1 from ⟨hi, e1⟩),
          e2, if_neg hi]
        congr 1; omega
      · intro m _ hm
        have : ¬ (i ∉ B ∧ (j i : ℕ) = (m : ℕ) + 1) := by
          rintro ⟨-, h⟩
          apply hm
          ext
          simp only
          omega
        simp [this, flatMode]
      · intro h; exact absurd (Finset.mem_univ _) h

end sumTT

section gauss
variable {N J : ℕ}

theorem Yf_eq_mono_fun (B : Finset (Fin N)) (j : Fin N → Fin (J + 1)) :
    Yf B j = mono (TT B j) := funext (Yf_eq_mono B j)

/-- (b1) Orthonormality of the Gaussian factors. -/
theorem integral_Yf_mul (B : Finset (Fin N)) (j j' : Fin N → Fin (J + 1)) :
    ∫ g, Yf B j g * Yf B j' g ∂gpi (N * J) = if ∀ i, i ∉ B → j i = j' i then 1 else 0 := by
  simp_rw [Yf_eq_mono]
  rw [integral_mono_mul]
  simp only [TT_eq_iff]

/-- (b2) The Gaussian energy of the Gaussian factors. -/
theorem sum_energy_Yf (lam : ℕ → ℝ) (hlam0 : lam 0 = 0) (B : Finset (Fin N))
    (j j' : Fin N → Fin (J + 1)) :
    ∑ k, lam ((flatMode k : ℕ) + 1) * ∫ g, fderiv ℝ (Yf B j) g (Pi.single k 1) *
        fderiv ℝ (Yf B j') g (Pi.single k 1) ∂gpi (N * J) =
      if ∀ i, i ∉ B → j i = j' i then ∑ i, (if i ∈ B then 0 else lam (j i)) else 0 := by
  rw [Yf_eq_mono_fun, Yf_eq_mono_fun]
  rw [sum_energy_mono (fun k => lam ((flatMode k : ℕ) + 1)) (TT B j) (TT B j')]
  by_cases h : ∀ i, i ∉ B → j i = j' i
  · rw [if_pos ((TT_eq_iff).2 h), if_pos h, sum_TT lam hlam0]
  · rw [if_neg (fun h' => h ((TT_eq_iff).1 h')), if_neg h]

end gauss

end SharpLSI.FL.HLA

end
