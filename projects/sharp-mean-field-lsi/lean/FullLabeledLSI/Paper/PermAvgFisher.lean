import FullLabeledLSI.Paper.PermAvg
import FullLabeledLSI.Infra.FisherDensity
import FullLabeledLSI.Infra.PermWeakGrad

/-!
# Lemma 5.1, Fisher part: the abstract Pythagoras identity

Vector fields on `Config N d` are functions `V : Config N d → Fin N × Fin d → ℝ`. The label
permutation acts by `(σ • V)(X)_{(i,k)} = V(X ∘ σ)_{(σ⁻¹ i, k)}`. Given the equivariance data of
the gradients (a.e.), the Pythagoras identity
`∫ u |a - ℓ|² = ∫ ū |ā - ℓ|² + ∫ u |a - ā|²` holds.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace SharpLSI.FL

variable {N d : ℕ}

/-- Vector fields on `Config N d`. -/
abbrev VF (N d : ℕ) := Config N d → Fin N × Fin d → ℝ

/-- The action of a label permutation on vector fields. -/
def VF.act (σ : Equiv.Perm (Fin N)) (V : VF N d) : VF N d :=
  fun X q => V (X ∘ σ) (σ.symm q.1, q.2)

/-- Pointwise dot product of vector fields. -/
def VF.dot (V W : VF N d) (X : Config N d) : ℝ := ∑ q, V X q * W X q

/-- Measurable and bounded. -/
def VF.Good (V : VF N d) : Prop :=
  (∀ q, Measurable fun X => V X q) ∧ ∃ C : ℝ, ∀ X q, |V X q| ≤ C

theorem VF.dot_act (σ : Equiv.Perm (Fin N)) (V W : VF N d) (X : Config N d) :
    VF.dot (VF.act σ V) (VF.act σ W) X = VF.dot V W (X ∘ σ) := by
  unfold VF.dot VF.act
  exact Fintype.sum_equiv (Equiv.prodCongr σ.symm (Equiv.refl _)) _ _ fun q => rfl

theorem VF.Good.act {σ : Equiv.Perm (Fin N)} {V : VF N d} (h : V.Good) : (VF.act σ V).Good := by
  obtain ⟨hm, C, hC⟩ := h
  refine ⟨fun q => ?_, C, fun X q => hC _ _⟩
  exact (hm _).comp (permEquiv (d := d) σ).measurable

theorem VF.Good.sub {V W : VF N d} (hV : V.Good) (hW : W.Good) : VF.Good (V - W) := by
  obtain ⟨hm, C, hC⟩ := hV
  obtain ⟨hm', C', hC'⟩ := hW
  exact ⟨fun q => (hm q).sub (hm' q), C + C', fun X q => (abs_sub _ _).trans (add_le_add (hC _ _) (hC' _ _))⟩

theorem VF.Good.dot {V W : VF N d} (hV : V.Good) (hW : W.Good) :
    Measurable (VF.dot V W) ∧ ∃ B : ℝ, ∀ X, |VF.dot V W X| ≤ B := by
  obtain ⟨hm, C, hC⟩ := hV
  obtain ⟨hm', C', hC'⟩ := hW
  refine ⟨Finset.measurable_sum _ fun q _ => (hm q).mul (hm' q),
    Fintype.card (Fin N × Fin d) * (C * C'), fun X => ?_⟩
  unfold VF.dot
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ q, |V X q * W X q| ≤ ∑ _q : Fin N × Fin d, C * C' := Finset.sum_le_sum fun q _ => by
        rw [abs_mul]; exact mul_le_mul (hC _ _) (hC' _ _) (abs_nonneg _) ((abs_nonneg _).trans (hC X q))
    _ = _ := by simp


/-- a.e. version of `integral_avgDens_mul`: `h` symmetric only almost everywhere. -/
theorem integral_avgDens_mul_ae {u h : Config N d → ℝ} (hu : Measurable u) (hh : Measurable h)
    {Bu Bh : ℝ} (hBu : ∀ x, |u x| ≤ Bu) (hBh : ∀ x, |h x| ≤ Bh)
    (hs : ∀ σ : Equiv.Perm (Fin N), ∀ᵐ X ∂(volume : Measure (Config N d)), h (X ∘ σ) = h X) :
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
    refine integral_congr_ae ?_
    filter_upwards [hs σ] with X hX
    simp only [hX]
  simp_rw [e1]
  rw [integral_const_mul, integral_finsetSum _ fun σ _ => hterm σ]
  simp only [e2, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    nsmul_eq_mul]
  have hN : (Nat.factorial N : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos N).ne'
  field_simp

/-- A bilinear-symmetric scalar built from `σ`-equivariant fields is symmetric a.e. -/
theorem VF.dot_perm_ae {V W : VF N d} (σ : Equiv.Perm (Fin N))
    (hV : ∀ᵐ X ∂(volume : Measure (Config N d)), ∀ q, VF.act σ V X q = V X q)
    (hW : ∀ᵐ X ∂(volume : Measure (Config N d)), ∀ q, VF.act σ W X q = W X q) :
    ∀ᵐ X ∂(volume : Measure (Config N d)), VF.dot V W (X ∘ σ) = VF.dot V W X := by
  filter_upwards [hV, hW] with X h1 h2
  rw [← VF.dot_act]
  unfold VF.dot
  exact Finset.sum_congr rfl fun q _ => by rw [h1, h2]


theorem VF.integrable_dot {V W : VF N d} (hV : V.Good) (hW : W.Good) :
    Integrable (VF.dot V W) (volume : Measure (Config N d)) := by
  obtain ⟨hm, B, hB⟩ := hV.dot hW
  exact integrable_bdd hm hB

/-- Averaging: `∫ Du·w = ∫ Dū·w` for `Dū = (N!)⁻¹ ∑_σ σ • Du` and equivariant `w`. -/
theorem integral_dot_avg {Du Dū w : VF N d} (hDu : Du.Good) (hw : w.Good)
    (hweq : ∀ σ : Equiv.Perm (Fin N), ∀ᵐ X ∂(volume : Measure (Config N d)),
      ∀ q, VF.act σ w X q = w X q)
    (hav : ∀ᵐ X ∂(volume : Measure (Config N d)), ∀ q,
      Dū X q = ((Nat.factorial N : ℝ))⁻¹ * ∑ σ : Equiv.Perm (Fin N), VF.act σ Du X q) :
    ∫ X, VF.dot Du w X ∂(volume : Measure (Config N d)) =
      ∫ X, VF.dot Dū w X ∂(volume : Measure (Config N d)) := by
  have key : ∀ σ : Equiv.Perm (Fin N), ∫ X, VF.dot (VF.act σ Du) w X ∂(volume : Measure (Config N d))
      = ∫ X, VF.dot Du w X ∂(volume : Measure (Config N d)) := fun σ => by
    rw [← integral_comp_perm_vol σ (VF.dot Du w)]
    refine integral_congr_ae ?_
    filter_upwards [hweq σ] with X hX
    rw [← VF.dot_act]
    unfold VF.dot
    exact Finset.sum_congr rfl fun q _ => by rw [hX q]
  have hN : (Nat.factorial N : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos N).ne'
  have hpt : ∀ᵐ X ∂(volume : Measure (Config N d)), VF.dot Dū w X =
      ((Nat.factorial N : ℝ))⁻¹ * ∑ σ : Equiv.Perm (Fin N), VF.dot (VF.act σ Du) w X := by
    filter_upwards [hav] with X hX
    unfold VF.dot
    have h1 : ∀ q, Dū X q * w X q =
        ((Nat.factorial N : ℝ))⁻¹ * ∑ σ : Equiv.Perm (Fin N), VF.act σ Du X q * w X q :=
      fun q => by rw [hX q, mul_assoc, Finset.sum_mul]
    rw [Finset.sum_congr rfl fun q _ => h1 q, ← Finset.mul_sum, Finset.sum_comm]
  rw [integral_congr_ae hpt, integral_const_mul,
    integral_finsetSum _ fun σ _ => VF.integrable_dot hDu.act hw]
  simp only [key, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    nsmul_eq_mul]
  field_simp


/-- **Abstract Pythagoras identity** (the Fisher part of Lemma 5.1). -/
theorem pythagoras {u : Config N d → ℝ} (hum : Measurable u) {Cu : ℝ} (hu0 : ∀ x, 0 < u x)
    (huC : ∀ x, u x ≤ Cu) {Du Da Dū Dā ℓ : VF N d}
    (hDu : Du.Good) (hDa : Da.Good) (hDū : Dū.Good) (hDā : Dā.Good) (hℓ : ℓ.Good)
    (hua : ∀ X q, u X * Da X q = Du X q)
    (hūā : ∀ X q, avgDens u X * Dā X q = Dū X q)
    (hāeq : ∀ σ : Equiv.Perm (Fin N), ∀ᵐ X ∂(volume : Measure (Config N d)),
      ∀ q, VF.act σ Dā X q = Dā X q)
    (hℓeq : ∀ σ : Equiv.Perm (Fin N), ∀ᵐ X ∂(volume : Measure (Config N d)),
      ∀ q, VF.act σ ℓ X q = ℓ X q)
    (hav : ∀ᵐ X ∂(volume : Measure (Config N d)), ∀ q,
      Dū X q = ((Nat.factorial N : ℝ))⁻¹ * ∑ σ : Equiv.Perm (Fin N), VF.act σ Du X q) :
    ∫ X, u X * VF.dot (Da - ℓ) (Da - ℓ) X ∂(volume : Measure (Config N d)) =
      ∫ X, avgDens u X * VF.dot (Dā - ℓ) (Dā - ℓ) X ∂(volume : Measure (Config N d)) +
        ∫ X, u X * VF.dot (Da - Dā) (Da - Dā) X ∂(volume : Measure (Config N d)) := by
  set w : VF N d := Dā - ℓ with hw
  have hwG : w.Good := hDā.sub hℓ
  have hweq : ∀ σ : Equiv.Perm (Fin N), ∀ᵐ X ∂(volume : Measure (Config N d)),
      ∀ q, VF.act σ w X q = w X q := fun σ => by
    filter_upwards [hāeq σ, hℓeq σ] with X h1 h2 q
    simp only [hw, Pi.sub_apply, VF.act] at h1 h2 ⊢
    rw [h1 q, h2 q] 
  have hmσ : Measurable u := hum
  have huB : ∀ x, |u x| ≤ Cu := fun x => by rw [abs_of_pos (hu0 x)]; exact huC x
  -- integrability of the pieces
  have hInt : ∀ {V W : VF N d}, V.Good → W.Good →
      Integrable (fun X => u X * VF.dot V W X) (volume : Measure (Config N d)) := fun {V W} hV hW => by
    obtain ⟨hm, B, hB⟩ := hV.dot hW
    exact integrable_bdd (hum.mul hm) (B := Cu * B) fun x => by
      rw [abs_mul]; exact mul_le_mul (huB x) (hB x) (abs_nonneg _) ((abs_nonneg _).trans (huB x))
  have hDaā : (Da - Dā).Good := hDa.sub hDā
  -- pointwise expansion
  have hexp : ∀ X, u X * VF.dot (Da - ℓ) (Da - ℓ) X =
      u X * VF.dot (Da - Dā) (Da - Dā) X + 2 * (u X * VF.dot (Da - Dā) w X) +
        u X * VF.dot w w X := fun X => by
    unfold VF.dot
    simp only [hw, Pi.sub_apply]
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun q _ => by ring
  -- the cross term vanishes
  have hcross : ∫ X, u X * VF.dot (Da - Dā) w X ∂(volume : Measure (Config N d)) = 0 := by
    have p1 : ∀ X, u X * VF.dot (Da - Dā) w X =
        VF.dot Du w X - u X * VF.dot Dā w X := fun X => by
      unfold VF.dot
      simp only [Pi.sub_apply]
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [← hua X q]; ring
    have i1 : Integrable (VF.dot Du w) (volume : Measure (Config N d)) :=
      VF.integrable_dot hDu hwG
    have i2 : Integrable (fun X => u X * VF.dot Dā w X) (volume : Measure (Config N d)) :=
      hInt hDā hwG
    simp_rw [p1]
    rw [integral_sub i1 i2]
    have e1 := integral_dot_avg hDu hwG hweq hav
    have hsym : ∀ σ : Equiv.Perm (Fin N), ∀ᵐ X ∂(volume : Measure (Config N d)),
        VF.dot Dā w (X ∘ σ) = VF.dot Dā w X := fun σ => VF.dot_perm_ae σ (hāeq σ) (hweq σ)
    obtain ⟨hm1, B1, hB1⟩ := hDā.dot hwG
    have e2 := integral_avgDens_mul_ae hum hm1 huB hB1 hsym
    have e3 : ∫ X, avgDens u X * VF.dot Dā w X ∂(volume : Measure (Config N d)) =
        ∫ X, VF.dot Dū w X ∂(volume : Measure (Config N d)) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
      show avgDens u X * VF.dot Dā w X = VF.dot Dū w X
      unfold VF.dot
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun q _ => by rw [← hūā X q]; ring
    rw [e1, ← e2, e3]; ring
  -- the symmetric term
  have hsymw : ∀ σ : Equiv.Perm (Fin N), ∀ᵐ X ∂(volume : Measure (Config N d)),
      VF.dot w w (X ∘ σ) = VF.dot w w X := fun σ => VF.dot_perm_ae σ (hweq σ) (hweq σ)
  obtain ⟨hm2, B2, hB2⟩ := hwG.dot hwG
  have e4 := integral_avgDens_mul_ae hum hm2 huB hB2 hsymw
  simp_rw [hexp]
  have ia := hInt hDaā hDaā
  have ib := hInt hDaā hwG
  have ic := hInt hwG hwG
  have ib2 : Integrable (fun X => 2 * (u X * VF.dot (Da - Dā) w X))
      (volume : Measure (Config N d)) := ib.const_mul 2
  have iab : Integrable (fun X => u X * VF.dot (Da - Dā) (Da - Dā) X +
      2 * (u X * VF.dot (Da - Dā) w X)) (volume : Measure (Config N d)) := ia.add ib2
  rw [integral_add iab ic, integral_add ia ib2, integral_const_mul, hcross, e4]
  ring

end SharpLSI.FL
