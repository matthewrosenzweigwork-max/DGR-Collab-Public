import DGPS.Examples.ThreeSpeciesCircle.OrdinaryRootLocalStabilityCore

/-! A genuine fixed-root comparison of the original Haar H1 deviation and the weighted
relative-root energy. One-dimensional H1 embedding suffices; no derivative-Linfinity
assumption or norm-equivalence conclusion is a premise. -/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace DGPS.Examples.ThreeSpeciesCircle

/-- Multiplication by the SAME positive continuous H1 root gives the required finite
original-H1 comparison. The constant is fixed before every absolute competitor. -/
theorem ordinaryRoot_originalH1_comparison (σ : AbsoluteDensity 1) (u : Torus 1 → ℝ)
    (hu : Continuous u) (hupos : ∀ x, 0 < u x) (hurep : σ.sqrt =ᵐ[haar 1] u) :
    ∃ C : ℝ, 0 < C ∧ ∀ ρ : AbsoluteDensity 1,
      let w := fun x => ρ.sqrt x / u x
      let hw := ordinaryEquality_relativeRoot_memH1 σ ρ u hu hupos hurep
      ordinaryRootH1Deviation σ ρ u ^ 2 ≤
        C * ((∫ x, σ.density x * (weakGradient w hw x 0) ^ 2 ∂haar 1) +
          ∫ x, σ.density x * (w x - 1) ^ 2 ∂haar 1) := by
  let S := weakGradient σ.sqrt σ.sqrt_mem
  have hσ : IsWeakGradient u S :=
    (isWeakGradient_weakGradient σ.sqrt_mem).congr_ae hurep (EventuallyEq.refl _ _)
  let J := ∫ x, (S x 0) ^ 2 ∂haar 1
  have hJ : 0 ≤ J := integral_nonneg fun _ => sq_nonneg _
  have hJi : Integrable (fun x => (S x 0) ^ 2) (haar 1) :=
    (memLp_coord hσ.memLp_grad 0).integrable_sq
  obtain ⟨x0, _, hx0⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty hu.continuousOn
  let m := u x0
  have hm : 0 < m := hupos x0
  have hm2 : 0 < m ^ 2 := sq_pos_of_pos hm
  have hmu : ∀ x, m ^ 2 ≤ u x ^ 2 := fun x =>
    (sq_le_sq₀ hm.le (hupos x).le).2 (hx0 (Set.mem_univ x))
  let C := (4 * m ^ 2 + 8 * J) / m ^ 2
  have hC : 0 < C := div_pos (by nlinarith) hm2
  refine ⟨C, hC, fun ρ => ?_⟩
  let w := fun x => ρ.sqrt x / u x
  let hw := ordinaryEquality_relativeRoot_memH1 σ ρ u hu hupos hurep
  let G := weakGradient w hw
  have hW : IsWeakGradient w G := isWeakGradient_weakGradient hw
  let d := fun x => w x - 1
  have hd : IsWeakGradient d G := hW.sub_const 1
  let A := (eLpNorm d 2 (haar 1)).toReal
  let B := (eLpNorm G 2 (haar 1)).toReal
  let H := A + B
  have hA : 0 ≤ A := ENNReal.toReal_nonneg
  have hB : 0 ≤ B := ENNReal.toReal_nonneg
  have hH : 0 ≤ H := add_nonneg hA hB
  obtain ⟨v, _, hvae, _, hv⟩ := exists_continuous_rep_one hd
  have hdb : ∀ᵐ x ∂haar 1, |d x| ≤ H := by
    filter_upwards [hvae] with x hx
    rw [← hx]
    exact hv x
  have hn : ∀ z : Tangent 1, ‖z‖ ^ 2 = (z 0) ^ 2 := by
    intro z
    simp [EuclideanSpace.norm_sq_eq]
  have hA2 : A ^ 2 = ∫ x, d x ^ 2 ∂haar 1 := by
    dsimp only [A]
    rw [toReal_eLpNorm_two hd.memLp, Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _)]
  have hB2 : B ^ 2 = ∫ x, (G x 0) ^ 2 ∂haar 1 := by
    dsimp only [B]
    rw [toReal_eLpNorm_two_vec hW.memLp_grad, Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _)]
    simp_rw [hn]
  obtain ⟨M, hM⟩ := isCompact_univ.exists_bound_of_continuousOn (hu.pow 2).continuousOn
  have hEi : Integrable (fun x => u x ^ 2 * (G x 0) ^ 2) (haar 1) :=
    (memLp_coord hW.memLp_grad 0).integrable_sq.bdd_mul (hu.pow 2).aestronglyMeasurable
      (Eventually.of_forall fun x => hM x (Set.mem_univ x))
  have hLi : Integrable (fun x => u x ^ 2 * d x ^ 2) (haar 1) :=
    hd.memLp.integrable_sq.bdd_mul (hu.pow 2).aestronglyMeasurable
      (Eventually.of_forall fun x => hM x (Set.mem_univ x))
  let E := ∫ x, u x ^ 2 * (G x 0) ^ 2 ∂haar 1
  let L := ∫ x, u x ^ 2 * d x ^ 2 ∂haar 1
  have hE : 0 ≤ E := integral_nonneg fun _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hL : 0 ≤ L := integral_nonneg fun _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hEmin : m ^ 2 * B ^ 2 ≤ E := by
    rw [hB2, ← integral_const_mul]
    exact integral_mono ((memLp_coord hW.memLp_grad 0).integrable_sq.const_mul _) hEi
      (fun x => mul_le_mul_of_nonneg_right (hmu x) (sq_nonneg _))
  have hLmin : m ^ 2 * A ^ 2 ≤ L := by
    rw [hA2, ← integral_const_mul]
    exact integral_mono (hd.memLp.integrable_sq.const_mul _) hLi
      (fun x => mul_le_mul_of_nonneg_right (hmu x) (sq_nonneg _))
  have hH2 : m ^ 2 * H ^ 2 ≤ 2 * (E + L) := by
    dsimp only [H]
    nlinarith [mul_nonneg (sq_nonneg m) (sq_nonneg (A - B))]
  let R := weakGradient ρ.sqrt ρ.sqrt_mem
  have hρ : IsWeakGradient ρ.sqrt R := isWeakGradient_weakGradient ρ.sqrt_mem
  have hprod : ∀ x, u x * w x = ρ.sqrt x := fun x => by
    dsimp only [w]
    field_simp [(hupos x).ne']
  have hg : R =ᵐ[haar 1] fun x => w x • S x + u x • G x :=
    hρ.ae_eq ((hσ.mul_one_dim hW).congr_ae (Eventually.of_forall hprod) (EventuallyEq.refl _ _))
  let I := ∫ x, (R x 0 - S x 0) ^ 2 ∂haar 1
  have hIi : Integrable (fun x => (R x 0 - S x 0) ^ 2) (haar 1) :=
    ((memLp_coord hρ.memLp_grad 0).sub (memLp_coord hσ.memLp_grad 0)).integrable_sq
  have hI : I ≤ 2 * E + 2 * H ^ 2 * J := by
    have hright : Integrable (fun x => 2 * (u x ^ 2 * (G x 0) ^ 2) +
        (2 * H ^ 2) * (S x 0) ^ 2) (haar 1) := (hEi.const_mul 2).add (hJi.const_mul _)
    have hi := integral_mono_ae hIi hright (by
      filter_upwards [hg, hdb] with x hx hb
      have hxx := congrArg (fun z : Tangent 1 => z 0) hx
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at hxx
      have hd2 : d x ^ 2 ≤ H ^ 2 := sq_le_sq' (by linarith [(abs_le.mp hb).1]) (abs_le.mp hb).2
      have hmul := mul_le_mul_of_nonneg_right hd2 (sq_nonneg (S x 0))
      have he : R x 0 - S x 0 = d x * S x 0 + u x * G x 0 := by
        dsimp only [d]
        rw [hxx]
        ring
      rw [he]
      nlinarith [sq_nonneg (d x * S x 0 - u x * G x 0)])
    rw [integral_add (hEi.const_mul 2) (hJi.const_mul _), integral_const_mul,
      integral_const_mul] at hi
    exact hi
  have hδ : IsWeakGradient (fun x => ρ.sqrt x - u x) (fun x => R x - S x) := by
    have hh := hρ.add (hσ.smul (-1))
    exact hh.congr_ae (Eventually.of_forall fun x => by ring)
      (Eventually.of_forall fun x => by simp [sub_eq_add_neg])
  have hdL : (eLpNorm (fun x => ρ.sqrt x - u x) 2 (haar 1)).toReal ^ 2 = L := by
    rw [toReal_eLpNorm_two hδ.memLp, Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _)]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      dsimp only [L, d, w]
      field_simp [(hupos x).ne'] <;> ring
  have hdG : (eLpNorm (fun x => R x - S x) 2 (haar 1)).toReal ^ 2 = I := by
    rw [toReal_eLpNorm_two_vec hδ.memLp_grad,
      Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _)]
    simp_rw [hn, PiLp.sub_apply]
    rfl
  have hnorm : ordinaryRootH1Deviation σ ρ u ^ 2 ≤ 2 * (L + I) := by
    unfold ordinaryRootH1Deviation
    have hs := sq_nonneg ((eLpNorm (fun x => ρ.sqrt x - u x) 2 (haar 1)).toReal -
      (eLpNorm (fun x => R x - S x) 2 (haar 1)).toReal)
    nlinarith [hdL, hdG]
  have hweighted : m ^ 2 * ordinaryRootH1Deviation σ ρ u ^ 2 ≤
      (4 * m ^ 2 + 8 * J) * (E + L) := by
    have h1 := mul_le_mul_of_nonneg_left hnorm hm2.le
    have h2 := mul_le_mul_of_nonneg_left hI hm2.le
    have h3 := mul_le_mul_of_nonneg_left hH2 (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hJ)
    nlinarith [mul_nonneg hm2.le hL]
  have heq : E + L =
      (∫ x, σ.density x * (G x 0) ^ 2 ∂haar 1) +
        ∫ x, σ.density x * (w x - 1) ^ 2 ∂haar 1 := by
    congr 1 <;> apply integral_congr_ae <;> filter_upwards [hurep] with x hx <;>
      dsimp only [AbsoluteDensity.density, d] <;> rw [hx]
  change ordinaryRootH1Deviation σ ρ u ^ 2 ≤ C *
    ((∫ x, σ.density x * (G x 0) ^ 2 ∂haar 1) +
      ∫ x, σ.density x * (w x - 1) ^ 2 ∂haar 1)
  rw [← heq]
  dsimp only [C]
  rw [div_mul_eq_mul_div]
  exact (le_div_iff₀ hm2).2 (by nlinarith)

/-- The local deficit controls the actual original Haar H1 deviation, with a genuine
fixed-root norm comparison already discharged. No bounded-gradient premise is needed. -/
theorem ordinaryRoot_localHaar_deficit_stability (h : ℝ) (σ : AbsoluteDensity 1)
    (hpos : 0 < ordinaryEntropy h σ)
    (hmin : ∀ τ : AbsoluteDensity 1, 0 < ordinaryEntropy h τ → str025_quot h σ ≤ str025_quot h τ)
    (u : Torus 1 → ℝ) (hu : Continuous u) (hupos : ∀ x, 0 < u x)
    (hurep : σ.sqrt =ᵐ[haar 1] u) (p : ℝ)
    (hap : (ordinaryLSRate (ordinaryReference h)).toReal < p)
    (hPC : ENNReal.ofReal p ≤ poincareRate (densityMeasure σ)) :
    ∃ η c : ℝ, 0 < η ∧ 0 < c ∧ ∀ ρ : AbsoluteDensity 1,
      ordinaryRootH1Deviation σ ρ u ≤ η →
      c * ordinaryRootH1Deviation σ ρ u ^ 2 ≤
        (ordinaryFisher h ρ).toReal -
          2 * (ordinaryLSRate (ordinaryReference h)).toReal * (ordinaryEntropy h ρ).toReal := by
  obtain ⟨C, hC, hcompare⟩ := ordinaryRoot_originalH1_comparison σ u hu hupos hurep
  obtain ⟨η, c, hη, hc, hlocal⟩ := ordinaryRoot_local_deficit_stability
    h σ hpos hmin u hu hupos hurep p hap hPC
  refine ⟨η, c / C, hη, div_pos hc hC, fun ρ hnear => ?_⟩
  have hl := hlocal ρ hnear
  have hm := mul_le_mul_of_nonneg_left (hcompare ρ) (div_nonneg hc.le hC.le)
  have heq : (c / C) * (C *
      ((∫ x, σ.density x *
        (weakGradient (fun y => ρ.sqrt y / u y)
          (ordinaryEquality_relativeRoot_memH1 σ ρ u hu hupos hurep) x 0) ^ 2 ∂haar 1) +
        ∫ x, σ.density x * (ρ.sqrt x / u x - 1) ^ 2 ∂haar 1)) =
      c * ((∫ x, σ.density x *
        (weakGradient (fun y => ρ.sqrt y / u y)
          (ordinaryEquality_relativeRoot_memH1 σ ρ u hu hupos hurep) x 0) ^ 2 ∂haar 1) +
        ∫ x, σ.density x * (ρ.sqrt x / u x - 1) ^ 2 ∂haar 1) := by
    field_simp [hC.ne']
  rw [heq] at hm
  exact hm.trans hl

end DGPS.Examples.ThreeSpeciesCircle
