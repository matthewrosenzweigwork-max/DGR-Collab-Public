import FullLabeledLSI.Paper.HybridGroundAltG
import FullLabeledLSI.Paper.HybridRLS
import FullLabeledLSI.Infra.SpectralSetup

/-!
# Hybrid inequality (7.17), alternative route, part H: the inequality for a `C¹` representative

* `posTm_of_posIPlus`: `PosIPlus A R σ` gives `PosTm A R J (min σ 1)`.
* `polyB_ae_congr`: `polyB` only depends on the basis up to `μ`-a.e. equality.
* `hybrid_core`: the hybrid inequality (7.17) for an arbitrary basis `e` with a `C¹` representative `e'`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open scoped ENNReal ContDiff

noncomputable section

namespace SharpLSI.FL.HLA

open SharpLSI SharpLSI.FL.Gross

section posconv
variable {d : ℕ} {W : Torus d → Torus d → ℝ} {μ : Measure (Torus d)} {e : ℕ → Torus d → ℝ}
  (A : FiniteRankApprox W μ e) {R J : ℕ} (hJ : ∀ i ∈ A.s R, i < J)

include hJ in
theorem posTm_of_posIPlus {σ : ℝ} (hσ : 0 < σ) (h : PosIPlus A R σ) :
    PosTm A R J (min σ 1) := by
  intro v
  classical
  set v1 : ℕ → ℝ := fun i => if i ∈ A.s R then zext v i else 0 with hv1
  have hs := h v1 (fun i hi => by simp [v1, hi])
  have hv1z : ∀ j ∈ A.s R, v1 j = zext v j := fun j hj => by simp [v1, hj]
  have hdiag : ∀ i ∈ A.s R, ∑ j ∈ A.s R, v1 i * (if i = j then (1:ℝ) else 0) * v1 j = v1 i ^ 2 := by
    intro i hi
    rw [Finset.sum_eq_single_of_mem i hi]
    · simp; ring
    · intro j _ hji
      rw [if_neg (Ne.symm hji)]; ring
  have hsplit : ∑ i ∈ A.s R, ∑ j ∈ A.s R, v1 i * ((if i = j then (1:ℝ) else 0) + A.a R i j) * v1 j =
      ∑ i ∈ A.s R, v1 i ^ 2 + ∑ i ∈ A.s R, v1 i * ∑ j ∈ A.s R, A.a R i j * zext v j := by
    have : ∀ i ∈ A.s R, ∑ j ∈ A.s R, v1 i * ((if i = j then (1:ℝ) else 0) + A.a R i j) * v1 j =
        v1 i ^ 2 + v1 i * ∑ j ∈ A.s R, A.a R i j * zext v j := by
      intro i hi
      have e1 : ∑ j ∈ A.s R, v1 i * ((if i = j then (1:ℝ) else 0) + A.a R i j) * v1 j =
          ∑ j ∈ A.s R, v1 i * (if i = j then (1:ℝ) else 0) * v1 j +
            ∑ j ∈ A.s R, v1 i * (A.a R i j * zext v j) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [hv1z j hj]; ring
      rw [e1, hdiag i hi, ← Finset.mul_sum]
    rw [Finset.sum_congr rfl this, Finset.sum_add_distrib]
  have hP : ∑ i ∈ A.s R, v1 i ^ 2 = ∑ i : Fin J, v1 (i : ℕ) ^ 2 :=
    sum_sR_eq A (f := fun m => v1 m ^ 2) (fun m hm => by simp [v1, hm]) hJ
  have hX : ∑ i ∈ A.s R, v1 i * ∑ j ∈ A.s R, A.a R i j * zext v j = v ⬝ᵥ (Tm A R J *ᵥ v) := by
    rw [sum_sR_eq A (f := fun i => v1 i * ∑ j ∈ A.s R, A.a R i j * zext v j)
      (fun m hm => by simp [v1, hm]) hJ]
    unfold dotProduct
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [sum_inner_zext A hJ v i, dif_pos i.2]
    by_cases hi : (i : ℕ) ∈ A.s R
    · rw [hv1z _ hi]; simp [zext]
    · have : (Tm A R J *ᵥ v) i = 0 := by
        simp only [mulVec, dotProduct, Tm_apply]
        exact Finset.sum_eq_zero fun j _ => by rw [A.supp R i j (Or.inl hi)]; ring
      simp [v1, hi, this]
  have hle : ∑ i : Fin J, v1 (i : ℕ) ^ 2 ≤ v ⬝ᵥ v := by
    unfold dotProduct
    refine Finset.sum_le_sum fun i _ => ?_
    by_cases hi : (i : ℕ) ∈ A.s R
    · rw [hv1z _ hi]; simp [zext, sq]
    · simp [v1, hi]; exact mul_self_nonneg _
  have hP0 : 0 ≤ ∑ i : Fin J, v1 (i : ℕ) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  rw [hsplit, hP, hX] at hs
  have hm1 : min σ 1 ≤ σ := min_le_left _ _
  have hm2 : min σ 1 ≤ 1 := min_le_right _ _
  have hm3 : 0 < min σ 1 := lt_min hσ one_pos
  nlinarith
end posconv


section transfer
variable {d N J : ℕ}

theorem hybFlat_mp (μ : Measure (Torus d)) [IsProbabilityMeasure μ] :
    MeasurePreserving (hybFlat N J) (hybMeasure μ N J)
      ((Measure.pi fun _ : Fin N => μ).prod (gpi (N * J))) :=
  MeasurePreserving.prod (MeasurePreserving.id _) (reshape_measurePreserving N J)

theorem polyB_ae_congr (μ : Measure (Torus d)) [IsProbabilityMeasure μ] {e e' : ℕ → Torus d → ℝ}
    (hae : ∀ j, e' j =ᵐ[μ] e j) (c : (Fin N → Fin (J + 1)) → ℝ) (B : Finset (Fin N)) :
    polyB e' c B =ᵐ[hybMeasure μ N J] polyB e c B := by
  have h1 : ∀ᵐ w ∂(hybMeasure μ N J), ∀ (i : Fin N) (m : ℕ), e' m (w.1 i) = e m (w.1 i) := by
    rw [ae_all_iff]; intro i; rw [ae_all_iff]; intro m
    have hmp1 : MeasurePreserving (fun w : Config N d × (Fin N → Fin J → ℝ) => w.1 i)
        (hybMeasure μ N J) μ :=
      (measurePreserving_eval (fun _ : Fin N => μ) i).comp measurePreserving_fst
    exact hmp1.quasiMeasurePreserving.ae (hae m)
  filter_upwards [h1] with w hw
  unfold polyB hybFactor
  simp only [hw]

end transfer

section core
variable {d N J : ℕ}

/-- **The hybrid inequality (7.17)** for a basis `e` having a `C¹` representative `e'` with `e' 0 = 1`. -/
theorem hybrid_core {W : Torus d → Torus d → ℝ} {μ : Measure (Torus d)} [IsProbabilityMeasure μ]
    {e e' : ℕ → Torus d → ℝ} (A : FiniteRankApprox W μ e) {R : ℕ} {lam : ℕ → ℝ}
    (he : IsRefEigenbasis μ e lam) (hac : μ ≪ volume) (hca : volume ≪ μ)
    (hC1 : ∀ m, C1T (e' m)) (hae : ∀ j, e' j =ᵐ[μ] e j) (he0 : e' 0 = fun _ => 1)
    (hlam0 : lam 0 = 0) {a : ℝ} (ha : 0 < a) (hrla : ENNReal.ofReal a ≤ rLS μ)
    (hrl : rLS μ ≤ ENNReal.ofReal (lam 1))
    (hJ : ∀ i ∈ A.s R, i < J) {σ : ℝ} (hσ : 0 < σ) (hpos : PosTm A R J σ)
    {C : ℕ → ℕ → ℝ} (hC : IsInverseOfIPlus (A.a R) C)
    (Bs : Finset (Fin N)) (hB : Bs.card < N) (c : (Fin N → Fin (J + 1)) → ℝ) :
    0 ≤ (∑ j, (∑ i, lam (j i)) * c j ^ 2)
      + ∫ w, polyB e c Bs w ^ 2 * vR A lam R (zext (Gcoll Bs w.2)) ∂hybMeasure μ N J
      - (bRate μ lam C).toReal / 2 *
          ((ent (hybMeasure μ N J) (fun w => polyB e c Bs w ^ 2)).toReal
            + ∫ w, polyB e c Bs w ^ 2 * uR A R (zext (Gcoll Bs w.2)) ∂hybMeasure μ N J
            + Real.log (kappaR A R) * ∫ w, polyB e c Bs w ^ 2 ∂hybMeasure μ N J) := by
  set ρ : ℝ := (bRate μ lam C).toReal with hρdef
  have hρ0 : 0 ≤ ρ := ENNReal.toReal_nonneg
  have hlam0' : ∀ m : ℕ, 0 ≤ lam (m + 1) := fun m => lam_succ_nonneg he m
  have hrtop : rLS μ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hrl
  have hbtop : bRate μ lam C ≠ ⊤ := ne_top_of_le_ne_top hrtop (min_le_left _ _)
  have hρa : ρ ≤ (rLS μ).toReal := ENNReal.toReal_mono hrtop (min_le_left _ _)
  have ha0 : 0 < (rLS μ).toReal :=
    ENNReal.toReal_pos (ne_of_gt (lt_of_lt_of_le (ENNReal.ofReal_pos.2 ha) hrla)) hrtop
  have hrls : ENNReal.ofReal (rLS μ).toReal ≤ rLS μ := (ENNReal.ofReal_toReal hrtop).le
  have hPt : IsProbabilityMeasure (tPt (uT A R J Bs) (kappaR A R)) := by
    rw [tPt_eq]; exact isProbabilityMeasure_Pt hJ hσ hpos hB
  have hκ : 0 < kappaR A R := kappa_pos A hJ hσ hpos
  have hS : ((Gcm J Bs)ᵀ * Tm A R J * Gcm J Bs)ᵀ = (Gcm J Bs)ᵀ * Tm A R J * Gcm J Bs := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, Tm_transpose,
      Matrix.mul_assoc]
  have hE := energy_identity hac hca he hC1 hae he0 hlam0 Bs c
  have hflat := hyb_flat (c := c) (Y := fun j => Yf Bs j) (Xj := fun j => Xf e' Bs j)
    (u := uT A R J Bs) (κ := kappaR A R) (mu := μ) (fun j => tg_Yf Bs j) (tg_uT A hJ)
    (fun j => C1C_Xf hC1 Bs j) hκ (fun k : Fin (N * J) => lam ((flatMode k : ℕ) + 1))
    (fun k => hlam0' _) hρ0 ha0 hρa hac hrls
    (fun f hf hL2 hE' => hgl_hybrid hJ hσ hpos hB hC he hrl f hf hL2 hE')
    ((Gcm J Bs)ᵀ * Tm A R J * Gcm J Bs) hS (uT_eq hJ) hE
  -- transport to the hybrid space
  have hmp := hybFlat_mp (N := N) (J := J) μ
  have hint : ∀ f : Config N d × (Fin (N * J) → ℝ) → ℝ,
      ∫ z, f z ∂((Measure.pi fun _ : Fin N => μ).prod (gpi (N * J))) =
        ∫ w, f (hybFlat N J w) ∂hybMeasure μ N J := fun f => (hmp.integral_comp' f).symm
  have hentm : ∀ f : Config N d × (Fin (N * J) → ℝ) → ℝ,
      ent ((Measure.pi fun _ : Fin N => μ).prod (gpi (N * J))) f =
        ent (hybMeasure μ N J) (f ∘ hybFlat N J) := fun f => by
    rw [← hmp.map_eq, ent_map_equiv]
  have ha_eq : ∀ w : Config N d × (Fin N → Fin J → ℝ),
      aF c (fun j => Yf Bs j) (fun j => Xf e' Bs j) (hybFlat N J w).1 (hybFlat N J w).2 =
        polyB e' c Bs w := fun w => (polyB_eq e' c Bs w.1 w.2).symm
  have hu_eq' : ∀ w : Config N d × (Fin N → Fin J → ℝ),
      uT A R J Bs (hybFlat N J w).2 = uR A R (zext (Gcoll Bs w.2)) :=
    fun w => (uR_zext_Gcoll A Bs w.2).symm
  have hv_eq : ∀ w : Config N d × (Fin N → Fin J → ℝ),
      vflat ((Gcm J Bs)ᵀ * Tm A R J * Gcm J Bs) (fun k : Fin (N * J) => lam ((flatMode k : ℕ) + 1))
          (hybFlat N J w).2 = vR A lam R (zext (Gcoll Bs w.2)) := by
    intro w
    rw [vflat_eq_vR Bs A hJ hB]
    show vR A lam R (zext (Gc J Bs (reshape N J w.2))) = _
    rw [Gc_reshape]
  have T1 : ∫ z, aF c (fun j => Yf Bs j) (fun j => Xf e' Bs j) z.1 z.2 ^ 2 *
        vflat ((Gcm J Bs)ᵀ * Tm A R J * Gcm J Bs)
          (fun k : Fin (N * J) => lam ((flatMode k : ℕ) + 1)) z.2
        ∂((Measure.pi fun _ : Fin N => μ).prod (gpi (N * J))) =
      ∫ w, polyB e' c Bs w ^ 2 * vR A lam R (zext (Gcoll Bs w.2)) ∂hybMeasure μ N J := by
    refine (hint _).trans (integral_congr_ae (Eventually.of_forall fun w => ?_))
    simp only [ha_eq, hv_eq]
  have T2 : ∫ z, aF c (fun j => Yf Bs j) (fun j => Xf e' Bs j) z.1 z.2 ^ 2 * uT A R J Bs z.2
        ∂((Measure.pi fun _ : Fin N => μ).prod (gpi (N * J))) =
      ∫ w, polyB e' c Bs w ^ 2 * uR A R (zext (Gcoll Bs w.2)) ∂hybMeasure μ N J := by
    refine (hint _).trans (integral_congr_ae (Eventually.of_forall fun w => ?_))
    simp only [ha_eq, hu_eq']
  have T3 : ∫ z, aF c (fun j => Yf Bs j) (fun j => Xf e' Bs j) z.1 z.2 ^ 2
        ∂((Measure.pi fun _ : Fin N => μ).prod (gpi (N * J))) =
      ∫ w, polyB e' c Bs w ^ 2 ∂hybMeasure μ N J := by
    refine (hint _).trans (integral_congr_ae (Eventually.of_forall fun w => ?_))
    simp only [ha_eq]
  have T4 : ent ((Measure.pi fun _ : Fin N => μ).prod (gpi (N * J)))
        (fun z => aF c (fun j => Yf Bs j) (fun j => Xf e' Bs j) z.1 z.2 ^ 2) =
      ent (hybMeasure μ N J) (fun w => polyB e' c Bs w ^ 2) := by
    rw [hentm]
    congr 1
    funext w
    simp only [Function.comp, ha_eq]
  rw [T1, T2, T3, T4] at hflat
  -- replace `e'` by `e`
  have hpe := polyB_ae_congr (N := N) (J := J) μ hae c Bs
  have hsq : (fun w => polyB e' c Bs w ^ 2) =ᵐ[hybMeasure μ N J] fun w => polyB e c Bs w ^ 2 :=
    hpe.mono fun w hw => by simp only [hw]
  have U1 : ∫ w, polyB e' c Bs w ^ 2 * vR A lam R (zext (Gcoll Bs w.2)) ∂hybMeasure μ N J =
      ∫ w, polyB e c Bs w ^ 2 * vR A lam R (zext (Gcoll Bs w.2)) ∂hybMeasure μ N J :=
    integral_congr_ae (hpe.mono fun w hw => by simp only [hw])
  have U2 : ∫ w, polyB e' c Bs w ^ 2 * uR A R (zext (Gcoll Bs w.2)) ∂hybMeasure μ N J =
      ∫ w, polyB e c Bs w ^ 2 * uR A R (zext (Gcoll Bs w.2)) ∂hybMeasure μ N J :=
    integral_congr_ae (hpe.mono fun w hw => by simp only [hw])
  have U3 : ∫ w, polyB e' c Bs w ^ 2 ∂hybMeasure μ N J = ∫ w, polyB e c Bs w ^ 2 ∂hybMeasure μ N J :=
    integral_congr_ae hsq
  have U4 : ent (hybMeasure μ N J) (fun w => polyB e' c Bs w ^ 2) =
      ent (hybMeasure μ N J) (fun w => polyB e c Bs w ^ 2) := ent_congr_ae hsq
  rw [U1, U2, U3, U4] at hflat
  exact hflat

end core

end SharpLSI.FL.HLA

end
