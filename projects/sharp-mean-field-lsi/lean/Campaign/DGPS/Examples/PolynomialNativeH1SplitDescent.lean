import DGPS.Examples.ThreeSpeciesCircle.H1SplitQuotientAlgebra

/-! Binary variational descent for EVERY normalized native weighted-H1 test.
The model is arbitrary. One-dimensional H1 embedding selects a continuous AE
representative with the SAME chosen gradient; no elliptic regularity or smooth
eigenfunction premise is used. The strict Rayleigh margin remains factual input. -/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal
open DGPS.Examples.ThreeSpeciesCircle

namespace DGPS.Examples.PolynomialSpecies

private theorem binaryH1_weak {g : Torus 1 → ℝ} {G : Torus 1 → Tangent 1}
    (hg : IsWeakGradient g G) :
    ∀ s : Fin 2, IsWeakGradient (![g, fun x => -g x] s) (![G, fun x => -G x] s) := by
  intro s
  fin_cases s
  · exact hg
  · change IsWeakGradient (fun x => -g x) (fun x => -G x)
    refine ⟨hg.memLp.neg, hg.memLp_grad.neg, ?_⟩
    intro φ hφ j
    simp only [Pi.neg_apply, neg_mul, integral_neg, neg_neg]
    rw [hg.ibp φ hφ j]
    have hf : (fun x : Torus 1 => (-G x) j * φ x) = fun x => -(G x j * φ x) := by
      funext x
      simp
    simp only [hf, integral_neg, neg_neg]

private theorem binaryH1_continuous {g : Torus 1 → ℝ} (hc : Continuous g) :
    ∀ s : Fin 2, Continuous (![g, fun x => -g x] s) := by
  intro s
  fin_cases s
  · exact hc
  · exact hc.neg

private theorem binaryH1_mean (σ : AbsoluteDensity 1) {g : Torus 1 → ℝ}
    (hm : ∫ x, g x ∂(densityMeasure σ : Measure (Torus 1)) = 0) :
    ∀ s : Fin 2, ∫ x, (![g, fun x => -g x] s) x
      ∂(densityMeasure σ : Measure (Torus 1)) = 0 := by
  intro s
  fin_cases s
  · exact hm
  · change (∫ x, -g x ∂(densityMeasure σ : Measure (Torus 1))) = 0
    rw [integral_neg, hm, neg_zero]

/-- The genuine equal-weight finite H1 split, with both original weak gradients. -/
def nativeH1BinarySplit (σ : AbsoluteDensity 1) (g : Torus 1 → ℝ)
    (G : Torus 1 → Tangent 1) (hg : IsWeakGradient g G) (hc : Continuous g)
    (hm : ∫ x, g x ∂(densityMeasure σ : Measure (Torus 1)) = 0)
    (t : ℝ) (hp : ∀ (s : Fin 2) x, 0 < 1 + t * (![g, fun x => -g x] s) x) : SpeciesFamily 1 :=
  finiteH1Split σ (2 : ℕ+) (fun _ => (1 / 2 : ℝ)) (fun _ => by norm_num)
    (by norm_num [Fin.sum_univ_two]) ![g, fun x => -g x] ![G, fun x => -G x]
    (binaryH1_weak hg) (binaryH1_continuous hc) (binaryH1_mean σ hm) t hp

/-- A native variational margin gives strict descent for every sufficiently
small NONZERO parameter of either sign, on the original full weighted H1 domain.
The barycenter is unchanged; the gap has its exact positive entropy increment. -/
theorem nativeH1BinarySplit_strict_improvement (A : InteractionData 1) (b : AbsoluteDrift A)
    (σ : AbsoluteDensity 1) (u : Torus 1 → ℝ) (hu : Continuous u) (hup : ∀ x, 0 < u x)
    (hurep : σ.sqrt =ᵐ[haar 1] u) (hbase : 0 < scalarGap A σ)
    (hD : scalarDissipation A b σ ≠ ⊤) (f : WeakH1Test (densityMeasure σ))
    (hfmean : ∫ x, f.fn x ∂(densityMeasure σ : Measure (Torus 1)) = 0)
    (hfmass : ∫ x, f.fn x ^ 2 ∂(densityMeasure σ : Measure (Torus 1)) = 1)
    (hmargin : (∫ x, ‖f.grad x‖ ^ 2 ∂(densityMeasure σ : Measure (Torus 1))) <
      (scalarQuotient A b σ).toReal) :
    ∃ (g : Torus 1 → ℝ) (hc : Continuous g) (hg : IsWeakGradient g f.grad)
        (hm : ∫ x, g x ∂(densityMeasure σ : Measure (Torus 1)) = 0),
      g =ᵐ[haar 1] f.fn ∧ g =ᵐ[(densityMeasure σ : Measure (Torus 1))] f.fn ∧
      ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < |t| → |t| < δ →
        ∃ hp : ∀ (s : Fin 2) x, 0 < 1 + t * (![g, fun x => -g x] s) x,
          let F := nativeH1BinarySplit σ g f.grad hg hc hm t hp
          densityMeasure (barycenter F) = densityMeasure σ ∧
          (speciesGap A F : ℝ) = (scalarGap A σ : ℝ) +
            (1 / 2 : ℝ) * ((∫ x, InformationTheory.klFun (1 + t * g x)
              ∂(densityMeasure σ : Measure (Torus 1))) +
              ∫ x, InformationTheory.klFun (1 + t * (-g x))
                ∂(densityMeasure σ : Measure (Torus 1))) ∧
          0 < speciesGap A F ∧ speciesDissipation A b F ≠ ⊤ ∧
            speciesQuotient A b F < scalarQuotient A b σ := by
  obtain ⟨g, hc, hgae, hgμ, hg⟩ := nativeTangent_continuous_rep σ u hu hup hurep f
  have hm : ∫ x, g x ∂(densityMeasure σ : Measure (Torus 1)) = 0 :=
    (integral_congr_ae hgμ).trans hfmean
  have hmass : ∫ x, g x ^ 2 ∂(densityMeasure σ : Measure (Torus 1)) = 1 :=
    (integral_congr_ae (hgμ.mono fun x hx => congrArg (fun z : ℝ => z ^ 2) hx)).trans hfmass
  let q : ℕ+ := 2
  let θ : Fin q → ℝ := fun _ => 1 / 2
  let gs : Fin q → Torus 1 → ℝ := ![g, fun x => -g x]
  let Gs : Fin q → Torus 1 → Tangent 1 := ![f.grad, fun x => -f.grad x]
  have hθ : ∀ s, 0 < θ s := fun _ => by norm_num [θ]
  have hθsum : ∑ s, θ s = 1 := by norm_num [θ, q, Fin.sum_univ_two]
  have hgs : ∀ s, IsWeakGradient (gs s) (Gs s) := binaryH1_weak hg
  have hgcs : ∀ s, Continuous (gs s) := binaryH1_continuous hc
  have hms : ∀ s, ∫ x, gs s x ∂(densityMeasure σ : Measure (Torus 1)) = 0 := binaryH1_mean σ hm
  have hcancel : ∀ x, ∑ s, θ s * gs s x = 0 := by
    intro x
    change (∑ s : Fin 2, (1 / 2 : ℝ) * (![g, fun x => -g x] s) x) = 0
    rw [Fin.sum_univ_two]
    change (1 / 2 : ℝ) * g x + (1 / 2 : ℝ) * (-g x) = 0
    ring
  have hGs : ∀ s, MemLp (Gs s) 2 (densityMeasure σ : Measure (Torus 1)) := by
    intro s
    fin_cases s
    · exact f.isWeak.memLp_grad
    · exact f.isWeak.memLp_grad.neg
  let Gb : ℝ := scalarGap A σ
  let R := (scalarDissipation A b σ).toReal / (2 * Gb)
  let E := ∫ x, ‖f.grad x‖ ^ 2 ∂(densityMeasure σ : Measure (Torus 1))
  let H := fun t : ℝ => ∑ s, θ s *
    ∫ x, InformationTheory.klFun (1 + t * gs s x) ∂(densityMeasure σ : Measure (Torus 1))
  let I := fun t : ℝ => ∑ s, θ s *
    ∫ x, ‖Gs s x‖ ^ 2 / (1 + t * gs s x) ∂(densityMeasure σ : Measure (Torus 1))
  have hGb : 0 < Gb := hbase
  have hRval : (scalarQuotient A b σ).toReal = R := by
    simp only [scalarQuotient, ENNReal.toReal_div, ENNReal.toReal_mul,
      ENNReal.toReal_ofNat, ENNReal.coe_toReal]
    rfl
  have hER : E < R := by simpa only [hRval] using hmargin
  have hBsum : (∑ s, θ s * ∫ x, gs s x ^ 2 ∂(densityMeasure σ : Measure (Torus 1))) = 1 := by
    have hn (s : Fin q) : (∫ x, gs s x ^ 2 ∂(densityMeasure σ : Measure (Torus 1))) = 1 := by
      fin_cases s
      · exact hmass
      · change (∫ x, (-g x) ^ 2 ∂(densityMeasure σ : Measure (Torus 1))) = 1
        simpa only [neg_sq] using hmass
    simp only [hn, mul_one, hθsum]
  have hEsum : (∑ s, θ s * ∫ x, ‖Gs s x‖ ^ 2 ∂(densityMeasure σ : Measure (Torus 1))) = E := by
    change (∑ s : Fin 2, (1 / 2 : ℝ) * ∫ x, ‖(![f.grad, fun x => -f.grad x] s) x‖ ^ 2
      ∂(densityMeasure σ : Measure (Torus 1))) = E
    rw [Fin.sum_univ_two]
    change (1 / 2 : ℝ) * E + (1 / 2 : ℝ) *
      (∫ x, ‖-f.grad x‖ ^ 2 ∂(densityMeasure σ : Measure (Torus 1))) = E
    simp only [norm_neg]
    ring
  have hHlim : Tendsto (fun t => H t / t ^ 2) (𝓝[{t : ℝ | t ≠ 0}] 0) (𝓝 (1 / 2 : ℝ)) := by
    have ht := tendsto_finsetSum Finset.univ fun s _ =>
      (relativeSplit_entropy_coefficient_tendsto (densityMeasure σ) (gs s) (hgcs s)).const_mul (θ s)
    have he : (∑ s, θ s * ((∫ x, gs s x ^ 2 ∂(densityMeasure σ : Measure (Torus 1))) / 2)) =
        (1 / 2 : ℝ) := by
      calc
        _ = (∑ s, θ s * ∫ x, gs s x ^ 2 ∂(densityMeasure σ : Measure (Torus 1))) / 2 := by
          rw [Finset.sum_div]
          apply Finset.sum_congr rfl
          intro s _
          ring
        _ = _ := by rw [hBsum]
    convert ht using 1
    · funext t
      dsimp only [H]
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro s _
      ring
    · exact congrArg (fun x : ℝ => 𝓝 x) he.symm
  have hIlim : Tendsto I (𝓝[{t : ℝ | t ≠ 0}] 0) (𝓝 E) := by
    have ht := tendsto_finsetSum Finset.univ fun s _ =>
      ((relativeSplit_information_coefficient_tendsto (densityMeasure σ) (gs s) (hgcs s)
        (Gs s) (hGs s)).mono_left (show 𝓝[{t : ℝ | t ≠ 0}] (0 : ℝ) ≤ 𝓝 (0 : ℝ) from nhdsWithin_le_nhds)).const_mul (θ s)
    simpa only [hEsum] using ht
  have hdiff := hIlim.sub (hHlim.const_mul (2 * R))
  have hlimit : E - 2 * R * (1 / 2 : ℝ) = E - R := by ring
  rw [hlimit] at hdiff
  have hgood : ∀ᶠ t : ℝ in 𝓝[{t : ℝ | t ≠ 0}] 0,
      (∀ s x, 0 < 1 + t * gs s x) ∧ I t - 2 * R * (H t / t ^ 2) < 0 := by
    filter_upwards [(finiteH1Split_eventually_positive q gs hgcs).filter_mono nhdsWithin_le_nhds,
      hdiff.eventually (gt_mem_nhds (sub_neg.mpr hER))] with t hp ht
    exact ⟨hp, ht⟩
  obtain ⟨δ, hδ, hδprop⟩ := Metric.mem_nhdsWithin_iff.1 hgood
  refine ⟨g, hc, hg, hm, hgae, hgμ, δ, hδ, fun t ht0 htδ => ?_⟩
  have htn : t ≠ 0 := abs_pos.mp ht0
  obtain ⟨hp, ht⟩ := hδprop ⟨by simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using htδ, htn⟩
  refine ⟨hp, ?_⟩
  let F := finiteH1Split σ q θ hθ hθsum gs Gs hgs hgcs hms t hp
  have hgap : (speciesGap A F : ℝ) = Gb + H t :=
    finiteH1Split_gap σ q θ hθ hθsum gs Gs hgs hgcs hms hcancel t hp A
  have hHpos : 0 ≤ H t := Finset.sum_nonneg fun s _ => mul_nonneg (hθ s).le
    (integral_nonneg fun x => InformationTheory.klFun_nonneg (hp s x).le)
  have hGt : 0 < speciesGap A F := by
    change (0 : ℝ) < (speciesGap A F : ℝ)
    rw [hgap]
    exact add_pos_of_pos_of_nonneg hGb hHpos
  obtain ⟨hDt, hDreal⟩ := finiteH1Split_dissipation_real σ q θ hθ hθsum gs Gs hgs hgcs hms
    hcancel hGs t hp A b hD
  have hDb : (scalarDissipation A b σ).toReal = 2 * R * Gb := by
    dsimp only [R]
    field_simp [hGb.ne']
    <;> ring
  have hcross : (speciesDissipation A b F).toReal < 2 * R * (speciesGap A F : ℝ) := by
    have hs : 0 < t ^ 2 := sq_pos_of_ne_zero htn
    have htMul := mul_neg_of_neg_of_pos ht hs
    have heq : (I t - 2 * R * (H t / t ^ 2)) * t ^ 2 = t ^ 2 * I t - 2 * R * H t := by
      field_simp [htn]
      <;> ring
    rw [heq] at htMul
    change (speciesDissipation A b F).toReal = (scalarDissipation A b σ).toReal + t ^ 2 * I t at hDreal
    rw [hDreal, hgap, hDb]
    nlinarith only [htMul]
  have hQfin : scalarQuotient A b σ ≠ ⊤ := by
    unfold scalarQuotient
    exact ENNReal.div_ne_top hD (mul_ne_zero (by norm_num) (by exact_mod_cast hbase.ne'))
  have hFfin : speciesQuotient A b F ≠ ⊤ := by
    unfold speciesQuotient
    exact ENNReal.div_ne_top hDt (mul_ne_zero (by norm_num) (by exact_mod_cast hGt.ne'))
  have hQlt : speciesQuotient A b F < scalarQuotient A b σ := by
    apply (ENNReal.toReal_lt_toReal hFfin hQfin).1
    rw [hRval]
    unfold speciesQuotient
    rw [ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_ofNat, ENNReal.coe_toReal]
    apply (div_lt_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) (show (0 : ℝ) < (speciesGap A F : ℝ) from hGt))).2
    nlinarith only [hcross]
  have hgapExplicit : (speciesGap A F : ℝ) = (scalarGap A σ : ℝ) +
      (1 / 2 : ℝ) * ((∫ x, InformationTheory.klFun (1 + t * g x) ∂(densityMeasure σ : Measure (Torus 1))) +
        ∫ x, InformationTheory.klFun (1 + t * (-g x)) ∂(densityMeasure σ : Measure (Torus 1))) := by
    rw [hgap]
    change Gb + (∑ s : Fin 2, (1 / 2 : ℝ) * ∫ x,
      InformationTheory.klFun (1 + t * (![g, fun x => -g x] s) x)
        ∂(densityMeasure σ : Measure (Torus 1))) = _
    rw [Fin.sum_univ_two]
    change Gb + ((1 / 2 : ℝ) * (∫ x, InformationTheory.klFun (1 + t * g x)
      ∂(densityMeasure σ : Measure (Torus 1))) +
      (1 / 2 : ℝ) * (∫ x, InformationTheory.klFun (1 + t * (-g x))
      ∂(densityMeasure σ : Measure (Torus 1)))) = _
    dsimp only [Gb]
    ring
  exact ⟨finiteH1Split_barycenter σ q θ hθ hθsum gs Gs hgs hgcs hms hcancel t hp,
    hgapExplicit, hGt, hDt, hQlt⟩

/-- Every normalized original-H1 Poincare attainer with the factual strict
Poincare/base-quotient margin has the same genuine two-sided binary descent.
The actual model's margin is NOT asserted by this conditional support. -/
theorem nativeH1BinarySplit_poincare_attainer_descent (A : InteractionData 1) (b : AbsoluteDrift A)
    (σ : AbsoluteDensity 1) (u : Torus 1 → ℝ) (hu : Continuous u) (hup : ∀ x, 0 < u x)
    (hurep : σ.sqrt =ᵐ[haar 1] u) (hbase : 0 < scalarGap A σ)
    (hD : scalarDissipation A b σ ≠ ⊤) (f : WeakH1Test (densityMeasure σ))
    (hfmean : ∫ x, f.fn x ∂(densityMeasure σ : Measure (Torus 1)) = 0)
    (hfmass : ∫ x, f.fn x ^ 2 ∂(densityMeasure σ : Measure (Torus 1)) = 1)
    (henergy : (∫ x, ‖f.grad x‖ ^ 2 ∂(densityMeasure σ : Measure (Torus 1))) =
      (poincareRate (densityMeasure σ)).toReal)
    (hPC : poincareRate (densityMeasure σ) < scalarQuotient A b σ) :
    ∃ (g : Torus 1 → ℝ) (hc : Continuous g) (hg : IsWeakGradient g f.grad)
        (hm : ∫ x, g x ∂(densityMeasure σ : Measure (Torus 1)) = 0),
      g =ᵐ[haar 1] f.fn ∧ g =ᵐ[(densityMeasure σ : Measure (Torus 1))] f.fn ∧
      ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < |t| → |t| < δ →
        ∃ hp : ∀ (s : Fin 2) x, 0 < 1 + t * (![g, fun x => -g x] s) x,
          let F := nativeH1BinarySplit σ g f.grad hg hc hm t hp
          densityMeasure (barycenter F) = densityMeasure σ ∧
          (speciesGap A F : ℝ) = (scalarGap A σ : ℝ) +
            (1 / 2 : ℝ) * ((∫ x, InformationTheory.klFun (1 + t * g x)
              ∂(densityMeasure σ : Measure (Torus 1))) +
              ∫ x, InformationTheory.klFun (1 + t * (-g x))
                ∂(densityMeasure σ : Measure (Torus 1))) ∧
          0 < speciesGap A F ∧ speciesDissipation A b F ≠ ⊤ ∧
            speciesQuotient A b F < scalarQuotient A b σ := by
  have hQfin : scalarQuotient A b σ ≠ ⊤ := by
    unfold scalarQuotient
    exact ENNReal.div_ne_top hD (mul_ne_zero (by norm_num) (by exact_mod_cast hbase.ne'))
  have hPCfin : poincareRate (densityMeasure σ) ≠ ⊤ := (hPC.trans_le le_top).ne
  have hmargin : (∫ x, ‖f.grad x‖ ^ 2 ∂(densityMeasure σ : Measure (Torus 1))) <
      (scalarQuotient A b σ).toReal :=
    henergy.trans_lt ((ENNReal.toReal_lt_toReal hPCfin hQfin).2 hPC)
  exact nativeH1BinarySplit_strict_improvement A b σ u hu hup hurep hbase hD f hfmean hfmass hmargin

/-- Every actual split label has a positive continuous H1 representative of
its square root. The original stored root is identified ONLY almost everywhere. -/
theorem nativeH1BinarySplit_positive_representatives
    (σ : AbsoluteDensity 1) (u : Torus 1 → ℝ) (hu : Continuous u) (hup : ∀ x, 0 < u x)
    (hurep : σ.sqrt =ᵐ[haar 1] u) (g : Torus 1 → ℝ)
    (G : Torus 1 → Tangent 1) (hg : IsWeakGradient g G) (hc : Continuous g)
    (hm : ∫ x, g x ∂(densityMeasure σ : Measure (Torus 1)) = 0)
    (t : ℝ) (hp : ∀ (s : Fin 2) x, 0 < 1 + t * (![g, fun x => -g x] s) x) :
    let F := nativeH1BinarySplit σ g G hg hc hm t hp
    ∀ s : Fin F.count, ∃ v : Torus 1 → ℝ, Continuous v ∧ (∀ x, 0 < v x) ∧
      (F.density s).sqrt =ᵐ[haar 1] v ∧ MemH1 v := by
  dsimp only
  intro s
  obtain ⟨v, hvc, hvrep, hvH1, m, hmpos, hvlower⟩ := relativeH1SplitDensity_positive_rep
    σ u hu hup hurep (![g, fun x => -g x] s) (![G, fun x => -G x] s)
    (binaryH1_weak hg s) (binaryH1_continuous hc s) (binaryH1_mean σ hm s) t (hp s)
  exact ⟨v, hvc, fun x => hmpos.trans_le (hvlower x), hvrep, hvH1⟩

end DGPS.Examples.PolynomialSpecies
