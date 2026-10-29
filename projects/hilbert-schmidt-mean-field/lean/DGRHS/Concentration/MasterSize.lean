import DGRHS.Concentration.MasterLimit

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace DGRHS.Concentration

/-- Exact scalar optimization of the adaptive cap and essential norm. Fixed
offsets are absorbed using n>=1; coefficients never require division by beta. -/
theorem adaptive_power_size_bound (n u α C₀ C₁ cap a : ℝ)
    (hn : 1 ≤ n) (hu : 1 ≤ u) (hα0 : 0 < α) (hα1 : α < 1)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (ha : 0 ≤ a)
    (hcap : cap ≤ C₀+C₁*(n/u)^α) (haBound : a ≤ C₀+C₁*(n/u)^α) :
    min u cap*(1+a) ≤ (1+C₀+C₁)^2*n^(2*(α/(1+α))) := by
  let p : ℝ := α/(1+α)
  let T : ℝ := n^p
  let L : ℝ := 1+C₀+C₁
  have hn' : 0 < n := lt_of_lt_of_le zero_lt_one hn
  have hu' : 0 < u := lt_of_lt_of_le zero_lt_one hu
  have hp : 0 < p := div_pos hα0 (by linarith)
  have hBalance : α*(1-p) = p := by
    dsimp [p]
    field_simp
    ring
  have hDiff : α-p*α = p := by nlinarith [hBalance]
  have hSum : α+p*(1-α) = 2*p := by nlinarith [hBalance]
  have hT : 1 ≤ T := Real.one_le_rpow hn hp.le
  have hT' : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hL : 1 ≤ L := by dsimp [L]; linarith
  have hTT : T ≤ T*T := by nlinarith [mul_nonneg (sub_nonneg.mpr hT) hT'.le]
  have hLL : L ≤ L^2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hL) (by linarith : 0 ≤ L)]
  have hSquare : T*T = n^(2*p) := by
    dsimp [T]
    rw [← Real.rpow_add hn']
    congr 1
    ring
  have hMixed : u*(n/u)^α = n^α*u^(1-α) := by
    rw [Real.div_rpow hn'.le hu'.le,Real.rpow_sub hu' 1 α,Real.rpow_one]
    ring
  have hMixedT : n^α*T^(1-α) = T*T := by
    dsimp [T]
    rw [← Real.rpow_mul hn'.le,← Real.rpow_add hn',hSum,← hSquare]
  have hRatioT : (n/T)^α = T := by
    rw [Real.div_rpow hn'.le hT'.le]
    dsimp [T]
    rw [← Real.rpow_mul hn'.le,← Real.rpow_sub hn',hDiff]
  have hTarget : L^2*(T*T) = (1+C₀+C₁)^2*n^(2*(α/(1+α))) := by
    rw [hSquare]
  rw [← hTarget]
  by_cases hSmall : u ≤ T
  · have hMixedBound : u*(n/u)^α ≤ T*T := by
      rw [hMixed,← hMixedT]
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hu'.le hSmall (by linarith)) (Real.rpow_nonneg hn'.le _)
    calc
      _ ≤ u*(1+a) := mul_le_mul_of_nonneg_right (min_le_left _ _) (by linarith)
      _ ≤ u*(1+C₀+C₁*(n/u)^α) := mul_le_mul_of_nonneg_left (by linarith) hu'.le
      _ = (1+C₀)*u+C₁*(u*(n/u)^α) := by ring
      _ ≤ (1+C₀)*T+C₁*(T*T) := add_le_add (mul_le_mul_of_nonneg_left hSmall (by linarith)) (mul_le_mul_of_nonneg_left hMixedBound hC₁)
      _ ≤ L*(T*T) := by
        have hb := mul_le_mul_of_nonneg_left hTT (by linarith : 0 ≤ 1+C₀)
        dsimp [L]
        nlinarith
      _ ≤ L^2*(T*T) := mul_le_mul_of_nonneg_right hLL (mul_nonneg hT'.le hT'.le)
  · have hBig : T ≤ u := le_of_not_ge hSmall
    have hRatio : (n/u)^α ≤ T := by
      rw [← hRatioT]
      apply Real.rpow_le_rpow (div_nonneg hn'.le hu'.le) _ hα0.le
      apply (div_le_div_iff₀ hu' hT').2
      exact mul_le_mul_of_nonneg_left hBig hn'.le
    have hc : min u cap ≤ L*T := by
      have hh := mul_le_mul_of_nonneg_left hRatio hC₁
      have ho := mul_le_mul_of_nonneg_left hT hC₀
      dsimp [L]
      nlinarith [min_le_right u cap]
    have ha' : 1+a ≤ L*T := by
      have hh := mul_le_mul_of_nonneg_left hRatio hC₁
      have ho := mul_le_mul_of_nonneg_left hT hC₀
      dsimp [L]
      nlinarith
    calc
      _ ≤ (L*T)*(L*T) := mul_le_mul hc ha' (by linarith) (mul_nonneg (by linarith) hT'.le)
      _ = L^2*(T*T) := by ring

/-- Actual finiteness and upper bound of the master size supremum from the
per-height physical cap and essential norm estimates. No size_finite premise. -/
theorem masterCutoffSize_le_adaptive_power {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (q : ℝ → Ω × Ω → ℝ) (cap : ℝ → ℝ)
    (n u₀ α C₀ C₁ : ℝ) (hn : 1 ≤ n) (hu₀ : 1 ≤ u₀)
    (hα0 : 0 < α) (hα1 : α < 1) (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hcap : ∀ u, u₀ ≤ u → cap u ≤ C₀+C₁*(n/u)^α)
    (ha : ∀ u, u₀ ≤ u → (eLpNormEssSup (q u) (μ.prod μ)).toReal ≤ C₀+C₁*(n/u)^α) :
    BddAbove (masterCutoffValues μ q cap u₀) ∧
      masterCutoffSize μ q cap u₀ ≤ (1+C₀+C₁)^2*n^(2*(α/(1+α))) := by
  have hb : ∀ s ∈ masterCutoffValues μ q cap u₀, s ≤ (1+C₀+C₁)^2*n^(2*(α/(1+α))) := by
    intro s hs
    obtain ⟨u,hu,rfl⟩ := hs
    exact adaptive_power_size_bound n u α C₀ C₁ (cap u) ((eLpNormEssSup (q u) (μ.prod μ)).toReal)
      hn (hu₀.trans hu) hα0 hα1 hC₀ hC₁ ENNReal.toReal_nonneg (hcap u hu) (ha u hu)
  refine ⟨⟨_,hb⟩,?_⟩
  apply csSup_le _ hb
  exact ⟨_,u₀,le_rfl,rfl⟩

#print axioms DGRHS.Concentration.adaptive_power_size_bound
#print axioms DGRHS.Concentration.masterCutoffSize_le_adaptive_power
#check @DGRHS.Concentration.masterCutoffSize_le_adaptive_power
end DGRHS.Concentration
