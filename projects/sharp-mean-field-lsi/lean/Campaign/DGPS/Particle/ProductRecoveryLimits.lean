import DGPS.Particle.ProductForceFisher
import DGPS.Variational.HeatRecoveryConvergence
import DGPS.Particle.Rates
import DGPS.Particle.Symmetry
import DGPS.Variational.SpeciesInclusion

/-!
# Full-domain product recovery and particle upper limits (LIP023)

For every finite species family `F` we combine the fixed-time product limits (LIP021, LIP022) with
the heat recovery convergence (LIP020) through a diagonal choice of heat times `t_N → 0⁺`, so that
the smooth positive product laws `ν_N` satisfy `N⁻¹ H(ν_N | P_N) → G_θ(F)` and
`N⁻¹ I(ν_N | P_N) → D_θ(F)` together.  The likelihood roots `f_N = √(dν_N/dP_N)` lie in
`H¹(P_N)` with `4 E_N(f_N) = I(ν_N | P_N)` and `Ent_{P_N}(f_N²) = H(ν_N | P_N)`.  Hence
`limsup r_N^all ≤ r_ms` and `limsup r_N^sym ≤ r_*`, with no attainment hypotheses.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace DGPS.Lipschitz

open DGPS DGPS.Particle DGPS.Particle.ProductRecovery DGPS.Particle.ProductForceFisher
  DGPS.Particle.ProductForceVariance

section Diagonal

/-- A diagonal selection: if `a k N → L k` as `N → ∞` for each `k` and `L k → L∞` as `k → ∞`,
there is an index `κ N → ∞` slowly growing with `N` such that `a (κ N) N → L∞`. -/
theorem exists_diagonal {E : Type*} [PseudoMetricSpace E] (a : ℕ → ℕ+ → E) (L : ℕ → E)
    (Linf : E) (ha : ∀ k, Tendsto (a k) atTop (𝓝 (L k))) (hL : Tendsto L atTop (𝓝 Linf)) :
    ∃ κ : ℕ+ → ℕ, Tendsto κ atTop atTop ∧ Tendsto (fun N => a (κ N) N) atTop (𝓝 Linf) := by
  classical
  have hM : ∀ k : ℕ, ∃ M : ℕ+, ∀ N ≥ M, dist (a k N) (L k) < 1 / ((k : ℝ) + 1) := fun k =>
    Metric.tendsto_atTop.1 (ha k) _ (by positivity)
  choose M hM using hM
  let P : ℕ → ℕ+ → Prop := fun k N => ∀ j ≤ k, ((M j : ℕ+) : ℕ) ≤ (N : ℕ)
  let κ : ℕ+ → ℕ := fun N => Nat.findGreatest (fun k => P k N) (N : ℕ)
  -- for `N` large, `P K N` holds
  have hP : ∀ K : ℕ, ∃ N₀ : ℕ+, ∀ N ≥ N₀, K ≤ κ N ∧ P (κ N) N := by
    intro K
    refine ⟨⟨∑ j ∈ Finset.range (K + 1), ((M j : ℕ+) : ℕ) + K + 1, by omega⟩, fun N hN => ?_⟩
    have hN' : ∑ j ∈ Finset.range (K + 1), ((M j : ℕ+) : ℕ) + K + 1 ≤ (N : ℕ) := hN
    have hPK : P K N := fun j hj => by
      have := Finset.single_le_sum (f := fun j => ((M j : ℕ+) : ℕ)) (fun _ _ => Nat.zero_le _)
        (Finset.mem_range.2 (show j < K + 1 by omega))
      omega
    have hKN : K ≤ (N : ℕ) := by omega
    exact ⟨Nat.le_findGreatest hKN hPK, Nat.findGreatest_spec (P := fun k => P k N) hKN hPK⟩
  refine ⟨κ, ?_, ?_⟩
  · rw [tendsto_atTop]
    intro K
    obtain ⟨N₀, h⟩ := hP K
    exact eventually_atTop.2 ⟨N₀, fun N hN => (h N hN).1⟩
  · rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨K1, hK1⟩ := exists_nat_gt (2 / ε)
    obtain ⟨K2, hK2⟩ := Metric.tendsto_atTop.1 hL (ε / 2) (by positivity)
    obtain ⟨N₀, h⟩ := hP (max K1 K2)
    refine ⟨N₀, fun N hN => ?_⟩
    obtain ⟨hK, hPN⟩ := h N hN
    have hk1 : K1 ≤ κ N := (le_max_left _ _).trans hK
    have hk2 : K2 ≤ κ N := (le_max_right _ _).trans hK
    have h1 : dist (a (κ N) N) (L (κ N)) < 1 / ((κ N : ℝ) + 1) :=
      hM (κ N) N (hPN (κ N) le_rfl)
    have h2 : dist (L (κ N)) Linf < ε / 2 := hK2 _ hk2
    have h3 : 1 / ((κ N : ℝ) + 1) < ε / 2 := by
      have hk : (K1 : ℝ) ≤ κ N := by exact_mod_cast hk1
      have hpos : (0 : ℝ) < (κ N : ℝ) + 1 := by positivity
      rw [div_lt_div_iff₀ hpos (by norm_num)]
      have : 2 / ε < (κ N : ℝ) + 1 := by linarith
      rw [div_lt_iff₀ hε] at this
      linarith
    calc dist (a (κ N) N) Linf ≤ dist (a (κ N) N) (L (κ N)) + dist (L (κ N)) Linf :=
          dist_triangle _ _ _
      _ < ε := by linarith

end Diagonal


section Likelihood

variable {d : ℕ} {N : ℕ+}

/-- `f` is the likelihood root of the law `ν` against the particle Gibbs law `P_N`: `f ≥ 0`
lies in `H¹(P_N)`, `ν = f² P_N`, the relative Fisher information of `ν` is finite and equals
`4 E_N(f)`, and the Gibbs entropy `Ent_{P_N}(f²)` is the relative entropy `H(ν | P_N)`. -/
def IsLikelihoodRoot (A : InteractionData d) (N : ℕ+) (ν : Measure (ParticleSpace d N))
    (f : ParticleH1 A N) : Prop :=
  0 ≤ᵐ[particleLaw A N] f.1 ∧
    ν = (particleLaw A N).withDensity (fun x => ENNReal.ofReal (f.1 x ^ 2)) ∧
    particleRelativeFisher A N ν ≠ ⊤ ∧
    4 * particleEnergy A N f = (particleRelativeFisher A N ν).toReal ∧
    particleEntropy A N f = relativeEntropy ν (particleLaw A N)

/-- Likelihood admissibility of the product law: its root lies in `H¹(P_N)` with the stated
energy and entropy identities, given a bounded weak gradient of the Hamiltonian. -/
theorem exists_likelihoodRoot (A : InteractionData d) (G : SpeciesFamily d)
    (σ : Fin N → Fin G.count) {g : ParticleSpace d N → Fin N → Tangent d}
    (hU : IsParticleHaarWeakGradient N (particleHamiltonian A N) g)
    (hb : ∃ C : ℝ, ∀ᵐ x ∂particleHaar d N, particleTangentNormSq (g x) ≤ C) :
    ∃ f : ParticleH1 A N, f.1 = root A G σ ∧ IsLikelihoodRoot A N (productLaw G σ) f := by
  have hw := root_isWeakGradient A G σ hU hb
  have hw' : IsParticleWeakGradient A N (root A G σ) (rootGrad A G σ g) :=
    (isParticleWeakGradient_iff A N _ _).2 hw
  let f : ParticleH1 A N := ⟨root A G σ, _, hw'⟩
  have hν := productLaw_eq_root A G σ
  have hnn : 0 ≤ᵐ[particleHaar d N] root A G σ := root_nonneg_ae A G σ
  have hnnP : 0 ≤ᵐ[particleLaw A N] root A G σ :=
    (particleLaw_absolutelyContinuous A N).ae_le hnn
  have hFish := particleRelativeFisher_eq A hw hnn hν
  have hint : Integrable (fun x => particleTangentNormSq (rootGrad A G σ g x))
      (particleLaw A N) := integrable_particleTangentNormSq hw'.memLp_grad
  have hE : particleEnergy A N f = ∫ x, particleTangentNormSq (rootGrad A G σ g x)
      ∂particleLaw A N := particleEnergy_eq_of_isParticleWeakGradient f hw'
  have hE0 : 0 ≤ particleEnergy A N f := particleEnergy_nonneg f
  have hI : particleRelativeFisher A N (productLaw G σ) =
      ENNReal.ofReal (4 * particleEnergy A N f) := by
    rw [hFish, hE, ENNReal.ofReal_mul (by norm_num),
      ofReal_integral_eq_lintegral_ofReal hint
        (Filter.Eventually.of_forall fun x => Finset.sum_nonneg fun i _ => sq_nonneg _) |>.symm]
    · simp
  have hH : relativeEntropy (productLaw G σ) (particleLaw A N) =
      homogeneousEntropy (particleLaw A N) (fun x => root A G σ x ^ 2) := by
    rw [hν]
    exact relativeEntropy_withDensity (Filter.Eventually.of_forall fun x => sq_nonneg _)
      (((root_aemeasurable A G σ).pow_const 2).mono_ac (particleLaw_absolutelyContinuous A N))
  refine ⟨f, rfl, hnnP, hν, ?_, ?_, ?_⟩
  · rw [hI]; exact ENNReal.ofReal_ne_top
  · rw [hI, ENNReal.toReal_ofReal (by positivity)]
  · rw [hH]; rfl

end Likelihood


section Symmetric

variable {d : ℕ} {N : ℕ+}

/-- For a one-species family all labels carry the same factor, so the root is invariant under
every relabelling of the particles. -/
theorem root_permute (A : InteractionData d) (G : SpeciesFamily d) (hG : G.count = 1)
    (σ : Fin N → Fin G.count) (π : Equiv.Perm (Fin N)) (x : ParticleSpace d N) :
    root A G σ (permuteParticles π x) = root A G σ x := by
  have hsub : Subsingleton (Fin G.count) := by rw [hG]; exact inferInstanceAs (Subsingleton (Fin 1))
  have hamp : amp G σ (permuteParticles π x) = amp G σ x := by
    unfold amp permuteParticles
    have h : ∀ k, (G.density (σ k)).sqrt (x (π k)) = (G.density (σ (π k))).sqrt (x (π k)) :=
      fun k => by rw [Subsingleton.elim (σ k) (σ (π k))]
    simp only [h]
    exact Equiv.prod_comp π (fun k => (G.density (σ k)).sqrt (x k))
  unfold root wfun
  rw [hamp, particleHamiltonian_permute]

theorem isSymmetric_root (A : InteractionData d) (G : SpeciesFamily d) (hG : G.count = 1)
    (σ : Fin N → Fin G.count) (f : ParticleH1 A N) (hf : f.1 = root A G σ) :
    IsSymmetricParticleTest f := by
  refine IsSymmetricParticleFun.of_forall fun π x => ?_
  rw [hf]
  exact root_permute A G hG σ π x

end Symmetric

section FixedTime

variable {d : ℕ}

/-- **Fixed-time product recovery.**  For any finite family `G` (no positivity or attainment
hypotheses) there are labelled product laws `ν_N = ⊗ᵢ ρ_{σ i}` with likelihood roots
`f_N ∈ H¹(P_N)` such that `N⁻¹ H(ν_N | P_N) → G_θ` and `N⁻¹ I(ν_N | P_N) → D_θ`; for one species
the roots are symmetric. -/
theorem fixed_time_product_recovery (A : InteractionData d) (hLip : LipschitzData A)
    (b : AbsoluteDrift A) (G : SpeciesFamily d) :
    ∃ (σ : (N : ℕ+) → Fin N → Fin G.count) (f : (N : ℕ+) → ParticleH1 A N),
      (∀ N : ℕ+, IsLikelihoodRoot A N (productLaw G (σ N)) (f N)) ∧
      Tendsto (fun N : ℕ+ => ((N : ℕ) : ℝ)⁻¹ *
        (relativeEntropy (productLaw G (σ N)) (particleLaw A N)).toReal) atTop
        (𝓝 (speciesGap A G : ℝ)) ∧
      Tendsto (fun N : ℕ+ => ((N : ℕ) : ℝ)⁻¹ *
        (particleRelativeFisher A N (productLaw G (σ N))).toReal) atTop
        (𝓝 (speciesDissipation A b G).toReal) ∧
      speciesDissipation A b G ≠ ⊤ ∧
      (G.count = 1 → ∀ N : ℕ+, IsSymmetricParticleTest (f N)) := by
  obtain ⟨B, M, σ, hBm, hM, hB, hBg, hσ, ⟨gV, hgV⟩, hPart, hrest⟩ :=
    product_force_relative_fisher_limit A hLip b G
  obtain ⟨-, -, -, -, hD, hDne⟩ := hrest gV hgV
  have hroot : ∀ N : ℕ+, ∃ f : ParticleH1 A N, f.1 = root A G (σ N) ∧
      IsLikelihoodRoot A N (productLaw G (σ N)) f := by
    intro N
    have hP := hPart gV N hgV
    have hU := (isParticleWeakGradient_iff A N _ _).1 hP
    obtain ⟨C, hC⟩ := ae_bound_gV hLip hgV
    have hall : ∀ᵐ x ∂particleHaar d N, ∀ i, ‖gV (x i)‖ ≤ C := by
      rw [ae_all_iff]
      intro i
      exact (measurePreserving_eval (fun _ : Fin N => haar d) i).quasiMeasurePreserving.ae hC
    have hb : ∃ C' : ℝ, ∀ᵐ x : ParticleSpace d N ∂particleHaar d N, particleTangentNormSq
        ((fun x i => gV (x i) + (N : ℝ)⁻¹ • ∑ j ∈ Finset.univ.erase i, B (x i) (x j)) x) ≤ C' := by
      refine ⟨N * (C + M) ^ 2, ?_⟩
      filter_upwards [hall] with x hx
      unfold particleTangentNormSq
      calc ∑ i, ‖gV (x i) + (N : ℝ)⁻¹ • ∑ j ∈ Finset.univ.erase i, B (x i) (x j)‖ ^ 2
          ≤ ∑ _i : Fin N, (C + M) ^ 2 := Finset.sum_le_sum fun i _ => by
            have h := norm_score_le (a := fun _ : Fin 1 => gV) hM hB (fun _ => (0 : Fin 1)) i x
            exact pow_le_pow_left₀ (norm_nonneg _) (h.trans (add_le_add_left (hx i) _)) 2
        _ = N * (C + M) ^ 2 := by simp
    exact exists_likelihoodRoot A G (σ N) hU hb
  choose f hfroot hfL using hroot
  refine ⟨σ, f, hfL, ?_, hD, hDne, fun hG N => isSymmetric_root A G hG (σ N) (f N) (hfroot N)⟩
  simpa only [one_div] using tendsto_product_entropy A G σ hσ

end FixedTime


section HeatTimes

variable {d : ℕ}

/-- The heat-flowed species densities are smooth and strictly positive. -/
theorem heatFamily_smooth_positive (F : SpeciesFamily d) {t : ℝ} (ht : 0 < t)
    (s : Fin F.count) :
    IsSmoothPeriodic (fun x => ((heatFamily F t).density s).density x) ∧
      ∀ x, 0 < ((heatFamily F t).density s).density x := by
  obtain ⟨h1, h2, -⟩ := heat_density_facts ht (F.density s).memLp_sqrt (F.density s).mass_one
  have e : (fun x => ((heatFamily F t).density s).density x) =
      heatOp t fun w => ((F.density s).sqrt w) ^ 2 := by
    funext x
    exact heatDensity_density ht x
  refine ⟨by rw [e]; exact h1, fun x => ?_⟩
  have hx := congrFun e x
  rw [hx]
  exact h2 x

/-- **Product recovery along slowly decreasing heat times.**  For a finite family `F` there are
heat times `t_N → 0⁺`, labellings `σ_N` and likelihood roots `f_N ∈ H¹(P_N)` of the smooth positive
product laws `ν_N = ⊗ᵢ H_{t_N} ρ_{σ_N i}` such that `N⁻¹ H(ν_N | P_N) → G_θ(F)` and
`N⁻¹ I(ν_N | P_N) → D_θ(F)` simultaneously. -/
theorem product_recovery_along_heat_times (A : InteractionData d) (hLip : LipschitzData A)
    (b : AbsoluteDrift A) (F : SpeciesFamily d) :
    ∃ (t : ℕ+ → ℝ) (σ : (N : ℕ+) → Fin N → Fin F.count) (f : (N : ℕ+) → ParticleH1 A N),
      (∀ N, 0 < t N) ∧ Tendsto t atTop (𝓝[>] 0) ∧
      (∀ (N : ℕ+) (s : Fin F.count),
        IsSmoothPeriodic (fun x => ((heatFamily F (t N)).density s).density x) ∧
          ∀ x, 0 < ((heatFamily F (t N)).density s).density x) ∧
      (∀ N : ℕ+, IsLikelihoodRoot A N (productLaw (heatFamily F (t N)) (σ N)) (f N)) ∧
      Tendsto (fun N : ℕ+ => ((N : ℕ) : ℝ)⁻¹ *
        (relativeEntropy (productLaw (heatFamily F (t N)) (σ N)) (particleLaw A N)).toReal)
        atTop (𝓝 (speciesGap A F : ℝ)) ∧
      Tendsto (fun N : ℕ+ => ((N : ℕ) : ℝ)⁻¹ *
        (particleRelativeFisher A N (productLaw (heatFamily F (t N)) (σ N))).toReal)
        atTop (𝓝 (speciesDissipation A b F).toReal) ∧
      speciesDissipation A b F ≠ ⊤ ∧
      (F.count = 1 → ∀ N : ℕ+, IsSymmetricParticleTest (f N)) := by
  have hex := fun k : ℕ => fixed_time_product_recovery A hLip b
    (heatFamily F (1 / ((k : ℝ) + 1)))
  choose σk fk hL hH hI hDk hSym using hex
  obtain ⟨σ0, f0, -, -, -, hDF, -⟩ := fixed_time_product_recovery A hLip b F
  obtain ⟨-, -, -, -, -, -, -, -, hG, -, -, hD⟩ :=
    joint_entropy_energy_and_score_convergence_under_heat_recovery A hLip b F
  have htpos : ∀ k : ℕ, (0 : ℝ) < 1 / ((k : ℝ) + 1) := fun k => by positivity
  have htk : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Filter.Eventually.of_forall htpos⟩
  have hGc : Tendsto (fun k : ℕ => (speciesGap A (heatFamily F (1 / ((k : ℝ) + 1))) : ℝ))
      atTop (𝓝 (speciesGap A F : ℝ)) := NNReal.tendsto_coe.2 (hG.comp htk)
  have hDc : Tendsto (fun k : ℕ =>
      (speciesDissipation A b (heatFamily F (1 / ((k : ℝ) + 1)))).toReal) atTop
      (𝓝 (speciesDissipation A b F).toReal) :=
    (ENNReal.tendsto_toReal hDF).comp (hD.comp htk)
  obtain ⟨κ, hκ, hdiag⟩ := exists_diagonal
    (fun (k : ℕ) (N : ℕ+) => (((N : ℕ) : ℝ)⁻¹ *
        (relativeEntropy (productLaw (heatFamily F (1 / ((k : ℝ) + 1))) (σk k N))
          (particleLaw A N)).toReal,
      ((N : ℕ) : ℝ)⁻¹ *
        (particleRelativeFisher A N (productLaw (heatFamily F (1 / ((k : ℝ) + 1))) (σk k N))).toReal))
    (fun k : ℕ => ((speciesGap A (heatFamily F (1 / ((k : ℝ) + 1))) : ℝ),
      (speciesDissipation A b (heatFamily F (1 / ((k : ℝ) + 1)))).toReal))
    ((speciesGap A F : ℝ), (speciesDissipation A b F).toReal)
    (fun k => (hH k).prodMk_nhds (hI k)) (hGc.prodMk_nhds hDc)
  refine ⟨fun N => 1 / ((κ N : ℝ) + 1), fun N => σk (κ N) N, fun N => fk (κ N) N,
    fun N => htpos _, htk.comp hκ, fun N s => heatFamily_smooth_positive F (htpos _) s,
    fun N => hL (κ N) N, ?_, ?_, hDF, fun h N => hSym (κ N) h N⟩
  · exact (continuous_fst.tendsto _).comp hdiag
  · exact (continuous_snd.tendsto _).comp hdiag

end HeatTimes

section Rates

variable {d : ℕ}

/-- The particle quotient of likelihood roots with converging entropy and Fisher information
converges to the species quotient, and the entropy is eventually positive. -/
theorem tendsto_particleQuotient (A : InteractionData d) (b : AbsoluteDrift A)
    (F : SpeciesFamily d) (hG : 0 < speciesGap A F)
    (ν : (N : ℕ+) → Measure (ParticleSpace d N)) (f : (N : ℕ+) → ParticleH1 A N)
    (hL : ∀ N : ℕ+, IsLikelihoodRoot A N (ν N) (f N))
    (hH : Tendsto (fun N : ℕ+ => ((N : ℕ) : ℝ)⁻¹ *
      (relativeEntropy (ν N) (particleLaw A N)).toReal) atTop (𝓝 (speciesGap A F : ℝ)))
    (hI : Tendsto (fun N : ℕ+ => ((N : ℕ) : ℝ)⁻¹ *
      (particleRelativeFisher A N (ν N)).toReal) atTop (𝓝 (speciesDissipation A b F).toReal))
    (hD : speciesDissipation A b F ≠ ⊤) :
    (∀ᶠ N : ℕ+ in atTop, 0 < particleEntropy A N (f N)) ∧
      Tendsto (fun N : ℕ+ => particleQuotient A N (f N)) atTop (𝓝 (speciesQuotient A b F)) := by
  have hGpos : (0 : ℝ) < (speciesGap A F : ℝ) := NNReal.coe_pos.2 hG
  have hev : ∀ᶠ N : ℕ+ in atTop,
      0 < (relativeEntropy (ν N) (particleLaw A N)).toReal := by
    filter_upwards [hH.eventually (lt_mem_nhds hGpos)] with N hN
    have hNpos : (0 : ℝ) < ((N : ℕ) : ℝ)⁻¹ := inv_pos.2 (Nat.cast_pos.2 N.pos)
    exact (mul_pos_iff_of_pos_left hNpos).1 hN
  have hent : ∀ N : ℕ+, 0 < (relativeEntropy (ν N) (particleLaw A N)).toReal →
      particleEntropy A N (f N) = ENNReal.ofReal (relativeEntropy (ν N) (particleLaw A N)).toReal ∧
        0 < particleEntropy A N (f N) := by
    intro N hN
    have hne : relativeEntropy (ν N) (particleLaw A N) ≠ ⊤ := (ENNReal.toReal_pos_iff.1 hN).2.ne
    rw [(hL N).2.2.2.2, ENNReal.ofReal_toReal hne]
    exact ⟨rfl, (ENNReal.toReal_pos_iff.1 hN).1⟩
  refine ⟨hev.mono fun N hN => (hent N hN).2, ?_⟩
  have hlim : Tendsto (fun N : ℕ+ => ENNReal.ofReal
      ((((N : ℕ) : ℝ)⁻¹ * (particleRelativeFisher A N (ν N)).toReal / 2) /
        (((N : ℕ) : ℝ)⁻¹ * (relativeEntropy (ν N) (particleLaw A N)).toReal))) atTop
      (𝓝 (ENNReal.ofReal ((speciesDissipation A b F).toReal / 2 / (speciesGap A F : ℝ)))) :=
    ENNReal.tendsto_ofReal ((hI.div_const 2).div hH hGpos.ne')
  have htarget : speciesQuotient A b F =
      ENNReal.ofReal ((speciesDissipation A b F).toReal / 2 / (speciesGap A F : ℝ)) := by
    have h2G : (2 : ℝ≥0∞) * (speciesGap A F : ℝ≥0∞) =
        ENNReal.ofReal (2 * (speciesGap A F : ℝ)) := by
      rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_coe_nnreal]
      norm_num
    unfold speciesQuotient
    rw [h2G]
    conv_lhs => rw [← ENNReal.ofReal_toReal hD]
    rw [← ENNReal.ofReal_div_of_pos (by positivity)]
    congr 1
    rw [div_div]
  rw [htarget]
  refine hlim.congr' ?_
  filter_upwards [hev] with N hN
  obtain ⟨hE, hpos⟩ := hent N hN
  have hI4 := (hL N).2.2.2.1
  have hNne : ((N : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 N.ne_zero
  unfold particleQuotient
  rw [hE, ← ENNReal.ofReal_div_of_pos hN]
  congr 1
  have : 2 * particleEnergy A N (f N) = (particleRelativeFisher A N (ν N)).toReal / 2 := by
    linarith
  rw [this]
  field_simp

end Rates

section Final

variable {d : ℕ}

/-- **Full-domain product recovery and particle upper limits (LIP023).**
For every finite family `F` (no positivity of the gap, no attainment) there are smooth positive
heat-flowed product laws `ν_N` with likelihood roots `f_N ∈ H¹(P_N)`, `4 E_N(f_N) = I(ν_N | P_N)`,
`Ent_{P_N}(f_N²) = H(ν_N | P_N)`, `N⁻¹ H(ν_N | P_N) → G_θ` and `N⁻¹ I(ν_N | P_N) → D_θ`; for one
species the roots are symmetric.  Consequently `limsup r_N^all ≤ r_ms` and
`limsup r_N^sym ≤ r_*`. -/
theorem full_domain_product_recovery_and_particle_upper_limits (A : InteractionData d)
    (hLip : LipschitzData A) (b : AbsoluteDrift A) :
    (∀ F : SpeciesFamily d,
      ∃ (t : ℕ+ → ℝ) (σ : (N : ℕ+) → Fin N → Fin F.count) (f : (N : ℕ+) → ParticleH1 A N),
        (∀ N, 0 < t N) ∧ Tendsto t atTop (𝓝[>] 0) ∧
        (∀ (N : ℕ+) (s : Fin F.count),
          IsSmoothPeriodic (fun x => ((heatFamily F (t N)).density s).density x) ∧
            ∀ x, 0 < ((heatFamily F (t N)).density s).density x) ∧
        (∀ N : ℕ+, IsLikelihoodRoot A N (productLaw (heatFamily F (t N)) (σ N)) (f N)) ∧
        Tendsto (fun N : ℕ+ => ((N : ℕ) : ℝ)⁻¹ *
          (relativeEntropy (productLaw (heatFamily F (t N)) (σ N)) (particleLaw A N)).toReal)
          atTop (𝓝 (speciesGap A F : ℝ)) ∧
        Tendsto (fun N : ℕ+ => ((N : ℕ) : ℝ)⁻¹ *
          (particleRelativeFisher A N (productLaw (heatFamily F (t N)) (σ N))).toReal)
          atTop (𝓝 (speciesDissipation A b F).toReal) ∧
        speciesDissipation A b F ≠ ⊤ ∧
        (F.count = 1 → ∀ N : ℕ+, IsSymmetricParticleTest (f N))) ∧
    limsup (fun N : ℕ+ => particleRateAll A N) atTop ≤ speciesRate A b ∧
    limsup (fun N : ℕ+ => particleRateSym A N) atTop ≤ scalarRate A b := by
  refine ⟨product_recovery_along_heat_times A hLip b, ?_, ?_⟩
  · refine le_iInf fun F => ?_
    obtain ⟨t, σ, f, -, -, -, hL, hH, hI, hD, -⟩ :=
      product_recovery_along_heat_times A hLip b F.1
    obtain ⟨hpos, hq⟩ := tendsto_particleQuotient A b F.1 F.2 _ f hL hH hI hD
    calc limsup (fun N : ℕ+ => particleRateAll A N) atTop
        ≤ limsup (fun N : ℕ+ => particleQuotient A N (f N)) atTop :=
          limsup_le_limsup (hpos.mono fun N hN => particleRateAll_le_quotient A N (f N) hN)
      _ = speciesQuotient A b F.1 := hq.limsup_eq
  · refine le_iInf fun ρ => ?_
    have hG : 0 < speciesGap A (SpeciesFamily.single ρ.1) := by
      rw [speciesGap_single]; exact ρ.2
    obtain ⟨t, σ, f, -, -, -, hL, hH, hI, hD, hSym⟩ :=
      product_recovery_along_heat_times A hLip b (SpeciesFamily.single ρ.1)
    obtain ⟨hpos, hq⟩ := tendsto_particleQuotient A b _ hG _ f hL hH hI hD
    calc limsup (fun N : ℕ+ => particleRateSym A N) atTop
        ≤ limsup (fun N : ℕ+ => particleQuotient A N (f N)) atTop :=
          limsup_le_limsup (hpos.mono fun N hN =>
            particleRateSym_le_quotient A N (f N) (hSym rfl N) hN)
      _ = speciesQuotient A b (SpeciesFamily.single ρ.1) := hq.limsup_eq
      _ = scalarQuotient A b ρ.1 := speciesQuotient_single A b ρ.1

end Final

end DGPS.Lipschitz
