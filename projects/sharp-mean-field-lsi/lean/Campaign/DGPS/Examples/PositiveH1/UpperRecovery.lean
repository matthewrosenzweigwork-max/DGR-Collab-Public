import Mathlib
import DGPS.Examples.PositiveH1.FiniteFamilyRecovery
import DGPS.Examples.PositiveH1.ConditionalForceVariance
import DGPS.Variational.SpeciesInclusion
import DGPS.Particle.Rates

/-!
# General finite family upper recovery (H1019)
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace DGPS.Examples.PositiveH1.Recovery

open DGPS DGPS.Particle DGPS.Examples.PositiveH1.Particle DGPS.Examples.PositiveH1.Fourier
  DGPS.Examples.PositiveH1.Model DGPS.Examples.PositiveH1.Nonlinear

/-! ### Labelings with prescribed asymptotic fractions -/

theorem exists_counts (n : ℕ+) (θ : Fin n → ℝ) (hθ : ∀ s, 0 ≤ θ s) (hsum : ∑ s, θ s = 1)
    (N : ℕ) : ∃ c : Fin n → ℕ, ∑ s, c s = N ∧ ∀ s, |(c s : ℝ) - N * θ s| ≤ n := by
  have hn : 0 < (n : ℕ) := n.pos
  set s0 : Fin n := ⟨0, hn⟩
  set f : Fin n → ℕ := fun s => ⌊(N : ℝ) * θ s⌋₊ with hf
  have hfle : ∀ s, (f s : ℝ) ≤ N * θ s := fun s =>
    Nat.floor_le (mul_nonneg (Nat.cast_nonneg _) (hθ s))
  have hflt : ∀ s, (N : ℝ) * θ s < f s + 1 := fun s => Nat.lt_floor_add_one _
  have hsumle : ((∑ s, f s : ℕ) : ℝ) ≤ N := by
    push_cast
    calc ∑ s, (f s : ℝ) ≤ ∑ s, (N : ℝ) * θ s := Finset.sum_le_sum fun s _ => hfle s
      _ = N := by rw [← Finset.mul_sum, hsum, mul_one]
  have hsumle' : ∑ s, f s ≤ N := by exact_mod_cast hsumle
  refine ⟨fun s => f s + if s = s0 then N - ∑ t, f t else 0, ?_, ?_⟩
  · rw [Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    omega
  · intro s
    have hdef : (N : ℝ) - ∑ t, (f t : ℝ) < n := by
      have : (N : ℝ) = ∑ t, (N : ℝ) * θ t := by rw [← Finset.mul_sum, hsum, mul_one]
      rw [this, ← Finset.sum_sub_distrib]
      calc ∑ t, ((N : ℝ) * θ t - f t) < ∑ _t : Fin n, (1 : ℝ) :=
            Finset.sum_lt_sum_of_nonempty ⟨s0, Finset.mem_univ _⟩ fun t _ => by
              linarith [hflt t]
        _ = n := by simp
    have hsumle'' : ∑ t, (f t : ℝ) ≤ N := by exact_mod_cast hsumle'
    have hdef0 : 0 ≤ (N : ℝ) - ∑ t, (f t : ℝ) := by linarith
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    by_cases hs : s = s0
    · simp only [hs, ite_true]
      push_cast [Nat.cast_sub hsumle']
      rw [abs_le]
      constructor <;> linarith [hfle s0, hflt s0]
    · simp only [hs, ite_false, add_zero]
      rw [abs_le]
      constructor <;> linarith [hfle s, hflt s]

theorem exists_labeling (n : ℕ+) (θ : Fin n → ℝ) (hθ : ∀ s, 0 ≤ θ s) (hsum : ∑ s, θ s = 1) :
    ∃ σ : ∀ N : ℕ+, Fin N → Fin n,
      ∀ s, Tendsto (fun N : ℕ+ => frac (σ N) s) atTop (𝓝 (θ s)) := by
  have key : ∀ N : ℕ+, ∃ σ : Fin N → Fin n, ∀ s, |frac σ s - θ s| ≤ n / (N : ℝ) := by
    intro N
    obtain ⟨c, hc, hcb⟩ := exists_counts n θ hθ hsum N
    have hcard : Fintype.card (Fin N) = Fintype.card (Σ i : Fin n, Fin (c i)) := by
      simp [Fintype.card_sigma, hc]
    obtain ⟨E⟩ := Fintype.card_eq.mp hcard
    refine ⟨fun i => (E i).1, fun s => ?_⟩
    have hcnt : cnt (fun i => (E i).1) s = c s := by
      unfold cnt
      rw [Finset.card_filter]
      push_cast
      refine (Equiv.sum_comp E
        (fun p : Σ i : Fin n, Fin (c i) => if p.1 = s then (1 : ℝ) else 0)).trans ?_
      rw [Fintype.sum_sigma]
      rw [Finset.sum_eq_single s (fun t _ ht => by simp [ht]) (by simp)]
      simp
    have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
    unfold frac
    rw [hcnt, show (c s : ℝ) / N - θ s = ((c s : ℝ) - N * θ s) / N by field_simp, abs_div,
      abs_of_pos hN]
    exact div_le_div_of_nonneg_right (hcb s) hN.le
  choose σ hσ using key
  refine ⟨σ, fun s => ?_⟩
  have hN : Tendsto (fun N : ℕ+ => ((N : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp tendsto_PNat_val_atTop_atTop
  have h0 : Tendsto (fun N : ℕ+ => (n : ℝ) / N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hN
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero (fun N => norm_nonneg _) (fun N => hσ N s) h0

/-! ### Entropy of the root of a product law -/

theorem particleEntropy_root (κ : ℝ) (N : ℕ+) (r : Fin N → AbsoluteDensity 1)
    (h : MemParticleH1 (kernelData κ) N (root κ r)) :
    particleEntropy (kernelData κ) N ⟨root κ r, h⟩ =
      relativeEntropy (labeledProduct r) (particleLaw (kernelData κ) N) := by
  obtain ⟨-, -, hν, hrn, -⟩ := rough_product_admissibility κ N r
  have hac : labeledProduct r ≪ particleLaw (kernelData κ) N := by
    rw [hν]; exact withDensity_absolutelyContinuous _ _
  rw [relativeEntropy_of_absolutelyContinuous hac]
  exact homogeneousEntropy_congr_ae hrn

/-- Bounded densities: a common a.e. upper bound for the finitely many species densities. -/
theorem exists_common_bound (F : SpeciesFamily 1) :
    ∃ B : ℝ, ∀ s, ∀ᵐ y ∂haar 1, (F.density s).density y ≤ B := by
  choose b hb using fun s => cfv_exists_bound (F.density s)
  refine ⟨∑ s, |b s|, fun s => ?_⟩
  filter_upwards [hb s] with y hy
  calc (F.density s).density y ≤ b s := hy
    _ ≤ |b s| := le_abs_self _
    _ ≤ ∑ t, |b t| := Finset.single_le_sum (f := fun t => |b t|) (fun t _ => abs_nonneg _)
        (Finset.mem_univ s)

/-- The core convergence at the level of `kernelData kappa`. -/
theorem core_tendsto (F : SpeciesFamily 1) (hG : 0 < speciesGap positiveH1 F)
    (σ : ∀ N : ℕ+, Fin N → Fin F.count)
    (hσ : ∀ s, Tendsto (fun N : ℕ+ => frac (σ N) s) atTop (𝓝 (F.weight s))) :
    (∀ᶠ N : ℕ+ in atTop, 0 < particleEntropy (kernelData kappa) N
      ⟨root kappa fun i => F.density (σ N i),
        (finite_species_rough_product_admissibility kappa N (σ N) F.density).1⟩) ∧
    Tendsto (fun N : ℕ+ => particleQuotient (kernelData kappa) N
      ⟨root kappa fun i => F.density (σ N i),
        (finite_species_rough_product_admissibility kappa N (σ N) F.density).1⟩) atTop
      (𝓝 (speciesQuotient positiveH1 positiveH1Drift F)) := by
  obtain ⟨B, hB⟩ := exists_common_bound F
  have hkap : (0 : ℝ) ≤ kappa := by unfold kappa; norm_num
  obtain ⟨-, hlim, hgap⟩ := finite_family_exact_entropy_recovery hkap F
  have hH := (hlim σ hσ)
  rw [hgap rfl] at hH
  obtain ⟨hDfin, hD⟩ := (finite_family_conditional_force_variance kappa F hB).2 rfl
  have hD' := hD σ hσ
  have hGr : (0 : ℝ) < (speciesGap positiveH1 F : ℝ) := by exact_mod_cast hG
  set Gr : ℝ := (speciesGap positiveH1 F : ℝ) with hGrdef
  set Dr : ℝ := (speciesDissipation positiveH1 positiveH1Drift F).toReal with hDrdef
  have hHpos : ∀ᶠ N : ℕ+ in atTop,
      0 < (relativeEntropy (labeledProduct fun i => F.density (σ N i))
          (particleLaw (kernelData kappa) N)).toReal := by
    filter_upwards [hH.eventually (lt_mem_nhds hGr)] with N hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast N.pos
    by_contra hle
    push Not at hle
    have := div_nonpos_of_nonpos_of_nonneg hle hN0.le
    linarith
  have hfin : ∀ N : ℕ+, particleEntropy (kernelData kappa) N
      ⟨root kappa fun i => F.density (σ N i),
        (finite_species_rough_product_admissibility kappa N (σ N) F.density).1⟩ =
      ENNReal.ofReal (relativeEntropy (labeledProduct fun i => F.density (σ N i))
          (particleLaw (kernelData kappa) N)).toReal := fun N => by
    rw [particleEntropy_root, ENNReal.ofReal_toReal
      ((finite_exact_identity kappa F (σ N)).1)]
  refine ⟨?_, ?_⟩
  · filter_upwards [hHpos] with N hN
    rw [hfin N]
    exact ENNReal.ofReal_pos.2 hN
  · have hreal : Tendsto (fun N : ℕ+ =>
        (4 * particleEnergy (kernelData kappa) N
          ⟨root kappa fun i => F.density (σ N i),
            (finite_species_rough_product_admissibility kappa N (σ N) F.density).1⟩ / N) /
        (2 * ((relativeEntropy (labeledProduct fun i => F.density (σ N i))
          (particleLaw (kernelData kappa) N)).toReal / N))) atTop (𝓝 (Dr / (2 * Gr))) :=
      hD'.div (hH.const_mul 2) (by positivity)
    have hreal' := ENNReal.tendsto_ofReal hreal
    have htarget : speciesQuotient positiveH1 positiveH1Drift F = ENNReal.ofReal (Dr / (2 * Gr)) := by
      unfold speciesQuotient
      rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_mul (by norm_num),
        hGrdef, ENNReal.ofReal_coe_nnreal, hDrdef, ENNReal.ofReal_toReal hDfin]
      simp
    rw [htarget]
    refine hreal'.congr' ?_
    filter_upwards [hHpos] with N hN
    unfold particleQuotient
    rw [hfin N]
    set E := particleEnergy (kernelData kappa) N
      ⟨root kappa fun i => F.density (σ N i),
        (finite_species_rough_product_admissibility kappa N (σ N) F.density).1⟩
    set H := (relativeEntropy (labeledProduct fun i => F.density (σ N i))
          (particleLaw (kernelData kappa) N)).toReal
    have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast N.ne_zero
    rw [← ENNReal.ofReal_div_of_pos hN]
    congr 1
    field_simp
    ring

/-! ### Symmetry of the identical-species product -/

theorem U_permute (κ : ℝ) (N : ℕ+) (π : Equiv.Perm (Fin N)) (x : ParticleSpace 1 N) :
    U κ N (permuteParticles π x) = U κ N x := by
  rw [U_eq_sum, U_eq_sum]
  congr 1
  simp only [permuteParticles]
  rw [← Equiv.sum_comp π (fun i => ∑ j, R (x i - x j))]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact Equiv.sum_comp π (fun j => R (x (π i) - x j))

theorem root_permute (κ : ℝ) (N : ℕ+) (r : Fin N → AbsoluteDensity 1) (hr : ∀ i j, r i = r j)
    (π : Equiv.Perm (Fin N)) (x : ParticleSpace 1 N) :
    root κ r (permuteParticles π x) = root κ r x := by
  unfold root
  have h1 : amp r (permuteParticles π x) = amp r x := by
    unfold amp
    simp only [permuteParticles]
    rw [← Equiv.prod_comp π (fun k => (r k).sqrt (x k))]
    exact Finset.prod_congr rfl fun k _ => by rw [hr k (π k)]
  have h2 : wfun κ N (permuteParticles π x) = wfun κ N x := by
    unfold wfun; rw [U_permute]
  rw [h1, h2]

theorem isSymmetric_root (κ : ℝ) (N : ℕ+) (r : Fin N → AbsoluteDensity 1)
    (hr : ∀ i j, r i = r j) (h : MemParticleH1 (kernelData κ) N (root κ r)) :
    IsSymmetricParticleTest (⟨root κ r, h⟩ : ParticleH1 (kernelData κ) N) :=
  IsSymmetricParticleFun.of_forall fun π x => root_permute κ N r hr π x

/-! ### Transport to `positiveH1` and the theorem -/

theorem kernelData_kappa_eq : kernelData kappa = positiveH1 := by
  unfold kernelData positiveH1
  simp [R_zero]

theorem upper_core (A : InteractionData 1) (hA : kernelData kappa = A) (F : SpeciesFamily 1)
    (hG : 0 < speciesGap positiveH1 F) (σ : ∀ N : ℕ+, Fin N → Fin F.count)
    (hσ : ∀ s, Tendsto (fun N : ℕ+ => frac (σ N) s) atTop (𝓝 (F.weight s))) :
    ∃ f : ∀ N : ℕ+, ParticleH1 A N,
      (∀ N, (f N).1 = root kappa fun i => F.density (σ N i)) ∧
      (∀ᶠ N : ℕ+ in atTop, 0 < particleEntropy A N (f N)) ∧
      Tendsto (fun N : ℕ+ => particleQuotient A N (f N)) atTop
        (𝓝 (speciesQuotient positiveH1 positiveH1Drift F)) ∧
      ((∀ N i j, σ N i = σ N j) → ∀ N, IsSymmetricParticleTest (f N)) := by
  subst hA
  obtain ⟨h1, h2⟩ := core_tendsto F hG σ hσ
  refine ⟨fun N => ⟨root kappa fun i => F.density (σ N i),
    (finite_species_rough_product_admissibility kappa N (σ N) F.density).1⟩,
    fun _ => rfl, h1, h2, fun hc N => ?_⟩
  exact isSymmetric_root kappa N _ (fun i j => by rw [hc N i j]) _

theorem single_labeling (ρ : AbsoluteDensity 1) :
    ∃ σ : ∀ N : ℕ+, Fin N → Fin (SpeciesFamily.single ρ).count,
      (∀ s, Tendsto (fun N : ℕ+ => frac (σ N) s) atTop
        (𝓝 ((SpeciesFamily.single ρ).weight s))) ∧ ∀ N i j, σ N i = σ N j := by
  refine ⟨fun _ _ => ⟨0, by simp⟩, fun s => ?_, fun _ _ _ => rfl⟩
  rw [SpeciesFamily.single_weight]
  refine tendsto_const_nhds.congr fun N => ?_
  have h1 : (s : ℕ) < 1 := by simpa using s.2
  have hs : s = ⟨0, by simp⟩ := Fin.ext (by show (s : ℕ) = 0; omega)
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast N.ne_zero
  unfold frac cnt
  simp [hs, hN]

/-- **H1019.** General finite family upper recovery, for the positive-`H¹` model `positiveH1`.

* For every finite species family `F` with `G_θ > 0` there are labelings `σ_N` with fractions
  `n_s(N)/N → θ_s`, and for any such labelings the root-product tests `f_N = √(dν_N/dP_N)`
  (labeled product `ν_N = ⊗ᵢ ρ_{σ_N(i)} m`) lie in `H¹(P_N)`, have positive entropy for all large
  `N`, and their quotients `2E_N(f_N)/Ent(f_N²)` converge to `D_θ/(2G_θ)`.
* Hence `limsup_N r_N^all ≤ r_ms`.
* For `q = 1` (a scalar density `ρ` with `G(ρ) > 0`) the products are symmetric, the quotients
  converge to `D(ρ)/(2G(ρ))`, and `limsup_N r_N^sym ≤ r_*`. -/
theorem general_finite_family_upper_recovery :
    (∀ F : SpeciesFamily 1, 0 < speciesGap positiveH1 F →
      (∃ σ : ∀ N : ℕ+, Fin N → Fin F.count,
        ∀ s, Tendsto (fun N : ℕ+ => frac (σ N) s) atTop (𝓝 (F.weight s))) ∧
      ∀ σ : ∀ N : ℕ+, Fin N → Fin F.count,
        (∀ s, Tendsto (fun N : ℕ+ => frac (σ N) s) atTop (𝓝 (F.weight s))) →
        ∃ f : ∀ N : ℕ+, ParticleH1 positiveH1 N,
          (∀ N, (f N).1 = root kappa fun i => F.density (σ N i)) ∧
          (∀ᶠ N : ℕ+ in atTop, 0 < particleEntropy positiveH1 N (f N)) ∧
          Tendsto (fun N : ℕ+ => particleQuotient positiveH1 N (f N)) atTop
            (𝓝 (speciesQuotient positiveH1 positiveH1Drift F))) ∧
    limsup (fun N : ℕ+ => particleRateAll positiveH1 N) atTop ≤
      speciesRate positiveH1 positiveH1Drift ∧
    (∀ ρ : AbsoluteDensity 1, 0 < scalarGap positiveH1 ρ →
      ∃ f : ∀ N : ℕ+, ParticleH1 positiveH1 N,
        (∀ N, IsSymmetricParticleTest (f N)) ∧
        (∀ᶠ N : ℕ+ in atTop, 0 < particleEntropy positiveH1 N (f N)) ∧
        Tendsto (fun N : ℕ+ => particleQuotient positiveH1 N (f N)) atTop
          (𝓝 (scalarQuotient positiveH1 positiveH1Drift ρ))) ∧
    limsup (fun N : ℕ+ => particleRateSym positiveH1 N) atTop ≤
      scalarRate positiveH1 positiveH1Drift := by
  have hall : ∀ F : SpeciesFamily 1, 0 < speciesGap positiveH1 F →
      (∃ σ : ∀ N : ℕ+, Fin N → Fin F.count,
        ∀ s, Tendsto (fun N : ℕ+ => frac (σ N) s) atTop (𝓝 (F.weight s))) ∧
      ∀ σ : ∀ N : ℕ+, Fin N → Fin F.count,
        (∀ s, Tendsto (fun N : ℕ+ => frac (σ N) s) atTop (𝓝 (F.weight s))) →
        ∃ f : ∀ N : ℕ+, ParticleH1 positiveH1 N,
          (∀ N, (f N).1 = root kappa fun i => F.density (σ N i)) ∧
          (∀ᶠ N : ℕ+ in atTop, 0 < particleEntropy positiveH1 N (f N)) ∧
          Tendsto (fun N : ℕ+ => particleQuotient positiveH1 N (f N)) atTop
            (𝓝 (speciesQuotient positiveH1 positiveH1Drift F)) := fun F hG =>
    ⟨exists_labeling F.count F.weight F.weight_nonneg F.weight_sum, fun σ hσ => by
      obtain ⟨f, h1, h2, h3, -⟩ := upper_core positiveH1 kernelData_kappa_eq F hG σ hσ
      exact ⟨f, h1, h2, h3⟩⟩
  have hsym : ∀ ρ : AbsoluteDensity 1, 0 < scalarGap positiveH1 ρ →
      ∃ f : ∀ N : ℕ+, ParticleH1 positiveH1 N,
        (∀ N, IsSymmetricParticleTest (f N)) ∧
        (∀ᶠ N : ℕ+ in atTop, 0 < particleEntropy positiveH1 N (f N)) ∧
        Tendsto (fun N : ℕ+ => particleQuotient positiveH1 N (f N)) atTop
          (𝓝 (scalarQuotient positiveH1 positiveH1Drift ρ)) := fun ρ hρ => by
    have hG : 0 < speciesGap positiveH1 (SpeciesFamily.single ρ) := by
      rw [speciesGap_single]; exact hρ
    obtain ⟨σ, hσ, hc⟩ := single_labeling ρ
    obtain ⟨f, -, h2, h3, h4⟩ := upper_core positiveH1 kernelData_kappa_eq _ hG σ hσ
    exact ⟨f, h4 hc, h2, by rwa [speciesQuotient_single] at h3⟩
  refine ⟨hall, ?_, hsym, ?_⟩
  · refine le_iInf fun F => ?_
    obtain ⟨σ, hσ⟩ := (hall F.1 F.2).1
    obtain ⟨f, -, h2, h3⟩ := (hall F.1 F.2).2 σ hσ
    calc limsup (fun N : ℕ+ => particleRateAll positiveH1 N) atTop
        ≤ limsup (fun N : ℕ+ => particleQuotient positiveH1 N (f N)) atTop :=
          limsup_le_limsup (by
            filter_upwards [h2] with N hN
            exact particleRateAll_le_quotient positiveH1 N (f N) hN)
      _ = speciesQuotient positiveH1 positiveH1Drift F.1 := h3.limsup_eq
  · refine le_iInf fun ρ => ?_
    obtain ⟨f, hs, h2, h3⟩ := hsym ρ.1 ρ.2
    calc limsup (fun N : ℕ+ => particleRateSym positiveH1 N) atTop
        ≤ limsup (fun N : ℕ+ => particleQuotient positiveH1 N (f N)) atTop :=
          limsup_le_limsup (by
            filter_upwards [h2] with N hN
            exact particleRateSym_le_quotient positiveH1 N (f N) (hs N) hN)
      _ = scalarQuotient positiveH1 positiveH1Drift ρ.1 := h3.limsup_eq

end DGPS.Examples.PositiveH1.Recovery
