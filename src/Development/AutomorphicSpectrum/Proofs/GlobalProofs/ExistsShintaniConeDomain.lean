module

public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AbelContinuation
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsTotallyPositiveBasisPositiveCoords
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.CongSubgroup
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.PartialZetaTwistedEntireDifference
import Mathlib.Tactic.Linter.HaveILetI
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.PlaceApplyStatement
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ShintaniConeDecompositionStatement
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SimplicialConeTilingStatement
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.TotallyPositiveBasisRatioBoundStatement
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Finite.Lemmas
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.CongSubgroup

-- Source module: Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsTotallyPositiveBasisPositiveCoordsStatement

section

@[expose] public section

open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones

theorem _root_.GlobalTheory.T.exists_totally_positive_basis_positive_coords : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (M : ℝ),
    ∃ (κ : Type) (_ : Fintype κ) (b : Module.Basis κ ℚ F), (∀ i, TotPos F (b i)) ∧
      ∀ x : F, TotPos F x → (∀ σ τ : F →+* ℝ, σ x ≤ M * τ x) → ∀ i, 0 < b.repr x i := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Gens.exists_totPos_basis | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Gens.exists_totPos_basis | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Gens.exists_totPos_basis <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GlobalProofs.FiniteUnitsBoundedEmbeddingRatio

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani

theorem embedding_unit_le_abs {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {R : ℝ} {u : (𝓞 F)ˣ}
    (hu : TotPos F ((u : 𝓞 F) : F)) (hR : ∀ σ τ : F →+* ℝ, σ ((u : 𝓞 F) : F) ≤ R * τ ((u : 𝓞 F) : F))
    (σ : F →+* ℝ) : σ ((u : 𝓞 F) : F) ≤ |R| := by
  classical
  haveI : Finite (F →+* ℝ) := Finite.of_equiv _ (realEmbeddingsEquiv F).symm
  haveI : Fintype (F →+* ℝ) := Fintype.ofFinite _
  have hprod : ∏ τ : F →+* ℝ, τ ((u : 𝓞 F) : F) = 1 := by
    rw [prod_real_embeddings_eq_absNorm (u : 𝓞 F) hu, Ideal.span_singleton_eq_top.2 u.isUnit, Ideal.absNorm_top]
    simp
  obtain ⟨τ, hτ⟩ : ∃ τ : F →+* ℝ, τ ((u : 𝓞 F) : F) ≤ 1 := by
    by_contra hne
    push_neg at hne
    have hlt : ∏ _τ : F →+* ℝ, (1 : ℝ) < ∏ τ : F →+* ℝ, τ ((u : 𝓞 F) : F) :=
      Finset.prod_lt_prod_of_nonempty₀ (fun _ _ => one_pos) (fun τ _ => hne τ) ⟨σ, Finset.mem_univ σ⟩
    rw [hprod] at hlt
    simp at hlt
  calc σ ((u : 𝓞 F) : F) ≤ R * τ ((u : 𝓞 F) : F) := hR σ τ
    _ ≤ |R| * τ ((u : 𝓞 F) : F) := mul_le_mul_of_nonneg_right (le_abs_self R) (hu τ).le
    _ ≤ |R| * 1 := mul_le_mul_of_nonneg_left hτ (abs_nonneg R)
    _ = |R| := mul_one _

theorem finite_totPos_units_bounded_ratio : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (R : ℝ),
    {u : (𝓞 F)ˣ | TotPos F ((u : 𝓞 F) : F) ∧ ∀ σ τ : F →+* ℝ, σ ((u : 𝓞 F) : F) ≤ R * τ ((u : 𝓞 F) : F)}.Finite := by
  intro F _ _ _ R
  have hinj : Function.Injective (fun u : (𝓞 F)ˣ => ((u : 𝓞 F) : F)) := fun a b h =>
    Units.ext (RingOfIntegers.ext h)
  refine ((Embeddings.finite_of_norm_le F ℂ |R|).preimage hinj.injOn).subset ?_
  rintro u ⟨hu, hR⟩
  refine ⟨(u : 𝓞 F).isIntegral_coe, fun φ => ?_⟩
  obtain ⟨σ, rfl⟩ := (realEmbeddingsEquiv F).surjective φ
  have h := embedding_unit_le_abs hu hR σ
  change ‖((σ ((u : 𝓞 F) : F) : ℝ) : ℂ)‖ ≤ |R|
  rw [Complex.norm_real, Real.norm_of_nonneg (hu σ).le]
  exact h

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GlobalProofs.FiniteUnitsBoundedEmbeddingRatioStatement

section

@[expose] public section

open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones

theorem _root_.GlobalTheory.T.finite_units_bounded_embedding_ratio : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (R : ℝ),
    {u : (𝓞 F)ˣ | TotPos F ((u : 𝓞 F) : F) ∧ ∀ σ τ : F →+* ℝ, σ ((u : 𝓞 F) : F) ≤ R * τ ((u : 𝓞 F) : F)}.Finite := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.finite_totPos_units_bounded_ratio | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.finite_totPos_units_bounded_ratio | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.finite_totPos_units_bounded_ratio <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GlobalProofs.UniqueReducedOrbitRepresentative

section

@[expose] public section

namespace GlobalTheory.CompanionTheory.SiegelKlingen

theorem exists_unique_minimal_translate :
    ∀ {G M : Type} [Group G] [Monoid M] (φ : G →* M) (f : G →* ℝ), (∀ g, 0 < f g) →
    Function.Injective f → ∀ (D : Set M),
    {g : G | ∃ x ∈ D, φ g * x ∈ D}.Finite → ∀ (x : M), (∃ g, φ g * x ∈ D) →
    ∃! g, φ g * x ∈ {y ∈ D | ∀ g' : G, f g' < 1 → φ g' * y ∉ D} := by
  intro G M _ _ φ f hpos hinj D hfin x ⟨g0, hg0⟩
  have key : ∀ a b : G, φ (a * b⁻¹) * (φ b * x) = φ a * x := by
    intro a b
    rw [← mul_assoc, ← map_mul, inv_mul_cancel_right]
  have hS : {g : G | φ g * x ∈ D}.Finite := by
    refine (hfin.image (fun h => h * g0)).subset ?_
    intro g hg
    exact ⟨g * g0⁻¹, ⟨φ g0 * x, hg0, by rw [key]; exact hg⟩, inv_mul_cancel_right g g0⟩
  obtain ⟨g, hgS, hmin⟩ := Set.exists_min_image _ f hS ⟨g0, hg0⟩
  refine ⟨g, ⟨hgS, fun g' hg' hD => ?_⟩, ?_⟩
  · have hmem : φ (g' * g) * x ∈ D := by rwa [map_mul, mul_assoc]
    have h1 := hmin _ hmem
    rw [map_mul] at h1
    have hp := hpos g
    nlinarith
  · rintro g2 ⟨hg2, hmin2⟩
    have h1 : 1 ≤ f (g * g2⁻¹) := not_lt.1 fun hlt => hmin2 _ hlt (by rw [key]; exact hgS)
    rw [map_mul, map_inv] at h1
    have hp2 := hpos g2
    have h3 := mul_le_mul_of_nonneg_right h1 hp2.le
    rw [one_mul, inv_mul_cancel_right₀ hp2.ne'] at h3
    exact hinj (le_antisymm h3 (hmin g2 hg2))

end GlobalTheory.CompanionTheory.SiegelKlingen
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GlobalProofs.UniqueReducedOrbitRepresentativeStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.unique_reduced_orbit_representative : ∀ {G M : Type} [Group G] [Monoid M] (φ : G →* M) (f : G →* ℝ), (∀ g, 0 < f g) → Function.Injective f → ∀ (D : Set M),
    {g : G | ∃ x ∈ D, φ g * x ∈ D}.Finite → ∀ (x : M), (∃ g, φ g * x ∈ D) →
    ∃! g, φ g * x ∈ {y ∈ D | ∀ g' : G, f g' < 1 → φ g' * y ∉ D} := by
  first | exact @GlobalTheory.CompanionTheory.SiegelKlingen.exists_unique_minimal_translate | exact GlobalTheory.CompanionTheory.SiegelKlingen.exists_unique_minimal_translate | (intros; apply GlobalTheory.CompanionTheory.SiegelKlingen.exists_unique_minimal_translate <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsShintaniConeDomain

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani

theorem exists_coneDomain : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔣 : Ideal (𝓞 F)), 𝔣 ≠ ⊥ →
    ∃ (ι : Type) (_ : Fintype ι) (r : ι → ℕ) (v : ∀ c, Fin (r c) → F), IsConeDomain 𝔣 r v := by
  intro F _ _ _ 𝔣 h𝔣
  classical
  obtain ⟨M, hM⟩ := GlobalTheory.T.exists_congruence_unit_balancing_embeddings F 𝔣 h𝔣
  obtain ⟨κ, _, b, hbpos, hbcov⟩ := GlobalTheory.T.exists_totally_positive_basis_positive_coords F M
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.T.totally_positive_basis_ratio_bound F b hbpos

  obtain ⟨σ₁⟩ : Nonempty (F →+* ℝ) := by
    have w : InfinitePlace F := Classical.choice inferInstance
    exact ⟨w.embedding_of_isReal (IsTotallyReal.isReal w)⟩

  let G := ↥(congSubgroup 𝔣)
  let φ : G →* F := ((algebraMap (𝓞 F) F : 𝓞 F →+* F) : 𝓞 F →* F).comp ((Units.coeHom (𝓞 F)).comp (congSubgroup 𝔣).subtype)
  have hφ : ∀ g : G, φ g = (((g : (𝓞 F)ˣ) : 𝓞 F) : F) := fun g => rfl
  have hgpos : ∀ g : G, TotPos F (φ g) := fun g => g.2.2
  let f : G →* ℝ := (σ₁ : F →* ℝ).comp φ
  have hf : ∀ g : G, f g = σ₁ (φ g) := fun g => rfl
  have hfpos : ∀ g, 0 < f g := fun g => hgpos g σ₁
  have hφinj : Function.Injective φ := by
    intro g g' h
    apply Subtype.ext
    apply Units.ext
    exact RingOfIntegers.coe_injective h
  have hfinj : Function.Injective f := fun g g' h => hφinj (σ₁.injective h)
  let D : Set F := {x | ∀ i, 0 < b.repr x i}

  have hDpos : ∀ x ∈ D, TotPos F x := by
    intro x hx σ
    have hk : Nonempty κ := b.index_nonempty

    rw [← b.sum_repr x, map_sum]
    refine Finset.sum_pos (fun i _ => ?_) Finset.univ_nonempty
    rw [Rat.smul_def, map_mul, map_ratCast]
    exact mul_pos (by exact_mod_cast hx i) (hbpos i σ)
  have hfin : {g : G | ∃ x ∈ D, φ g * x ∈ D}.Finite := by
    have hfin0 := GlobalTheory.T.finite_units_bounded_embedding_ratio F (R * R)
    refine Set.Finite.of_finite_image (f := fun g : G => (g : (𝓞 F)ˣ)) (hfin0.subset ?_) (Subtype.val_injective.injOn)
    rintro _ ⟨g, ⟨x, hx, hgx⟩, rfl⟩
    refine ⟨hgpos g, fun σ τ => ?_⟩
    have h1 := hR _ hgx σ τ
    have h2 := hR x hx τ σ
    have hxσ := hDpos x hx σ
    have hgτ := hgpos g τ
    rw [map_mul, map_mul] at h1
    have h3 : σ (φ g) * σ x ≤ (R * R * τ (φ g)) * σ x := by
      calc σ (φ g) * σ x ≤ R * (τ (φ g) * τ x) := h1
        _ ≤ R * (τ (φ g) * (R * σ x)) := by gcongr
        _ = _ := by ring
    exact le_of_mul_le_mul_right h3 hxσ
  let E : Set F := {y ∈ D | ∀ g' : G, f g' < 1 → φ g' * y ∉ D}
  let T := {g : G | ∃ x ∈ D, φ g * x ∈ D}
  let Λ : Set (F →ₗ[ℚ] ℚ) := (fun p : G × κ => (b.coord p.2).comp (LinearMap.mulLeft ℚ (φ p.1))) '' (T ×ˢ Set.univ)
  have hΛ : Λ.Finite := (hfin.prod Set.finite_univ).image _
  have hsign : ∀ (p q : ℚ), SignType.sign p = SignType.sign q → 0 < p → 0 < q := by
    intro p q h hp
    rw [sign_pos hp] at h
    exact sign_eq_one_iff.mp h.symm
  have htile : Tile ((posCone F : ConvexCone ℚ F) : Set F) (fun _ => True) E := by
    refine GlobalTheory.T.cone_tiling_by_sign_regions (posCone F) b hbpos Λ hΛ E (fun x hx => hx.1) ?_
    intro x y hx hy hs hxE
    refine ⟨hy, fun g' hg' hyD => ?_⟩
    refine hxE.2 g' hg' ?_
    have hgT : g' ∈ T := ⟨y, hy, hyD⟩
    intro i
    have := hs _ ⟨(g', i), ⟨hgT, trivial⟩, rfl⟩
    simp only [LinearMap.comp_apply, Module.Basis.coord_apply, LinearMap.mulLeft_apply] at this
    exact hsign _ _ this.symm (hyD i)
  have h0 : (0 : F) ∉ E := by
    intro h
    have := hDpos 0 h.1 σ₁
    simp at this
  obtain ⟨ι, hι, r, v, hr, hli, hvP, hsub, hun⟩ := GlobalTheory.T.shintani_cone_decomposition _ _ E htile h0
  refine ⟨ι, hι, r, v, hr, hli, hvP, ?_⟩
  intro x hx

  obtain ⟨u, hu, hub⟩ := hM x hx
  have hxD : ∃ g : G, φ g * x ∈ D := by
    refine ⟨⟨u, hu⟩, hbcov _ ?_ hub⟩
    intro σ
    rw [map_mul]
    exact mul_pos (hu.2 σ) (hx σ)
  obtain ⟨g, hg, hguniq⟩ := GlobalTheory.T.unique_reduced_orbit_representative φ f hfpos hfinj D hfin x hxD
  obtain ⟨c, hc, hcuniq⟩ := hun _ hg
  refine ⟨(⟨g.1, g.2⟩, c), hc, ?_⟩
  rintro ⟨⟨u', hu'⟩, c'⟩ hp
  have hp' : φ ⟨u', hu'⟩ * x ∈ openCone (v c') := hp
  have hg' : (⟨u', hu'⟩ : G) = g := hguniq _ (hsub c' hp')
  have hc' : c' = c := by
    apply hcuniq
    rw [← hg']
    exact hp'
  subst hc'
  have := congrArg Subtype.val hg'
  simp only at this
  simp [this]

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani
end
end
end
