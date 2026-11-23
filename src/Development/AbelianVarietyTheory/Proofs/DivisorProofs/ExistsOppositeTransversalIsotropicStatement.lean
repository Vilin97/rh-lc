module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmHostUnitAddConjEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjInvariantTraceGeneratorLocalStatement
public import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmHostUnitAddConjEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiltGraded
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOppositeSubmoduleImprovedModPrimeOfNeConjStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOppositeSubmoduleImprovedModPrimeOfOrthogoStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRankOneChangeImprovesImageRealPrimeStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVectorMapsIntoIdealOfNotOntoMod
import Mathlib.Tactic.Linter.Style
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotropicImageNotOntoModConjIdealStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SupSmulTopEqTopOfForallMaximalOverNatStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOneModMaximalMemOtherMaximalsOverNat

section

@[expose] public section

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt

theorem GlobalTheory.sep_one_mod_maximal_mem_others : ∀ {E : Type} [Field E] [NumberField E] (n : ℕ) (hn : 0 < n) (𝔭 : Ideal (𝓞 E)) (h𝔭 : 𝔭.IsMaximal),
    ∃ e : 𝓞 E, e - 1 ∈ 𝔭 ∧ ∀ 𝔮 : Ideal (𝓞 E), 𝔮.IsMaximal → (n : 𝓞 E) ∈ 𝔮 → 𝔮 ≠ 𝔭 → e ∈ 𝔮 := by
  intro E _ _ n hn 𝔭 h𝔭
  have hn0 : (n : 𝓞 E) ≠ 0 := by exact_mod_cast hn.ne'
  have hI0 : Ideal.span {(n : 𝓞 E)} ≠ ⊥ := by
    rwa [Ne, Ideal.span_singleton_eq_bot]
  set S := (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(n : 𝓞 E)})).toFinset.erase 𝔭
    with hS
  have htop : 𝔭 ⊔ ∏ 𝔮 ∈ S, 𝔮 = ⊤ := by
    refine Ideal.sup_prod_eq_top fun 𝔮 h𝔮 => ?_
    rw [hS, Finset.mem_erase, Multiset.mem_toFinset, Ideal.mem_normalizedFactors_iff hI0] at h𝔮
    obtain ⟨hne, hpr, hle⟩ := h𝔮
    have hbot : 𝔮 ≠ ⊥ := by
      rintro rfl
      rw [Ideal.span_le, Set.singleton_subset_iff] at hle
      exact hn0 hle
    have hmax : 𝔮.IsMaximal := hpr.isMaximal hbot
    by_contra hc
    have e1 : 𝔭 = 𝔭 ⊔ 𝔮 := h𝔭.eq_of_le hc le_sup_left
    have h2 : 𝔮 ≤ 𝔭 := e1 ▸ le_sup_right
    exact hne (hmax.eq_of_le h𝔭.ne_top h2)
  have h1 : (1 : 𝓞 E) ∈ 𝔭 ⊔ ∏ 𝔮 ∈ S, 𝔮 := htop ▸ Submodule.mem_top
  obtain ⟨p, hp, e, he, hpe⟩ := Submodule.mem_sup.mp h1
  refine ⟨e, ?_, fun 𝔮 hmax hn𝔮 hne => ?_⟩
  · have : e - 1 = -p := by rw [← hpe]; ring
    rw [this]; exact 𝔭.neg_mem hp
  · have hmem : 𝔮 ∈ S := by
      rw [hS, Finset.mem_erase, Multiset.mem_toFinset, Ideal.mem_normalizedFactors_iff hI0]
      exact ⟨hne, hmax.isPrime, (Ideal.span_singleton_le_iff_mem _).2 hn𝔮⟩
    exact Ideal.prod_le_inf.trans (Finset.inf_le hmem) he
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOneModMaximalMemOtherMaximalsOverNatStatement

section

@[expose] public section

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt


theorem _root_.GlobalTheory.T.exists_one_mod_maximal_mem_other_maximals_over_nat : ∀ {E : Type} [Field E] [NumberField E] (n : ℕ) (hn : 0 < n) (𝔭 : Ideal (𝓞 E)) (h𝔭 : 𝔭.IsMaximal),
    ∃ e : 𝓞 E, e - 1 ∈ 𝔭 ∧ ∀ 𝔮 : Ideal (𝓞 E), 𝔮.IsMaximal → (n : 𝓞 E) ∈ 𝔮 → 𝔮 ≠ 𝔭 → e ∈ 𝔮 := by
  first | exact @GlobalTheory.sep_one_mod_maximal_mem_others | exact GlobalTheory.sep_one_mod_maximal_mem_others | (intros; apply GlobalTheory.sep_one_mod_maximal_mem_others <;> assumption)
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVectorMapsIntoIdealOfNotOntoModStatement

section

@[expose] public section

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt


theorem _root_.GlobalTheory.T.exists_vector_mapsInto_ideal_of_not_onto_mod : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)
    {X : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (y : D.La →ₗ[𝓞 E] X) (Z Z' : Submodule (𝓞 E) D.La) (h : IsOpp D Z Z')
    (hr : Module.finrank (𝓞 E) Z = Module.finrank (𝓞 E) X) (𝔭 : Ideal (𝓞 E)) (h𝔭 : 𝔭.IsMaximal)
    (hi : img D y Z' 𝔭 ≠ ⊤),
    ∃ v : Z', y v ∈ 𝔭 • (⊤ : Submodule (𝓞 E) X) ∧ ∃ ℓ₀ : Z' →ₗ[𝓞 E] 𝓞 E, ℓ₀ v ∉ 𝔭 := by
  first | exact @GlobalTheory.LowFilt.IsOpp.exists_ker_vec | exact GlobalTheory.LowFilt.IsOpp.exists_ker_vec | (intros; apply GlobalTheory.LowFilt.IsOpp.exists_ker_vec <;> assumption)
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteMaximalIdealsContainingNatCast

section

@[expose] public section

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt

namespace GlobalTheory.LowDat

theorem finite_maximal_ideals_containing_natCast :
    ∀ {E : Type} [Field E] [NumberField E] (n : ℕ) (hn : 0 < n),
    {𝔮 : Ideal (𝓞 E) | 𝔮.IsMaximal ∧ (n : 𝓞 E) ∈ 𝔮}.Finite := by
  intro E _ _ n hn
  have hn0 : (n : 𝓞 E) ≠ 0 := by exact_mod_cast hn.ne'
  have hI : Ideal.span {(n : 𝓞 E)} ≠ 0 := by
    simpa [Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot] using hn0
  refine ((Ideal.finite_factors hI).image
    (fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 E) => v.asIdeal)).subset ?_
  rintro 𝔮 ⟨hmax, hmem⟩
  have hne : 𝔮 ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hmem
    exact hn0 hmem
  refine ⟨⟨𝔮, hmax.isPrime, hne⟩, ?_, rfl⟩
  show 𝔮 ∣ Ideal.span {(n : 𝓞 E)}
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  exact hmem

end GlobalTheory.LowDat
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteMaximalIdealsContainingNatCastStatement

section

@[expose] public section

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt


theorem _root_.GlobalTheory.T.finite_maximal_ideals_containing_natCast' : ∀ {E : Type} [Field E] [NumberField E] (n : ℕ) (hn : 0 < n),
    {𝔮 : Ideal (𝓞 E) | 𝔮.IsMaximal ∧ (n : 𝓞 E) ∈ 𝔮}.Finite := by
  first | exact @GlobalTheory.LowDat.finite_maximal_ideals_containing_natCast | exact GlobalTheory.LowDat.finite_maximal_ideals_containing_natCast | (intros; apply GlobalTheory.LowDat.finite_maximal_ideals_containing_natCast <;> assumption)
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOppositeTransversalIsotropic

section

@[expose] public section

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt

namespace GlobalTheory.LowFilt.Transv

theorem fin_max : ∀ {E : Type} [Field E] [NumberField E] (n : ℕ) (hn : 0 < n),
    {𝔮 : Ideal (𝓞 E) | 𝔮.IsMaximal ∧ (n : 𝓞 E) ∈ 𝔮}.Finite :=
  GlobalTheory.T.finite_maximal_ideals_containing_natCast'

theorem exists_sep : ∀ {E : Type} [Field E] [NumberField E] (n : ℕ) (hn : 0 < n) (𝔭 : Ideal (𝓞 E)) (h𝔭 : 𝔭.IsMaximal),
    ∃ e : 𝓞 E, e - 1 ∈ 𝔭 ∧ ∀ 𝔮 : Ideal (𝓞 E), 𝔮.IsMaximal → (n : 𝓞 E) ∈ 𝔮 → 𝔮 ≠ 𝔭 → e ∈ 𝔮 :=
  GlobalTheory.T.exists_one_mod_maximal_mem_other_maximals_over_nat

theorem sup_eq_top : ∀ {E : Type} [Field E] [NumberField E] {X : Type} [AddCommGroup X] [Module (𝓞 E) X]
    (N : Submodule (𝓞 E) X) (n : ℕ) (hn : 0 < n)
    (h : ∀ 𝔮 : Ideal (𝓞 E), 𝔮.IsMaximal → (n : 𝓞 E) ∈ 𝔮 → N ⊔ 𝔮 • (⊤ : Submodule (𝓞 E) X) = ⊤),
    N ⊔ Ideal.span {(n : 𝓞 E)} • (⊤ : Submodule (𝓞 E) X) = ⊤ :=
  GlobalTheory.T.sup_smul_top_eq_top_of_forall_maximal_over_nat

theorem exists_ker_vec : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)
    {X : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (y : D.La →ₗ[𝓞 E] X) (Z Z' : Submodule (𝓞 E) D.La) (h : IsOpp D Z Z')
    (hr : Module.finrank (𝓞 E) Z = Module.finrank (𝓞 E) X) (𝔭 : Ideal (𝓞 E)) (h𝔭 : 𝔭.IsMaximal)
    (hi : img D y Z' 𝔭 ≠ ⊤),
    ∃ v : Z', y v ∈ 𝔭 • (⊤ : Submodule (𝓞 E) X) ∧ ∃ ℓ₀ : Z' →ₗ[𝓞 E] 𝓞 E, ℓ₀ v ∉ 𝔭 :=
  GlobalTheory.T.exists_vector_mapsInto_ideal_of_not_onto_mod

theorem exists_real_theta : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (𝔭 : Ideal (𝓞 E))
    (h𝔭 : 𝔭.IsMaximal),
    ∃ θ : 𝓞 E →+ ℤ, (∀ t, θ (H.bar t) = θ t) ∧ ∃ s : 𝓞 E, s ∉ 𝔭 ∧ H.bar s ∉ 𝔭 ∧
      ∀ ψ : 𝓞 E →+ ℤ, ∃ t : 𝓞 E, ∀ u, ψ (s * u) = θ (t * u) :=
  GlobalTheory.T.exists_conj_invariant_trace_generator_local

theorem img_bar_ne_top : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)
    {X : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (y : D.La →ₗ[𝓞 E] X) (n : ℕ) (hn : 0 < n) (hc : Cois D y n) (Z Z' : Submodule (𝓞 E) D.La) (h : IsOpp D Z Z')
    (hr : Module.finrank (𝓞 E) Z = Module.finrank (𝓞 E) X) (𝔭 : Ideal (𝓞 E)) (h𝔭 : 𝔭.IsMaximal)
    (hn𝔭 : (n : 𝓞 E) ∈ 𝔭) (hi : img D y Z' 𝔭 ≠ ⊤) (hL : (perp D Z ⊓ perp D Z').map y ≤ img D y Z' 𝔭),
    img D y Z' (𝔭.map (H.bar : 𝓞 E →+* 𝓞 E)) ≠ ⊤ :=
  GlobalTheory.T.isotropicImage_not_onto_mod_conj_ideal

theorem improves_A : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)
    {X : Type} [AddCommGroup X] [Module (𝓞 E) X] (y : D.La →ₗ[𝓞 E] X) (n : ℕ)
    (Z Z' : Submodule (𝓞 E) D.La) (h : IsOpp D Z Z') (𝔭 : Ideal (𝓞 E)) (h𝔭 : 𝔭.IsMaximal) (hn𝔭 : (n : 𝓞 E) ∈ 𝔭)
    (e : 𝓞 E) (he1 : e - 1 ∈ 𝔭) (he : ∀ 𝔮 : Ideal (𝓞 E), 𝔮.IsMaximal → (n : 𝓞 E) ∈ 𝔮 → 𝔮 ≠ 𝔭 → e ∈ 𝔮)
    (v : Z') (hv : y v ∈ 𝔭 • (⊤ : Submodule (𝓞 E) X)) (ℓ₀ : Z' →ₗ[𝓞 E] 𝓞 E) (hℓ₀ : ℓ₀ v ∉ 𝔭)
    (m : D.La) (hm : m ∈ perp D Z ⊓ perp D Z') (hym : y m ∉ img D y Z' 𝔭)
    (hA : 𝔭.map (H.bar : 𝓞 E →+* 𝓞 E) ≠ 𝔭 ∨ Z.map y ≤ img D y Z' 𝔭),
    ∃ Z'', Improves D y n 𝔭 Z Z' Z'' :=
  GlobalTheory.T.exists_oppositeSubmodule_improved_mod_prime_of_orthogonal

theorem rankOneChange_improves_real_prime_first : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)
    {X : Type} [AddCommGroup X] [Module (𝓞 E) X] (y : D.La →ₗ[𝓞 E] X) (n : ℕ)
    (Z Z' : Submodule (𝓞 E) D.La) (h : IsOpp D Z Z') (𝔭 : Ideal (𝓞 E)) (h𝔭 : 𝔭.IsMaximal)
    (hb : 𝔭.map (H.bar : 𝓞 E →+* 𝓞 E) = 𝔭)
    (e : 𝓞 E) (he1 : e - 1 ∈ 𝔭) (he : ∀ 𝔮 : Ideal (𝓞 E), 𝔮.IsMaximal → (n : 𝓞 E) ∈ 𝔮 → 𝔮 ≠ 𝔭 → e ∈ 𝔮)
    (v : Z') (hv : y v ∈ 𝔭 • (⊤ : Submodule (𝓞 E) X)) (ℓ₀ : Z' →ₗ[𝓞 E] 𝓞 E) (hℓ₀ : ℓ₀ v ∉ 𝔭)
    (θ : 𝓞 E →+ ℤ) (hθ : ∀ t, θ (H.bar t) = θ t) (s : 𝓞 E) (hs : s ∉ 𝔭) (hs' : H.bar s ∉ 𝔭)
    (hgen : ∀ ψ : 𝓞 E →+ ℤ, ∃ t : 𝓞 E, ∀ u, ψ (s * u) = θ (t * u))
    (hZ : ¬ Z.map y ≤ img D y Z' 𝔭),
    ∃ Z'', Improves D y n 𝔭 Z Z' Z'' :=
  GlobalTheory.T.exists_rankOneChange_improves_image_real_prime

theorem rankOneChange_improves_nonreal_prime : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)
    {X : Type} [AddCommGroup X] [Module (𝓞 E) X] (y : D.La →ₗ[𝓞 E] X) (n : ℕ)
    (Z Z' : Submodule (𝓞 E) D.La) (h : IsOpp D Z Z') (𝔭 : Ideal (𝓞 E)) (h𝔭 : 𝔭.IsMaximal) (hn𝔭 : (n : 𝓞 E) ∈ 𝔭)
    (hb : 𝔭.map (H.bar : 𝓞 E →+* 𝓞 E) ≠ 𝔭)
    (e : 𝓞 E) (he1 : e - 1 ∈ 𝔭) (he : ∀ 𝔮 : Ideal (𝓞 E), 𝔮.IsMaximal → (n : 𝓞 E) ∈ 𝔮 → 𝔮 ≠ 𝔭 → e ∈ 𝔮)
    (e' : 𝓞 E) (he1' : e' - 1 ∈ 𝔭.map (H.bar : 𝓞 E →+* 𝓞 E))
    (he' : ∀ 𝔮 : Ideal (𝓞 E), 𝔮.IsMaximal → (n : 𝓞 E) ∈ 𝔮 → 𝔮 ≠ 𝔭.map (H.bar : 𝓞 E →+* 𝓞 E) → e' ∈ 𝔮)
    (v : Z') (hv : y v ∈ 𝔭 • (⊤ : Submodule (𝓞 E) X)) (ℓ₀ : Z' →ₗ[𝓞 E] 𝓞 E) (hℓ₀ : ℓ₀ v ∉ 𝔭)
    (v₂ : Z') (hv₂ : y v₂ ∈ 𝔭.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) X)) (ℓ₁ : Z' →ₗ[𝓞 E] 𝓞 E)
    (hℓ₁ : ℓ₁ v₂ ∉ 𝔭.map (H.bar : 𝓞 E →+* 𝓞 E))
    (θ : 𝓞 E →+ ℤ) (hθ : ∀ t, θ (H.bar t) = θ t) (s : 𝓞 E) (hs : s ∉ 𝔭) (hs' : H.bar s ∉ 𝔭)
    (hgen : ∀ ψ : 𝓞 E →+ ℤ, ∃ t : 𝓞 E, ∀ u, ψ (s * u) = θ (t * u))
    (hZ : ¬ Z.map y ≤ img D y Z' 𝔭),
    ∃ Z'', Improves D y n 𝔭 Z Z' Z'' :=
  GlobalTheory.T.exists_oppositeSubmodule_improved_mod_prime_of_ne_conj

theorem img_top_of {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)
    {X : Type} [AddCommGroup X] [Module (𝓞 E) X] (y : D.La →ₗ[𝓞 E] X) (n : ℕ) (hc : Cois D y n)
    (Z Z' : Submodule (𝓞 E) D.La) (h : IsOpp D Z Z') (𝔭 : Ideal (𝓞 E)) (hn𝔭 : (n : 𝓞 E) ∈ 𝔭)
    (hZ : Z.map y ≤ img D y Z' 𝔭) (hL : ∀ m ∈ perp D Z ⊓ perp D Z', y m ∈ img D y Z' 𝔭) :
    img D y Z' 𝔭 = ⊤ := by
  rw [eq_top_iff]
  intro x _
  obtain ⟨a, e, hae⟩ := hc.1 x
  obtain ⟨z, hz, m, hm, b, hb, rfl⟩ := h.exists_decomp a
  have h1 : y (z + m + b) ∈ img D y Z' 𝔭 := by
    rw [map_add (f := _), map_add (f := _)]
    exact add_mem (add_mem (hZ ⟨z, hz, rfl⟩) (hL m hm)) (Submodule.mem_sup_left ⟨b, hb, rfl⟩)
  have h2 : n • e ∈ img D y Z' 𝔭 := by
    apply Submodule.mem_sup_right
    rw [← Nat.cast_smul_eq_nsmul (𝓞 E)]
    exact Submodule.smul_mem_smul hn𝔭 trivial
  have h3 : x = y (z + m + b) - n • e := by rw [hae]; abel
  rw [h3]
  exact sub_mem h1 h2

theorem improve {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)
    {X : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (y : D.La →ₗ[𝓞 E] X) (n : ℕ) (hn : 0 < n) (hc : Cois D y n) (Z Z' : Submodule (𝓞 E) D.La) (h : IsOpp D Z Z')
    (hr : Module.finrank (𝓞 E) Z = Module.finrank (𝓞 E) X) (𝔭 : Ideal (𝓞 E)) (h𝔭 : 𝔭.IsMaximal)
    (hn𝔭 : (n : 𝓞 E) ∈ 𝔭) (hi : img D y Z' 𝔭 ≠ ⊤) : ∃ Z'', Improves D y n 𝔭 Z Z' Z'' := by
  obtain ⟨e, he1, he⟩ := exists_sep (E := E) n hn 𝔭 h𝔭
  obtain ⟨v, hv, ℓ₀, hℓ₀⟩ := exists_ker_vec D y Z Z' h hr 𝔭 h𝔭 hi
  obtain ⟨θ, hθ, s, hs, hs', hgen⟩ := exists_real_theta H 𝔭 h𝔭
  by_cases hA : ∃ m ∈ perp D Z ⊓ perp D Z', y m ∉ img D y Z' 𝔭 ∧
      (𝔭.map (H.bar : 𝓞 E →+* 𝓞 E) ≠ 𝔭 ∨ Z.map y ≤ img D y Z' 𝔭)
  · obtain ⟨m, hm, hym, hA⟩ := hA
    exact improves_A D y n Z Z' h 𝔭 h𝔭 hn𝔭 e he1 he v hv ℓ₀ hℓ₀ m hm hym hA
  have hZ : ¬ Z.map y ≤ img D y Z' 𝔭 := fun hZ =>
    hi (img_top_of D y n hc Z Z' h 𝔭 hn𝔭 hZ fun m hm => by_contra fun h' => hA ⟨m, hm, h', Or.inr hZ⟩)
  by_cases hb : 𝔭.map (H.bar : 𝓞 E →+* 𝓞 E) = 𝔭
  · exact rankOneChange_improves_real_prime_first D y n Z Z' h 𝔭 h𝔭 hb e he1 he v hv ℓ₀ hℓ₀ θ hθ s hs hs' hgen hZ
  have hL : (perp D Z ⊓ perp D Z').map y ≤ img D y Z' 𝔭 := by
    rintro _ ⟨m, hm, rfl⟩
    exact by_contra fun h' => hA ⟨m, hm, h', Or.inl hb⟩
  have hi' := img_bar_ne_top D y n hn hc Z Z' h hr 𝔭 h𝔭 hn𝔭 hi hL
  have h𝔭' : (𝔭.map (H.bar : 𝓞 E →+* 𝓞 E)).IsMaximal := Ideal.map_isMaximal_of_equiv H.bar
  have hn𝔭' : (n : 𝓞 E) ∈ 𝔭.map (H.bar : 𝓞 E →+* 𝓞 E) := by
    simpa using Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) hn𝔭
  obtain ⟨e', he1', he'⟩ := exists_sep (E := E) n hn _ h𝔭'
  obtain ⟨v₂, hv₂, ℓ₁, hℓ₁⟩ := exists_ker_vec D y Z Z' h hr _ h𝔭' hi'
  exact rankOneChange_improves_nonreal_prime D y n Z Z' h 𝔭 h𝔭 hn𝔭 hb e he1 he e' he1' he' v hv ℓ₀ hℓ₀ v₂ hv₂ ℓ₁ hℓ₁ θ hθ s hs hs' hgen hZ

end GlobalTheory.LowFilt.Transv

namespace GlobalTheory.LowFilt

open GlobalTheory.LowFilt.Transv in
theorem exists_opp_transv : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) {X : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (y : D.La →ₗ[𝓞 E] X) (n : ℕ), 0 < n → Cois D y n → ∀ Z Z₀ : Submodule (𝓞 E) D.La, IsOpp D Z Z₀ →
    Module.finrank (𝓞 E) Z = Module.finrank (𝓞 E) X →
    ∃ Z' : Submodule (𝓞 E) D.La, IsOpp D Z Z' ∧ ∀ x, ∃ b ∈ Z', ∃ e, y b = x + n • e := by
  intro E _ _ _ H D X _ _ _ _ y n hn hc Z Z₀ h0 hr
  classical
  let S := {𝔮 : Ideal (𝓞 E) | 𝔮.IsMaximal ∧ (n : 𝓞 E) ∈ 𝔮}
  haveI : Finite S := (fin_max (E := E) n hn).to_subtype
  haveI : Module.Finite (𝓞 E) X := Module.Finite.of_restrictScalars_finite ℤ (𝓞 E) X
  let F : Submodule (𝓞 E) D.La → (S → Submodule (𝓞 E) X) := fun Z' q => img D y Z' q.1
  haveI : IsNoetherian (𝓞 E) X := isNoetherian_of_isNoetherianRing_of_finite (𝓞 E) X
  have h1 : WellFoundedLT (S → (Submodule (𝓞 E) X)ᵒᵈ) := Pi.wellFoundedLT
  haveI : WellFoundedGT (S → Submodule (𝓞 E) X) := h1
  have wf : WellFounded (fun a b : S → Submodule (𝓞 E) X => b < a) := wellFounded_gt
  obtain ⟨_, ⟨Z', hZ', rfl⟩, hmax⟩ := wf.has_min (F '' {Z' | IsOpp D Z Z'}) ⟨_, Z₀, h0, rfl⟩
  have htop : ∀ 𝔮 : Ideal (𝓞 E), 𝔮.IsMaximal → (n : 𝓞 E) ∈ 𝔮 →
      Z'.map y ⊔ 𝔮 • (⊤ : Submodule (𝓞 E) X) = ⊤ := by
    intro 𝔮 hq hnq
    by_contra hne
    obtain ⟨Z'', h1, h2, h3⟩ := improve D y n hn hc Z Z' hZ' hr 𝔮 hq hnq hne
    exact hmax (F Z'') ⟨Z'', h1, rfl⟩
      (lt_of_le_not_ge (fun q => h2 q.1 q.2.1 q.2.2) fun hle => h3 (hle ⟨𝔮, hq, hnq⟩))
  have hall := sup_eq_top (Z'.map y) n hn htop
  refine ⟨Z', hZ', fun x => ?_⟩
  have hx : x ∈ Z'.map y ⊔ Ideal.span {(n : 𝓞 E)} • (⊤ : Submodule (𝓞 E) X) := by rw [hall]; trivial
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_sup] at hx
  obtain ⟨_, ⟨b, hb, rfl⟩, w, hw, hsum⟩ := hx
  obtain ⟨e', -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hw
  refine ⟨b, hb, -e', ?_⟩
  rw [smul_neg, ← Nat.cast_smul_eq_nsmul (𝓞 E), ← hsum]
  abel

end GlobalTheory.LowFilt
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOppositeTransversalIsotropicStatement

section

@[expose] public section

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt


theorem _root_.GlobalTheory.T.exists_opposite_transversal_isotropic : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) {X : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (y : D.La →ₗ[𝓞 E] X) (n : ℕ), 0 < n → Cois D y n → ∀ Z Z₀ : Submodule (𝓞 E) D.La, IsOpp D Z Z₀ →
    Module.finrank (𝓞 E) Z = Module.finrank (𝓞 E) X →
    ∃ Z' : Submodule (𝓞 E) D.La, IsOpp D Z Z' ∧ ∀ x, ∃ b ∈ Z', ∃ e, y b = x + n • e := by
  first | exact @GlobalTheory.LowFilt.exists_opp_transv | exact GlobalTheory.LowFilt.exists_opp_transv | (intros; apply GlobalTheory.LowFilt.exists_opp_transv <;> assumption)
end
end
end
