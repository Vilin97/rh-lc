module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GenericCentreSpecializes
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.PropZ
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsGenOfIsVBOne
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DvrModelOfNumberFieldPlace
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
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.FactPrimes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsGenOfIsVBOne
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.Topology.Sheaves.Presheaf
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteTypeOverIntegersModelStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeGeneratorInvertConstantStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProperDvrModelLatticeValuationStatement
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterGoodD
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.DvrModelOfNumberFieldPlaceStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.dvr_model_of_number_field_place : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (κ : Type) [Finite κ] (x : κ → Ω) (F' : Type) [Field F'] [NumberField F'] (ψ : F' →+* Ω) (v : HeightOneSpectrum (𝓞 F')) (π : F'), (∀ q : X, genPt ξ ⤳ q) → CoordTie ℤ ξ x → NormalCpt ξ → v.valuation F' π = WithZero.exp (-1 : ℤ) → ∃ (O : Type) (_ : CommRing O) (_ : IsDomain O) (_ : IsDiscreteValuationRing O) (_ : Algebra O Ω) (X' : Scheme.{0}) (ξ' : Spec (CommRingCat.of Ω) ⟶ X') (s : X' ⟶ Spec (CommRingCat.of O)) (g : X' ⟶ X) (ϖ : O), IsProper s ∧ Irreducible ϖ ∧ Function.Injective (algebraMap O Ω) ∧ ξ' ≫ s = Spec.map (CommRingCat.ofHom (algebraMap O Ω)) ∧ ξ' ≫ g = ξ ∧ IsCptGen ξ' ∧ (∀ q' : X', genPt ξ' ⤳ q') ∧ algebraMap O Ω ϖ = ψ π ∧ (∀ a : Ω, a ∈ (algebraMap O Ω).range ↔ ∃ b : F', v.valuation F' b ≤ 1 ∧ ψ b = a) ∧ (∀ (p' : Cpt ξ') (p : Cpt ξ), p.1 = g p'.1 → ∀ a : Ω, a ∈ regAt ξ' p' ↔ a ∈ regAt ξ p) ∧ ∀ p : Cpt ξ, (∀ a : F', v.valuation F' a ≤ 1 → ψ a ∈ regAt ξ p) → ∃ p' : Cpt ξ', g p'.1 = p.1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.LocModel.exists_localisation | exact GlobalTheory.CompanionTheory.Ar.Flat.LocModel.exists_localisation | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.LocModel.exists_localisation <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsPrimeDividingUniformizer

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Rescar

theorem exists_prime_natCast_mem {R : Type*} [CommRing R] (P : Ideal R) [hP : P.IsPrime]
    (n : ℕ) (hn : n ≠ 0) (hmem : (n : R) ∈ P) : ∃ ℓ : ℕ, ℓ.Prime ∧ (ℓ : R) ∈ P := by
  induction n using Nat.recOnMul with
  | zero => exact absurd rfl hn
  | one =>
    exact absurd (by simpa using hmem : (1 : R) ∈ P) (fun h => hP.ne_top ((Ideal.eq_top_iff_one P).2 h))
  | prime p hp => exact ⟨p, hp, hmem⟩
  | mul a b iha ihb =>
    have ha : a ≠ 0 := fun h => hn (by simp [h])
    have hb : b ≠ 0 := fun h => hn (by simp [h])
    rw [Nat.cast_mul] at hmem
    rcases hP.mem_or_mem hmem with h | h
    · exact iha ha h
    · exact ihb hb h

theorem exists_prime_div_uniformiser (F' : Type) [Field F'] [NumberField F']
    (v : HeightOneSpectrum (𝓞 F')) (π : F') (hπ : v.valuation F' π = WithZero.exp (-1 : ℤ)) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ v.valuation F' ((ℓ : F') / π) ≤ 1 := by
  have hne : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  have hmem : ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 F') ∈ v.asIdeal := by
    simpa using Ideal.absNorm_mem v.asIdeal
  obtain ⟨ℓ, hℓ, hℓmem⟩ := exists_prime_natCast_mem v.asIdeal _ hne hmem
  refine ⟨ℓ, hℓ, ?_⟩
  have hlt : v.valuation F' (ℓ : F') < 1 := by
    have := (v.valuation_lt_one_iff_mem (K := F') (ℓ : 𝓞 F')).2 hℓmem
    simpa using this
  have hle : v.valuation F' (ℓ : F') ≤ WithZero.exp (-1 : ℤ) := by
    rcases eq_or_ne (v.valuation F' (ℓ : F')) 0 with h0 | h0
    · rw [h0]; exact zero_le'
    · obtain ⟨a, ha⟩ : ∃ a : ℤ, v.valuation F' (ℓ : F') = WithZero.exp a :=
        ⟨WithZero.log _, (WithZero.exp_log h0).symm⟩
      rw [ha] at hlt ⊢
      have h1 : a < 0 := by
        rw [← WithZero.exp_zero] at hlt
        exact WithZero.exp_lt_exp.1 hlt
      exact WithZero.exp_le_exp.2 (by omega)
  rw [map_div₀, hπ]
  exact div_le_one_of_le₀ hle zero_le'

end GlobalTheory.CompanionTheory.Ar.Rescar
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsPrimeDividingUniformizerStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.exists_prime_dividing_uniformizer : ∀ (F' : Type) [Field F'] [NumberField F'] (v : HeightOneSpectrum (𝓞 F')) (π : F'), v.valuation F' π = WithZero.exp (-1 : ℤ) → ∃ ℓ : ℕ, ℓ.Prime ∧ v.valuation F' ((ℓ : F') / π) ≤ 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Rescar.exists_prime_div_uniformiser | exact GlobalTheory.CompanionTheory.Ar.Rescar.exists_prime_div_uniformiser | (intros; apply GlobalTheory.CompanionTheory.Ar.Rescar.exists_prime_div_uniformiser <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.CptFlatInputsOfPropZ

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.CptIn

theorem orderAt_of_unit {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {L : Lat ξ Ω} {σ ϖ ϖ' : Ω}
    {M : ℕ} {a : ℤ} {p : Cpt ξ} (h : OrderAt L σ ϖ M a p) (hu : unitAt ξ p (ϖ / ϖ')) : OrderAt L σ ϖ' M a p := by
  obtain ⟨e, c, he, hL, hσ, hc⟩ := h
  refine ⟨e, c, he, hL, hσ, ?_⟩
  have h0 : ϖ ≠ 0 := fun h => hu.1 (by simp [h])
  have h1 : ϖ' ≠ 0 := fun h => hu.1 (by simp [h])
  have hz : ∀ n : ℤ, unitAt ξ p ((ϖ / ϖ') ^ n) := fun n => by
    cases n with
    | ofNat m => simpa using ZUnit.pow hu m
    | negSucc m => simpa using ZUnit.inv (ZUnit.pow hu (m + 1))
  have : c ^ M / ϖ' ^ a = c ^ M / ϖ ^ a * (ϖ / ϖ') ^ a := by
    rw [div_zpow]
    field_simp
  rw [this]
  exact ZUnit.mul hc (hz a)

theorem exists_orders (hZ : PropZ) {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    {κ : Type} [Finite κ] {x : κ → Ω} {F' : Type} [Field F'] [NumberField F'] (ψ : F' →+* Ω)
    (hcl : ∀ x : Ω, (∃ f : Polynomial F', f ≠ 0 ∧ f.eval₂ ψ x = 0) → x ∈ Set.range ψ)
    (hall : ∀ q : X, genPt ξ ⤳ q) (ht : CoordTie ℤ ξ x) (hN : NormalCpt ξ) (L : Lat ξ Ω) (σ : Ω)
    (hL : L.IsVB 1 ⊤) (hg : ∀ p ∈ genFibre ℤ ξ, L.IsGenAt p σ)
    (hp : ∀ ℓ : ℕ, ℓ.Prime → TrivMod L (ℓ : Ω) ∨ NumTrivMod L (ℓ : Ω)) :
    ∃ r : HeightOneSpectrum (𝓞 F') →₀ ℚ, ∀ (v : HeightOneSpectrum (𝓞 F')) (π : F'),
      v.valuation F' π = WithZero.exp (-1 : ℤ) → ∃ (m : ℕ) (k : ℤ), 0 < m ∧ (k : ℚ) = m * r v ∧ ∀ p : Cpt ξ,
        (∀ a : F', v.valuation F' a ≤ 1 → ψ a ∈ regAt ξ p) → OrderAt L σ (ψ π) m k p := by
  classical
  have hchar : CharZero Ω := charZero_of_injective_ringHom ψ.injective
  have hplace : ∀ (v : HeightOneSpectrum (𝓞 F')) (π : F'), v.valuation F' π = WithZero.exp (-1 : ℤ) →
      ∃ (M : ℕ) (a : ℤ), 0 < M ∧ ∀ p : Cpt ξ, (∀ a : F', v.valuation F' a ≤ 1 → ψ a ∈ regAt ξ p) →
        OrderAt L σ (ψ π) M a p := by
    intro v π hπ
    obtain ⟨O, _, _, _, _, X', ξ', s, g, ϖ, hs, hϖ, hinj, hξs, hξg, hgen', hall', hϖπ, hrange, hreg, hsurj⟩ :=
      GlobalTheory.T.dvr_model_of_number_field_place X Ω ξ κ x F' ψ v π hall ht hN hπ
    obtain ⟨ℓ, hℓ, hℓv⟩ := GlobalTheory.T.exists_prime_dividing_uniformizer F' v π hπ
    obtain ⟨u, hu⟩ : ∃ u : O, algebraMap O Ω u = ψ ((ℓ : F') / π) :=
      (hrange _).2 ⟨_, hℓv, rfl⟩
    have hπ0 : π ≠ 0 := by
      rintro rfl
      simp at hπ
      exact WithZero.exp_ne_zero hπ.symm
    have hcc : ConstClosed O Ω := by
      intro a ha
      obtain ⟨f, hf, hfa⟩ := ha
      have hlift : f.map (algebraMap O Ω) ∈ Polynomial.lifts ψ := by
        rw [Polynomial.lifts_iff_coeff_lifts]
        intro n
        rw [Polynomial.coeff_map]
        obtain ⟨b, -, hb⟩ := (hrange _).1 ⟨f.coeff n, rfl⟩
        exact ⟨b, hb⟩
      obtain ⟨f', hf'⟩ := (Polynomial.mem_lifts _).1 hlift
      have hne : f' ≠ 0 := by
        rintro rfl
        rw [Polynomial.map_zero] at hf'
        exact hf ((Polynomial.map_eq_zero_iff hinj).1 hf'.symm)
      obtain ⟨b, rfl⟩ := hcl a ⟨f', hne, by
        rw [← Polynomial.eval_map, hf', Polynomial.eval_map]
        exact hfa⟩
      by_cases hb : v.valuation F' b ≤ 1
      · obtain ⟨x₀, hx₀⟩ := (hrange (ψ b)).2 ⟨b, hb, rfl⟩
        exact ⟨x₀, 1, one_ne_zero, by rw [map_one, mul_one]; exact hx₀.symm⟩
      · have hb0 : b ≠ 0 := by
          rintro rfl
          simp at hb
        have hb' : v.valuation F' b⁻¹ ≤ 1 := by
          rw [map_inv₀]
          exact inv_le_one_of_one_le₀ (le_of_not_ge hb)
        obtain ⟨y₀, hy₀⟩ := (hrange (ψ b⁻¹)).2 ⟨b⁻¹, hb', rfl⟩
        refine ⟨1, y₀, ?_, ?_⟩
        · rintro rfl
          rw [map_zero] at hy₀
          exact inv_ne_zero hb0 ((map_eq_zero ψ).1 hy₀.symm)
        · rw [hy₀, ← map_mul, mul_inv_cancel₀ hb0, map_one, map_one]
    have hℓu : (ℓ : Ω) = algebraMap O Ω (ϖ * u) := by
      rw [map_mul, hϖπ, hu, ← map_mul, mul_div_cancel₀ _ hπ0, map_natCast]
    obtain ⟨M, a, hM, h⟩ := @GlobalTheory.T.proper_dvr_model_lattice_valuation X X' Ω _ _ ξ ξ' g O _ _ _ _ s hs ϖ L σ ℓ u hZ hϖ hinj hξs hξg ht.gen hgen' hall'
      hN hcc hreg hL hg hℓu (hp ℓ hℓ)
    refine ⟨M, a, hM, fun p hv => ?_⟩
    have := h p (hsurj p hv)
    rwa [hϖπ] at this
  obtain ⟨s, hs1, hs2, hs3⟩ := GlobalTheory.T.finite_type_over_integers_model X Ω ξ κ x hall ht
  obtain ⟨n, hn, hgn⟩ := @GlobalTheory.T.lattice_generator_invert_constant X Ω _ ξ ℤ _ _ _ s _ hs1 hs2 hs3 (Int.cast_injective) ht.gen L Set.univ 1 σ
    one_ne_zero (fun _ _ => trivial) hL hg
  have hn' : ((n : F'))⁻¹ ≠ 0 := inv_ne_zero (by exact_mod_cast hn)
  have hfin := HeightOneSpectrum.Support.finite (𝓞 F') ((n : F'))⁻¹
  choose π hπ using fun v : HeightOneSpectrum (𝓞 F') => v.valuation_exists_uniformizer F'
  choose M a hM hord using fun v => hplace v (π v) (hπ v)
  let T := HeightOneSpectrum.Support (𝓞 F') ((n : F'))⁻¹
  let r₀ : HeightOneSpectrum (𝓞 F') → ℚ := fun v => if v ∈ T then (a v : ℚ) / M v else 0
  have hr₀ : (Function.support r₀).Finite := hfin.subset fun v hv => by
    by_contra h
    exact hv (if_neg h)
  refine ⟨Finsupp.ofSupportFinite r₀ hr₀, fun v π' hπ' => ?_⟩
  have hrv : (Finsupp.ofSupportFinite r₀ hr₀) v = r₀ v := rfl
  rw [hrv]
  by_cases hv : v ∈ T
  · have hMv : (M v : ℚ) ≠ 0 := by exact_mod_cast (hM v).ne'
    refine ⟨M v, a v, hM v, by simp only [r₀, if_pos hv]; field_simp, fun p hp => ?_⟩
    refine orderAt_of_unit (hord v p hp) ?_
    have h0 : π' ≠ 0 := by
      rintro rfl
      simp at hπ'
      exact WithZero.exp_ne_zero hπ'.symm
    have h1 : π v ≠ 0 := by
      intro h
      have := hπ v
      rw [h] at this
      simp at this
      exact WithZero.exp_ne_zero this.symm
    have e1 : v.valuation F' (π v / π') = 1 := by
      rw [map_div₀, hπ v, hπ', div_self (WithZero.exp_ne_zero)]
    have e2 : v.valuation F' (π v / π')⁻¹ = 1 := by rw [map_inv₀, e1, inv_one]
    rw [← map_div₀]
    exact ⟨(map_ne_zero ψ).2 (div_ne_zero h1 h0), hp _ e1.le, by rw [← map_inv₀]; exact hp _ e2.le⟩
  · refine ⟨1, 0, one_pos, by simp only [r₀, if_neg hv]; simp, fun p hp => ?_⟩
    have h1 : v.valuation F' (n : F') ≤ 1 := by
      have := v.valuation_le_one (K := F') (n : 𝓞 F')
      simpa using this
    have h2 : v.valuation F' ((n : F'))⁻¹ ≤ 1 := not_lt.1 hv
    have hu : unitAt ξ p (algebraMap ℤ Ω n) := by
      have e : algebraMap ℤ Ω n = ψ (n : F') := by simp
      rw [e]
      exact ⟨(map_ne_zero ψ).2 (by exact_mod_cast hn), hp _ h1, by rw [← map_inv₀]; exact hp _ h2⟩
    have := hgn p hu
    exact orderAt_one_zero.2 this

theorem isCoeffAt_of_smul {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {V : Type}
    [AddCommGroup V] [Module Ω V] {A B : Lat ξ V} {p q : ℕ} {a a' : ⋀[Ω]^p V} {b b' : ⋀[Ω]^q V} {x : Cpt ξ}
    {d₁ d₂ : Ω} (h₁ : d₁ ≠ 0) (h₂ : d₂ ≠ 0) (ea : a' = d₁ • a) (eb : b' = d₂ • b)
    (h : IsCoeffAt A B p q a' b' x 1) : IsCoeffAt A B p q a b x (d₁ / d₂)⁻¹ := by
  obtain ⟨α, β, hα, hβ, hA, hB, e⟩ := h
  rw [one_mul] at e
  subst e
  refine ⟨α * d₁, α * d₂, mul_ne_zero hα h₁, mul_ne_zero hα h₂, ?_, ?_, ?_⟩
  · rw [hA, ea, smul_smul]
  · rw [hB, eb, smul_smul]
  · field_simp

end GlobalTheory.CompanionTheory.Ar.Flat.CptIn
end
end
end
