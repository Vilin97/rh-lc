module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExponentsThetaSystemBigOddPrimeStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
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
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymplecticLevelAfterFiniteExtensionBase
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaSystemSpreadOfLevelFractionFieldStatement
public import Development.AbelianVarietyTheory.Definitions.Degenerations.ArithBase
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisedCoverPullbackSemiAbelianModel
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ZarhinNormalProjectiveModelExistsProof

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOddPrimeIsUnitOfCompleteNormalCharZeroBase

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory

theorem exists_odd_prime_isUnit_of_base :
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∃ n : ℕ, n.Prime ∧ Odd n ∧ IsUnit (n : R) := by
  intro R _ _ _ _
  by_cases h3 : IsUnit ((3 : ℕ) : R)
  · exact ⟨3, Nat.prime_three, ⟨1, rfl⟩, h3⟩
  by_cases h5 : IsUnit ((5 : ℕ) : R)
  · exact ⟨5, by norm_num, ⟨2, rfl⟩, h5⟩
  exfalso
  have m3 : ((3 : ℕ) : R) ∈ maximalIdeal R := (mem_maximalIdeal _).2 h3
  have m5 : ((5 : ℕ) : R) ∈ maximalIdeal R := (mem_maximalIdeal _).2 h5
  have m2 : ((5 : ℕ) : R) - ((3 : ℕ) : R) ∈ maximalIdeal R := Ideal.sub_mem _ m5 m3
  have m1 : ((3 : ℕ) : R) - (((5 : ℕ) : R) - ((3 : ℕ) : R)) ∈ maximalIdeal R := Ideal.sub_mem _ m3 m2
  have e : ((3 : ℕ) : R) - (((5 : ℕ) : R) - ((3 : ℕ) : R)) = 1 := by push_cast; ring
  rw [e] at m1
  exact (mem_maximalIdeal _).1 m1 isUnit_one

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOddPrimeIsUnitOfCompleteNormalCharZeroBaseStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_odd_prime_isUnit_of_completeNormalCharZeroBase : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∃ n : ℕ, n.Prime ∧ Odd n ∧ IsUnit (n : R) := by
  first | exact @GlobalTheory.exists_odd_prime_isUnit_of_base | exact GlobalTheory.exists_odd_prime_isUnit_of_base | (intros; apply GlobalTheory.exists_odd_prime_isUnit_of_base <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymplecticLevelAfterFiniteExtensionBaseStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_symplecticLevel_after_finiteExtension_base : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (A : PolAV (Sp (FractionRing R))), (letI := A.isAb.comm; GlobalTheory.ZH.HypS A.A A.L) → ∀ m : ℕ, 1 ≤ m → IsUnit (m : R) → ∃ (R₁ : Type) (_ : CommRing R₁) (_ : IsDomain R₁) (_ : IsLocalRing R₁) (ρ : R →+* R₁) (A₁ : PolAV (Sp (FractionRing R₁))) (a : A₁.A.left ⟶ A.A.left) (ζ : R₁ˣ) (_ : ReciprocityTheory.ChartRestriction.G.Out.Level A₁ m (unitOn (Units.map (algebraMap R₁ (FractionRing R₁)).toMonoidHom ζ))), FinExt ρ ∧ IsFib ρ A A₁ a ∧ A₁.g = A.g ∧ (letI := A₁.isAb.comm; GlobalTheory.ZH.HypS A₁.A A₁.L) := by
  first | exact @GlobalTheory.MumLevel.exists_level_finExt | exact GlobalTheory.MumLevel.exists_level_finExt | (intros; apply GlobalTheory.MumLevel.exists_level_finExt <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTupleThetaConstantRatiosGenerateField

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open Classical

namespace GlobalTheory.ZH

theorem thetaSys_gen_tuple (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : GlobalTheory.ZH.ThetaSys o Ω) :
    ∃ (J₀ : Type) (_ : Fintype J₀) (t₀ : J₀ → Ω), (∃ i, t₀ i ≠ 0) ∧
      Module.Finite (Subfield.closure (Set.range (algebraMap o Ω) ∪
        {x | ∃ i j : S.Gam × J₀, x = S.th j.1 * t₀ j.2 / (S.th i.1 * t₀ i.2)})) Ω := by
  obtain ⟨s, hs⟩ := S.fg
  obtain ⟨x₀, hx₀⟩ := S.th_ne
  let t₀ : Option s → Ω := fun i => match i with | none => 1 | some y => (y : Ω)
  refine ⟨Option s, inferInstance, t₀, ⟨none, one_ne_zero⟩, ?_⟩
  set K := Subfield.closure (Set.range (algebraMap o Ω) ∪
        {x | ∃ i j : S.Gam × Option s, x = S.th j.1 * t₀ j.2 / (S.th i.1 * t₀ i.2)}) with hK
  have hbase : ∀ a : o, algebraMap o Ω a ∈ K := fun a =>
    Subfield.subset_closure (Or.inl ⟨a, rfl⟩)
  have hgen : ∀ y ∈ s, y ∈ K := by
    intro y hy
    apply Subfield.subset_closure
    refine Or.inr ⟨(x₀, none), (x₀, some ⟨y, hy⟩), ?_⟩
    simp only [t₀, mul_one]
    field_simp
  let KA : Subalgebra o Ω :=
    { K.toSubring with algebraMap_mem' := hbase }
  have hR : S.R ≤ KA := by
    rw [← hs]
    exact Algebra.adjoin_le (fun y hy => hgen y hy)
  have hall : ∀ x : Ω, x ∈ K := by
    intro x
    obtain ⟨a, ha, b, hb, rfl⟩ := S.frac x
    exact K.div_mem (hR ha) (hR hb)
  refine ⟨⟨{1}, eq_top_iff.mpr fun x _ => ?_⟩⟩
  simp only [Finset.coe_singleton]
  rw [Submodule.mem_span_singleton]
  exact ⟨⟨x, hall x⟩, by simp [Algebra.smul_def]; rfl⟩

end GlobalTheory.ZH
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTupleThetaConstantRatiosGenerateFieldStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open Classical

theorem _root_.GlobalTheory.T.exists_tuple_thetaConstant_ratios_generate_field : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : GlobalTheory.ZH.ThetaSys o Ω), ∃ (J₀ : Type) (_ : Fintype J₀) (t₀ : J₀ → Ω), (∃ i, t₀ i ≠ 0) ∧ Module.Finite (Subfield.closure (Set.range (algebraMap o Ω) ∪ {x | ∃ i j : S.Gam × J₀, x = S.th j.1 * t₀ j.2 / (S.th i.1 * t₀ i.2)})) Ω := by
  first | exact @GlobalTheory.ZH.thetaSys_gen_tuple | exact GlobalTheory.ZH.thetaSys_gen_tuple | (intros; apply GlobalTheory.ZH.thetaSys_gen_tuple <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisedCoverPullbackSemiAbelianModelStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open Classical

theorem _root_.GlobalTheory.T.exists_uniformised_cover_pullback_semiAbelian_model : ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁] (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [GlobalTheory.ZH.ArithBase o Ω] (S : GlobalTheory.ZH.ThetaSys o Ω) (ρS : S.Real) (M : GlobalTheory.ZH.RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), S.Over₀ M U₀ → GlobalTheory.ZH.ZHOut ρS M U₀ EE → ∀ (b : o →+* R₁) (e : Ω →+* FractionRing R₁), (∀ x : o, e (algebraMap o Ω x) = algebraMap R₁ (FractionRing R₁) (b x)) → ∀ (A₁ : PolAV (Sp (FractionRing R₁))) (φ : A₁.A.left ⟶ ρS.P.A.left), IsGrpPullback A₁.A ρS.P.A (spMap (e.comp S.R.val.toRingHom)) φ → LBIso A₁.L (ρS.P.L.pull φ) → ∃ C : UCover R₁, C.A = A₁ := by
  first | exact @GlobalTheory.Mum.exists_uCover_of_zhOut | exact GlobalTheory.Mum.exists_uCover_of_zhOut | (intros; apply GlobalTheory.Mum.exists_uCover_of_zhOut <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisedCoverFiniteExtOfSymmetric

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_uCover : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (A : PolAV (Sp (FractionRing R))), (letI := A.isAb.comm; GlobalTheory.ZH.HypS A.A A.L) → ∃ (R₁ : Type) (_ : CommRing R₁) (_ : IsDomain R₁) (_ : IsLocalRing R₁) (ρ : R →+* R₁) (C : UCover R₁) (a : C.A.A.left ⟶ A.A.left), FinExt ρ ∧ IsFib ρ A C.A a := by
  intro R _ _ _ hR A hA
  obtain ⟨n, hn, hno, hnu⟩ := GlobalTheory.T.exists_odd_prime_isUnit_of_completeNormalCharZeroBase R hR
  obtain ⟨k, j, hk, hj, hbig⟩ := GlobalTheory.T.exists_exponents_thetaSystem_big_odd_prime A.g n hn hno
  have hmu : IsUnit (((n ^ j * (n ^ k) ^ 2) ^ 2 : ℕ) : R) := by
    push_cast; exact ((hnu.pow _).mul ((hnu.pow _).pow _)).pow _
  obtain ⟨R₁, _, _, _, ρ, A₁, a, ζ, lev, hfin, hfib, hg, hS⟩ :=
    GlobalTheory.T.exists_symplecticLevel_after_finiteExtension_base R hR A hA _ (Nat.one_le_iff_ne_zero.2 (pow_ne_zero _ (mul_ne_zero (pow_ne_zero _ hn.ne_zero) (pow_ne_zero _ (pow_ne_zero _ hn.ne_zero))))) hmu
  haveI : CharZero R₁ := ⟨fun x y h => by
    have := hR.2
    exact Nat.cast_injective (hfin.2.1 (by simpa using h))⟩
  have hnu₁ : IsUnit (n : R₁) := by simpa using hnu.map ρ
  obtain ⟨o, Ω, _, _, _, _, S, ρS, b, e, φ, hSg, hSN, hSr, hb, hcart, hlb⟩ :=
    GlobalTheory.T.exists_thetaSystem_spread_of_level_fractionField R₁ A₁ hS n k j hn hno hk hj hnu₁ ζ lev
  have hB : S.Big := hbig o Ω S (hSg.trans hg) hSN hSr
  obtain ⟨J₀, _, t₀, ht₀, hfin'⟩ := GlobalTheory.T.exists_tuple_thetaConstant_ratios_generate_field o Ω S
  obtain ⟨M, U₀, EE, hO, -, -, ⟨Z⟩⟩ := GlobalTheory.zhSt_holds o Ω S ρS hB J₀ t₀ ht₀ hfin'
  obtain ⟨C, hC⟩ := GlobalTheory.T.exists_uniformised_cover_pullback_semiAbelian_model R₁ o Ω S ρS M U₀ EE hO Z b e hb A₁ φ hcart hlb
  subst hC
  exact ⟨R₁, _, _, _, ρ, C, a, hfin, hfib⟩

end GlobalTheory.Mum
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisedCoverFiniteExtOfSymmetricStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_uniformised_cover_finite_ext_of_symmetric : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (A : PolAV (Sp (FractionRing R))), (letI := A.isAb.comm; GlobalTheory.ZH.HypS A.A A.L) → ∃ (R₁ : Type) (_ : CommRing R₁) (_ : IsDomain R₁) (_ : IsLocalRing R₁) (ρ : R →+* R₁) (C : UCover R₁) (a : C.A.A.left ⟶ A.A.left), FinExt ρ ∧ IsFib ρ A C.A a := by
  first | exact @GlobalTheory.Mum.exists_uCover | exact GlobalTheory.Mum.exists_uCover | (intros; apply GlobalTheory.Mum.exists_uCover <;> assumption)
end
end
