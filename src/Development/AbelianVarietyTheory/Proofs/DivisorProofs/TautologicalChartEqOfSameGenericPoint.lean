module

public import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
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
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExtId
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComesFromBaseOfPullbackInjectiveDomains
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComesFromBaseOfRefinesPolarisedDataStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCDvrTwoEmbeddings
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelPointPairsLowerBase
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RefinePolarisedMonomialPeriodsMonomialData
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.XMemNonZeroDivisors
import Mathlib.Algebra.Order.Star.Int
import Development.AbelianVarietyTheory.Definitions.Divisors.ExtId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenOfIso
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericPointMapOverRingHomUniqueStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSemiAbelianOfIsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodPartMemTautologicalPointTorsionStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelFibrePowerPointEqOfMatchingLowerDataStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecMapCompEqOfCompInjectiveLocalSchemeStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureMapEqOfSameGenericImageModuliStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautologicalCoordsEqOfMatchingData
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautologicalLatticeIdentificationEqIdStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautologicalPointTransportFieldMapStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationPullbacksMatchTorsionPairs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc

-- Source module: Development.AbelianVarietyTheory.Definitions.Divisors.NotIsComplAtPowerSeriesC

section

@[expose] public section

noncomputable section
open IsLocalRing

namespace GlobalTheory.TChart

variable {o : Type} [CommRing o] {ζ : o} {g n : ℕ} {φ : GlobalTheory.LocM.InvFun ℤ}

theorem Taut.s_ne_zero (C : Taut ζ g n φ) (k : Fin C.m ⊕ Fin C.N) : C.s k ≠ 0 := by
  intro h
  have hflat : C.ψ.Flat := C.compl.2.2.1
  algebraize [C.ψ]

  have hreg : IsSMulRegular C.R
      (algebraMap (MvPolynomial (Fin C.m ⊕ Fin C.N) C.W) C.R (MvPolynomial.X k)) :=
    IsSMulRegular.of_flat (MvPolynomial.isRegular_X (n := k) (R := C.W)).left.isSMulRegular
  have h0 : algebraMap (MvPolynomial (Fin C.m ⊕ Fin C.N) C.W) C.R (MvPolynomial.X k) = 0 := h
  rw [h0] at hreg
  exact one_ne_zero (hreg (a₁ := (1 : C.R)) (a₂ := 0) (by simp))

end GlobalTheory.TChart
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComesFromBaseOfPullbackInjectiveDomainsStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

theorem _root_.GlobalTheory.T.comesFromBase_of_pullback_injective_domains : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) {I : Type} [Fintype I] (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ) (R : Type) [CommRing R] [IsDomain R] (V : Type) [CommRing V] [IsDomain V] (J : Ideal R) (D₀ : DegData R J) (ω : W →+* R) (s : I → R) (e : D₀.toPre.X ≃+ (Fin T.r → ℤ)) (β : D₀.toPre.P.A.left ⟶ T.B.left) (ββ : (G2 D₀.toPre.P.A).left ⟶ (G2 T.B).left) (w : LB.Iso (abelian₂ D₀.toPre.P.A D₀.toPre.P.L) ((abelian₂ T.B T.M.L).pull ββ)) (f : R →+* V) (D : DegPre V) (hD : IsPullDeg f D₀.toPre D), Function.Injective f → From T ω s ε n D₀.toPre e β ββ w → ∃ ββ' w', From T (f.comp ω) (fun i => f (s i)) ε n D (hD.xe.trans e) ((hD.e.hom.left ≫ pullback.fst D₀.toPre.P.A.hom (specOf f)) ≫ β) ββ' w' := by
  first | exact @GlobalTheory.TInj.from_pull | exact GlobalTheory.TInj.from_pull | (intros; apply GlobalTheory.TInj.from_pull <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelPointPairsLowerBaseStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

theorem _root_.GlobalTheory.T.exists_level_point_pairs_lower_base : ∀ {o : Type} [CommRing o] {ζ : o} {n : ℕ} (L : LowBase ζ n), 1 ≤ n → ∀ (R : Type) [CommRing R] [IsDomain R] (V : Type) [CommRing V] [IsDomain V] (J : Ideal R) (J' : Ideal V) (D₀ : DegData R J) (D₁ D₂ : DegData V J') (ω : L.W →+* R) (β : D₀.toPre.P.A.left ⟶ L.T.B.left), IsGrpPullback D₀.toPre.P.A L.T.B (spMap ω) β → ∀ (f₁ f₂ : R →+* V) (hD₁ : IsPullDeg f₁ D₀.toPre D₁.toPre) (hD₂ : IsPullDeg f₂ D₀.toPre D₂.toPre) (F₀ : Type) [Field F₀] [IsAlgClosed F₀] [Algebra (FractionRing R) F₀] (F : Type) [Field F] [Algebra (FractionRing V) F] (j₁ j₂ : F₀ →+* F) (b : D₁.toPre.P.A ⟶ D₂.toPre.P.A) (φ : D₁.toPre.X ≃+ D₂.toPre.X), Ext f₁ j₁ → Ext f₂ j₂ → (∀ p₀ : QkPt D₀.toPre F₀ n, ∃ (p₁ : QkPt D₁.toPre F n) (p₂ : QkPt D₂.toPre F n), p₁.y = hD₁.xe.symm p₀.y ∧ Tr f₁ hD₁ j₁ p₀.g p₁.g ∧ p₂.y = hD₂.xe.symm p₀.y ∧ Tr f₂ hD₂ j₂ p₀.g p₂.g ∧ QImg b φ p₁ p₂) → (∀ l : Fin L.h ⊕ Fin L.h → ℤ, ∃ (p₁ : QkPt D₁.toPre F n) (p₂ : QkPt D₂.toPre F n), p₁.y = 0 ∧ p₁.g.b.left ≫ ((hD₁.e.hom.left ≫ pullback.fst D₀.toPre.P.A.hom (specOf f₁)) ≫ β) ≫ L.β = (TF (R := V) F).hom ≫ spMap (f₁.comp ω) ≫ L.u ≫ (GlobalTheory.LowChart.powA L.F L.T.r).hom ≫ (L.F.univ.lev l).left ∧ p₂.y = 0 ∧ p₂.g.b.left ≫ ((hD₂.e.hom.left ≫ pullback.fst D₀.toPre.P.A.hom (specOf f₂)) ≫ β) ≫ L.β = (TF (R := V) F).hom ≫ spMap (f₂.comp ω) ≫ L.u ≫ (GlobalTheory.LowChart.powA L.F L.T.r).hom ≫ (L.F.univ.lev l).left ∧ QImg b φ p₁ p₂) := by
  exact @GlobalTheory.TInj.exists_level_pairs
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRefinementTautologicalChartFiniteExtension

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

theorem GlobalTheory.TInj.taut_refine : ∀ {o : Type} [CommRing o] {ζ : o} {g n : ℕ} {φ : InvFun ℤ}, 1 ≤ n → ∀ C : Taut ζ g n φ, IsCN C.R → ∃ (R₁ : Type) (_ : CommRing R₁) (_ : IsDomain R₁) (_ : IsLocalRing R₁) (ρ : C.R →+* R₁) (D : DegData R₁ (maximalIdeal R₁)) (e' : D.toPre.X ≃+ C.Q.X), IsCN R₁ ∧ Function.Injective ρ ∧ ρ.Finite ∧ IsLocalHom ρ ∧ Refines C.Q ρ D.toPre e' := by
  intro o _ ζ g n φ hn C hCN
  obtain ⟨hmono, -, hcone, hdef, ht0⟩ := GlobalTheory.TChart.Taut.monomial_chart g n φ hn C
  have hsymm : ∀ i y z, ((n : ℤ) • C.δ i) y z = ((n : ℤ) • C.δ i) z y := fun i y z => by
    simp only [LinearMap.smul_apply, mem_balForms_int.1 (hcone.mem i) y z]
  have hnn : ∀ i y, 0 ≤ ((n : ℤ) • C.δ i) y y := fun i y => by
    simp only [LinearMap.smul_apply, smul_eq_mul]
    exact mul_nonneg (by positivity) (hcone.nonneg i y)
  have hdef' : ∀ y, y ≠ 0 → ∃ i, 0 < ((n : ℤ) • C.δ i) y y := fun y hy => by
    obtain ⟨i, hi⟩ := hdef y hy
    refine ⟨i, ?_⟩
    simp only [LinearMap.smul_apply, smul_eq_mul]
    exact mul_pos (by exact_mod_cast hn) hi
  obtain ⟨R', _, _, _, ρ, -, D, e, hCN', hinj, hfin, hloc, -, href, -⟩ :=
    GlobalTheory.PolDeg.refine_monomial_of_polarised C.R C.Q C.m C.t (fun i => (n : ℤ) • C.δ i) hCN hmono C.bd ht0 hsymm hnn hdef'
  exact ⟨R', inferInstance, inferInstance, inferInstance, ρ, D, e, hCN', hinj, hfin, hloc, href⟩
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRefinementTautologicalChartFiniteExtensionStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

theorem _root_.GlobalTheory.T.exists_refinement_tautologicalChart_finiteExtension : ∀ {o : Type} [CommRing o] {ζ : o} {g n : ℕ} {φ : InvFun ℤ}, 1 ≤ n → ∀ C : Taut ζ g n φ, IsCN C.R → ∃ (R₁ : Type) (_ : CommRing R₁) (_ : IsDomain R₁) (_ : IsLocalRing R₁) (ρ : C.R →+* R₁) (D : DegData R₁ (maximalIdeal R₁)) (e' : D.toPre.X ≃+ C.Q.X), IsCN R₁ ∧ Function.Injective ρ ∧ ρ.Finite ∧ IsLocalHom ρ ∧ Refines C.Q ρ D.toPre e' := by
  first | exact @GlobalTheory.TInj.taut_refine | exact GlobalTheory.TInj.taut_refine | (intros; apply GlobalTheory.TInj.taut_refine <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautologicalCoordsEqOfMatchingDataStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

theorem _root_.GlobalTheory.T.tautological_coords_eq_of_matching_data : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) {I : Type} [Fintype I] (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ) (V : Type) [CommRing V] [IsDomain V] (ω : W →+* V) (D₁ D₂ : DegPre V) (s₁ : I → V) (e₁ : D₁.X ≃+ (Fin T.r → ℤ)) (β₁ : D₁.P.A.left ⟶ T.B.left) (ββ₁ : (G2 D₁.P.A).left ⟶ (G2 T.B).left) (w₁ : LB.Iso (abelian₂ D₁.P.A D₁.P.L) ((abelian₂ T.B T.M.L).pull ββ₁)) (s₂ : I → V) (e₂ : D₂.X ≃+ (Fin T.r → ℤ)) (β₂ : D₂.P.A.left ⟶ T.B.left) (ββ₂ : (G2 D₂.P.A).left ⟶ (G2 T.B).left) (w₂ : LB.Iso (abelian₂ D₂.P.A D₂.P.L) ((abelian₂ T.B T.M.L).pull ββ₂)) (b : D₁.P.A ⟶ D₂.P.A) (φ : D₁.X ≃+ D₂.X) (F : Type) [Field F] [Algebra (FractionRing V) F], 1 ≤ n → (∃ ε₀ : Module.Basis I ℤ (balForms (id : ℤ → ℤ) (Fin T.r → ℤ)), ∀ i, ε i = ε₀ i) → D₁.TauBimult → D₂.TauBimult → From T ω s₁ ε n D₁ e₁ β₁ ββ₁ w₁ → From T ω s₂ ε n D₂ e₂ β₂ ββ₂ w₂ → (∀ i, s₁ i ≠ 0) → (∀ i, s₂ i ≠ 0) → Match D₁ D₂ b φ F → (∀ y, e₂ (φ y) = e₁ y) → b.left ≫ β₂ = β₁ → (∀ a : Fin T.r → ℤ, ∃ (p₁ : QkPt D₁ F n) (p₂ : QkPt D₂ F n), p₁.y = e₁.symm a ∧ TautPt T ω s₁ ε n D₁ e₁ β₁ ββ₁ w₁ F a p₁.g ∧ p₂.y = e₂.symm a ∧ TautPt T ω s₂ ε n D₂ e₂ β₂ ββ₂ w₂ F a p₂.g ∧ QImg b φ p₁ p₂) → s₁ = s₂ := by
  first | exact @GlobalTheory.TInj.coords_eq_of_match | exact GlobalTheory.TInj.coords_eq_of_match | (intros; apply GlobalTheory.TInj.coords_eq_of_match <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationPullbacksMatchTorsionPairsStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

theorem _root_.GlobalTheory.T.uniformisation_pullbacks_match_torsionPairs : ∀ {X : Scheme.{0}} {g n : ℕ} {B : Type} [CommRing B] {ζ : B} {sX : X ⟶ Sp B} (c : SiegPre g n ζ sX), IsUnit ζ → 1 ≤ n → ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (J : Ideal R), AdmBase R J → ∀ (D₀ : DegData R J) (A₀ : PolAV (Sp (FractionRing R))) (G₀ : Over (Sp R)) [GrpObj G₀] [IsCommMonObj G₀] (U₀ : Unif J D₀ A₀ G₀), IsSemiAbelian G₀ → ∀ (y₀ : Sp (FractionRing R) ⟶ X) (α₀ : A₀.A.left ⟶ c.A.left), OverPt c A₀ y₀ α₀ → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (maximalIdeal V) V → ∀ f₁ f₂ : R →+* V, Function.Injective f₁ → Function.Injective f₂ → J.map f₁ ≤ maximalIdeal V → J.map f₂ ≤ maximalIdeal V → ∀ κ₁ κ₂ : Sp (FractionRing V) ⟶ Sp (FractionRing R), κ₁ ≫ jK R = jK V ≫ spMap f₁ → κ₂ ≫ jK R = jK V ≫ spMap f₂ → κ₁ ≫ y₀ = κ₂ ≫ y₀ → ∃ (D₁ D₂ : DegData V (maximalIdeal V)) (hD₁ : IsPullDeg f₁ D₀.toPre D₁.toPre) (hD₂ : IsPullDeg f₂ D₀.toPre D₂.toPre) (j₁ j₂ : (AlgebraicClosure (FractionRing R)) →+* (AlgebraicClosure (FractionRing V))) (b : D₁.toPre.P.A ⟶ D₂.toPre.P.A) (φ : D₁.toPre.X ≃+ D₂.toPre.X), Ext f₁ j₁ ∧ Ext f₂ j₂ ∧ Match D₁.toPre D₂.toPre b φ (AlgebraicClosure (FractionRing V)) ∧ (∀ p₀ : QkPt D₀.toPre (AlgebraicClosure (FractionRing R)) n, ∃ (p₁ : QkPt D₁.toPre (AlgebraicClosure (FractionRing V)) n) (p₂ : QkPt D₂.toPre (AlgebraicClosure (FractionRing V)) n), p₁.y = hD₁.xe.symm p₀.y ∧ Tr f₁ hD₁ j₁ p₀.g p₁.g ∧ p₂.y = hD₂.xe.symm p₀.y ∧ Tr f₂ hD₂ j₂ p₀.g p₂.g ∧ QImg b φ p₁ p₂) := by
  first | exact @GlobalTheory.TInj.pull_pair_match | exact GlobalTheory.TInj.pull_pair_match | (intros; apply GlobalTheory.TInj.pull_pair_match <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautologicalChartEqOfSameGenericPoint

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

noncomputable section
namespace GlobalTheory.TInj

theorem tautChart_eq_of_genPt : ∀ {g n : ℕ} {φ : InvFun ℤ}, 3 ≤ n → ∀ (F : SFam g n (zetaAway n)) (C : Taut (zetaAway n) g n φ) (G₁ : Over (Sp C.R)) [GrpObj G₁] [IsCommMonObj G₁] (y : Sp (FractionRing C.R) ⟶ F.X) (α₁ : pullback G₁.hom (jK C.R) ⟶ F.univ.A.left), C.IsFam F G₁ y α₁ → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (θ₁ θ₂ : C.R →+* R'), IsCN R' → Function.Injective θ₁ → Function.Injective θ₂ → IsLocalHom θ₁ → IsLocalHom θ₂ → ∀ (κ₁ κ₂ : Sp (FractionRing R') ⟶ Sp (FractionRing C.R)), κ₁ ≫ jK C.R = jK R' ≫ spMap θ₁ → κ₂ ≫ jK C.R = jK R' ≫ spMap θ₂ → κ₁ ≫ y = κ₂ ≫ y → spMap (θ₁.comp C.iw) ≫ C.u = spMap (θ₂.comp C.iw) ≫ C.u ∧ (θ₁.comp C.iw = θ₂.comp C.iw → ∀ k, θ₁ (C.s k) = θ₂ (C.s k)) := by
  intro g n φ hn F C G₁ _ _ y α₁ hC R' _ _ _ θ₁ θ₂ hR' hθ₁ hθ₂ hl₁ hl₂ κ₁ κ₂ hκ₁ hκ₂ hy
  obtain ⟨hsa, -, -, hM, hys⟩ := hC
  have hn1 : 1 ≤ n := by omega
  have hCN : IsCN C.R := hM.isCN
  obtain ⟨R₁, _, _, _, ρ, D, e', hR₁, hρ, hρf, hρl, href⟩ := GlobalTheory.T.exists_refinement_tautologicalChart_finiteExtension hn1 C hCN
  obtain ⟨β, ββ, w, hFrom⟩ := GlobalTheory.T.comesFromBase_of_refines_polarisedData C.T (fun k => (C.ε k : LinearMap.BilinForm ℤ (Fin C.T.r → ℤ))) n C.R R₁ ρ C.iw C.s C.Q C.e D.toPre e' hρ C.data href
  obtain ⟨G₀, _, _, π, A₀, U₀, hU⟩ := hM.unif R₁ ρ hR₁ hρ hρf D e' href
  obtain ⟨hπ, κρ, πK, α₀, α₂, hκρ, -, hA, hsq, hL, -⟩ := hU
  have hsa₀ : IsSemiAbelian G₀ := GlobalTheory.Mum.EvenDesc.isSemiAbelian_of_isGrpPullback hπ hsa
  obtain ⟨V, _, _, _, _, η', f₁, f₂, hVc, hη', hf₁, hf₂, hlf₁, hlf₂, hc₁, hc₂⟩ :=
    exists_cDvr_two_embeddings C.R R₁ R' ρ hρ hρf hR' θ₁ θ₂ hθ₁ hθ₂ hl₁ hl₂
  obtain ⟨κf₁, hκf₁⟩ := exists_genericMap hf₁
  obtain ⟨κf₂, hκf₂⟩ := exists_genericMap hf₂
  obtain ⟨κη, hκη⟩ := exists_genericMap hη'
  have e₁ : κf₁ ≫ κρ = κη ≫ κ₁ := GlobalTheory.T.genericPointMap_over_ringHom_unique (f₁.comp ρ) _ _
    (by rw [Category.assoc, hκρ, ← Category.assoc, hκf₁, Category.assoc, ← spMap_comp])
    (by rw [Category.assoc, hκ₁, ← Category.assoc, hκη, Category.assoc, ← spMap_comp, hc₁])
  have e₂ : κf₂ ≫ κρ = κη ≫ κ₂ := GlobalTheory.T.genericPointMap_over_ringHom_unique (f₂.comp ρ) _ _
    (by rw [Category.assoc, hκρ, ← Category.assoc, hκf₂, Category.assoc, ← spMap_comp])
    (by rw [Category.assoc, hκ₂, ← Category.assoc, hκη, Category.assoc, ← spMap_comp, hc₂])
  have hy₀ : κf₁ ≫ (κρ ≫ y) = κf₂ ≫ (κρ ≫ y) := by
    rw [← Category.assoc, e₁, Category.assoc, hy, ← Category.assoc, ← e₂, Category.assoc]
  have hmap : ∀ f : R₁ →+* V, IsLocalHom f → (maximalIdeal R₁).map f ≤ maximalIdeal V := fun f hf =>
    Ideal.map_le_iff_le_comap.mpr fun x hx => (mem_maximalIdeal _).2 (map_nonunit f x ((mem_maximalIdeal _).1 hx))
  haveI : CharZero R₁ := hR₁.2.2.2
  obtain ⟨D₁, D₂, hD₁, hD₂, j₁, j₂, b, φ', hE₁, hE₂, hMatch, hpairs⟩ :=
    GlobalTheory.T.uniformisation_pullbacks_match_torsionPairs F.univ (GlobalTheory.LowChart.isUnit_zetaAway n hn) hn1 R₁ (maximalIdeal R₁)
      ⟨hR₁.1, inferInstance, hR₁.2.1, hR₁.2.2.1⟩ D A₀ G₀ U₀ hsa₀ (κρ ≫ y) α₀ ⟨hA, α₂, hsq, hL⟩ V hVc f₁ f₂ hf₁ hf₂
      (hmap f₁ hlf₁) (hmap f₂ hlf₂) κf₁ κf₂ hκf₁ hκf₂ hy₀
  obtain ⟨ββ₁, w₁, hFrom₁⟩ := GlobalTheory.T.comesFromBase_of_pullback_injective_domains C.T (fun k => (C.ε k : LinearMap.BilinForm ℤ (Fin C.T.r → ℤ))) n R₁ V
    (maximalIdeal R₁) D (ρ.comp C.iw) (fun k => ρ (C.s k)) (e'.trans C.e) β ββ w f₁ D₁.toPre hD₁ hf₁ hFrom
  obtain ⟨ββ₂, w₂, hFrom₂⟩ := GlobalTheory.T.comesFromBase_of_pullback_injective_domains C.T (fun k => (C.ε k : LinearMap.BilinForm ℤ (Fin C.T.r → ℤ))) n R₁ V
    (maximalIdeal R₁) D (ρ.comp C.iw) (fun k => ρ (C.s k)) (e'.trans C.e) β ββ w f₂ D₂.toPre hD₂ hf₂ hFrom
  have hne₀ : ∀ k, ρ (C.s k) ≠ 0 := fun k => (map_ne_zero_iff ρ hρ).2 (C.s_ne_zero k)
  have htaut : ∀ a : Fin C.T.r → ℤ, ∃ (p₁ : QkPt D₁.toPre (AlgebraicClosure (FractionRing V)) n)
      (p₂ : QkPt D₂.toPre (AlgebraicClosure (FractionRing V)) n),
      p₁.y = (hD₁.xe.trans (e'.trans C.e)).symm a ∧
      TautPt C.T (f₁.comp (ρ.comp C.iw)) (fun k => f₁ (ρ (C.s k))) (fun k => (C.ε k : LinearMap.BilinForm ℤ (Fin C.T.r → ℤ))) n
        D₁.toPre (hD₁.xe.trans (e'.trans C.e)) ((hD₁.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf f₁)) ≫ β) ββ₁ w₁
        (AlgebraicClosure (FractionRing V)) a p₁.g ∧
      p₂.y = (hD₂.xe.trans (e'.trans C.e)).symm a ∧
      TautPt C.T (f₂.comp (ρ.comp C.iw)) (fun k => f₂ (ρ (C.s k))) (fun k => (C.ε k : LinearMap.BilinForm ℤ (Fin C.T.r → ℤ))) n
        D₂.toPre (hD₂.xe.trans (e'.trans C.e)) ((hD₂.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf f₂)) ≫ β) ββ₂ w₂
        (AlgebraicClosure (FractionRing V)) a p₂.g ∧ QImg b φ' p₁ p₂ := by
    intro a
    obtain ⟨p₀, hp₀y, hp₀⟩ := GlobalTheory.T.periodPart_mem_tautologicalPoint_torsion C.T (fun k => (C.ε k : LinearMap.BilinForm ℤ (Fin C.T.r → ℤ))) n R₁ D.toPre
      (ρ.comp C.iw) (fun k => ρ (C.s k)) (e'.trans C.e) β ββ w D.tau_bimult hFrom hne₀
      (AlgebraicClosure (FractionRing R₁)) a
    obtain ⟨p₁, p₂, hp₁y, hTr₁, hp₂y, hTr₂, hQ⟩ := hpairs p₀
    refine ⟨p₁, p₂, ?_, ?_, ?_, ?_, hQ⟩
    · rw [hp₁y, hp₀y]; rfl
    · exact GlobalTheory.T.tautologicalPoint_transport_fieldMap C.T _ n R₁ V (maximalIdeal R₁) D (ρ.comp C.iw) (fun k => ρ (C.s k)) (e'.trans C.e) β ββ w f₁
        D₁.toPre hD₁ ββ₁ w₁ hf₁ D₁.tau_bimult hFrom hFrom₁ _ _ j₁ hE₁ a p₀.g p₁.g hp₀ hTr₁
    · rw [hp₂y, hp₀y]; rfl
    · exact GlobalTheory.T.tautologicalPoint_transport_fieldMap C.T _ n R₁ V (maximalIdeal R₁) D (ρ.comp C.iw) (fun k => ρ (C.s k)) (e'.trans C.e) β ββ w f₂
        D₂.toPre hD₂ ββ₂ w₂ hf₂ D₂.tau_bimult hFrom hFrom₂ _ _ j₂ hE₂ a p₀.g p₂.g hp₀ hTr₂
  have hlev := GlobalTheory.T.exists_level_point_pairs_lower_base C.toLowBase hn1 R₁ V (maximalIdeal R₁) (maximalIdeal V) D D₁ D₂ (ρ.comp C.iw) β hFrom.1
    f₁ f₂ hD₁ hD₂ (AlgebraicClosure (FractionRing R₁)) (AlgebraicClosure (FractionRing V)) j₁ j₂ b φ' hE₁ hE₂ hpairs
  have hloc : ∀ f : R₁ →+* V, IsLocalHom f → ∀ x, x ∈ maximalIdeal C.R → f (ρ x) ∈ maximalIdeal V := fun f hf x hx =>
    (mem_maximalIdeal _).2 (map_nonunit f _ (map_nonunit ρ x ((mem_maximalIdeal _).1 hx)))
  have hbd₁ : ∀ k, f₁ (ρ (C.s (.inl k))) ∈ maximalIdeal V ∧ f₁ (ρ (C.s (.inl k))) ≠ 0 := fun k =>
    ⟨hloc f₁ hlf₁ _ (C.bd k), (map_ne_zero_iff f₁ hf₁).2 (hne₀ _)⟩
  have hbd₂ : ∀ k, f₂ (ρ (C.s (.inl k))) ∈ maximalIdeal V ∧ f₂ (ρ (C.s (.inl k))) ≠ 0 := fun k =>
    ⟨hloc f₂ hlf₂ _ (C.bd k), (map_ne_zero_iff f₂ hf₂).2 (hne₀ _)⟩
  have hu₁ : ∀ k, IsUnit (f₁ (ρ (C.s (.inr k)))) := fun k => ((C.tor k).map ρ).map f₁
  have hu₂ : ∀ k, IsUnit (f₂ (ρ (C.s (.inr k)))) := fun k => ((C.tor k).map ρ).map f₂
  have hfin1 := GlobalTheory.T.tautological_lattice_identification_eq_id C.T φ C.m C.N n (fun k => (C.ε k : LinearMap.BilinForm ℤ (Fin C.T.r → ℤ))) hn C.cone C.defin V
    D₁.toPre D₂.toPre (f₁.comp (ρ.comp C.iw)) (fun k => f₁ (ρ (C.s k))) (hD₁.xe.trans (e'.trans C.e))
    ((hD₁.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf f₁)) ≫ β) ββ₁ w₁
    (f₂.comp (ρ.comp C.iw)) (fun k => f₂ (ρ (C.s k))) (hD₂.xe.trans (e'.trans C.e))
    ((hD₂.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf f₂)) ≫ β) ββ₂ w₂ b φ' (AlgebraicClosure (FractionRing V))
    D₁.tau_bimult D₂.tau_bimult hFrom₁ hFrom₂ hbd₁ hu₁ hbd₂ hu₂ hMatch htaut
  have hb := GlobalTheory.T.structureMap_eq_of_same_genericImage_moduli F.s y C.b hys θ₁ θ₂ κ₁ κ₂ hκ₁ hκ₂ hy
  have k₁ : f₁.comp (ρ.comp C.iw) = η'.comp (θ₁.comp C.iw) := by
    rw [← RingHom.comp_assoc, hc₁, RingHom.comp_assoc]
  have k₂ : f₂.comp (ρ.comp C.iw) = η'.comp (θ₂.comp C.iw) := by
    rw [← RingHom.comp_assoc, hc₂, RingHom.comp_assoc]
  have hbase : (f₁.comp (ρ.comp C.iw)).comp C.toLowBase.T.b = (f₂.comp (ρ.comp C.iw)).comp C.toLowBase.T.b := by
    rw [k₁, k₂]
    change η'.comp (θ₁.comp C.b) = η'.comp (θ₂.comp C.b)
    rw [hb]
  obtain ⟨hU', hβeq⟩ := GlobalTheory.T.siegelFibrePower_point_eq_of_matching_lower_data C.toLowBase hn (GlobalTheory.LowChart.isUnit_zetaAway n hn) (isUnit_natCast (by omega))
    (fun k => (C.ε k : LinearMap.BilinForm ℤ (Fin C.T.r → ℤ))) V
    D₁.toPre D₂.toPre (f₁.comp (ρ.comp C.iw)) (fun k => f₁ (ρ (C.s k))) (hD₁.xe.trans (e'.trans C.e))
    ((hD₁.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf f₁)) ≫ β) ββ₁ w₁
    (f₂.comp (ρ.comp C.iw)) (fun k => f₂ (ρ (C.s k))) (hD₂.xe.trans (e'.trans C.e))
    ((hD₂.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf f₂)) ≫ β) ββ₂ w₂ b φ' (AlgebraicClosure (FractionRing V))
    D₁.tau_bimult D₂.tau_bimult hFrom₁ hFrom₂ hbase hMatch hfin1 htaut hlev
  refine ⟨GlobalTheory.T.specMap_comp_eq_of_comp_injective_localScheme C.u (θ₁.comp C.iw) (θ₂.comp C.iw) η' hη' (by rw [← k₁, ← k₂]; exact hU'), fun heq k => ?_⟩
  have hω : f₁.comp (ρ.comp C.iw) = f₂.comp (ρ.comp C.iw) := by rw [k₁, k₂, heq]
  have hβ₂ := hβeq hω
  rw [← hω] at hFrom₂ htaut
  have hs := GlobalTheory.T.tautological_coords_eq_of_matching_data C.T (fun k => (C.ε k : LinearMap.BilinForm ℤ (Fin C.T.r → ℤ))) n V (f₁.comp (ρ.comp C.iw))
    D₁.toPre D₂.toPre (fun k => f₁ (ρ (C.s k))) (hD₁.xe.trans (e'.trans C.e))
    ((hD₁.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf f₁)) ≫ β) ββ₁ w₁
    (fun k => f₂ (ρ (C.s k))) (hD₂.xe.trans (e'.trans C.e))
    ((hD₂.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf f₂)) ≫ β) ββ₂ w₂ b φ' (AlgebraicClosure (FractionRing V))
    hn1 ⟨C.ε, fun _ => rfl⟩ D₁.tau_bimult D₂.tau_bimult hFrom₁ hFrom₂ (fun k => (map_ne_zero_iff f₁ hf₁).2 (hne₀ k))
    (fun k => (map_ne_zero_iff f₂ hf₂).2 (hne₀ k)) hMatch hfin1 hβ₂ htaut
  have h1 := congrFun hs k
  have h2 := DFunLike.congr_fun hc₁ (C.s k)
  have h3 := DFunLike.congr_fun hc₂ (C.s k)
  simp only [RingHom.comp_apply] at h1 h2 h3
  exact hη' (by rw [← h2, ← h3]; exact h1)

end GlobalTheory.TInj
end
end
end
