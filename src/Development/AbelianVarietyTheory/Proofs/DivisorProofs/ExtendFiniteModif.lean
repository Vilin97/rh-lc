module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LePreimageOfCompEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartValEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartValueIsIntegralOfIntegralAtPoints
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralAtClosedFibreOfRegularAtAllTraitsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralElementAffineSectionGenerated
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageGenericBaseChangeModificatio
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralSectionEverywhereOfClosedFibreStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallyIntegralSectionsExtendOverFiniteModificat

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartValueIsIntegralOfIntegralAtPointsStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum


theorem _root_.GlobalTheory.T.chartValue_isIntegral_of_integral_at_points : ∀ {X Y : Scheme.{0}} (L : LB X) (α : Y ⟶ X) (k : ℕ) (s : SecK L α k) (j : L.ι) (W : X.Opens) (hW : W ≤ L.U j), IsAffineOpen W → IsAffineOpen (α ⁻¹ᵁ W) → (∀ x ∈ W, IntAt L α s x) → (α.app W).hom.IsIntegralElem (chartVal L α s j W hW) := by
  first | exact @GlobalTheory.Mum.chartVal_isIntegral_of_intAt | exact GlobalTheory.Mum.chartVal_isIntegral_of_intAt | (intros; apply GlobalTheory.Mum.chartVal_isIntegral_of_intAt <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralElementAffineSectionGeneratedStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum


theorem _root_.GlobalTheory.T.integral_element_affine_section_generated : ∀ (R : Type) [CommRing R] [IsDomain R] (M : Modif R) (G : Over M.S), Smooth G.hom → ∀ (Y : Scheme.{0}) (α : Y ⟶ G.left) (t : Y ⟶ Sp (FractionRing R)) (hpb : IsPullback α t G.hom M.gp) (W : G.left.Opens) (U : M.S.Opens) (hWU : W ≤ G.hom ⁻¹ᵁ U), IsAffineOpen W → IsAffineOpen U → ∀ f : Γ(Y, α ⁻¹ᵁ W), (α.app W).hom.IsIntegralElem f → ∃ (n : ℕ) (c : Fin n → Γ(G.left, W)) (b : Fin n → Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U)), (∀ m, (M.gp.app U).hom.IsIntegralElem (b m)) ∧ f = ∑ m, (α.app W).hom (c m) * (t.appLE (M.gp ⁻¹ᵁ U) (α ⁻¹ᵁ W) (locInt_le_gen G.hom α t M.gp hpb.w W U hWU)).hom (b m) := by
  first | exact @GlobalTheory.Mum.eq_sum_of_isIntegral_genericChart | exact GlobalTheory.Mum.eq_sum_of_isIntegral_genericChart | (intros; apply GlobalTheory.Mum.eq_sum_of_isIntegral_genericChart <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageGenericBaseChangeModificatioStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum


theorem _root_.GlobalTheory.T.isAffineOpen_preimage_genericBaseChange_modification : ∀ (R : Type) [CommRing R] [IsDomain R] (M : Modif R) (G : Over M.S) (Y : Scheme.{0}) (α : Y ⟶ G.left) (t : Y ⟶ Sp (FractionRing R)), IsPullback α t G.hom M.gp → ∀ W : G.left.Opens, IsAffineOpen W → IsAffineOpen (α ⁻¹ᵁ W) := by
  first | exact @GlobalTheory.Mum.isAffineOpen_preimage_genericBaseChange | exact GlobalTheory.Mum.isAffineOpen_preimage_genericBaseChange | (intros; apply GlobalTheory.Mum.isAffineOpen_preimage_genericBaseChange <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallyIntegralOfRegularAtAllTraits

section

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem locInt_of_traitReg : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [CharZero R] (M : Modif R) (G : Over M.S), Smooth G.hom → QuasiCompact G.hom → GeometricallyIrreducible G.hom → ∀ (L : LB G.left), L.IsLB → ∀ (Y : Scheme.{0}) (α : Y ⟶ G.left) (t : Y ⟶ Sp (FractionRing R)) (hpb : IsPullback α t G.hom M.gp) (k : ℕ) (s : SecK L α k), TraitReg M G L s → LocInt M G L α t hpb.w s := by
  intro R _ _ _ _ _ M G hsm hqc hgi L hL Y α t hpb k s hs
  have h4 := GlobalTheory.T.integral_at_closedFibre_of_regular_at_all_traits R M G hsm hqc hgi L hL Y α t hpb k s hs
  have h5 := GlobalTheory.T.isIntegralSection_everywhere_of_closedFibre R M G hsm hqc hgi L hL Y α t hpb k s h4
  intro j W U hW hWU hWa hUa
  exact GlobalTheory.T.integral_element_affine_section_generated R M G hsm Y α t hpb W U hWU hWa hUa _
    (GlobalTheory.T.chartValue_isIntegral_of_integral_at_points L α k s j W hW hWa (GlobalTheory.T.isAffineOpen_preimage_genericBaseChange_modification R M G Y α t hpb W hWa) (fun x _ => h5 x))

end GlobalTheory.Mum
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallyIntegralOfRegularAtAllTraitsStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum


theorem _root_.GlobalTheory.T.locallyIntegral_of_regular_at_all_traits : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [CharZero R] (M : Modif R) (G : Over M.S), Smooth G.hom → QuasiCompact G.hom → GeometricallyIrreducible G.hom → ∀ (L : LB G.left), L.IsLB → ∀ (Y : Scheme.{0}) (α : Y ⟶ G.left) (t : Y ⟶ Sp (FractionRing R)) (hpb : IsPullback α t G.hom M.gp) (k : ℕ) (s : SecK L α k), TraitReg M G L s → LocInt M G L α t hpb.w s := by
  first | exact @GlobalTheory.Mum.locInt_of_traitReg | exact GlobalTheory.Mum.locInt_of_traitReg | (intros; apply GlobalTheory.Mum.locInt_of_traitReg <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallyIntegralSectionsExtendOverFiniteModificatStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum


theorem _root_.GlobalTheory.T.locallyIntegralSections_extend_over_finiteModification : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [CharZero R] (M : Modif R) (G : Over M.S), Smooth G.hom → QuasiCompact G.hom → GeometricallyIrreducible G.hom → ∀ (L : LB G.left), L.IsLB → ∀ (Y : Scheme.{0}) (α : Y ⟶ G.left) (t : Y ⟶ Sp (FractionRing R)) (hpb : IsPullback α t G.hom M.gp) (I : Type) [Finite I] (k : I → ℕ) (s : ∀ i, SecK L α (k i)), (∀ i, LocInt M G L α t hpb.w (s i)) → ∃ (M' : Modif R) (h : M'.S ⟶ M.S), IsFinite h ∧ M'.gp ≫ h = M.gp ∧ h ≫ M.π = M'.π ∧ ∀ i, ∃ σ : SecK L (pullback.fst G.hom h) (k i), Agree L σ (s i) := by
  first | exact @GlobalTheory.Mum.extend_locInt | exact GlobalTheory.Mum.extend_locInt | (intros; apply GlobalTheory.Mum.extend_locInt <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendFiniteModif

section

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem extend_finiteModif : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [CharZero R] (M : Modif R) (G : Over M.S), Smooth G.hom → QuasiCompact G.hom → GeometricallyIrreducible G.hom → ∀ (L : LB G.left), L.IsLB → ∀ (Y : Scheme.{0}) (α : Y ⟶ G.left) (t : Y ⟶ Sp (FractionRing R)), IsPullback α t G.hom M.gp → ∀ (I : Type) [Finite I] (k : I → ℕ) (s : ∀ i, SecK L α (k i)), (∀ i, TraitReg M G L (s i)) → ∃ (M' : Modif R) (h : M'.S ⟶ M.S), IsFinite h ∧ M'.gp ≫ h = M.gp ∧ h ≫ M.π = M'.π ∧ ∀ i, ∃ σ : SecK L (pullback.fst G.hom h) (k i), Agree L σ (s i) := by
  intro R _ _ _ _ _ M G hsm hqc hgi L hL Y α t hpb I _ k s hs
  exact GlobalTheory.T.locallyIntegralSections_extend_over_finiteModification R M G hsm hqc hgi L hL Y α t hpb I k s
    (fun i => GlobalTheory.T.locallyIntegral_of_regular_at_all_traits R M G hsm hqc hgi L hL Y α t hpb (k i) (s i) (hs i))

end GlobalTheory.Mum
end
end
end
