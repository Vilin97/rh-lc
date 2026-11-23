module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
public import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefIntersectionNumberNonnegSubscheme
public import Development.WeilBound.CoreStatements.PublishedTheorems.NefNumerics.NefRiemannRoch.NefLineBundleNumericalTheoremsProof
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.Definitions.Divisors.CharZeroFunctionField
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemConeOfMem
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Data.Nat.Choose.Multinomial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithKleimanSelfIntersectionNonnegStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoheightAddPointClosureDimEqDim
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasPointClosureDimBasicProjArithAmbient
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianLineBundleIsNefPullbackStatement
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ResidueDegreeOfIsClosedImmersion
import Mathlib.Tactic.Basify
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithHeightNonnegVerticalOfNefOnFibres

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.VertHeight

theorem charZero_residueField_genericPoint (Z : Scheme.{0}) [IsIntegral Z] (hc : CharZero Γ(Z, ⊤)) :
    CharZero (Z.residueField (genericPoint Z)) := by
  have h₁ : CharZero Z.functionField :=
    (RingHom.charZero_iff (Z.germToFunctionField_injective ⊤)).1 hc
  exact (RingHom.charZero_iff (Z.residue (genericPoint Z)).hom.injective).1 h₁

theorem height_nonneg_of_vertical : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X]
    (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (C : HermLB p) (h : X → ℝ), NefFib C →
    C.IsArithHeight h → ∀ z : X, ¬ CharZero (X.residueField z) → 0 ≤ h z := by
  intro k _ X _ p D hX C h hC H z hz
  obtain ⟨Z, i, _, _, rfl⟩ := exists_isClosedImmersion_genericPoint z
  rcases hX.vertical_or_horizontal i with ⟨ℓ, _, ⟨a⟩⟩ | ⟨hc, -⟩
  · letI := a
    haveI := hX.finite
    obtain ⟨d, hd⟩ := hX.exists_dim_eq i
    rw [H.vertical Z i (ZMod ℓ) d hd, Nat.card_zmod]
    refine mul_nonneg ?_ (Real.log_nonneg (by exact_mod_cast (Fact.out : ℓ.Prime).one_le))
    have hN := GlobalTheory.FibreNef.isNef_pull_of_nefOver ℓ i C
      ((GlobalTheory.VertForm.nefFib_iff C).1 hC ℓ Fact.out)
    rw [topSelf_def]
    exact_mod_cast GlobalTheory.nefNumerics_outright.1.interNum_nonneg
      (GlobalTheory.FibreNef.isProjOver_fibre hX.isProjOver ℓ i) hd fun _ => hN
  · haveI := charZero_residueField_genericPoint Z hc
    exact absurd ((i.residueFieldMap (genericPoint Z)).hom.charZero) hz

end GlobalTheory.VertHeight
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithHeightNonnegVerticalOfNefOnFibresStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

theorem _root_.GlobalTheory.T.arithHeight_nonneg_vertical_of_nefOnFibres : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (C : HermLB p) (h : X → ℝ), NefFib C → C.IsArithHeight h → ∀ z : X, ¬ CharZero (X.residueField z) → 0 ≤ h z := by
  first | exact @GlobalTheory.VertHeight.height_nonneg_of_vertical | exact GlobalTheory.VertHeight.height_nonneg_of_vertical | (intros; apply GlobalTheory.VertHeight.height_nonneg_of_vertical <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithKleimanHeightNefOfIsNef

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.KleimanNef

theorem htNef_of_isNef : GlobalTheory.Published.ArCalc → AmpleHS → SemiPull → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X]
    (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ C : HermLB p, C.IsNef D → HtNef C D := by
  intro hA hAmp hSP
  suffices H : ∀ D : ℕ, ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k),
      IsArithVar p D → ∀ C : HermLB p, C.IsNef D → HtNef C D by
    intro k _ X _ p D hX C hC
    exact H D k X p hX C hC
  intro D
  induction D using Nat.strong_induction_on with
  | _ D ih =>
  intro k _ X _ p hX C hC
  have hng : ∀ (C : HermLB p) (h : X → ℝ), C.IsNef D → C.IsArithHeight h →
      ∀ z, z ≠ genericPoint X → 0 ≤ h z := by
    intro C h hC hh z hz
    by_cases hcz : CharZero (X.residueField z)
    swap
    · exact GlobalTheory.T.arithHeight_nonneg_vertical_of_nefOnFibres k X p D hX C h (nefFib_of_isNef hC) hh z hcz
    obtain ⟨Z, i, _, _, rfl⟩ := exists_isClosedImmersion_genericPoint z
    rcases hX.vertical_or_horizontal i with ⟨ℓ, hℓ, ⟨alg⟩⟩ | ⟨hc, e, he⟩
    · exfalso
      have hcz' : CharZero (Z.residueField (genericPoint Z)) :=
        (RingHom.charZero_iff (i.residueFieldMap (genericPoint Z)).hom.injective).1 hcz
      let f : ZMod ℓ →+* Z.residueField (genericPoint Z) :=
        (Z.evaluation ⊤ (genericPoint Z) trivial).hom.comp (algebraMap (ZMod ℓ) Γ(Z, ⊤))
      have h2 := congrArg f (ZMod.natCast_self ℓ)
      rw [map_natCast, map_zero] at h2
      exact hℓ.out.ne_zero (by exact_mod_cast h2)
    · have hZ : IsArithVar (i ≫ p) e := hX.of_isClosedImmersion i hc he
      have hamb := GlobalTheory.MixHt.isAmb_of_isArithVar hX
      obtain ⟨-, -, -, -, hcl, hgd⟩ := GlobalTheory.MixHt.hasDim_basic k X p hamb
      have hd : GlobalTheory.MixHt.HasDim (i (genericPoint Z)) (e + 1) := (hcl Z i _ _).2 ((hgd Z _).2 he)
      have hco := GlobalTheory.DimCoheight.coheight_add_eq k X p hamb (D + 1) hX.dim_eq _ _ hd
      have hne : Order.coheight (i (genericPoint Z)) ≠ 0 := by
        intro h0
        rw [Order.coheight_eq_zero] at h0
        apply hz
        have h1 : i (genericPoint Z) ≤ genericPoint X := genericPoint_specializes _
        exact (Specializes.antisymm (h0 h1) (genericPoint_specializes _)).eq
      have heD : e < D := by
        by_contra hle
        push_neg at hle
        obtain ⟨c, hc'⟩ : ∃ c : ℕ, Order.coheight (i (genericPoint Z)) = c := by
          refine ⟨(Order.coheight (i (genericPoint Z))).toNat, (ENat.coe_toNat fun ht => ?_).symm⟩
          rw [ht, top_add] at hco
          exact ENat.top_ne_coe _ hco
        rw [hc'] at hco hne
        have : c + (e + 1) = D + 1 := by exact_mod_cast hco
        have : c ≠ 0 := by exact_mod_cast hne
        omega
      have hnef : (C.pull i rfl).IsNef e := GlobalTheory.T.hermitianLineBundle_isNef_pullback hA hSP k X Z p (i ≫ p) D e hX hZ i rfl C hC
      exact (ih e heD k Z (i ≫ p) hZ _ hnef).2 _ (hh.restrict hX i rfl) (genericPoint Z)
  refine ⟨hC.semiPos, fun h hh x => ?_⟩
  by_cases hx : x = genericPoint X
  · subst hx
    rcases Nat.eq_zero_or_pos D with rfl | hD
    · have := ((hh.isNef_iff hX).1 hC).2 X (𝟙 X) (by simpa using hX.dim_eq)
      simpa using this
    · exact GlobalTheory.T.arithKleiman_selfIntersection_nonneg hA hAmp k X p D hX hD hng C _ hC ⟨h, hh, rfl⟩
  · exact hng C h hC hh x hx

end GlobalTheory.KleimanNef
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithKleimanHeightNefOfIsNefStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

theorem _root_.GlobalTheory.T.arithKleiman_heightNef_of_isNef : GlobalTheory.Published.ArCalc → AmpleHS → SemiPull → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ C : HermLB p, C.IsNef D → HtNef C D := by
  first | exact @GlobalTheory.KleimanNef.htNef_of_isNef | exact GlobalTheory.KleimanNef.htNef_of_isNef | (intros; apply GlobalTheory.KleimanNef.htNef_of_isNef <;> assumption)
end
end
