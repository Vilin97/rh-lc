module

public import Development.AbelianVarietyTheory.Definitions.Divisors.NotOrdGeOfNotMem
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.ValuationFormPsiBalancedSymmetricPeriodForm
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PsiCoordExistsUniqueUpToUnitLocal
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Data.Nat.Choose.Multinomial
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolarisedAbelianSemiAbelianSiegelPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisationFiniteExtensionSiegelFamilyStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMonomialPeriodsSymmetricExponentForm

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
open ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.MonPeriods

theorem exists_isMonomial_symm : ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ ϖ : W, Irreducible ϖ →
    ∀ D : DegData W (maximalIdeal W), ∃ β : LinearMap.BilinForm ℤ D.toPre.X, (∀ a b, β a b = β b a) ∧
      IsMonomial D.toPre ![ϖ] ![β] := by
  intro W _ _ _ hW ϖ hϖ D
  obtain ⟨hdvr, hcomp, hchar⟩ := hW
  haveI := hdvr
  haveI := hcomp
  haveI := hchar
  choose Q hQ using QForm.exists_QVal (ϖ := ϖ) hϖ D
  have hQ' : QForm.IsQ D.toPre ϖ Q := hQ
  have hex : ∀ χ, ∃ r, PsiCoord D.toPre χ r := fun χ =>
    ((GlobalTheory.PsiCoordLocal.main W D inferInstance χ).1).imp fun _ h => h.1
  have hv : ∀ χ, HasVal ϖ (algebraMap W (FractionRing W) (hex χ).choose) (Q χ) := fun χ =>
    GlobalTheory.ValForm.hasVal_coord (hQ χ) (hex χ).choose_spec
  have h0 : ∀ a, 0 ≤ Q a := fun a => by
    by_cases ha : a = 0
    · rw [ha, QForm.Q_zero (ϖ := ϖ) hϖ D hQ']
    · exact zero_le_one.trans (QForm.Q_pos (ϖ := ϖ) hϖ D hQ' ha)
  let be : LinearMap.BilinForm ℤ D.toPre.X :=
    LinearMap.mk₂ ℤ (fun a b => QForm.bHom (ϖ := ϖ) hϖ D hQ' a b)
      (fun a a' b => by simp only [map_add (f := _), AddMonoidHom.add_apply])
      (fun c a b => by simp only [map_zsmul, AddMonoidHom.smul_apply, smul_eq_mul])
      (fun a b b' => by simp only [map_add (f := _)])
      (fun c a b => by simp only [map_zsmul, smul_eq_mul])
  have hbe : ∀ a b, be a b = QForm.bOf D.toPre Q a b := fun _ _ => rfl
  refine ⟨be, fun y z => ?_, fun y => ?_⟩
  · rw [hbe, hbe, QForm.bOf_comm]
  · obtain ⟨u, hu⟩ := hv y
    set r := (hex y).choose with hr
    have hn : (((Q y).toNat : ℕ) : ℤ) = Q y := Int.toNat_of_nonneg (h0 y)
    have e : r = ↑u * ϖ ^ (Q y).toNat := by
      apply IsFractionRing.injective W (FractionRing W)
      rw [hu, map_mul, map_pow, _root_.mul_comm, ← zpow_natCast, hn]
    refine ⟨u, fun _ => (Q y).toNat, fun i => ?_, ?_⟩
    · fin_cases i
      simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      rw [hbe, ← QForm.two_Q_eq (ϖ := ϖ) hϖ D hQ', hn]
    · have hc : PsiCoord D.toPre y r := (hex y).choose_spec
      rw [e] at hc
      simpa using hc

end GlobalTheory.MonPeriods
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMonomialPeriodsSymmetricExponentFormStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem _root_.GlobalTheory.T.exists_monomialPeriods_symmetric_exponentForm : ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ ϖ : W, Irreducible ϖ →
    ∀ D : DegData W (maximalIdeal W), ∃ β : LinearMap.BilinForm ℤ D.toPre.X, (∀ a b, β a b = β b a) ∧
      IsMonomial D.toPre ![ϖ] ![β] := by
  first | exact @GlobalTheory.MonPeriods.exists_isMonomial_symm | exact GlobalTheory.MonPeriods.exists_isMonomial_symm | (intros; apply GlobalTheory.MonPeriods.exists_isMonomial_symm <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolarisedAbelianSemiAbelianSiegelPointStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem _root_.GlobalTheory.T.exists_polarisedAbelian_semiAbelian_siegelPoint : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V],
    GlobalTheory.Mum.Base V → IsDiscreteValuationRing V → ∀ y : Sp (FractionRing V) ⟶ F.X,
      ∃ (V₁ : Type) (_ : CommRing V₁) (_ : IsDomain V₁) (_ : IsLocalRing V₁) (f : V →+* V₁)
        (fK : FractionRing V →+* FractionRing V₁), GlobalTheory.LN.CDvr V₁ ∧ Function.Injective f ∧ IsLocalHom f ∧ f.Finite ∧
        (∀ a, fK (algebraMap V _ a) = algebraMap V₁ _ (f a)) ∧
        ∃ (A : PolAV (Sp (FractionRing V₁))) (α : A.A.left ⟶ F.univ.A.left) (α₂ : (G2 A.A).left ⟶ (G2 F.univ.A).left),
          IsGrpPullback A.A F.univ.A (spMap fK ≫ y) α ∧ IsSquare α α₂ ∧ LBIso (abelian₂ A.A A.L) (F.univ.P.pull α₂) ∧
          ∃ (G : Over (Sp V₁)) (_ : GrpObj G) (_ : IsCommMonObj G) (gen : (Over.pullback (jK V₁)).obj G ≅ A.A),
            IsSemiAbelian G ∧ IsMonHom gen.hom := by
  first | exact @GlobalTheory.CExtGen.exists_polAV_semiAbelian | exact GlobalTheory.CExtGen.exists_polAV_semiAbelian | (intros; apply GlobalTheory.CExtGen.exists_polAV_semiAbelian <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitExistsAfterFiniteExtensionOfCompleteDVR

section

@[expose] public section

noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.Poinc

theorem traitExtSt_of (h₁ : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V],
      GlobalTheory.Mum.Base V → IsDiscreteValuationRing V → ∀ y : Sp (FractionRing V) ⟶ F.X,
        ∃ (V₁ : Type) (_ : CommRing V₁) (_ : IsDomain V₁) (_ : IsLocalRing V₁) (f : V →+* V₁)
          (fK : FractionRing V →+* FractionRing V₁), GlobalTheory.LN.CDvr V₁ ∧ Function.Injective f ∧ IsLocalHom f ∧ f.Finite ∧
          (∀ a, fK (algebraMap V _ a) = algebraMap V₁ _ (f a)) ∧
          ∃ (A : PolAV (Sp (FractionRing V₁))) (α : A.A.left ⟶ F.univ.A.left) (α₂ : (G2 A.A).left ⟶ (G2 F.univ.A).left),
            IsGrpPullback A.A F.univ.A (spMap fK ≫ y) α ∧ IsSquare α α₂ ∧ LBIso (abelian₂ A.A A.L) (F.univ.P.pull α₂) ∧
            ∃ (G : Over (Sp V₁)) (_ : GrpObj G) (_ : IsCommMonObj G) (gen : (Over.pullback (jK V₁)).obj G ≅ A.A),
              IsSemiAbelian G ∧ IsMonHom gen.hom)
    (h₂ : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (V₁ : Type) [CommRing V₁] [IsDomain V₁]
      [IsLocalRing V₁], GlobalTheory.LN.CDvr V₁ → ∀ (y₁ : Sp (FractionRing V₁) ⟶ F.X) (A : PolAV (Sp (FractionRing V₁)))
      (α : A.A.left ⟶ F.univ.A.left) (α₂ : (G2 A.A).left ⟶ (G2 F.univ.A).left),
      IsGrpPullback A.A F.univ.A y₁ α → IsSquare α α₂ → LBIso (abelian₂ A.A A.L) (F.univ.P.pull α₂) →
      ∀ (G : Over (Sp V₁)) [GrpObj G] [IsCommMonObj G] (gen : (Over.pullback (jK V₁)).obj G ≅ A.A),
      IsSemiAbelian G → IsMonHom gen.hom →
        ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (f : V₁ →+* W)
          (fK : FractionRing V₁ →+* FractionRing W), GlobalTheory.LN.CDvr W ∧ Function.Injective f ∧ IsLocalHom f ∧ f.Finite ∧
          (∀ a, fK (algebraMap V₁ _ a) = algebraMap W _ (f a)) ∧
          ∃ (G' : Over (Sp W)) (_ : GrpObj G') (_ : IsCommMonObj G') (D : DegData W (maximalIdeal W))
            (A' : PolAV (Sp (FractionRing W))) (_ : Unif (maximalIdeal W) D A' G') (α' : A'.A.left ⟶ F.univ.A.left)
            (α₂' : (G2 A'.A).left ⟶ (G2 F.univ.A).left),
            IsSemiAbelian G' ∧ IsGrpPullback A'.A F.univ.A (spMap fK ≫ y₁) α' ∧ IsSquare α' α₂' ∧
            LBIso (abelian₂ A'.A A'.L) (F.univ.P.pull α₂'))
    (h₃ : ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ ϖ : W, Irreducible ϖ →
      ∀ D : DegData W (maximalIdeal W), ∃ β : LinearMap.BilinForm ℤ D.toPre.X, (∀ a b, β a b = β b a) ∧
        IsMonomial D.toPre ![ϖ] ![β]) : TraitExtSt := by
  intro g n o _ ζ F V _ _ _ hB hD y
  obtain ⟨V₁, _, _, _, f, fK, hC₁, hinj₁, hloc₁, hfin₁, hK₁, A, α, α₂, hcart, hsq, hlb, G, _, _, gen, hsemi, hmon⟩ :=
    h₁ g n o ζ F V hB hD y
  obtain ⟨W, _, _, _, f', fK', hCW, hinj₂, hloc₂, hfin₂, hK₂, G', _, _, D, A', U, α', α₂', hsemi', hcart', hsq', hlb'⟩ :=
    h₂ g n o ζ F V₁ hC₁ (spMap fK ≫ y) A α α₂ hcart hsq hlb G gen hsemi hmon
  obtain ⟨hdvr, hcpl, hchar⟩ := hCW
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible W
  obtain ⟨β, hβs, hβm⟩ := h₃ W ⟨hdvr, hcpl, hchar⟩ ϖ hϖ D
  have hsp : spMap (fK'.comp fK) = spMap fK' ≫ spMap fK := by
    unfold spMap
    simp
  refine ⟨
    { V := W
      complete := hcpl
      ϖ := ϖ
      irr := hϖ
      y := spMap (fK'.comp fK) ≫ y
      G := G'
      semi := hsemi'
      D := D
      A := A'
      U := U
      α := α'
      α₂ := α₂'
      cart := ?_
      sq := hsq'
      lb := hlb'
      β := β
      symm := hβs
      mono := hβm },
    f'.comp f, fK'.comp fK, hinj₂.comp hinj₁, ?_, hfin₂.comp hfin₁, ?_, rfl⟩
  · rw [hsp, Category.assoc]
    exact hcart'
  · exact RingHom.isLocalHom_comp f' f
  · intro a
    simp [hK₁, hK₂]

theorem traitExtSt : TraitExtSt :=
  traitExtSt_of GlobalTheory.T.exists_polarisedAbelian_semiAbelian_siegelPoint GlobalTheory.T.exists_uniformisation_finiteExtension_siegelFamily GlobalTheory.T.exists_monomialPeriods_symmetric_exponentForm

end GlobalTheory.Poinc
end
end
end
