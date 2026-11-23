module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeGlobalOneFormsPrimitiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeOneFormFrameAndSquareStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlobalTwoFormEqSumWedgeGlobalOneForms
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairCoverAffine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoFormExistsPowSmulEqZeroOfIsLocalization
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumWedgePrimitiveOneFormsEqZeroAbelianSchemeStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExteriorDerivGlobalOneFormEqSumWedge

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem dOne_glob_eq_wsum : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R),
    HasFrame F → CohomZeroIsConstants F → ∀ w : Glob1 F, ∃ (n : ℕ) (u v : Fin n → Glob1 F), ClRel F w u v := by
  intro R _ C _ F hF hH w
  obtain ⟨n, u, v, h⟩ := twoForm_eq_wsum R C F hF hH (fun T ↦ dOne R (F.obj T) (w.1 T))
    (fun T T' φ ↦ by rw [pOm_dOne, ← w.2 φ])
  exact ⟨n, u, v, fun T ↦ congrFun h T⟩

end GlobalTheory.AbCoh
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExteriorDerivGlobalOneFormEqSumWedgeStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exteriorDeriv_globalOneForm_eq_sum_wedge : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R), HasFrame F → CohomZeroIsConstants F → ∀ w : Glob1 F, ∃ (n : ℕ) (u v : Fin n → Glob1 F), ClRel F w u v := by
  first | exact @GlobalTheory.AbCoh.dOne_glob_eq_wsum | exact GlobalTheory.AbCoh.dOne_glob_eq_wsum | (intros; apply GlobalTheory.AbCoh.dOne_glob_eq_wsum <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExteriorDerivSumWedgeSemilinearPullback

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem clRel_pullForm : ∀ (R R' : Type) [CommRing R] [CommRing R'] (X X' : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (σ : R →+* R') (φ : X' ⟶ X) (h : φ ≫ s = s' ≫ spMap σ) (w : GlobForm s) (n : ℕ) (u v : Fin n → GlobForm s), ClRel (OAff s) w u v → ClRel (OAff s') (GlobalTheory.CechDR.pullForm h w) (fun k ↦ GlobalTheory.CechDR.pullForm h (u k)) (fun k ↦ GlobalTheory.CechDR.pullForm h (v k)) := by
  intro R R' _ _ X X' s s' σ φ h w n u v hw T'
  have hp : ∀ (ω : GlobForm s) (p : Pair φ), (GlobalTheory.CechDR.pullForm h ω).1 (Opposite.op p.1.1) =
      (semiHom_secPull h p).m1 (ω.1 (Opposite.op p.1.2)) :=
    fun ω p ↦ ((isPullForm_iff.1 (isPullForm_pullForm h ω)) p).symm
  have hg : ∀ (ω : GlobForm s') {T T' : AffOp X'} (a : T ⟶ T'), p1 (OAff s') a (ω.1 T) = ω.1 T' :=
    fun ω _ _ a ↦ (ω.2 a).symm
  rw [← sub_eq_zero]
  refine twoForm_sep_of_basis s' (pairFst φ) (pair_cover_affine φ s') T' _ fun t a ↦ ?_
  rw [map_sub, sub_eq_zero, pOm_dOne, hg]
  have e1 : ∀ k, pOm (OAff s') 2 a (wedge R' _ ((GlobalTheory.CechDR.pullForm h (u k)).1 T')
      ((GlobalTheory.CechDR.pullForm h (v k)).1 T')) = wedge R' _ ((GlobalTheory.CechDR.pullForm h (u k)).1 ((pairFst φ).obj t))
      ((GlobalTheory.CechDR.pullForm h (v k)).1 ((pairFst φ).obj t)) := fun k ↦
    (pOm_wedge (OAff s') a _ _).trans (by rw [hg, hg])
  refine Eq.trans ?_ ((map_sum (pOm (OAff s') 2 a) _ _).trans (Finset.sum_congr rfl fun k _ ↦ e1 k)).symm
  have key : ∀ p : Pair φ, dOne R' (Sec s' p.1.1.1) ((GlobalTheory.CechDR.pullForm h w).1 (Opposite.op p.1.1)) =
      ∑ k, wedge R' (Sec s' p.1.1.1) ((GlobalTheory.CechDR.pullForm h (u k)).1 (Opposite.op p.1.1))
        ((GlobalTheory.CechDR.pullForm h (v k)).1 (Opposite.op p.1.1)) := by
    intro p
    calc dOne R' (Sec s' p.1.1.1) ((GlobalTheory.CechDR.pullForm h w).1 (Opposite.op p.1.1))
        = dOne R' (Sec s' p.1.1.1) ((semiHom_secPull h p).m1 (w.1 (Opposite.op p.1.2))) :=
          congrArg _ (hp w p)
      _ = (semiHom_secPull h p).mOm 2 (dOne R (Sec s p.1.2.1) (w.1 (Opposite.op p.1.2))) :=
          (SemiHom.mOm_dOne _ _).symm
      _ = (semiHom_secPull h p).mOm 2 (wsum (OAff s) u v (Opposite.op p.1.2)) :=
          congrArg ((semiHom_secPull h p).mOm 2) (hw (Opposite.op p.1.2))
      _ = (semiHom_secPull h p).mOm 2 (∑ k, wedge R (Sec s p.1.2.1) ((u k).1 (Opposite.op p.1.2))
            ((v k).1 (Opposite.op p.1.2))) := rfl
      _ = ∑ k, (semiHom_secPull h p).mOm 2 (wedge R (Sec s p.1.2.1) ((u k).1 (Opposite.op p.1.2))
            ((v k).1 (Opposite.op p.1.2))) := map_sum _ _ _
      _ = ∑ k, wedge R' (Sec s' p.1.1.1) ((semiHom_secPull h p).m1 ((u k).1 (Opposite.op p.1.2)))
            ((semiHom_secPull h p).m1 ((v k).1 (Opposite.op p.1.2))) :=
          Finset.sum_congr rfl fun k _ ↦ SemiHom.mOm_wedge (semiHom_secPull h p) ((u k).1 (Opposite.op p.1.2))
            ((v k).1 (Opposite.op p.1.2))
      _ = ∑ k, wedge R' (Sec s' p.1.1.1) ((GlobalTheory.CechDR.pullForm h (u k)).1 (Opposite.op p.1.1))
            ((GlobalTheory.CechDR.pullForm h (v k)).1 (Opposite.op p.1.1)) :=
          Finset.sum_congr rfl fun k _ ↦ congrArg₂ (fun a b ↦ wedge R' (Sec s' p.1.1.1) a b)
            (hp (u k) p).symm (hp (v k) p).symm
  exact key t.unop

end GlobalTheory.AbCoh
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExteriorDerivSumWedgeSemilinearPullbackStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exteriorDerivSumWedge_semilinearPullback : ∀ (R R' : Type) [CommRing R] [CommRing R'] (X X' : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (σ : R →+* R') (φ : X' ⟶ X) (h : φ ≫ s = s' ≫ spMap σ) (w : GlobForm s) (n : ℕ) (u v : Fin n → GlobForm s), ClRel (OAff s) w u v → ClRel (OAff s') (GlobalTheory.CechDR.pullForm h w) (fun k ↦ GlobalTheory.CechDR.pullForm h (u k)) (fun k ↦ GlobalTheory.CechDR.pullForm h (v k)) := by
  first | exact @GlobalTheory.AbCoh.clRel_pullForm | exact GlobalTheory.AbCoh.clRel_pullForm | (intros; apply GlobalTheory.AbCoh.clRel_pullForm <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeGlobalOneFormsClosed

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem closed1_eq_top_of_abelian : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ),
    IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → Closed1 (OAff A.hom) = ⊤ := by
  intro R _ A _ g hA hg
  obtain ⟨hF, h0, -, -⟩ := GlobalTheory.T.abelianScheme_oneFormFrame_and_square R A g hA hg
  have hP := GlobalTheory.T.abelianScheme_globalOneForms_primitive R A g hA hg
  rw [eq_top_iff]
  intro w _
  obtain ⟨n, u, v, hw⟩ := GlobalTheory.T.exteriorDeriv_globalOneForm_eq_sum_wedge R _ (OAff A.hom) hF h0 w
  have hμ : ClRel (OAff (A ⊗ A).hom) (pF μ[A] w) (fun k ↦ pF μ[A] (u k)) (fun k ↦ pF μ[A] (v k)) :=
    GlobalTheory.T.exteriorDerivSumWedge_semilinearPullback R R _ _ A.hom (A ⊗ A).hom (RingHom.id R) (μ[A]).left (ovw μ[A]) w n u v hw
  have h1 : ClRel (OAff (A ⊗ A).hom) (pF (fst A A) w) (fun k ↦ pF (fst A A) (u k))
      (fun k ↦ pF (fst A A) (v k)) :=
    GlobalTheory.T.exteriorDerivSumWedge_semilinearPullback R R _ _ A.hom (A ⊗ A).hom (RingHom.id R) (fst A A).left (ovw (fst A A)) w n u v hw
  have h2 : ClRel (OAff (A ⊗ A).hom) (pF (snd A A) w) (fun k ↦ pF (snd A A) (u k))
      (fun k ↦ pF (snd A A) (v k)) :=
    GlobalTheory.T.exteriorDerivSumWedge_semilinearPullback R R _ _ A.hom (A ⊗ A).hom (RingHom.id R) (snd A A).left (ovw (snd A A)) w n u v hw
  have hsum : wsum (OAff (A ⊗ A).hom) (fun k ↦ pF μ[A] (u k)) (fun k ↦ pF μ[A] (v k)) =
      wsum (OAff (A ⊗ A).hom) (fun k ↦ pF (fst A A) (u k)) (fun k ↦ pF (fst A A) (v k)) +
        wsum (OAff (A ⊗ A).hom) (fun k ↦ pF (snd A A) (u k)) (fun k ↦ pF (snd A A) (v k)) := by
    funext T
    have e := hP w
    calc _ = dOne R _ ((pF μ[A] w).1 T) := (hμ T).symm
      _ = dOne R _ ((pF (fst A A) w).1 T + (pF (snd A A) w).1 T) :=
          congrArg (fun x : GlobForm (A ⊗ A).hom ↦ dOne R _ (x.1 T)) e
      _ = dOne R _ ((pF (fst A A) w).1 T) + dOne R _ ((pF (snd A A) w).1 T) := map_add _ _ _
      _ = _ := congrArg₂ (· + ·) (h1 T) (h2 T)
  have hz := GlobalTheory.T.sum_wedge_primitive_oneForms_eq_zero_abelianScheme R A g hA hg n u v hsum
  exact fun T ↦ (hw T).trans (congrFun hz T)

end GlobalTheory.AbCoh
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeGlobalOneFormsClosedStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.abelianScheme_globalOneForms_closed : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → Closed1 (OAff A.hom) = ⊤ := by
  first | exact @GlobalTheory.AbCoh.closed1_eq_top_of_abelian | exact GlobalTheory.AbCoh.closed1_eq_top_of_abelian | (intros; apply GlobalTheory.AbCoh.closed1_eq_top_of_abelian <;> assumption)
end
end
