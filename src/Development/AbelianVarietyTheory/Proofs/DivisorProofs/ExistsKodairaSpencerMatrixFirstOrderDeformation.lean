module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsNormalFormArcDatumFramedPointRootOfUnity
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsLocallyNoetherian
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WedgeOrdVpBaseChangeOfNeBot
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
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsLocallyNoetherian
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolarizationFormIsotropicFiltration
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingActionOfIsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTangentFrameOfFramedPointCommRingStatement
public import Formalism.LocalToGlobal.ProjectiveLattices.IsCombAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpPullbackBasisLiftCompatible
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsKodairaSpencerValueEndomorphismLiftStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerRowDualEigenvectorMemSpanRingStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerUniqueValueAbelianSchemeCommRingStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizationCrystalFormAdjointConjAction
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WedgeOrdVpBaseChangeOfNeBot
import Mathlib.Tactic.Linter.Style
import Development.AbelianVarietyTheory.Definitions.Divisors.CommGroupMulMulEqMulInvMulMulMul
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsKSRIffIsKS

section

@[expose] public section

set_option autoImplicit false


noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Frames GlobalTheory.AllWt
open Formalism.L2.Pj
open scoped Classical

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FlagTan

open GlobalTheory.DeRham GlobalTheory.Cris GlobalTheory.Published

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

def IsKSR (Φ : Finset (E →+* ℂ)) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S)
    (x' : Sp (DualNumber S) ⟶ Xo.X) (M : HIx Dw Φ → S) : Prop :=
  ∃ (A : Over (Sp S)) (_ : GrpObj A) (A' : Over (Sp (DualNumber S))) (_ : GrpObj A')
    (π : A.left ⟶ Xo.univ.t.G.left) (π' : A'.left ⟶ Xo.univ.t.G.left) (i : A.left ⟶ A'.left)
    (h : IsGrpPullback A A' (epsRed S) i) (ψ : LinearMap.BilinForm S (HdR A))
    (ub : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → (epsR S ⟶ A)) (hb : (Σ σ : E →+* ℂ, Fin (Dw.mult σ)) → HdR A),
    IsGrpPullback A Xo.univ.t.G y.x π ∧ IsGrpPullback A' Xo.univ.t.G x' π' ∧ i ≫ π' = π ∧
    IsPolForm (dp0 S) (𝟙 _) A (Xo.univ.t.PP.L.pull π) ψ ∧
    (∀ σ k, (ub σ k).left ≫ π = y.u σ k) ∧ (∀ σ k, DeRham.IsLieImage (hb ⟨σ, k⟩) (ub σ k)) ∧
    ∀ (τ : Φ) (a : Fin (Dw.mult (conjEmb τ.1))), ∃ w, IsLieComb (fun b => M ⟨τ, a, b⟩) (ub τ.1) w ∧
      IsKSRow h ψ hb ⟨conjEmb τ.1, a⟩ w

theorem isKSR_iff_isKS {Φ : Finset (E →+* ℂ)} {K : Type} [Field K] [Algebra c.F K] {y : FrPt Xo c K}
    {x' : Sp (DualNumber K) ⟶ Xo.X} {M : HIx Dw Φ → K} : IsKSR Φ y x' M ↔ IsKS Φ y x' M := Iff.rfl

theorem IsKSR.baseChange (P : AbelianDeRham) {Φ : Finset (E →+* ℂ)} {S S' : Type} [CommRing S] [Algebra c.F S]
    [CommRing S'] [Algebra c.F S'] {ψ : S →ₐ[c.F] S'} {y : FrPt Xo c S} {y' : FrPt Xo c S'} (h : FrMap ψ y y')
    {x : Sp (DualNumber S) ⟶ Xo.X} {M : HIx Dw Φ → S}
    (hM : IsKSR Φ y x M) : IsKSR Φ y' (spMap (dualMap ψ.toRingHom) ≫ x) (ψ ∘ M) := by
  obtain ⟨A, _, A', _, π, π', i, hi, b, ub, hb, hπ, hπ', e, hpol, hu, hl, hM⟩ := hM
  let : Algebra S S' := ψ.toRingHom.toAlgebra
  obtain ⟨B, _, φ, hφ⟩ := exists_isGrpPullback A (spMap (algebraMap S S'))
  obtain ⟨B', _, φ', hφ'⟩ := exists_isGrpPullback A' (spMap (dualMap (algebraMap S S')))
  have e₀ : spMap (algebraMap S S') ≫ epsRed S = epsRed S' ≫ spMap (dualMap (algebraMap S S')) := by
    rw [← Cris.spMap_comp, ← Cris.spMap_comp]
    congr 1
    ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  have w : (φ ≫ i) ≫ A'.hom = (B.hom ≫ epsRed S') ≫ spMap (dualMap (algebraMap S S')) := by
    rw [(hφ.comp hi).1.w, e₀, Category.assoc]
  have sq : hφ'.1.lift _ _ w ≫ φ' = φ ≫ i := hφ'.1.lift_fst _ _ _
  have hj : IsGrpPullback B B' (epsRed S') (hφ'.1.lift _ _ w) :=
    hφ'.cancel ((hφ.comp hi).congr e₀ sq.symm) (hφ'.1.lift_snd _ _ _)
  have hU := ObjDim.isAbelianScheme Xo.univ
  have hg := ObjDim.smoothOfRelativeDimension Xo.univ
  have hA := PolPull.isAbelianScheme_of_isGrpPullback hU hπ
  have gA := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hπ.1 hg
  have hA' := PolPull.isAbelianScheme_of_isGrpPullback hU hπ'
  have gA' := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hπ'.1 hg
  obtain ⟨bc, hF⟩ := P.2.2.1 S A _ hA gA S' B φ hφ
  have hL := (P.2.1 S' B _ (PolPull.isAbelianScheme_of_isGrpPullback hA hφ)
    ((smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hφ.1 gA)).1
  obtain ⟨b', hpol', eb⟩ := hpol.pull_comp (AbelianDeRham.bcMor hφ) (UnivPol.pol Xo).isLB
  choose tv htv using ArcQ.NormalForm.exists_baseChange hφ
  choose th hth using bc.exists
  refine ⟨B, _, B', _, φ ≫ π, φ' ≫ π', _, hj, b', fun σ k => tv (ub σ k), fun k => th (hb k),
    (hφ.comp hπ).congr h.1.symm rfl, hφ'.comp hπ', by rw [← Category.assoc, sq, Category.assoc, e], hpol',
    fun σ k => ?_, fun σ k => (hl σ k).baseChange (hφ := hφ) hF hL (hth _) (htv _), fun τ a => ?_⟩
  · rw [← Category.assoc, htv, Category.assoc, hu, h.2.1] <;> rfl
  · obtain ⟨w, hw, f, hf, hd, hv⟩ := hM τ a
    refine ⟨tv w, ArcQ.NormalForm.isLieComb_baseChange hφ (fun _ => htv _) (htv w) hw, th f,
      mem_Fil_of_corr (hφ := hφ) hF (hth f) hf, fun k => ?_,
      hv.baseChange (hφ := hφ) P hA' gA' hj hφ' sq (hth f) (htv w)⟩
    rw [eb _ _ _ _ (hth f) (hth _), hd]
    split_ifs <;> simp

end GlobalTheory.FlagTan
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolarizationFormIsotropicFiltrationStatement

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory GlobalTheory.DeRham GlobalTheory.Cris
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_polarization_form_isotropic_filtration : GlobalTheory.Published.AbelianDeRham → ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X} {A : Over (Sp S)} [GrpObj A] {π : A.left ⟶ Xo.univ.t.G.left}, IsGrpPullback A Xo.univ.t.G x π → ∃ ψ : LinearMap.BilinForm S (HdR A), IsPolForm (dp0 S) (𝟙 _) A (Xo.univ.t.PP.L.pull π) ψ ∧ (∀ f ∈ Fil A, ∀ g ∈ Fil A, ψ f g = 0) ∧ LinearMap.IsPerfPair ψ ∧ ∀ f, (∀ g ∈ Fil A, ψ f g = 0) → f ∈ Fil A := by
  first | exact @GlobalTheory.PolExistsRing.polForm_exists | exact GlobalTheory.PolExistsRing.polForm_exists | (intros; apply GlobalTheory.PolExistsRing.polForm_exists <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpPullbackBasisLiftCompatibleStatement

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory GlobalTheory.DeRham GlobalTheory.Cris
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.grp_pullback_basis_lift_compatible : GlobalTheory.Published.AbelianDeRham → ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) {A : Over (Sp S)} [GrpObj A] {π : A.left ⟶ Xo.univ.t.G.left}, IsGrpPullback A Xo.univ.t.G y.x π → ∀ (ub : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → (epsR S ⟶ A)), (∀ σ k, (ub σ k).left ≫ π = y.u σ k) → ∀ (hb : (Σ σ : E →+* ℂ, Fin (Dw.mult σ)) → HdR A), (∀ k, IsLieImage (hb k) (ub k.1 k.2)) → Submodule.span S (Set.range hb) ⊔ Fil A = ⊤ ∧ LinearIndependent S (fun k => (Submodule.Quotient.mk (hb k) : HdR A ⧸ Fil A)) := by
  first | exact @GlobalTheory.LieBasisRing.lifts_basis_mod_fil | exact GlobalTheory.LieBasisRing.lifts_basis_mod_fil | (intros; apply GlobalTheory.LieBasisRing.lifts_basis_mod_fil <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizationFormAdjointCmActionModuliPoint

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory GlobalTheory.DeRham GlobalTheory.Cris
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PolAdjointRing

theorem polForm_adjoint : GlobalTheory.Published.AbelianDeRham → ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X} {A : Over (Sp S)} [GrpObj A] {π : A.left ⟶ Xo.univ.t.G.left}, IsGrpPullback A Xo.univ.t.G x π → ∀ (a : OAct (𝓞 E) A), (∀ z, (a.act z).left ≫ π = π ≫ (Xo.univ.t.act.act z).left) → ∀ {ψ : LinearMap.BilinForm S (HdR A)}, IsPolForm (dp0 S) (𝟙 _) A (Xo.univ.t.PP.L.pull π) ψ → IsAdjointFor a (fun z => H.bar z) ψ := by
  open ReciprocityTheory.ChartRestriction.G.Semi CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonObj in
   intro P E _ _ _ H Dw l Xo S _ x A _ π hπ a ha ψ hψ z u v
   have hG := ObjDim.isAbelianScheme Xo.univ
   have hA : IsAbelianScheme A := by
     have := hG.comm
     have hc : IsCommMonObj A := by
       rw [isCommMonObj_iff_isMulCommutative]
       intro T
       refine ⟨⟨fun x y => Over.OverMorphism.ext (hπ.1.hom_ext ?_ (by rw [Over.w, Over.w]))⟩⟩
       rw [← hπ.2 T x y (pushPt hπ.1.w x) (pushPt hπ.1.w y) rfl rfl,
         ← hπ.2 T y x (pushPt hπ.1.w y) (pushPt hπ.1.w x) rfl rfl, _root_.mul_comm]
     exact ⟨hc, MorphismProperty.of_isPullback (P := @Smooth) hπ.1 hG.smooth,
       MorphismProperty.of_isPullback (P := @IsProper) hπ.1 hG.proper,
       MorphismProperty.of_isPullback (P := @GeometricallyConnected) hπ.1 hG.geomConnected⟩
   have gA := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hπ.1
     (ObjDim.smoothOfRelativeDimension Xo.univ)
   have := hA.comm
   have := a.hom
   exact GlobalTheory.PolAdjoint.adjoint_of_lbIso P.1 hA gA (pull_isLB Xo.univ.t.PP.isLB π) hψ (a.act z)
     (a.act (H.bar z)) (GlobalTheory.PolAdjoint.lbIso_cube hπ _ (ha z) (ha (H.bar z)) (Xo.univ.t.adj z)) u v
end GlobalTheory.PolAdjointRing
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizationFormAdjointCmActionModuliPointStatement

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory GlobalTheory.DeRham GlobalTheory.Cris
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.polarizationForm_adjoint_cmAction_moduli_point : GlobalTheory.Published.AbelianDeRham → ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X} {A : Over (Sp S)} [GrpObj A] {π : A.left ⟶ Xo.univ.t.G.left}, IsGrpPullback A Xo.univ.t.G x π → ∀ (a : OAct (𝓞 E) A), (∀ z, (a.act z).left ≫ π = π ≫ (Xo.univ.t.act.act z).left) → ∀ {ψ : LinearMap.BilinForm S (HdR A)}, IsPolForm (dp0 S) (𝟙 _) A (Xo.univ.t.PP.L.pull π) ψ → IsAdjointFor a (fun z => H.bar z) ψ := by
  first | exact @GlobalTheory.PolAdjointRing.polForm_adjoint | exact GlobalTheory.PolAdjointRing.polForm_adjoint | (intros; apply GlobalTheory.PolAdjointRing.polForm_adjoint <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKodairaSpencerMatrixFirstOrderDeformation

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.TangentOrigin
open GlobalTheory.FlagMod GlobalTheory.TopForm
open GlobalTheory.FlagTan (dimFlag psiSet TIx HIx VIx IsTanFrame IsDef IsVert KSIso kap)
open GlobalTheory.AllWt (exOf)
open scoped Classical
open GlobalTheory.DeRham GlobalTheory.Cris
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false


noncomputable section

namespace GlobalTheory.FlagTan

open TensorProduct GlobalTheory.Frames GlobalTheory.Published

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem IsKSR.baseChangeForKSFamily (P : AbelianDeRham) {Φ : Finset (E →+* ℂ)} {S S' : Type} [CommRing S] [Algebra c.F S]
    [CommRing S'] [Algebra c.F S'] {ψ : S →ₐ[c.F] S'} {y : FrPt Xo c S} {y' : FrPt Xo c S'} (h : FrMap ψ y y')
    {x : Sp (DualNumber S) ⟶ Xo.X} {M : HIx Dw Φ → S}
    (hM : IsKSR Φ y x M) : IsKSR Φ y' (spMap (dualMap ψ.toRingHom) ≫ x) (ψ ∘ M) := by
  obtain ⟨A, _, A', _, π, π', i, hi, b, ub, hb, hπ, hπ', e, hpol, hu, hl, hM⟩ := hM
  let : Algebra S S' := ψ.toRingHom.toAlgebra
  obtain ⟨B, _, φ, hφ⟩ := exists_isGrpPullback A (spMap (algebraMap S S'))
  obtain ⟨B', _, φ', hφ'⟩ := exists_isGrpPullback A' (spMap (dualMap (algebraMap S S')))
  have e₀ : spMap (algebraMap S S') ≫ GlobalTheory.DeRham.epsRed S = GlobalTheory.DeRham.epsRed S' ≫ spMap (dualMap (algebraMap S S')) := by
    rw [← Cris.spMap_comp, ← Cris.spMap_comp]
    congr 1
    ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  have w : (φ ≫ i) ≫ A'.hom = (B.hom ≫ GlobalTheory.DeRham.epsRed S') ≫ spMap (dualMap (algebraMap S S')) := by
    rw [(hφ.comp hi).1.w, e₀, Category.assoc]
  have sq : hφ'.1.lift _ _ w ≫ φ' = φ ≫ i := hφ'.1.lift_fst _ _ _
  have hj : IsGrpPullback B B' (GlobalTheory.DeRham.epsRed S') (hφ'.1.lift _ _ w) :=
    hφ'.cancel ((hφ.comp hi).congr e₀ sq.symm) (hφ'.1.lift_snd _ _ _)
  have hU := ObjDim.isAbelianScheme Xo.univ
  have hg := ObjDim.smoothOfRelativeDimension Xo.univ
  have hA := PolPull.isAbelianScheme_of_isGrpPullback hU hπ
  have gA := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hπ.1 hg
  have hA' := PolPull.isAbelianScheme_of_isGrpPullback hU hπ'
  have gA' := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hπ'.1 hg
  obtain ⟨bc, hF⟩ := P.2.2.1 S A _ hA gA S' B φ hφ
  have hL := (P.2.1 S' B _ (PolPull.isAbelianScheme_of_isGrpPullback hA hφ)
    ((smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hφ.1 gA)).1
  obtain ⟨b', hpol', eb⟩ := hpol.pull_comp (AbelianDeRham.bcMor hφ) (UnivPol.pol Xo).isLB
  choose tv htv using ArcQ.NormalForm.exists_baseChange hφ
  choose th hth using bc.exists
  refine ⟨B, _, B', _, φ ≫ π, φ' ≫ π', _, hj, b', fun σ k => tv (ub σ k), fun k => th (hb k),
    (hφ.comp hπ).congr h.1.symm rfl, hφ'.comp hπ', by rw [← Category.assoc, sq, Category.assoc, e], hpol',
    fun σ k => ?_, fun σ k => (hl σ k).baseChange (hφ := hφ) hF hL (hth _) (htv _), fun τ a => ?_⟩
  · rw [← Category.assoc, htv, Category.assoc, hu, h.2.1] <;> rfl
  · obtain ⟨w, hw, f, hf, hd, hv⟩ := hM τ a
    refine ⟨tv w, ArcQ.NormalForm.isLieComb_baseChange hφ (fun _ => htv _) (htv w) hw, th f,
      mem_Fil_of_corr (hφ := hφ) hF (hth f) hf, fun k => ?_,
      hv.baseChange (hφ := hφ) P hA' gA' hj hφ' sq (hth f) (htv w)⟩
    rw [eb _ _ _ _ (hth f) (hth _), hd]
    split_ifs <;> simp


end GlobalTheory.FlagTan

namespace GlobalTheory.KSFam

theorem conj_embK' {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} (c : Coeff l)
    (τ : E →+* ℂ) (z : 𝓞 E) : embK c (conjEmb τ) (H.bar z) = embK c τ z := by
  apply Subtype.ext
  rw [embK_coe, embK_coe]
  show starRingEnd ℂ (τ ((H.bar z : 𝓞 E) : E)) = τ (z : E)
  rw [H.9 z, NumberField.IsCMField.complexEmbedding_complexConj, Complex.conj_conj]

theorem ksFamily : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (hP : GlobalTheory.Published.AbelianDeRham) {S : Type} [CommRing S] [Algebra c.F S]
    (y : FrPt Xo c S) (x' : Sp (DualNumber S) ⟶ Xo.X) (h1 : x' ≫ Xo.s = sOf c (DualNumber S))
    (h2 : spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ x' = y.x), ∃ Mx : HIx Dw (psiSet H) → S, ∀ (K : Type) [Field K] [Algebra c.F K] (ψ : S →ₐ[c.F] K) (y' : FrPt Xo c K),
      FrMap ψ y y' → GlobalTheory.FlagTan.IsKS (psiSet H) y' (spMap (Formalism.L2.Pj.dualMap ψ.toRingHom) ≫ x') (ψ ∘ Mx) := by
  intro E _ _ _ H Dw l Xo c hP S _ _ y x' h1 h2
  suffices hM : ∃ M, GlobalTheory.FlagTan.IsKSR (psiSet H) y x' M by
    obtain ⟨M, hM⟩ := hM
    refine ⟨M, fun K _ _ ψ y' hy => GlobalTheory.FlagTan.isKSR_iff_isKS.mp ?_⟩
    exact GlobalTheory.FlagTan.IsKSR.baseChangeForKSFamily hP hy hM

  let : GrpObj ((Over.pullback x').obj Xo.univ.t.G) := Functor.grpObjObj (F := Over.pullback x')
  let : GrpObj ((Over.pullback (GlobalTheory.DeRham.epsRed S)).obj ((Over.pullback x').obj Xo.univ.t.G)) :=
    Functor.grpObjObj (F := Over.pullback (GlobalTheory.DeRham.epsRed S))
  have hA' := isGrpPullback_pullback Xo.univ.t.G x'
  have hi := isGrpPullback_pullback ((Over.pullback x').obj Xo.univ.t.G) (GlobalTheory.DeRham.epsRed S)
  have hA : IsGrpPullback ((Over.pullback (GlobalTheory.DeRham.epsRed S)).obj ((Over.pullback x').obj Xo.univ.t.G))
      Xo.univ.t.G y.x (pullback.fst _ _ ≫ pullback.fst _ _) := (hi.comp hA').congr h2 rfl
  have : IsCommMonObj ((Over.pullback (GlobalTheory.DeRham.epsRed S)).obj ((Over.pullback x').obj Xo.univ.t.G)) :=
    GlobalTheory.PolPull.isCommMonObj_of_isGrpPullback hA
  have hab := GlobalTheory.ObjDim.isAbelianScheme Xo.univ
  have hsm := GlobalTheory.ObjDim.smoothOfRelativeDimension Xo.univ
  have hab' := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hab hA'
  have hab0 := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hab hA
  have hsm' : SmoothOfRelativeDimension (Module.finrank ℚ E / 2 * (Dw.p + Dw.q))
      ((Over.pullback x').obj Xo.univ.t.G).hom := by
    exact (smoothOfRelativeDimension_isStableUnderBaseChange (n := Module.finrank ℚ E / 2 * (Dw.p + Dw.q))).of_isPullback
      (IsPullback.of_hasPullback _ _) hsm
  have hsm0 : SmoothOfRelativeDimension (Module.finrank ℚ E / 2 * (Dw.p + Dw.q))
      ((Over.pullback (GlobalTheory.DeRham.epsRed S)).obj ((Over.pullback x').obj Xo.univ.t.G)).hom := by
    exact (smoothOfRelativeDimension_isStableUnderBaseChange (n := Module.finrank ℚ E / 2 * (Dw.p + Dw.q))).of_isPullback
      (IsPullback.of_hasPullback _ _) hsm'

  obtain ⟨ψ, hpol, hiso, hperf, hmax⟩ := GlobalTheory.T.exists_polarization_form_isotropic_filtration hP Xo hA

  obtain ⟨a', ha'⟩ := GlobalTheory.OActPull.exists_oAct_of_isGrpPullback Xo.univ.t.act hA'
  obtain ⟨a, ha⟩ := GlobalTheory.OActPull.exists_oAct_of_isGrpPullback a' hi
  have haπ : ∀ z, (a.act z).left ≫ (pullback.fst _ _ ≫ pullback.fst _ _) =
      (pullback.fst _ _ ≫ pullback.fst _ _) ≫ (Xo.univ.t.act.act z).left := by
    intro z
    rw [← Category.assoc, ha z, Category.assoc, ha' z, Category.assoc]
  have hadj := GlobalTheory.T.polarizationForm_adjoint_cmAction_moduli_point hP Xo hA a haπ hpol

  obtain ⟨ub, hub1, hubT, hubE, hubS⟩ := GlobalTheory.T.exists_tangent_frame_of_framedPoint_commRing y hA a haπ
  have hex : ∀ k : (Σ σ : E →+* ℂ, Fin (Dw.mult σ)), ∃ h, IsLieImage h (ub k.1 k.2) := fun k =>
    (hP.2.1 S _ _ hab0 hsm0).1.2 _ (hubT k.1 k.2)
  choose hb hhb using hex
  obtain ⟨hspan, hlin⟩ := GlobalTheory.T.grp_pullback_basis_lift_compatible hP y hA ub hub1 hb hhb
  have hreg := GlobalTheory.T.kodairaSpencerUniqueValue_abelianScheme_commRing hP hi hab' hsm'
  have hcomp := fun z f w (e : IsKSValue hi f w) => GlobalTheory.T.isKodairaSpencerValue_endomorphism_lift hi a a' ha z e
  have heig : ∀ (k : (Σ σ : E →+* ℂ, Fin (Dw.mult σ))) (z : 𝓞 E),
      act (dp0 S) (𝟙 _) a z (hb k) - (algebraMap c.F S).comp (embK c k.1) z • hb k ∈
        Fil ((Over.pullback (GlobalTheory.DeRham.epsRed S)).obj ((Over.pullback x').obj Xo.univ.t.G)) := by
    intro k z
    have := a.hom z
    have e1 := (hhb k).push (a.act z)
    rw [hubE] at e1
    rw [act_apply]
    exact e1.sub_mem ((hhb k).smul _)
  have key : ∀ (τ : psiSet H) (j : Fin (Dw.mult (conjEmb τ.1))), ∃ cf : Fin (Dw.mult τ.1) → S, ∃ w,
      IsLieComb cf (ub τ.1) w ∧ GlobalTheory.FlagTan.IsKSRow hi ψ hb ⟨conjEmb τ.1, j⟩ w := fun τ j =>
    GlobalTheory.T.kodairaSpencerRow_dual_eigenvector_mem_span_ring hi a (fun z => H.bar z) ψ hiso hmax hperf hadj hreg hcomp
      (fun σ => (algebraMap c.F S).comp (embK c σ)) ub hb hspan hlin heig hubS τ.1 (conjEmb τ.1)
      (fun z => by simp only [RingHom.comp_apply, conj_embK']) j
  choose cf hcf using key
  exact ⟨fun k => cf k.1 k.2.1 k.2.2, _, inferInstance, _, inferInstance, _, _, _, hi, ψ, ub, hb, hA, hA', rfl, hpol,
    hub1, fun σ k => hhb ⟨σ, k⟩, fun τ j => hcf τ j⟩

end GlobalTheory.KSFam
end
end
end
