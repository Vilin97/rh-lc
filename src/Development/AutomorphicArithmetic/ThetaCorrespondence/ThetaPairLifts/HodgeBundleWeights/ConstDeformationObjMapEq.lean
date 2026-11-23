module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Hypotheses2
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionDualNumberPointEqConstantCharZeroStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ESecCompOfIsGrpPullback
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RelAmpleOfGenericIso
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FamilyFibreEqUniformisedPullbackGenericFibre
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoTangentPullConstantDeformationStatement
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsGrpPullbackOfLoc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigIsoCongr
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ConstDeformationActionTrivial

section

@[expose] public section

section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory MonObj MonoidalCategory
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.ConstDeform
theorem constDeformation_act_eq : _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.GrothendieckDeformation → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K) (x' : Sp (DualNumber K) ⟶ Xo.X), 1 ≤ Dw.p + Dw.q → GlobalTheory.FlagTan.IsTanX y x' → ∀ (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (π : A.left ⟶ Xo.univ.t.G.left) (π' : A'.left ⟶ Xo.univ.t.G.left) (i : A.left ⟶ A'.left) (q : A'.left ⟶ A.left), IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i → IsGrpPullback A Xo.univ.t.G y.x π → IsGrpPullback A' Xo.univ.t.G x' π' → i ≫ π' = π → i ≫ q = 𝟙 _ → IsGrpPullback A' A (spMap (algebraMap K (DualNumber K))) q → ∀ (o : Obj Dw l (baseKA l) (x' ≫ Xo.s)) (m : ObjMap o Xo.univ x') (g : o.t.G.left ⟶ A'.left), g ≫ π' = m.cm.F → g ≫ A'.hom = o.t.G.hom → ∀ hF : IsGrpPullback o.t.G Xo.univ.t.G (constPt x') (g ≫ q ≫ π), ∀ a, (o.t.act.act a).left ≫ (g ≫ q ≫ π) = (g ≫ q ≫ π) ≫ (Xo.univ.t.act.act a).left := by
  intro hP hGD E _ _ _ H Dw l Xo c K _ _ y x' hpq hT A _ A' _ π π' i q hi hπ hπ' hiπ hiq hq o m g hg hgw hF a
  haveI := Xo.univ.t.act.hom a
  have wβ : (π ≫ (Xo.univ.t.act.act a).left) ≫ Xo.univ.t.G.hom = A.hom ≫ y.x := by
    rw [Category.assoc, Over.w (Xo.univ.t.act.act a), hπ.1.w]
  let β : A ⟶ A := Over.homMk (hπ.1.lift _ A.hom wβ) (hπ.1.lift_snd _ _ _)
  have hβ : β.left ≫ π = π ≫ (Xo.univ.t.act.act a).left := hπ.1.lift_fst _ _ _
  haveI : IsMonHom β := GlobalTheory.UU.isMonHom_of_over_isMonHom hπ hπ (Xo.univ.t.act.act a) β hβ
  have wα : (π' ≫ (Xo.univ.t.act.act a).left) ≫ Xo.univ.t.G.hom = A'.hom ≫ x' := by
    rw [Category.assoc, Over.w (Xo.univ.t.act.act a), hπ'.1.w]
  let α : A' ⟶ A' := Over.homMk (hπ'.1.lift _ A'.hom wα) (hπ'.1.lift_snd _ _ _)
  have hα : α.left ≫ π' = π' ≫ (Xo.univ.t.act.act a).left := hπ'.1.lift_fst _ _ _
  haveI : IsMonHom α := GlobalTheory.UU.isMonHom_of_over_isMonHom hπ' hπ' (Xo.univ.t.act.act a) α hα
  have wδ : (q ≫ β.left) ≫ A.hom = A'.hom ≫ spMap (algebraMap K (DualNumber K)) := by
    rw [Category.assoc, Over.w β, hq.1.w]
  let δ : A' ⟶ A' := Over.homMk (hq.1.lift _ A'.hom wδ) (hq.1.lift_snd _ _ _)
  have hδ : δ.left ≫ q = q ≫ β.left := hq.1.lift_fst _ _ _
  haveI : IsMonHom δ := GlobalTheory.UU.isMonHom_of_over_isMonHom hq hq β δ hδ
  have hA' := PolPull.isAbelianScheme_of_isGrpPullback (ObjDim.isAbelianScheme Xo.univ) hπ'
  have gA' := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hπ'.1
    (ObjDim.smoothOfRelativeDimension Xo.univ)
  have LH := (hGD.at_dualNumber K).2.2
  have e1 : i ≫ α.left = β.left ≫ i := by
    apply hπ'.1.hom_ext
    · simp only [Category.assoc]
      rw [hα, reassoc_of% hiπ, hiπ, hβ]
    · simp only [Category.assoc]
      rw [Over.w α, hi.1.w, reassoc_of% (Over.w β)]
  have e2 : i ≫ δ.left = β.left ≫ i := by
    apply hq.1.hom_ext
    · simp only [Category.assoc]
      rw [hδ, reassoc_of% hiq, hiq, Category.comp_id]
    · simp only [Category.assoc]
      rw [Over.w δ, hi.1.w, reassoc_of% (Over.w β)]
  have hαδ : α = δ := GlobalTheory.Published.GrothendieckMessing.LiftHom.unique LH hi hA' gA' hi hA' gA' β e1 e2
  have hga : (o.t.act.act a).left ≫ g = g ≫ α.left := by
    apply hπ'.1.hom_ext
    · simp only [Category.assoc]
      rw [hα, hg, reassoc_of% hg]
      exact m.act a
    · simp only [Category.assoc]
      rw [hgw, Over.w α, hgw, Over.w (o.t.act.act a)]
  calc (o.t.act.act a).left ≫ (g ≫ q ≫ π) = g ≫ α.left ≫ q ≫ π := by rw [reassoc_of% hga]
    _ = g ≫ q ≫ π ≫ (Xo.univ.t.act.act a).left := by rw [hαδ, reassoc_of% hδ, hβ]
    _ = (g ≫ q ≫ π) ≫ (Xo.univ.t.act.act a).left := by simp only [Category.assoc]
end GlobalTheory.ConstDeform
end

section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory MonObj MonoidalCategory
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.const_deformation_action_trivial : _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.GrothendieckDeformation → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K) (x' : Sp (DualNumber K) ⟶ Xo.X), 1 ≤ Dw.p + Dw.q → GlobalTheory.FlagTan.IsTanX y x' → ∀ (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (π : A.left ⟶ Xo.univ.t.G.left) (π' : A'.left ⟶ Xo.univ.t.G.left) (i : A.left ⟶ A'.left) (q : A'.left ⟶ A.left), IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i → IsGrpPullback A Xo.univ.t.G y.x π → IsGrpPullback A' Xo.univ.t.G x' π' → i ≫ π' = π → i ≫ q = 𝟙 _ → IsGrpPullback A' A (spMap (algebraMap K (DualNumber K))) q → ∀ (o : Obj Dw l (baseKA l) (x' ≫ Xo.s)) (m : ObjMap o Xo.univ x') (g : o.t.G.left ⟶ A'.left), g ≫ π' = m.cm.F → g ≫ A'.hom = o.t.G.hom → ∀ hF : IsGrpPullback o.t.G Xo.univ.t.G (constPt x') (g ≫ q ≫ π), ∀ a, (o.t.act.act a).left ≫ (g ≫ q ≫ π) = (g ≫ q ≫ π) ≫ (Xo.univ.t.act.act a).left := by
  first | exact @_root_.GlobalTheory.ConstDeform.constDeformation_act_eq | exact _root_.GlobalTheory.ConstDeform.constDeformation_act_eq | (intros; apply _root_.GlobalTheory.ConstDeform.constDeformation_act_eq <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.CubicalStructureConstSectionPullback

section

@[expose] public section

section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory MonObj MonoidalCategory
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi
namespace GlobalTheory.ConstDefCub
theorem cubical_structure_pullback_const_point : _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.GrothendieckDeformation → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K) (x' : Sp (DualNumber K) ⟶ Xo.X), 1 ≤ Dw.p + Dw.q → GlobalTheory.FlagTan.IsTanX y x' → ∀ (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (π : A.left ⟶ Xo.univ.t.G.left) (π' : A'.left ⟶ Xo.univ.t.G.left) (i : A.left ⟶ A'.left) (q : A'.left ⟶ A.left), IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i → IsGrpPullback A Xo.univ.t.G y.x π → IsGrpPullback A' Xo.univ.t.G x' π' → i ≫ π' = π → i ≫ q = 𝟙 _ → IsGrpPullback A' A (spMap (algebraMap K (DualNumber K))) q → ∀ (o : Obj Dw l (baseKA l) (x' ≫ Xo.s)) (m : ObjMap o Xo.univ x') (g : o.t.G.left ⟶ A'.left), g ≫ π' = m.cm.F → g ≫ A'.hom = o.t.G.hom → ∀ hF : IsGrpPullback o.t.G Xo.univ.t.G (constPt x') (g ≫ q ≫ π), (cubeMapOf hF).IsPullCubical o.t.cub Xo.univ.t.cub := by
  intro hP hGD E _ _ _ H Dw l Xo c K _ _ y x' hpq htan A _ A' _ π π' i q hi hπ hπ' hiπ hiq hq o m g hg1 hg2 hF
  haveI : IsProper o.t.G.hom := o.proper
  have hA : IsAbelianScheme o.t.G := AbelianSchemeGerms.isAbelianScheme_of_proper o.t.G o.t.semi
  refine GlobalTheory.TripleModel.isPullCubical_of_lbIso GlobalTheory.SemiRigid.globalFns hA hF o.t.cub Xo.univ.t.cub ?_
  obtain ⟨w, -, hw, -⟩ := rigIso_congr rfl m.cm m.lin rfl rfl
  have K2 : LBIso (Xo.univ.t.PP.L.pull π') (Xo.univ.t.PP.L.pull (q ≫ π)) :=
    GlobalTheory.T.lineBundle_iso_tangent_pull_constant_deformation E H Dw l Xo c K y.x x' A A' π π' i q hi hπ hπ' hiπ hiq hq
  have hM := Xo.univ.t.PP.isLB
  have h1 : LBIso o.t.PP.L (Xo.univ.t.PP.L.pull (g ≫ π')) := hg1 ▸ ⟨w, hw⟩
  have h2 : LBIso ((Xo.univ.t.PP.L.pull π').pull g) (Xo.univ.t.PP.L.pull (g ≫ q ≫ π)) :=
    GlobalTheory.Ex.GenericFibre.lbIso_pull K2 g rfl
  have h3 : LBIso ((Xo.univ.t.PP.L.pull π').pull g) (Xo.univ.t.PP.L.pull (g ≫ π')) :=
    GlobalTheory.FamRep.lbIso_pull_pull hM π' g
  exact LBIso.trans o.t.PP.isLB (pull_isLB hM _) (pull_isLB hM _) h1
    (LBIso.trans (pull_isLB hM _) (pull_isLB (pull_isLB hM _) _) (pull_isLB hM _) h3.symm h2)
end GlobalTheory.ConstDefCub
end

section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory MonObj MonoidalCategory
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.cubical_structure_const_section_pullback : _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.GrothendieckDeformation → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K) (x' : Sp (DualNumber K) ⟶ Xo.X), 1 ≤ Dw.p + Dw.q → GlobalTheory.FlagTan.IsTanX y x' → ∀ (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (π : A.left ⟶ Xo.univ.t.G.left) (π' : A'.left ⟶ Xo.univ.t.G.left) (i : A.left ⟶ A'.left) (q : A'.left ⟶ A.left), IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i → IsGrpPullback A Xo.univ.t.G y.x π → IsGrpPullback A' Xo.univ.t.G x' π' → i ≫ π' = π → i ≫ q = 𝟙 _ → IsGrpPullback A' A (spMap (algebraMap K (DualNumber K))) q → ∀ (o : Obj Dw l (baseKA l) (x' ≫ Xo.s)) (m : ObjMap o Xo.univ x') (g : o.t.G.left ⟶ A'.left), g ≫ π' = m.cm.F → g ≫ A'.hom = o.t.G.hom → ∀ hF : IsGrpPullback o.t.G Xo.univ.t.G (constPt x') (g ≫ q ≫ π), (cubeMapOf hF).IsPullCubical o.t.cub Xo.univ.t.cub := by
  first | exact @_root_.GlobalTheory.ConstDefCub.cubical_structure_pullback_const_point | exact _root_.GlobalTheory.ConstDefCub.cubical_structure_pullback_const_point | (intros; apply _root_.GlobalTheory.ConstDefCub.cubical_structure_pullback_const_point <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ConstDeformationObjMapEq

section

@[expose] public section

section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory MonObj MonoidalCategory
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.ConstDeform
theorem constDeformation_objMap_eq : _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.GrothendieckDeformation → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K) (x' : Sp (DualNumber K) ⟶ Xo.X), 1 ≤ Dw.p + Dw.q → GlobalTheory.FlagTan.IsTanX y x' → ∀ (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (π : A.left ⟶ Xo.univ.t.G.left) (π' : A'.left ⟶ Xo.univ.t.G.left) (i : A.left ⟶ A'.left) (q : A'.left ⟶ A.left), IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i → IsGrpPullback A Xo.univ.t.G y.x π → IsGrpPullback A' Xo.univ.t.G x' π' → i ≫ π' = π → i ≫ q = 𝟙 _ → IsGrpPullback A' A (spMap (algebraMap K (DualNumber K))) q → ∀ o : Obj Dw l (baseKA l) (x' ≫ Xo.s), Nonempty (ObjMap o Xo.univ x') → Nonempty (ObjMap o Xo.univ (constPt x')) := by
  intro hP hGD E _ _ _ H Dw l Xo c K _ _ y x' hpq hT A _ A' _ π π' i q hi hπ hπ' hiπ hiq hq o ⟨m⟩
  have hw : m.cm.F ≫ Xo.univ.t.G.hom = o.t.G.hom ≫ x' := m.cart.1.w
  let g : o.t.G.left ⟶ A'.left := hπ'.1.lift m.cm.F o.t.G.hom hw
  have hg : g ≫ π' = m.cm.F := hπ'.1.lift_fst _ _ _
  have hgw : g ≫ A'.hom = o.t.G.hom := hπ'.1.lift_snd _ _ _
  have hgc : IsGrpPullback o.t.G A' (𝟙 _) g :=
    hπ'.cancel (m.cart.congr (Category.id_comp _).symm hg.symm) (by rw [hgw, Category.comp_id])
  have hred : spMap (algebraMap K (DualNumber K)) ≫ y.x = constPt x' := by
    rw [← hT.2]; rfl
  have hF : IsGrpPullback o.t.G Xo.univ.t.G (constPt x') (g ≫ q ≫ π) :=
    (hgc.comp (hq.comp hπ)).congr (by rw [Category.id_comp, hred]) rfl
  haveI : CharZero K := (RingHom.charZero_iff (algebraMap c.F K).injective).1 inferInstance
  have hgq := hgc.comp hq
  have hcomm : ∀ (T : Over (Sp K)) (x y : T ⟶ A), x * y = y * x := by
    intro T x y
    apply Over.OverMorphism.ext
    apply hπ.1.hom_ext
    · have e1 := hπ.2 T x y (pushPt hπ.1.w x) (pushPt hπ.1.w y) rfl rfl
      have e2 := hπ.2 T y x (pushPt hπ.1.w y) (pushPt hπ.1.w x) rfl rfl
      rw [← e1, ← e2, _root_.mul_comm]
    · rw [Over.w (x * y), Over.w (y * x)]
  have key : ∀ (σ : 𝟙_ (Over (Sp (DualNumber K))) ⟶ o.t.G) (τ : 𝟙_ (Over Xo.X) ⟶ Xo.univ.t.G) (n : ℕ),
      0 < n → σ ^ n = 1 → σ.left ≫ m.cm.F = x' ≫ τ.left →
      σ.left ≫ (g ≫ q ≫ π) = constPt x' ≫ τ.left := by
    intro σ τ n hn hσ hστ
    let u := pushHom hgq (𝟙_ (Over (Sp (DualNumber K)))) σ
    have hu : u ^ n = 1 := by rw [← map_pow, hσ, map_one]
    have e := GlobalTheory.T.torsion_dualNumber_point_eq_constant_charZero K A _ (by simp) (hcomm _) u n hn hu
    have hul : u.left = σ.left ≫ g ≫ q := by
      show σ.left ≫ (g ≫ q) = _; rfl
    rw [hul] at e
    let w := spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ σ.left ≫ g
    have hw' : w ≫ A'.hom = 𝟙 _ ≫ GlobalTheory.DeRham.epsRed K := by
      simp only [w, Category.assoc, hgw, Category.id_comp]
      rw [Over.w σ]; rfl
    let s₀ := hi.1.lift w (𝟙 _) hw'
    have hs₀ : s₀ ≫ i = w := hi.1.lift_fst _ _ _
    calc σ.left ≫ (g ≫ q ≫ π) = (σ.left ≫ g ≫ q) ≫ π := by simp only [Category.assoc]
      _ = (spMap (algebraMap K (DualNumber K)) ≫ w ≫ q) ≫ π := by rw [e]; simp only [w, Category.assoc]
      _ = spMap (algebraMap K (DualNumber K)) ≫ s₀ ≫ i ≫ π' := by
          rw [← hs₀]; simp only [Category.assoc]; rw [reassoc_of% hiq, hiπ]
      _ = spMap (algebraMap K (DualNumber K)) ≫ spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ σ.left ≫ m.cm.F := by
          rw [reassoc_of% hs₀]; simp only [w, Category.assoc, hg]
      _ = constPt x' ≫ τ.left := by rw [hστ]; rfl
  have hpow : ∀ (f : Dw.La → (𝟙_ (Over (Sp (DualNumber K))) ⟶ o.t.G)), (∀ a b, f (a + b) = f a * f b) →
      ∀ (n : ℕ) a, f (n • a) = f a ^ n := by
    intro f hf n a
    induction n with
    | zero =>
      have h0 := hf 0 0
      rw [add_zero] at h0
      rw [zero_smul, pow_zero]
      exact mul_left_cancel (h0.symm.trans (_root_.mul_one _).symm)
    | succ n ih => rw [succ_nsmul, hf, ih, pow_succ]
  have hM : ((l.M : ℕ) : 𝓞 E) ∈ l.Mb := by
    have h1 : ((l.M : ℕ) : 𝓞 E) ∈ l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
      rw [l.prod]; exact Ideal.mem_span_singleton_self _
    exact Ideal.mul_le_left (I := l.Mb) (J := l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) h1
  exact ⟨{
    cm := cubeMapOf hF
    cart := hF
    base := rfl
    act := _root_.GlobalTheory.T.const_deformation_action_trivial hP hGD E H Dw l Xo c K y x' hpq hT A A' π π' i q hi hπ hπ' hiπ hiq hq o m g hg hgw hF
    lin := _root_.GlobalTheory.T.cubical_structure_const_section_pullback hP hGD E H Dw l Xo c K y x' hpq hT A A' π π' i q hi hπ hπ' hiπ hiq hq o m g hg hgw hF
    eta := fun a => key (o.eta a) (Xo.univ.eta a) l.M (by have := l.three_le; omega)
      (by rw [← hpow _ o.eta_add]; exact o.eta_ker _ (by
        rw [← Nat.cast_smul_eq_nsmul (𝓞 E)]; exact Submodule.smul_mem_smul hM Submodule.mem_top))
      (m.eta a)
    etaA := fun a => key (o.etaA a) (Xo.univ.etaA a) l.A l.A_pos
      (by rw [← hpow _ o.etaA_add]; exact o.etaA_ker a) (m.etaA a) }⟩
end GlobalTheory.ConstDeform
end

section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory MonObj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.const_deformation_obj_eq : _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.GrothendieckDeformation → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K) (x' : Sp (DualNumber K) ⟶ Xo.X), 1 ≤ Dw.p + Dw.q → GlobalTheory.FlagTan.IsTanX y x' → ∀ (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (π : A.left ⟶ Xo.univ.t.G.left) (π' : A'.left ⟶ Xo.univ.t.G.left) (i : A.left ⟶ A'.left) (q : A'.left ⟶ A.left), IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i → IsGrpPullback A Xo.univ.t.G y.x π → IsGrpPullback A' Xo.univ.t.G x' π' → i ≫ π' = π → i ≫ q = 𝟙 _ → IsGrpPullback A' A (spMap (algebraMap K (DualNumber K))) q → ∀ o : Obj Dw l (baseKA l) (x' ≫ Xo.s), Nonempty (ObjMap o Xo.univ x') → Nonempty (ObjMap o Xo.univ (constPt x')) := by
  first | exact @_root_.GlobalTheory.ConstDeform.constDeformation_objMap_eq | exact _root_.GlobalTheory.ConstDeform.constDeformation_objMap_eq | (intros; apply _root_.GlobalTheory.ConstDeform.constDeformation_objMap_eq <;> assumption)
end
end
end
