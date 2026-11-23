module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SlopeBoundSt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformisationTriplesCompleteDVRTorsion
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ProperRelAmpleKTrivOfFieldExtension
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CommGroupCommonFactorQuotientCancel
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUnitOfIsWtZero
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
public import Mathlib.Basic.Complex.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSectionPrimitiveBundleTranslateLocalRingStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SplitTorusHomProperTrivialField
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsMonHomPointedSplitExtToAbelianVariety
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.CategoryTheory.ExtremalEpi
public import Development.WeilBound.CoreStatements.HodgeTatePoints.PpicTransl
public import Development.WeilBound.CoreStatements.HodgeTatePoints.PpicWeight
public import Development.WeilBound.CoreStatements.HodgeTatePoints.PquoFibre
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSplitExtIsGtOfTorusExtension
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsSemiAbelianOfProperGenericTorusExtensionSpecialFiber
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.TypeStar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AdmissibleBasePowerSeries

-- Source module: Development.WeilBound.CoreStatements.HodgeTatePoints.PpicLamdiff

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace PositivityTheory.HtPt.Ppic
open GlobalTheory.CechPic GlobalTheory.UU

noncomputable def tqOfIso {S : Scheme.{0}} {X : Type} [AddCommGroup X] {G : Over S} [GrpObj G] (T : TQ G X) {A : Over S}
    [GrpObj A] (hA : IsAbelianScheme A) (β : T.B ≅ A) [IsMonHom β.hom] : TQ G X :=
  haveI : IsIso β.hom.left := inferInstanceAs (IsIso ((Over.forget _).map β.hom))
  { B := A
    comm := hA.comm
    isAb := hA
    q := T.q ≫ β.hom
    i := T.i
    q_hom := by have := T.q_hom; infer_instance
    i_hom := T.i_hom
    q_flat := by have := T.q_flat; rw [Over.comp_left]; infer_instance
    q_surj := by have := T.q_surj; rw [Over.comp_left]; infer_instance
    q_affine := by have := T.q_affine; rw [Over.comp_left]; infer_instance
    isKernel := by
      have sq : IsPullback η[T.B] (𝟙 _) β.hom η[A] :=
        IsPullback.of_vert_isIso ⟨by rw [IsMonHom.one_hom, Category.id_comp]⟩
      have h := T.isKernel.paste_vert sq
      rwa [Category.comp_id] at h
    loc := fun b χ => by
      obtain ⟨V, hV, u, hu⟩ := T.loc (β.inv.left b) χ
      have le : (T.q ≫ β.hom).left ⁻¹ᵁ (β.inv.left ⁻¹ᵁ V) ≤ T.q.left ⁻¹ᵁ V := by
        rw [← Scheme.Hom.comp_preimage, ← Over.comp_left, Category.assoc, β.hom_inv_id, Category.comp_id]
      exact ⟨β.inv.left ⁻¹ᵁ V, hV, res le u, hu.res le⟩ }

theorem lamdiff : (∀ (k : Type) [Field k] [IsAlgClosed k] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (G : Over (Sp k)) [GrpObj G] [IsCommMonObj G] (T : GlobalTheory.UU.TQ G X) (N : LB T.B.left), N.IsLB → ∀ t : LB.Gen (N.pull T.q.left), t.IsGen → ∃ (χ : X) (t' : LB.Gen (N.pull T.q.left)), T.GenWt N t' χ) → ∀ (Q : Out.PolAV (Sp ℂ)) (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (G : Over (Sp ℂ)) [GrpObj G] [IsCommMonObj G] (T : GlobalTheory.UU.TQ G X) (β : T.B ≅ Q.A), IsMonHom β.hom → ∀ M : LB Q.A.left, M.IsLB → LBIso (M.pull (T.q ≫ β.hom).left) (Q.L.pull (T.q ≫ β.hom).left) → ∃ u : LB.Gen (abelian₂ Q.A (LB.div M Q.L)), u.IsGen := by
  intro hw Q X _ _ _ G _ _ T β hβ M hM hiso
  haveI := hβ
  have hL := Q.isLB
  have hN : (LB.div M Q.L).IsLB := LB.isLB_div hM hL
  have hNp : ((LB.div M Q.L).pull (T.q ≫ β.hom).left).IsLB := LB.isLB_pull hN _
  have hc : cls ((LB.div M Q.L).pull (T.q ≫ β.hom).left) hNp = 0 := by
    rw [cls_pull hN _ hNp, cls_div hM hL hN, map_sub,
      ← cls_pull hM _ (LB.isLB_pull hM _), ← cls_pull hL _ (LB.isLB_pull hL _), sub_eq_zero]
    exact (cls_eq_iff _ _).2 hiso
  obtain ⟨t, ht⟩ := (cls_eq_zero_iff hNp).1 hc
  let T' := tqOfIso T Q.isAb β
  obtain ⟨χ, t', ht'⟩ := hw ℂ X G T' (LB.div M Q.L) hN t ht
  obtain ⟨N', s, hN', hs, u, hu⟩ := GlobalTheory.WtBundle.exists_genWt T' χ
  have hI : LBIso (LB.div M Q.L) N' := GlobalTheory.UU.lbIso_of_genWt _ X G T' _ N' t' s χ hN hN' ht' hs
  have hLam : (abelian₂ Q.A (LB.div M Q.L)).IsLB := LB.isLB_linComb hN _ _
  have hLam' : (abelian₂ Q.A N').IsLB := LB.isLB_linComb hN' _ _
  have h0 := (cls_eq_zero_iff hLam').2 ⟨u, hu⟩
  refine (cls_eq_zero_iff hLam).1 ?_
  refine (cls_linComb hN _ _ hLam).trans ?_
  rw [(cls_eq_iff hN hN').2 hI]
  exact (cls_linComb hN' _ _ hLam').symm.trans h0

end PositivityTheory.HtPt.Ppic
end
end

-- Source module: Development.WeilBound.CoreStatements.HodgeTatePoints.PpicPic

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace PositivityTheory.HtPt.Ppic
open GlobalTheory.CechPic

theorem pic : ∀ (Q : Out.PolAV (Sp ℂ)) (M : LB Q.A.left), M.IsLB → (∃ u : LB.Gen (abelian₂ Q.A (LB.div M Q.L)), u.IsGen) → ∃ x : 𝟙_ (Over (Sp ℂ)) ⟶ Q.A, LBIso M (Q.L.pull ((toUnit Q.A ≫ x) * 𝟙 Q.A).left) := by
  intro Q M hM hu
  have hO : (LB.div M Q.L).IsLB := LB.isLB_div hM Q.isLB
  obtain ⟨x, hx⟩ := GlobalTheory.T.exists_section_primitiveBundle_translate_localRing GlobalTheory.abelianSchemeLaws_all.1 GlobalTheory.abelianSchemeLaws_all.2 ℂ Q _ hO hu
  refine ⟨x, ?_⟩
  have e := (cls_eq_iff hO (LB.isLB_linComb Q.isLB _ _)).2 hx
  rw [cls_div hM Q.isLB, cls_linComb Q.isLB, Fin.sum_univ_two] at e
  refine (cls_eq_iff hM (pull_isLB Q.isLB _)).1 ?_
  rw [cls_pull Q.isLB]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, neg_smul, pull_id] at e
  rw [← sub_eq_add_neg] at e
  exact sub_left_injective e

end PositivityTheory.HtPt.Ppic
end
end

-- Source module: Development.WeilBound.CoreStatements.HodgeTatePoints.PpicQuot

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace PositivityTheory.HtPt.Ppic

theorem exists_factor_torus {K : Type} [Field K] [IsAlgClosed K] {G B B' : Over (Sp K)} [GrpObj G] [GrpObj B] [GrpObj B']
    (hB' : IsAbelianScheme B') {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (i : splitTorus (Sp K) X ⟶ G) (q : G ⟶ B) [IsMonHom i] [IsMonHom q] [Flat q.left] [Surjective q.left]
    [QuasiCompact q.left] (hk : IsPullback i (toUnit _) q (η : 𝟙_ _ ⟶ B)) (f : G ⟶ B') [IsMonHom f] :
    ∃ a : B ⟶ B', q ≫ a = f := by
  haveI : IsProper B'.hom := hB'.proper
  have hif : i ≫ f = toUnit _ ≫ η :=
    GlobalTheory.splitTorus_hom_proper_trivial_field K X B' (i ≫ f) inferInstance
  refine GlobalTheory.ExtensionRigidity.exists_factor q f ?_
  intro W a b hab
  have h1 := map_div (IsMonHom.monoidHom q W) a b
  simp only [IsMonHom.monoidHom_apply] at h1
  rw [hab, div_self'] at h1
  have hc : (a / b) ≫ q = toUnit W ≫ η := by rw [h1, Hom.one_def]
  have e2 : (a / b) ≫ f = 1 := by
    rw [← hk.lift_fst (a / b) (toUnit W) hc, Category.assoc, hif, ← Category.assoc, Hom.one_def]
    congr 1
    exact toUnit_unique _ _
  have h3 := map_div (IsMonHom.monoidHom f W) a b
  simp only [IsMonHom.monoidHom_apply] at h3
  rw [e2] at h3
  exact div_eq_one.1 h3.symm

theorem quot : ∀ (G : Over (Sp ℂ)) [GrpObj G] [IsCommMonObj G] (τ : TorusExtension G) (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (T : GlobalTheory.UU.TQ G X), letI := τ.grpB; ∃ e : τ.B ≅ T.B, IsMonHom e.hom ∧ τ.q ≫ e.hom = T.q := by
  intro G _ _ τ X _ _ _ T
  letI := τ.grpB
  letI := τ.addCommGroup
  haveI := τ.free
  haveI := τ.finite
  haveI := τ.q_hom
  haveI := τ.q_flat
  haveI := τ.q_surjective
  haveI := τ.q_quasiCompact
  haveI := τ.i_hom
  haveI := T.q_hom
  haveI := T.q_flat
  haveI := T.q_surj
  haveI := T.q_affine
  haveI := T.i_hom
  obtain ⟨a, ha⟩ := exists_factor_torus T.isAb τ.i τ.q τ.isKernel T.q
  obtain ⟨b, hb⟩ := exists_factor_torus τ.isAbelian T.i T.q T.isKernel τ.q
  haveI : Epi τ.q := Over.epi_of_epi_left _
  haveI : Epi T.q := Over.epi_of_epi_left _
  haveI : MorphismProperty.IsStableUnderComposition @Surjective :=
    { comp_mem := fun f g hf hg => by haveI := hf; haveI := hg; infer_instance }
  haveI : Epi (τ.q ⊗ₘ τ.q) := by
    haveI : Flat (τ.q ⊗ₘ τ.q).left :=
      MorphismProperty.pullbackMap (P := @Flat) τ.q_flat τ.q_flat (Over.w τ.q).symm (Over.w τ.q).symm
    haveI : Surjective (τ.q ⊗ₘ τ.q).left :=
      MorphismProperty.pullbackMap (P := @Surjective) τ.q_surjective τ.q_surjective
        (Over.w τ.q).symm (Over.w τ.q).symm
    haveI : QuasiCompact (τ.q ⊗ₘ τ.q).left :=
      MorphismProperty.pullbackMap (P := @QuasiCompact) τ.q_quasiCompact τ.q_quasiCompact
        (Over.w τ.q).symm (Over.w τ.q).symm
    exact Over.epi_of_epi_left _
  have hma : IsMonHom a := by
    refine ⟨?_, ?_⟩
    · rw [← IsMonHom.one_hom τ.q, Category.assoc, ha, IsMonHom.one_hom]
    · rw [← cancel_epi (τ.q ⊗ₘ τ.q), ← IsMonHom.mul_hom_assoc, ha, IsMonHom.mul_hom,
        tensorHom_comp_tensorHom_assoc, ha]
  refine ⟨⟨a, b, ?_, ?_⟩, hma, ha⟩
  · rw [← cancel_epi τ.q, reassoc_of% ha, hb, Category.comp_id]
  · rw [← cancel_epi T.q, reassoc_of% hb, ha, Category.comp_id]

end PositivityTheory.HtPt.Ppic
end
end

-- Source module: Development.WeilBound.CoreStatements.HodgeTatePoints.PquoSplit

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj

namespace PositivityTheory.HtPt.Pquo

theorem split : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (r : V →+* ℂ) (tV : SAB H (Sp V)), Function.Surjective r → RingHom.ker r = IsLocalRing.maximalIdeal V → ∀ P : AbPart tV (spMap r), GlobalTheory.LN.SplitOver tV.G (IsLocalRing.maximalIdeal V) := by
  intro E _ _ _ H V _ _ _ r tV hs hk P
  obtain ⟨ψ, hψ⟩ : ∃ ψ : ℂ →+* V ⧸ IsLocalRing.maximalIdeal V,
      ψ.comp r = Ideal.Quotient.mk (IsLocalRing.maximalIdeal V) :=
    ⟨r.liftOfRightInverse _ (Function.rightInverse_surjInv hs)
      ⟨Ideal.Quotient.mk (IsLocalRing.maximalIdeal V), by rw [hk, Ideal.mk_ker]⟩,
      RingHom.liftOfRightInverse_comp _ _ _ _⟩
  letI : Field (V ⧸ IsLocalRing.maximalIdeal V) := Ideal.Quotient.field _
  have e : spMap ψ ≫ spMap r = spMap (Ideal.Quotient.mk (IsLocalRing.maximalIdeal V)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hψ]
  obtain ⟨T⟩ := GlobalTheory.SS.nonempty_torusExtension_pullback (Ω := V ⧸ IsLocalRing.maximalIdeal V) (spMap ψ) P.tK.G ⟨P.τ⟩
  obtain ⟨i, hi, -⟩ := grpPullback_iso
    (((isGrpPullback_pullback P.tK.G (spMap ψ)).comp P.m.cart).congr e rfl)
    (isGrpPullback_pullback tV.G (spMap (Ideal.Quotient.mk (IsLocalRing.maximalIdeal V))))
  exact GlobalTheory.exists_splitExt_isGt_of_torusExtension (V ⧸ IsLocalRing.maximalIdeal V) _ ⟨torusExtOfIso i T⟩

end PositivityTheory.HtPt.Pquo
end
end

-- Source module: Development.WeilBound.CoreStatements.HodgeTatePoints.PpicDvr

section

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

open Out

namespace PositivityTheory.HtPt.Ppic

private theorem isMonHom_comp_comp {C : Type*} [Category C] [CartesianMonoidalCategory C]
    {A B D F : C} [MonObj A] [MonObj B] [MonObj D] [MonObj F]
    (a : A ≅ B) (b : B ≅ D) (c : D ≅ F) (ha : IsMonHom a.hom) (hb : IsMonHom b.hom)
    (hc : IsMonHom c.hom) : IsMonHom (a.hom ≫ b.hom ≫ c.hom) := by
  infer_instance


open GlobalTheory.CechPic in
theorem isPrincipal_tB_of (hU : GlobalTheory.LN.UDvrSt) : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (r : V →+* ℂ) (tV : SAB H (Sp V)), GlobalTheory.LN.CDvr V → Function.Surjective r → RingHom.ker r = IsLocalRing.maximalIdeal V → GlobalTheory.LN.PolAt tV (Out.jK V) → ∀ P : AbPart tV (spMap r), IsPrincipal P.tB := by
  intro E _ _ _ H V _ _ _ r tV hC hr hker hpol P
  obtain ⟨Pu, -⟩ := hU E H V hC tV hpol (PositivityTheory.HtPt.Pquo.split E H V r tV hr hker P)
  obtain ⟨Q, X, _, _, _, T, β, hβ, hL⟩ := PositivityTheory.HtPt.Pquo.fibre E H V r tV hr hker Pu P
  obtain ⟨e', he', hq⟩ := PositivityTheory.HtPt.Ppic.quot P.tK.G P.τ X T
  letI := P.τ.grpB
  let g : Q.A ≅ P.tB.G := Iso.trans β.symm (Iso.trans e'.symm P.e)
  haveI : IsMonHom g.hom :=
    isMonHom_comp_comp β.symm e'.symm P.e (by show IsMonHom β.inv; infer_instance)
      (by show IsMonHom e'.inv; infer_instance) P.e_hom
  have hLB := P.tB.PP.isLB
  have hQL := Q.isLB
  have hKL := P.tK.PP.isLB
  have hMLB : (P.tB.PP.L.pull g.hom.left).IsLB := LB.isLB_pull hLB _
  have hrefl : LBIso (P.tB.PP.L.pull g.hom.left) (P.tB.PP.L.pull g.hom.left) :=
    (cls_eq_iff hMLB hMLB).1 rfl
  have hcomp : (T.q ≫ β.hom).left ≫ g.hom.left = (P.τ.q ≫ P.e.hom).left := by
    rw [← Over.comp_left]
    congr 1
    simp only [g, Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc]
    rw [← hq, Category.assoc, Iso.hom_inv_id_assoc]
  have h1 : LBIso ((P.tB.PP.L.pull g.hom.left).pull (T.q ≫ β.hom).left)
      (P.tB.PP.L.pull (P.τ.q ≫ P.e.hom).left) :=
    GlobalTheory.GenSpread.lbIso_pull_of_lbIso hrefl _ hcomp.symm
  have h2 : LBIso ((P.tB.PP.L.pull g.hom.left).pull (T.q ≫ β.hom).left)
      (Q.L.pull (T.q ≫ β.hom).left) :=
    LBIso.trans (LB.isLB_pull hMLB _) (LB.isLB_pull hLB _) (LB.isLB_pull hQL _) h1
      (LBIso.trans (LB.isLB_pull hLB _) hKL (LB.isLB_pull hQL _) P.pp.symm hL)
  obtain ⟨u, hu⟩ := PositivityTheory.HtPt.Ppic.lamdiff PositivityTheory.HtPt.Ppic.weight Q X P.tK.G T β hβ _ hMLB h2
  obtain ⟨x, hx⟩ := PositivityTheory.HtPt.Ppic.pic Q _ hMLB ⟨u, hu⟩
  obtain ⟨hA, hK⟩ := PositivityTheory.HtPt.Ppic.transl Q _ hMLB x hx
  haveI := P.tB.semi.smooth
  haveI := P.tB.semi.separated
  haveI := P.tB.semi.quasiCompact
  haveI : IsProper Q.A.hom := Q.isAb.proper
  have hpb : IsGrpPullback Q.A P.tB.G (specOf (RingHom.id ℂ)) g.hom.left :=
    (isGrpPullback_of_iso g).congr (specOf_id ℂ).symm rfl
  exact GlobalTheory.AmpleDescent.proper_relAmple_kTriv_of_fieldExtension ℂ ℂ (RingHom.id ℂ) P.tB.G Q.A
    g.hom.left hpb P.tB.PP.L _ hLB hMLB hrefl inferInstance hA hK

theorem dvr : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (r : V →+* ℂ) (tV : SAB H (Sp V)), GlobalTheory.LN.CDvr V → Function.Surjective r → RingHom.ker r = IsLocalRing.maximalIdeal V → GlobalTheory.LN.PolAt tV (Out.jK V) → ∀ P : AbPart tV (spMap r), IsPrincipal P.tB :=
  isPrincipal_tB_of GlobalTheory.LN.uDvrSt_holds

end PositivityTheory.HtPt.Ppic
end
end
end
