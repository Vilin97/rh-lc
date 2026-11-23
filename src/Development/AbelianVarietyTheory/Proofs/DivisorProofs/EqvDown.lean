module

public import Development.AbelianVarietyTheory.Definitions.Divisors.LabExt
public import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.InVVwIffOfNotTorsion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntertwiningBijectiveOfFieldBaseChangeStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FamExt
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FunEqZeroOfAffine
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Data.Nat.Choose.Multinomial
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FamExt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelPointsAlgClosureFractionRingBijectiveStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundlePowSectionsAlgClosureFieldBaseChangeStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionLabelsSurjectiveOfLargerAlgClosedFieldStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointOperatorSymmetricFrameFieldExtensionStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FinrankFamOfLaws
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnivIdentity

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearMapThetaGroupActionSections

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Desc

noncomputable section

namespace GlobalTheory.Mum.Desc

open GlobalTheory.FieldBaseChange

theorem exists_linear_isActOf : ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Sp (FractionRing R))) (F : Type) [Field F] [Algebra (FractionRing R) F] (N : ℕ) (θ : ThetaGrp A.A A.L (N : ℤ) (TFK (R := R) F)), ∃ b : SecF A F N →ₗ[F] SecF A F N, ∀ t t' : SecF A F N, IsActOf A.A A.L N θ t t' ↔ t' = b t := by
  intro R _ _ A F _ _ N θ
  have hex : ∀ t : SecF A F N, ∃ u : SecF A F N, IsActOf A.A A.L N θ t u :=
    fun t => GlobalTheory.VVCompare.exists_isActOf A.A A.isLB θ t
  choose Θ hΘ using hex
  have hb : (translT A.A θ.pt).left ≫ (fst (TFK (R := R) F) A.A).left = (fst (TFK (R := R) F) A.A).left :=
    congrArg (fun q => q.left) (lift_fst _ _ : translT A.A θ.pt ≫ fst _ _ = _)
  have hv := fun (t u : SecF A F N) (h : IsActOf A.A A.L N θ t u) y J hJ =>
    GlobalTheory.VVCompare.sv_of_isTwistPull A.A h (𝟙 _) y (J := J) hJ
  refine ⟨⟨⟨Θ, fun s s' => sec_ext' A.isLB fun y J hJ => ?_⟩,
    fun c s => sec_ext' A.isLB fun y J hJ => ?_⟩, fun t t' => ⟨fun h => sec_ext' A.isLB fun y J hJ => ?_, ?_⟩⟩
  · refine (hv _ _ (hΘ _) y J hJ).trans ?_
    refine Eq.symm ((sval_add' hJ _ _ _).trans (Eq.trans ?_ (congrArg _ (sval_add' hJ _ s s')).symm))
    exact (congrArg₂ (· + ·) (hv _ _ (hΘ s) y J hJ) (hv _ _ (hΘ s') y J hJ)).trans (mul_add _ _ _).symm
  · refine (hv _ _ (hΘ _) y J hJ).trans ?_
    refine Eq.symm ((sval_smul' hJ _ _ _).trans (Eq.trans ?_ (congrArg _ (sval_smul' hJ _ c s)).symm))
    rw [Category.assoc, hb]
    exact (congrArg _ (hv _ _ (hΘ s) y J hJ)).trans (mul_left_comm _ _ _)
  · exact (hv _ _ h y J hJ).trans (hv _ _ (hΘ t) y J hJ).symm
  · rintro rfl
    exact hΘ t

end GlobalTheory.Mum.Desc
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearMapThetaGroupActionSectionsStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Desc

theorem _root_.GlobalTheory.T.exists_linearMap_thetaGroup_action_sections : ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Sp (FractionRing R))) (F : Type) [Field F] [Algebra (FractionRing R) F] (N : ℕ) (θ : ThetaGrp A.A A.L (N : ℤ) (TFK (R := R) F)), ∃ b : SecF A F N →ₗ[F] SecF A F N, ∀ t t' : SecF A F N, IsActOf A.A A.L N θ t t' ↔ t' = b t := by
  first | exact @GlobalTheory.Mum.Desc.exists_linear_isActOf | exact GlobalTheory.Mum.Desc.exists_linear_isActOf | (intros; apply GlobalTheory.Mum.Desc.exists_linear_isActOf <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearMapTorsionPointSymmetricFrameOperato

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Desc

noncomputable section

namespace GlobalTheory.Mum.PhiLinear

theorem exists_linear_phi : ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (I : Ideal R), AdmBase R I → ∀ (D : DegData R I) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N : ℕ), Odd N → ∀ (p : QkPt D.toPre F N) (w : GlobalTheory.UT.Frm D.toPre F N p.g.b), GlobalTheory.UT.TXFrame N p w → ∃ a : Fam D.toPre F N →ₗ[F] Fam D.toPre F N, ∀ s s', PhiRel D.toPre F N p w s s' ↔ s' = a s := by
  intro R _ _ _ I _ D F _ _ _ N hN p w hw
  exact ReciprocityTheory.ChartRestriction.G.DVR.phiFun_of_globalFns GlobalTheory.globalFns_holds R I D F N hN.pos p w hw.1

end GlobalTheory.Mum.PhiLinear
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearMapTorsionPointSymmetricFrameOperatoStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Desc

theorem _root_.GlobalTheory.T.exists_linearMap_torsionPoint_symmetricFrame_operator : ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (I : Ideal R), AdmBase R I → ∀ (D : DegData R I) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N : ℕ), Odd N → ∀ (p : QkPt D.toPre F N) (w : GlobalTheory.UT.Frm D.toPre F N p.g.b), GlobalTheory.UT.TXFrame N p w → ∃ a : Fam D.toPre F N →ₗ[F] Fam D.toPre F N, ∀ s s', PhiRel D.toPre F N p w s s' ↔ s' = a s := by
  first | exact @GlobalTheory.Mum.PhiLinear.exists_linear_phi | exact GlobalTheory.Mum.PhiLinear.exists_linear_phi | (intros; apply GlobalTheory.Mum.PhiLinear.exists_linear_phi <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGroupSymmetricLiftActionFieldExtension

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Desc

namespace GlobalTheory.Mum.Desc

theorem isActOf_secExt : ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Sp (FractionRing R))) (F : Type) [Field F] [Algebra (FractionRing R) F] (em : Kb R →ₐ[FractionRing R] F) (N : ℕ), Odd N → ∀ (x : TFK (R := R) (Kb R) ⟶ A.A) (θ : ThetaGrp A.A A.L (N : ℤ) (TFK (R := R) (Kb R))) (θ' : ThetaGrp A.A A.L (N : ℤ) (TFK (R := R) F)), SymLift A.A A.L N N x θ → SymLift A.A A.L N N (baseEm em ≫ x) θ' → ∀ t t' : SecF A (Kb R) N, IsActOf A.A A.L N θ t t' → IsActOf A.A A.L N θ' (secExt A em N t) (secExt A em N t') := by
  intro R _ _ A F _ _ em N hN x θ θ' H H' t t' a
  exact GlobalTheory.WeightProbe.act_pull A hN (baseEm em) H H' a

end GlobalTheory.Mum.Desc
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGroupSymmetricLiftActionFieldExtensionStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Desc

theorem _root_.GlobalTheory.T.thetaGroup_symmetricLift_action_fieldExtension : ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Sp (FractionRing R))) (F : Type) [Field F] [Algebra (FractionRing R) F] (em : Kb R →ₐ[FractionRing R] F) (N : ℕ), Odd N → ∀ (x : TFK (R := R) (Kb R) ⟶ A.A) (θ : ThetaGrp A.A A.L (N : ℤ) (TFK (R := R) (Kb R))) (θ' : ThetaGrp A.A A.L (N : ℤ) (TFK (R := R) F)), SymLift A.A A.L N N x θ → SymLift A.A A.L N N (baseEm em ≫ x) θ' → ∀ t t' : SecF A (Kb R) N, IsActOf A.A A.L N θ t t' → IsActOf A.A A.L N θ' (secExt A em N t) (secExt A em N t') := by
  first | exact @GlobalTheory.Mum.Desc.isActOf_secExt | exact GlobalTheory.Mum.Desc.isActOf_secExt | (intros; apply GlobalTheory.Mum.Desc.isActOf_secExt <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqvDown

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.Desc

theorem lawsLL : GlobalTheory.UT.LL :=
  ⟨GlobalTheory.allSixLaws.1, GlobalTheory.allSixLaws.2.1, GlobalTheory.allSixLaws.2.2.1, GlobalTheory.allSixLaws.2.2.2.1, GlobalTheory.allSixLaws.2.2.2.2.1⟩

theorem eqv_down : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R))
    (A : PolAV (Sp (FractionRing R))) (N : ℕ), Odd N → ∀ (lab : QkPt D.toPre (Kb R) N → (TFK (R := R) (Kb R) ⟶ A.A))
    (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (em : Kb R →ₐ[FractionRing R] F) lab' E',
    LabExt em lab lab' → Eqv D.toPre A F N lab' E' → ∃ E, Eqv D.toPre A (Kb R) N lab E := by
  intro R _ _ _ hB D A N hN lab F _ _ _ em lab' E' hL hE
  obtain ⟨hAdm, hC⟩ := hB
  have hN1 : 1 ≤ N := hN.pos
  have honto := GlobalTheory.T.torsionLabels_surjective_of_larger_algClosed_field R D.toPre A N hN1 lab F em lab' hL hE.onto
  have hframe : ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra (FractionRing R) K] (p : QkPt D.toPre K N),
      ∃ w, GlobalTheory.UT.TXFrame N p w := fun K _ _ _ p =>
    (GlobalTheory.UT.SymFrame.main lawsLL R (maximalIdeal R) hAdm D K N hN p).1
  let J := {q : (p : QkPt D.toPre (Kb R) N) × GlobalTheory.UT.Frm D.toPre (Kb R) N p.g.b ×
      ThetaGrp A.A A.L (N : ℤ) (TFK (R := R) (Kb R)) // GlobalTheory.UT.TXFrame N q.1 q.2.1 ∧ SymLift A.A A.L N N (lab q.1) q.2.2}
  choose a ha using fun i : J => GlobalTheory.T.exists_linearMap_torsionPoint_symmetricFrame_operator R (maximalIdeal R) hAdm D (Kb R) N hN i.1.1 i.1.2.1 i.2.1
  choose b hb using fun i : J => GlobalTheory.T.exists_linearMap_thetaGroup_action_sections R A (Kb R) N i.1.2.2
  have hq := (GlobalTheory.T.levelPoints_algClosure_fractionRing_bijective R D.toPre F em N hN1).1
  choose p' hp' using fun i : J => (hq i.1.1).exists
  choose w' hw' using fun i : J => hframe F (p' i)
  have hlab : ∀ i : J, lab' (p' i) = baseEm em ≫ lab i.1.1 := fun i =>
    Over.OverMorphism.ext (by rw [hL _ _ (hp' i)]; rfl)
  choose θ' hθ' using fun i : J =>
    GlobalTheory.WeightProbe.exists_symLift_top A hN (lab' (p' i)) ((hE.onto _).2 ⟨_, rfl⟩)
  choose a' ha' using fun i : J => GlobalTheory.T.exists_linearMap_torsionPoint_symmetricFrame_operator R (maximalIdeal R) hAdm D F N hN (p' i) (w' i) (hw' i)
  choose b' hb' using fun i : J => GlobalTheory.T.exists_linearMap_thetaGroup_action_sections R A F N (θ' i)
  letI : Algebra (Kb R) F := em.toRingHom.toAlgebra
  haveI : IsScalarTower (FractionRing R) (Kb R) F := IsScalarTower.of_algebraMap_eq fun r => (em.commutes r).symm
  haveI : FiniteDimensional F (Fam D.toPre F N) :=
    (GlobalTheory.UU.finrank_fam_of_laws GlobalTheory.allSixLaws.1 GlobalTheory.allSixLaws.2.1 R D.toPre D.tau_bimult F N hN1).1
  have hfamExt : GlobalTheory.FieldBaseChange.IsExtension (famExt D.toPre em N) :=
    GlobalTheory.FieldBaseChange.isExtension_famPull D.toPre (Kb R) F _ hN1
  have hsecExt := GlobalTheory.T.lineBundlePowSections_algClosure_fieldBaseChange R A F em N
  have ca : ∀ i v, a' i (famExt D.toPre em N v) = famExt D.toPre em N (a i v) := fun i v =>
    ((ha' i _ _).1 (GlobalTheory.T.torsionPointOperator_symmetricFrame_fieldExtension R (maximalIdeal R) hAdm D F em N hN i.1.1 i.1.2.1 (p' i) (w' i) i.2.1 (hw' i) (hp' i) v _
      ((ha i v _).2 rfl))).symm
  have cb : ∀ i t, b' i (secExt A em N t) = secExt A em N (b i t) := fun i t =>
    ((hb' i _ _).1 (GlobalTheory.T.thetaGroup_symmetricLift_action_fieldExtension R A F em N hN (lab i.1.1) i.1.2.2 (θ' i) i.2.2 (by rw [← hlab i]; exact hθ' i) t _
      ((hb i t _).2 rfl))).symm
  let E'' : Fam D.toPre F N →ₗ[F] SecF A F N :=
    { toFun := E'
      map_add' := fun s t => GlobalTheory.FieldBaseChange.SecOver.ext _ _ fun j => hE.add s t (s + t) (fun _ _ => rfl) j
      map_smul' := fun c s => GlobalTheory.FieldBaseChange.SecOver.ext _ _ fun j =>
        hE.smul c s (c • s) ((ReciprocityTheory.ChartRestriction.G.DVR.isSmul_iff _ _ _).2 rfl) j }
  have cE : ∀ i v, E'' (a' i v) = b' i (E'' v) := fun i v =>
    (hb' i _ _).1 (hE.act (p' i) (w' i) (θ' i) v (a' i v) (hw' i) (hθ' i) ((ha' i v _).2 rfl))
  obtain ⟨E, hEb, hEc⟩ := GlobalTheory.T.exists_intertwining_bijective_of_fieldBaseChange (Kb R) F _ _ _ _ (famExt D.toPre em N) (secExt A em N) hfamExt hsecExt J a b a' b'
    ca cb E'' hE.bij cE
  refine ⟨fun s => E s, ⟨hEb, ?_, ?_, honto, hframe (Kb R),
    fun p => GlobalTheory.WeightProbe.exists_symLift_top A hN (lab p) ((honto _).2 ⟨p, rfl⟩), ?_⟩⟩
  · intro s s' s'' h j
    have : s'' = s + s' := ReciprocityTheory.ChartRestriction.G.DVR.fam_ext h
    subst this
    exact congrArg (fun q : SecF A (Kb R) N => LB.Sec.f q j) (map_add E s s')
  · intro c s s' h j
    rw [(ReciprocityTheory.ChartRestriction.G.DVR.isSmul_iff _ _ _).1 h]
    exact congrArg (fun q : SecF A (Kb R) N => LB.Sec.f q j) (map_smul E c s)
  · intro p w θ s s' hw hθ hP
    let i : J := ⟨⟨p, w, θ⟩, hw, hθ⟩
    have e1 : s' = a i s := (ha i s s').1 hP
    have e2 : E s' = b i (E s) := by rw [e1]; exact hEc i s
    exact (hb i (E s) (E s')).2 e2

end GlobalTheory.Mum.Desc
end
end
