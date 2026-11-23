module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodGeneric
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Formalism.LocalToGlobal.Divisibility.InertPartitionLePartF
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HcFiniteAndSchurMult
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CarriedPartEigensystemPassageOfTypeStatement
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConjugateSpaceJointEigenspacesPairCommISup
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
public import Formalism.LocalToGlobal.Columns.HeckeSp
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.LinearAlgebra.Eigenspace.Pi
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.TypeStar
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EigenPartLeTypePartOfPassageStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EveryLiftOperatorIsLabelOperatorWithPartnerStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSeparatingInertEigenvaluePassageStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GoodProjectorUnitaryFormsModelLaws
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharacterisationPlacesPartsOfWeakStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RealizationFamilyNormalOperatorsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalOperatorsFormsOnRankSpaceNormalStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaIntertwinesMatchedOperatorsStatement
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharacterisationPlacesPartsOfWeak
public import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Formalism.LocalToGlobal.IndefiniteReal.MemRangeAdjointOfKerStable
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConjugateSpaceJointEigenspacesPairCommISupStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.conjugateSpace_jointEigenspaces_pairComm_iSup : ∀ (s : Bool) {E I : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (h : I → Module.End ℂ E), (Formalism.L2.Col.PairComm h → Formalism.L2.Col.PairComm (fun i => (Tw.map s (h i) : Module.End ℂ (Tw s E)))) ∧ (∀ Q : (I → ℂ) → Prop, Formalism.L2.Col.eigSum (fun i => (Tw.map s (h i) : Module.End ℂ (Tw s E))) Q = Tw.sub s (Formalism.L2.Col.eigSum h fun x => Q fun i => cj s (x i))) ∧ ∀ {C : Type} (Ec : C → Submodule ℂ E), Tw.sub s (⨆ c, Ec c) = ⨆ c, Tw.sub s (Ec c) := by
  first | exact @GlobalTheory.TwEig.pairComm_eigSum_sub_iSup | exact GlobalTheory.TwEig.pairComm_eigSum_sub_iSup | (intros; apply GlobalTheory.TwEig.pairComm_eigSum_sub_iSup <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemIInfOfApply

section

@[expose] public section

namespace GlobalTheory.IndependentInfimum

open Module

theorem le_of_indep {K V X : Type*} [Field K] [AddCommGroup V] [Module K V]
    (U W : X → Submodule K V) (hW : iSupIndep W) (hUW : ∀ x, U x ≤ W x)
    (hU : ⨆ x, U x = ⊤) (x : X) : W x ≤ U x := by
  classical
  intro w hw
  have htop : w ∈ ⨆ y, U y := by rw [hU]; exact Submodule.mem_top
  have hsplit : (⨆ y, U y) = U x ⊔ ⨆ (y) (_ : y ≠ x), U y := by
    apply le_antisymm
    · refine iSup_le fun y => ?_
      by_cases hy : y = x
      · subst hy
        exact le_sup_left
      · exact le_sup_of_le_right (le_iSup₂_of_le y hy le_rfl)
    · exact sup_le (le_iSup U x) (iSup₂_le fun y _ => le_iSup U y)
  rw [hsplit] at htop
  obtain ⟨u, hu, w', hw', hsum⟩ := Submodule.mem_sup.1 htop
  have hw'W : w' ∈ ⨆ (y) (_ : y ≠ x), W y :=
    (iSup₂_mono fun y _ => hUW y) hw'
  have hdiff : w - u ∈ W x := W x |>.sub_mem hw (hUW x hu)
  have heq : w - u = w' := by rw [← hsum]; abel
  have hdis := (hW x).le_bot (Submodule.mem_inf.2 ⟨hdiff, heq ▸ hw'W⟩)
  rw [Submodule.mem_bot, sub_eq_zero] at hdis
  rw [hdis]
  exact hu

theorem mem_iInf_of_apply {K V I : Type*} [Field K] [AddCommGroup V] [Module K V]
    (A : I → Module.End K V) (x : I → K) (v : V) (hv : ∀ i, A i v = x i • v) :
    v ∈ ⨅ i, (A i).maxGenEigenspace (x i) := Submodule.mem_iInf _ |>.2 fun i =>
  Module.End.eigenspace_le_maxGenEigenspace (Module.End.mem_eigenspace_iff.2 (hv i))

theorem main {E I C : Type} [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]
    (h : I → Module.End ℂ E) (e : Module.End ℂ E) (Ec : C → Submodule ℂ E) (lab : C → I → ℂ)
    (he : e * e = e) (hE : ⨆ (c : C), Ec c = LinearMap.range e)
    (hl : ∀ (c : C), ∀ w ∈ Ec c, ∀ (i : I), (h i : E → E) w = lab c i • w) :
    (Formalism.L2.Col.PairComm fun (i : I) ↦ h i * e) ∧ ∀ (Q : (I → ℂ) → Prop), ¬Q (0 : I → ℂ) →
      Formalism.L2.Col.eigSum (fun (i : I) ↦ h i * e) Q = ⨆ (c : C), ⨆ (_ : Q (lab c)), Ec c := by
  classical
  have hee : ∀ v, e (e v) = e v := fun v => by
    have := congrArg (fun f : Module.End ℂ E => f v) he
    simpa using this
  have hfix : ∀ c, ∀ w ∈ Ec c, e w = w := by
    intro c w hw
    have : w ∈ LinearMap.range e := hE ▸ Submodule.mem_iSup_of_mem c hw
    obtain ⟨u, rfl⟩ := this
    exact hee u
  have hA : ∀ c, ∀ w ∈ Ec c, ∀ i, (h i * e) w = lab c i • w := by
    intro c w hw i
    rw [Module.End.mul_apply, hfix c w hw, hl c w hw]
  have hcomm : ∀ i j, Commute (h i * e) (h j * e) := by
    intro i j
    have key : ∀ w ∈ ⨆ c, Ec c, (h i * e) ((h j * e) w) = (h j * e) ((h i * e) w) := by
      intro w hw
      induction hw using Submodule.iSup_induction' with
      | mem c w hw =>
        rw [hA c w hw j, hA c w hw i, map_smul, map_smul, hA c w hw j, hA c w hw i, smul_comm]
      | zero => simp
      | add a b _ _ ha hb => simp only [map_add (f := _), ha, hb]
    ext v
    have hv : e v ∈ ⨆ c, Ec c := by rw [hE]; exact ⟨v, rfl⟩
    have := key _ hv
    simpa [Module.End.mul_apply, hee] using this
  refine ⟨hcomm, fun Q hQ => ?_⟩
  have hind : iSupIndep fun x : I → ℂ => ⨅ i, (h i * e).maxGenEigenspace (x i) :=
    Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo (fun i => h i * e)
      fun i j φ => Module.End.mapsTo_maxGenEigenspace_of_comm (hcomm j i) φ
  let U : (I → ℂ) → Submodule ℂ E := fun x =>
    (⨆ (c : C) (_ : lab c = x), Ec c) ⊔ ⨆ (_ : x = 0), LinearMap.ker e
  have hUW : ∀ x, U x ≤ ⨅ i, (h i * e).maxGenEigenspace (x i) := by
    intro x
    refine sup_le (iSup₂_le fun c hc w hw => ?_) (iSup_le fun hx w hw => ?_)
    · exact mem_iInf_of_apply (fun i => h i * e) x w fun i => hc ▸ hA c w hw i
    · refine mem_iInf_of_apply (fun i => h i * e) x w fun i => ?_
      rw [LinearMap.mem_ker] at hw
      simp [hx, Module.End.mul_apply, hw]
  have hU : ⨆ x, U x = ⊤ := by
    rw [eq_top_iff]
    intro v _
    have h1 : LinearMap.range e ≤ ⨆ x, U x := by
      rw [← hE]
      exact iSup_le fun c => le_iSup_of_le (lab c)
        (le_sup_of_le_left (le_iSup₂_of_le (f := fun c' (_ : lab c' = lab c) => Ec c') c rfl le_rfl))
    have h2 : LinearMap.ker e ≤ ⨆ x, U x :=
      le_iSup_of_le 0 (le_sup_of_le_right
        (le_iSup_of_le (f := fun _ : (0 : I → ℂ) = 0 => LinearMap.ker e) rfl le_rfl))
    have h3 : v - e v ∈ LinearMap.ker e := by simp [LinearMap.mem_ker, hee]
    have := Submodule.add_mem _ (h1 ⟨v, rfl⟩) (h2 h3)
    simpa using this
  unfold Formalism.L2.Col.eigSum Formalism.L2.Col.eigAt
  apply le_antisymm
  · refine iSup₂_le fun x hx => (le_of_indep U _ hind hUW hU x).trans ?_
    refine sup_le (iSup₂_le fun c hc => ?_) (iSup_le fun h0 => absurd (h0 ▸ hx) hQ)
    exact le_iSup₂_of_le (f := fun c (_ : Q (lab c)) => Ec c) c (hc ▸ hx) le_rfl
  · refine iSup₂_le fun c hc => ?_
    refine le_iSup₂_of_le
      (f := fun (x : I → ℂ) (_ : Q x) => ⨅ i, (h i * e).maxGenEigenspace (x i)) (lab c) hc ?_
    intro w hw
    exact mem_iInf_of_apply (fun i => h i * e) (lab c) w (hA c w hw)

end GlobalTheory.IndependentInfimum
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.EigSumMulProjEq

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Hk3


open Formalism.L2.Col in
theorem eigSum_mul_proj_eq {E I C : Type} [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]
    (h : I → Module.End ℂ E) (e : Module.End ℂ E) (Ec : C → Submodule ℂ E) (lab : C → I → ℂ)
    (he : e * e = e) (hr : (⨆ c, Ec c) = LinearMap.range e)
    (hh : ∀ c, ∀ w ∈ Ec c, ∀ i, h i w = lab c i • w) :
    PairComm (fun i => h i * e) ∧ ∀ Q : (I → ℂ) → Prop, ¬ Q 0 →
      eigSum (fun i => h i * e) Q = ⨆ (c : C) (_ : Q (lab c)), Ec c := by
  first
  | exact @_root_.GlobalTheory.IndependentInfimum.main
  | exact _root_.GlobalTheory.IndependentInfimum.main
  | (apply _root_.GlobalTheory.IndependentInfimum.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.IndependentInfimum.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IndependentInfimum.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IndependentInfimum.main ..)

end GlobalTheory.Hk3
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ZeroEigensystemNotPassageOfFiniteType

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ZeroPassage

theorem dualPoly_coeff_zero {K : Type} [Field K] (s : K) (p : K[X]) (hp : p ≠ 0) : (dualPoly s p).coeff 0 = 1 := by
  unfold dualPoly
  rw [coeff_C_mul, coeff_zero_eq_eval_zero, eval_comp]
  simp [← coeff_zero_eq_eval_zero, hp]

theorem heckePoly_zero {L Pl : Type} [Field L] (n : ℕ) (q : Pl → ℕ) (P : Pl) :
    Formalism.L2.Col.heckePoly n q (fun _ => (0 : L)) P = 0 := by
  simp [Formalism.L2.Col.heckePoly, Formalism.L2.Col.heckePolyOf]

theorem mem_resSet_of_mem_ixFin3 {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G]
    {Pl0 I0 Ty : Type} {B : BlockDat K G Pl0} (D : InertDat3 B I0 Ty) {X : Finset (G → K)}
    {p : Typ3 K Pl0 I0 Ty} (hp : p ∈ D.ixFin3 X) : p.1 ∈ B.resSet X := by
  unfold InertDat3.ixFin3 at hp
  split_ifs at hp with hfin
  · rw [Set.Finite.mem_toFinset] at hp
    refine ⟨hp.1, fun hb => hp.2.2 ?_⟩
    have hle : D.inertTypeEigenspaceSum p ≤ B.partF p.1 := by
      refine iSup₂_le fun x hx => ?_
      refine le_trans ?_ (Formalism.L2.Col.eigAt_le_eigSum (op := B.op) (C := B.HasRes p.1) (x := fun i => x (Sum.inl i)) hx.1)
      exact le_iInf fun i => iInf_le (fun k => (D.opAll k).maxGenEigenspace (x k)) (Sum.inl i)
    rw [eq_bot_iff] at hb ⊢
    exact le_trans (Submodule.comap_mono (Submodule.map_mono hle)) hb
  · simp at hp

theorem zero_not_passage : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), R.WeakCharacterisation F → ∀ j (p : A3.fam3.base3.Ix), ¬ cxSys D.what₂.embLL ((A3.liftI j A3.A.μ0).HasRes3 (A3.fam3.tr3 j p.1)) 0 := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F h j p
  rintro ⟨x, hx, hx0⟩
  obtain ⟨P, hP⟩ := (GlobalTheory.CoreThree.heckeCharacterisation_places_parts_of_weak R F h).2.2.2.2.2.2
  have hxz : (fun i => x (Sum.inl i)) = fun _ => (0 : D.what₂.LL) := by
    funext i
    have h1 := congrFun hx0 (Sum.inl i)
    exact (map_eq_zero_iff _ D.what₂.embLL.injective).1 h1.symm
  let P' : (A3.A.fam.L j A3.A.μ0).Pl := ⟨P, hP⟩
  have hres := hx.1 P'
  rw [hxz] at hres
  replace hres := (heckePoly_zero (L := D.what₂.LL) (Pl := (A3.A.fam.L j A3.A.μ0).Pl) _ _ _).symm.trans hres
  have hmem : p.1.1 ∈ (A3.A.fam.R A3.A.μ0).resSet A3.A.X := mem_resSet_of_mem_ixFin3 (A3.rowI A3.A.μ0) p.2
  have hc : (p.1.1 P).coeff 0 = 1 :=
    (A3.A.fam.R A3.A.μ0).lf_coeff_zero_of_mem_resSet (fun Q => (h.base.fam.degR A3.A.μ0 Q).1) hmem P
  have hne : p.1.1 P ≠ 0 := fun h0 => by rw [h0, coeff_zero] at hc; exact zero_ne_one hc
  have hb : ((A3.A.fam.L j A3.A.μ0).blockProd P').coeff 0 = 1 := by
    rw [coeff_zero_eq_eval_zero]; exact (A3.A.fam.L j A3.A.μ0).lf_blockProd_eval_zero P'
  have ht : ((A3.fam3.tr3 j p.1).1 ((A3.A.fam.L j A3.A.μ0).pl P')).coeff 0 = 1 := dualPoly_coeff_zero _ _ hne
  have h2 := congrArg (fun f => _root_.AddMonoidAlgebra.coeff (M := ℕ) f 0) hres
  simp only [coeff_zero, mul_coeff_zero, hb, ht, mul_one] at h2
  exact zero_ne_one h2

end GlobalTheory.ZeroPassage
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ZeroEigensystemNotPassageOfFiniteTypeStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.zero_eigensystem_not_passage_of_finiteType : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), R.WeakCharacterisation F → ∀ j (p : A3.fam3.base3.Ix), ¬ cxSys D.what₂.embLL ((A3.liftI j A3.A.μ0).HasRes3 (A3.fam3.tr3 j p.1)) 0 := by
  first | exact @GlobalTheory.ZeroPassage.zero_not_passage | exact GlobalTheory.ZeroPassage.zero_not_passage | (intros; apply GlobalTheory.ZeroPassage.zero_not_passage <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeThetaLevel3Exists

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Hk3

theorem tw_cut_eig (s : Bool) {E I C : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (h : I → Module.End ℂ E) (e : Module.End ℂ E) (Ec : C → Submodule ℂ E) (lab : C → I → ℂ)
    (he : e * e = e) (hs : (⨆ c, Ec c) = LinearMap.range e) (hl : ∀ c, ∀ w ∈ Ec c, ∀ i, h i w = lab c i • w) :
    Formalism.L2.Col.PairComm (fun i => (Tw.map s (h i * e) : Module.End ℂ (Tw s E))) ∧
      ∀ Q : (I → ℂ) → Prop, ¬ Q 0 →
        Formalism.L2.Col.eigSum (fun i => (Tw.map s (h i * e) : Module.End ℂ (Tw s E))) Q =
          Tw.sub s (⨆ (c : C) (_ : Q (fun i => cj s (lab c i))), Ec c) := by
  obtain ⟨hc, hq⟩ := GlobalTheory.Hk3.eigSum_mul_proj_eq h e Ec lab he hs hl
  obtain ⟨a, b, -⟩ := GlobalTheory.T.conjugateSpace_jointEigenspaces_pairComm_iSup s (fun i => h i * e)
  refine ⟨a hc, fun Q hQ => ?_⟩
  have h0 : (fun i => cj s ((0 : I → ℂ) i)) = 0 := by funext i; simp
  rw [b Q, hq _ (by rw [h0]; exact hQ)]

theorem cxSys_cj_iff {K I : Type} [Field K] {σ τ : K →+* ℂ} {s : Bool} (h : ∀ a, σ a = cj s (τ a)) (H : (I → K) → Prop) (y : I → ℂ) :
    cxSys σ H (fun i => cj s (y i)) ↔ cxSys τ H y := by
  constructor
  · rintro ⟨x, hx, e⟩
    refine ⟨x, hx, funext fun i => ?_⟩
    have := congrFun e i
    simp only [h] at this
    simpa [cj_cj] using congrArg (cj s) this
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, funext fun i => (h _).symm⟩


theorem heckeTheta_level3_exists_alt : HoweUnram → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), GlobalTheory.Chain.LiftInteg D → R.WeakCharacterisation F → R.toRealDat.ExAt → InertJunk A3 → ∀ s, A3.fam3.Ok3 s → GoodGeneric A3.A.X F.P0 F.ψ0⁻¹ → R.toRealDat.LUnif → R.PGUnit F → R.PGEquiv F → R.PLevW F → R.PThmA → (0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) → R.PThmB → (R.toCx3 F).PartsW false → A3.fam3.TypesSep3 → ((∃ tr, R.TrISem F tr ∧ TrISepWith A3 tr) → R.TrISem F A3.trI ∧ A3.fam3.TrISep) → ∃ hW, HeckeIntertwiningLifts A3 (R.toCx3 F) hW := by
  intro hHowe hHC hCusp D G _ _ Pl0 I0 T A3 Ks _ _ _ R F hLI hC hEx hJ s hOk hGG hLU hGU hGE hLW hA hPos hB hParts hTS hPin
  have hirr : ∀ χ ∈ A3.A.X, IsAbsIrrChar χ := hOk.ok2.irr
  obtain ⟨hCoreE, hSF, -, -, -, hWc, -⟩ := GlobalTheory.T.heckeCharacterisation_places_of_weakCharacterisation R F hC
  have hCore := hCoreE hEx
  have hSch : SchurAll R.toRealDat :=
    ⟨fun _ _ _ => (GlobalTheory.MultFinite.hcFinite_and_schurMult hHC hCusp D _ _ _ _ _ _ _ _).2,
      (GlobalTheory.MultFinite.hcFinite_and_schurMult hHC hCusp D _ _ _ _ _ _ _ _).2,
      fun _ => (GlobalTheory.MultFinite.hcFinite_and_schurMult hHC hCusp D _ _ _ _ _ _ _ _).2⟩
  have hTr := (hPin (GlobalTheory.T.exists_separating_inert_eigenvalue_passage hHowe R F hLI hC hEx hSch hJ hirr hB hPos)).1
  have hOps := fun i => GlobalTheory.T.sphericalOperators_forms_on_rank_space_normal R.toRealDat F.lv2 hCore hSch hirr R.SF hSF i
  choose h hIsW hNorm hGc hSup hInv hEig hChar using hOps
  have hDict := GlobalTheory.T.every_liftOperator_is_labelOperator_with_partner hHowe R F hLI hC hEx hSch hJ
  choose pl cV cW hD using hDict
  have hLaws := GlobalTheory.Hk3.eH_laws R.toRealDat F.lv2 hCore hirr
  have hcut := fun j => tw_cut_eig (twAt D.what₂.embLL A3.A.v0) (fun i => h j (pl j A3.A.μ0 i) (cW j A3.A.μ0 i)) (eH R.toRealDat j)
    (Wcc R.toRealDat R.SF j) (fun c => labW j (pl j A3.A.μ0) (cW j A3.A.μ0) c) (hLaws j).1 (hSup j)
    (fun c w hw i => hEig j c _ ((hD j A3.A.μ0).good i) _ w hw)
  refine ⟨fun j t i => Tw.map (E := (R.HW j (sg0 D A3.A)).H) (F := (R.HW j (sg0 D A3.A)).H) (twAt D.what₂.embLL A3.A.v0) (h j (pl j t i) (cW j t i) * eH R.toRealDat j), ?_, ?_, ?_⟩
  · intro j t i u
    obtain ⟨hV, hVo, -⟩ := (GlobalTheory.T.realization_family_normal_operators R.toRealDat F.lv2 hCore.lev hCore.fam hCore.models).2 j t
    have hK := RealDat3.kFormL_of (R := R) (F := F) hCore.models
    have hop : (R.toCx3 F).opLC j t (Sum.inl i) = Tw.map (E := (R.HV j t).H) (F := (R.HV j t).H) (twAt D.what₂.embLL A3.A.v0) (hV (pl j t i) (cV j t i)) := by
      refine LinearMap.ext_on_range (hK j t).2 fun k => ?_
      rw [← CxData.jL_opL _ hK]
      show Tw.mk (twAt D.what₂.embLL A3.A.v0) (R.jV j t ((A3.liftI j t).opAll i _)) = Tw.mk (twAt D.what₂.embLL A3.A.v0) (hV _ _ (R.jV j t _))
      exact congrArg (Tw.mk (twAt D.what₂.embLL A3.A.v0)) ((hD j t).op hV hVo i _)
    have hs := (GlobalTheory.T.theta_intertwines_matched_operators R.toRealDat F.lv2 hCore hSch hirr R.SF hSF j t (pl j t i) ((hD j t).good i) _ _ ((hD j t).mat i) hV hVo).1 (h j) (hIsW j)
    rw [hop]
    show R.phs j • Tw.mk (twAt D.what₂.embLL A3.A.v0) (R.thG j t (hV _ _ (Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := (R.HV j t).H) u))) =
      Tw.map (E := (R.HW j (sg0 D A3.A)).H) (F := (R.HW j (sg0 D A3.A)).H) (twAt D.what₂.embLL A3.A.v0) (h j (pl j t i) (cW j t i) * eH R.toRealDat j)
        (R.phs j • Tw.mk (twAt D.what₂.embLL A3.A.v0) (R.thG j t (Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := (R.HV j t).H) u)))
    rw [map_smul]
    congr 1
    show Tw.mk (twAt D.what₂.embLL A3.A.v0) (R.thG j t (hV _ _ (Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := (R.HV j t).H) u))) = Tw.mk (twAt D.what₂.embLL A3.A.v0) (h j (pl j t i) (cW j t i) (eH R.toRealDat j (R.thG j t (Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := (R.HV j t).H) u))))
    rw [(hLaws j).2.2.2 t, hs]
  · intro j
    exact (hcut j).1
  · intro j p
    have hv := fun a => R.toRealDat.emb0 a
    have hQ0 : ¬ cxSys A3.fam3.base3.v0.embedding ((A3.liftI j A3.A.fam.μ0).HasRes3 (A3.fam3.tr3 j p.1)) 0 := by
      intro h0
      have h1 : (0 : (A3.liftI j A3.A.fam.μ0).OpIx → ℂ) = fun i => cj (twAt D.what₂.embLL A3.A.v0) ((0 : (A3.liftI j A3.A.fam.μ0).OpIx → ℂ) i) := by
        funext i; simp
      rw [h1] at h0
      exact GlobalTheory.T.zero_eigensystem_not_passage_of_finiteType R F hC j p ((cxSys_cj_iff hv _ _).1 h0)
    have key := (hcut j).2 _ hQ0
    show Tw.sub _ (R.Wp3 j p) = _
    refine Eq.trans ?_ key.symm
    congr 1
    apply le_antisymm
    · refine iSup₂_le fun c hc => ?_
      by_cases hne : R.Wc' j c = ⊥
      · rw [hne]; exact bot_le
      · exact le_iSup₂_of_le c ((cxSys_cj_iff hv _ _).2
          (GlobalTheory.T.carriedPart_eigensystem_passage_of_type hHowe R F hLI hC hEx hSch hJ s hOk hGG hLU hGU hGE hLW hA hPos hB hTr j _ _ _ (hD j A3.A.μ0) p c hc hne)) (hWc j c).le
    · refine iSup₂_le fun c hc => ?_
      rw [← hWc j c]
      exact GlobalTheory.T.eigenPart_le_typePart_of_passage hHowe R F hLI hC hEx hSch hJ s hOk hGG hLU hGU hGE hLW hA hPos hB hTr hParts hTS j _ _ _ (hD j A3.A.μ0) p c
        ((cxSys_cj_iff hv _ _).1 hc)

end GlobalTheory.Hk3

end
end
end
