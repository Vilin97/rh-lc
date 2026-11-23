module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.HodgeTraceFromLefschetzAndGroupSide
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.SigmaSplit
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsProjOverSPow
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SPowSmooth
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.HeckeTraceSemiHolds
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.LevelIsPullback
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PAltLin
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PCntFn
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PCntSum
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PCoeffOcc
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PFnDecomp
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PGeoStep
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PHExpInj
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PHodgeEig
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PHodgeTr
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PHomEx
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PHopWord
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.SigmaSplit
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.InvMemLatMonoidOfMemAwaySupp
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.InvPol
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PKSHodge
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.HeckeTraceSemi
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PLegBc
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PMapEq
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.POccOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PPolPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibrePowerMapOfTotalSpacesIsPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteEtaleSurjectiveProj
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PSigmaSplit
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PTatePull
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PTransPull
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PUnifBound
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PtsOfSplits
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PullCongr

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PHodgeFin

section

@[expose] public section

open UpperTheory.Gal.LocalSmoothExtension

open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh

theorem UpperTheory.Gal.LocalSmoothExtension.hodgeFin_of :
    HolomorphicLefschetzFormula → HodgeFin := by
  intro hW Z s d hsm hproj a b
  haveI := hsm
  have hF : ∀ y : CxPts (Scheme.emptyTo Z ≫ s) (RingHom.id ℂ),
      y ∈ (∅ : Finset (CxPts (Scheme.emptyTo Z ≫ s) (RingHom.id ℂ))) ↔
        y.1 ≫ Scheme.emptyTo Z = y.1 ≫ Scheme.emptyTo Z :=
    fun y => (isEmptyElim (y.1.base (Classical.arbitrary _)) : False).elim
  have key := hW Z s d hproj ∅ (Scheme.emptyTo Z ≫ s) (Scheme.emptyTo Z) (Scheme.emptyTo Z) rfl rfl
    inferInstance inferInstance ∅ hF (fun _ => 0) (fun y hy => by simp at hy) a
  exact key.1 b
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PKNNormal

section

section

open UpperTheory.Gal.LocalSmoothExtension

theorem UpperTheory.Gal.LocalSmoothExtension.kNNormal_of :
    KNNormal := by
  intro p _ D G L M
  have key : ∀ k ∈ L.KN 1, ∀ u, L.CongOne M u → L.CongOne M (k * u * k⁻¹) := by
    intro k hk u hu v hv
    obtain ⟨w, hw, e⟩ := hu _ (UpperTheory.Gal.Int.Geo.integ_of_mem (inv_mem hk) v hv)
    refine ⟨L.actG k w, UpperTheory.Gal.Int.Geo.integ_of_mem hk w hw, ?_⟩
    have h1 : L.actG k (L.actG k⁻¹ v) = v := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, e, map_add (f := _), map_nsmul, h1]
  refine ⟨fun k hk u hu => ⟨key k hk u hu.1, ?_⟩, fun hM => GlobalTheory.W2.relIndex_KN_ne_zero L one_pos hM⟩
  have e : (k * u * k⁻¹)⁻¹ = k * u⁻¹ * k⁻¹ := by group
  rw [e]
  exact key k hk _ hu.2
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PKSProj

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open UpperTheory.Gal.LocalSmoothExtension
open UpperTheory.Gal.Int.Geo (KS Lv Sc)

theorem UpperTheory.Gal.LocalSmoothExtension.kSProj_of :
    ZSm → ZPr → KSProj := by
  intro hSm hPr p _ D G L hSc gb k T N
  have hq : qAt T N = (T.e N).hom ≫ ((KS.pow (T.M N).univ.A k).hom ≫ (T.M N).s) := (T.e_q N).symm
  rw [hq]
  constructor
  · obtain ⟨M, i, hi, hi'⟩ := hPr p D hSc.cpt gb N.1 N.2.1 N.2.2 (T.M N) k
    refine ⟨M, (T.e N).hom ≫ i, ?_, ?_⟩
    · haveI := hi
      infer_instance
    · rw [Category.assoc, hi']
  · obtain ⟨d, hd⟩ := hSm D.toG gb N.1 N.2.1 (T.M N) k
    haveI := hd
    have h0 : SmoothOfRelativeDimension 0 (T.e N).hom := inferInstance
    have h2 := AlgebraicGeometry.smoothOfRelativeDimension_comp (n := 0) (m := d) (T.e N).hom
      ((KS.pow (T.M N).univ.A k).hom ≫ (T.M N).s)
    rw [zero_add] at h2
    exact ⟨d, h2⟩
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PLefSum

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open Matrix Polynomial
open UpperTheory.Gal.W2 (lefTerm)

namespace UpperTheory.Gal.LocalSmoothExtension

theorem lefSum_of : LefSum := by
  intro d A y
  set p : ℂ[X] := (1 + (X : ℂ[X]) • A.map (C : ℂ →+* ℂ[X])).det with hp
  have hdeg : p.natDegree < d + 1 := by
    have h1 : (1 + (X : ℂ[X]) • A.map (C : ℂ →+* ℂ[X]) : Matrix (Fin d) (Fin d) ℂ[X]) =
        (X : ℂ[X]) • A.map C + (1 : Matrix (Fin d) (Fin d) ℂ).map C := by
      rw [Matrix.map_one C (map_zero _) (map_one _), add_comm]
    have hle := natDegree_det_X_add_C_le A 1
    rw [← h1, Fintype.card_fin] at hle
    exact Nat.lt_succ_of_le hle
  have hev : p.eval (-y) = (1 - y • A).det := by
    rw [hp, ← coe_evalRingHom, RingHom.map_det]
    congr 1
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply,
      Matrix.sub_apply, Matrix.one_apply, coe_evalRingHom, smul_eq_mul]
    split_ifs <;> simp <;> ring
  unfold lefTerm
  rw [← hev, eval_eq_sum_range' hdeg, Finset.sum_div]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

end UpperTheory.Gal.LocalSmoothExtension
end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PModelBc

section

section

open UpperTheory.Gal.LocalSmoothExtension
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.Gen.BaseChange

theorem UpperTheory.Gal.LocalSmoothExtension.modelBc_of :
    MapEq → ModelBc := by
  intro hM G R₁ R₂ _ _ _ _ τ gb₁ gb₂ hρ ht N M
  obtain ⟨o', ⟨mo⟩⟩ := exists_gObjMap_pull (pullback.fst M.s (spMap τ)) M.univ
  let U : GObj gb₂ N (pullback.snd M.s (spMap τ)) := up hρ ht pullback.condition.symm o'
  have hrep : ∀ (S : Scheme.{0}) (s' : S ⟶ Sp R₂) (o : GObj gb₂ N s'),
      ∃! j : S ⟶ pullback M.s (spMap τ), j ≫ pullback.snd M.s (spMap τ) = s' ∧ Nonempty (GObjMap o U j) := by
    intro S s' o
    let u : GObj gb₁ N (s' ≫ spMap τ) := down hρ ht rfl o
    obtain ⟨a, ⟨ha, ⟨ma⟩⟩, hun⟩ := M.rep S _ u
    let j : S ⟶ pullback M.s (spMap τ) := pullback.lift a s' ha
    have j₁ : j ≫ pullback.fst M.s (spMap τ) = a := pullback.lift_fst _ _ _
    have j₂ : j ≫ pullback.snd M.s (spMap τ) = s' := pullback.lift_snd _ _ _
    obtain ⟨mj, -⟩ := (hM G R₁ gb₁ N S _ _ _ _ _ u o' M.univ j (pullback.fst M.s (spMap τ)) mo).2 (j₁.symm ▸ ma)
    have mj' : GObjMap o U j := ⟨mj.φ, mj.φ₂, mj.cart, mj.sq, mj.act, mj.pol, mj.eta⟩
    refine ⟨j, ⟨j₂, ⟨mj'⟩⟩, ?_⟩
    rintro j' ⟨h₂, ⟨m'⟩⟩
    have m'' : GObjMap u o' j' := ⟨m'.φ, m'.φ₂, m'.cart, m'.sq, m'.act, m'.pol, m'.eta⟩
    obtain ⟨n, -⟩ := (hM G R₁ gb₁ N S _ _ _ _ _ u o' M.univ j' (pullback.fst M.s (spMap τ)) mo).1 m''
    have e : j' ≫ pullback.fst M.s (spMap τ) = a :=
      hun _ ⟨by rw [Category.assoc, pullback.condition, ← Category.assoc, h₂], ⟨n⟩⟩
    apply pullback.hom_ext
    · rw [e, j₁]
    · rw [h₂, j₂]
  refine ⟨⟨pullback M.s (spMap τ), pullback.snd M.s (spMap τ), U, hrep⟩, pullback.fst M.s (spMap τ),
    IsPullback.of_hasPullback M.s (spMap τ), ⟨⟨mo.φ, mo.φ₂, mo.cart, mo.sq, mo.act, mo.pol, mo.eta⟩⟩⟩
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PPowComp

section

section

open UpperTheory.Gal.LocalSmoothExtension
open CategoryTheory

theorem UpperTheory.Gal.LocalSmoothExtension.powComp_of :
    PowComp := by
  intro S₁ S₂ S₃ A₁ A₂ A₃ f g e φ χ ω h₁ h₂ h₃ hfg hφχ k
  subst hfg
  subst hφχ
  apply GlobalTheory.KS.PowPB.pow_left_hom_ext
  · rw [Category.assoc, GlobalTheory.KS.PowPB.powMap_w, ← Category.assoc, GlobalTheory.KS.PowPB.powMap_w,
      GlobalTheory.KS.PowPB.powMap_w, Category.assoc]
  · intro i
    rw [Category.assoc, GlobalTheory.KS.PowPB.powMap_pr, ← Category.assoc, GlobalTheory.KS.PowPB.powMap_pr,
      GlobalTheory.KS.PowPB.powMap_pr, Category.assoc]
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PSigmaFEt

section

section

open AlgebraicGeometry CategoryTheory Limits
open UpperTheory.Gal.LocalSmoothExtension

theorem UpperTheory.Gal.LocalSmoothExtension.sigmaFEt_of :
    SigmaFEt := by
  intro Y Z s _ _ I _
  obtain ⟨k, ⟨e⟩⟩ := Finite.exists_equiv_fin I
  have hfold := GlobalTheory.Et.TrivTors.isFinite_sigmaDesc_fin Y k
  let i : (∐ fun _ : I => Y) ≅ ∐ fun _ : Fin k => Y :=
    Sigma.whiskerEquiv (f := fun _ : I => Y) (g := fun _ : Fin k => Y) e fun _ => Iso.refl Y
  have hd : (Sigma.desc fun _ : I => s) = i.hom ≫ (Sigma.desc fun _ : Fin k => 𝟙 Y) ≫ s := by
    apply Sigma.hom_ext
    intro a
    simp [i]
  refine ⟨by rw [hd]; infer_instance, ?_⟩
  have := HasRingHomProperty.instIsZariskiLocalAtSource (P := @Etale)
  exact IsZariskiLocalAtSource.sigmaDesc (P := @Etale) fun _ => inferInstance
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.HodgeTraceOfLefschetzAndGroupSide

section

@[expose] public section

namespace UpperTheory.Gal.LocalSmoothExtension

theorem HopWord_holds : HopWord := hopWord_of Tw.fnRing Tw.hopLin Tw.hopMul
theorem TransPull_holds : TransPull := transPull_of homEx_of polPull_of tatePull_of
theorem KSBc_holds : KSBc := kSBc_of (modelBc_of mapEq_of) (legBc_of mapEq_of TransPull_holds) powComp_of
theorem MemOp_holds : MemOp :=
  memOp2_of kNNormal_of cntFn_of cntSum_of sigmaFEt_of (sigmaSplit_of sigmaFEt_of Tw.splitsPts Tw.ptsOfSplits)
    Tw.twGal Tw.hopEx
theorem OccOf_holds : OccOf :=
  occOf_of MemOp_holds Tw.hodgeGood Tw.hodgeTr Tw.bcGood Tw.opBc Tw.opTr Tw.bcSplits
theorem KSProj_holds : KSProj := kSProj_of GlobalTheory.WeightTwoHeckePower.sPow_smooth GlobalTheory.WeightTwoHeckePower.isProjOver_sPow

theorem hodgeTrace_of_lefschetz_and_groupSide : HodgeTraceFromLefschetzAndGroupSide := fun hW hP hF h₁ h₂ =>
  have hT : UpperTheory.Gal.LocalSmoothExtension.HodgeTr :=
    hodgeTr_of (GroupTop_of h₁ h₂) fnDecomp_of HopWord_holds altLin_of
      (geoStep_of hW hP hF lefSum_of Tw.hodgeGood Tw.hodgeTr Tw.hopOp Tw.opTr)
      CxLin_holds Tw.hodgeGood
  have hE : HodgeEig :=
    hodgeEig_of hT hP (hodgeFin_of hW) unifBound_of hExpInj_of coeffOcc_of EigOf_holds HopWord_holds Tw.hodgeGood
  ⟨hT, hE, kSHodge_of hE KSBc_holds SpecConj_holds MemOp_holds fnDecomp_of OccOf_holds⟩

theorem ksHodge_of_inputs (hW : HolomorphicLefschetzFormula) (hF : FixK) (h₁ : GlobalTheory.RootSumWeights.MarkWeightedFixedPointEqDefinitePairOdd) (h₂ : GlobalTheory.LKDef.TraceDefinitePairsEqAutomorphicTrace) :
    UpperTheory.Gal.Int.Geo.KSHodge :=
  (hodgeTrace_of_lefschetz_and_groupSide hW KSProj_holds hF h₁ h₂).2.2

end UpperTheory.Gal.LocalSmoothExtension
end
end
