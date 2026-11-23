module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSeparatedOfIsQProjOver
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeQuotientTriple
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointPicardClassEqTranslateOfTrivialLambda
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelTrivialRigidTranslateLineBundle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleRigidTranslateLineBundleRationalPoint
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPolarisationDescentMulOddVeryDense
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPointPrimitiveBundleEqTranslatePpav
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEquivariantToBidual
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsIsoQuotToImOmegaLieOfSplit
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.MemVanishingIdealOfFormVanishingTorsion
public import ReciprocityTheory.L2DbarEstimates.IsLocalHomeomorph
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRigLBCubical
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullEqZeroOfChart
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsProjOverOfIsProjOverBase
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelObjectPullbackExistsAndPrincipal
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelStructurePullback
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleTrivialOfSamePolarization

section

@[expose] public section

open CategoryTheory AlgebraicGeometry Set Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.ArInt GlobalTheory.TorsionForm
open GlobalTheory.LB (toMod)
open GlobalTheory.LieVB (omega)
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe (Fl Pt stdLat symMat tauU siegel symPart ChernIsFlat IsMetric InducesPolarisation cov)
open ReciprocityTheory.L2DbarEstimates (V)
open Filter Topology
open scoped ContDiff
open MonoidalCategory CartesianMonoidalCategory Limits
open GlobalTheory.CechPic (Pic cls lam)
open MonObj
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AmpleKerFibre

theorem relAmple_kTriv_of_lam_eq : ∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Sp K)) [GrpObj B], IsAbelianScheme B → ∀ (L₀ : LB B.left) (h₀ : L₀.IsLB), Out.RelAmple B L₀ → Out.KTriv B L₀ → ∀ (N : LB B.left) (hN : N.IsLB), lam (cls N hN) (fst B B) (snd B B) = lam (cls L₀ h₀) (fst B B) (snd B B) → Out.RelAmple B N ∧ Out.KTriv B N := by
  intro K _ _ B _ hB L₀ h₀ hA hK N hN hlam
  have := hB.comm
  obtain ⟨O, hO, eO⟩ := CechPic.cls_surj (cls N hN - cls L₀ h₀)
  have lamO : lam (cls O hO) (fst B B) (snd B B) = 0 := by
    rw [eO, GlobalTheory.PrimitiveOverField.lam_sub, hlam, sub_self]
  obtain ⟨x, hx⟩ := GlobalTheory.PointTranslate.exists_point_cls_eq_lam K B hB L₀ h₀ hK O hO lamO
  have hR : (GlobalTheory.RigidTranslate.rigTransl L₀ x).IsLB := LB.isLB_linComb h₀ _ _
  have hcls : cls _ hR = cls N hN := by
    rw [CechPic.cls_linComb h₀, Fin.sum_univ_two]
    have e1 : cls N hN = cls O hO + cls L₀ h₀ := by rw [eO]; abel
    rw [e1, hx, GlobalTheory.PrimitiveOverField.lam_const, Over.id_left, CechPic.pull_id]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, neg_smul]
    rw [GlobalTheory.PrimitiveOverField.pull_const, GlobalTheory.PolTranslate.transl, _root_.mul_comm (𝟙 B)]
    abel
  have hiso := (CechPic.cls_eq_iff hR hN).1 hcls
  refine ⟨?_, GlobalTheory.MulDescent.kTriv_of_lbIso hR hN hiso
    (GlobalTheory.RigidTranslate.kTriv_rigTransl_any _ B L₀ h₀ x hK)⟩
  have hAR := GlobalTheory.RigidTranslate.relAmple_rigTransl_point K B hB L₀ h₀ x hA
  obtain ⟨w, hw⟩ : LBIso N ((GlobalTheory.RigidTranslate.rigTransl L₀ x).pull (𝟙 B.left)) :=
    hiso.symm.chartPull (Geo.Tor.chartPullId N) (Geo.Tor.chartPullPull _ (𝟙 _) (𝟙 _) rfl)
  exact relAmple_pull (A' := B) (IsPullback.id_horiz B.hom) hR hN ((isGen_iff w).1 hw) ⊤
    (isAffineOpen_top _) (fun _ => trivial) hAR

end GlobalTheory.AmpleKerFibre
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleOfMumfordBundleIsoUniversal

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZM

namespace GlobalTheory.MumAmple

theorem relAmple_of_lam_iso_univ : ∀ {o : Type} [CommRing o] {ζ : o} {g n : ℕ} (F : SFam g n ζ) (R' : Type) [CommRing R'] [IsNoetherianRing R'] (T : Sp R' ⟶ F.X) (B : Over (Sp R')) [GrpObj B] [IsCommMonObj B] (β : B.left ⟶ F.univ.A.left) (β₂ : (G2 B).left ⟶ (G2 F.univ.A).left), IsGrpPullback B F.univ.A T β → IsSquare β β₂ → ∀ L : LB B.left, L.IsLB → LBIso (abelian₂ B L) (F.univ.P.pull β₂) → RelAmple B L := by
  intro o _ ζ g n F R' _ _ T B _ _ β β₂ hpb hsq L hL hiso
  have hB : IsAbelianScheme B :=
    { comm := inferInstance
      smooth := MorphismProperty.of_isPullback (P := @Smooth) hpb.1 F.univ.ab.smooth
      proper := MorphismProperty.of_isPullback (P := @IsProper) hpb.1 F.univ.ab.proper
      geomConnected := MorphismProperty.of_isPullback (P := @GeometricallyConnected) hpb.1 F.univ.ab.geomConnected }
  have := hB.proper
  have := hB.smooth
  refine ProperFinite.relAmple_of_geometricFibres B hL fun K _ _ y => ?_
  have hk := isGrpPullback_pullback B y
  have hkU := hk.comp hpb
  obtain ⟨⟨c, hc⟩, hprin⟩ := GlobalTheory.siegPre_pullback g n o ζ F.X (Sp K) F.s ((y ≫ T) ≫ F.s) (y ≫ T) F.univ rfl
  have hcp := hprin c hc F.princ
  obtain ⟨φc, φc₂, hcpb, hcsq, hcP, -⟩ := hc
  obtain ⟨L₀, h₀, hlam₀, ha₀⟩ := PolBundleLoc.exists_ample_root c.A c.ab c.isLB c.rig₁ c.rig₂ c.symm hcp.1
  have hk₀ := KTrivOfLam.kTriv_of_lam_iso _ c.A c.ab c.P c.isLB hcp.2 L₀ h₀ hlam₀
  obtain ⟨e, he, heφ⟩ := grpPullback_iso hcpb hkU
  haveI := he
  let ψ : c.A.left ⟶ B.left := e.hom.left ≫ pullback.fst B.hom y
  have hψ : IsGrpPullback c.A B y ψ := by
    have := (isGrpPullback_of_iso e).comp hk
    rwa [Category.id_comp] at this
  obtain ⟨ψ₂, sψ⟩ := SiegPull.exists_isSquare hψ.1.w
  have hN : (L.pull ψ).IsLB := pull_isLB hL ψ
  have hlamN : LBIso (abelian₂ c.A (L.pull ψ)) ((abelian₂ B L).pull ψ₂) :=
    SiegPull.lbIso_lam_pull hψ ((CechPic.cls_eq_iff hN hN).1 rfl) sψ
  have hsq' : IsSquare (ψ ≫ β) (ψ₂ ≫ β₂) := SiegPull.isSquare_comp sψ hsq
  have hφ : ψ ≫ β = φc := by simpa [ψ, Category.assoc] using heφ
  have e₂ : ψ₂ ≫ β₂ = φc₂ := SiegPull.isSquare_unique hsq' hcsq hφ
  have hpullP : LBIso ((abelian₂ B L).pull ψ₂) (F.univ.P.pull (ψ₂ ≫ β₂)) := SiegPull.lbIso_pull_comp hiso ψ₂
  rw [e₂] at hpullP
  have iLN : (abelian₂ c.A (L.pull ψ)).IsLB := LB.isLB_linComb hN _ _
  have iL0 : (abelian₂ c.A L₀).IsLB := LB.isLB_linComb h₀ _ _
  have iLB : (abelian₂ B L).IsLB := LB.isLB_linComb hL _ _
  have hlam : CechPic.lam (CechPic.cls (L.pull ψ) hN) (fst c.A c.A) (snd c.A c.A) =
      CechPic.lam (CechPic.cls L₀ h₀) (fst c.A c.A) (snd c.A c.A) :=
    (CechPic.cls_cube_two hN _ _ iLN).symm.trans
      (((CechPic.cls_eq_iff iLN (pull_isLB iLB _)).2 hlamN).trans
        (((CechPic.cls_eq_iff (pull_isLB iLB _) (pull_isLB F.univ.isLB _)).2 hpullP).trans
          (((CechPic.cls_eq_iff c.isLB (pull_isLB F.univ.isLB _)).2 hcP).symm.trans
            (((CechPic.cls_eq_iff iL0 c.isLB).2 hlam₀).symm.trans (CechPic.cls_cube_two h₀ _ _ iL0)))))
  obtain ⟨hampN, -⟩ := AmpleKerFibre.relAmple_kTriv_of_lam_eq K c.A c.ab L₀ h₀ ha₀ hk₀ (L.pull ψ) hN hlam
  have : IsProper c.A.hom := c.ab.proper
  have hAN := (relAmple_iff_isAmpleLB_of_isAffine c.A hN).1 hampN
  haveI : IsIso e.inv.left := inferInstanceAs (IsIso ((Over.forget _).map e.inv))
  have h1 := hAN.pull_of_isAffineHom e.inv.left
  have h2 : LBIso ((L.pull ψ).pull e.inv.left) (L.pull (pullback.fst B.hom y)) := by
    have h3 := SiegPull.lbIso_pull_comp ((CechPic.cls_eq_iff hN hN).1 rfl) e.inv.left
    have ee : e.inv.left ≫ ψ = pullback.fst B.hom y := by
      simp only [ψ]
      rw [← Category.assoc, ← Over.comp_left, e.inv_hom_id, Over.id_left, Category.id_comp]
    rwa [ee] at h3
  exact (isAmpleLB_congr (pull_isLB hN _) (pull_isLB hL _) h2).1 h1

end GlobalTheory.MumAmple
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleOfMumfordBundleIsoUniversalStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.relAmple_of_mumfordBundle_iso_universal : ∀ {o : Type} [CommRing o] {ζ : o} {g n : ℕ} (F : SFam g n ζ) (R' : Type) [CommRing R'] [IsNoetherianRing R'] (T : Sp R' ⟶ F.X) (B : Over (Sp R')) [GrpObj B] [IsCommMonObj B] (β : B.left ⟶ F.univ.A.left) (β₂ : (G2 B).left ⟶ (G2 F.univ.A).left), IsGrpPullback B F.univ.A T β → IsSquare β β₂ → ∀ L : LB B.left, L.IsLB → LBIso (abelian₂ B L) (F.univ.P.pull β₂) → RelAmple B L := by
  first | exact @GlobalTheory.MumAmple.relAmple_of_lam_iso_univ | exact GlobalTheory.MumAmple.relAmple_of_lam_iso_univ | (intros; apply GlobalTheory.MumAmple.relAmple_of_lam_iso_univ <;> assumption)
end
end
