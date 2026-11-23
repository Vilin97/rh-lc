module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeIdempotentCoeffAcrossLayers
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChebotarevDegreeOneIffCheb
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LabConj
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NormalIntegrality
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSetAutWdTieLabConj
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTameGeneratorsGreenCuspidalLabellingStatement
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteTwistFrameExtraExcludedOverSmallPrimes
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FillPreservesIdempotent
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RayClassFieldHostConductorIsRayClassFieldStatement
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOfFinOrderFbar
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsWdSide
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyResidueFieldUnitBallEquiv
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Tactic.NormNum.Parity
import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.Objects
import ReciprocityTheory.Automorphisms.PlaceA
public import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.ExistsCgTrueCharSide
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsNbcAuSideStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MRowTame

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTypes

section

@[expose] public section

noncomputable section

namespace GlobalTheory.ParRay

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial




theorem exists_types : GlobalTheory.Published.RayClassFieldSt → GlobalTheory.Published.ChebotarevDegreeOne → ∀ (D : D7) (hE : IsEmpty D.nd.Loc)
    (jE : D.host.E →+* Qb) (Pl : PlSide D), (∀ k, IsRayPrime (KQbar D jE) (D.host.QS * D.host.q * D.host.d) (D.host.g k)) →
    ∃ X h1 h0, X.tg = D.ntypes.tg ∧ X.teichC = D.ntypes.teichC ∧ X.eSer = D.ntypes.eSer ∧ X.cenAmb = D.ntypes.cenAmb ∧
      X.cenMt = D.ntypes.cenMt ∧ Nonempty (ParSide (setTy D hE X h1 h0) jE) ∧
      (Nonempty (GrpSide D) → IotaOk (setTy D hE X h1 h0) ⟨Pl.ι, Pl.ι_w, Pl.plB, Pl.plB_eq, Pl.plκ⟩) := by
  intro hray _ D hE jE Pl hg
  obtain ⟨h, hf, hgal, hab, hunr, hsplit⟩ := GlobalTheory.T.rayClassFieldHostConductor_isRayClassField hray D jE
  letI := algK D jE h
  have := nfOf hf
  let X : NTypes D.naut :=
    { D.ntypes with
      Mray := MrayC D jE
      instMray := inferInstance
      nfMray := nfOf hf
      algKM := algK D jE h
      Mray_gal := hgal
      Mray_ab := hab
      Mray_unr := hunr
      g_Mray := fun k => hsplit _ (hg k)
      iota := fun k _ w =>
        haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
        redHom (Pl.plB w) (Pl.plκ w) (D.ntypes.teichC k)
      iota_inj := fun k _ w x y hx hy cx cy hxy =>
        haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
        redHom_inj (Pl.plB w) (Pl.plκ w) (D.ntypes.teichC k) (D.ntypes.teichC_inj k) x y hx hy cx cy hxy
      Par := ParC D
      labPar := fun k σ v => D.naut.items₂ k (D.naut.plGw k v) (isoLoc D.nd D.naut σ.1 (D.naut.plGw k v))
      labPar_monic := fun k σ v => σ.2.2.2.2 k v
      locPar := fun σ w => isoLoc D.nd D.naut σ.1 w
      locPar_dim := fun σ w => (GlobalTheory.RowPar.lpDim_isoLoc D.naut σ.1 w).trans σ.2.2.2.1
      labPar_def := fun _ _ _ => rfl
      MtPar := fun _ _ _ => ⊥
      AmbPar := fun _ _ => ⊥ }
  refine ⟨X, D.nStage_trivialCharacter_compat, D.nStage_trivialCharacter_coeff_eq, rfl, rfl, rfl, rfl, rfl, ⟨?_⟩, fun _ => ?_⟩
  · exact
      { eM := RingEquiv.refl _
        eM_K := fun _ => rfl
        eP := Equiv.refl _
        locPar_def := fun _ _ => rfl }
  · intro lam k v x
    rfl

end GlobalTheory.ParRay

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypesTrueOfRayClass

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.HeightCounting.TopA



theorem exists_label_of_eq {g : ℕ} [Fact g.Prime] {t t' : Formalism.CyclotomicNorms.Fbar g →* ℂ} (e : t' = t)
    (h : ∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → t x = t y → x = y)
    (h' : ∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → t' x = t' y → x = y) (ζ : ℕ → Formalism.CyclotomicNorms.Fbar g) (hζ : IsGenSys ζ)
    (O : Formalism.IrreducibleCountingLemmas.TYPES.LabelMap (ZMod g) (convC t h ζ hζ)) (h1 : Formalism.IrreducibleCountingLemmas.TYPES.LabelMapEquivariant O) (h2 : LabTwLawO O) :
    ∃ O' : Formalism.IrreducibleCountingLemmas.TYPES.LabelMap (ZMod g) (convC t' h' ζ hζ), Formalism.IrreducibleCountingLemmas.TYPES.LabelMapEquivariant O' ∧ LabTwLawO O' ∧
      ∀ r f, eSerO O' r f = eSerO O r f := by
  subst e
  exact ⟨O, h1, h2, fun _ _ => rfl⟩




theorem exists_grp_setTy (D : D7) (hE : IsEmpty D.nd.Loc) (X : NTypes D.naut) (h1 h0) (e1 : X.tg = D.ntypes.tg)
    (e2 : X.teichC = D.ntypes.teichC) (e3 : X.eSer = D.ntypes.eSer) (Γ : GrpSide D) :
    ∃ Γ' : GrpSide (setTy D hE X h1 h0), Γ'.ζ = Γ.ζ := by
  have hO := fun k => haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    exists_label_of_eq (congrFun e2 k) (D.ntypes.teichC_inj k) (X.teichC_inj k) (Γ.ζ k) (Γ.ζ_gen k) (Γ.O k) (Γ.O_equiv k) (Γ.O_tw k)
  choose O hO1 hO2 hO3 using hO
  refine ⟨{ tA := Γ.tA, tκ := Γ.tκ, teichC_def := fun k => ?_, ζ := Γ.ζ, ζ_gen := Γ.ζ_gen, O := O, eSer_def := fun k f => ?_
            kv := Γ.kv, tg_tame := fun k v => ?_, O_equiv := hO1, O_tw := hO2 }, rfl⟩
  · have := Γ.teichC_def k
    rw [← e2] at this
    exact this
  · exact ((congrFun (congrFun e3 k) f).trans (Γ.eSer_def k f)).trans (hO3 k _ f).symm
  · have := Γ.tg_tame k v
    rw [← e1] at this
    exact this




theorem exists_kv_of_eq (D : D7) {g : ℕ} [Fact g.Prime] {w w' : PlE D.host} (e : w' = w) (σ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om)
    (ζ : ℕ → Formalism.CyclotomicNorms.Fbar g) (κ : IsLocalRing.ResidueField (D.nd.plOm.1 w) ≃+* Formalism.CyclotomicNorms.Fbar g)
    (h : TameCoupled (D.nd.plOm.1 w) κ σ ζ) :
    ∃ κ' : IsLocalRing.ResidueField (D.nd.plOm.1 w') ≃+* Formalism.CyclotomicNorms.Fbar g, TameCoupled (D.nd.plOm.1 w') κ' σ ζ := by
  subst e
  exact ⟨κ, h⟩


theorem exists_eq_of_heq {P P' : Fin 2 → Type} {β : Type} (e : P' = P) {f : ∀ k, P k → β} {f' : ∀ k, P' k → β} (h : HEq f' f)
    (k : Fin 2) (v : P' k) : ∃ v₀, f k v₀ = f' k v := by
  subst e
  exact ⟨v, by rw [eq_of_heq h]⟩


end GlobalTheory.HeightCounting.TopA

end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ConclOfGrp

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
noncomputable section
namespace GlobalTheory.HeightCounting.TopA
def ConclAlt (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb)
    (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r) : Prop :=
  ∃ (L : Lay0 D) (hZ : L.ZOk) (hη : L.EtaOk) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding (setK D L hZ hη) (cfK L hZ hη cf) jE), Nonempty (_root_.GlobalTheory.HeightCounting.CGTrueT hL _ A.wdT) ∧ _root_.GlobalTheory.HeightCounting.AutomorphicSideRealised hL _ A.wdT A.au ∧ _root_.GlobalTheory.HeightCounting.RepresentationParametersHold hL (setK D L hZ hη) rep (fun σ w => A.wdT.e w (A.row.locR σ w)) A.row.satR ∧ GlobalTheory.Mem.Top.TypesTrue L.ntypes cf.P cf.W ∧ L.nd.PlG = D.nd.PlG ∧ HEq L.naut.plGw D.naut.plGw ∧ HEq L.ntypes.cenAmb D.ntypes.cenAmb ∧ HEq L.ntypes.cenMt D.ntypes.cenMt ∧ (∀ k, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩; A.grp.ζ k = (GlobalTheory.Mem.TypePl.labDat (D.host.g k)).gen) ∧ L.loc = D.loc ∧ HEq (@NData.Om _ _ _ L.nd) (@NData.Om _ _ _ D.nd) ∧ HEq (@NData.instOm _ _ _ L.nd) (@NData.instOm _ _ _ D.nd) ∧ HEq (@NData.algOm _ _ _ L.nd) (@NData.algOm _ _ _ D.nd) ∧ HEq (@NData.plOm _ _ _ L.nd) (@NData.plOm _ _ _ D.nd) ∧ LabConj _ A.wdT


theorem conclusion_of_au_true_and_types_true (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb)
    (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (h1 : Nonempty (_root_.GlobalTheory.HeightCounting.CGTrueT hL D A.wdT))
    (h2 : _root_.GlobalTheory.HeightCounting.AutomorphicSideRealised hL D A.wdT A.au) (h3 : _root_.GlobalTheory.HeightCounting.RepresentationParametersHold hL D rep (fun σ w => A.wdT.e w (A.row.locR σ w)) A.row.satR)
    (h4 : GlobalTheory.Mem.Top.TypesTrue D.ntypes cf.P cf.W)
    (h5 : ∀ k, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩; A.grp.ζ k = (GlobalTheory.Mem.TypePl.labDat (D.host.g k)).gen)
    (h6 : LabConj D A.wdT) : _root_.GlobalTheory.HeightCounting.TopA.ConclAlt hL D cf jE rep :=
  ⟨lay0 D, ⟨D.Z_tie, D.Zgood_tie⟩, D.etaJ_tie, A, h1, h2, h3, h4, rfl, HEq.rfl, HEq.rfl, HEq.rfl, h5, rfl, HEq.rfl, HEq.rfl,
    HEq.rfl, HEq.rfl, h6⟩


theorem concl_setK_alt (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb)
    (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r) (L : Lay0 D) (hZ : L.ZOk) (hη : L.EtaOk)
    (k1 : L.nd.PlG = D.nd.PlG) (k2 : HEq L.naut.plGw D.naut.plGw) (k3 : HEq L.ntypes.cenAmb D.ntypes.cenAmb)
    (k4 : HEq L.ntypes.cenMt D.ntypes.cenMt) (k5 : L.loc = D.loc) (k6 : HEq (@NData.Om _ _ _ L.nd) (@NData.Om _ _ _ D.nd))
    (k7 : HEq (@NData.instOm _ _ _ L.nd) (@NData.instOm _ _ _ D.nd))
    (k8 : HEq (@NData.algOm _ _ _ L.nd) (@NData.algOm _ _ _ D.nd))
    (k9 : HEq (@NData.plOm _ _ _ L.nd) (@NData.plOm _ _ _ D.nd))
    (h : _root_.GlobalTheory.HeightCounting.TopA.ConclAlt hL (setK D L hZ hη) (cfK L hZ hη cf) jE rep) : _root_.GlobalTheory.HeightCounting.TopA.ConclAlt hL D cf jE rep := by
  obtain ⟨L', hZ', hη', A, h1, h2, h3, h4, e1, e2, e3, e4, h5, e5, e6, e7, e8, e9, h6⟩ := h
  exact ⟨L', hZ', hη', A, h1, h2, h3, h4, e1.trans k1, e2.trans k2, e3.trans k3, e4.trans k4, h5, e5.trans k5, e6.trans k6,
    e7.trans k7, e8.trans k8, e9.trans k9, h6⟩


theorem conclusion_of_automorphic_side_true (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (hdR : GlobalTheory.Published.DeRhamPotSemistable) (hR : GlobalTheory.Published.RayClassFieldSt)
    (hC : GlobalTheory.Published.ChebotarevDegreeOne) (D : D7) (hE : IsEmpty D.nd.Loc) (cf : CharFrame D) (jE : D.host.E →+* Qb)
    (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r)
    (hray : ∀ k, IsRayPrime (KQbar D jE) (D.host.QS * D.host.q * D.host.d) (D.host.g k))
    (hT : GlobalTheory.Mem.Top.TypesTrue D.ntypes cf.P cf.W) (Γ : GrpSide D)
    (hζ : ∀ k, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩; Γ.ζ k = (GlobalTheory.Mem.TypePl.labDat (D.host.g k)).gen)
    (hχ : ChiTOk D cf)
    (T : GlobalTheory.RowTie.WDTie D.nd D.naut) (hlab : LabTrue D T) (hconj : LabConj D T) (Rs : RowSide D)
    (hrow : _root_.GlobalTheory.HeightCounting.RepresentationParametersHold hL D rep (fun σ w => T.e w (Rs.locR σ w)) Rs.satR)
    (hcg : Nonempty (_root_.GlobalTheory.HeightCounting.CGTrueT hL D T)) (chr : CharSide D cf) (au : _root_.GlobalTheory.HeightCounting.AUSideAlt D) (hau : _root_.GlobalTheory.HeightCounting.AutomorphicSideRealised hL D T au) : _root_.GlobalTheory.HeightCounting.TopA.ConclAlt hL D cf jE rep := by
  obtain ⟨Pl⟩ := GlobalTheory.HeightCounting.nonempty_plSide D
  obtain ⟨X, h1, h0, e1, e2, e3, e4, e5, ⟨par⟩, hι⟩ := GlobalTheory.ParRay.exists_types hR hC D hE jE Pl hray
  obtain ⟨Γ', hΓ⟩ := exists_grp_setTy D hE X h1 h0 e1 e2 e3 Γ
  obtain ⟨wd⟩ := GlobalTheory.HeightCounting.exists_wdSide hdR (setTy D hE X h1 h0) T
  obtain ⟨cg⟩ := hcg
  let cf' : CharFrame (setTy D hE X h1 h0) :=
    ⟨cf.P, cf.W, cf.mu0, cf.eta, cf.chiPsi, cf.del, cf.del', cf.isMu0, cf.isEta, cf.isChi, cf.isDel, cf.isDel'⟩
  have hlab' : LabTrue (setTy D hE X h1 h0) T := by
    intro k v a
    have := hlab k v a
    rw [← e1, ← e2] at this
    exact this
  have hconj' : LabConj (setTy D hE X h1 h0) T := by
    intro k v w hw
    have := hconj k v w hw
    rw [← e1, ← e2] at this
    exact this
  have hχ' : ChiTOk (setTy D hE X h1 h0) cf' := by
    intro k v j u hu
    have := hχ k v j u hu
    rw [← e1, ← e2] at this
    exact this
  have hT' : GlobalTheory.Mem.Top.TypesTrue X cf.P cf.W :=
    ⟨hT.pl, fun k => (congrFun e2 k).trans (hT.teich k), hT.chi, fun k p => (congrFun (congrFun e3 k) p).trans (hT.ser k p)⟩
  have H : _root_.GlobalTheory.HeightCounting.TopA.ConclAlt hL (setTy D hE X h1 h0) cf' jE rep :=
    _root_.GlobalTheory.HeightCounting.TopA.conclusion_of_au_true_and_types_true hL (setTy D hE X h1 h0) cf' jE rep
      { bare := hE, wdT := T, lab := hlab', chr := { chr with }, row := ⟨Rs.locR, Rs.satR, Rs.lab_eq⟩
        pl := ⟨Pl.ι, Pl.ι_w, Pl.plB, Pl.plB_eq, Pl.plκ⟩, iota := hι ⟨Γ⟩, wd := wd, grp := Γ', par := par, au := { au with }
        chiT := hχ' }
      ⟨{ cg with }⟩ hau hrow hT' (fun k => (congrFun hΓ k).trans (hζ k)) hconj'
  exact _root_.GlobalTheory.HeightCounting.TopA.concl_setK_alt hL D cf jE rep (lay0 (setTy D hE X h1 h0)) ⟨fun i => hE.elim i, fun i => hE.elim i⟩ D.etaJ_tie
    rfl HEq.rfl (heq_of_eq e4) (heq_of_eq e5) rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl H


theorem conclusion_of_cusp_galois_true (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (hdR : GlobalTheory.Published.DeRhamPotSemistable) (hR : GlobalTheory.Published.RayClassFieldSt)
    (hC : GlobalTheory.Published.ChebotarevDegreeOne) (D : D7) (hE : IsEmpty D.nd.Loc) (cf : CharFrame D) (jE : D.host.E →+* Qb)
    (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r)
    (hray : ∀ k, IsRayPrime (KQbar D jE) (D.host.QS * D.host.q * D.host.d) (D.host.g k))
    (hT : GlobalTheory.Mem.Top.TypesTrue D.ntypes cf.P cf.W) (Γ : GrpSide D)
    (hζ : ∀ k, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩; Γ.ζ k = (GlobalTheory.Mem.TypePl.labDat (D.host.g k)).gen)
    (hχ : ChiTOk D cf)
    (T : GlobalTheory.RowTie.WDTie D.nd D.naut) (hlab : LabTrue D T) (hconj : LabConj D T) (Rs : RowSide D)
    (hrow : _root_.GlobalTheory.HeightCounting.RepresentationParametersHold hL D rep (fun σ w => T.e w (Rs.locR σ w)) Rs.satR)
    (hcg : Nonempty (_root_.GlobalTheory.HeightCounting.CGTrueT hL D T)) (chr : CharSide D cf) : _root_.GlobalTheory.HeightCounting.TopA.ConclAlt hL D cf jE rep := by
  obtain ⟨C, au, hau⟩ := _root_.GlobalTheory.T.exists_nbc_auSide_true_of_isEmpty_loc hL D hE T
  obtain ⟨cg⟩ := hcg
  let cf' : CharFrame (setBC D C) :=
    ⟨cf.P, cf.W, cf.mu0, cf.eta, cf.chiPsi, cf.del, cf.del', cf.isMu0, cf.isEta, cf.isChi, cf.isDel, cf.isDel'⟩
  have H : _root_.GlobalTheory.HeightCounting.TopA.ConclAlt hL (setBC D C) cf' jE rep :=
    _root_.GlobalTheory.HeightCounting.TopA.conclusion_of_automorphic_side_true hL hdR hR hC (setBC D C) hE cf' jE rep hray hT { Γ with } hζ hχ T hlab hconj ⟨Rs.locR, Rs.satR, Rs.lab_eq⟩ hrow
      ⟨{ cg with }⟩ { chr with } au hau
  exact _root_.GlobalTheory.HeightCounting.TopA.concl_setK_alt hL D cf jE rep (lay0 (setBC D C)) ⟨fun i => hE.elim i, fun i => hE.elim i⟩ D.etaJ_tie
    rfl HEq.rfl HEq.rfl HEq.rfl rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl H


theorem conclusion_of_local_parameters_true (hA : GlobalTheory.Published.AutomorphicFormsFiniteGL) (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (hdR : GlobalTheory.Published.DeRhamPotSemistable) (hR : GlobalTheory.Published.RayClassFieldSt)
    (hC : GlobalTheory.Published.ChebotarevDegreeOne) (D : D7) (hE : IsEmpty D.nd.Loc) (cf : CharFrame D) (jE : D.host.E →+* Qb)
    (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r)
    (hray : ∀ k, IsRayPrime (KQbar D jE) (D.host.QS * D.host.q * D.host.d) (D.host.g k))
    (hT : GlobalTheory.Mem.Top.TypesTrue D.ntypes cf.P cf.W) (Γ : GrpSide D)
    (hζ : ∀ k, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩; Γ.ζ k = (GlobalTheory.Mem.TypePl.labDat (D.host.g k)).gen)
    (hχ : ChiTOk D cf)
    (T : GlobalTheory.RowTie.WDTie D.nd D.naut) (hlab : LabTrue D T) (hconj : LabConj D T) (Rs : RowSide D)
    (hrow : _root_.GlobalTheory.HeightCounting.RepresentationParametersHold hL D rep (fun σ w => T.e w (Rs.locR σ w)) Rs.satR) :
    _root_.GlobalTheory.HeightCounting.TopA.ConclAlt hL D cf jE rep := by
  obtain ⟨K, hcg, ⟨chr⟩⟩ := _root_.UpperTheory.One.M.New.exists_cgTrue_charSide hL hA D hE T cf hT.pl
  have H : _root_.GlobalTheory.HeightCounting.TopA.ConclAlt hL (setCG D hE K) (cfCG hE K cf) jE rep :=
    _root_.GlobalTheory.HeightCounting.TopA.conclusion_of_cusp_galois_true hL hdR hR hC (setCG D hE K) hE (cfCG hE K cf) jE rep hray ⟨hT.pl, hT.teich, hT.chi, hT.ser⟩ { Γ with } hζ hχ
      (wdCG hE K T) hlab hconj ⟨Rs.locR, Rs.satR, Rs.lab_eq⟩ hrow hcg chr
  exact _root_.GlobalTheory.HeightCounting.TopA.concl_setK_alt hL D cf jE rep (lay0 (setCG D hE K)) ⟨fun i => hE.elim i, fun i => hE.elim i⟩ D.etaJ_tie
    rfl HEq.rfl HEq.rfl HEq.rfl rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl H


theorem conclusion_of_group_side (hA : GlobalTheory.Published.AutomorphicFormsFiniteGL) (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (hdR : GlobalTheory.Published.DeRhamPotSemistable) (hR : GlobalTheory.Published.RayClassFieldSt)
    (hC : GlobalTheory.Published.ChebotarevDegreeOne) (D : D7) (hE : IsEmpty D.nd.Loc) (cf : CharFrame D) (jE : D.host.E →+* Qb)
    (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r)
    (hray : ∀ k, IsRayPrime (KQbar D jE) (D.host.QS * D.host.q * D.host.d) (D.host.g k))
    (hT : GlobalTheory.Mem.Top.TypesTrue D.ntypes cf.P cf.W) (Γ : GrpSide D)
    (hζ : ∀ k, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩; Γ.ζ k = (GlobalTheory.Mem.TypePl.labDat (D.host.g k)).gen)
    (hχ : ChiTOk D cf)
    (hd : RowDepth D rep) : _root_.GlobalTheory.HeightCounting.TopA.ConclAlt hL D cf jE rep := by
  obtain ⟨Rw, hRw⟩ := _root_.GlobalTheory.RowPar.exists_rowWD_rowTrue_m_alt hL D rep hd
  obtain ⟨lab, h, A, C, tm, tg, hl, hpl, T, hlab, hconj, Rs, hp, hs⟩ := GlobalTheory.HeightCounting.exists_setAut_wdTie_labConj D hE Rw
  let cf' : CharFrame (setAut D hE lab h A C tm tg hl) :=
    ⟨cf.P, cf.W, cf.mu0, cf.eta, cf.chiPsi, cf.del, cf.del', cf.isMu0, cf.isEta, cf.isChi, cf.isDel, cf.isDel'⟩
  have hk := fun k v => haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    exists_kv_of_eq D (hpl k v) (D.ntypes.tg k v) (Γ.ζ k) (Γ.kv k v) (Γ.tg_tame k v)
  choose kv hkv using hk
  have hχ' : ChiTOk (setAut D hE lab h A C tm tg hl) cf' := by
    intro k v j u hu
    have := hχ k v j u hu
    rw [← hpl k v] at this
    exact this
  have hrow : _root_.GlobalTheory.HeightCounting.RepresentationParametersHold hL (setAut D hE lab h A C tm tg hl) rep (fun σ w => T.e w (Rs.locR σ w)) Rs.satR := by
    have e1 : (fun σ w => T.e w (Rs.locR σ w)) = Rw.par := funext fun σ => funext fun w => hp σ w
    have e2 : Rs.satR = Rw.sat := funext fun σ => funext fun w => hs σ w
    rw [e1, e2]
    exact hRw
  have hT' : GlobalTheory.Mem.Top.TypesTrue (setAut D hE lab h A C tm tg hl).ntypes cf.P cf.W :=
    ⟨fun k v => (hpl k v).symm ▸ hT.pl k v, hT.teich, hT.chi, hT.ser⟩
  have H : _root_.GlobalTheory.HeightCounting.TopA.ConclAlt hL (setAut D hE lab h A C tm tg hl) cf' jE rep :=
    _root_.GlobalTheory.HeightCounting.TopA.conclusion_of_local_parameters_true hA hL hdR hR hC (setAut D hE lab h A C tm tg hl) hE cf' jE rep hray hT'
      { Γ with kv := kv, tg_tame := hkv } hζ hχ' T hlab hconj Rs hrow
  exact _root_.GlobalTheory.HeightCounting.TopA.concl_setK_alt hL D cf jE rep (lay0 (setAut D hE lab h A C tm tg hl)) ⟨fun i => hE.elim i, fun i => hE.elim i⟩ D.etaJ_tie
    rfl (heq_of_eq (funext fun k => funext fun v => hpl k v)) HEq.rfl HEq.rfl rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl H


theorem exists_sideA_alt : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, GlobalTheory.Published.AutomorphicFormsFiniteGL → GlobalTheory.Published.DeRhamPotSemistable → GlobalTheory.Published.GreenCuspidal → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt → GlobalTheory.Published.ChebotarevDegreeOne → ∀ (D : D7) (hE : IsEmpty D.nd.Loc) (cf : CharFrame D) (jE : D.host.E →+* Qb) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r), (∀ j g, ∃ z : ℤ, eExp D j g = z) → GlobalTheory.Mem.Top.TypesTrue D.ntypes cf.P cf.W → RowDepth D rep → (∀ k, IsRayPrime (KQbar D jE) (D.host.QS * D.host.q * D.host.d) (D.host.g k)) → ∃ (L : Lay0 D) (hZ : L.ZOk) (hη : L.EtaOk) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding (setK D L hZ hη) (cfK L hZ hη cf) jE), Nonempty (_root_.GlobalTheory.HeightCounting.CGTrueT hL _ A.wdT) ∧ _root_.GlobalTheory.HeightCounting.AutomorphicSideRealised hL _ A.wdT A.au ∧ _root_.GlobalTheory.HeightCounting.RepresentationParametersHold hL (setK D L hZ hη) rep (fun σ w => A.wdT.e w (A.row.locR σ w)) A.row.satR ∧ GlobalTheory.Mem.Top.TypesTrue L.ntypes cf.P cf.W ∧ L.nd.PlG = D.nd.PlG ∧ HEq L.naut.plGw D.naut.plGw ∧ HEq L.ntypes.cenAmb D.ntypes.cenAmb ∧ HEq L.ntypes.cenMt D.ntypes.cenMt ∧ (∀ k, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩; A.grp.ζ k = (GlobalTheory.Mem.TypePl.labDat (D.host.g k)).gen) ∧ L.loc = D.loc ∧ HEq (@NData.Om _ _ _ L.nd) (@NData.Om _ _ _ D.nd) ∧ HEq (@NData.instOm _ _ _ L.nd) (@NData.instOm _ _ _ D.nd) ∧ HEq (@NData.algOm _ _ _ L.nd) (@NData.algOm _ _ _ D.nd) ∧ HEq (@NData.plOm _ _ _ L.nd) (@NData.plOm _ _ _ D.nd) ∧ LabConj _ A.wdT := by
  intro hL hA hdR hG hAr hR hC D hE cf jE rep hz hT hd hray
  obtain ⟨L, hZ, hη, hE', hT', k1, k2, k3, k4, ⟨Γ, hζ⟩, hχ, k5, k6, k7, k8, k9⟩ := GlobalTheory.T.exists_tame_generators_green_cuspidal_labelling hG hAr D hE cf hz hT
  have hd' : RowDepth (setK D L hZ hη) rep := by
    intro σ k v
    obtain ⟨v₀, e⟩ := exists_eq_of_heq k1 k2 k v
    obtain ⟨s, τ, h1, h2⟩ := hd σ k v₀
    exact ⟨s, τ, h1.trans e, h2⟩
  exact _root_.GlobalTheory.HeightCounting.TopA.concl_setK_alt hL D cf jE rep L hZ hη k1 k2 k3 k4 k5 k6 k7 k8 k9
    (_root_.GlobalTheory.HeightCounting.TopA.conclusion_of_group_side hA hL hdR hR hC (setK D L hZ hη) hE' (cfK L hZ hη cf) jE rep hray hT' Γ hζ hχ hd')
end GlobalTheory.HeightCounting.TopA
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ConclOfGrpStatement

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

theorem _root_.GlobalTheory.T.types_true_of_ray_class_alt : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, GlobalTheory.Published.AutomorphicFormsFiniteGL → GlobalTheory.Published.DeRhamPotSemistable → GlobalTheory.Published.GreenCuspidal → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt → GlobalTheory.Published.ChebotarevDegreeOne → ∀ (D : D7) (hE : IsEmpty D.nd.Loc) (cf : CharFrame D) (jE : D.host.E →+* Qb) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r), (∀ j g, ∃ z : ℤ, eExp D j g = z) → GlobalTheory.Mem.Top.TypesTrue D.ntypes cf.P cf.W → RowDepth D rep → (∀ k, IsRayPrime (GlobalTheory.HeightCounting.KQbar D jE) (D.host.QS * D.host.q * D.host.d) (D.host.g k)) → ∃ (L : Lay0 D) (hZ : L.ZOk) (hη : L.EtaOk) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding (setK D L hZ hη) (cfK L hZ hη cf) jE), Nonempty (_root_.GlobalTheory.HeightCounting.CGTrueT hL _ A.wdT) ∧ _root_.GlobalTheory.HeightCounting.AutomorphicSideRealised hL _ A.wdT A.au ∧ _root_.GlobalTheory.HeightCounting.RepresentationParametersHold hL (setK D L hZ hη) rep (fun σ w => A.wdT.e w (A.row.locR σ w)) A.row.satR ∧ GlobalTheory.Mem.Top.TypesTrue L.ntypes cf.P cf.W ∧ L.nd.PlG = D.nd.PlG ∧ HEq L.naut.plGw D.naut.plGw ∧ HEq L.ntypes.cenAmb D.ntypes.cenAmb ∧ HEq L.ntypes.cenMt D.ntypes.cenMt ∧ (∀ k, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩; A.grp.ζ k = (GlobalTheory.Mem.TypePl.labDat (D.host.g k)).gen) ∧ L.loc = D.loc ∧ HEq (@NData.Om _ _ _ L.nd) (@NData.Om _ _ _ D.nd) ∧ HEq (@NData.instOm _ _ _ L.nd) (@NData.instOm _ _ _ D.nd) ∧ HEq (@NData.algOm _ _ _ L.nd) (@NData.algOm _ _ _ D.nd) ∧ HEq (@NData.plOm _ _ _ L.nd) (@NData.plOm _ _ _ D.nd) ∧ LabConj _ A.wdT := by
  first | exact @_root_.GlobalTheory.HeightCounting.TopA.exists_sideA_alt | exact _root_.GlobalTheory.HeightCounting.TopA.exists_sideA_alt | (intros; apply _root_.GlobalTheory.HeightCounting.TopA.exists_sideA_alt <;> assumption)
end
end
end
