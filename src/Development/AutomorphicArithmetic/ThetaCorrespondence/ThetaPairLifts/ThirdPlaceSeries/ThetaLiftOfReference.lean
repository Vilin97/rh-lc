module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasThetaAtOfThetaMod
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PublishedInputsThirdLayer
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AtRows
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharacteristicFunctionIntegralApply
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreClausesOfWeakCharacterisation
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReferenceTupleDatumFormReadsThetaLiftInnerProducStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EasyInputs
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HcFiniteAndSchurMult
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowFiniteTypesIsotypicPartsSpanOrthogonal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SchurPairingInvariantUnderStandardGroupStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryCongruenceConjContainsCongruenceStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCanonicalModuleSuccessor
public import Formalism.LocalToGlobal.IndefiniteReal.CompZeroOfOrth
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
import Mathlib.Tactic.Linter.Style
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EtaJUntw
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotBaseCondFalse
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionOfIntro
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasThetaAtOfThetaMod
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FunKilled
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReferenceTupleThetaValuedMapMemThetaDataStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstRelIffTwistFactorAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelValuesThird
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TrilinearThetaFormReferenceTupleInvariantStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaFunctionsSpannedHeckeTwistedStandardFrameStatement
import Formalism.LocalToGlobal.IndefiniteReal.FockTheta.RealPlaceImaginaryGeneratorReEqZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JumpsCardOfBuilt

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReferenceTupleFormsSmoothAdmissibleUnitaryModule

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL GlobalTheory.SplitRead GlobalTheory.NPin

open GlobalTheory.RefPair

noncomputable section

namespace GlobalTheory.RefRowMod

open MeasureTheory Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Lev
  Formalism.IndefR.Links Formalism.IndefR.RecTie Formalism.IndefR.Mult Formalism.IndefR.PeterssonHilbertSpace



theorem main : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G]
    (Pl0 I0 T : Type) (A3 : Formalism.L2.DIV.FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks]
    [Algebra Ks D.what₂.LL] (R : Formalism.IndefR.Links.RealDat3 D A3 Ks) (F : Formalism.IndefR.Links.Face3 D A3)
    (cG : Formalism.L2.DIV.G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := A3) R.toRealDat F.lv2 X0),
    GlobalTheory.Mem.R3.Pins R F cG → GlobalTheory.Mem.R3.Holds R F → R.toRealDat.ExAt →
    ∀ (i : Fin D.R.m), ∃ X : GlobalTheory.NPin.RowMod D (GlobalTheory.RefTheta.repY Y) (i.1 + 1), GlobalTheory.RefTheta.IsCanonR Y i rfl X := by
  intro hH hC D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y hP _ hEx j
  have hcore := (GlobalTheory.CoreOfWeak.core_of_weak R F hP.char hEx).1
  have hmod := hcore.models
  have hθ := hmod.inf
  have hν := hmod.νW j
  have hHaar : (R.νW j).IsHaarMeasure := hν.1.1
  have hFD := hν.2
  have hSig : (Wc D j).SigOK := D.sp.W_sig _
  have hSA : SchurAll D := fun V _ S θ M J χ μ 𝓕 => (GlobalTheory.MultFinite.hcFinite_and_schurMult hH hC D θ V S M J χ μ 𝓕).2
  have hHA : HCAll D := fun V _ S θ M J χ => (GlobalTheory.MultFinite.hcFinite_and_schurMult hH hC D θ V S M J χ 0 ∅).1
  have hStd : GlobalTheory.Mem.R3.StdFrame Y.hF (Y.PW j) := Y.stdPsi.2 j
  have hcc := GlobalTheory.T.unitary_congruence_conj_contains_congruence D.host.E D.R.r
  obtain ⟨hlin, hherm, hpos⟩ := GlobalTheory.FinTypesRows.minf_sesq (M := R.MW j (sg0 D A3.A)) (θ := R.θ) (R.νW j) (R.fdW j)
    (Y.PW j) hSA hSig hθ hHaar hFD
  have hT := Y.tied.lift
  have hLev := GlobalTheory.FinTypesRows.levOK_levS (Y.PW j) hStd (R.βW j) (R.datWp j (R.levL F.lv2 false (sg0 D A3.A)))
  set c : ℝ := (∏ ρ, ((Mult.dimK _ _ (kapAt (Wc D j) (sg0 D A3.A) ρ) : ℚ) : ℝ)) * (RealDat.nP F.lv2 false)⁻¹ with hcdef
  have hc : 0 < c := mul_pos (Finset.prod_pos fun ρ _ => by exact_mod_cast GlobalTheory.Mem.EasyInputs.dimOK D j (sg0 D A3.A) ρ)
    (inv_pos.2 (RealDat.nP_pos false))
  have hSm := GlobalTheory.Mem.EasyInputs.smAll D (Wc D j) _ (R.MW j (sg0 D A3.A))
  have hex : ∀ x ∈ principalLevelFrame.Minf R.θ (Y.PW j) (R.MW j (sg0 D A3.A)), ∀ y ∈ principalLevelFrame.Minf R.θ (Y.PW j) (R.MW j (sg0 D A3.A)),
      ∃ b, Mult.IsMultIP (R.MW j (sg0 D A3.A)) (R.νW j) (R.fdW j) x y b := by
    intro x hx y hy
    obtain ⟨N, -, hx', hy'⟩ := GlobalTheory.FinTypesRows.exists_common (Y.PW j) hx hy
    exact hSA _ hSig _ R.θ _ _ _ _ _ hθ hHaar hFD x hx' y hy'
  let φ : D.what₂.Mj (j.1 + 1) →ₗ[ℂ] Mult.MMap (R.MW j (sg0 D A3.A)) :=
    (PiTensorProduct.lift : Mult.MMap (R.MW j (sg0 D A3.A)) ≃ₗ[ℂ] _).symm.toLinearMap ∘ₗ
      (Submodule.subtype ((toLiftReal R.toRealDat F.lv2 Y.tupT Y.hm Y.hTop Y.hinj).Wc j)) ∘ₗ (Y.IL.jMj j).toLinearMap
  have hφ : ∀ y, PiTensorProduct.lift (φ y) = (Y.IL.jMj j y).1 := by
    intro y
    exact LinearEquiv.apply_symm_apply _ _
  have hgood : ∀ y, φ y ∈ Mult.goodPart R.θ (R.MW j (sg0 D A3.A)) (levS _ (R.βW j) (R.datWp j (R.levL F.lv2 false (sg0 D A3.A))))
      (levChi _ (R.βW j) (R.datWp j (R.levL F.lv2 false (sg0 D A3.A)))) (R.eWf j (sg0 D A3.A)) := by
    intro y
    obtain ⟨a, ha, hay⟩ := (Y.IL.jMj j y).2
    have : φ y = a := by
      show PiTensorProduct.lift.symm (Y.IL.jMj j y).1 = a
      rw [← hay]
      exact LinearEquiv.symm_apply_apply _ _
    rw [this]
    exact ha
  have hmem : ∀ y, φ y ∈ principalLevelFrame.Minf R.θ (Y.PW j) (R.MW j (sg0 D A3.A)) := fun y =>
    principalLevelFrame.mult_le_Minf hLev (Mult.goodPart_le _ _ _ _ _ (hgood y))
  refine ⟨{ A := Mult.MMap (R.MW j (sg0 D A3.A))
            ρ := principalLevelFrame.actM (Y.PW j) (R.MW j (sg0 D A3.A))
            C := principalLevelFrame.Minf R.θ (Y.PW j) (R.MW j (sg0 D A3.A))
            B := fun x y => (c : ℂ) * Mult.ipM (R.MW j (sg0 D A3.A)) (R.νW j) (R.fdW j) x y
            lin := fun x hx y hy z hz c' => by
              rw [hlin x hx y hy z hz c']
              ring
            herm := fun x hx y hy => by
              rw [map_mul, Complex.conj_ofReal, ← hherm x hx y hy]
            pos := fun x hx hx0 => by
              rw [Complex.re_ofReal_mul]
              exact mul_pos hc (hpos x hx hx0)
            stab := fun h x hx => GlobalTheory.FinTypesRows.minf_stable (Y.PW j) hcc h hx
            inv := fun h x hx y hy => by
              rw [GlobalTheory.T.schur_pairing_invariant_under_standard_group D (Wc D j) _ R.θ (R.MW j (sg0 D A3.A)) D.R.r (Y.PW j) (R.νW j) (R.fdW j) hSA hSig hθ
                hHaar hFD h x hx y hy]
            smooth := fun x hx => GlobalTheory.FinTypesRows.minf_smooth (Y.PW j) hx
            adm := fun N hN => GlobalTheory.FinTypesRows.minf_adm (Y.PW j) hHA hSig hθ (GlobalTheory.FinTypesRows.levN_open (Y.PW j) hStd) N hN
            φ := φ
            φ_mem := hmem
            φ_inner := fun x y => by
              beta_reduce
              rw [hT.mj j x y]
              change (∏ τ, ((Mult.dimK _ _ (kapAt (Wc D j) (sg0 D A3.A) τ) : ℚ) : ℂ)) *
                Mult.ipM (R.MW j (sg0 D A3.A)) (ENNReal.ofReal (RealDat.nP F.lv2 false)⁻¹ • R.νW j) (R.fdW j) (φ x) (φ y) = _
              rw [GlobalTheory.RowModCanon.ipM_smul_measure _ hSm _ _ (inv_nonneg.2 (RealDat.nP_pos false).le) _ _
                (hex _ (hmem x) _ (hmem y)), hcdef]
              push_cast
              ring
            isot := fun σ y => by
              rw [hT.isot j σ y, Y.prtWE j σ]
              constructor
              · rintro ⟨a, ha, hay⟩
                have e : φ y = a := by
                  show PiTensorProduct.lift.symm (Y.IL.jMj j y).1 = a
                  rw [← hay]
                  exact LinearEquiv.symm_apply_apply _ _
                rw [e]
                exact (Submodule.mem_inf.1 ha).2
              · intro h
                exact ⟨φ y, Submodule.mem_inf.2 ⟨hgood y, h⟩, hφ y⟩ }, LinearMap.id, c, Function.injective_id, hc,
    Submodule.map_id _, fun h x => rfl, fun x _ y _ => rfl, fun y => hφ y⟩

end GlobalTheory.RefRowMod
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReferenceTupleFormsSmoothAdmissibleUnitaryModuleStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL GlobalTheory.SplitRead GlobalTheory.NPin

open GlobalTheory.RefPair


theorem _root_.GlobalTheory.T.referenceTuple_forms_smoothAdmissibleUnitaryModule : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : Formalism.L2.DIV.FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : Formalism.IndefR.Links.RealDat3 D A3 Ks) (F : Formalism.IndefR.Links.Face3 D A3) (cG : Formalism.L2.DIV.G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := A3) R.toRealDat F.lv2 X0), GlobalTheory.Mem.R3.Pins R F cG → GlobalTheory.Mem.R3.Holds R F → R.toRealDat.ExAt → ∀ (i : Fin D.R.m), ∃ X : GlobalTheory.NPin.RowMod D (GlobalTheory.RefTheta.repY Y) (i.1 + 1), GlobalTheory.RefTheta.IsCanonR Y i rfl X := by
  first | exact @GlobalTheory.RefRowMod.main | exact GlobalTheory.RefRowMod.main | (intros; apply GlobalTheory.RefRowMod.main <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReferenceTupleWeilDatumCharacters

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL GlobalTheory.SplitRead GlobalTheory.NPin

open GlobalTheory.RefPair

namespace GlobalTheory.RefTupleChars

theorem ref_chars : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : Formalism.L2.DIV.FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : Formalism.IndefR.Links.RealDat3 D A3 Ks) (F : Formalism.IndefR.Links.Face3 D A3) (cG : Formalism.L2.DIV.G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := A3) R.toRealDat F.lv2 X0), GlobalTheory.Mem.R3.Pins R F cG → GlobalTheory.Mem.R3.Holds R F → R.toRealDat.ExAt → ∀ (i : Fin D.R.m), Formalism.IndefR.Links.ChrEq (Formalism.IndefR.Lift.chrTh (R.toLevCh.mu (GlobalTheory.RefTheta.t0 Y)) R.eta (i.1 + 1)).1 (R.C.mu0 i) ∧ Formalism.IndefR.Links.ChrEq (Formalism.IndefR.Lift.chrTh (R.toLevCh.mu (GlobalTheory.RefTheta.t0 Y)) R.eta (i.1 + 1)).2 (R.C.mu0 i * R.C.eta⁻¹) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y hP _ hEx i
  have hlev := (GlobalTheory.CoreOfWeak.core_of_weak R F hP.char hEx).1.lev
  have ht : GlobalTheory.RefTheta.t0 Y = A3.A.μ0 := by
    show Y.tupT D.what₂.mu0 = A3.A.μ0
    rw [← Y.tup0, Y.tupT_tup]
  rw [ht]
  have hxC := hlev.xi A3.A.μ0
  rw [hlev.xi_base] at hxC
  have hxi : R.toLevCh.xi A3.A.μ0 = 1 := MonoidHom.ext fun x =>
    GlobalTheory.TwistFactorCompare.eq_one_of_chrEq_one hxC x
  have e : Formalism.IndefR.Lift.chrTh (R.toLevCh.mu A3.A.μ0) R.eta (i.1 + 1) =
      (R.toLevCh.mu0 (i.1 + 1), R.toLevCh.mu0 (i.1 + 1) * R.eta⁻¹) := by
    simp only [Formalism.IndefR.Lift.chrTh, Formalism.IndefR.Links.LevCh.mu, Formalism.IndefR.Lift.tup, hxi, mul_one]
  rw [e]
  have hm := hlev.mu0 i
  have h2 := GlobalTheory.ClassScalarValue.chrEq_mul_inv hm hxC hlev.eta
  rw [hxi, mul_one, mul_one] at h2
  exact ⟨hm, h2⟩

end GlobalTheory.RefTupleChars
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReferenceTupleWeilDatumCharactersStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL GlobalTheory.SplitRead GlobalTheory.NPin

open GlobalTheory.RefPair


theorem _root_.GlobalTheory.T.referenceTuple_weilDatum_characters : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : Formalism.L2.DIV.FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : Formalism.IndefR.Links.RealDat3 D A3 Ks) (F : Formalism.IndefR.Links.Face3 D A3) (cG : Formalism.L2.DIV.G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := A3) R.toRealDat F.lv2 X0), GlobalTheory.Mem.R3.Pins R F cG → GlobalTheory.Mem.R3.Holds R F → R.toRealDat.ExAt → ∀ (i : Fin D.R.m), Formalism.IndefR.Links.ChrEq (Formalism.IndefR.Lift.chrTh (R.toLevCh.mu (GlobalTheory.RefTheta.t0 Y)) R.eta (i.1 + 1)).1 (R.C.mu0 i) ∧ Formalism.IndefR.Links.ChrEq (Formalism.IndefR.Lift.chrTh (R.toLevCh.mu (GlobalTheory.RefTheta.t0 Y)) R.eta (i.1 + 1)).2 (R.C.mu0 i * R.C.eta⁻¹) := by
  first | exact @GlobalTheory.RefTupleChars.ref_chars | exact GlobalTheory.RefTupleChars.ref_chars | (intros; apply GlobalTheory.RefTupleChars.ref_chars <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRowThetaModule

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL GlobalTheory.SplitRead GlobalTheory.NPin

open GlobalTheory.RefPair


open GlobalTheory.RefTheta GlobalTheory.ThetaTri Formalism.IndefR.Datum Formalism.IndefR.Links in
theorem GlobalTheory.RefTheta.datum_real : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : Formalism.L2.DIV.FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : Formalism.IndefR.Links.RealDat3 D A3 Ks) (F : Formalism.IndefR.Links.Face3 D A3) (cG : Formalism.L2.DIV.G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := A3) R.toRealDat F.lv2 X0), GlobalTheory.Mem.R3.Pins R F cG → GlobalTheory.Mem.R3.Holds R F → R.toRealDat.ExAt → ∀ (M : MtFam D), GlobalTheory.HeightCounting.MtAd Y M → ∀ (i : Fin D.R.m), ∃ X : GlobalTheory.NPin.RowMod D (GlobalTheory.RefTheta.repY Y) (i.1 + 1), HasThetaAt D (M D.what₂.mu0 (i.1 + 1) (by omega) (by omega)) X (R.C.mu0 i) R.C.eta := by
  intro hHC hCR D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y hP hH hEx M Ad i
  have hC := (GlobalTheory.CoreOfWeak.core_of_weak R F hP.char hEx).1
  obtain ⟨X, hc⟩ := GlobalTheory.T.referenceTuple_forms_smoothAdmissibleUnitaryModule hHC hCR D G Pl0 I0 T A3 Ks R F cG X0 Y hP hH hEx i
  have hth : ∀ v, IsThetaFunO R.ψ (Vc D i) (Wc D i) (phi0 Y i v) := fun v => hC.thP.pt_theta i _ _
  have h0 : phi0 Y i ∈ Om Ad i hc := GlobalTheory.T.referenceTuple_thetaValued_map_mem_thetaData hHC hCR D G Pl0 I0 T A3 Ks R F cG X0 Y hP hH hEx M Ad i X hc _ hth
  refine ⟨X, Om Ad i hc, inferInstance, inferInstance, om Ad i hc, lamL Ad i hc, ⟨_, h0⟩, ?_, ?_, ?_⟩
  · intro h g φ Fm Fm' y y' hF hy
    exact GlobalTheory.T.trilinearThetaForm_referenceTuple_invariant D G Pl0 I0 T A3 Ks R F cG X0 Y hP hH hEx M Ad i X hc h g φ.1 φ.2 Fm Fm' y y' hF hy
  · intro x y Fm hF
    exact GlobalTheory.T.referenceTuple_datumForm_reads_thetaLift_innerProducts D G Pl0 I0 T A3 Ks R F cG X0 Y hP hH hEx M Ad i X hc x y Fm hF
  intro s μw ηw hμw hηw
  obtain ⟨h1, h2⟩ := GlobalTheory.T.referenceTuple_weilDatum_characters D G Pl0 I0 T A3 Ks R F cG X0 Y hP hH hEx i
  have hv : ∀ v, phi0 Y i v ∈ ⨆ (ι : GlobalTheory.SplitWeil.SB (Matrix (Fin D.R.nV) (Fin D.R.r)
      (s.w.adicCompletion D.host.E)) →ₗ[ℂ] (WO (Vc D i) (Wc D i) → ℂ))
      (_ : GlobalTheory.NPin.IsLinAt (omStd Ad i (t0 Y)) s μw ηw ι ∧ ∀ Φ, IsThetaFunO R.ψ (Vc D i) (Wc D i) (ι Φ)),
      LinearMap.range ι := fun v =>
    GlobalTheory.T.thetaFunctions_spanned_heckeTwisted_standardFrame D R.ψ (Vc D i) (Wc D i) D.R.nV D.R.r (Ad.PV i) (Y.PW i) Y.hF
      (Ad.std i) (Y.stdPsi.2 i) _ _ (R.ωP i (t0 Y)) (hC.thP.ωP i _) _ _ h1 h2 s μw ηw hμw hηw _ (hth v)
  have hlin := mem_iSup_isLinAt_lin' (omStd Ad i (t0 Y)) (IsThetaFunO R.ψ (Vc D i) (Wc D i)) (· ∈ Om Ad i hc)
    (fun β f hf => GlobalTheory.T.referenceTuple_thetaValued_map_mem_thetaData hHC hCR D G Pl0 I0 T A3 Ks R F cG X0 Y hP hH hEx M Ad i X hc _ fun v => by
      simpa [single1] using Formalism.IndefR.Fock.CCR.theta_smul hf (β v))
    s μw ηw _ hv
  exact mem_iSup_isLinAt_omSub _ _ _ _ _ _ _ _ _ s μw ηw h0 hlin
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaLiftOfReference

section

@[expose] public section



section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL GlobalTheory.SplitRead GlobalTheory.NPin
open GlobalTheory.RefPair
theorem GlobalTheory.RefTheta.locComp_of_isRc_classMapD_cenLoc : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.LiftRef.ForallRowSideParameters hL fun D cf rep _ _ M => ∀ (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m), ∃ X : RowMod D rep j, HasThetaAt D (M D.what₂.mu0 j h1 h2) X (cf.mu0 ⟨j - 1, by omega⟩) cf.eta := by
  intro hN hL
  unfold _root_.GlobalTheory.LiftRef.ForallRowSideParameters OverRows
  refine GlobalTheory.HeightCounting.JumpsAt.evLgG_of_forall fun K B f T _ w _ Z Wt hX z p0 Y hH hEx _ _ _ Rw a M tup Q hMA _ j h1 h2 => ?_
  obtain ⟨i, rfl⟩ : ∃ i : Fin (w.st Z).toD7.R.m, j = (i : ℕ) + 1 := ⟨⟨j - 1, by omega⟩, by simp only; omega⟩
  have hC : z.R.C = TC.cf w.I w.l Z := z.lev.C
  obtain ⟨X, hX⟩ := GlobalTheory.RefTheta.datum_real hN.hc hN.decay _ _ _ _ _ _ _ z.R z.F z.cG p0 Y z.pins hH hEx M hMA i
  refine ⟨X, ?_⟩
  rw [← hC]
  exact hX
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL GlobalTheory.SplitRead GlobalTheory.NPin
open GlobalTheory.RefPair

theorem _root_.GlobalTheory.T.exists_theta_at_of_third_layer : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.LiftRef.ForallRowSideParameters hL fun D cf rep _ _ M => ∀ (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m), ∃ X : RowMod D rep j, HasThetaAt D (M D.what₂.mu0 j h1 h2) X (cf.mu0 ⟨j - 1, by omega⟩) cf.eta := by
  first | exact @_root_.GlobalTheory.RefTheta.locComp_of_isRc_classMapD_cenLoc | exact _root_.GlobalTheory.RefTheta.locComp_of_isRc_classMapD_cenLoc | (intros; apply _root_.GlobalTheory.RefTheta.locComp_of_isRc_classMapD_cenLoc <;> assumption)
end
end
end
end
