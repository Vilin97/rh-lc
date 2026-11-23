module

public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSmoothAutomorphicRightTranslateFinite
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelGroupActionIsAction
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
import Mathlib.Topology.Sheaves.Init
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.StepVecThetaLem
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChainStepVectorsAndAdjointVectorsAreTheta
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EasyInputs
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.TwoSplitIdem
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockPolynomialVectorsOfSmoothThetaStable
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GramMapMulInv
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HcFiniteAndSchurMult
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevOKAll
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepVecExists
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.VacuumOrientedExists
public import Formalism.LocalToGlobal.IndefiniteReal.WeilFull
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDatumFixesLatticeVacuaAtInertPlaces
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDatumRealDerivativeFockVectorsAll
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.GinfCSecondCountable
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.MeasLev

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPrincipalLevelMultiplicityFiniteGroupImage

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MultAction

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S)
  (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)

abbrev MultP : Submodule ℂ (MMap M) := Mult θ M (levS V β (flag1L L)) (levChi V β (flag1L L))

variable {θ M β L}

theorem hasType {U : MMap M} (hU : U ∈ MultP θ M β L) (v : M.Vec) : HasType V β (flag1L L) (U v) :=
  fun κ hκ y => ((GlobalTheory.MultMem.mem_mult_iff D θ V S M _ _ U).1 hU).lev v κ hκ y

theorem isMultMap_translate {J : Set (GA D V)} {χ : GA D V → ℂ} {T : MMap M} (h : IsMultMap θ M J χ T) {k : GA D V}
    (hk : k ∈ GfC V) : IsMultMap θ M ∅ χ (heckeOn M {k} T) := by
  have e : ∀ v, heckeOn M {k} T v = rTr V k (T v) := fun v => by
    funext g
    simp [heckeOn, postOn_apply, heckeLin_apply, rTr]
  refine ⟨fun v => ?_, fun v => ?_, fun v k hk => hk.elim, fun τ g hg v w hw => ?_, fun τ v x => ?_⟩
  · rw [e]
    exact GlobalTheory.FinTranslate.isAutFunSm_rTr θ V k hk _ (h.aut v)
  · rw [e]
    intro r C hC μ 𝓕 hμ h𝓕 g
    simp only [rTr, mul_assoc]
    exact h.cusp v r C hC μ 𝓕 hμ h𝓕 (g * k)
  · rw [e, e, h.equiv τ g hg v w hw]
    funext x
    unfold rTr
    rw [mul_assoc, mul_assoc, GlobalTheory.FinTranslate.comm_fin_real V hk (GlobalTheory.FinTranslate.atTau_mem θ V τ g)]
  · obtain ⟨ℓ, s, e'⟩ := h.cont τ v (x * k)
    exact ⟨ℓ, s, fun w => by rw [e, e']; rfl⟩

theorem exists_principalLevelMultiplicity_finiteGroup_image (g0 : G0 L.Pg L.r) (T : MMap M) (hT : T ∈ MultP θ M β L) :
    ∃ T' ∈ MultP θ M β L, ∀ v, T' v = actG0 V β L g0 (T v) := by
  by_cases hk : ∃ κ, IsLevelLift V β L g0 κ
  · have hκ := hk.choose_spec
    rw [GlobalTheory.MultMem.mem_mult_iff] at hT
    have hact : ∀ v, ((levChi V β (flagL L) hk.choose)⁻¹ • heckeOn M {hk.choose} T) v =
        actG0 V β L g0 (T v) := by
      intro v
      unfold actG0
      rw [dite_eq_left hk]
      funext g
      simp [heckeOn, postOn_apply, heckeLin_apply]
    have h0 : IsMultMap θ M ∅ (levChi V β (flag1L L))
        ((levChi V β (flagL L) hk.choose)⁻¹ • heckeOn M {hk.choose} T) := by
      rw [← GlobalTheory.MultMem.mem_mult_iff]
      exact Submodule.smul_mem _ _
        ((GlobalTheory.MultMem.mem_mult_iff ..).2 (isMultMap_translate hT hκ.1))
    refine ⟨_, Submodule.subset_span ⟨h0.aut, h0.cusp, fun v k hk' g => ?_, h0.equiv, h0.cont⟩, hact⟩
    rw [hact]
    exact GlobalTheory.FlagAction.act_hasType (fun k hk => hT.lev v k hk) hk k hk' g
  · refine ⟨0, Submodule.zero_mem _, fun v => ?_⟩
    unfold actG0
    rw [dite_eq_right hk]
    rfl

theorem act_mem (g : G0 L.Pg L.r) {U : MMap M} (hU : U ∈ MultP θ M β L) : postOn M (actL V β L g) U ∈ MultP θ M β L := by
  obtain ⟨U', h1, h2⟩ := exists_principalLevelMultiplicity_finiteGroup_image g U hU
  have h : postOn M (actL V β L g) U = U' := MultilinearMap.ext fun v => (h2 v).symm
  rw [h]
  exact h1

theorem act_one {U : MMap M} (hU : U ∈ MultP θ M β L) : postOn M (actL V β L 1) U = U :=
  MultilinearMap.ext fun v => GlobalTheory.FlagAction.act_one (hasType hU v)

theorem act_mul (hl : LiftsExist V β L) (g g' : G0 L.Pg L.r) {U : MMap M} (hU : U ∈ MultP θ M β L) :
    postOn M (actL V β L (g * g')) U = postOn M (actL V β L g) (postOn M (actL V β L g') U) :=
  MultilinearMap.ext fun v => GlobalTheory.FlagAction.act_mul (hasType hU v) (hl g) (hl g')

variable {G : Type} [Group G] [Fintype G] (eG : G ≃* G0 L.Pg L.r)

theorem postOn_gaL (c : G → ℂ) (U : MMap M) :
    postOn M (gaL V β L eG c) U = ∑ g, c g • postOn M (actL V β L (eG g)) U := by
  refine MultilinearMap.ext fun v => ?_
  simp only [gaL, postOn, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.compMultilinearMap_apply,
    LinearMap.sum_apply, LinearMap.smul_apply, MultilinearMap.sum_apply, MultilinearMap.smul_apply]

theorem gaL_act (hl : LiftsExist V β L) {c : G → ℂ} (hc : ∀ g a, c (g * a * g⁻¹) = c a) (g : G) {U : MMap M}
    (hU : U ∈ MultP θ M β L) :
    postOn M (gaL V β L eG c) (postOn M (actL V β L (eG g)) U) =
      postOn M (actL V β L (eG g)) (postOn M (gaL V β L eG c) U) := by
  have hm : ∀ a b : G, postOn M (actL V β L (eG a)) (postOn M (actL V β L (eG b)) U) =
      postOn M (actL V β L (eG (a * b))) U := fun a b => by
    rw [map_mul]
    exact (act_mul hl _ _ hU).symm

  rw [postOn_gaL, postOn_gaL, map_sum]
  simp only [map_smul, hm]
  refine (Fintype.sum_equiv (MulAut.conj g).toEquiv _ _ fun a => ?_).symm
  show _ = c (g * a * g⁻¹) • postOn M (actL V β L (eG (g * a * g⁻¹ * g))) U
  rw [hc, inv_mul_cancel_right]


end GlobalTheory.MultAction

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ActRep

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Lev
open scoped TensorProduct InnerProductSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MultAction

theorem actRep : ∀ D : D7, ActRep D := by
  intro D V β L S θ M hl hP
  have e : Formalism.IndefR.Lev.flag1L L = L := by
    rw [flag1L, withP, ← hP]
  have hM : Mult θ M (levS V β L) (levChi V β L) = MultP θ M β L := by
    rw [MultP, e]
  rw [hM]
  refine ⟨fun g T hT => act_mem g hT, fun T hT => act_one hT, fun g h T hT => act_mul hl g h hT, ?_⟩
  intro G _ _ eG c hc g T hT
  have h := gaL_act eG hl (c := c) (fun a b => hc a b) (eG.symm g) hT
  rwa [MulEquiv.apply_symm_apply] at h

end GlobalTheory.MultAction

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChainStepVectorsAndAdjointVectorsAreThetaStatement

section

@[expose] public section

open Formalism.BasicNotions

theorem _root_.GlobalTheory.T.chainStepVectors_and_adjointVectors_areTheta : ∀ D : D7, Formalism.IndefR.Fin.VecThetaSD D := by
  first | exact @GlobalTheory.VecTheta.vecThetaSD | exact GlobalTheory.VecTheta.vecThetaSD | (intros; apply GlobalTheory.VecTheta.vecThetaSD <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockPolynomialVectorsOfSmoothThetaStableStatement

section

@[expose] public section

open Formalism.BasicNotions

theorem _root_.GlobalTheory.T.fockPolynomialVectors_of_smoothTheta_stable : ∀ D : D7, Formalism.IndefR.Fin.PtStable D := by
  first | exact @GlobalTheory.FockTheta.ptStable | exact GlobalTheory.FockTheta.ptStable | (intros; apply GlobalTheory.FockTheta.ptStable <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDatumFixesLatticeVacuaAtInertPlacesStatement

section

@[expose] public section

open Formalism.BasicNotions

theorem _root_.GlobalTheory.T.weil_datum_fixes_lattice_vacua_at_inert_places : ∀ D : D7, Formalism.IndefR.WeilFull.InertAllO D := by
  first | exact @GlobalTheory.InertAll.inertAllO | exact GlobalTheory.InertAll.inertAllO | (intros; apply GlobalTheory.InertAll.inertAllO <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDatumRealDerivativeFockVectorsAllStatement

section

@[expose] public section

open Formalism.BasicNotions

theorem _root_.GlobalTheory.T.weilDatum_realDerivative_fockVectors_all : ∀ D : D7, Formalism.IndefR.WeilFull.RealAllO D := by
  first | exact @GlobalTheory.WeilReal.realAllO | exact GlobalTheory.WeilReal.realAllO | (intros; apply GlobalTheory.WeilReal.realAllO <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinksAnalyticHypothesesOfWeilRepHarishChandra

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LinksInputs

theorem inputs_of_hypotheses : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists →
    GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, Inputs D := by
  intro hW _ hH hC D
  obtain ⟨hcart, hsd, hsp, hdim, hpet, hsm⟩ := GlobalTheory.Mem.EasyInputs.easy_inputs D
  exact
    { weil := Formalism.IndefR.WeilFull.weilExistsFull_of (hW D) (GlobalTheory.T.weil_datum_fixes_lattice_vacua_at_inert_places D) (GlobalTheory.T.weilDatum_realDerivative_fockVectors_all D)
      vac := GlobalTheory.Member.vacuum_oriented_exists D
      stepVec := GlobalTheory.PlaceDatum.stepVecExists D
      thPVec := GlobalTheory.PlaceVec.thPVecExists D
      ptStable := GlobalTheory.T.fockPolynomialVectors_of_smoothTheta_stable D
      cartan := hcart
      selfDual := hsd
      vecTheta := GlobalTheory.T.chainStepVectors_and_adjointVectors_areTheta D
      measFD := Formalism.IndefR.Eqv.measFDExists_holds D
      measDef := Formalism.IndefR.Eqv.measLevDefExists_holds D
      fund := Formalism.IndefR.Eqv.fundDomExists_holds D
      sp := hsp
      lev := GlobalTheory.Mem.LevelOK.levOK_all D
      hc := fun V _ S θ M J χ => (GlobalTheory.MultFinite.hcFinite_and_schurMult hH hC D θ V S M J χ 0 ∅).1
      schur := fun V _ S θ M J χ μ 𝓕 => (GlobalTheory.MultFinite.hcFinite_and_schurMult hH hC D θ V S M J χ μ 𝓕).2
      pet := hpet
      sm := hsm
      dim := hdim
      act := GlobalTheory.MultAction.actRep D }

end GlobalTheory.LinksInputs

end
end
end
