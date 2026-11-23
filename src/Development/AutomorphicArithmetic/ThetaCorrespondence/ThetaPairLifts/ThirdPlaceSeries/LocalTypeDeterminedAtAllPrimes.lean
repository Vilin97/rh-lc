module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HtCard
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.StepJumpDirect
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InjPrimeTo
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PublishedInputsThirdLayer
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaDataExists
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AtMemberImp
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CompatibleSystemSatisfiesLocalProperty
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.InePolEqWdAtStatement
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoeffRingsHaveRootsOfUnity
import Formalism.LocalToGlobal.Divisibility.PsiWeilOfAbsNorm
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EtaJUntw
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotBaseCondFalse
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionOfIntro
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FunKilled
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallySizesCongruencesHostFactsColumnChoices
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsBisSide
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsTerSide
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.JumpsCardOfBuilt
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftSplitsLocally
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SClose
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TiedConditionOfLayer
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ZlStableAtStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SpecializationAtMemberOfLayer

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CardGLResidueTypePrimeDvdCardTypeGroup

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

namespace GlobalTheory.ZetaSer

theorem coeffRings_contain_rootsOfUnity_of_groupOrder (D : D7) (h : RootsLL D) : GlobalTheory.PendOf.CoeffRingsHaveRootsOfUnity D := by
  obtain ⟨ζ, hζ⟩ := h
  intro i
  have hpos := D.what₂.restRowsFiniteGroupCard_pos
  have hz : IsPrimitiveRoot (D.nd.embK i ζ) D.what₂.restRowsFiniteGroupCard := hζ.map_of_injective (D.nd.embK i).injective
  have hint : IsIntegral (D.nd.O i) (D.nd.embK i ζ) := ⟨Polynomial.X ^ D.what₂.restRowsFiniteGroupCard - Polynomial.C 1,
    Polynomial.monic_X_pow_sub_C 1 hpos.ne', by simp [hz.pow_eq_one]⟩
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  refine ⟨y, ?_⟩
  rw [← hy] at hz
  exact hz.of_map_of_injective (IsFractionRing.injective _ _)

theorem trace_mem_fieldRange {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {L : Type} [Field L] (e : L →+* ℂ) {n : ℕ} (hn : 0 < n) {ζ : L} (hζ : IsPrimitiveRoot ζ n)
    (f : Module.End ℂ V) (hf : f ^ n = 1) : LinearMap.trace ℂ V f ∈ e.fieldRange := by
  classical
  let b := Module.finBasis ℂ V
  rw [LinearMap.trace_eq_matrix_trace ℂ b, Matrix.trace_eq_sum_roots_charpoly]
  refine multiset_sum_mem _ fun μ hμ => ?_
  have hroot : (LinearMap.charpoly f).IsRoot μ := by
    rw [← LinearMap.charpoly_toMatrix f b]
    exact (Polynomial.mem_roots'.mp hμ).2
  obtain ⟨v, hv⟩ := ((Module.End.hasEigenvalue_iff_isRoot_charpoly f μ).2 hroot).exists_hasEigenvector
  have hpow : μ ^ n = 1 := by
    have h1 := hv.pow_apply n
    rw [hf, Module.End.one_apply] at h1
    have h2 : (μ ^ n - 1) • v = 0 := by rw [sub_smul, one_smul, ← h1, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h2).resolve_right hv.2)
  have hζc := hζ.map_of_injective e.injective
  haveI : NeZero n := ⟨hn.ne'⟩
  obtain ⟨j, -, hj⟩ := hζc.eq_pow_of_pow_eq_one hpow
  exact ⟨ζ ^ j, by rw [map_pow, hj]⟩

end GlobalTheory.ZetaSer

namespace GlobalTheory.ZetaSer

theorem card_GL_residue_typePrime_dvd_card_typeGroup (D : D7) (k : Fin 2) :
    Nat.card (GL (Fin D.R.r) (ZMod (D.host.g k))) ∣ D.what₂.restRowsFiniteGroupCard := by
  rw [D.nd.restN_card_levelGroup_eq]
  have hf : D.R.f ≠ 0 := by
    unfold Formalism.BasicNotions.Ranks.f Formalism.BasicNotions.Ranks.n
    have := Nat.one_le_two_pow (n := D.R.e)
    have := D.R.ord_pos
    omega
  exact (dvd_pow_self _ hf).trans (Finset.dvd_prod_of_mem _ (Finset.mem_univ k))

theorem coeff_zIdem_mem {Γ : Type} [Group Γ] [Fintype Γ] {L : Type} [Field L] (e : L →+* ℂ) {n : ℕ} (hn : 0 < n)
    {ζ : L} (hζ : IsPrimitiveRoot ζ n) (hΓ : Nat.card Γ ∣ n) (τ : FDRep ℂ Γ) (γ : Γ) :
    (Formalism.IrreducibleCountingLemmas.TYPES.zIdem τ).coeff γ ∈ e.fieldRange := by
  rw [Formalism.IrreducibleCountingLemmas.TYPES.zIdem_coeff]
  refine mul_mem (div_mem (natCast_mem _ _) (natCast_mem _ _)) (trace_mem_fieldRange e hn hζ _ ?_)
  obtain ⟨c, hc⟩ := hΓ
  rw [← map_pow, hc, pow_mul, pow_card_eq_one', one_pow, map_one]

theorem serLL_of_rootsLL (D : D7) (h : RootsLL D) (G : GrpSide D) : GlobalTheory.PendOf.SerLL D := by
  obtain ⟨ζ, hζ⟩ := h
  intro k f γ
  apply RingHom.mem_fieldRange.mp
  rw [G.eSer_def k f]
  unfold eSerO
  refine finsum_induction (fun x : MonoidAlgebra ℂ (GL (Fin D.R.r) (ZMod (D.host.g k))) => x.coeff γ ∈ D.what₂.embLL.fieldRange) ?_ ?_ fun z => ?_
  · simp
  · intro x y hx hy
    simpa using add_mem hx hy
  · refine finsum_induction (fun x : MonoidAlgebra ℂ (GL (Fin D.R.r) (ZMod (D.host.g k))) => x.coeff γ ∈ D.what₂.embLL.fieldRange) ?_ ?_ fun hz => ?_
    · simp
    · intro x y hx hy
      simpa using add_mem hx hy
    · obtain ⟨τ, -, rfl, -⟩ := hz
      exact coeff_zIdem_mem _ D.what₂.restRowsFiniteGroupCard_pos hζ (card_GL_residue_typePrime_dvd_card_typeGroup D k) τ γ

theorem rootsOfUnity_and_seriesIdempotent_rational : ∀ D : D7, RootsLL D → GlobalTheory.PendOf.CoeffRingsHaveRootsOfUnity D ∧ (GrpSide D → GlobalTheory.PendOf.SerLL D) :=
  fun D h => ⟨coeffRings_contain_rootsOfUnity_of_groupOrder D h, serLL_of_rootsLL D h⟩

end GlobalTheory.ZetaSer
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AtMemAnd

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
noncomputable section
namespace GlobalTheory.HeightCounting.Up.PendLayer
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists}
theorem atMem_mono {p q : _root_.GlobalTheory.HeightCounting.Up.LayPAlt hL} (h : _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL p)
    (hpq : ∀ K B f T w Z Wt p0 t nch n c, p K B f T w Z Wt p0 t nch n c → q K B f T w Z Wt p0 t nch n c) : _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL q :=
  EvG.imp h fun _ _ _ _ _ hK => large₂.imp hK fun B f T _ H kp w Z Wt p0 t nch n xd c a b d =>
    hpq _ B f T w Z Wt p0 t nch n c (H kp w Z Wt p0 t nch n xd c a b d)
theorem atMem_and' {p q : _root_.GlobalTheory.HeightCounting.Up.LayPAlt hL} (h : _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL p) (h' : _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL q) :
    _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun K B f T w Z Wt p0 t nch n c => p K B f T w Z Wt p0 t nch n c ∧ q K B f T w Z Wt p0 t nch n c :=
  EvG.imp (EvG.inter h h') fun _ _ _ _ _ hK => large₂.imp (large₂.inter hK.1 hK.2) fun _ _ _ _ H kp w Z Wt p0 t nch n xd c a b d =>
    ⟨H.1 kp w Z Wt p0 t nch n xd c a b d, H.2 kp w Z Wt p0 t nch n xd c a b d⟩
theorem atMem_mono_of_colPin {q : ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), w.Lt → Prop}
    (h : EvLgG fun K B f _ => KPx B f → ∀ (T : TwDat B) (w : ColW B f T) (Z : w.Lt), q B f T w Z) :
    _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ B f T w Z _ _ _ _ _ _ => q B f T w Z :=
  EvG.imp h fun _ _ _ _ _ hK => large₂.imp hK fun _ _ T _ H kp w Z _ _ _ _ _ _ _ _ _ _ => H kp T w Z
end GlobalTheory.HeightCounting.Up.PendLayer
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PendingLayerConditionAtMember

section

@[expose] public section



section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
noncomputable section
namespace GlobalTheory.HeightCounting.Up.PendLayer
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists}
theorem tieChi_of_labAll_green_chi_cen (hP : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt) (hS : GlobalTheory.Published.DepthZeroSupport) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D)
    (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (hX : GlobalTheory.NJoin.Agree X P.M P.rep) (hJ : JumpsCard D.nd D.naut)
    (hlab : GlobalTheory.PendOf.LabAll D P.T) (hgreen : GlobalTheory.PendOf.GreenLab P.ty.grp) (hchi : ChiTOk D P.cf)
    (hcen : CenLoc D P.M) (hzl : GlobalTheory.PendOf.ZLStable D) (hci : GlobalTheory.PendOf.CenInt D) (hroots : RootsLL D) :
    PairedCharacterCondition.tieChi (D := D) ∧ ∃ Q : PairedCharacterCondition.Pend D, PairedCharacterCondition.admDZ Q ∧ GlobalTheory.Pass.EigSpan Q := by
  have hrow : ∀ i : D.nd.Loc, Nonempty (GlobalTheory.NPin.RowMod D P.rep (D.nd.j i)) := by
    intro i
    have h1 := (D.nd.j_range i).1
    have h2 := (D.nd.j_range i).2
    obtain ⟨Y, -⟩ := _root_.GlobalTheory.RowModCanon.main_alt_alt hP.hc hP.decay hL D P X hX ⟨D.nd.j i - 1, by omega⟩ (D.nd.j i) (by simp; omega)
    exact ⟨Y⟩
  have hA := _root_.UpperTheory.GalS.a_close_main hP.what₂ hL D P hJ
  have hZ := GlobalTheory.ZetaSer.rootsOfUnity_and_seriesIdempotent_rational D hroots
  exact ⟨_root_.GlobalTheory.TieChiPin.locComp_of_isRc_classMapD_cenLoc hP.what₂ hL D P hrow hlab hchi,
    _root_.GlobalTheory.PinClose.locComp_of_isRc_classMapD_cenLoc hP.what₂ hS hL D P hrow hlab hcen hgreen hchi hA.tie0 hA.a5 hzl hci (hZ.2 P.ty.grp) hZ.1⟩
theorem locComp_of_isRc_classMapD_cenLoc : HtCard → _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → GlobalTheory.Published.DepthZeroSupport → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists,
    _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t nch n c => PairedCharacterCondition.tieChi (D := w.D Z) ∧ ∃ Q : PairedCharacterCondition.Pend (w.D Z), PairedCharacterCondition.admDZ Q ∧ GlobalTheory.Pass.EigSpan Q := by
  intro hH hP hS hL
  have h1 := _root_.GlobalTheory.HeightCounting.Up.PendLayer.atMem_and' (_root_.GlobalTheory.T.cenLoc_zlStable_cenInt_at_members hL) (_root_.GlobalTheory.HeightCounting.Up.PendLayer.atMem_and' (_root_.GlobalTheory.HeightCounting.JumpsAt.jumpsCard_at_members_of_htCard hH hL)
    (_root_.GlobalTheory.HeightCounting.Up.PendLayer.atMem_and' (_root_.GlobalTheory.HeightCounting.Up.isTied_of_layer_member_alt hP hL) (_root_.GlobalTheory.HeightCounting.Up.PendLayer.atMem_mono_of_colPin (hL := hL) GlobalTheory.HeightCounting.Up.sizes_host_at_record)))
  refine _root_.GlobalTheory.HeightCounting.Up.PendLayer.atMem_mono h1 fun K B f T w Z Wt p0 t nch n c h => ?_
  obtain ⟨⟨hcen, hzl, hci⟩, hJ, ⟨X, hpin, -⟩, -, -, hroots, -⟩ := h
  have hM : X.P.M = c.a.all.gal.mt := hpin.M_eq
  exact _root_.GlobalTheory.HeightCounting.Up.PendLayer.tieChi_of_labAll_green_chi_cen hP hS (w.D Z) X.P X.X X.agree hJ hpin.lab hpin.green hpin.chiT (hM ▸ hcen) hzl hci hroots
end GlobalTheory.HeightCounting.Up.PendLayer
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

theorem _root_.GlobalTheory.T.tieChi_at_mem_of_depth_zero_inputs : (HtCard → _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → GlobalTheory.Published.DepthZeroSupport → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t nch n c => PairedCharacterCondition.tieChi (D := w.D Z) ∧ ∃ Q : PairedCharacterCondition.Pend (w.D Z), PairedCharacterCondition.admDZ Q ∧ GlobalTheory.Pass.EigSpan Q) := by
  first | exact @_root_.GlobalTheory.HeightCounting.Up.PendLayer.locComp_of_isRc_classMapD_cenLoc | exact _root_.GlobalTheory.HeightCounting.Up.PendLayer.locComp_of_isRc_classMapD_cenLoc | (intros; apply _root_.GlobalTheory.HeightCounting.Up.PendLayer.locComp_of_isRc_classMapD_cenLoc <;> assumption)
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocalTypeDeterminedAtAllPrimes

section

@[expose] public section



section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
namespace GlobalTheory.TypePrimesFinished
theorem locComp_of_isRc_classMapD_cenLoc : GlobalTheory.HeightCounting.HtCard → _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → GlobalTheory.Published.DepthZeroSupport → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ _ _ _ _ => (PairedCharacterCondition.tieChi (D := w.D Z) ∧ (∃ Q : PairedCharacterCondition.Pend (w.D Z), PairedCharacterCondition.admDZ Q ∧ GlobalTheory.Pass.EigSpan Q) ∧ GlobalTheory.Pass.TieInePoly (w.D Z) ∧ GlobalTheory.TypeLeaf.SerLoc (w.D Z)) := by
  intro hC hP hS hL
  refine _root_.GlobalTheory.HeightCounting.Up.Model.AtMem.at_member_imp
    (_root_.GlobalTheory.HeightCounting.Up.Model.AtMem.and_z (_root_.GlobalTheory.T.tieChi_at_mem_of_depth_zero_inputs hC hP hS hL)
      (_root_.GlobalTheory.HeightCounting.Up.Model.AtMem.and_z (_root_.GlobalTheory.T.exists_character_choice_pin_at_of_third_layer hP hL) (_root_.GlobalTheory.T.serLoc_at_member_of_published_inputs hP hL))) ?_
  intro K B f T w Z Wt p0 t nch n c h
  obtain ⟨⟨h1, h2⟩, ⟨P, _⟩, h4⟩ := h
  exact ⟨h1, h2, _root_.GlobalTheory.T.tieInePoly_of_characterChoice hL (w.D Z) P, h4⟩
end GlobalTheory.TypePrimesFinished
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

theorem _root_.GlobalTheory.T.tieChi_at_members_of_depthZero : GlobalTheory.HeightCounting.HtCard → _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → GlobalTheory.Published.DepthZeroSupport → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ _ _ _ _ => (PairedCharacterCondition.tieChi (D := w.D Z) ∧ (∃ Q : PairedCharacterCondition.Pend (w.D Z), PairedCharacterCondition.admDZ Q ∧ GlobalTheory.Pass.EigSpan Q) ∧ GlobalTheory.Pass.TieInePoly (w.D Z) ∧ GlobalTheory.TypeLeaf.SerLoc (w.D Z)) := by
  first | exact @_root_.GlobalTheory.TypePrimesFinished.locComp_of_isRc_classMapD_cenLoc | exact _root_.GlobalTheory.TypePrimesFinished.locComp_of_isRc_classMapD_cenLoc | (intros; apply _root_.GlobalTheory.TypePrimesFinished.locComp_of_isRc_classMapD_cenLoc <;> assumption)
end
end
end
end
