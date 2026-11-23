module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.FullExists
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LocalAdditiveCharContinuous
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LocUnram
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.ConcreteLevelAdelicSubset
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.DoubleCosetSingleUnfolding
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RowsConc
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.RightInvOfLattice
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NilradicalLatticeZMemSpan
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RCocompactPfFinal
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SlabCountPfFinal
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SlabFinal
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SlabMajPtPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.UnipotentInLevelSubgroup
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FixedDecomposition
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.SchurCoreA
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ClmEqZeroOfSpan
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CplxNF
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LeviTens
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.SubOneMulVecFix
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.NormAdditiveCharacterTypePrimeEqOne
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.TypedLoc
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.FinLevi
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.LocDualGen
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.LocHaarRR
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.PinHostLoc
public import Formalism.PeriodIntegrals.LocHaarRR

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.FullTied

section

@[expose] public section

noncomputable section

open scoped Classical TensorProduct
open Matrix
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.L2.SG.TermOp Formalism.L2.SG.Full

namespace Formalism.L2.SG.Pf.FullLocalDualAgreement

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def LocalDualAgreement : Prop :=
  ∀ D : D7, Formalism.L2.SG.Pf.LocCP.LocTied D → ∃ (δ : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, (D.s.atP p).Fp)
    (M : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, Formalism.MainNotions.S.Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Formalism.MainNotions.S.LocalSplitGroups.Agree δ M p) ∧
    ∀ (p : Formalism.MainNotions.S.LocalSplitGroups.PlF D) (i : Fin 2), ((D.host.g i : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal →
      δ p = (D.s.atP p).ιF (((D.host.g 0 : ℕ) : D.host.F) * ((D.host.g 1 : ℕ) : D.host.F) /
        ((D.host.g i : ℕ) : D.host.F))

theorem locCTied_of (h1 : Formalism.L2.SG.Pf.LocCP.LocDualC) (h2 : Formalism.L2.SG.Pf.LocCP.LocUnramC)
    (h4 : Formalism.L2.SG.Pf.LocCP.LocHaarC) : LocalDualAgreement := fun D hT => by
  obtain ⟨δ, M, hA, hpin⟩ := Formalism.L2.SG.Pf.LocCP.locBody_of D hT h1 h2 Formalism.L2.SG.Pf.LocCP.locPsiContC h4
  exact ⟨δ, M, hA, fun p i hi => hpin p i hi⟩

theorem locCTied_of' (h1 : Formalism.L2.SG.Pf.LocCP.LocDualC) (h4 : Formalism.L2.SG.Pf.LocCP.LocHaarC) : LocalDualAgreement :=
  locCTied_of h1 Formalism.L2.SG.Pf.LocUnramP.locUnramC h4

theorem locDualC_of' (hG : Formalism.L2.SG.Pf.LocCP.LocDualGenC) (hP : Formalism.L2.SG.Pf.LocCP.PinHostC) :
    Formalism.L2.SG.Pf.LocCP.LocDualC :=
  Formalism.L2.SG.Pf.LocCP.locDualC_of hG Formalism.L2.SG.Pf.LocUnramP.locUnramC hP

end Formalism.L2.SG.Pf.FullLocalDualAgreement

namespace Formalism.L2.SG.Pf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem fullExists_tied (h1 : TRExistsC) (hR : LatticeRowBijectionClassFinite) (hL : FullLocalDualAgreement.LocalDualAgreement) :
    ∀ (D : D7) (X : HidaSetting D), X.LevelSubgroupCharacter → Formalism.L2.SG.Pf.LocCP.LocTied D → Nonempty (Full X) := by
  intro D X hK hT
  have hRS : RowStepsC := rowStepsC_of (fun D X hK u =>
    let ⟨a2, a3, a4, a5⟩ := hR D X hK u
    ⟨latSub X u, latRow_of X u a2, a3, a4, classFin_of X u hK a5, gamIsom_of X (inclInj_holds X) u⟩)
  obtain ⟨TR, hTR⟩ := h1 D X hK
  have h2 : ∀ u : D.what₂.Word, ∃ what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V), IsRowReps D (X.Fu u) what₂ ∧
      (∀ Λ ∈ what₂, Formalism.L2.SG.Saturated.IsSplitRow D (X.Fu u) Λ) ∧ ∃ cs : ColSys X u what₂, ColReps hK cs := by
    intro u
    obtain ⟨a0, a1, a2, a3, a4, a5, a6⟩ := hRS D X hK u
    exact rowsCols_of X u hK a0 a1 a2 a3 a4 a5 a6
  choose what₂ hrows hsplit cs hcs using h2
  choose Dt hDt using fun u => repsExist X u
  choose FN hFN using fundNC_holds D X hK
  obtain ⟨δ, M, hag, hpin⟩ := hL D hT
  exact ⟨⟨hK, TR, hTR, what₂, hrows, hsplit, cs, hcs, Dt, hDt, FN, hFN, δ, M, hag, hpin⟩⟩

end Formalism.L2.SG.Pf
end
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.SchurNFCOf

section

@[expose] public section

noncomputable section

open scoped Classical InnerProductSpace
open MeasureTheory NumberField Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.L2.SG.TermOp Formalism.L2.SG.Full

namespace PI.SchurPlaces

open Formalism.L2.SG.KappaOffDiagonal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem schurNFC_of (hA : SchurCoreA) (hB : GeomB) : SchurNFC := by
  intro D X u u' Λ Λ' q hdiff hrel hG P hP
  obtain ⟨C, hC, hM⟩ := hB D X u u' Λ Λ' q hrel hG
  obtain ⟨v₀⟩ : Nonempty (InfinitePlace X.B.I.F) := inferInstance
  refine hA D.R.k (InfinitePlace X.B.I.F) (X.Vloc u) (X.Vloc u') (X.Vpi u) (X.Vpi u') (X.tensU u) (X.tensU u')
    (X.tensU_inner u) (X.tensU_span u) (X.tensU_inner u') (X.tensU_span u') (X.piLoc u) (X.piLoc u')
    (fun v i => ((D.hcW u (X.pl v)).u i : ℝ)) (fun v i => ((D.hcW u' (X.pl v)).u i : ℝ))
    (fun v => X.piLoc_type u v) (fun v => X.piLoc_type u' v) v₀ (hdiff (X.pl v₀)) C hC P ?_
  intro M hMu
  obtain ⟨h, hh, h1, h2⟩ := hM M hMu
  exact ⟨X.piU u h, X.piU u' (q.1.1.1⁻¹ * h * q.1.1.1), h1, h2, hP h hh⟩

end PI.SchurPlaces

theorem schurNFC : Formalism.L2.SG.KappaOffDiagonal.SchurNFC :=
  PI.SchurPlaces.schurNFC_of (PI.SchurPlaces.schurCoreA_of Formalism.MainNotions.BridgeLemma.schur_lemma_unitary_distinct_params)
    (PI.SchurPlaces.Geo.geomB_of PI.SchurPlaces.leviTens PI.SchurPlaces.wfrSpan PI.SchurPlaces.cplxNF)
end
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.HostUnram

section

@[expose] public section

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.HostUnramP

open NumberField IsDedekindDomain Formalism.BasicNotions

def HostUnramG : Prop :=
  ∀ D : D7, Formalism.L2.SG.Pf.LocCP.LocTied D → ∀ (p : HeightOneSpectrum (𝓞 D.host.F)) (i : Fin 2),
    ((D.host.g i : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal → ((D.host.g i : ℕ) : 𝓞 D.host.F) ∉ p.asIdeal ^ 2

theorem gi_val (D : D7) (p : HeightOneSpectrum (𝓞 D.host.F)) (i : Fin 2)
    (hi : ((D.host.g i : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal) :
    p.intValuation ((D.host.g i : ℕ) : 𝓞 D.host.F) = WithZero.exp (-1 : ℤ) := by
  exact Formalism.L2.SG.Pf.TypedLoc.tower_val D.host.F D.host.E (D.host.g_prime i) (D.nd.g_split i) p hi

theorem hostUnramG : HostUnramG := by
  intro D _ p i hi hsq
  have h2 := (p.intValuation_le_pow_iff_mem _ 2).mpr hsq
  rw [gi_val D p i hi] at h2
  have h3 := WithZero.exp_le_exp.mp h2
  omega

end Formalism.L2.SG.Pf.HostUnramP
end
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.FullExistsTiedHolds

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.Pf Formalism.L2.SG.TermOp.Vanish

namespace Formalism.L2.SG.Closed

theorem FinLeviC_holds : Formalism.L2.SG.Pf.FinLeviC := Formalism.L2.SG.Pf.FinLeviPf.finLeviC_holds

theorem FoldOKC_outright : FoldOKC := FoldOKC_holds FinLeviC_holds

theorem OOLintSumC_holds : Formalism.L2.SG.Pf.OOLintSumC :=
  Formalism.L2.SG.Pf.ooLintSumC_holds_slab Formalism.L2.SG.Pf.SlabMajPt.pointwise_majorant_by_columns Formalism.L2.SG.Pf.SlabCount.countC_holds

theorem OOIntAllC_outright : OOIntAllC := OOIntAllC_holds OOLintSumC_holds

theorem AbsConvC_outright : AbsConvC := AbsConvC_holds OOLintSumC_holds

theorem KppOffC_holds : Formalism.L2.SG.RowsConc.KppOffC :=
  Formalism.L2.SG.FixedDecomposition.kppOffC_of_steps0 FoldOKC_outright FundExistsC_holds OOIntAllC_outright LemmaVC_holds
    (Formalism.L2.SG.FixedDecomposition.covariantRepZero_of_lemmaV AvgCore_holds Formalism.L2.SG.Pf.ginfUnimod_holds Formalism.L2.SG.Pf.nLamNinf_holds
      ChiTrivialC_holds Formalism.L2.SG.Pf.psiInfChar_holds Formalism.L2.SG.Pf.rClosedC_holds Formalism.L2.SG.Pf.roDiscreteC_holds
      Formalism.L2.SG.TermOp.Vanish.rational_cocompact_holds)
    schurNFC

theorem LocHaarC_holds : Formalism.L2.SG.Pf.LocCP.LocHaarC := by
  intro D _ p
  obtain ⟨μ, h1, h2, h3⟩ := local_haar_real_real _ _ _ _ (D.s.atP p) (Formalism.L2.SG.Pf.LocCP.reduced p)
  refine ⟨μ, h1, h2, ?_⟩
  have hR : Formalism.L2.SG.Pf.LocCP.RR p = PI.LocHaarRR.RR (D.s.atP p) := by
    unfold Formalism.L2.SG.Pf.LocCP.RR PI.LocHaarRR.RR
    cases (D.s.atP p).split <;> rfl
  rw [hR]
  exact h3

theorem PinHostC_holds : Formalism.L2.SG.Pf.LocCP.PinHostC :=
  fun D hT p i hi => prime_quotient_unit _ _ _ _ (D.s.atP p) D.host.g D.host.g_prime D.host.g_ne i hi
    (Formalism.L2.SG.Pf.HostUnramP.hostUnramG D hT p i hi)

theorem LocDualGenC_holds : Formalism.L2.SG.Pf.LocCP.LocDualGenC := fun D _ p => local_dual_generation _ _ _ _ (D.s.atP p)

theorem LocCTied_holds : Formalism.L2.SG.Pf.FullLocalDualAgreement.LocalDualAgreement :=
  Formalism.L2.SG.Pf.FullLocalDualAgreement.locCTied_of' (Formalism.L2.SG.Pf.FullLocalDualAgreement.locDualC_of' LocDualGenC_holds PinHostC_holds)
    LocHaarC_holds

end Formalism.L2.SG.Closed
end
end
