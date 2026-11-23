module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.VacTIff
public import Formalism.LocalToGlobal.InertKernelTheory.DefsRepComb
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StrongApproximationDecomposition
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FiniteDimensionalMram
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CharConjFixedEqOne
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsDiscriminantTwelfthRootOfIdealLatticeIffDelta1
import Development.AbelianVarietyTheory.Definitions.Foundations.ValuedAlgebraMapEqOne
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MidChart
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.KerTh
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsDiscriminantTwelfthRootOfIdealLatticeIffDelta1
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MovedWeilVacuumEqVacuumOfMovedLatticesStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueColumnStepsAreStandardHermitianPairs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisedFamilyStandardLatticesEqBaseVector
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SpanRangeEmb4EqTop
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.RepComb
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.IsAdmissibleFlagPairOfUnitriangularLeftAutomorph
public import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.IntegralSquareRoots.OneEntryMem
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicTranslateOneEqStandardLattice

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdForm.MovesOne

theorem finM_one {D : D7} (V : HSp D) {n : ℕ} (hn : V.rank = n) : finM V hn (1 : GA D V) = 1 := by
  subst hn
  unfold finM Formalism.L2.Theta.mt
  rw [map_one, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
  simp

theorem moves_one : ∀ (D : D7) (V : HSp D) (n : ℕ) (hn : V.rank = n) (N : Submodule (𝓞 D.host.E) (Fin n → D.host.E)),
    Moves V hn 1 N → N = Formalism.L2.Col.stdLat D.host.E n := by
  intro D V n hn N h
  ext x
  rw [h x, inv_one, finM_one, Matrix.one_mulVec]
  simp only [GlobalTheory.SplitDec.rat_int_iff]
  exact ⟨fun hx i _ => hx i, fun hx i => hx i trivial⟩

end GlobalTheory.AdForm.MovesOne
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicTranslateOneEqStandardLatticeStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.adelicTranslate_one_eq_standardLattice : ∀ (D : D7) (V : HSp D) (n : ℕ) (hn : V.rank = n) (N : Submodule (𝓞 D.host.E) (Fin n → D.host.E)), Moves V hn 1 N → N = Formalism.L2.Col.stdLat D.host.E n := by
  first | exact @GlobalTheory.AdForm.MovesOne.moves_one | exact GlobalTheory.AdForm.MovesOne.moves_one | (intros; apply GlobalTheory.AdForm.MovesOne.moves_one <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CharConjFixedEqOneStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.character_eq_one_of_isDetRoot_of_even : ∀ (D : D7) (μ : (AE D)ˣ →* Circle) (n : ℕ), ResEta D μ n → Even n → ∀ (V : HSp D) (x : (AE D)ˣ), IsDetRoot V 1 x → μ x = 1 := by
  first | exact @GlobalTheory.char_conj_fixed_eq_one | exact GlobalTheory.char_conj_fixed_eq_one | (intros; apply GlobalTheory.char_conj_fixed_eq_one <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeChainStandardPair

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ThetaLineStd

theorem aaOf_top (D : D7) : (Formalism.L2.PairingIndexBounds.F.aaOf D ⊤) = (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) :=
  GlobalTheory.Mem.Col2.Th.perAA_top D.host

end GlobalTheory.ThetaLineStd
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDiscriminantTwelfthRootOfIdeal

section

@[expose] public section

noncomputable section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric

namespace GlobalTheory.Glob.IntegralWittCoefficients

theorem isCurveIdeal_top (D : D7) : IsCurveIdeal D ⊤ :=
  ⟨top_ne_bot, by simp⟩

end GlobalTheory.Glob.IntegralWittCoefficients
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MovedVacuumAtIdentityNonzeroConstant

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

noncomputable section
namespace GlobalTheory.AdForm.VacAllBase

theorem thetaSpace_std_line {B : Base} {X : PreX B.toPre} (I : TC B X) (hI : I.Ok) (l : I.Laws) (Z : TC.Later B (I.cols l)) (i : ℕ) (hi : i + 1 ≤ B.R.m) : ∀ F ∈ Formalism.L2.Th1.H.Th (HV I.A.sc) (alV (I.rec7 l Z).host.d I.A.sc) (LamC (tauE (I.rec7 l Z)) I.A.δ ((I.rec7 l Z).host.AA0 : Submodule (𝓞 (I.rec7 l Z).host.E) (I.rec7 l Z).host.E) (Formalism.L2.Col.stdLat (I.rec7 l Z).host.E (B.R.N i)) (Formalism.L2.Col.stdLat (I.rec7 l Z).host.E (B.R.N (i + 1)))), ∃ c : ℂ, F = c • I.J.V.thMoved (B.R.N i) (B.R.N (i + 1)) (Formalism.L2.Col.stdLat (I.rec7 l Z).host.E (B.R.N i)) (Formalism.L2.Col.stdLat (I.rec7 l Z).host.E (B.R.N (i + 1))) := by
  intro F hF
  let Bk : Formalism.L2.Ker.Base (I.rec7 l Z) ⊤ I.J.δ := GlobalTheory.Mem.Col2.Th.VacIn.toRec (D := I.rec7 l Z) I.J.V
  have hS : Bk.StdOK := GlobalTheory.FourthRootStd.stdOK Bk (GlobalTheory.Glob.IntegralWittCoefficients.isCurveIdeal_top _)
    ((GlobalTheory.Mem.Col2.Th.isDiscriminantTwelfthRoot_host_iff (I.rec7 l Z) ⊤ I.J.δ).1 hI.amb_ok.delta)
  have hLa : LamC (tauE (I.rec7 l Z)) I.A.δ ((I.rec7 l Z).host.AA0 : Submodule (𝓞 (I.rec7 l Z).host.E) (I.rec7 l Z).host.E) (Formalism.L2.Col.stdLat (I.rec7 l Z).host.E (B.R.N i)) (Formalism.L2.Col.stdLat (I.rec7 l Z).host.E (B.R.N (i + 1))) = Formalism.MainNotions.TaylorLogMetric.La (I.rec7 l Z) (Formalism.MainNotions.TaylorLogMetric.tor0 (I.rec7 l Z) ⊤ I.J.δ) (Formalism.MainNotions.StandardLatticesGL3.stdL (I.rec7 l Z) (B.R.N i)) (Formalism.MainNotions.StandardLatticesGL3.stdL (I.rec7 l Z) (B.R.N (i + 1))) := by
    rw [← Formalism.L2.KerInert.RepComb.lamK_eq, Formalism.L2.KerInert.RepComb.lamK, GlobalTheory.ThetaLineStd.aaOf_top]
    rfl
  have hH : (HV (ι := (I.rec7 l Z).what₂.Tau) (a := B.R.N i) (b := B.R.N (i + 1)) I.A.sc) = formV (Formalism.MainNotions.TaylorLogMetric.area (Formalism.MainNotions.TaylorLogMetric.lamOf (I.rec7 l Z) ⊤ I.J.δ)) (I.rec7 l Z).what₂.Tau (B.R.N i) (B.R.N (i + 1)) :=
    Formalism.L2.KerInert.RepComb.HV_eq_formV _
  rw [hLa, alV, hH] at hF
  have hF' : F ∈ Formalism.L2.Th1.H.Th (formV (Formalism.MainNotions.TaylorLogMetric.area (Formalism.MainNotions.TaylorLogMetric.lamOf (I.rec7 l Z) ⊤ I.J.δ)) (I.rec7 l Z).what₂.Tau (B.R.N i) (B.R.N (i + 1))) (Formalism.MainNotions.TaylorLogMetric.al (I.rec7 l Z) Bk.tor) (Formalism.MainNotions.TaylorLogMetric.La (I.rec7 l Z) Bk.tor (Formalism.MainNotions.StandardLatticesGL3.stdL (I.rec7 l Z) (B.R.N i)) (Formalism.MainNotions.StandardLatticesGL3.stdL (I.rec7 l Z) (B.R.N (i + 1)))) := by
    refine Formalism.L2.Ker.Th_congr _ _ _ _ (fun x hx => ?_) hF
    obtain ⟨m, hm⟩ := Bk.qInt0 hS _ _ x hx
    exact (Formalism.L2.Ker.al_eq _ Bk.tor x m hm).symm
  obtain ⟨c, hc⟩ := Formalism.L2.PairingIndexBounds.Eq.J.thZeroSpans hS _ _ F hF'
  refine ⟨c, ?_⟩
  have hM : I.J.V.thMoved (B.R.N i) (B.R.N (i + 1)) (Formalism.L2.Col.stdLat (I.rec7 l Z).host.E (B.R.N i)) (Formalism.L2.Col.stdLat (I.rec7 l Z).host.E (B.R.N (i + 1))) = Bk.thMoved (B.R.N i) (B.R.N (i + 1)) (Formalism.MainNotions.StandardLatticesGL3.stdL (I.rec7 l Z) (B.R.N i)) (Formalism.MainNotions.StandardLatticesGL3.stdL (I.rec7 l Z) (B.R.N (i + 1))) := rfl
  obtain ⟨x, hx, hIx⟩ := GlobalTheory.NatAtStd.Iop_self (I.rec7 l Z) Bk.tor (Formalism.MainNotions.TaylorLogMetric.La (I.rec7 l Z) Bk.tor (Formalism.MainNotions.StandardLatticesGL3.stdL (I.rec7 l Z) (B.R.N i)) (Formalism.MainNotions.StandardLatticesGL3.stdL (I.rec7 l Z) (B.R.N (i + 1))))
  have hfix : (fun z => Formalism.MainNotions.TaylorLogMetric.al (I.rec7 l Z) Bk.tor x * Formalism.MainNotions.TaylorLogMetric.U (I.rec7 l Z) Bk.tor x (Bk.thZero (B.R.N i) (B.R.N (i + 1))) z) = Bk.thZero (B.R.N i) (B.R.N (i + 1)) :=
    funext fun z => (Bk.thZeroMem hS _ _).2 x hx z
  have hMz : Bk.thMoved (B.R.N i) (B.R.N (i + 1)) (Formalism.MainNotions.StandardLatticesGL3.stdL (I.rec7 l Z) (B.R.N i)) (Formalism.MainNotions.StandardLatticesGL3.stdL (I.rec7 l Z) (B.R.N (i + 1))) = Bk.thZero (B.R.N i) (B.R.N (i + 1)) := by
    unfold Formalism.L2.Ker.Base.thMoved Formalism.L2.Ker.Base.thHalf
    rw [hIx, hIx, hfix, hfix]
  rw [hM, hMz]
  exact hc

theorem moveT_one : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) ψ θ, IsStdChar (I.rec7 l Z) ψ (-1) → IsInfFam θ → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m) vac, IsVacO ψ θ ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)) (fun _ => 1) (fun _ => 1) (intVec _ _) (intVec _ _) vac → ∀ (a : I.ι) μ om, ChrEq μ (I.C.mu0 ⟨i, hi⟩ * I.xi a) → IsWeilDatumO ψ _ _ μ μ om → ∃ c₀ : ℂ, c₀ ≠ 0 ∧ GlobalTheory.AdForm.VacAll.MoveT I l Z θ i hi c₀ μ om vac 1 1 := by
  intro B X I hI hP l Z ψ θ hψ hθ i hi vac hvac a μ om _ hom
  have hstd := (GlobalTheory.AdForm.StdStepsT.stdPair_steps_all I hI hP l Z ψ θ hψ hθ).1 i hi
  have key := GlobalTheory.T.movedWeilVacuum_eq_vacuum_of_movedLattices (I.rec7 l Z) ψ θ _ _ _ _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) (rankN (I.rec7 l Z) (i + 1) hi)
    I.A.δ I.A.sc hstd μ om hom vac hvac 1 (one_mem _) 1 (one_mem _)
  have S1 : ∀ (D : D7) (V : HSp D) (n : ℕ) (hn : V.rank = n) (N : Submodule (𝓞 D.host.E) (Fin n → D.host.E)),
      Moves V hn 1 N → N = Formalism.L2.Col.stdLat D.host.E n := GlobalTheory.T.adelicTranslate_one_eq_standardLattice
  have S2 : ∀ (D : D7) (μ : (AE D)ˣ →* Circle) (n : ℕ), ResEta D μ n → Even n → ∀ (V : HSp D) (x : (AE D)ˣ),
      IsDetRoot V 1 x → μ x = 1 := GlobalTheory.T.character_eq_one_of_isDetRoot_of_even
  have S3 := thetaSpace_std_line I hI l Z i hi
  by_cases hex : Moves _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) 1 (Formalism.L2.Col.stdLat (I.rec7 l Z).host.E (B.R.N i)) ∧
      Moves _ (rankN (I.rec7 l Z) (i + 1) hi) 1 (Formalism.L2.Col.stdLat (I.rec7 l Z).host.E (B.R.N (i + 1)))
  · obtain ⟨-, hmem, hne⟩ := key _ _ hex.1 hex.2
    obtain ⟨c, hc⟩ := S3 _ hmem
    refine ⟨c, ?_, ?_⟩
    · rintro rfl
      apply hne
      exact hc.trans (zero_smul _ _)
    · intro N N' hN hN' x y hx hy
      obtain rfl := S1 _ _ _ _ N hN
      obtain rfl := S1 _ _ _ _ N' hN'
      have hx1 : μ x = 1 := S2 _ _ _ hom.resS hstd.rk.2.2.1 _ x hx
      have hy1 : μ y = 1 := S2 _ _ _ hom.resT hstd.rk.2.2.2 _ y hy
      rw [hx1, hy1]
      show xiN θ _ _ _ _ I.A.δ I.A.sc _ = _
      refine hc.trans ?_
      funext z
      simp only [Pi.smul_apply, smul_eq_mul, Circle.coe_one, inv_one, mul_one]
      rfl
  · refine ⟨1, one_ne_zero, ?_⟩
    intro N N' hN hN'
    exact absurd ⟨S1 _ _ _ _ N hN ▸ hN, S1 _ _ _ _ N' hN' ▸ hN'⟩ hex

end GlobalTheory.AdForm.VacAllBase
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MovedVacuumAtIdentityNonzeroConstantStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf


theorem _root_.GlobalTheory.T.movedVacuum_at_identity_nonzero_constant : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) ψ θ, IsStdChar (I.rec7 l Z) ψ (-1) → IsInfFam θ → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m) vac, IsVacO ψ θ ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)) (fun _ => 1) (fun _ => 1) (intVec _ _) (intVec _ _) vac → ∀ (a : I.ι) μ om, ChrEq μ (I.C.mu0 ⟨i, hi⟩ * I.xi a) → IsWeilDatumO ψ _ _ μ μ om → ∃ c₀ : ℂ, c₀ ≠ 0 ∧ GlobalTheory.AdForm.VacAll.MoveT I l Z θ i hi c₀ μ om vac 1 1 := by
  first | exact @GlobalTheory.AdForm.VacAllBase.moveT_one | exact GlobalTheory.AdForm.VacAllBase.moveT_one | (intros; apply GlobalTheory.AdForm.VacAllBase.moveT_one <;> assumption)
end
end
