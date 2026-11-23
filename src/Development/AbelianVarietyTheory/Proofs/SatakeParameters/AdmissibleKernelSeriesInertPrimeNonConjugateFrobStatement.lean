module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.BeData
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsConstantCoeffOne
public import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
public import Formalism.LocalToGlobal.KernelLattices.AdaptedEnt
public import Formalism.LocalToGlobal.InertKernelTheory.StatementAlgT
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AtLinAdaptedCoefEqStandardSeriesStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CombOfTied
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsStandardBasesLatticeAtPlaceOfAdaptedBasesStatement
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.StdBases
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.BiextensionRelation
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.ComplexMultiplicationFieldData
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KurComplete
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.TransportFirstLevel
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
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.OrbitIdentityAllOfIntegralClassHostLogStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.StandardBasesHyperbolicPairOrthonormalStatement
import Formalism.SharpRestriction.AdmissibleParameterJoins.GandSp
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.StandardSeriesBConditionsLargePrimeStatement
import Formalism.PeriodIntegrals.OrbJetBase
public import Formalism.SharpRestriction.Divisibility.LocalNonemptiness.OrbitAdmissibleOfSplitBound
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOfInertPrimeEllipticCurveLocalData

section

@[expose] public section

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

namespace GlobalTheory.KerStd

theorem BeData.exists_of_curveData : ∀ (p : ℕ) [Fact p.Prime] (g2 g3 s2 ε : MaximalUnramifiedExtension p) (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p)
    (F : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension p)), CurveData p g2 g3 s2 ε σ F → ∀ (d : ℕ) [NeZero d], Even d →
    ∃ (om oms : Fin (d / 2) → MaximalUnramifiedExtension p) (ζ : MaximalUnramifiedExtension p), BeData p d σ F (cob F (phFF p g2 g3 s2 ε)) om oms ζ := by
  intro p _ g2 g3 s2 ε σ F hC d _ hd
  obtain ⟨-, hg2, hg3, hε, hth, hσ, hF, hN⟩ := hC
  have hff := Formalism.L2.Th1.D.FAux.ffs (l := p) Formalism.L2.Th1.D.first_level_on_curve g2 g3 ε hg2 hg3 hε hth σ hσ F hF s2 hN
  have hp : p.Prime := Fact.out
  have hd0 : d ≠ 0 := NeZero.ne d
  have h1 : 1 < p ^ d := Nat.one_lt_pow hd0 hp.one_lt
  obtain ⟨ζ, hζ⟩ := Formalism.L2.Th1.D.kurRoots p (p ^ d - 1) (by omega) (fun hdv => by
    have h2 : p ∣ p ^ d := dvd_pow_self p hd0
    have h3 : p ∣ 1 := by
      have := Nat.dvd_sub h2 hdv
      rwa [Nat.sub_sub_self h1.le] at this
    exact hp.one_lt.ne' (Nat.dvd_one.1 h3))
  obtain ⟨om, oms, hO, hT⟩ := Formalism.L2.Th1.D.trDualExists (MaximalUnramifiedExtension p) p d σ hσ hd ζ hζ
  exact ⟨om, oms, ζ, hσ, hF, hff.1, hff.2.1, hO, hT, hζ⟩

end GlobalTheory.KerStd
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOfInertPrimeEllipticCurveLocalDataStatement

section

@[expose] public section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

theorem _root_.GlobalTheory.T.exists_of_inertPrimeEllipticCurveLocalData : ∀ (p : ℕ) [Fact p.Prime] (g2 g3 s2 ε : MaximalUnramifiedExtension p) (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p) (F : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension p)), CurveData p g2 g3 s2 ε σ F → ∀ (d : ℕ) [NeZero d], Even d → ∃ (om oms : Fin (d / 2) → MaximalUnramifiedExtension p) (ζ : MaximalUnramifiedExtension p), BeData p d σ F (cob F (phFF p g2 g3 s2 ε)) om oms ζ := by
  first | exact @GlobalTheory.KerStd.BeData.exists_of_curveData | exact GlobalTheory.KerStd.BeData.exists_of_curveData | (intros; apply GlobalTheory.KerStd.BeData.exists_of_curveData <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormalisedFamilyStandardBasesIntegrality

section

@[expose] public section

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

namespace GlobalTheory.KerStd

theorem normalisedFamily_standardBases_integrality : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Formalism.L2.Ker.Base D cc δ) (χ : IdE D → ℂ) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), HostAt B χ p lam → OrbitPlaces.OrbOK D p → ((IsResidueClassZero D p ∧ hP D p ≠ 0) ∨ IsSg D p) → ∃ (ep : ℂ_[p]) (be : MvPowerSeries (ZMod (nP D p)) ℂ_[p]), ‖ep‖ = 1 ∧ BeStd p (nP D p) be ∧ ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E), admitted D N N' L L' → StdBases D lam L P → StdBases D lam L' P' → ∀ G, IsComb D B.tor (B.eNat χ) lam L L' G → ∀ R, OrbitPlaces.IsReps D p R → OrbitPlaces.ThetaExpansionAllPlaces D p R ep (fun _ => -1) (fun _ => be) (stdSer D lam (fun _ => 1) P P' G) := by
  intro D cc δ B χ p _ lam hA hO hCS
  obtain ⟨c, g2, g3, s2, ε, σ, F, hc, hCD, hH⟩ := hA
  obtain ⟨om, oms, ζ, hBD⟩ := GlobalTheory.T.exists_of_inertPrimeEllipticCurveLocalData p g2 g3 s2 ε σ F hCD (nP D p) hO.even
  refine ⟨c, beOf p (nP D p) σ (cob F (phFF p g2 g3 s2 ε)) om oms ζ, hc,
    ⟨σ, F, cob F (phFF p g2 g3 s2 ε), om, oms, ζ, hBD, rfl⟩, ?_⟩
  intro N N' L L' P P' hAdm hP hP' G hG R hR
  obtain ⟨r, b, hb, ho, hint⟩ := hH N N' L L' hAdm
  obtain ⟨f, f', hf, heq⟩ := GlobalTheory.T.standardSeries_scaled_eq_orthonormalSeries_hyperbolicSubst D p lam σ hCD.2.2.2.2.2.1 hO hCS om oms hBD.2.2.2.2.1 hBD.2.2.2.2.2.1
    R hR N N' L L' P P' hAdm hP hP' r b hb ho
  exact GlobalTheory.T.orbitIdentity_all_of_integralClass_hostLog_alt D p g2 g3 s2 ε σ F hCD hO om oms ζ hBD R hR N N' r f f' hf (thOrth D lam c b G) (hint G hG) c
    (stdSer D lam (fun _ => 1) P P' G) (heq c G)

end GlobalTheory.KerStd
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormalisedFamilyStandardBasesIntegralityStatement

section

@[expose] public section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

theorem _root_.GlobalTheory.T.normalisedFamily_standardBases_integrality_alt : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Formalism.L2.Ker.Base D cc δ) (χ : IdE D → ℂ) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), HostAt B χ p lam → OrbitPlaces.OrbOK D p → ((IsResidueClassZero D p ∧ hP D p ≠ 0) ∨ IsSg D p) → ∃ (ep : ℂ_[p]) (be : MvPowerSeries (ZMod (nP D p)) ℂ_[p]), ‖ep‖ = 1 ∧ BeStd p (nP D p) be ∧ ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E), admitted D N N' L L' → StdBases D lam L P → StdBases D lam L' P' → ∀ G, IsComb D B.tor (B.eNat χ) lam L L' G → ∀ R, OrbitPlaces.IsReps D p R → OrbitPlaces.ThetaExpansionAllPlaces D p R ep (fun _ => -1) (fun _ => be) (stdSer D lam (fun _ => 1) P P' G) := by
  first | exact @GlobalTheory.KerStd.normalisedFamily_standardBases_integrality | exact GlobalTheory.KerStd.normalisedFamily_standardBases_integrality | (intros; apply GlobalTheory.KerStd.normalisedFamily_standardBases_integrality <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdmissibleKernelSeriesInertPrimeNonConjugateFrob

section

@[expose] public section

noncomputable section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

namespace GlobalTheory.KerStd

theorem exists_beFam_evenConditionsInert_of_kerEnt : Formalism.L2.KerInert.AlgTAll → (∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Formalism.L2.Ker.Base D cc δ) (χ : IdE D → ℂ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → IsChi D χ → ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), 5 ≤ p → (IsResidueClassZero D p ∨ IsSg D p) → HostAt B χ p lam) → ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : Formalism.L2.Ker.KerEntTied ex), t.Hyp → t.Adapted → 3 ≤ D.host.splitBound → ∃ ep be, BeFam D ep be ∧ OrbitPlaces.EvenConditionsInert (OrbitPlaces.ofKer (nuRowOK D) t.ent ep be (fun _ _ => -1)) Y := by
  intro hAlg hHost D L hT Gi Gl K Y cX ex t hHyp hAd h3
  have hOrb := (Formalism.MainNotions.DIV.Inh.orbit_admissible_of_split_bound D h3).1
  have key : ∀ w : D.what₂.places.Pl, ∃ (e : ℂ_[D.what₂.places.resChar w])
      (b : MvPowerSeries (ZMod (nP D (D.what₂.places.resChar w))) ℂ_[D.what₂.places.resChar w]),
      ((IsResidueClassZero D (D.what₂.places.resChar w) ∧ HEv D (D.what₂.places.resChar w)) ∨ IsSg D (D.what₂.places.resChar w)) →
      ‖e‖ = 1 ∧ BeStd (D.what₂.places.resChar w) (nP D (D.what₂.places.resChar w)) b ∧
      ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
        (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E),
        admitted D N N' L L' → StdBases D (t.ent.lam w) L P → StdBases D (t.ent.lam w) L' P' →
        ∀ G, IsComb D t.B.tor (t.B.eNat t.χ) (t.ent.lam w) L L' G → ∀ R, OrbitPlaces.IsReps D (D.what₂.places.resChar w) R →
          OrbitPlaces.ThetaExpansionAllPlaces D (D.what₂.places.resChar w) R e (fun _ => -1) (fun _ => b) (stdSer D (t.ent.lam w) (fun _ => 1) P P' G) := by
    intro w
    by_cases hc : (IsResidueClassZero D (D.what₂.places.resChar w) ∧ HEv D (D.what₂.places.resChar w)) ∨ IsSg D (D.what₂.places.resChar w)
    · have hO := hOrb _ (D.what₂.places.resChar_prime w) hc
      have hH := hHost D t.cc t.δ t.B t.χ t.cc_ok t.δ_ok t.χ_ok (D.what₂.places.resChar w) (t.ent.lam w) hO.five
        (hc.imp_left And.left)
      obtain ⟨e, b, he, hb, hB⟩ := GlobalTheory.T.normalisedFamily_standardBases_integrality_alt D t.cc t.δ t.B t.χ _ (t.ent.lam w) hH hO (hc.imp_left (And.imp_right HEv.ne_zero))
      exact ⟨e, b, fun _ => ⟨he, hb, hB⟩⟩
    · exact ⟨1, 0, fun h => absurd h hc⟩
  choose ep be hbe using key
  refine ⟨ep, fun w _ => be w, ?_, ?_⟩
  · intro w hc
    obtain ⟨he, hb, -⟩ := hbe w hc
    exact ⟨he, fun _ => hb⟩
  · intro u μ w hLev hc R hR
    obtain ⟨he, hb, hB⟩ := hbe w hc
    have hO := hOrb _ (D.what₂.places.resChar_prime w) hc
    refine ⟨⟨he, fun _ _ => Or.inr rfl, fun _ _ => GlobalTheory.T.standard_series_b_conditions_large_prime _ _ _ hO.five hO.two hO.even hb⟩, ?_⟩
    intro i hi _ c c'
    have hAdPl : Formalism.L2.Ker.AdPl D w := by
      rcases hc with h | h
      · exact Or.inl h.1
      · exact Or.inr (Or.inl h)
    obtain ⟨Pm, hBas, -, hConj, hTh⟩ := hAd w hAdPl u μ hLev
    have hcomb := GlobalTheory.Ggeo.KerComb.comb_of_tied hAlg D L hT Gi Gl K Y cX ex t hHyp u μ w hLev i hi c c'
    have hS : ∀ j, j ≤ D.R.m → ∀ c, StdBases D (t.ent.lam w) ((t.O u μ).lat j c).1 (Pm j c) := fun j hj c =>
      GlobalTheory.T.isStandardBasesLatticeAtPlace_of_adapted_bases D _ (t.ent.lam w) _ _ _ ((t.O u μ).lat j c).2.1 (fun τ => hBas j hj c τ)
        (fun τ τ' h => hConj j hj c τ τ' h)
    show OrbitPlaces.ThetaExpansionAllPlaces D _ R (ep w) (fun _ => -1) (fun _ => be w) (t.ent.Th u μ w i c c')
    rw [hTh i hi c c', GlobalTheory.T.atLin_adaptedCoef_eq_standardSeries]
    exact hB _ _ _ _ _ _ hcomb.1 (hS i hi.le c) (hS (i + 1) hi c') _ hcomb.2 R hR

end GlobalTheory.KerStd
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdmissibleKernelSeriesInertPrimeNonConjugateFrobStatement

section

@[expose] public section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

theorem _root_.GlobalTheory.T.admissibleKernelSeries_inertPrime_nonConjugateFrobenius : Formalism.L2.KerInert.AlgTAll → (∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Formalism.L2.Ker.Base D cc δ) (χ : IdE D → ℂ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → IsChi D χ → ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), 5 ≤ p → (IsResidueClassZero D p ∨ IsSg D p) → HostAt B χ p lam) → ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : Formalism.L2.Ker.KerEntTied ex), t.Hyp → t.Adapted → 3 ≤ D.host.splitBound → ∃ ep be, BeFam D ep be ∧ OrbitPlaces.EvenConditionsInert (OrbitPlaces.ofKer (nuRowOK D) t.ent ep be (fun _ _ => -1)) Y := by
  first | exact @GlobalTheory.KerStd.exists_beFam_evenConditionsInert_of_kerEnt | exact GlobalTheory.KerStd.exists_beFam_evenConditionsInert_of_kerEnt | (intros; apply GlobalTheory.KerStd.exists_beFam_evenConditionsInert_of_kerEnt <;> assumption)
end
end
