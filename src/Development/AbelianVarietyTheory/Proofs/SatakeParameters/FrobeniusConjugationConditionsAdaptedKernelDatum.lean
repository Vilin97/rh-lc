module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsConstantCoeffOne
public import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
public import Formalism.LocalToGlobal.KernelLattices.AdaptedEnt
public import Formalism.LocalToGlobal.InertKernelTheory.StatementAlgT
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AtLinAdaptedCoefEqStandardSeriesStatement
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.StdBases
public import Formalism.SharpRestriction.Divisibility.OrbitPlaces
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExponentShapeOfIntegralClassOneLetter
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
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SubstUnitaryLogarithmicCoordinatesStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitaryMatrixOfOrthonormalLocalBasisAllPlaces
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CombOfTied
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsStandardBasesLatticeAtPlaceOfAdaptedBasesStatement
public import Development.AutomorphicArithmetic.OrbitLabellings.LatticePairsOddDegreeIsometric
public import Formalism.SharpRestriction.Divisibility.LocalNonemptiness.OrbitAdmissibleOfSplitBound

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExponentShapeOfIntegralClassOneLetterStatement

section

@[expose] public section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

theorem _root_.GlobalTheory.T.exponentShape_of_integralClass_oneLetter : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (g2 g3 s2 ε : MaximalUnramifiedExtension p) (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p) (F : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension p)), CurveData p g2 g3 s2 ε σ F → nP D p = 1 → ∀ (N N' : ℕ) (ep : ℂ_[p]) (Th : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p]), ‖ep‖ = 1 → HostLog p g2 g3 s2 ε (MvPowerSeries.subst (fun v : OrbitPlaces.Pl D × Fin N × Fin N' => (MvPowerSeries.C ep * MvPowerSeries.X v : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])) Th : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p]) → OrbitPlaces.ThetaExpansionRealPlaces D p Th := by
  first | exact @GlobalTheory.KerStd.expShape_of_integralClass | exact GlobalTheory.KerStd.expShape_of_integralClass | (intros; apply GlobalTheory.KerStd.expShape_of_integralClass <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitaryMatrixOfOrthonormalLocalBasisAllPlacesStatement

section

@[expose] public section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

theorem _root_.GlobalTheory.T.unitaryMatrix_of_orthonormal_localBasis_allPlaces : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p), UnrOK (MaximalUnramifiedExtension p) p σ → 5 ≤ p → IsResidueClassZero D p → hP D p = 0 → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E), admitted D N N' L L' → StdBases D lam L P → StdBases D lam L' P' → ∀ (r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), LocBasis D p (YYl D L L') b → TaylorLogMetric.Orthonormal D b → ∃ γ : Fin r → (OrbitPlaces.Pl D × Fin N × Fin N') → MaximalUnramifiedExtension p, (∀ i j, ‖γ i j‖ ≤ 1 ∧ σ (σ (γ i j)) = γ i j) ∧ (∀ j j', ∑ i, σ (γ i j) * γ i j' = if j = j' then 1 else 0) ∧ ∀ (c : ℂ_[p]) (G : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]), (MvPowerSeries.subst (fun v : OrbitPlaces.Pl D × Fin N × Fin N' => (MvPowerSeries.C c * MvPowerSeries.X v : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])) (stdSer D lam (fun _ => 1) P P' G) : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p]) = MvPowerSeries.subst (fun i => (∑ j, MvPowerSeries.C (γ i j : ℂ_[p]) * MvPowerSeries.X j : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])) (thOrth D lam c b G) := by
  first | exact @GlobalTheory.KerStd.unitary_of_orthonormal | exact GlobalTheory.KerStd.unitary_of_orthonormal | (intros; apply GlobalTheory.KerStd.unitary_of_orthonormal <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.B0StandardSeriesAdmissible

section

@[expose] public section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

namespace GlobalTheory.KerStd

theorem nP_eq_one_of_hP_eq_zero (D : D7) (p : ℕ) (hC : IsResidueClassZero D p) (h0 : hP D p = 0) : nP D p = 1 := by
  have hS : ¬ IsSg D p := by
    intro hs
    unfold IsResidueClassZero at hC
    unfold IsSg at hs
    rw [hC] at hs
    exact absurd hs (by decide)
  unfold nP
  rw [if_neg hS, h0, addOrderOf_zero]

theorem thetaExpansionRealPlaces_stdSer_of_adm : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Formalism.L2.Ker.Base D cc δ) (χ : IdE D → ℂ) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), HostAt B χ p lam → 5 ≤ p → IsResidueClassZero D p → hP D p = 0 → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E), admitted D N N' L L' → StdBases D lam L P → StdBases D lam L' P' → ∀ G, IsComb D B.tor (B.eNat χ) lam L L' G → OrbitPlaces.ThetaExpansionRealPlaces D p (stdSer D lam (fun _ => 1) P P' G) := by
  intro D cc δ B χ p _ lam hHost h5 hC hP0 N N' L L' P P' hAdm hS hS' G hG
  obtain ⟨c, g2, g3, s2, ε, σ, F, hc, hcd, hfam⟩ := hHost
  obtain ⟨r, b, hLB, hON, hInt⟩ := hfam N N' L L' hAdm
  obtain ⟨γ, hγ1, hγ2, hγ3⟩ := GlobalTheory.T.unitaryMatrix_of_orthonormal_localBasis_allPlaces D p lam σ hcd.2.2.2.2.2.1 h5 hC hP0 N N' L L' P P' hAdm hS hS' r b hLB hON
  have hU := GlobalTheory.T.subst_unitary_logarithmic_coordinates p g2 g3 s2 ε σ F hcd (Fin r) (OrbitPlaces.Pl D × Fin N × Fin N') γ hγ1 (by convert hγ2) _ (hInt G hG)
  rw [← hγ3 c G] at hU
  exact GlobalTheory.T.exponentShape_of_integralClass_oneLetter D p g2 g3 s2 ε σ F hcd (nP_eq_one_of_hP_eq_zero D p hC hP0) N N' c _ hc hU

end GlobalTheory.KerStd
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.B0StandardSeriesAdmissibleStatement

section

@[expose] public section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

theorem _root_.GlobalTheory.T.thetaExpansionRealPlaces_stdSer_of_adm' : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Formalism.L2.Ker.Base D cc δ) (χ : IdE D → ℂ) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), HostAt B χ p lam → 5 ≤ p → IsResidueClassZero D p → hP D p = 0 → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E), admitted D N N' L L' → StdBases D lam L P → StdBases D lam L' P' → ∀ G, IsComb D B.tor (B.eNat χ) lam L L' G → OrbitPlaces.ThetaExpansionRealPlaces D p (stdSer D lam (fun _ => 1) P P' G) := by
  first | exact @GlobalTheory.KerStd.thetaExpansionRealPlaces_stdSer_of_adm | exact GlobalTheory.KerStd.thetaExpansionRealPlaces_stdSer_of_adm | (intros; apply GlobalTheory.KerStd.thetaExpansionRealPlaces_stdSer_of_adm <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.FrobeniusConjugationConditionsAdaptedKernelDatum

section

@[expose] public section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

namespace GlobalTheory.Ggeo

theorem frobeniusConjugation_conditions_adaptedKernelDatum_alt : Formalism.L2.KerInert.AlgTAll → (∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Formalism.L2.Ker.Base D cc δ) (χ : IdE D → ℂ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → IsChi D χ → ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), 5 ≤ p → (IsResidueClassZero D p ∨ IsSg D p) → HostAt B χ p lam) → ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : Formalism.L2.Ker.KerEntTied ex), t.Hyp → t.Adapted → 3 ≤ D.host.splitBound → ∀ ep be sg, OrbitPlaces.EvenConditionsAtC (OrbitPlaces.ofKer (nuRowOK D) t.ent ep be sg) Y := by
  intro hAlg hHost D L hT Gi Gl K Y cX ex t hHyp hAd h3 ep be sg
  have main : ∀ u μ (w : D.what₂.places.Pl), LevFree Y u μ w → IsResidueClassZero D (D.what₂.places.resChar w) → ∀ i < D.R.m, ∀ c c',
      ∀ Q : MvPowerSeries (OrbitPlaces.Pl D × Fin (D.R.N i) × Fin (D.R.N (i + 1))) ℂ_[D.what₂.places.resChar w] → Prop,
      (HostAt t.B t.χ (D.what₂.places.resChar w) (t.ent.lam w) → 5 ≤ D.what₂.places.resChar w →
        ∀ (L : Submodule (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin (D.R.N (i + 1)) → D.host.E))
          (P : D.what₂.Tau → Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E)
          (P' : D.what₂.Tau → Matrix (Fin (D.R.N (i + 1))) (Fin (D.R.N (i + 1))) D.host.E),
          admitted D (D.R.N i) (D.R.N (i + 1)) L L' → StdBases D (t.ent.lam w) L P → StdBases D (t.ent.lam w) L' P' →
          ∀ G, IsComb D t.B.tor (t.B.eNat t.χ) (t.ent.lam w) L L' G → Q (stdSer D (t.ent.lam w) (fun _ => 1) P P' G)) →
      Q (t.ent.Th u μ w i c c') := by
    intro u μ w hLF' hC i hi c c' Q hQ
    have hprime : (D.what₂.places.resChar w).Prime := Fact.out
    have h5 : 5 ≤ D.what₂.places.resChar w := (DIV.Inh.orbit_admissible_of_split_bound D h3).2 _ hprime hC
    have hAdPl : Formalism.L2.Ker.AdPl D w := Or.inl hC
    obtain ⟨Pm, hB, -, hConj, hTh⟩ := hAd w hAdPl u μ hLF'
    obtain ⟨hAdm, hComb⟩ := GlobalTheory.Ggeo.KerComb.comb_of_tied hAlg D L hT Gi Gl K Y cX ex t hHyp u μ w hLF' i hi c c'
    have hHA := hHost D t.cc t.δ t.B t.χ t.cc_ok t.δ_ok t.χ_ok (D.what₂.places.resChar w) (t.ent.lam w) h5 (Or.inl hC)
    have hS : StdBases D (t.ent.lam w) ((t.O u μ).lat i c).1 (Pm i c) :=
      GlobalTheory.T.isStandardBasesLatticeAtPlace_of_adapted_bases D _ (t.ent.lam w) _ _ _ ((t.O u μ).lat i c).2.1 (fun τ => hB i hi.le c τ)
        (fun τ τ' h => hConj i hi.le c τ τ' h)
    have hS' : StdBases D (t.ent.lam w) ((t.O u μ).lat (i + 1) c').1 (Pm (i + 1) c') :=
      GlobalTheory.T.isStandardBasesLatticeAtPlace_of_adapted_bases D _ (t.ent.lam w) _ _ _ ((t.O u μ).lat (i + 1) c').2.1 (fun τ => hB (i + 1) hi c' τ)
        (fun τ τ' h => hConj (i + 1) hi c' τ τ' h)
    have key := hQ hHA h5 _ _ _ _ hAdm hS hS' _ hComb
    rw [hTh i hi c c', GlobalTheory.T.atLin_adaptedCoef_eq_standardSeries]
    exact key
  refine ⟨fun u μ w hLF hC hP0 i hi _ c c' => ?_, fun u μ w hLF hC i hi _ c c' => ?_⟩
  · exact main u μ w hLF hC i hi c c' (OrbitPlaces.ThetaExpansionRealPlaces D (D.what₂.places.resChar w)) fun hHA h5 =>
      GlobalTheory.T.thetaExpansionRealPlaces_stdSer_of_adm' D t.cc t.δ t.B t.χ (D.what₂.places.resChar w) (t.ent.lam w) hHA h5 hC hP0 _ _
  · have hodd : Odd (nP D (D.what₂.places.resChar w)) := by
      have hs : ¬ IsSg D (D.what₂.places.resChar w) := fun h => by
        have h1 : D.host.cls (D.what₂.places.resChar w) = PrimeClass.inertClass := hC.1
        have h2 : D.host.cls (D.what₂.places.resChar w) = PrimeClass.signal := h
        rw [h1] at h2; cases h2
      unfold nP
      rw [if_neg hs]
      exact hC.2.1
    exact main u μ w hLF hC.1 i hi c c' (OrbitPlaces.EvenConditionsAllReal D (D.what₂.places.resChar w)) fun hHA h5 =>
      UpperTheory.lattice_pairs_odd_degree_isometric D t.cc t.δ t.B t.χ (D.what₂.places.resChar w) (t.ent.lam w) hHA h5 hC.1 hodd _ _

end GlobalTheory.Ggeo
end
end
