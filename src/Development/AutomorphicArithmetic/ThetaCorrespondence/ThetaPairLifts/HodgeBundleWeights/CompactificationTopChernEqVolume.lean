module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InterNumDetNonposSplitTorus
public import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.Multiplier
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovolumeEqSelfDualLatticesSameHermitianSpaceStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSelfDualTr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFullLevelGroupDataSameCovolume
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTransportSelfDualDataOneHermitianSpaceStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexUniformizationLawsOfGoodDeepCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEffCartierCompl
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.CoveringTopologyRefinement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ProportionalityOfLocalCharts
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
public import Formalism.LocalToGlobal.ProjectiveLattices.ModelAt
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LevelCarrying
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCoprimeOfNatCast
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRightActFunPull
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFullLevelGroupDataSameCovolumeStatement

section

@[expose] public section

open NumberField

theorem _root_.GlobalTheory.T.exists_fullLevelGroup_data_same_covolume : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l) (c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → (∀ p : ℕ, p.Prime → l.GoodAt p) → 1 ≤ Dw.p → 1 ≤ Dw.q → ∀ k : U.Comp, ∃ Y : ReciprocityTheory.ChartRestriction.G.FD.Data E r, Y.Ψ = (U.X k).Ψ ∧ Y.p0 = (U.X k).p0 ∧ Y.Gm = (U.X k).Gm ∧ Y.Λ = (U.X k).Λ ∧ Y.ξ0 = (U.X k).ξ0 ∧ GlobalTheory.EqCovol.IsLevGrp l Y ∧ GlobalTheory.EqCovol.IsSelfDualTr Y ∧ GlobalTheory.TrueCx.covol (U.X k) = GlobalTheory.TrueCx.covol Y := by
  first | exact @GlobalTheory.EqCovol.exists_levGrp_covol | exact GlobalTheory.EqCovol.exists_levGrp_covol | (intros; apply GlobalTheory.EqCovol.exists_levGrp_covol <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexUniformisationComponentsCovolumeEq

section

@[expose] public section

open NumberField

namespace GlobalTheory.EqCovol

theorem covol_eq_of_isUnf : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l) (c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → (∀ p : ℕ, p.Prime → l.GoodAt p) → 1 ≤ Dw.p → 1 ≤ Dw.q → ∀ k k' : U.Comp, GlobalTheory.TrueCx.covol (U.X k) = GlobalTheory.TrueCx.covol (U.X k') := by
  intro E _ _ _ H Dw l Xo c σ r U hσ hU hG hp hq k k'
  obtain ⟨Y, hΨ, hp0, -, -, -, hL, hS, hc⟩ := GlobalTheory.T.exists_fullLevelGroup_data_same_covolume E H Dw l Xo c σ r U hσ hU hG hp hq k
  obtain ⟨Y', hΨ', hp0', -, -, -, hL', hS', hc'⟩ := GlobalTheory.T.exists_fullLevelGroup_data_same_covolume E H Dw l Xo c σ r U hσ hU hG hp hq k'
  obtain ⟨hr, hk, -⟩ := hU
  have hY : ∀ τ : E →+* ℂ, τ ∈ Y.Ψ ↔ τ (H.rt : E) = H.rt0 := fun τ => hΨ ▸ (hk k).2 τ
  have hY' : ∀ τ : E →+* ℂ, τ ∈ Y'.Ψ ↔ τ (H.rt : E) = H.rt0 := fun τ => hΨ' ▸ (hk k').2 τ
  have eΨ : Y'.Ψ = Y.Ψ := Finset.ext fun τ => (hY' τ).trans (hY τ).symm
  have ep : Y'.p0 = Y.p0 := by rw [hp0, hp0', (hk k).1, (hk k').1]
  have h1 : 1 ≤ Y.p0 := by rw [hp0, (hk k).1]; exact hq
  have h2 : Y.p0 < r := by rw [hp0, (hk k).1, hr]; omega
  obtain ⟨Z, hZΨ, hZG, hZξ, hZp, hZL, hZS, hZc⟩ := GlobalTheory.T.exists_transport_selfDual_data_one_hermitianSpace E H l r Y Y' hY eΨ ep h1 h2 hL' hS hS'
  rw [hc, hc', ← hZc]
  exact GlobalTheory.T.covolume_eq_selfDual_lattices_same_hermitian_space E H l r Y Z hG hY hZΨ hZG hZξ hZp h1 h2 hL hZL hS hZS

end GlobalTheory.EqCovol
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexUniformisationComponentsCovolumeEqStatement

section

@[expose] public section

open NumberField

theorem _root_.GlobalTheory.T.complexUniformisation_components_covolume_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l) (c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → (∀ p : ℕ, p.Prime → l.GoodAt p) → 1 ≤ Dw.p → 1 ≤ Dw.q → ∀ k k' : U.Comp, GlobalTheory.TrueCx.covol (U.X k) = GlobalTheory.TrueCx.covol (U.X k') := by
  first | exact @GlobalTheory.EqCovol.covol_eq_of_isUnf | exact GlobalTheory.EqCovol.covol_eq_of_isUnf | (intros; apply GlobalTheory.EqCovol.covol_eq_of_isUnf <;> assumption)
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.CompactificationTopChernEqVolume

section

@[expose] public section

section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
namespace GlobalTheory.CompEqVol
theorem equal_volume_of_compactification : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.SemiAbelianLieSeminegative → ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → 2 < Module.finrank ℚ D.host.E / 2 → InR D j → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → EqVolume Y.U := by
  intro hP2 hS hKS hSA D T hT j hp hq hf hj Y e o hY
  have hr : 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q := by omega
  obtain ⟨M, hs, hb, hk, hc⟩ := hKS.exists_model_charts hS hr Y.d.Xo₂ Y.d.c₂
  obtain ⟨TF, hTF⟩ := GlobalTheory.CompProport.exists_torFlag_charts hr M hs hb hk hc
  have hσ : GoodEmb Y.d.c₂ Y.d.c₂.F.val.toRingHom := rfl
  obtain ⟨-, q, -, hv⟩ := _root_.GlobalTheory.CompProport.invariant_volume_eq_covolume (_root_.GlobalTheory.T.covering_topology_refinement hP2) hP2.q7 hSA hY hf TF hTF hσ
  have hg0 : ∀ p : ℕ, p.Prime → T.Q.l.GoodAt p :=
    Formalism.L2.Pj.goodAt_of_two_primes hT.pins.2.1.1 (D.host.g_prime 0) (D.host.g_prime 1) D.host.g_ne
  have hg : ∀ p : ℕ, p.Prime → Y.d.l₂.GoodAt p := GlobalTheory.LawsDeep.goodAt_of_mul _ _ _ hY.lev.1.2.1 hg0
  have hcov := GlobalTheory.T.complexUniformisation_components_covolume_eq _ _ _ _ _ _ _ _ (Formalism.L2.PjFree.Unf.ofPj (Y.U Y.d.c₂.F.val.toRingHom)) hσ
    ((Formalism.L2.PjFree.isUnf_ofPj _).2 (hY.unf _ hσ)) hg hp hq
  intro Z Z'
  obtain ⟨k, rfl⟩ := q.surjective Z
  obtain ⟨k', rfl⟩ := q.surjective Z'
  rw [hv, hv]
  exact congrArg (fun x => x * _ / _) (hcov k k')
end GlobalTheory.CompEqVol
end

section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

theorem _root_.GlobalTheory.T.compactification_top_chern_eq_volume : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.SemiAbelianLieSeminegative → ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → 2 < Module.finrank ℚ D.host.E / 2 → InR D j → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → EqVolume Y.U := by
  first | exact @_root_.GlobalTheory.CompEqVol.equal_volume_of_compactification | exact _root_.GlobalTheory.CompEqVol.equal_volume_of_compactification | (intros; apply _root_.GlobalTheory.CompEqVol.equal_volume_of_compactification <;> assumption)
end
end
end
