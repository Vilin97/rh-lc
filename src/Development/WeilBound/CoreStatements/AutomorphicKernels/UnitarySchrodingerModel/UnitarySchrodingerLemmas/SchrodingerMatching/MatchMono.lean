module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.DictKAOfParts
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.WhitNDgOfLocalOfSteps
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaDecompositionUnitary
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelParabolicUnnMatrixBlockUpperTriangular
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
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnfoldingHoldsStatement
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.FiniteMatchingK2.FinitePlacesMatch
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.FockLatticeHeights.HWFinal
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.SchrodingerMatching.HaarFam
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsSelfDualLatticeIff
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.IwasawaReduction.ModOfCg
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.SchrodingerMatching.PsiPlaces
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussMulUnitary
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhitKA
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.MatrixInfinitySpan.RealMatch
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.SchrodingerMatching.Assembly
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypeFromConjugateComplement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacOfMemSchwartzA
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RealAdelesCmFieldEquivComplexCmType
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrameIntegralEqThetaPartNondegenerate
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeftInvSubtypeSum
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasSign

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightKInvariance

section

@[expose] public section

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.PfSWUS

open GlobalTheory.StdUnn

theorem height_mul_K {D : D7} {n : ℕ} {H : G D n → ℝ≥0} (hH : IsHeight H) (x : G D n) {k : G D n} (hk : k ∈ K D n) :
    H (x * k) = H x := by
  obtain ⟨p, hp, k', hk', rfl⟩ := GlobalTheory.StdUnn.Iwasawa.exists_mul D n x
  obtain ⟨a, ha⟩ := GlobalTheory.StdUnn.LeftInvSect.exists_blkA hp
  rw [mul_assoc, hH p hp a ha _ ((K D n).mul_mem hk' hk), hH p hp a ha k' hk']

end GlobalTheory.CompanionTheory.PfSWUS

end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightKInvarianceStatement

section

@[expose] public section

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.height_K_invariance : PositivityTheory.PfSWUS.HeightKInv := by
  first | exact @GlobalTheory.CompanionTheory.PfSWUS.height_mul_K | exact GlobalTheory.CompanionTheory.PfSWUS.height_mul_K | (intros; apply GlobalTheory.CompanionTheory.PfSWUS.height_mul_K <;> assumption)
end
end
end

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.HaarFamilies.HaarFam

section

@[expose] public section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory

namespace PositivityTheory.PfSWUS.SwMatch

theorem haarFam : HaarFam := by
  intro D n
  have key : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers D.host.F),
      ∃ m : Measure (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E), m.IsAddHaarMeasure := by
    intro v
    have := (GlobalTheory.LocalDensityCompare.lcs (E := D.host.E) v).1
    have := (GlobalTheory.LocalDensityCompare.lcs (E := D.host.E) v).2.1
    have := GlobalTheory.LocalDensityCompare.topRing (E := D.host.E) v
    have : BorelSpace (HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E) := ⟨rfl⟩
    have : BorelSpace (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E) := Pi.borelSpace
    exact ⟨Measure.addHaar, inferInstance⟩
  choose lam hlam using key
  exact ⟨lam, hlam⟩

end PositivityTheory.PfSWUS.SwMatch

end
end
end

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.MatrixInfinitySpan.RealConj

section

@[expose] public section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.PfSWUS.SwSpan

open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.IwaAd PositivityTheory.PfSWUS.SwMatch

theorem matInf_map {D : D7} (θ : InfFam D) (τ : D.what₂.Tau) {n : ℕ} (X : Mx D n n) :
    (PositivityTheory.SiegelWeilFormula.Gen.matInf X).map (θ τ) = compAt θ τ X := by
  ext i j
  rfl

theorem aTau_val {D : D7} (θ : InfFam D) {n : ℕ} (a : GL (Fin n) (AE D)) (τ : D.what₂.Tau) :
    (aTau θ a τ).1 = compAt θ τ a.1 := rfl

theorem realConj : RealConj := by
  intro D θ hθ n a b
  unfold PositivityTheory.SiegelWeilFormula.Gen.nuInf
  refine Finset.prod_congr rfl fun τ _ => ?_
  have hA : ((aTau θ a τ)⁻¹).1 * compAt θ τ a.1 = 1 := by
    rw [← aTau_val, ← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel, Matrix.GeneralLinearGroup.coe_one]
  have hc : compAt θ τ (conjH a b).1 = compAt θ τ a.1 * compAt θ τ b.1 * (compAt θ τ a.1)ᴴ := by
    rw [← GlobalTheory.VacKInf.LeviFix.compAt_adj' hθ τ a.1]
    show (a.1 * b.1 * adj a.1).map ((θ τ).comp (infPart D)) = _
    rw [Matrix.map_mul, Matrix.map_mul]
    rfl
  have hB : ((aTau θ a τ)⁻¹).1 * (compAt θ τ a.1 * compAt θ τ b.1 * (compAt θ τ a.1)ᴴ) *
      (((aTau θ a τ)⁻¹).1)ᴴ = compAt θ τ b.1 := by
    calc _ = (((aTau θ a τ)⁻¹).1 * compAt θ τ a.1) * compAt θ τ b.1 *
          (((aTau θ a τ)⁻¹).1 * compAt θ τ a.1)ᴴ := by
            rw [Matrix.conjTranspose_mul]
            simp only [Matrix.mul_assoc]
      _ = compAt θ τ b.1 := by rw [hA]; simp
  rw [matInf_map, matInf_map, hc, hB]
  simp

end PositivityTheory.PfSWUS.SwSpan
end
end
end

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.SchrodingerMatching.PsiVal

section

@[expose] public section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.PfSWUS.SwMatch

open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.IwaAd GlobalTheory.CompanionTheory.SiegelND

theorem exists_ext_infFam (D : D7) (θ : InfFam D) (hθ : IsInfFam θ) :
    ∃ θ' : (D.host.E →+* ℂ) → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ),
      (∀ φ, Formalism.MainNotions.StandardLattice.IsInfEmb φ (θ' φ)) ∧ ∀ τ, θ' (tauE D τ) = θ τ := by
  classical
  obtain ⟨θ₀, h₀⟩ := (GlobalTheory.Member.infiniteAdele_bijective D).1
  refine ⟨Function.extend (tauE D) θ θ₀, fun φ => ?_, fun τ => (GlobalTheory.MassLink.tauE_injective' D).extend_apply θ θ₀ τ⟩
  by_cases h : ∃ τ, tauE D τ = φ
  · obtain ⟨τ, rfl⟩ := h
    rw [(GlobalTheory.MassLink.tauE_injective' D).extend_apply θ θ₀ τ]
    exact hθ τ
  · rw [Function.extend_apply' θ θ₀ φ h]
    exact h₀ φ

theorem infFam_spec (D : D7) (θ : InfFam D) (hθ : IsInfFam θ) :
    (∀ τ, Continuous (θ τ)) ∧
      (∀ τ z, θ τ (sigR (Ainf D.host.F) D.sp.cm.sig z) = starRingEnd ℂ (θ τ z)) ∧
      Function.Bijective fun (z : Ainf D.host.F ⊗[D.host.F] D.host.E) τ => θ τ z := by
  obtain ⟨θ', h', e⟩ := exists_ext_infFam D θ hθ
  obtain ⟨h1, h2, h3⟩ := (GlobalTheory.Member.infiniteAdele_bijective D).2 θ' h'
  refine ⟨fun τ => e τ ▸ h1 _, fun τ z => e τ ▸ h2 _ z, ?_⟩
  have h0 : D.host.φ₀ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ) := D.host.φ₀_mem
  let ι : D.what₂.Tau → {φ : D.host.E →+* ℂ // φ D.host.sqrtMinusD = D.host.φ₀ D.host.sqrtMinusD} :=
    fun τ => ⟨tauE D τ, (Formalism.L2.Theta.tauE_sqrtMinusD D τ).trans h0.symm⟩
  have hι : Function.Bijective ι :=
    ⟨fun a b h => GlobalTheory.MassLink.tauE_injective' D (congrArg Subtype.val h), fun φ => by
      obtain ⟨τ, hτ⟩ := GlobalTheory.MassLink.tauE_surj' D φ.1 (φ.2.trans h0)
      exact ⟨τ, Subtype.ext hτ⟩⟩
  have h4 := (hι.comp_right (γ := ℂ)).comp h3
  convert h4 using 2 with z
  funext τ
  exact (congrArg (fun t => t z) (e τ)).symm

theorem psiPlaces : PsiPlaces := by
  intro D n V ψ χ θ μ ω H l s ν Φ h
  obtain ⟨h1, h2, h3⟩ := infFam_spec D θ h.hθ
  exact ⟨h.hψ, h1, h3, h2, GlobalTheory.ResAniso.VacSchwartz.realPar_ne_zero D θ h.hθ ψ h.hψ l h.hl, h.hl⟩


open GlobalTheory.CompanionTheory.SiegelND.ThetaGlue in
theorem valueSide : ValueSide := by
  intro D r V ν hν φ β hβ μH 𝓕 hμ h𝓕
  have hrank : ∀ (δ : GL (Fin V.rank) D.host.E) (ξ : Matrix (Fin V.rank) (Fin r) D.host.E),
      (δ.1 * ξ).rank = ξ.rank := fun δ ξ =>
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ ((Matrix.isUnit_iff_isUnit_det _).1 δ.isUnit)
  have hL := GlobalTheory.CompanionTheory.SplitGram.leftInv_subtypeSum V φ
    (fun x : Matrix (Fin V.rank) (Fin r) D.host.E => x.rank = r ∧ gramQ V x = β.1)
    (fun δ hδ ξ h => ⟨(hrank δ ξ).trans h.1, (GlobalTheory.CompanionTheory.SplitGram.gramQ_mul V hδ ξ).trans h.2⟩)
  have hI := average_eq_meanC V ν μH hν hμ 𝓕 h𝓕 _ hL
  have hS : HeckeCharacterZeroLocus.SiegelWeilU.thetaS D.host.F D.host.E D.sp.cm.sig V.rank V.gram (fun X => φ (tupOf X))
      {X | HeckeCharacterZeroLocus.SiegelWeilU.gramE D.sp.cm.sig V.gram X = β.1} =
      fun h => ∑' x : {x : Matrix (Fin V.rank) (Fin r) D.host.E // x.rank = r ∧ gramQ V x = β.1},
        φ (GlobalTheory.SiegelFormula.invPt V h x.1) := by
    funext h
    refine (tsum_congr fun X => ?_).trans ((fibEquiv V β hβ).tsum_eq
      fun x => φ (GlobalTheory.SiegelFormula.invPt V h x.1))
    exact congrArg φ (tupOf_actW V h X.1)
  exact hI.trans (congrArg (HeckeCharacterZeroLocus.SiegelWeilU.meanC μH 𝓕) hS.symm)

end PositivityTheory.PfSWUS.SwMatch

end
end
end

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.SchrodingerMatching.MatchMono

section

@[expose] public section

namespace PositivityTheory.PfSWUS.SwMatch

theorem matchMono : PositivityTheory.PfSWUS.MatchMono :=
  matchMono_of' psiPlaces PositivityTheory.PfSWUS.SwSpanR.realMatch PositivityTheory.PfSWUS.SwSpan.realConj PositivityTheory.PfSWUS.SwFockk.heightWN
    PositivityTheory.PfSWUS.KFinMatch.finite_places_match GlobalTheory.CompanionTheory.IwaRedHand.mod_of_cg valueSide GlobalTheory.T.unfolding_holds GlobalTheory.T.height_K_invariance haarFam

end PositivityTheory.PfSWUS.SwMatch
end
end
