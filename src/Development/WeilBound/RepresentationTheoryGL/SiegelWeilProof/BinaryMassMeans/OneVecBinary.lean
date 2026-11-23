module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.LowRankSiegelDensities.SiegelDensitiesLowAOf
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.UnitaryGroupFiniteVolume
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SiegelWeilUnitaryConvergentOfSiegelWeilConvergen
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCuspidalNeZero
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SiegelSetUnitary
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
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CountingFormula
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EquidistributionStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HassePrincipleStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeftSideFormula
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalMassFormulaStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeanValueFormulaStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormThetaMul
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.EulerProductMeasureZeroStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianOneByOneIsScalarStatement
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SimilitudeInvarianceStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TestFunctionExists
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VectorLengthFormulaOfParts
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.SingleRowSide.Srside

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Cocompactness

section

@[expose] public section

noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU PositivityTheory.Rg.Mass

namespace GlobalTheory.CompanionTheory.MassCocompact

theorem coCpt : CoCpt := by
  intro F E _ _ _ _ _ σ J d b li lam μ 𝓕 mi m hCM hJ hA _ _ hμ h𝓕 _ _
  have hW : GlobalTheory.SiegelSet.IsWittFrame σ J (0 : Matrix (Fin 2) (Fin 0) E) 0 :=
    ⟨Subsingleton.elim _ _, Subsingleton.elim _ _, Subsingleton.elim _ _, fun z _ _ hz => hA z hz⟩
  obtain ⟨C, hC, hcov⟩ := GlobalTheory.SiegelSet.Model.compact_quotient GlobalTheory.CompanionTheory.SiegelRed.siegelSetUnitary hCM hJ hW
  refine ⟨⟨C, hC, fun h => ?_⟩, ?_, ?_⟩
  · obtain ⟨γ, hγ, c, hc, e⟩ := hcov h
    exact ⟨⟨γ, hγ⟩, c, hc, e⟩
  · exact (GlobalTheory.SiegelWeilConvCompare.measure_fundamentalDomain_pos F E σ 2 J μ hμ 𝓕 h𝓕).ne'
  · exact (((GlobalTheory.CompanionTheory.SW.finVol_unitaryGroup F E σ hCM 2 J hJ).2 μ hμ).2 𝓕 h𝓕).ne

end GlobalTheory.CompanionTheory.MassCocompact

end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CocompactnessStatement

section

@[expose] public section

open PositivityTheory.Rg.Mass

theorem _root_.GlobalTheory.T.cocompactness : CoCpt := by
  first | exact @GlobalTheory.CompanionTheory.MassCocompact.coCpt | exact GlobalTheory.CompanionTheory.MassCocompact.coCpt | (intros; apply GlobalTheory.CompanionTheory.MassCocompact.coCpt <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CountingFormulaStatement

section

@[expose] public section

open PositivityTheory.Rg.Mass

theorem _root_.GlobalTheory.T.counting_formula : TestEx → LSide → RSide → Cnt := by
  first | exact @GlobalTheory.CompanionTheory.RgMass.cnt | exact GlobalTheory.CompanionTheory.RgMass.cnt | (intros; apply GlobalTheory.CompanionTheory.RgMass.cnt <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeftSideFormulaStatement

section

@[expose] public section

open PositivityTheory.Rg.Mass

theorem _root_.GlobalTheory.T.left_side_formula : Equi → CoCpt → LSide := by
  first | exact @GlobalTheory.CompanionTheory.SW.LS.lside | exact GlobalTheory.CompanionTheory.SW.LS.lside | (intros; apply GlobalTheory.CompanionTheory.SW.LS.lside <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormThetaMulStatement

section

@[expose] public section

open PositivityTheory.Rg.Mass

theorem _root_.GlobalTheory.T.counting_bound_alt : CountBd := by
  first | exact @GlobalTheory.CompanionTheory.MassCount.countBd | exact GlobalTheory.CompanionTheory.MassCount.countBd | (intros; apply GlobalTheory.CompanionTheory.MassCount.countBd <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OneVectorFormulaOfParts

section

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open PositivityTheory.Rg.Mass

namespace GlobalTheory.CompanionTheory.Mass

theorem anisotropic_binary_one_vector_formula : Prop1 → Simil → Hasse → Cnt → E1 := by
  intro hP hS hH hC F E _ _ _ _ _ σ hcm J hJ hA T hT hd d b li lam hli hlam μ 𝓕 hμ h𝓕 mi m hmi hm
  obtain ⟨β, rfl, hβ, he⟩ := GlobalTheory.T.hermitian_one_by_one_is_scalar F E σ hcm T hT
  have hβ0 : β ≠ 0 := hβ hd
  simp only [he]
  have hsph : {X : Fin 1 → Fin 2 → E | gramE σ J X = fun _ _ => algebraMap F E β} = sph σ J β := rfl
  rw [hsph]
  obtain ⟨c, hc⟩ := hP F E σ J d b li lam μ 𝓕 mi m hcm hJ hA hli hlam hμ h𝓕 hmi hm β hβ0
  by_cases h0 : mi (hermScal (Ainf F) σ (algebraMap F _ β)) = 0 ∨
      ∃ v, m v (hermScal (Fv F v) σ (algebraMap F _ β)) = 0
  · rw [(GlobalTheory.T.euler_product_measure_zero F E σ hcm d b 1 2 _ c _ _).2.1 hc h0]
    exact (GlobalTheory.T.euler_product_measure_zero F E σ hcm d b 1 2 0 1 _ _).2.2 hc.1 hc.2.1 h0
  push Not at h0
  have hne : (sph σ J β).Nonempty :=
    hH F E σ J d b li lam μ 𝓕 mi m hcm hJ hA hli hlam hμ h𝓕 hmi hm β hβ0 h0.1
  have hall : ∀ β' : F, β' ≠ 0 → EP b μ 𝓕 mi m β' c := by
    intro β' hβ'
    by_cases hn : (sph σ J β').Nonempty
    · exact hS F E σ J d b li lam μ 𝓕 mi m hcm hJ hA hli hlam hμ h𝓕 hmi hm β β' hβ0 hβ' hne hn c hc
    · obtain ⟨c', hc'⟩ := hP F E σ J d b li lam μ 𝓕 mi m hcm hJ hA hli hlam hμ h𝓕 hmi hm β' hβ'
      have hz : mi (hermScal (Ainf F) σ (algebraMap F _ β')) = 0 := by
        by_contra hz
        exact hn (hH F E σ J d b li lam μ 𝓕 mi m hcm hJ hA hli hlam hμ h𝓕 hmi hm β' hβ' hz)
      have ht : thetaMeas σ J μ 𝓕 (sph σ J β') = 0 := by
        have he' : IsEmpty (sph σ J β') := Set.not_nonempty_iff_eq_empty.1 hn ▸ inferInstance
        simp [thetaMeas]
      unfold EP
      rw [ht]
      exact (GlobalTheory.T.euler_product_measure_zero F E σ hcm d b 1 2 0 c _ _).2.2 hc'.1 hc'.2.1 (Or.inl hz)
  have h1 : c = 1 := hC F E σ J d b li lam μ 𝓕 mi m hcm hJ hA hli hlam hμ h𝓕 hmi hm c hall
  exact h1 ▸ hc

end GlobalTheory.CompanionTheory.Mass
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OneVectorFormulaOfPartsStatement

section

@[expose] public section

open PositivityTheory.Rg.Mass

theorem _root_.GlobalTheory.T.one_vector_formula_of_parts : Prop1 → Simil → Hasse → Cnt → E1 := by
  first | exact @GlobalTheory.CompanionTheory.Mass.anisotropic_binary_one_vector_formula | exact GlobalTheory.CompanionTheory.Mass.anisotropic_binary_one_vector_formula | (intros; apply GlobalTheory.CompanionTheory.Mass.anisotropic_binary_one_vector_formula <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TestFunctionExistsStatement

section

@[expose] public section

open PositivityTheory.Rg.Mass

theorem _root_.GlobalTheory.T.test_function_exists : TestEx := by
  first | exact @GlobalTheory.CompanionTheory.SW.MassTest.testEx | exact GlobalTheory.CompanionTheory.SW.MassTest.testEx | (intros; apply GlobalTheory.CompanionTheory.SW.MassTest.testEx <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VectorLengthFormulaOfPartsStatement

section

@[expose] public section

open PositivityTheory.Rg.Mass

theorem _root_.GlobalTheory.T.vector_length_formula_of_parts : CoCpt → LocMass → Prop1 := by
  first | exact @GlobalTheory.CompanionTheory.Mass.One.vector_length_formula_up_to_constant | exact GlobalTheory.CompanionTheory.Mass.One.vector_length_formula_up_to_constant | (intros; apply GlobalTheory.CompanionTheory.Mass.One.vector_length_formula_up_to_constant <;> assumption)
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.OneVecBinary

section

@[expose] public section

namespace PositivityTheory.Rg.Mass

theorem e1 : E1 :=
  GlobalTheory.T.one_vector_formula_of_parts (GlobalTheory.T.vector_length_formula_of_parts GlobalTheory.T.cocompactness GlobalTheory.T.local_mass_formula) GlobalTheory.T.similitude_invariance GlobalTheory.T.hasse_principle
    (GlobalTheory.T.counting_formula GlobalTheory.T.test_function_exists (GlobalTheory.T.left_side_formula GlobalTheory.T.equidistribution GlobalTheory.T.cocompactness)
      (PositivityTheory.Rg.Mass.LiteralAutomorphy.srside (GlobalTheory.T.mean_value_formula GlobalTheory.T.equidistribution GlobalTheory.T.counting_bound_alt) GlobalTheory.T.local_mass_formula))

theorem oneVecBinary : PositivityTheory.PfSWUS.HMass.OneVecBinary := by
  intro F E _ _ _ _ _ σ hc M J hJ hM hA T hT hd
  subst hM
  exact e1 F E σ hc J hJ (fun x hx => by_contra fun h => hA x h hx) T hT hd

end PositivityTheory.Rg.Mass
end
end
