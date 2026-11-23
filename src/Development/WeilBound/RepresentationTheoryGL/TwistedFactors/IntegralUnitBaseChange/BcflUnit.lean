module

public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.InvTransposeGLInvTransposeGL
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.Development
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeFirstPropertyStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeFourthPropertyStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeSecondPropertyStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeThirdPropertyStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormCentralizerIdentificationStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormCommutesSeparableHoldsStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormMapFirstPropertyStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormMapIntegralPropertyStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormMapSecondPropertyStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormMapThirdPropertyStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormMapTorusSurjectiveStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SeparableNormCommuting
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentHeckeFourthPropertyStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentHeckeSupportStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitFundamentalLemmaFirstHolds
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedDictionaryPartBStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedDualFamilyHoldsStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedExtensionIntegralBasis

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeThirdProperty

section

@[expose] public section

namespace GlobalTheory.CompanionTheory.TwistedCent

open PositivityTheory.Rg.Tf.Loc

theorem mem_twCent_twConj_iff {G : Type} [Group G] (θ : Monoid.End G) (g δ x : G) :
    x ∈ twCent θ (twConj θ g δ) ↔ g * x * g⁻¹ ∈ twCent θ δ := by
  rw [mem_twCent, mem_twCent]
  simp only [twConj, map_mul, map_inv]
  constructor
  · intro h
    calc (g * x * g⁻¹)⁻¹ * δ * (θ g * θ x * (θ g)⁻¹)
        = g * (x⁻¹ * (g⁻¹ * δ * θ g) * θ x) * (θ g)⁻¹ := by group
      _ = g * (g⁻¹ * δ * θ g) * (θ g)⁻¹ := by rw [h]
      _ = δ := by group
  · intro h
    calc x⁻¹ * (g⁻¹ * δ * θ g) * θ x
        = g⁻¹ * ((g * x * g⁻¹)⁻¹ * δ * (θ g * θ x * (θ g)⁻¹)) * θ g := by group
      _ = g⁻¹ * δ * θ g := by rw [h]

theorem h3 : PositivityTheory.Rg.Tf.Loc.H3 := fun _ _ θ g δ x => mem_twCent_twConj_iff θ g δ x

end GlobalTheory.CompanionTheory.TwistedCent
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeThirdPropertyStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.hecke_third_property : PositivityTheory.Rg.Tf.Loc.H3 := by
  first | exact @GlobalTheory.CompanionTheory.TwistedCent.h3 | exact GlobalTheory.CompanionTheory.TwistedCent.h3 | (intros; apply GlobalTheory.CompanionTheory.TwistedCent.h3 <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SeparableNormCommutingStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.separable_norm_commuting : PositivityTheory.Rg.Tf.Loc.A1 := by
  first | exact @GlobalTheory.CompanionTheory.Centraliser.a1 | exact GlobalTheory.CompanionTheory.Centraliser.a1 | (intros; apply GlobalTheory.CompanionTheory.Centraliser.a1 <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitFundamentalLemmaFirstHoldsStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.unit_fundamental_lemma_first_holds : PositivityTheory.Rg.Tf.Loc.D0a → PositivityTheory.Rg.Tf.Loc.T0 → PositivityTheory.Rg.Tf.Loc.A1 → PositivityTheory.Rg.Tf.Loc.A2 → PositivityTheory.Rg.Tf.Loc.A3 → PositivityTheory.Rg.Tf.Loc.N4 → PositivityTheory.Rg.Tf.Loc.L2 → PositivityTheory.Rg.Tf.Loc.L3 → PositivityTheory.Rg.Tf.Loc.L4 → PositivityTheory.Rg.Tf.Loc.H2 → PositivityTheory.Rg.Tf.Loc.H3 → PositivityTheory.Rg.Tf.Loc.H4 → PositivityTheory.Rg.Tf.Loc.Z1 := by
  first | exact @GlobalTheory.CompanionTheory.UnitFL.unit_fundamental_lemma_first | exact GlobalTheory.CompanionTheory.UnitFL.unit_fundamental_lemma_first | (intros; apply GlobalTheory.CompanionTheory.UnitFL.unit_fundamental_lemma_first <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitFundamentalLemmaSecondHolds

section

@[expose] public section

open MeasureTheory PositivityTheory.Rg.Tf.Loc
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.UnitFL

theorem unit_fundamental_lemma_second : PositivityTheory.Rg.Tf.Loc.L2 → PositivityTheory.Rg.Tf.Loc.N4 → PositivityTheory.Rg.Tf.Loc.Z2 := by
  intro hL2 hN4
  unfold PositivityTheory.Rg.Tf.Loc.Z2
  intro k E _ _ _ _ _ _ _ _ _ _ _ _ hun σ hgen n _ _ _ _ μE μk _ _ _ _ γ μγ _ hnot _
  have hno : ∀ g : GL (Fin n) k, g⁻¹ * γ * g ∉ unitGL (n := Fin n) k := by
    intro g hg
    obtain ⟨c, -, -, hc⟩ := hN4 k E hun σ hgen n γ (hL2.1 k n γ ⟨g, hg⟩)
    exact hnot ⟨c, 1, by simpa using hc⟩
  have hzero : (fun g : GL (Fin n) k => unitFn (n := Fin n) k (g⁻¹ * γ * g)) = fun _ => 0 := by
    funext g
    exact Set.indicator_of_notMem (hno g) _
  unfold orbIntegral quotLIntegral
  rw [hzero]
  split_ifs <;> simp

end GlobalTheory.CompanionTheory.UnitFL
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitFundamentalLemmaSecondHoldsStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.unit_fundamental_lemma_second_holds : PositivityTheory.Rg.Tf.Loc.L2 → PositivityTheory.Rg.Tf.Loc.N4 → PositivityTheory.Rg.Tf.Loc.Z2 := by
  first | exact @GlobalTheory.CompanionTheory.UnitFL.unit_fundamental_lemma_second | exact GlobalTheory.CompanionTheory.UnitFL.unit_fundamental_lemma_second | (intros; apply GlobalTheory.CompanionTheory.UnitFL.unit_fundamental_lemma_second <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedExtensionIntegralBasisStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.unramified_extension_integral_basis : PositivityTheory.Rg.Tf.Loc.D0a := by
  first | exact @GlobalTheory.CompanionTheory.UnramDict.unramifiedDictionary_a | exact GlobalTheory.CompanionTheory.UnramDict.unramifiedDictionary_a | (intros; apply GlobalTheory.CompanionTheory.UnramDict.unramifiedDictionary_a <;> assumption)
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.QuotientIntegralOfCompactOpen

section

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PositivityTheory.Rg.Tf.Loc

theorem quotient_integral_of_compact_open (hT : T0) (h : QuotientIntegralCompactOpen) : H2 := by
  intro F _ _ _ _ n _ _ μG H μH h1 h2 h3 h4 Fn _ h5 h6 Rp h7 h8
  obtain ⟨-, -, ho, hc⟩ := hT.1 F n
  exact h F n μG H μH (unitGL F) ho hc h1 h2 h3 h4 Fn h5 h6 Rp h7 h8

theorem measure_transport_of_open_set (hT : T0) (hD : D0a) (h : MeasureTransportOpenSet) : H4 := by
  intro k E _ _ _ _ _ _ _ _ _ _ _ _ hun σ hgen n _ _ _ _ δ γ hh μδ μγ h1 h2 h3 y z hz
  exact h k E hun σ hgen n (unitGL E : Subgroup (GL (Fin n) E)) (unitGL k : Subgroup (GL (Fin n) k))
    (hT.1 E n).2.2.1 (fun g => (hD k E hun σ hgen).2.2.1 n g) δ γ hh μδ μγ h1 h2 h3 y z hz

theorem bcflUnit_of_leaves (hD0a : D0a) (hD0b : D0a → IntegralBasisUnramified) (hD0c : IntegralBasisUnramified → TraceOneIntegralElement) (hT0 : T0) (hA1 : A1)
    (hA2 : A1 → A2) (hA3 : A2 → A3) (hN1 : N1) (hN2 : N2) (hN3 : N1 → N2 → N3)
    (hN4 : D0a → IntegralBasisUnramified → TraceOneIntegralElement → N3 → N4) (hL1 : L1) (hL2 : D0a → L2) (hL3 : TraceOneIntegralElement → L1 → L3)
    (hL4 : D0a → A1 → L4) (hH2U : QuotientIntegralCompactOpen) (hH3 : H3) (hH4U : D0a → T0 → A1 → MeasureTransportOpenSet)
    (hZ1 : D0a → T0 → A1 → A2 → A3 → N4 → L2 → L3 → L4 → H2 → H3 → H4 → Z1)
    (hZ2 : L2 → N4 → Z2) : BCFLUnit := by
  have b := hD0b hD0a
  have c := hD0c b
  have a2 := hA2 hA1
  have n4 := hN4 hD0a b c (hN3 hN1 hN2)
  have l2 := hL2 hD0a
  have z1 := hZ1 hD0a hT0 hA1 a2 (hA3 a2) n4 l2 (hL3 c hL1) (hL4 hD0a hA1) (quotient_integral_of_compact_open hT0 hH2U) hH3
    (measure_transport_of_open_set hT0 hD0a (hH4U hD0a hT0 hA1))
  have z2 := hZ2 l2 n4
  intro k E
  intros
  exact ⟨by apply z1 <;> assumption, by apply z2 <;> assumption⟩

end PositivityTheory.Rg.Tf.Loc
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.BcflUnit

section

@[expose] public section

namespace PositivityTheory.Rg.Tf.Loc

theorem bcflUnit : BCFLUnit :=
  bcflUnit_of_leaves GlobalTheory.T.unramified_extension_integral_basis GlobalTheory.T.integralBasisUnramified_of_d0a GlobalTheory.T.unramified_dual_family_holds GlobalTheory.T.norm_map_torus_surjective GlobalTheory.T.separable_norm_commuting GlobalTheory.T.norm_commutes_separable_holds GlobalTheory.T.norm_centralizer_identification GlobalTheory.T.norm_map_first_property GlobalTheory.T.norm_map_second_property GlobalTheory.T.norm_map_third_property GlobalTheory.T.norm_map_integral_property GlobalTheory.T.lattice_first_property GlobalTheory.T.lattice_second_property GlobalTheory.T.lattice_third_property GlobalTheory.T.lattice_fourth_property GlobalTheory.T.unipotent_hecke_support GlobalTheory.T.hecke_third_property GlobalTheory.T.unipotent_hecke_fourth_property GlobalTheory.T.unit_fundamental_lemma_first_holds GlobalTheory.T.unit_fundamental_lemma_second_holds

end PositivityTheory.Rg.Tf.Loc
end
end
