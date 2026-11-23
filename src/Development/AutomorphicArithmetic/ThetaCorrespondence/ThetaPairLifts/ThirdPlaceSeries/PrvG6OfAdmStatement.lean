module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HeckeCharEqOfLAdicRealisation
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspidalGaloisUnramified
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AbsIrreducibleConstituentRanksUniqueOfCharpoly
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EigencharacterOfSummandCharZero
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIrreducibleConstituentsCharpolyProductStatement
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ValuationRingModelStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MemZAndCuspOfStepsStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MuCharHolds
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ResidueCountOfSsRank
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeCharEqOfLAdicRealisation
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.ResidualIrreducibleOfTheorem
import Mathlib.Tactic.Basify
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SixthDecomposition
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SixthWeightStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.AbsIrreducibleConstituentRanksUniqueOfCharpolyStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition

theorem _root_.GlobalTheory.T.absIrreducible_constituent_ranks_unique_of_charpoly : SSRankUnique := by
  first | exact @GlobalTheory.SSRank.ssRankUnique_holds | exact GlobalTheory.SSRank.ssRankUnique_holds | (intros; apply GlobalTheory.SSRank.ssRankUnique_holds <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.EigencharacterOfSummandCharZeroStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition

theorem _root_.GlobalTheory.T.eigencharacter_of_summand_charZero : EigenCharTwist := by
  first | exact @GlobalTheory.eigenCharTwist_holds | exact GlobalTheory.eigenCharTwist_holds | (intros; apply GlobalTheory.eigenCharTwist_holds <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.StringRankOneLengthAndMultisetSumSingleton

section

@[expose] public section

open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition

namespace GlobalTheory.SixthNumerics

theorem numerics : Numerics := by
  intro r t d n a A hr ht had hw hsum hpos hn hle
  have hd : d = t + 2 * a := by omega
  have hA : A ≠ 0 := by
    rintro rfl
    simp at hsum
    omega
  have hmem : ∀ x ∈ A, x = 1 := by
    intro x hx
    have h1 := Multiset.count_le_of_le x hle
    rw [Multiset.count_nsmul] at h1
    have hc : 1 ≤ Multiset.count x A := Multiset.one_le_count_iff_mem.mpr hx
    have h2 : d ≤ Multiset.count x (r ::ₘ Multiset.replicate t 1) :=
      le_trans (by nlinarith) h1
    by_contra hx1
    rw [Multiset.count_cons, Multiset.count_replicate] at h2
    split_ifs at h2 <;> omega
  have hrep : A = Multiset.replicate (Multiset.card A) 1 := Multiset.eq_replicate_card.mpr hmem
  have hcard : 1 ≤ Multiset.card A := Multiset.card_pos.mpr hA
  have h1 := Multiset.count_le_of_le 1 hle
  rw [Multiset.count_nsmul, Multiset.count_cons, Multiset.count_replicate_self] at h1
  have hc1 : Multiset.count 1 A = Multiset.card A := by
    conv_lhs => rw [hrep]
    exact Multiset.count_replicate_self _ _
  rw [hc1] at h1
  have hr1 : (1 : ℕ) ≠ r := by omega
  simp [hr1] at h1
  have hsum' : n = Multiset.card A := by
    rw [← hsum, hrep]; simp
  have : Multiset.card A = 1 := by nlinarith
  refine ⟨by omega, ?_⟩
  have : a = 0 := by nlinarith
  omega

theorem rest : Rest := by
  intro ι _ d A r hd hA hs
  have hc := congrArg Multiset.card hs
  have hc' : ∑ k, d k * Multiset.card (A k) = 1 := by
    rw [Multiset.card_sum] at hc
    simpa [Multiset.card_nsmul] using hc
  have hterm : ∀ k, 1 ≤ d k * Multiset.card (A k) := fun k =>
    Nat.mul_le_mul (hd k) (Multiset.card_pos.mpr (hA k))
  have hle : ∀ k, d k * Multiset.card (A k) = 1 := by
    intro k
    have := Finset.single_le_sum (f := fun k => d k * Multiset.card (A k))
      (fun i _ => Nat.zero_le _) (Finset.mem_univ k)
    have := hterm k
    omega
  have hcardle : Fintype.card ι ≤ 1 := by
    have := Finset.card_nsmul_le_sum Finset.univ (fun k => d k * Multiset.card (A k)) 1
      (fun k _ => hterm k)
    simp at this
    omega
  have hne : Nonempty ι := by
    by_contra h
    rw [not_nonempty_iff] at h
    simp at hs
  have hcard : Fintype.card ι = 1 := le_antisymm hcardle Fintype.card_pos
  refine ⟨hcard, fun k => ?_⟩
  have hdk : d k = 1 := Nat.eq_one_of_mul_eq_one_right (hle k)
  refine ⟨hdk, ?_⟩
  have hsub : Subsingleton ι := Fintype.card_le_one_iff_subsingleton.mp hcardle
  rw [Finset.sum_eq_single k (fun b _ hb => absurd (Subsingleton.elim b k) hb)
    (fun h => absurd (Finset.mem_univ k) h), hdk, one_smul] at hs
  exact hs

theorem numerics_and_rest : Numerics ∧ Rest := ⟨numerics, rest⟩

end GlobalTheory.SixthNumerics
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.StringRankOneLengthAndMultisetSumSingletonStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition

theorem _root_.GlobalTheory.T.stringRankOneLength_and_multisetSumSingleton : Numerics ∧ Rest := by
  first | exact @GlobalTheory.SixthNumerics.numerics_and_rest | exact GlobalTheory.SixthNumerics.numerics_and_rest | (intros; apply GlobalTheory.SixthNumerics.numerics_and_rest <;> assumption)
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SixthCharacterEqualityHoldsAltAlt

section

@[expose] public section



section
noncomputable section
namespace GlobalTheory.HeckeCharacterEquality
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition
theorem sixth_character_equality_holds_alt_alt : _root_.GlobalTheory.StringRepresentationDecomposition.HeckeCharEqOfLAdicRealisation' := by
  intro D hA i χ χ' s ρ h h'
  have hAN := hA.1.1.2.2.2.2.2.2.1
  have hloc : ∀ w, w ∉ placesOver D.host.E (D.nd.l i) → D.naut.locG χ w = D.naut.locG χ' w := by
    intro w hw
    have e := congrArg (fun a => D.naut.lpTw a (-s)) ((h w hw).symm.trans (h' w hw))
    simpa [D.naut.lpTw_add, D.naut.lpTw_zero] using e
  have hp := hAN [⟨1, χ, 1⟩] [⟨1, χ', 1⟩] (by simp) (by simp) (by
    have hfin := placesOver_finite_joint_conditions_zpowers D.host.E (D.nd.l i) (D.nd.lPrime i).out.ne_zero
    filter_upwards [hfin.compl_mem_cofinite] with w hw
    simp only [isoLoc, spehLoc, List.foldr]
    rw [hloc w hw])
  have := List.perm_singleton.1 hp
  simpa using this
end GlobalTheory.HeckeCharacterEquality
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SixthCharacterEqualityHoldsStatement

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition

theorem _root_.GlobalTheory.T.hecke_char_eq_of_l_adic_realisation : _root_.GlobalTheory.StringRepresentationDecomposition.HeckeCharEqOfLAdicRealisation' := by
  first | exact @_root_.GlobalTheory.HeckeCharacterEquality.sixth_character_equality_holds_alt_alt | exact _root_.GlobalTheory.HeckeCharacterEquality.sixth_character_equality_holds_alt_alt | (intros; apply _root_.GlobalTheory.HeckeCharacterEquality.sixth_character_equality_holds_alt_alt <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PrvG6OfAdm

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition
namespace GlobalTheory.ClosingSixth
theorem conclusionG6_of_adm_alt : ∀ D : D7, _root_.Formalism.MainNotions.SumRepresentations.AdmissibleDatum D → RbEx D → SumRepresentations.ConclusionG6 D :=
  _root_.GlobalTheory.T.prvG6_of_admissible_of_g6_decomposition _root_.GlobalTheory.T.centred_string_decomposition _root_.GlobalTheory.T.purity_string_weight _root_.GlobalTheory.T.hecke_char_eq_of_l_adic_realisation _root_.UpperTheory.GalS.muChar_holds_alt GlobalTheory.T.eigencharacter_of_summand_charZero
    (_root_.GlobalTheory.T.resCount_of_valRing_ssList_ssRank GlobalTheory.T.valuation_ring_model GlobalTheory.T.exists_irreducible_constituents_charpoly_product GlobalTheory.T.absIrreducible_constituent_ranks_unique_of_charpoly)
    GlobalTheory.T.stringRankOneLength_and_multisetSumSingleton.1 GlobalTheory.T.stringRankOneLength_and_multisetSumSingleton.2
end GlobalTheory.ClosingSixth
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PrvG6OfAdmStatement

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition

theorem _root_.GlobalTheory.T.prvG6_of_admissible' : ∀ D : D7, _root_.Formalism.MainNotions.SumRepresentations.AdmissibleDatum D → RbEx D → SumRepresentations.ConclusionG6 D := by
  first | exact @_root_.GlobalTheory.ClosingSixth.conclusionG6_of_adm_alt | exact _root_.GlobalTheory.ClosingSixth.conclusionG6_of_adm_alt | (intros; apply _root_.GlobalTheory.ClosingSixth.conclusionG6_of_adm_alt <;> assumption)
end
end
end
