module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedBasesBlockTriangularOfReducedEtaleFiltratStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralBlock
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralCrystallineBlockDataOfReductionPair
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WachLatticesRankOneModelsReducedFiltration

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralCrystallineBlockDataOfReductionPairStatement

section

@[expose] public section

open NumberField GlobalTheory.ExpFrame

theorem _root_.GlobalTheory.T.integralCrystallineBlockData_of_reductionPair : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (n t : ℕ) (J : (E →+* PadicAlgCl l) → Fin n → ℤ) (bot : (E →+* PadicAlgCl l) → ℤ), BlockPair E Ω l n t J bot → GlobalTheory.WachBlock.IntegralBlock E Ω l n t J bot := by
  first | exact @GlobalTheory.WachBlock.integralBlock_of_blockPair | exact GlobalTheory.WachBlock.integralBlock_of_blockPair | (intros; apply GlobalTheory.WachBlock.integralBlock_of_blockPair <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.WachLatticesRankOneModelsReducedFiltrationStatement

section

@[expose] public section

open NumberField GlobalTheory.ExpFrame

theorem _root_.GlobalTheory.T.wachLattices_rankOne_models_reducedFiltration : GlobalTheory.Published.BhattScholzeCrystallineLattices → ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 → ¬ (l : ℤ) ∣ NumberField.discr E → ∀ (σ : Equiv.Perm (E →+* PadicAlgCl l)), IsFrobPerm σ → ∀ (n t h : ℕ) (J : (E →+* PadicAlgCl l) → Fin n → ℤ) (bot : (E →+* PadicAlgCl l) → ℤ), (∀ i a, 0 ≤ J i a ∧ J i a ≤ h) → (∀ i (s : Fin t), 0 ≤ bot i + ((s : ℕ) : ℤ) ∧ bot i + ((s : ℕ) : ℤ) ≤ h) → GlobalTheory.WachBlock.IntegralBlock E Ω l n t J bot → ∃ (O' F L' : Type) (_ : CommRing O') (_ : IsDomain O') (_ : Algebra ℤ_[l] O') (_ : Field F) (_ : CharP F l) (_ : Field L') (I : Ideal O') (_ : IsAdicComplete I O') (red : O' →+* F) (un : PowerSeries O') (N : Formalism.CohomologicalDescent.FrobeniusPeriodChange.Lat (E →+* PadicAlgCl l) n O') (Npsi : Fin t → Formalism.CohomologicalDescent.FrobeniusPeriodChange.Lat (E →+* PadicAlgCl l) 1 O') (u : ℤ_[l]ˣ) (c : ℤ_[l]) (ζ : O') (em : O' →+* L') (jj : ℕ → PowerSeries O' →+* PowerSeries L'), ((u : ℤ_[l]) = 1 + (l : ℤ_[l]) * c ∧ IsUnit c ∧ Formalism.CohomologicalDescent.FrobeniusPeriodChange.IsUn l O' (u : ℤ_[l]) un) ∧ (IsPrimitiveRoot ζ l ∧ ζ - 1 ∈ I ∧ Function.Injective em ∧ ∀ b ∈ Finset.Ioo 0 l, Formalism.CohomologicalDescent.FrobeniusPeriodChange.IsLocExp l O' L' em (ζ ^ b - 1) (u : ℤ_[l]) (jj b)) ∧ Formalism.CohomologicalDescent.FrobeniusPeriodChange.LatN l N h u J em jj ∧ (∀ s, Formalism.CohomologicalDescent.FrobeniusPeriodChange.LatN l (Npsi s) h u (fun i _ => bot i + ((s : ℕ) : ℤ)) em jj) ∧ GlobalTheory.WachBlock.RedFilt σ l (PowerSeries.map red un) (fun i => (N.P i).map (PowerSeries.map red)) (fun i => (N.D i).map (PowerSeries.map red)) (fun s i => PowerSeries.map red ((Npsi s).P i 0 0)) (fun s i => PowerSeries.map red ((Npsi s).D i 0 0)) := by
  first | exact @GlobalTheory.WachPlace.wach_lattices | exact GlobalTheory.WachPlace.wach_lattices | (intros; apply GlobalTheory.WachPlace.wach_lattices <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineBlockLatticesOverPowerSeriesRing

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.DIV GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization

namespace GlobalTheory.WachBlock

theorem wach_inputs : GlobalTheory.Published.BhattScholzeCrystallineLattices → ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 → ¬ (l : ℤ) ∣ NumberField.discr E → ∀ (σ : Equiv.Perm (E →+* PadicAlgCl l)), IsFrobPerm σ → ∀ (n t h : ℕ) (J : (E →+* PadicAlgCl l) → Fin n → ℤ) (bot : (E →+* PadicAlgCl l) → ℤ), (∀ i a, 0 ≤ J i a ∧ J i a ≤ h) → (∀ i (s : Fin t), 0 ≤ bot i + ((s : ℕ) : ℤ) ∧ bot i + ((s : ℕ) : ℤ) ≤ h) → BlockPair E Ω l n t J bot → ∃ (O' F L' : Type) (_ : CommRing O') (_ : IsDomain O') (_ : Algebra ℤ_[l] O') (_ : Field F) (_ : CharP F l) (_ : Field L') (I : Ideal O') (_ : IsAdicComplete I O') (Wl : Formalism.CohomologicalDescent.FrobeniusPeriodChange.WLat (E →+* PadicAlgCl l) t n O' F) (u : ℤ_[l]ˣ) (c : ℤ_[l]) (kap : (E →+* PadicAlgCl l) → Fin t → ℤ) (ζ : O') (em : O' →+* L') (jj : ℕ → PowerSeries O' →+* PowerSeries L'), Formalism.CohomologicalDescent.FrobeniusPeriodChange.NInputs Wl σ l h u c J (fun i s => bot i + ((s : ℕ) : ℤ)) kap I ζ em jj := by
  intro hBS E Ω _ _ _ _ _ _ l _ hl2 hdisc σ hσ n t h J bot hJ hbot hBP
  obtain ⟨O', F, L', i1, i2, i3, i4, i5, i6, I, i7, red, un, N, Npsi, u, c, ζ, em, jj, hU, hR, hN, hψ, hF⟩ :=
    GlobalTheory.T.wachLattices_rankOne_models_reducedFiltration hBS E Ω l hl2 hdisc σ hσ n t h J bot hJ hbot (GlobalTheory.T.integralCrystallineBlockData_of_reductionPair E Ω l n t J bot hBP)
  obtain ⟨g, b, pos, w, kap, hpos, hP, hG, hPd, hGd⟩ :=
    GlobalTheory.T.adaptedBases_blockTriangular_of_reducedEtaleFiltration _ σ l n t F _ _ _ _ _ (Fact.out : l.Prime).pos inferInstance hF
  exact ⟨O', F, L', i1, i2, i3, i4, i5, i6, I, i7, ⟨red, un, N, Npsi, g, b, pos, w⟩, u, c, kap, ζ, em, jj,
    ⟨hU, hJ, hbot, hpos, hP, hG, hPd, hGd⟩, hR, hN, hψ⟩

end GlobalTheory.WachBlock

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineBlockLatticesOverPowerSeriesRingStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.L2.DIV GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization

theorem _root_.GlobalTheory.T.crystalline_block_lattices_over_power_series_ring : GlobalTheory.Published.BhattScholzeCrystallineLattices → ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 → ¬ (l : ℤ) ∣ NumberField.discr E → ∀ (σ : Equiv.Perm (E →+* PadicAlgCl l)), IsFrobPerm σ → ∀ (n t h : ℕ) (J : (E →+* PadicAlgCl l) → Fin n → ℤ) (bot : (E →+* PadicAlgCl l) → ℤ), (∀ i a, 0 ≤ J i a ∧ J i a ≤ h) → (∀ i (s : Fin t), 0 ≤ bot i + ((s : ℕ) : ℤ) ∧ bot i + ((s : ℕ) : ℤ) ≤ h) → BlockPair E Ω l n t J bot → ∃ (O' F L' : Type) (_ : CommRing O') (_ : IsDomain O') (_ : Algebra ℤ_[l] O') (_ : Field F) (_ : CharP F l) (_ : Field L') (I : Ideal O') (_ : IsAdicComplete I O') (Wl : Formalism.CohomologicalDescent.FrobeniusPeriodChange.WLat (E →+* PadicAlgCl l) t n O' F) (u : ℤ_[l]ˣ) (c : ℤ_[l]) (kap : (E →+* PadicAlgCl l) → Fin t → ℤ) (ζ : O') (em : O' →+* L') (jj : ℕ → PowerSeries O' →+* PowerSeries L'), Formalism.CohomologicalDescent.FrobeniusPeriodChange.NInputs Wl σ l h u c J (fun i s => bot i + ((s : ℕ) : ℤ)) kap I ζ em jj := by
  first | exact @GlobalTheory.WachBlock.wach_inputs | exact GlobalTheory.WachBlock.wach_inputs | (intros; apply GlobalTheory.WachBlock.wach_inputs <;> assumption)
end
end
