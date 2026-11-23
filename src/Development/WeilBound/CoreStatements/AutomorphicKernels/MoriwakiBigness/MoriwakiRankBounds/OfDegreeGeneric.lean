module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.MoriwakiBigness.MoriwakiRankBounds.Development
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Statements
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.KleimanGenericPointSectionInput
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.KleimanInputNefAmpleSectionCount
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.PCoordCurveAlgebraic
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
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsKleimanScheme
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ProjDefs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDimensionalChartLattice
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.TendstoFinrankVeryAmple
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PCutRegular
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.IsMultiHomogIdealIff
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AssemblyBase
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ExistsLinearIndependentOfGenerates
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.ReduceModChar
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsKodairaGeneric
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSectionLatticeFinite
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PChartDenominator
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PKodairaSection
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PLiftBirationalNef
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNefOnGenericOfSemipos
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNefPlusAmpleDegree
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionLatticeFinite
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPerturb
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PFsLineLevi
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PFsLineSmooth
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCoordNeZero

section

@[expose] public section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry GroundTheory.Heights₂.Heights.HilbertSamuel Filter Topology

namespace GlobalTheory.CompanionTheory.Ar.Relevant

theorem exists_coord_ne_zero :
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
      (y : (Σ k, ι k) → Ω) (D : ℕ), IsArithVar (mCoordIdeal y) (D + 1) → ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 := by
  intro K _ ι _ Ω _ _ y D hP k
  obtain ⟨i, hi⟩ := hP.2.1.2.2 k
  exact ⟨i, fun h0 => hi (GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet.CoordCurveDegree.X_mem_of_eq_zero h0)⟩

end GlobalTheory.CompanionTheory.Ar.Relevant
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBigIffGenDeg

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter

noncomputable section

namespace BigIffGenDeg

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem charZero_of_isArithVar {y : (Σ k, ι k) → Ω} {d : ℕ} (h : IsArithVar (mCoordIdeal y) d) : CharZero Ω := by
  refine charZero_of_inj_zero fun n hn => ?_
  have hmem : ((n : ℤ)) ∈ (mCoordIdeal y).comap (C : ℤ →+* MRing ι) := by
    show mConeMap y (C (n : ℤ)) = 0
    rw [map_natCast C n, map_natCast, ← map_natCast (MvPolynomial.C : Ω →+* MvPolynomial K Ω), hn, map_zero]
  rw [h.2.2.1] at hmem
  exact_mod_cast (Ideal.mem_bot.mp hmem)

theorem coord_ne_zero_of_isArithVar {y : (Σ k, ι k) → Ω} {d : ℕ} (h : IsArithVar (mCoordIdeal y) d) :
    ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 := by
  intro k
  obtain ⟨i, hi⟩ := h.2.1.2.2 k
  refine ⟨i, fun h0 => hi ?_⟩
  show mConeMap y (X ⟨k, i⟩) = 0
  simp [mConeMap, h0]

end BigIffGenDeg

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsChartLatRank

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def ChartLatRank.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (a : K → ℤ) (n : ℕ),
    (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) →
      Module.finrank ℤ (AddSubgroup.toIntSubmodule (chartLat y a n)) = Module.finrank ℚ (chartLatQ y a n)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PChartLatRank

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

theorem chartLat_subset_chartLatQ {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
    [CharZero Ω] (y : (Σ k, ι k) → Ω) (a : K → ℤ) (n : ℕ) {s : Ω} (hs : s ∈ chartLat y a n) :
    s ∈ chartLatQ y a n := by
  intro c hc
  have hle : chartRingZ y c ≤ (chartRingQ y c).restrictScalars ℤ :=
    Algebra.adjoin_le (Algebra.subset_adjoin (R := ℚ))
  exact hle (hs c hc)

theorem ChartLatRank.proof (hfin : SectionLatticeFinite.Statement) : ChartLatRank.Statement := by
  intro K _ ι _ Ω _ _ y a n hy
  classical
  set M := AddSubgroup.toIntSubmodule (chartLat y a n) with hM
  have hfg : M.FG := (Submodule.fg_iff_addSubgroup_fg M).mpr (hfin K ι Ω y a n hy)
  have : Module.Finite ℤ M := Module.Finite.iff_fg.mpr hfg
  obtain ⟨r, b⟩ := Module.basisOfFiniteTypeTorsionFree' (R := ℤ) (M := M)
  set v : Fin r → Ω := fun i => ((b i : M) : Ω) with hv
  have hvZ : LinearIndependent ℤ v := b.linearIndependent.map' M.subtype M.ker_subtype
  have hvQ : LinearIndependent ℚ v := (LinearIndependent.iff_fractionRing ℤ ℚ).mp hvZ
  have hspan : Submodule.span ℚ (Set.range v) = chartLatQ y a n := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact chartLat_subset_chartLatQ y a n (b i).2
    · intro s hs
      obtain ⟨N, hN, hNs⟩ := ChartDenominator.proof K ι Ω y a n s hs
      have hmemM : (⟨(N : Ω) * s, hNs⟩ : M) ∈ Submodule.span ℤ (Set.range b) := b.mem_span _
      have hmemZ : (N : Ω) * s ∈ Submodule.span ℤ (Set.range v) := by
        have h := Submodule.mem_map_of_mem (f := M.subtype) hmemM
        rw [Submodule.map_span, ← Set.range_comp] at h
        exact h
      have hmemQ : (N : Ω) * s ∈ Submodule.span ℚ (Set.range v) :=
        Submodule.span_le_restrictScalars ℤ ℚ _ hmemZ
      have hN0 : (N : Ω) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
      have hs' : s = ((N : ℚ)⁻¹) • ((N : Ω) * s) := by
        rw [Rat.smul_def]
        push_cast
        field_simp
      rw [hs']
      exact Submodule.smul_mem _ _ hmemQ
  rw [Module.finrank_eq_card_basis b, ← hspan, finrank_span_eq_card hvQ]

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSemiposTwist

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

noncomputable section

theorem SemiposTwist.proof : SemiposTwist.Statement := by
  intro K _ ι _ P0 P L p q hL
  set U : Set ((Σ k, ι k) → ℂ) := {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} with hU
  have hUo : IsOpen U := by
    have e : U = ⋂ k, ⋃ i, {z : (Σ k, ι k) → ℂ | z ⟨k, i⟩ ≠ 0} := by
      ext z
      simp [hU]
    rw [e]
    exact isOpen_iInter_of_finite fun k =>
      isOpen_iUnion fun i => (continuous_apply _).isOpen_preimage _ isOpen_ne
  have hH : IsSmoothHerm (fsH ι) := FsLineSmooth.proof K ι
  have hsm : IsSmoothHerm (HermLine.zcomb L (fsH ι) q p) := by
    have e : (HermLine.zcomb L (fsH ι) q p).h = fun z => L.h z ^ q * (fsH ι).h z ^ p := by
      funext z
      show L.h z ^ (q : ℤ) * (fsH ι).h z ^ (p : ℤ) = _
      rw [zpow_natCast, zpow_natCast]
    unfold IsSmoothHerm
    rw [e]
    exact (hL.1.pow q).mul (hH.pow p)
  refine ⟨hsm, fun z hz w hw => ?_⟩
  have hzU : z ∈ U := hz.1
  have hlog : ∀ A : HermLine ι, IsSmoothHerm A → ContDiffAt ℝ 2 (fun y => Real.log (A.h y)) z :=
    fun A hA => ((hA.contDiffAt (hUo.mem_nhds hzU)).of_le (WithTop.coe_le_coe.2 le_top)).log
      (A.pos z hzU).ne'
  have h1 := hlog L hL.1
  have h2 := hlog (fsH ι) hH
  have hev : (fun y => Real.log ((HermLine.zcomb L (fsH ι) q p).h y)) =ᶠ[𝓝 z]
      fun y => (0 + (q : ℝ) * Real.log (L.h y)) + (p : ℝ) * Real.log ((fsH ι).h y) := by
    filter_upwards [hUo.mem_nhds hzU] with y hy
    show Real.log (L.h y ^ (q : ℤ) * (fsH ι).h y ^ (p : ℤ)) = _
    rw [Real.log_mul (zpow_pos (L.pos y hy) _).ne' (zpow_pos ((fsH ι).pos y hy) _).ne',
      Real.log_zpow, Real.log_zpow]
    push_cast
    ring
  have hLz : 0 ≤ ReciprocityTheory.AnForm.levi (fun y => Real.log (L.h y)) z w := hL.2 z hz w hw
  have hHz : 0 ≤ ReciprocityTheory.AnForm.levi (fun y => Real.log ((fsH ι).h y)) z w :=
    FsLineLevi.proof K ι z w hzU
  have e1 := ReciprocityTheory.AnForm.levi_add_smul (f := fun y => 0 + (q : ℝ) * Real.log (L.h y))
    (g := fun y => Real.log ((fsH ι).h y)) (p : ℝ) (contDiffAt_const.add (contDiffAt_const.mul h1)) h2 w
  have e2 := ReciprocityTheory.AnForm.levi_add_smul (f := fun _ => (0 : ℝ))
    (g := fun y => Real.log (L.h y)) (q : ℝ) contDiffAt_const h1 w
  have hl0 : ReciprocityTheory.AnForm.levi (fun _ => (0 : ℝ)) z w = 0 := by simp [ReciprocityTheory.AnForm.levi]
  change 0 ≤ ReciprocityTheory.AnForm.levi _ z w
  rw [ReciprocityTheory.AnForm.levi_congr hev, e1, e2, hl0]
  have a1 := mul_nonneg (Nat.cast_nonneg (α := ℝ) q) hLz
  have a2 := mul_nonneg (Nat.cast_nonneg (α := ℝ) p) hHz
  linarith

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
end

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.MoriwakiBigness.MoriwakiRankBounds.OfDegreeGeneric

section

@[expose] public section

namespace PositivityTheory.Pf1.MbRank

open MvPolynomial Filter Topology
open GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (secOver mIdealOver chartRingOver)
open GlobalTheory.CompanionTheory.Hypotheses₂.NefVolume GroundTheory.Heights₂.Heights.ForSecondHalf

noncomputable section

theorem ShiftSectionsRankB.of_degreeGeneric (hDG : GroundTheory.Heights₂.Heights.Inter.DegreeGeneric.Statement) :
    ShiftSectionsRankB.Statement := by
  intro K _ ι _ Ω _ y D A P0 hV hB hP0 hs q hq
  classical
  have := BigIffGenDeg.charZero_of_isArithVar hV
  have hy := BigIffGenDeg.coord_ne_zero_of_isArithVar hV
  set N := HermLine.zcomb A (fsH ι) (q : ℤ) 1 with hN
  have hR : ChartLatRank.Statement :=
    ChartLatRank.proof (SectionLatticeFinite.proof Closed.ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cond)
  have hrk : ∀ n : ℕ, (Module.finrank ℤ (chartLat y N.a n) : ℝ) = Module.finrank ℚ (chartLatQ y N.a n) :=
    fun n => by exact_mod_cast hR K ι Ω y N.a n hy
  obtain rfl | ⟨d, rfl⟩ : D = 0 ∨ ∃ d, D = d + 1 := by
    rcases D with _ | d
    · exact Or.inl rfl
    · exact Or.inr ⟨d, rfl⟩
  · have hconst : (fun n : ℕ => (Module.finrank ℤ (chartLat y N.a n) : ℝ) /
        ((n : ℝ) ^ 0 / ((Nat.factorial 0 : ℕ) : ℝ))) = fun _ => (genDeg (mCoordIdeal y) 0 N.a : ℝ) := by
      funext n
      rw [hrk n, ← SectionsDimZero.full K ι Ω y N.a n (by simpa using hV)]
      simp
    rw [hconst]
    exact tendsto_const_nhds
  · have hsN : IsSemipositiveRel P0 (mCoordIdeal y) N := by
      have h := SemiposTwist.proof K ι P0 (mCoordIdeal y) A 1 q hs
      simpa [hN] using h
    have hNef : NefOnGenericDeg (mCoordIdeal y) N.a :=
      nefOnGenericDeg_of_semipos NefOnGenericOfSemipos.proof hDG hP0 hsN
    set a := N.a with ha
    obtain ⟨hK, hS⟩ := (GlobalTheory.CompanionTheory.Relay.kleiman_input_nef_ample_section_count GlobalTheory.CompanionTheory.Relay.kleiman_genericPointSectionInput).2
    have : Nonempty K := hV.1
    have hI : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.genIdeal y = mIdealOver ℚ y := LiftBirationalNef.genIdeal_eq y
    have hP := isProjVarF_map_of_isArithVar hV
    have hnz := GlobalTheory.CompanionTheory.Ar.Relevant.exists_coord_ne_zero K ι Ω y (d + 1) hV
    have hdim : FieldNumbers.relDim (mIdealOver ℚ y) = ((d + 1 : ℕ) : WithBot (WithTop ℤ)) :=
      hI ▸ (FieldNumbers.CutRegular.relDim_eq_natCast_iff _ (d + 1)).2 hP.2
    have hnef : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman2.IsNef ℚ y a := fun W hW hle hW1 =>
      NefPlusAmpleDegree.nefOnF_of_nefOnGenericDeg hNef W
        ⟨(Bridge.isMultiProjPrime_iff W).mp hW, (FieldNumbers.CutRegular.relDim_eq_natCast_iff W 1).1 hW1⟩
        (hI.le.trans hle)
    have hfinQ : ∀ b, FiniteDimensional ℚ (chartLatQ y b 1) := fun b =>
      GlobalTheory.CompanionTheory.GenericFibre.finiteDimensional_chartLatQ K ι Ω y (d + 1) b hV
    have hfd : ∀ b, FiniteDimensional ℚ (secOver ℚ y b) := fun b => by
      rw [← chartLatQ_eq_secOver]
      exact hfinQ b
    have hsh : ∀ M : ℕ, ∃ C : ℝ, ∀ᶠ n : ℕ in atTop,
        (Module.finrank ℚ (secOver ℚ y ((n : ℤ) • a + fun _ => (M : ℤ))) : ℝ) ≤
          (Module.finrank ℚ (secOver ℚ y ((n : ℤ) • a)) : ℝ) + C * (n : ℝ) ^ d := by
      intro M
      obtain ⟨C, hC⟩ := shiftSectionBound K ι Ω y (d + 1) a M (by omega) hV hB
      refine ⟨C, hC.mono fun n hn => ?_⟩
      have h := hn.2
      rw [Nat.add_sub_cancel, chartLatQ_eq_secOver, chartLatQ_eq_secOver] at h
      exact h
    have hlim := tendsto_finrank_nef hK hS hnz hdim hnef hfd hsh
    set F : ℝ := ((d + 1).factorial : ℝ) with hF
    have hfac : F ≠ 0 := by rw [hF]; exact_mod_cast (Nat.factorial_pos _).ne'
    have hgen : (genDeg (mCoordIdeal y) (d + 1) a : ℝ) =
        F * ((NumbersDVR.intNum ℚ (mIdealOver ℚ y) (fun _ : Fin (d + 1) => a) : ℝ) / F) := by
      rw [mul_div_cancel₀ _ hfac, ← hI]
      rfl
    rw [hgen]
    refine (hlim.const_mul F).congr' (Eventually.of_forall fun n => ?_)
    simp only
    rw [hrk n, ← chartLatQ_smul, chartLatQ_eq_secOver, div_div_eq_mul_div]
    ring

theorem ShiftSectionsRankUpper.of_degreeGeneric (hDG : GroundTheory.Heights₂.Heights.Inter.DegreeGeneric.Statement) :
    ShiftSectionsRankUpper.Statement :=
  ShiftSectionsRankUpper.of_B (ShiftSectionsRankB.of_degreeGeneric hDG)

end

end PositivityTheory.Pf1.MbRank
end
end
