module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TSelF
public import Formalism.LocalToGlobal.ClassOfRecordOfChoice
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ClassOfRecordOfChoice
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.HeckeStdTwOfStd
public import Formalism.SharpRestriction.GlobalTheoremInputs
public import CompanionTheory.AutomorphicTheory.HeckeStandardModules.InvMemRl
public import CompanionTheory.AutomorphicTheory.HeckeStandardModules.HeckeStdStatement
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverF
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverSplit
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverAct
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStdB
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Formalism.LocalToGlobal.IndefiniteRealisationChoice
import Formalism.SharpRestriction.GlobalSchurBounds.QuadraticLogDerivCongr
import Formalism.SharpRestriction.GlobalSchurBounds.TheoremThreeUnderScaleOfGeneral

-- Source module: Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverFP

section

@[expose] public section

open Formalism.BasicNotions

namespace Formalism.L2

theorem linkEtaTw_of_plain {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (hP : HeckeStdPlain)
    (h : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ∃ (M : MtFam (Fm.D x i)) (T : NormalizedLocalCompatibility (Fm.D x i) M),
      HeckeTied (Fm.D x i) M ∧ SplitEx (Fm.D x i)) :
    LocsCoverTwF Fm := by
  obtain ⟨x0, hx⟩ := h
  refine locsCoverTwF_of Fm ⟨x0, fun x hx' i => ?_⟩
  rcases hx x hx' i with ⟨M, T, HT, hex⟩
  exact ⟨M, T, heckeStd_of_plain T hP HT hex (genOutBad_of T)⟩

end Formalism.L2
end
end

-- Source module: Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStdL

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.BasicNotions

namespace Formalism.L2

section Rfl

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]

end Rfl

theorem heckeStdPlain_of_statement (h : ReciprocityTheory.ChartRestriction.L3H.HeckeStdStatement) : HeckeStdPlain := by
  intro L _ _ _ n a J χ B hJo hB s ϖ k hs hu hk1 hk2
  exact h L n a.W a.ρ a.alg J χ B hJo hB s ϖ k hs hu hk1 hk2

theorem linkEtaTw_of_statement {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (h : ReciprocityTheory.ChartRestriction.L3H.HeckeStdStatement)
    (hfam : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ∃ (M : MtFam (Fm.D x i)) (_ : NormalizedLocalCompatibility (Fm.D x i) M),
      HeckeTied (Fm.D x i) M ∧ SplitEx (Fm.D x i)) :
    LocsCoverTwF Fm :=
  linkEtaTw_of_plain Fm (heckeStdPlain_of_statement h) hfam

end Formalism.L2
end
end
end

-- Source module: Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverMain

section

@[expose] public section

open Formalism.BasicNotions NumberField

namespace Formalism.L2

theorem linkEtaTw_main {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (h : ReciprocityTheory.ChartRestriction.L3H.HeckeStdStatement)
    (hfam : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ∃ (M : MtFam (Fm.D x i)) (_ : NormalizedLocalCompatibility (Fm.D x i) M),
      HeckeTied (Fm.D x i) M ∧ ∀ z : (Fm.D x i).host.E, (Fm.D x i).host.conj z = IsCMField.complexConj _ z) :
    LocsCoverTwF Fm := by
  obtain ⟨x0, hx⟩ := hfam
  refine linkEtaTw_of_statement Fm h ⟨x0, fun x hx' i => ?_⟩
  obtain ⟨M, T, HT, hstar⟩ := hx x hx' i
  exact ⟨M, T, HT, splitEx_of_star hstar⟩

end Formalism.L2
end
end

-- Source module: Formalism.LocalToGlobal.NormalizedHeckeFactors.HostConj

section

@[expose] public section

open Formalism.BasicNotions Formalism.FrobeniusOrbits NumberField

namespace Formalism.L2

theorem hostConj_eq_restrict (D : D7) :
    D.host.conj = (IsCMField.complexConj D.host.E).restrictScalars ℚ := by
  symm
  refine (D.host.toHostAx.eq_conjE_iff _).mpr ?_
  let φ : D.host.E →+* ℂ := Classical.choice inferInstance
  exact (D.host.isConj_iff_galE φ _).mp
    (fun x => IsCMField.complexEmbedding_complexConj D.host.E φ x)

theorem hostConj_eq_complexConj (D : D7) :
    ∀ z : D.host.E, D.host.conj z = IsCMField.complexConj D.host.E z := by
  intro z
  rw [hostConj_eq_restrict D]
  rfl

theorem locs_cover_twists_of_hecke {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (h : ReciprocityTheory.ChartRestriction.L3H.HeckeStdStatement)
    (hfam : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ∃ (M : MtFam (Fm.D x i)) (_ : NormalizedLocalCompatibility (Fm.D x i) M),
      HeckeTied (Fm.D x i) M) :
    LocsCoverTwF Fm := by
  obtain ⟨x0, hx⟩ := hfam
  refine linkEtaTw_main Fm h ⟨x0, fun x hx' i => ?_⟩
  obtain ⟨M, T, HT⟩ := hx x hx' i
  exact ⟨M, T, HT, hostConj_eq_complexConj (Fm.D x i)⟩

end Formalism.L2
end
end

-- Source module: Formalism.LocalToGlobal.NormalizedHeckeFactors.EtaClosed

section

@[expose] public section

open Formalism.BasicNotions NumberField

namespace Formalism.L2

theorem linkEtaTw_closed {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)
    (hfam : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ∃ (M : MtFam (Fm.D x i)) (_ : NormalizedLocalCompatibility (Fm.D x i) M),
      HeckeTied (Fm.D x i) M) :
    ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, Formalism.MainNotions.N.LocsCoverTw (Fm.D x i) :=
  locs_cover_twists_of_hecke Fm ReciprocityTheory.ChartRestriction.L3H.heckeStd hfam

theorem linkEta_closed {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)
    (hfam : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ∃ (M : MtFam (Fm.D x i)) (_ : NormalizedLocalCompatibility (Fm.D x i) M),
      HeckeTied (Fm.D x i) M) :
    Formalism.MainNotions.LinkEta Fm := by
  exact linkEtaTw_closed Fm hfam

end Formalism.L2
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkEta

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory Formalism.MainNotions.RT Formalism.L2.Top3 Formalism.L2.Top4
theorem GlobalTheory.Top.closed_linkEta_of_duty : ∀ (𝒜 : FamClass)
    (sel : _root_.Formalism.L2.TwistSelection 𝒜)
    (hduty : ∀ {eps : ℝ} (Fm : FamP eps), 𝒜 Fm → Duty Fm), Closed (D3 3 𝒜) fun Fm _ => LinkEta Fm := by
  intro 𝒜 sel _
  refine Closed.of_class fun Fm _ hc => ?_
  obtain ⟨x0, hx0⟩ := _root_.Formalism.L2.Top3.tied_families_of_choice_alt (sel Fm (d3_a hc))
  refine Formalism.L2.linkEta_closed Fm ⟨max x0 (Fm.x1 + 1), fun x hx i => ?_⟩
  have h1 : Fm.x1 < x := lt_of_lt_of_le (lt_add_one _) ((le_max_right _ _).trans hx)
  obtain ⟨T⟩ := hx0 x h1 ((le_max_left _ _).trans hx) i
  exact ⟨T.n.gal.mt, T.n.cover, T.n.gal.hecke⟩
end
end
end
