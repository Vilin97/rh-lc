module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HasPartAnd
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CmGoodModelOfGlobalArtinReciprocity
public import Formalism.LocalToGlobal.InertKernelTheory.DefsRepDict
public import Formalism.LocalToGlobal.InertKernelTheory.GenusOneModelExistsLattice
public import Formalism.LocalToGlobal.InertKernelTheory.StatementAlgT
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaSeriesDataHypothesesBelowMaximalLevel
public import Formalism.LocalToGlobal.InertKernelTheory.StatementInt
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AtOfTrueColumns
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepRepEqOneAtTypePrimes
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThreeLeSplitAt
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RowTwUHolds
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TuplesHaveLocalModelsAtConstructedPointOverTrueCStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OneSubTwoOmegaSq
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsRingEquivTranscendental
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertThetaAdmissibilityOfComplexMultiplication
public import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.Statement
public import Formalism.LocalToGlobal.InertKernelTheory.KernelsIntegralInert
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Tactic.Linter.HaveILetI
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TorsionTaylorAlgebraicLatticeExistsOfCm

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelDatumConditionsAtStandardKernelComparison

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Svd NumberField IsDedekindDomain

namespace GlobalTheory.PdvTie

theorem at_of_stdTie : Formalism.L2.KerInert.AlgTAll → Formalism.L2.KerInert.GenusOneModelExistsLattice → Formalism.L2.KerInert.Rep.CurveDict → Formalism.L2.KerInert.IntInert → ∀ (D : D7) (O : Obj D) (t : KerEntTied O.ex), StdTie D O t → 3 ≤ D.host.splitBound → 5 ≤ O.K.dl1 → 4 ≤ O.K.dl2 → (∀ Ee : OrbitPlaces.Ent D, OrbitPlaces.Shape D O.L O.Gx Ee ∧ ∀ u, ∀ j < D.R.m, ∀ s ∈ D.host.TT, Ee.row u j (false, s) 0 - Ee.row u j (false, s) 1 ≤ 2 * O.L.sc.a) → GlobalTheory.Pdv.At O.ex t.ent := by
  intro hA hG hC hI D O t hT hs h1 h2 hE
  refine StdTie.ind (R := fun D O t => 3 ≤ D.host.splitBound → 5 ≤ O.K.dl1 → 4 ≤ O.K.dl2 →
      (∀ Ee : OrbitPlaces.Ent D, OrbitPlaces.Shape D O.L O.Gx Ee ∧ ∀ u, ∀ j < D.R.m, ∀ s ∈ D.host.TT, Ee.row u j (false, s) 0 - Ee.row u j (false, s) 1 ≤ 2 * O.L.sc.a) →
      GlobalTheory.Pdv.At O.ex t.ent) ?_ hT hs h1 h2 hE
  intro B X I l l0 Z O t h hs h1 h2 hE
  exact GlobalTheory.PdvClose.at_of_true_columns hA hG hC hI I h.ok h.pins l Z l0 O.L O.gatT O.Gx O.Gy O.K O.X O.cX O.ex t
    (GlobalTheory.Pdv.colNorm_of_tw I h.isTw) h.jets h.tw h.ker h.entC h.adapted h.top hs h1 h2 hE

end GlobalTheory.PdvTie
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelDatumConditionsAtStandardKernelComparisonStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Svd NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.kernelDatumConditions_at_standardKernelComparison : Formalism.L2.KerInert.AlgTAll → Formalism.L2.KerInert.GenusOneModelExistsLattice → Formalism.L2.KerInert.Rep.CurveDict → Formalism.L2.KerInert.IntInert → ∀ (D : D7) (O : Obj D) (t : KerEntTied O.ex), StdTie D O t → 3 ≤ D.host.splitBound → 5 ≤ O.K.dl1 → 4 ≤ O.K.dl2 → (∀ Ee : OrbitPlaces.Ent D, OrbitPlaces.Shape D O.L O.Gx Ee ∧ ∀ u, ∀ j < D.R.m, ∀ s ∈ D.host.TT, Ee.row u j (false, s) 0 - Ee.row u j (false, s) 1 ≤ 2 * O.L.sc.a) → GlobalTheory.Pdv.At O.ex t.ent := by
  first | exact @GlobalTheory.PdvTie.at_of_stdTie | exact GlobalTheory.PdvTie.at_of_stdTie | (intros; apply GlobalTheory.PdvTie.at_of_stdTie <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.RowAtOfStdTie

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Svd NumberField IsDedekindDomain

namespace GlobalTheory.Pdv

theorem rowAt_of_stdTie : Formalism.L2.KerInert.AlgTAll → Formalism.L2.KerInert.GenusOneModelExistsLattice → Formalism.L2.KerInert.Rep.CurveDict → Formalism.L2.KerInert.IntInert → ∀ {Bd : BdT} (Q : V4.Slot) (Lk : LkT Bd) (ker : ∀ (D : D7) (O : Obj D) (c : ℝ), Bd D O c → KerEntTied O.ex), RowE Q Lk (fun _ D O c b => StdTie D O (ker D O c b)) → Row Q Lk (AtAll fun D O c b => GlobalTheory.Pdv.At O.ex (ker D O c b).ent) := by
  intro hA hG hD hI Bd Q Lk ker hE
  choose x0 hx0 using GlobalTheory.ShapeUniform.shape_uniform
  refine ⟨fun κ D O c b => x0 κ.eps ≤ O.L.sc.x ∧ StdTie D O (ker D O c b), ?_, ?_⟩
  · have h1 : RowE Q Lk (fun κ D O _ _ => x0 κ.eps ≤ O.L.sc.x) := by
      unfold RowE EvP
      refine ParEv.of_all fun κ _ => ⟨x0 κ.eps, fun K hk hx β _ c b _ => ?_⟩
      show x0 κ.eps ≤ β.p.L.sc.x
      rw [β.sc]
      exact hx
    exact (h1.and hE).mono fun _ _ _ H => H
  · intro 𝒜 σ s eps Fm hc x hx i
    obtain ⟨κ, hl, _, ht⟩ := s Fm hc
    obtain ⟨_, h0, hst⟩ := ht x hx i
    have hxx : (Fm.L x i).sc.x = x := Fm.L_x x i hx
    have hge : x0 eps ≤ x := by
      have h0' : x0 κ.eps ≤ (Fm.L x i).sc.x := h0
      rw [hl.eps_eq, hxx] at h0'
      exact h0'
    have hsh := hx0 eps Fm x hge hx i
    have hsb : 3 ≤ (Fm.D x i).host.splitBound :=
      (hsh (OrbitPlaces.ofKer (nuRowOK (Fm.D x i)) (ker _ _ _ (σ Fm hc x hx i)).ent (fun _ => 0) (fun _ _ => 0) (fun _ _ => 0))).2.2
    exact GlobalTheory.T.kernelDatumConditions_at_standardKernelComparison hA hG hD hI (Fm.D x i) (objAt Fm x hx i) (ker _ _ _ (σ Fm hc x hx i)) hst hsb
      Fm.fixed.2.1.ge Fm.fixed.2.2.1.ge (fun Ee => ⟨(hsh Ee).1, (hsh Ee).2.1⟩)

end GlobalTheory.Pdv
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.BundleBothPartsOfStandardKernelAndSixHypotheses

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Svd NumberField IsDedekindDomain

namespace GlobalTheory.Svd

theorem servH_row (hA : Formalism.L2.KerInert.AlgTAll) (hG : Formalism.L2.KerInert.GenusOneModelExistsLattice) (hC : Formalism.L2.KerInert.Rep.CurveDict)
    (hI : Formalism.L2.KerInert.IntInert) (hE : GlobalTheory.TwV.Lt.AdmAtEnt2) (hX : GlobalTheory.TwV.Lt.CurveEx) :
    ∀ {Bd : BdT} (Q : V4.Slot) (Lk : LkT Bd) (ker : ∀ (D : D7) (O : Obj D) (c : ℝ), Bd D O c → KerEntTied O.ex),
      (∀ K X f T c, Q K X f T c → positionOf HasPart K X f T c) →
      RowE Q Lk (fun _ D O c b => StdTie D O (ker D O c b)) → Row Q Lk (ServH ker) := by
  intro Bd Q Lk ker hQ hT
  have hM : RowE Q Lk (fun _ D O _ _ => ModelsAt D O) :=
    RowE.of_all fun _ K β _ _ _ hq _ => GlobalTheory.T.tuplesHaveLocalModels_at_constructedPoint_over_trueColumns hE hX K β (hQ _ _ _ _ _ hq)
  exact Row.and (GlobalTheory.Svd.rowTwU Q Lk hM) (GlobalTheory.Pdv.rowAt_of_stdTie hA hG hC hI Q Lk ker hT)

end GlobalTheory.Svd
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.BundleBothPartsOfStandardKernelAndSixHypothesesStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Svd NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.bundle_bothParts_of_standardKernel_and_six_hypotheses : Formalism.L2.KerInert.AlgTAll → Formalism.L2.KerInert.GenusOneModelExistsLattice → Formalism.L2.KerInert.Rep.CurveDict → Formalism.L2.KerInert.IntInert → GlobalTheory.TwV.Lt.AdmAtEnt2 → GlobalTheory.TwV.Lt.CurveEx → ∀ {Bd : BdT} (Q : V4.Slot) (Lk : LkT Bd) (ker : ∀ (D : D7) (O : Obj D) (c : ℝ), Bd D O c → KerEntTied O.ex), (∀ K X f T c, Q K X f T c → positionOf HasPart K X f T c) → RowE Q Lk (fun _ D O c b => StdTie D O (ker D O c b)) → Row Q Lk (ServH ker) := by
  first | exact @GlobalTheory.Svd.servH_row | exact GlobalTheory.Svd.servH_row | (intros; apply GlobalTheory.Svd.servH_row <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsGenusOneFormalIsoOfUnramifiedGoodReduction

section

@[expose] public section

namespace GlobalTheory.TwV.Lt

theorem curveEx_of_cm (h2 : Formalism.L2.Th1.CM.CM2) (h3 : Formalism.L2.Th1.CM.CM3) : CurveEx := by
  intro D cc δ B χ hc hd hχ p _ hcop h5 hIn lam
  obtain ⟨g, hgl, hAt, hM, hLT⟩ :=
    GlobalTheory.InertGenusOne.datum_exists_coprime h2 h3 D cc δ hc hd p hcop h5 hIn lam
  exact ⟨g, hLT, h5, hAt, hIn, hM, hc, hd, hχ, hgl.symm, hAt.2.2.2.1⟩

theorem exists_genusOne_formal_iso_of_unramified_good_reduction (h : Formalism.L2.Th1.CM.CM2) : CurveEx :=
  curveEx_of_cm h GlobalTheory.HondaCM3.cm3

end GlobalTheory.TwV.Lt
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntInertOfComplexMultiplicationCondition

section

@[expose] public section

namespace GlobalTheory

theorem intInert_of_complexMultiplication_condition : Formalism.L2.Th1.CM.CM2 → Formalism.L2.KerInert.IntInert :=
  fun h => by
    haveI : Fact Formalism.L2.Th1.CM.CM2 := ⟨h⟩
    exact Formalism.L2.KerInert.kernels_integral_inert

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.BundleBothPartsOfStandardKernelOfGlobalArtinReci

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Svd NumberField IsDedekindDomain

namespace GlobalTheory.Svd

theorem servH_row_of_artin :
    GlobalTheory.Published.GlobalArtinReciprocity → ∀ {Bd : BdT} (Q : V4.Slot) (Lk : LkT Bd)
      (ker : ∀ (D : D7) (O : Obj D) (c : ℝ), Bd D O c → KerEntTied O.ex),
      (∀ K X f T c, Q K X f T c → positionOf HasPart K X f T c) →
      RowE Q Lk (fun _ D O c b => StdTie D O (ker D O c b)) → Row Q Lk (ServH ker) := by
  intro hA Bd Q Lk ker hQ hE
  have h2 : Formalism.L2.Th1.CM.CM2 := GlobalTheory.Corev.CmTwoClosing.cmGoodModel_of_globalArtinReciprocity hA
  obtain ⟨hT, hG, hC⟩ := GlobalTheory.CurveThetaInert.torsionTaylorAlgebraic_latticeExists_of_cm h2
  exact GlobalTheory.T.bundle_bothParts_of_standardKernel_and_six_hypotheses hT hG hC (GlobalTheory.intInert_of_complexMultiplication_condition h2) (GlobalTheory.TwV.Lt.inert_theta_admissibility_of_complex_multiplication h2)
    (GlobalTheory.TwV.Lt.exists_genusOne_formal_iso_of_unramified_good_reduction h2) Q Lk ker hQ hE

end GlobalTheory.Svd
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.BundleBothPartsOfStandardKernelOfGlobalArtinReciStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Svd NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.bundle_bothParts_of_standardKernel_of_globalArtinReciprocity : GlobalTheory.Published.GlobalArtinReciprocity → ∀ {Bd : BdT} (Q : V4.Slot) (Lk : LkT Bd) (ker : ∀ (D : D7) (O : Obj D) (c : ℝ), Bd D O c → KerEntTied O.ex), (∀ K X f T c, Q K X f T c → positionOf HasPart K X f T c) → RowE Q Lk (fun _ D O c b => StdTie D O (ker D O c b)) → Row Q Lk (ServH ker) := by
  first | exact @GlobalTheory.Svd.servH_row_of_artin | exact GlobalTheory.Svd.servH_row_of_artin | (intros; apply GlobalTheory.Svd.servH_row_of_artin <;> assumption)
end
end
