module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OffQOfSizeRows
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.PartFixed
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
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselToFourierJacobiNonvanishingTower
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsGoodGridFramesOfDepthFixedStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtYAndItYOfPair
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FockVectorsChainIsVacuumOffThetaLevels
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeisenbergOrientedFiniteFixesFockPolynomialVecto
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CosetVectorsNonzeroDepthFockVacuaStatement
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TowerEx
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockConjugatesSpanDepthDataStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiToBesselNonvanishingTowerStatement
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NonvanishingThetaTowerBottomRungStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselPeriodAscentOfTowerRungs

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

namespace GlobalTheory.Asc

theorem ascent_of_rungs : TowerEx → Rung0 → RungB → RungJ → Ascent := by
  intro hT h0 hB hJ D hq T L μ0 hL sc G W M hM v Ψ hΨ u hu hper
  obtain ⟨F, hE, ΓL, hG⟩ := hT D hq T L μ0 hL sc G W M hM v
  have key : ∀ k (h : 2 * k + 2 ≤ D.R.m), NZB W M v F Ψ u k h := by
    intro k
    induction k with
    | zero =>
      intro h
      exact hB D hq T L μ0 hL sc G W M hM v F ΓL hE hG Ψ hΨ u hu 0 h
        (h0 D hq T L μ0 hL sc G W M hM v F ΓL hE hG Ψ hΨ u hu hper h)
    | succ k ih =>
      intro h
      have h' : 2 * k + 2 ≤ D.R.m := by omega
      exact hB D hq T L μ0 hL sc G W M hM v F ΓL hE hG Ψ hΨ u hu (k + 1) h
        (hJ D hq T L μ0 hL sc G W M hM v F ΓL hE hG Ψ hΨ u hu k h h' (ih h'))
  obtain ⟨r, hr⟩ := D.R.m_even
  have h2 := D.R.two_le_m
  have hk : 2 * (r - 1) + 2 ≤ D.R.m := by omega
  have hk' : 2 * (r - 1) + 2 = D.R.m := by omega
  obtain ⟨ρ, Φ, hne⟩ := key (r - 1) hk
  refine ⟨ρ, Φ, ?_⟩
  let f : ∀ i, Fn G (.grid i 0) := fun i => if hi : i ≤ D.R.m then part W M ρ Φ u i hi else 0
  have hf : f D.R.m = thetaChi W M ρ Φ u := by
    simp only [f, dif_pos le_rfl]; rfl
  have := hE.top (r - 1) hk hk' Ψ f (hΨ.1 _ le_rfl) (by rw [hf, ← part_m]; exact hu ρ Φ _ le_rfl) (by
    simp only [f, dif_pos hk]; exact hne)
  rwa [hf] at this

end GlobalTheory.Asc
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselPeriodAscentOfTowerRungsStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

theorem _root_.GlobalTheory.T.besselPeriod_ascent_of_tower_rungs : TowerEx → Rung0 → RungB → RungJ → Ascent := by
  first | exact @GlobalTheory.Asc.ascent_of_rungs | exact GlobalTheory.Asc.ascent_of_rungs | (intros; apply GlobalTheory.Asc.ascent_of_rungs <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselToFourierJacobiNonvanishingTowerStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

theorem _root_.GlobalTheory.T.bessel_to_fourierJacobi_nonvanishing_tower : FockTot → PartFixed → RungJ := by
  first | exact @GlobalTheory.Asc.RungJac.rungJ | exact GlobalTheory.Asc.RungJac.rungJ | (intros; apply GlobalTheory.Asc.RungJac.rungJ <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstRowDataHaveDepth

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.FirstRowDepth

theorem datumDep : GlobalTheory.SepRows.DatumDep := by
  intro D hq T L μ0 hL sc G W M hM ρ Φ i
  obtain ⟨-, ⟨hth, hlat⟩, -⟩ := GlobalTheory.T.coset_vectors_nonzero_depth_fock_vacua D hq T L μ0 hL sc G W M hM i.1 i.2 (Φ i)
  have hthP : ∀ P, IsThetaFunO W.ψ (G.pS (.chi i.1 0)) (G.pT (.chi i.1 0))
      (W.fock (.chi i.1 0) (W.cosVec i (Φ i)) P) := fun P =>
    GlobalTheory.Chain.InnerSteps.theta_pureTensorO W.ψ_std W.θ_is _ _ _ _ hth P
  refine ⟨hthP (ρ i), fun u hu => ?_, fun e he u hu hh => ?_⟩
  · exact GlobalTheory.Hk3.FiniteHeis.heisO_pureTensorO_of_finite W.ψ W.θ _ _ W.θ_is _ _ _ _ _ hthP (2 • u)
      (GlobalTheory.VacGood.infPart_latO (AddSubgroup.nsmul_mem _ hu 2).1) (hlat.1 u hu) (ρ i)
  · exact GlobalTheory.Hk3.FiniteHeis.heisO_pureTensorO_of_finite W.ψ W.θ _ _ W.θ_is _ _ _ _ _ hthP u
      (GlobalTheory.VacGood.infPart_latO hu.1) (hlat.2 e he u hu hh) (ρ i)

end GlobalTheory.FirstRowDepth

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstRowDataHaveDepthStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

theorem _root_.GlobalTheory.T.firstRow_data_have_depth : GlobalTheory.SepRows.DatumDep := by
  first | exact @GlobalTheory.FirstRowDepth.datumDep | exact GlobalTheory.FirstRowDepth.datumDep | (intros; apply GlobalTheory.FirstRowDepth.datumDep <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridLiftsFixedByCongruenceDepthOfDepthData

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

noncomputable section

namespace GlobalTheory.Asc

theorem partFixed_of_depFixed : DepFixed → DatumDep → PartFixed := by
  intro hD hd D q T L μ0 hL sc G W M hM ρ Φ u i h k hk g
  have hf := hd D q T L μ0 hL sc G W M hM ρ Φ ⟨i, h⟩
  have key := hD D q T L μ0 hL sc G W M hM i h (.chi i 0) (Or.inl rfl) _ hf 1 (one_mem _) k hk
  show liftA W M (.right i 0) (W.datum ρ Φ ⟨i, h⟩) _ (g * k) = liftA W M (.right i 0) (W.datum ρ Φ ⟨i, h⟩) _ g
  rw [liftA_apply, liftA_apply]
  congr 1
  funext x
  congr 1
  show W.om (.chi i 0) (negGA _ (g * k), x) _ 0 = W.om (.chi i 0) (negGA _ g, x) _ 0
  have e : ((negGA _ (g * k), x) : GA D (G.pS (.chi i 0)) × GA D (G.pT (.chi i 0))) =
      (negGA _ g, x) * G.toPair (.chi i 0) 1 k := by
    show _ = (negGA _ g, x) * (negGA _ k, 1)
    rw [map_mul, Prod.mk_mul_mk, mul_one]
  rw [e, map_mul, Module.End.mul_apply, key]

end GlobalTheory.Asc

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridLiftsFixedByCongruenceDepthOfDepthDataStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

theorem _root_.GlobalTheory.T.gridLiftsFixedByCongruenceDepth_of_depthData : DepFixed → DatumDep → PartFixed := by
  first | exact @GlobalTheory.Asc.partFixed_of_depFixed | exact GlobalTheory.Asc.partFixed_of_depFixed | (intros; apply GlobalTheory.Asc.partFixed_of_depFixed <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselPeriodNonvanishingAscentOfDepthData

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

namespace GlobalTheory.Asc

theorem ascent_of_depFixed : DepFixed → Ascent := fun hD =>
  have hTot : FockTot := GlobalTheory.T.fockConjugates_span_depth_data
  have hPart : PartFixed := GlobalTheory.T.gridLiftsFixedByCongruenceDepth_of_depthData hD GlobalTheory.T.firstRow_data_have_depth
  GlobalTheory.T.besselPeriod_ascent_of_tower_rungs (GlobalTheory.T.existsGoodGridFrames_of_depthFixed hD) (GlobalTheory.T.nonvanishing_thetaTower_bottom_rung hTot) (GlobalTheory.T.fourierJacobi_to_bessel_nonvanishing_tower hTot hPart)
    (GlobalTheory.T.bessel_to_fourierJacobi_nonvanishing_tower hTot hPart)

end GlobalTheory.Asc
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselPeriodNonvanishingAscentOfDepthDataStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

theorem _root_.GlobalTheory.T.bessel_period_nonvanishing_ascent_of_depth_data : DepFixed → Ascent := by
  first | exact @GlobalTheory.Asc.ascent_of_depFixed | exact GlobalTheory.Asc.ascent_of_depFixed | (intros; apply GlobalTheory.Asc.ascent_of_depFixed <;> assumption)
end
end
