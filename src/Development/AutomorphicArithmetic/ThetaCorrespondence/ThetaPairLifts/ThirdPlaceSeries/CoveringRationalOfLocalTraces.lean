module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Realised
public import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralFormsEqSpanIntegralRationalFormsStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
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
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ChiMulPsiInvMemCore

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalCoverBound

section

@[expose] public section

open NumberField

namespace GlobalTheory.CovTop

open GlobalTheory.BigTop Formalism.IndefR.FWT

variable {D : Formalism.BasicNotions.D7} {L : Formalism.BasicNotions.SizeData₂ D} {hT : Formalism.BasicNotions.GatTies D} {Gi : Formalism.MainNotions.G.Inst D L}
  {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y0 : Formalism.BasicNotions.DivX D} {cX : Formalism.BasicNotions.ExtraC}
  {ex : Formalism.BasicNotions.Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ}

theorem rho_mem_WK (p : PtAt ex Csz) (i : Fin D.R.m) (g) (f) (hf : f ∈ (p.R.toRealDat.FW i).WK) :
    (p.R.toRealDat.FW i).ρ g f ∈ (p.R.toRealDat.FW i).WK := by
  by_cases hk : ActKeeps (κ := p.κ) p.O i
  · obtain ⟨c, hc⟩ := (p.fw.e i).surjective ⟨f, hf⟩
    obtain ⟨_, h2⟩ := (p.rhoGeo i).1 hk g c
    rw [hc] at h2
    rw [← h2]
    exact Subtype.property _
  · rw [(p.rhoGeo i).2 hk g]
    exact hf

end GlobalTheory.CovTop
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ChiMulPsiInvMemCoreStatement

section

@[expose] public section



section
open NumberField

theorem _root_.GlobalTheory.T.chi_mul_psi_inv_mem_range_algebraMap : ∀ {D : Formalism.BasicNotions.D7} {L : Formalism.BasicNotions.SizeData₂ D} {hT : Formalism.BasicNotions.GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y0 : Formalism.BasicNotions.DivX D} {cX : Formalism.BasicNotions.ExtraC} {ex : Formalism.BasicNotions.Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : GlobalTheory.BigTop.PtAt ex Csz) (i : Fin D.R.m), p.PointConditions' → GlobalTheory.CovTop.RecTied D L → ∀ u : (p.F.lv2.lvl false).P, (((p.R.toRealDat.FW i).chi u * (p.F.lv2.lvl false).ψ⁻¹ u : D.what₂.LLˣ) : D.what₂.LL) ∈ Set.range (algebraMap p.T.Q.c.F D.what₂.LL) := by
  first | exact @_root_.GlobalTheory.CovTop.chi_mul_psi_inv_mem_core_alt | exact _root_.GlobalTheory.CovTop.chi_mul_psi_inv_mem_core_alt | (intros; apply _root_.GlobalTheory.CovTop.chi_mul_psi_inv_mem_core_alt <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RatAtOfRows

section

@[expose] public section



section
open NumberField
namespace GlobalTheory.CovTop
open GlobalTheory.BigTop Formalism.IndefR.FWT
variable {D : Formalism.BasicNotions.D7} {L : Formalism.BasicNotions.SizeData₂ D} {hT : Formalism.BasicNotions.GatTies D} {Gi : Formalism.MainNotions.G.Inst D L}
  {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y0 : Formalism.BasicNotions.DivX D} {cX : Formalism.BasicNotions.ExtraC}
  {ex : Formalism.BasicNotions.Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ}
theorem ratAt_of_rows_alt (p : PtAt ex Csz) (i : Fin D.R.m) (hp : p.PointConditions') (ht : RecTied D L) : RatAt p i :=
  GlobalTheory.T.integralForms_eq_span_integralRationalForms _ _ _ _ _ _ _ _ (p.fw.ks i) (fun u f hf => rho_mem_WK p i u f hf) (_root_.GlobalTheory.T.chi_mul_psi_inv_mem_range_algebraMap p i hp ht)
end GlobalTheory.CovTop
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoveringRationalOfLocalTraces

section

@[expose] public section



section
section
open NumberField
namespace GlobalTheory.CovTop
open GlobalTheory.BigTop Formalism.IndefR.FWT
variable {D : Formalism.BasicNotions.D7} {L : Formalism.BasicNotions.SizeData₂ D} {hT : Formalism.BasicNotions.GatTies D} {Gi : Formalism.MainNotions.G.Inst D L}
  {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y0 : Formalism.BasicNotions.DivX D} {cX : Formalism.BasicNotions.ExtraC}
  {ex : Formalism.BasicNotions.Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ}
theorem covering_rational_of_local_traces_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.LiftRational := by
  intro _
  refine ⟨1, one_pos, fun eps _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm CH _ _ =>
    ⟨0, le_rfl, ⟨0, fun x hx _ ι p hp i => _root_.GlobalTheory.CovTop.ratAt_of_rows_alt p i hp.1 hp.2⟩⟩⟩⟩
end GlobalTheory.CovTop
end
section
open GlobalTheory.CovTop GlobalTheory.BigTop

theorem _root_.GlobalTheory.T.liftRational_of_prints : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.LiftRational := by
  first | exact @_root_.GlobalTheory.CovTop.covering_rational_of_local_traces_alt | exact _root_.GlobalTheory.CovTop.covering_rational_of_local_traces_alt | (intros; apply _root_.GlobalTheory.CovTop.covering_rational_of_local_traces_alt <;> assumption)
end
end
end
end
