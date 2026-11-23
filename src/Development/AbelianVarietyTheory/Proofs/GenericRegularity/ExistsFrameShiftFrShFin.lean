module

public import Formalism.LocalToGlobal.ProjectiveLattices.DivFinOfLawA3
public import Formalism.LocalToGlobal.ProjectiveLattices.VAtVNeBot
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.EvaluationLawsGenericFramesAtlasHoldStatement
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsFrameShiftOfValuedPointsStatement
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsGlobalModelGoodLevelAllPrimesStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt

-- Source module: Development.AbelianVarietyTheory.Proofs.GenericRegularity.FrShFinOfDivFinOfFinset

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

namespace GlobalTheory.Reg

theorem frShFin_of_divFin_of_finset : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ [Fintype (Comp Xo c)] (d : ReciprocityTheory.ChartRestriction.G.T0.Data c.F (Comp Xo c) (fun Z => Om Z) (WTZ E) (fun Z => AC Z)) (δ : ∀ Z : Comp Xo c, AddValuation (Om Z) (WithTop ℤ) → Ix Dw → ℤ), DivFin d → (∀ Z : Comp Xo c, ∃ S : Finset (Om Z), (∀ s ∈ S, s ≠ 0) ∧ ∀ v : AddValuation (Om Z) (WithTop ℤ), ReciprocityTheory.ChartRestriction.G.T0.IsNormDiscrete v → ((∃ la, ReciprocityTheory.ChartRestriction.G.T0.IsOver (K := c.F) v la) ∨ ReciprocityTheory.ChartRestriction.G.T0.IsTrivOn c.F v) → (∀ s ∈ S, v s = 0) → δ Z v = 0) → FrShFin d δ := by
  intro E _ _ _ H Dw l Xo c _ d δ hd hS
  unfold FrShFin
  unfold DivFin at hd
  intro Z
  obtain ⟨S, hS0, hSv⟩ := hS Z
  refine (Set.Finite.biUnion (t := fun s => {v | d.admitted Z v ∧ v s ≠ 0}) S.finite_toSet
    fun s hs => hd Z s (hS0 s hs)).subset ?_
  rintro v ⟨hadm, hδ⟩
  have hnot : ¬ ∀ s ∈ S, v s = 0 := by
    intro hall
    apply hδ
    obtain ⟨hnd, hcase⟩ := hadm
    refine hSv v hnd ?_ hall
    rcases hcase with ⟨la, hla, -⟩ | ⟨ht, -⟩
    · exact Or.inl ⟨la, hla⟩
    · exact Or.inr ht
  push_neg at hnot
  obtain ⟨s, hs, hvs⟩ := hnot
  exact Set.mem_biUnion (Finset.mem_coe.mpr hs) ⟨hadm, hvs⟩

end GlobalTheory.Reg
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsFrameShiftFrShFin

section

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FrameNorm GlobalTheory.Reg

namespace GlobalTheory.Reg

theorem exists_frameShift_frShFin : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → (∀ p : ℕ, p.Prime → l.GoodAt p) → l.A = 1 → ∀ h : GenFrEx Xo c, ∃ δ : ∀ Z : Comp Xo c, AddValuation (Om Z) (WithTop ℤ) → Ix Dw → ℤ, (∀ (Z : Comp Xo c) (v : AddValuation (Om Z) (WithTop ℤ)), T0.IsNormDiscrete v → ((∃ la, T0.IsOver (K := c.F) v la) ∨ T0.IsTrivOn c.F v) → ∃ (T : CDVR) (ψ : Om Z →+* T.Fr) (y : IntFr Xo c T (ψ.comp (algebraMap c.F (Om Z)))), (∀ a : Om Z, a ≠ 0 → ((vV T.V (ψ a) : ℤ) : WithTop ℤ) = v a) ∧ ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c), f ∈ sec Xo c a n → (evI y f = 0 ↔ evC h Z f = 0) ∧ (evC h Z f ≠ 0 → ordC (δ Z v) v (wtZ a n) (valC h a n f Z) = vV T.V (evI y f))) ∧ ∀ [Fintype (Comp Xo c)] (d : T0.Data c.F (Comp Xo c) (fun Z => Om Z) (WTZ E) (fun Z => AC Z)), DivFin d → FrShFin d δ := by
  intro E _ _ _ H Dw l Xo c hpq hgood hA h
  obtain ⟨hM, ⟨Y⟩⟩ := GlobalTheory.T.exists_global_model_goodLevel_all_primes E H Dw l Xo c hpq hgood hA
  have hEv : EvLaws Xo c := (GlobalTheory.T.evaluation_laws_generic_frames_atlas_hold E H Dw l Xo c).1
  have hInt : IntDiagUnit Xo c := (GlobalTheory.T.evaluation_laws_generic_frames_atlas_hold E H Dw l Xo c).2.1
  have hTw : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt :=
    GlobalTheory.lawsFieldsSeparately.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨δ, h1, h2⟩ := GlobalTheory.T.exists_frame_shift_of_valued_points hTw E H Dw l Xo c hEv hInt hM Y h
  exact ⟨δ, h1, fun d hD => GlobalTheory.Reg.frShFin_of_divFin_of_finset E H Dw l Xo c d δ hD h2⟩

end GlobalTheory.Reg
end
end
