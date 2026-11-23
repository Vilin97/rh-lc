module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CohDimTwoLocalOfLocalFiniteness
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsDualDualRep
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CocycleFormsSpanOddResidueChar
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
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAuxiliaryPrimesPrescribedFrobenius
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsElementsSelmerFormsSmallCorank
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FirstHalfLocalCohomologyVanishingOfLocalDualityT
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReciprocityAuxiliaryPlacesSecondHalf
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidualBoundOfComponentsStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidualSelmerDeterminantOrderBound
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidualSelmerFinrankEqDualStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanTwoOfGaloisHypothesis

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CocycleFormsSpanOddResidueCharStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel

theorem _root_.GlobalTheory.T.cocycleFormsSpan_oddResidueChar : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), GalHyp bkP i s → SpanOdd i s := by
  first | exact @GlobalTheory.ResSel.SpanOddPf.spanOdd | exact GlobalTheory.ResSel.SpanOddPf.spanOdd | (intros; apply GlobalTheory.ResSel.SpanOddPf.spanOdd <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAuxiliaryPrimesPrescribedFrobeniusStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel

theorem _root_.GlobalTheory.T.exists_auxiliary_primes_prescribed_frobenius : Cheb → ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (i : X.Tw), StepAB X i := by
  first | exact @GlobalTheory.ChosenPrimes.stepAB | exact GlobalTheory.ChosenPrimes.stepAB | (intros; apply GlobalTheory.ChosenPrimes.stepAB <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsElementsSelmerFormsSmallCorankStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel

theorem _root_.GlobalTheory.T.exists_elements_selmerForms_small_corank : GlobalFiniteness → ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw), (∀ s, GalHyp bkP i s → SpanOdd i s ∧ SpanTwo i s ∧ EqDim bkP i s) → ChooseH bkP i := by
  first | exact @GlobalTheory.ChooseForms.chooseH | exact GlobalTheory.ChooseForms.chooseH | (intros; apply GlobalTheory.ChooseForms.chooseH <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FirstHalfLocalCohomologyVanishingOfLocalDualityTStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel

theorem _root_.GlobalTheory.T.firstHalfLocalCohomologyVanishing_of_localDualityTheorems : LocalFiniteness → LocalTateDuality → LocalEulerChar → TameLocal → ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), GalHyp bkP i s → FirstHalf i s := by
  first | exact @GlobalTheory.ScalarFrob.firstHalf | exact GlobalTheory.ScalarFrob.firstHalf | (intros; apply GlobalTheory.ScalarFrob.firstHalf <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReciprocityAuxiliaryPlacesSecondHalfStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel

theorem _root_.GlobalTheory.T.reciprocity_auxiliaryPlaces_secondHalf : Cheb → PoitouTateTotallyComplex → CohDimTwo → TameLocal → LocalFiniteness → LocalTateDuality → LocalEulerChar → GlobalFiniteness → GlobalEulerChar → UnramifiedOrthogonality → Gen.ArchimedeanSignatureMatching → ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), GalHyp bkP i s → FirstHalf i s → Recip bkP i s := by
  first | exact @GlobalTheory.ResRecip.reciprocity | exact GlobalTheory.ResRecip.reciprocity | (intros; apply GlobalTheory.ResRecip.reciprocity <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidualSelmerDeterminantOrderBoundStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel

theorem _root_.GlobalTheory.T.residual_selmer_determinant_order_bound : TameLocal → ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), GalHyp bkP i s → FirstHalf i s → Recip bkP i s → EqDim bkP i s → ResBound bkP i s := by
  first | exact @GlobalTheory.ResOrder.resBound | exact GlobalTheory.ResOrder.resBound | (intros; apply GlobalTheory.ResOrder.resBound <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanTwoOfGaloisHypothesisStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel

theorem _root_.GlobalTheory.T.span_two_of_galois_hypothesis : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), GalHyp bkP i s → SpanTwo i s := by
  first | exact @GlobalTheory.ResSel.AltSpan.spanTwo_of_galHyp | exact GlobalTheory.ResSel.AltSpan.spanTwo_of_galHyp | (intros; apply GlobalTheory.ResSel.AltSpan.spanTwo_of_galHyp <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidualSelmerBoundOfAuxiliaryPrimesOdd

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel

namespace GlobalTheory.ResSel

theorem residual_bound_of_parts : Cheb → PoitouTateTotallyComplex → CohDimTwo → TameLocal → LocalFiniteness → LocalTateDuality → LocalEulerChar → GlobalFiniteness → GlobalEulerChar → UnramifiedOrthogonality → Gen.ArchimedeanSignatureMatching → GreenbergWiles → ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X), ResidualBoundOddPrimes bkP := by
  intro hC hPT hCD hT hLF hLT hLE hGF hGE hU hA _ D N X bkP
  have hgw : ∀ i s, GalHyp bkP i s → EqDim bkP i s := fun i s h =>
    GlobalTheory.T.residual_selmer_finrank_eq_dual hC hPT hCD hT hLF hLT hLE hGF hGE hU hA D N X bkP i s h
  refine GlobalTheory.T.residual_bound_of_components D N X bkP (fun i => GlobalTheory.T.exists_auxiliary_primes_prescribed_frobenius hC D N X i)
    (fun i => GlobalTheory.T.exists_elements_selmerForms_small_corank hGF D N X bkP i fun s h =>
      ⟨GlobalTheory.T.cocycleFormsSpan_oddResidueChar D N X bkP i s h, GlobalTheory.T.span_two_of_galois_hypothesis D N X bkP i s h, hgw i s h⟩)
    (fun i s h => ?_)
  have hk := GlobalTheory.T.firstHalfLocalCohomologyVanishing_of_localDualityTheorems hLF hLT hLE hT D N X bkP i s h
  exact GlobalTheory.T.residual_selmer_determinant_order_bound hT D N X bkP i s h hk
    (GlobalTheory.T.reciprocity_auxiliaryPlaces_secondHalf hC hPT hCD hT hLF hLT hLE hGF hGE hU hA D N X bkP i s h hk) (hgw i s h)

end GlobalTheory.ResSel
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidualSelmerBoundOfAuxiliaryPrimesOddStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published

theorem _root_.GlobalTheory.T.residualSelmerBound_of_auxiliaryPrimes_odd : Cheb → PoitouTateTotallyComplex → CohDimTwo → TameLocal → LocalFiniteness → LocalTateDuality → LocalEulerChar → GlobalFiniteness → GlobalEulerChar → UnramifiedOrthogonality → Gen.ArchimedeanSignatureMatching → GreenbergWiles → ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X), ResidualBoundOddPrimes bkP := by
  first | exact @GlobalTheory.ResSel.residual_bound_of_parts | exact GlobalTheory.ResSel.residual_bound_of_parts | (intros; apply GlobalTheory.ResSel.residual_bound_of_parts <;> assumption)
end
end
