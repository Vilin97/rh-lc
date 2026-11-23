module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLimENF
public import Development.AbelianVarietyTheory.PublishedTheorems.BesselIntegrals.BesselXiIntegrable
public import Development.AbelianVarietyTheory.Definitions.Jets.BasicLiftAll
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsPolyDiffOpRadialPartEqShiftedOperatorStatement
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MirrorTodaRadialOperatorPolynomialCoefficientLif
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.PolyLiftConjLastMinorMulRadialPairTerm
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.PolynomialLiftDualOperatorCombination
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TopDensityDominated

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.MirrorTodaRadialOperatorPolynomialCoefficientLifStatement

section

@[expose] public section

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

theorem _root_.GlobalTheory.T.mirrorTodaRadialOperator_polynomialCoefficient_lift : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (μ : Measure (Mt P.k P.r)) (L : LevelData (RA P Bs) P.r) (st : Start (RA P Bs)) (l0 : ℕ) (d : Q.NFData P (RA P Bs)), P5.IsData P Bs.z Bs.z' Bs.π Bs.π' X μ L st l0 → IsNF X d → ∀ y : ℝ, PolyLift P Bs (2 * P.r + P.k + 1) (8 * (P.r + 1) * (2 * P.r + P.k + 1)) (d.L.Ahatv y) := by
  first | exact @GlobalTheory.MirrorToda.polyLift_ahatv | exact GlobalTheory.MirrorToda.polyLift_ahatv | (intros; apply GlobalTheory.MirrorToda.polyLift_ahatv <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.PolyLiftConjLastMinorMulRadialPairTermStatement

section

@[expose] public section

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

theorem _root_.GlobalTheory.T.polyLift_conjLastMinor_mul_radialPairTerm : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (μ : Measure (Mt P.k P.r)) (L : LevelData (RA P Bs) P.r) (st : Start (RA P Bs)) (l0 : ℕ) (d : Q.NFData P (RA P Bs)), P5.IsData P Bs.z Bs.z' Bs.π Bs.π' X μ L st l0 → IsNF X d → ∀ y : ℝ, PolyLift P Bs (2 * P.r + P.k + 1) (8 * (P.r + 1) * (2 * P.r + P.k + 1)) (rh d y) := by
  first | exact @GlobalTheory.HatNF.LiftR.polyLift_rh | exact GlobalTheory.HatNF.LiftR.polyLift_rh | (intros; apply GlobalTheory.HatNF.LiftR.polyLift_rh <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.PolynomialLiftDualOperatorCombinationStatement

section

@[expose] public section

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

theorem _root_.GlobalTheory.T.polynomial_lift_dual_operator_combination : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (μ : Measure (Mt P.k P.r)) (L : LevelData (RA P Bs) P.r) (st : Start (RA P Bs)) (l0 : ℕ) (d : Q.NFData P (RA P Bs)), P5.IsData P Bs.z Bs.z' Bs.π Bs.π' X μ L st l0 → IsNF X d → ∀ y : ℝ, PolyLift P Bs (2 * P.r + P.k + 1) (8 * (P.r + 1) * (2 * P.r + P.k + 1)) (rhv d y) := by
  first | exact @GlobalTheory.HatNF.MirrorLift.polyLift_rhv | exact GlobalTheory.HatNF.MirrorLift.polyLift_rhv | (intros; apply GlobalTheory.HatNF.MirrorLift.polyLift_rhv <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.BasicOperatorsPolynomialLiftNoInversePower

section

@[expose] public section

namespace GlobalTheory.HatNF

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory

theorem mem_nfSpan_zero_zero_one_of_mem {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] {P : M.Par}
    (d : Q.NFData P A) (T : Set A) {x : A} (hx : x ∈ T) : x ∈ nfSpan d T 0 0 1 := by
  refine Submodule.subset_span ⟨1, (bmon d).one_mem, [x], rfl, ?_, ?_⟩
  · intro h hh
    rw [List.mem_singleton] at hh
    exact hh ▸ hx
  · simp

theorem basicLiftAll_zero : BasicLiftAll (fun _ => 0) := by
  intro Wp Wq _ _ _ _ _ _ P Bs X μ L st l0 d hD hN x hx
  obtain ⟨y, -, h | h | h | h⟩ := hx
  · exact mem_nfSpan_zero_zero_one_of_mem d _ (h ▸ GlobalTheory.T.exists_polyDiffOp_radialPart_eq_shiftedOperator Wp Wq P Bs X μ L st l0 d hD hN y)
  · exact mem_nfSpan_zero_zero_one_of_mem d _ (h ▸ GlobalTheory.T.mirrorTodaRadialOperator_polynomialCoefficient_lift Wp Wq P Bs X μ L st l0 d hD hN y)
  · exact mem_nfSpan_zero_zero_one_of_mem d _ (h ▸ GlobalTheory.T.polyLift_conjLastMinor_mul_radialPairTerm Wp Wq P Bs X μ L st l0 d hD hN y)
  · exact mem_nfSpan_zero_zero_one_of_mem d _ (h ▸ GlobalTheory.T.polynomial_lift_dual_operator_combination Wp Wq P Bs X μ L st l0 d hD hN y)

end GlobalTheory.HatNF
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.BasicOperatorsPolynomialLiftNoInversePowerStatement

section

@[expose] public section

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

theorem _root_.GlobalTheory.T.basicOperators_polynomialLift_no_inversePower : BasicLiftAll (fun _ => 0) := by
  first | exact @GlobalTheory.HatNF.basicLiftAll_zero | exact GlobalTheory.HatNF.basicLiftAll_zero | (intros; apply GlobalTheory.HatNF.basicLiftAll_zero <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.TopDensityCutoffDominatedOfHCXi

section

@[expose] public section

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

namespace GlobalTheory.HatNF

theorem topDensity_cut_dominated_all :
    GlobalTheory.HCXi.BesselXiIntegrable → Formalism.FourierDecayAlt.P.CutBP.NFTopDomAll := by
  intro hΞ Cb
  obtain ⟨Cc, H⟩ := GlobalTheory.HatNF.top_density_dominated hΞ (fun _ => 0) GlobalTheory.T.basicOperators_polynomialLift_no_inversePower Cb
  refine ⟨Cc, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p f A₀ p₀ χ Y N hH w hw hN
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hH
  obtain ⟨hm, h, hi, hb⟩ := H Wp Wq P p f A₀ p₀ χ N w a1 a2 a3 a4 a5 (by simpa using a6) hw.1 hN
  have e : ∀ ε : ℝ,
      D.cutF p.T.base χ (Formalism.FourierDecayAlt.P.TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε =
      mulG p.T.base (fun y => χ (y / ε) * y ^ p₀) f := by
    intro ε
    funext g
    simp only [D.cutF, Formalism.FourierDecayAlt.P.TBBx4.fpm, mulG, ContinuousLinearMap.comp_id, smul_smul]
    try push_cast
    try rfl
  refine ⟨eventually_nhdsWithin_of_forall fun ε hε => ?_, h, hi,
    eventually_nhdsWithin_of_forall fun ε hε => ae_of_all _ fun c => ?_⟩
  · rw [e]; exact hm ε hε
  · rw [e]; exact hb ε hε c
end GlobalTheory.HatNF
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.TopDensityCutoffDominatedOfHCXiStatement

section

@[expose] public section

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

theorem _root_.GlobalTheory.T.topDensity_cutoff_dominated_of_HC_xi : GlobalTheory.HCXi.BesselXiIntegrable → Formalism.FourierDecayAlt.P.CutBP.NFTopDomAll := by
  first | exact @GlobalTheory.HatNF.topDensity_cut_dominated_all | exact GlobalTheory.HatNF.topDensity_cut_dominated_all | (intros; apply GlobalTheory.HatNF.topDensity_cut_dominated_all <;> assumption)
end
end
