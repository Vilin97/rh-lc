module

public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Hilbert90IntegralIdelesOfMovedPrimes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicUnitaryCharacterTrivialAtNonsplitPlace
public import Mathlib.Analysis.Complex.Circle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexCharEqOneOfForallCircleChar
public import Formalism.LocalRingCardinality.DataHost
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsProdLocalComponentsEqPrimePartStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPrimeIffNonSplitPlaceIdempotent
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertSupportedUnitaryPointIntegralCofiniteStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonSplitSupportedFinitePartIntegralInertStatement
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaCosetIndicatorReadingSphericalOffModulus
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.SharpRestriction.GlobalSchurBounds.StandardIntegralLatticeExists
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdelicPointUnitaryGroupGramOne
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ClassFunctionSumIntegral
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinPt

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexCharEqOneOfForallCircleCharStatement

section

@[expose] public section

open NumberField IsDedekindDomain
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.eq_one_of_forall_circle_char_eq_one : ∀ {G : Type} [Group G] (ν : G →* ℂˣ) (x : G), (∀ μ : G →* Circle, (∀ g, ν g = 1 → μ g = 1) → μ x = 1) → ν x = 1 := by
  first | exact @GlobalTheory.complexChar_eq_one_of_forall_circleChar | exact GlobalTheory.complexChar_eq_one_of_forall_circleChar | (intros; apply GlobalTheory.complexChar_eq_one_of_forall_circleChar <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SuppInertUnitaryAdelicPointComponentAtPrimes

section

@[expose] public section

open NumberField IsDedekindDomain
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.NormSum.PartSupp

open Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum.VacInt

theorem zeroAt_mul_left (D : Formalism.BasicNotions.D7) {q : ℕ} {e z : AE D} (he : e ∈ OhE D) (hz : ZeroAt D q z) :
    ZeroAt D q (e * z) := by
  intro k
  obtain ⟨m, hm, hc, s, hs, h⟩ := hz k
  exact ⟨m, hm, hc, e * s, mul_mem he hs, by linear_combination e * h⟩

theorem trivAt_part_of_trivAt (D : Formalism.BasicNotions.D7) {N : ℕ} (P : ℕ → Prop) (g : GA D N) {q : ℕ}
    (h : TrivAt D q (g : GL (Fin N) (AE D))) : TrivAt D q (part D P g : GL (Fin N) (AE D)) := by
  intro i j
  have := zeroAt_mul_left D (e := eps D.host.E P) (eps_mem P) (h i j)
  convert this using 1
  show cutM _ _ _ i j - _ = _
  rw [cutM_apply]
  ring

theorem suppInert_part_of_suppInert : ∀ {D : Formalism.BasicNotions.D7} {N : ℕ} (P : ℕ → Prop) (y : Formalism.MainNotions.StandardLatticesGL3.GA D N),
    Formalism.MainNotions.StandardLatticesGL3.SuppInert D (y : GL (Fin N) (Formalism.MainNotions.StandardLatticesGL3.AE D)) →
      Formalism.MainNotions.StandardLatticesGL3.SuppInert D (GlobalTheory.NormSum.VacInt.part D P y : GL (Fin N) (Formalism.MainNotions.StandardLatticesGL3.AE D)) :=
  fun {D} {_} P y hy q hq h => trivAt_part_of_trivAt D P y (hy q hq h)

end GlobalTheory.NormSum.PartSupp
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SuppInertUnitaryAdelicPointComponentAtPrimesStatement

section

@[expose] public section

open NumberField IsDedekindDomain
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.suppInert_unitaryAdelicPointComponentAtPrimes : ∀ {D : Formalism.BasicNotions.D7} {N : ℕ} (P : ℕ → Prop) (y : Formalism.MainNotions.StandardLatticesGL3.GA D N), Formalism.MainNotions.StandardLatticesGL3.SuppInert D (y : GL (Fin N) (Formalism.MainNotions.StandardLatticesGL3.AE D)) → Formalism.MainNotions.StandardLatticesGL3.SuppInert D (GlobalTheory.NormSum.VacInt.part D P y : GL (Fin N) (Formalism.MainNotions.StandardLatticesGL3.AE D)) := by
  first | exact @GlobalTheory.NormSum.PartSupp.suppInert_part_of_suppInert | exact GlobalTheory.NormSum.PartSupp.suppInert_part_of_suppInert | (intros; apply GlobalTheory.NormSum.PartSupp.suppInert_part_of_suppInert <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryPrimeComponentFinsetProd

section

@[expose] public section

open NumberField IsDedekindDomain
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

noncomputable section

namespace GlobalTheory.NormSum.VacInt.PartFin

open GlobalTheory.NormSum.VacInt

section Cut

variable {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]

theorem cutM_of_eq_zero (e : R) (he : e * e = e) (h : e = 0) (A : Matrix n n R) : cutM e he A = 1 := by
  subst h
  show (0 : R) • A + (1 - 0 : R) • (1 : Matrix n n R) = 1
  simp

theorem cutM_add (e e' f : R) (he : e * e = e) (he' : e' * e' = e') (hf : f * f = f) (h0 : e * e' = 0)
    (h : f = e + e') (A : Matrix n n R) : cutM f hf A = cutM e he A * cutM e' he' A := by
  subst h
  have h1 : e * (1 - e') = e := by linear_combination - h0
  have h2 : (1 - e) * e' = e' := by linear_combination - h0
  have h3 : (1 - e) * (1 - e') = 1 - (e + e') := by linear_combination h0
  show (e + e') • A + (1 - (e + e')) • (1 : Matrix n n R) =
    (e • A + (1 - e) • (1 : Matrix n n R)) * (e' • A + (1 - e') • (1 : Matrix n n R))
  simp only [add_mul, mul_add, smul_mul_smul_comm, Matrix.mul_one, Matrix.one_mul, h0, h1, h2, h3,
    zero_smul, zero_add, add_smul]
  abel

end Cut

variable {E : Type} [Field E] [NumberField E]

theorem eps_empty : eps E (fun p => p ∈ (∅ : Finset ℕ)) = 0 :=
  ext_prV fun v => by rw [prV_eps, map_zero]; simp

theorem eps_insert (q : ℕ) (s : Finset ℕ) (h : q ∉ s) :
    eps E (fun p => p ∈ insert q s) = eps E (fun p => p = q) + eps E (fun p => p ∈ s) :=
  ext_prV fun v => by
    rw [map_add (f := _), prV_eps, prV_eps, prV_eps]
    by_cases h1 : pr v = q
    · simp [h1, h]
    · by_cases h2 : pr v ∈ s <;> simp [h1, h2]

theorem eps_single_mul (q : ℕ) (s : Finset ℕ) (h : q ∉ s) :
    eps E (fun p => p = q) * eps E (fun p => p ∈ s) = 0 :=
  ext_prV fun v => by
    rw [map_mul, prV_eps, prV_eps, map_zero]
    by_cases h1 : pr v = q
    · simp [h1, h]
    · simp [h1]

theorem part_finset : ∀ {D : Formalism.BasicNotions.D7} {N : ℕ} (y : Formalism.MainNotions.StandardLatticesGL3.GA D N), GlobalTheory.NormSum.VacInt.part D (fun p => p ∈ (∅ : Finset ℕ)) y = 1 ∧ ∀ (q : ℕ) (s : Finset ℕ), q ∉ s → GlobalTheory.NormSum.VacInt.part D (fun p => p ∈ insert q s) y = GlobalTheory.NormSum.VacInt.part D (fun p => p = q) y * GlobalTheory.NormSum.VacInt.part D (fun p => p ∈ s) y := by
  intro D N y
  exact ⟨Subtype.ext (Units.ext (cutM_of_eq_zero _ _ eps_empty _)), fun q s h =>
    Subtype.ext (Units.ext (cutM_add _ _ _ _ _ _ (eps_single_mul q s h) (eps_insert q s h) _))⟩

end GlobalTheory.NormSum.VacInt.PartFin
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryPrimeComponentFinsetProdStatement

section

@[expose] public section

open NumberField IsDedekindDomain
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.unitaryPrimeComponent_finset_prod : ∀ {D : Formalism.BasicNotions.D7} {N : ℕ} (y : Formalism.MainNotions.StandardLatticesGL3.GA D N), GlobalTheory.NormSum.VacInt.part D (fun p => p ∈ (∅ : Finset ℕ)) y = 1 ∧ ∀ (q : ℕ) (s : Finset ℕ), q ∉ s → GlobalTheory.NormSum.VacInt.part D (fun p => p ∈ insert q s) y = GlobalTheory.NormSum.VacInt.part D (fun p => p = q) y * GlobalTheory.NormSum.VacInt.part D (fun p => p ∈ s) y := by
  first | exact @GlobalTheory.NormSum.VacInt.PartFin.part_finset | exact GlobalTheory.NormSum.VacInt.PartFin.part_finset | (intros; apply GlobalTheory.NormSum.VacInt.PartFin.part_finset <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicCharacterEqOneSplitInert

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.InertSuppChar

theorem eq_one_at_inert {D : Formalism.BasicNotions.D7} (V : Formalism.BasicNotions.TH.HSp D) (hG : V.gram = 1) (μ : Formalism.MainNotions.StandardLatticesGL3.GA D V.rank →* Circle)
    (hμ : ∀ k : Formalism.MainNotions.StandardLatticesGL3.GA D V.rank, Formalism.MainNotions.StandardLatticesGL3.SuppInert D (k : GL (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) →
      Formalism.MainNotions.StandardLatticesGL3.IntG D (k : GL (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) → μ k = 1)
    {q : ℕ} (hq : q.Prime) (hi : Formalism.MainNotions.StandardLatticesGL3.InertQ D q) (y : Formalism.MainNotions.StandardLatticesGL3.GA D V.rank) :
    μ (GlobalTheory.NormSum.VacInt.part D (fun p => p = q) y) = 1 := by
  obtain ⟨g, hg⟩ := GlobalTheory.BotFormula.exists_isFinPt_of_gram_one V hG y rfl
  rw [← GlobalTheory.BotClassDict.finStd_of_isFinPt V hG hg]
  obtain ⟨l, hl, e⟩ := GlobalTheory.T.exists_prod_localComponents_eq_primePart V hG q hq g
  rw [← e, map_list_prod, map_list_prod, List.map_map]
  refine List.prod_eq_one (M := Circle) fun z hz => ?_
  obtain ⟨h, hh, rfl⟩ := List.mem_map.1 hz
  obtain ⟨v, ε, hε, hqv, hs⟩ := hl h hh
  have hn : GlobalTheory.WeilParts.NonSplitAt D v ε := (GlobalTheory.InertPlace.inertQ_iff_nonSplitAt D q hq v ε hε hqv).1 hi
  refine GlobalTheory.InertChar.char_eq_one_of_nonSplit D V _
    (GlobalTheory.NormRatio.SphCoset.isSelfDualC_of_gram_one hG (Formalism.MainNotions.GlobalTheoryTheory.Inhab.stdL_isSD D V.rank)) v ε hn
    (μ.comp (GlobalTheory.BotClassDict.finStd V hG)) (fun k hk hst => ?_) h hs
  obtain ⟨a1, a2⟩ := GlobalTheory.T.nonSplitSupported_finitePart_integral_inert V hG v ε hn k hk hst
  exact hμ _ a1 a2

theorem char_eq_one : ∀ {D : Formalism.BasicNotions.D7} (V : Formalism.BasicNotions.TH.HSp D), V.gram = 1 → ∀ (ν : Formalism.MainNotions.StandardLatticesGL3.GA D V.rank →* ℂˣ),
  (∀ k : Formalism.MainNotions.StandardLatticesGL3.GA D V.rank, Formalism.MainNotions.StandardLatticesGL3.SuppSplit D (k : GL (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) → ν k = 1) →
  (∀ k : Formalism.MainNotions.StandardLatticesGL3.GA D V.rank, Formalism.MainNotions.StandardLatticesGL3.SuppInert D (k : GL (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) →
    Formalism.MainNotions.StandardLatticesGL3.IntG D (k : GL (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) → ν k = 1) →
  ∀ x, ν x = 1 := by
  intro D V hG ν hs hi x
  refine GlobalTheory.T.eq_one_of_forall_circle_char_eq_one ν x fun μ hμ => ?_
  rw [← GlobalTheory.NormSum.VacInt.part_mul_compl D (fun q => ¬ Formalism.MainNotions.StandardLatticesGL3.InertQ D q) x, map_mul,
    hμ _ (hs _ (GlobalTheory.NormSum.VacInt.suppSplit_part D x)), one_mul]
  have hy := GlobalTheory.NormSum.VacInt.suppInert_part D x
  generalize GlobalTheory.NormSum.VacInt.part D (fun q => ¬¬Formalism.MainNotions.StandardLatticesGL3.InertQ D q) x = y at hy ⊢
  obtain ⟨s, hs1, hs2⟩ := GlobalTheory.T.inertSupportedUnitaryPoint_integral_cofinite y hy
  rw [← GlobalTheory.NormSum.VacInt.part_mul_compl D (fun p => p ∈ s) y, map_mul,
    hμ _ (hi _ (GlobalTheory.T.suppInert_unitaryAdelicPointComponentAtPrimes _ _ hy) hs2), mul_one]
  have hloc : ∀ q, q.Prime → Formalism.MainNotions.StandardLatticesGL3.InertQ D q → μ (GlobalTheory.NormSum.VacInt.part D (fun p => p = q) y) = 1 :=
    fun q hq hqi => eq_one_at_inert V hG μ (fun k a1 a2 => hμ _ (hi k a1 a2)) hq hqi y
  clear hs2
  induction s using Finset.induction_on with
  | empty => rw [(GlobalTheory.T.unitaryPrimeComponent_finset_prod y).1, map_one]
  | insert q s hq ih =>
    rw [(GlobalTheory.T.unitaryPrimeComponent_finset_prod y).2 q s hq, map_mul, hloc q (hs1 q (Finset.mem_insert_self q s)).1
      (hs1 q (Finset.mem_insert_self q s)).2, one_mul]
    exact ih fun p hp => hs1 p (Finset.mem_insert_of_mem hp)

end GlobalTheory.InertSuppChar
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicCharacterEqOneSplitInertStatement

section

@[expose] public section

open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.unitaryAdelicCharacter_eq_one_split_inert : ∀ {D : D7} (V : HSp D), V.gram = 1 → ∀ (ν : Formalism.MainNotions.StandardLatticesGL3.GA D V.rank →* ℂˣ),
  (∀ k : Formalism.MainNotions.StandardLatticesGL3.GA D V.rank, Formalism.MainNotions.StandardLatticesGL3.SuppSplit D (k : GL (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) → ν k = 1) →
  (∀ k : Formalism.MainNotions.StandardLatticesGL3.GA D V.rank, Formalism.MainNotions.StandardLatticesGL3.SuppInert D (k : GL (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) →
    Formalism.MainNotions.StandardLatticesGL3.IntG D (k : GL (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) → ν k = 1) →
  ∀ x, ν x = 1 := by
  first | exact @GlobalTheory.InertSuppChar.char_eq_one | exact GlobalTheory.InertSuppChar.char_eq_one | (intros; apply GlobalTheory.InertSuppChar.char_eq_one <;> assumption)
end
end
