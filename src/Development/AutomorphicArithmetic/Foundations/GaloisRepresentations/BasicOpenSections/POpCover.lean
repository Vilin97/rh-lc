module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.OpCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyCoefficientRingInvarianceStatement
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.AllHolds
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsWtZero
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.WtDegConst
import Mathlib.Tactic.Linter.HaveILetI
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpecHolds
import Mathlib.Tactic.Polynomial.Basic
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCorrOpOfAvg
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.ResClosed

-- Source module: Development.EtaleCohomology.EtaleTrace.LTransferCut

section

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped TensorProduct

namespace LateralTheory.EtaleTrace.Tr

def Splits {Y X W : Scheme.{0}} (a : Y ⟶ X) (x : W ⟶ X) (m : ℕ) (s : Fin m → (W ⟶ Y)) : Prop :=
  ∃ hs : ∀ j, s j ≫ a = x, IsIso (Sigma.desc (fun j => pullback.lift (s j) (𝟙 W) (by rw [hs j, Category.id_comp])) :
      ∐ (fun _ : Fin m => W) ⟶ pullback a x)

section
variable (R : Type) [CommRing R]

abbrev fr (X : Scheme.{0}) : Shv R := (free R).obj (yoneda.obj X)

abbrev gen {U X : Scheme.{0}} (x : U ⟶ X) : Sec (fr R X) U := freeGen R (yoneda.obj X) U x

def IsTr {Y X : Scheme.{0}} (a : Y ⟶ X) (τ : fr R X ⟶ fr R Y) : Prop :=
  ∀ (W : Scheme.{0}) (x : W ⟶ X) (m : ℕ) (s : Fin m → (W ⟶ Y)), Splits a x m s →
    Sec.map τ (gen R x) = ∑ j, gen R (s j)

variable {R}

end

def LSpl : Prop := ∀ {Y X W : Scheme.{0}} (a : Y ⟶ X) (x : W ⟶ X) (m : ℕ) (s : Fin m → (W ⟶ Y)), Splits a x m s →
  (∀ (U : Scheme.{0}) (w : U ⟶ W), Splits a (w ≫ x) m (fun j => w ≫ s j)) ∧
  (∀ y : W ⟶ Y, y ≫ a = x → ∀ t : W, ∃ (O : W.Opens) (j : Fin m), t ∈ O ∧ O.ι ≫ y = O.ι ≫ s j) ∧
  (Nonempty W → Function.Injective s)

def LLoc : Prop := ∀ {Y X : Scheme.{0}} (a : Y ⟶ X), IsFinite a → Etale a → ∀ (W : Scheme.{0}) (x : W ⟶ X) (t : W),
  ∃ (U : Scheme.{0}) (g : U ⟶ W) (m : ℕ) (s : Fin m → (U ⟶ Y)), Etale g ∧ t ∈ Set.range g ∧ Splits a (g ≫ x) m s

def LTau : Prop := ∀ (R : Type) [CommRing R] {Y X : Scheme.{0}} (a : Y ⟶ X), IsFinite a → Etale a →
  ∃ τ : fr R X ⟶ fr R Y, IsTr R a τ

section Glue
variable (l : ℕ) [Fact l.Prime]

end Glue

end LateralTheory.EtaleTrace.Tr

end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.TrTransferQ

section

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace UpperTheory.Gal.TranscendenceTraces

def TrPushQ : Prop := ∀ (l : ℕ) [Fact l.Prime] (n i : ℤ) {Z Z' S : Scheme.{0}} (h : Z ⟶ Z') (p : Z' ⟶ S) [IsFinite h]
  [IsFinite p] (w : Wt Z), IsWt (h ≫ p) w → IsUnit (l : Γ(S, ⊤)) →
  trHQ l (h ≫ p) w n i ∘ₗ pullHQ l (sch.map h) n i = trHQ l p (w.push h) n i

open LateralTheory.EtaleTrace.Tr (Splits LSpl LLoc LTau)

end UpperTheory.Gal.TranscendenceTraces

end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.BTrPushQ

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.trPushQ_of :
    TrPush → TrHl → WtPush → TrPushQ := by
  intro hP hH hW l _ n i Z Z' S h p _ _ w hw hl
  have key : trHl l (h ≫ p) w n i ∘ₗ pullHl l (sch.map h) n i = trHl l p (Wt.push h w) n i := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    funext k
    rw [LinearMap.comp_apply, hH l n i (h ≫ p) w hw hl, hH l n i p (Wt.push h w) (hW h p w hw) hl]
    haveI : NeZero (l ^ k) := ⟨pow_ne_zero k (Fact.out : Nat.Prime l).ne_zero⟩
    exact hP (l ^ k) n i h p w hw (by push_cast; exact hl.pow k) (x.1 k)
  simp only [trHQ, pullHQ, ← key, LinearMap.baseChange_comp]
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.POpCover

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et GlobalTheory.GalV
open UpperTheory.Gal.TranscendenceTraces (gp pt Wt fib IsWt)
open UpperTheory.Gal.crystallineComparison (PtId fn)
open UpperTheory.Gal UpperTheory.Gal.Mod

private theorem push_const_one {Z Z' : Scheme.{0}} (u : Z ⟶ Z') [IsFinite u] (δ : ℕ)
    (hδ : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : gp Ω ⟶ Z'), (fib u x).ncard = δ) :
    (Wt.const Z 1).push u = Wt.const Z' (δ : ℤ) := by
  funext Ω _ _ x
  simp only [Wt.push, Wt.const]
  rw [← hδ Ω x]
  obtain hs | hs := (fib u x).infinite_or_finite
  · rw [hs.ncard, Nat.cast_zero]
    exact finsum_mem_eq_zero_of_infinite (by simpa [Function.support_const one_ne_zero] using hs)
  · rw [finsum_mem_eq_finite_toFinset_sum _ hs, Set.ncard_eq_toFinset_card _ hs]
    simp

theorem UpperTheory.Gal.Mod.opCover :
    OpCover := by
  intro l _ S S' c c' u _ δ hw hw' hp hf hl hδ k i
  haveI := c.fin
  haveI := c'.fin
  have hadic := TranscendenceTraces.all_holds.2.2
  have hwl := TranscendenceTraces.all_holds.1.2.2.1
  have hwc : IsWt (u ≫ c'.p) (Wt.const c.Z 1) := by
    have h0 := c.wt
    rw [hw, ← hp] at h0
    exact h0
  have hwc' : IsWt c'.p (Wt.const c'.Z 1) := by
    have h0 := c'.wt
    rw [hw'] at h0
    exact h0
  have hpush := TranscendenceTraces.trPushQ_of TranscendenceTraces.trPush_holds hadic.2.1 TranscendenceTraces.wtPush_holds l k i u c'.p
    (Wt.const c.Z 1) hwc hl
  rw [push_const_one u δ hδ] at hpush
  have hcomp := hadic.2.2.2.1 l k i c'.p (𝟙 S) (Wt.const c'.Z 1) (Wt.const S (δ : ℤ)) hwc'
    (hwl.2.2 (𝟙 S) (δ : ℤ)) hl
  have hmul : Wt.mul c'.p (Wt.const c'.Z 1) (Wt.const S (δ : ℤ)) = Wt.const c'.Z (δ : ℤ) := by
    funext Ω _ _ z
    simp [Wt.mul, Wt.const]
  rw [Category.comp_id, hmul, TranscendenceTraces.trIdQ_holds GlobalTheory.T.etaleCohomology_coefficientRing_invariance l k i S δ hl,
    LinearMap.smul_comp, LinearMap.id_comp] at hcomp
  have hpull : pullHQ l (sch.map (u ≫ c'.f)) k i =
      pullHQ l (sch.map u) k i ∘ₗ pullHQ l (sch.map c'.f) k i := by
    simp only [pullHQ, Functor.map_comp, pullHl_comp, LinearMap.baseChange_comp]
  unfold TranscendenceTraces.Corr.opQ
  rw [← hf, ← hp, hw, hw', hpull, ← LinearMap.comp_assoc, hpush, hcomp, LinearMap.smul_comp]
  first
    | rfl
    | simp only [Int.cast_natCast, Nat.cast_smul_eq_nsmul]
    | (norm_cast; simp [Nat.cast_smul_eq_nsmul])
end
end
