module

public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemRangeOfOneTmulMem
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
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
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Order.Int.LeastGreatest
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsPlaceChartOfSplitIdempotent
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitFrameSelfDualLatticeCompletion
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitSupportedUnitaryComponent
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralTensorAdelesEqAdelicCompletionOne
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemHomLatticeIffIntegralMatrixSplitChart
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemHyperspecialIffGIntOfSuppAtSplit
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
public import Formalism.LocalToGlobal.IndefiniteReal.ConjSubConjSub
public import Development.AbelianVarietyTheory.Definitions.Divisors.InstCMHostS
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.ConjSubConjSub

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqMultipleOfStandardLattice

section

@[expose] public section

open IsDedekindDomain NumberField Matrix

namespace GlobalTheory.LatticeBetweenMultiples

lemma one_add_mulVec_mem {F : Type} [Field F] [NumberField F]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) {n : ℕ}
    (S : AddSubgroup (Fin n → v.adicCompletion F))
    (hGL : ∀ x : GL (Fin n) (v.adicCompletion F), (∀ i j, x.1 i j ∈ v.adicCompletionIntegers F) →
      (∀ i j, (x⁻¹).1 i j ∈ v.adicCompletionIntegers F) → ∀ w ∈ S, x.1.mulVec w ∈ S)
    (N : Matrix (Fin n) (Fin n) (v.adicCompletion F)) (hN : N * N = 0)
    (hNi : ∀ i j, N i j ∈ v.adicCompletionIntegers F) {w : Fin n → v.adicCompletion F}
    (hw : w ∈ S) : (1 + N).mulVec w ∈ S := by
  have h1 : (1 + N) * (1 - N) = 1 := by
    rw [add_mul, one_mul, mul_sub, mul_one, hN, sub_zero, sub_add_cancel]
  have h2 : (1 - N) * (1 + N) = 1 := by
    rw [sub_mul, one_mul, mul_add, mul_one, hN, add_zero, add_sub_cancel_right]
  have h1m : ∀ i j, (1 : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j ∈
      v.adicCompletionIntegers F := by
    intro i j
    rw [Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  have hp : ∀ i j, (1 + N) i j ∈ v.adicCompletionIntegers F := by
    intro i j; rw [Matrix.add_apply]; exact add_mem (h1m i j) (hNi i j)
  have hm : ∀ i j, (1 - N) i j ∈ v.adicCompletionIntegers F := by
    intro i j; rw [Matrix.sub_apply]; exact sub_mem (h1m i j) (hNi i j)
  exact hGL ⟨1 + N, 1 - N, h1, h2⟩ hp hm w hw

theorem eq_multiple_of_standard_lattice : ∀ {F : Type} [Field F] [NumberField F]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) {n : ℕ}
    (S : AddSubgroup (Fin n → v.adicCompletion F)),
    (∀ o ∈ v.adicCompletionIntegers F, ∀ w ∈ S, o • w ∈ S) →
    (∃ t : v.adicCompletion F, t ≠ 0 ∧ ∀ w : Fin n → v.adicCompletion F,
      (∀ i, w i ∈ v.adicCompletionIntegers F) → t • w ∈ S) →
    (∃ t : v.adicCompletion F, t ≠ 0 ∧ ∀ w ∈ S, ∀ i, t * w i ∈ v.adicCompletionIntegers F) →
    (∀ x : GL (Fin n) (v.adicCompletion F), (∀ i j, x.1 i j ∈ v.adicCompletionIntegers F) →
      (∀ i j, (x⁻¹).1 i j ∈ v.adicCompletionIntegers F) → ∀ w ∈ S, x.1.mulVec w ∈ S) →
    ∃ t : v.adicCompletion F, t ≠ 0 ∧ ∀ w, w ∈ S ↔ ∀ i, t * w i ∈ v.adicCompletionIntegers F := by
  intro F _ _ v n S hO ⟨tl, htl0, htl⟩ ⟨tu, htu0, htu⟩ hGL
  classical
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨1, one_ne_zero, fun w => ?_⟩
    have hw : w = 0 := Subsingleton.elim _ _
    subst hw
    exact ⟨fun _ i => i.elim0, fun _ => S.zero_mem⟩
  have memO : ∀ x : v.adicCompletion F, x ∈ v.adicCompletionIntegers F ↔ Valued.v x ≤ 1 :=
    fun x => Iff.rfl

  have hbd : ∀ w ∈ S, ∀ i, Valued.v (w i) ≤ (Valued.v tu)⁻¹ := by
    intro w hw i
    have h := (memO _).1 (htu w hw i)
    rw [map_mul] at h
    have hu : Valued.v tu ≠ 0 := (Valuation.ne_zero_iff _).2 htu0
    calc Valued.v (w i) = (Valued.v tu)⁻¹ * (Valued.v tu * Valued.v (w i)) := by
          rw [← mul_assoc, inv_mul_cancel₀ hu, one_mul]
      _ ≤ (Valued.v tu)⁻¹ * 1 := by gcongr
      _ = (Valued.v tu)⁻¹ := mul_one _
  let P : ℤ → Prop := fun k => ∃ w ∈ S, ∃ i, Valued.v (w i) =
    ((Multiplicative.ofAdd k : Multiplicative ℤ) : WithZero (Multiplicative ℤ))
  obtain ⟨mB, hmB⟩ : ∃ m : Multiplicative ℤ, (m : WithZero (Multiplicative ℤ)) = (Valued.v tu)⁻¹ :=
    WithZero.ne_zero_iff_exists.1 (inv_ne_zero ((Valuation.ne_zero_iff _).2 htu0))
  have hPb : ∃ b : ℤ, ∀ z, P z → z ≤ b := by
    refine ⟨Multiplicative.toAdd mB, fun z ⟨w, hw, i, hz⟩ => ?_⟩
    have h := hbd w hw i
    rw [hz, ← hmB, WithZero.coe_le_coe] at h
    exact Multiplicative.ofAdd_le.1 (by simpa using h)
  let i₀' : Fin n := ⟨0, hn⟩
  have hPn : ∃ z, P z := by
    have hmem : tl • (fun _ => (1 : v.adicCompletion F)) ∈ S := htl _ (fun _ => one_mem _)
    obtain ⟨m, hm⟩ : ∃ m : Multiplicative ℤ, (m : WithZero (Multiplicative ℤ)) = Valued.v tl :=
      WithZero.ne_zero_iff_exists.1 ((Valuation.ne_zero_iff _).2 htl0)
    refine ⟨Multiplicative.toAdd m, _, hmem, i₀', ?_⟩
    simp [← hm]
  obtain ⟨lb, ⟨w₀, hw₀, i₀, hc⟩, hlb⟩ := Int.exists_greatest_of_bdd hPb hPn
  set c := w₀ i₀ with hcdef
  have hvc : Valued.v c ≠ 0 := by rw [hc]; exact WithZero.coe_ne_zero
  have hc0 : c ≠ 0 := fun h => hvc (by rw [h, map_zero])
  have hmax : ∀ w ∈ S, ∀ i, Valued.v (w i) ≤ Valued.v c := by
    intro w hw i
    by_cases h0 : w i = 0
    · rw [h0, map_zero]; exact zero_le'
    obtain ⟨m, hm⟩ : ∃ m : Multiplicative ℤ, (m : WithZero (Multiplicative ℤ)) = Valued.v (w i) :=
      WithZero.ne_zero_iff_exists.1 ((Valuation.ne_zero_iff _).2 h0)
    have hk := hlb (Multiplicative.toAdd m) ⟨w, hw, i, by simp [← hm]⟩
    rw [← hm, hc, WithZero.coe_le_coe]
    exact Multiplicative.toAdd_le.1 (by simpa using hk)
  have hint : ∀ w ∈ S, ∀ i, c⁻¹ * w i ∈ v.adicCompletionIntegers F := by
    intro w hw i
    rw [memO, map_mul, map_inv₀]
    calc (Valued.v c)⁻¹ * Valued.v (w i) ≤ (Valued.v c)⁻¹ * Valued.v c :=
          by gcongr; exact hmax w hw i
      _ = 1 := inv_mul_cancel₀ hvc

  have hsingle0 : Pi.single i₀ c ∈ S := by
    let N : Matrix (Fin n) (Fin n) (v.adicCompletion F) :=
      fun a b => if b = i₀ ∧ a ≠ i₀ then -(c⁻¹ * w₀ a) else 0
    have hN : N * N = 0 := by
      funext a b
      simp only [Matrix.mul_apply, Matrix.zero_apply]
      refine Finset.sum_eq_zero (fun m _ => ?_)
      by_cases hm : m = i₀ <;> simp [N, hm]
    have hNi : ∀ i j, N i j ∈ v.adicCompletionIntegers F := by
      intro i j
      simp only [N]
      split_ifs
      · exact neg_mem (hint w₀ hw₀ i)
      · exact zero_mem _
    have h := one_add_mulVec_mem v S hGL N hN hNi hw₀
    convert h using 1
    funext a
    rw [Matrix.add_mulVec, Matrix.one_mulVec, Pi.add_apply]
    by_cases ha : a = i₀
    · subst ha
      simp [N, Matrix.mulVec, dotProduct, hcdef]
    · simp [N, Matrix.mulVec, dotProduct, ha, Pi.single_apply, ← hcdef]
      field_simp
      ring
  have hsingle : ∀ j, Pi.single j c ∈ S := by
    intro j
    by_cases hj : j = i₀
    · subst hj; exact hsingle0
    let N : Matrix (Fin n) (Fin n) (v.adicCompletion F) :=
      fun a b => if a = j ∧ b = i₀ then 1 else 0
    have hN : N * N = 0 := by
      funext a b
      simp only [Matrix.mul_apply, Matrix.zero_apply]
      refine Finset.sum_eq_zero (fun m _ => ?_)
      by_cases hm : m = i₀
      · subst hm; simp [N, Ne.symm hj]
      · simp [N, hm]
    have hNi : ∀ i k, N i k ∈ v.adicCompletionIntegers F := by
      intro i k
      simp only [N]
      split_ifs
      · exact one_mem _
      · exact zero_mem _
    have h := one_add_mulVec_mem v S hGL N hN hNi hsingle0
    have heq : (1 + N).mulVec (Pi.single i₀ c) = Pi.single i₀ c + Pi.single j c := by
      funext a
      rw [Matrix.add_mulVec, Matrix.one_mulVec]
      simp [N, Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [heq] at h
    simpa using S.sub_mem h hsingle0
  refine ⟨c⁻¹, inv_ne_zero hc0, fun w => ⟨fun hw i => hint w hw i, fun hw => ?_⟩⟩
  have hsum : w = ∑ j, (c⁻¹ * w j) • Pi.single j c := by
    funext a
    rw [Finset.sum_apply, Finset.sum_eq_single a]
    · simp only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul]
      field_simp
    · intro b _ hb
      simp [Pi.single_apply, Ne.symm hb]
    · simp
  rw [hsum]
  exact S.sum_mem (fun j _ => hO _ (hw j) _ (hsingle j))

end GlobalTheory.LatticeBetweenMultiples
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPlaceHyperspecialStableLatticeEqMultiple

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram SphOp hyp)
open GlobalTheory.StdFrame (StdPsi)
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI

namespace GlobalTheory.SplitLatMatch

open GlobalTheory.SplitHecke

variable {D : D7}



theorem half (V : HSp D) (e : Formalism.L2.Theta.AE D) (he : IsSplitIdem D e)
    (M : AddSubgroup (Fin V.rank → (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)))
    (hM : ∀ a ∈ intAE D, ∀ z ∈ M, a • z ∈ M)
    (hf : ∀ z ∈ M, finPart D (e + cA D e) • z = z)
    (hb : ∃ N : ℕ, 0 < N ∧ (∀ y ∈ Formalism.L2.NTheta.LamHat V, ((N : ℕ) : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) • (finPart D (e + cA D e) • y) ∈ M) ∧ ∀ z ∈ M, ((N : ℕ) : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) • z ∈ Formalism.L2.NTheta.LamHat V)
    (hK : ∀ g : GA D V, g ∈ KsphC V ∅ → SuppF V (e + cA D e) g → ∀ z ∈ M, (finMat D.sp.cm.sig V.gram g).mulVec z ∈ M) :
    ∃ a a' : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E, finPart D e * a * a' = finPart D e ∧
      ∀ z, (finPart D e • z ∈ M ↔ (finPart D e * a) • z ∈ Formalism.L2.NTheta.LamHat V) := by
  obtain ⟨v, π, hπ⟩ := GlobalTheory.SplitChart.exists_chart e he
  obtain ⟨β, hβ⟩ := GlobalTheory.SplitFrame.exists_frame e v π he hπ V
  obtain ⟨φ, hφ⟩ := GlobalTheory.SplitFrame.exists_factor hπ
  have hπe : π e = 1 := GlobalTheory.SplitHomLattice.pi_idem he hπ
  have hpe : φ (finPart D e) = 1 := by rw [hφ]; exact hπe
  have hpp : finPart D e * finPart D e = finPart D e := by rw [← map_mul, he.1]
  have hpO : finPart D e ∈ intAE D := GlobalTheory.AdIdem.idempotent_mem_intAE D _ hpp
  have hpq : finPart D e * finPart D (cA D e) = 0 := by rw [← map_mul, he.2.1, map_zero]
  have hφs : Function.Surjective φ := fun t => by
    obtain ⟨a, rfl⟩ := hπ.1 t
    exact ⟨finPart D a, hφ a⟩
  have hker : ∀ x, φ x = 0 → finPart D e * x = 0 := by
    intro x hx
    obtain ⟨a, rfl⟩ := GlobalTheory.SplitHecke.Stab.finPart_surj x
    rw [hφ] at hx
    rw [← map_mul, (hπ.2.1 a).1 hx, map_zero]
  let T : (Fin V.rank → (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) →+ (Fin V.rank → Fv D.host.F v) :=
    { toFun := fun z => (β⁻¹).1 *ᵥ fun k => φ (z k)
      map_zero' := by
        have : (fun k : Fin V.rank => φ ((0 : Fin V.rank → (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) k)) = 0 :=
          funext fun k => by rw [Pi.zero_apply, map_zero, Pi.zero_apply]
        simp only [this, Matrix.mulVec_zero]
      map_add' := by
        intro x y
        have : (fun k => φ ((x + y) k)) = (fun k => φ (x k)) + fun k => φ (y k) :=
          funext fun k => by rw [Pi.add_apply, map_add (f := _), Pi.add_apply]
        simp only [this, Matrix.mulVec_add] }
  have hT : ∀ z, T z = (β⁻¹).1 *ᵥ fun k => φ (z k) := fun z => rfl
  have hTs : ∀ (x : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) z, T (x • z) = φ x • T z := by
    intro x z
    rw [hT, hT, ← Matrix.mulVec_smul]
    congr 1
    funext k
    rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, map_mul]
  have hTp : ∀ z, T (finPart D e • z) = T z := by
    intro z; rw [hTs, hpe, one_smul]
  have hmem : ∀ z, finPart D e • z ∈ Formalism.L2.NTheta.LamHat V ↔ ∀ i, T z i ∈ v.adicCompletionIntegers D.host.F := by
    intro z
    choose y hy using fun k => GlobalTheory.SplitHecke.Stab.finPart_surj (z k)
    have e1 : finPart D e • z = fun i => finPart D (e * y i) := funext fun i => by
      rw [Pi.smul_apply, smul_eq_mul, map_mul, hy]
    have e2 : (fun k => φ (z k)) = fun k => π (y k) := funext fun k => by rw [← hy, hφ]
    rw [e1, hβ y, hT, e2]
    exact forall_congr' fun i => isInt_Ov
  have hinj : ∀ z m, T z = T m → finPart D e • z = finPart D e • m := by
    intro z m h
    have h1 : (fun k => φ (z k)) = fun k => φ (m k) := by
      have := congrArg (fun u => β.1 *ᵥ u) h
      simpa only [hT, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.one_mulVec] using this
    funext k
    have h2 := hker (z k - m k) (by rw [map_sub, sub_eq_zero]; exact congrFun h1 k)
    rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
    rw [mul_sub, sub_eq_zero] at h2
    exact h2
  let S : AddSubgroup (Fin V.rank → Fv D.host.F v) := M.map T
  have hS : ∀ z, T z ∈ S ↔ finPart D e • z ∈ M := by
    intro z
    constructor
    · rintro ⟨m, hm, h⟩
      rw [hinj z m h.symm]
      exact hM _ hpO m hm
    · intro h
      exact ⟨_, h, hTp z⟩
  obtain ⟨N, hN, hlo, hup⟩ := hb
  have : CharZero (Fv D.host.F v) := charZero_of_injective_algebraMap (algebraMap D.host.F (Fv D.host.F v)).injective
  have hN' : ((N : ℕ) : Fv D.host.F v) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have hφN : φ ((N : ℕ) : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) = (N : Fv D.host.F v) := map_natCast φ N
  have hf' : finPart D (e + cA D e) * finPart D e = finPart D e := by
    rw [map_add, add_mul, hpp, mul_comm (finPart D (cA D e)), hpq, add_zero]
  obtain ⟨t, ht, hSt⟩ := GlobalTheory.LatticeBetweenMultiples.eq_multiple_of_standard_lattice v S (by
      intro o ho w hw
      obtain ⟨m, hm, rfl⟩ := hw
      obtain ⟨a, ha⟩ := hπ.1 o
      refine ⟨finPart D (e * a) • m, hM _ ((hπ.2.2.2 a).2 (isInt_Ov.2 (ha ▸ ho))) m hm, ?_⟩
      rw [hTs, hφ, map_mul, hπe, one_mul, ha])
    (by
      refine ⟨N, hN', fun w hw => ?_⟩
      choose z hz using fun k => hφs ((β.1 *ᵥ w) k)
      have hTz : T z = w := by
        rw [hT, (funext hz : (fun k => φ (z k)) = β.1 *ᵥ w), Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel,
          Units.val_one, Matrix.one_mulVec]
      have hzL : finPart D e • z ∈ Formalism.L2.NTheta.LamHat V := (hmem z).2 (by rw [hTz]; exact hw)
      have h1 := hlo _ hzL
      rw [smul_smul (finPart D (e + cA D e)), hf'] at h1
      exact ⟨_, h1, by rw [hTs, hTp, hφN, hTz]⟩)
    (by
      refine ⟨N, hN', fun w hw i => ?_⟩
      obtain ⟨m, hm, rfl⟩ := hw
      have h2 : finPart D e • (((N : ℕ) : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) • m) ∈ Formalism.L2.NTheta.LamHat V :=
        GlobalTheory.LatDual.smul_mem_lamHat V _ hpO _ (hup m hm)
      have h3 := (hmem _).1 h2 i
      rwa [hTs, hφN, Pi.smul_apply, smul_eq_mul] at h3)
    (by
      intro x hx1 hx2 w hw
      obtain ⟨m, hm, rfl⟩ := hw
      obtain ⟨g, hg, hgx⟩ := GlobalTheory.SplitOnto.exists_suppAt_rho_eq e v π he hπ V β x
      have hgK : g ∈ KsphC V ∅ := (GlobalTheory.SplitHecke.Stab.mem_KsphC_iff_gInt e v π he hπ V β hβ g hg).2 (by
        rw [hgx]
        exact ⟨fun i j => isInt_Ov.2 (hx1 i j), fun i j => isInt_Ov.2 (hx2 i j)⟩)
      refine ⟨_, hK g hgK hg m hm, ?_⟩
      have e1 : (fun k => φ ((finMat D.sp.cm.sig V.gram g *ᵥ m) k)) = (mt V g).map π *ᵥ fun k => φ (m k) := by
        funext k
        rw [RingHom.map_mulVec, GlobalTheory.SplitHecke.Stab.finMat_eq, Matrix.map_map]
        congr 2
        funext y
        exact hφ y
      rw [hT, hT, e1, ← hgx, rho_val, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
        Matrix.mul_assoc _ β.1, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one])
  obtain ⟨a, ha⟩ := hφs t
  obtain ⟨a', ha'⟩ := hφs t⁻¹
  refine ⟨a, a', ?_, fun z => ?_⟩
  · have := hker (a * a' - 1) (by rw [map_sub, map_mul, ha, ha', mul_inv_cancel₀ ht, map_one, sub_self])
    linear_combination this
  · rw [← hS, hSt, mul_smul, hmem, hTs, ha]
    simp only [Pi.smul_apply, smul_eq_mul]

end GlobalTheory.SplitLatMatch

namespace GlobalTheory.SplitLatMatch

variable {D : D7}



theorem lat_split : ∀ {D : D7} (V : HSp D) (P : Pl D.host.E) (e : Formalism.L2.Theta.AE D), Formalism.L2.NTheta.IsIdemAt e P → ∀ (M : AddSubgroup (Fin V.rank → (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E))), (∀ a ∈ intAE D, ∀ z ∈ M, a • z ∈ M) → (∀ z ∈ M, finPart D (e + cA D e) • z = z) → (∃ N : ℕ, 0 < N ∧ (∀ y ∈ Formalism.L2.NTheta.LamHat V, ((N : ℕ) : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) • (finPart D (e + cA D e) • y) ∈ M) ∧ ∀ z ∈ M, ((N : ℕ) : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) • z ∈ Formalism.L2.NTheta.LamHat V) → (∀ g : GA D V, g ∈ KsphC V ∅ → SuppF V (e + cA D e) g → ∀ z ∈ M, (finMat D.sp.cm.sig V.gram g).mulVec z ∈ M) → ∃ c : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E), IsUnit c ∧ ∀ z, z ∈ M ↔ (finPart D (e + cA D e) • z = z ∧ c • z ∈ Formalism.L2.NTheta.LamHat V) := by
  intro D V P e hP M hMs hf hb hK
  have he : IsSplitIdem D e := hP.1
  have he' := GlobalTheory.SplitScalar.isSplitIdem_conj he
  obtain ⟨a, a', ha, hA⟩ := half V e he M hMs hf hb hK
  have hsum : cA D e + cA D (cA D e) = e + cA D e := by rw [cA_cA, add_comm]
  obtain ⟨b, b', hb', hB⟩ := half V (cA D e) he' M hMs (by rw [hsum]; exact hf) (by rw [hsum]; exact hb)
    (by rw [hsum]; exact hK)
  have hpp : finPart D e * finPart D e = finPart D e := by rw [← map_mul, he.1]
  have hqq : finPart D (cA D e) * finPart D (cA D e) = finPart D (cA D e) := by rw [← map_mul, he'.1]
  have hpq : finPart D e * finPart D (cA D e) = 0 := by rw [← map_mul, he.2.1, map_zero]
  have hpO : finPart D e ∈ intAE D := GlobalTheory.AdIdem.idempotent_mem_intAE D _ hpp
  have hqO : finPart D (cA D e) ∈ intAE D := GlobalTheory.AdIdem.idempotent_mem_intAE D _ hqq
  have hfe : finPart D (e + cA D e) = finPart D e + finPart D (cA D e) := map_add _ _ _
  rw [hfe] at hf
  rw [hfe]
  refine ⟨finPart D e * a + finPart D (cA D e) * b + (1 - (finPart D e + finPart D (cA D e))),
    isUnit_iff_exists_inv.2 ⟨finPart D e * a' + finPart D (cA D e) * b' + (1 - (finPart D e + finPart D (cA D e))),
      by linear_combination (a * a' - a - a' + 1) * hpp + (b * b' - b - b' + 1) * hqq +
        (a * b' + b * a' - a - a' - b - b' + 2) * hpq + ha + hb'⟩, fun z => ⟨fun hz => ⟨hf z hz, ?_⟩, fun ⟨hz, hc⟩ => ?_⟩⟩
  · have h1 := (hA z).1 (hMs _ hpO z hz)
    have h2 := (hB z).1 (hMs _ hqO z hz)
    have h3 := hf z hz
    have e1 : (finPart D e * a + finPart D (cA D e) * b + (1 - (finPart D e + finPart D (cA D e)))) • z =
        (finPart D e * a) • z + (finPart D (cA D e) * b) • z + (z - (finPart D e + finPart D (cA D e)) • z) := by
      funext i
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [e1, h3, sub_self, add_zero]
    exact add_mem h1 h2
  · have e2 : ∀ (p c : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E), p * (finPart D e * a + finPart D (cA D e) * b + (1 - (finPart D e + finPart D (cA D e)))) = p * c →
        p • ((finPart D e * a + finPart D (cA D e) * b + (1 - (finPart D e + finPart D (cA D e)))) • z) = (p * c) • z := by
      intro p c h
      rw [smul_smul, h]
    have h1 : finPart D e • z ∈ M := (hA z).2 (by
      rw [← e2 (finPart D e) a (by linear_combination (a - 1) * hpp + (b - 1) * hpq)]
      exact GlobalTheory.LatDual.smul_mem_lamHat V _ hpO _ hc)
    have h2 : finPart D (cA D e) • z ∈ M := (hB z).2 (by
      rw [← e2 (finPart D (cA D e)) b (by linear_combination (b - 1) * hqq + (a - 1) * hpq)]
      exact GlobalTheory.LatDual.smul_mem_lamHat V _ hqO _ hc)
    rw [← hz, add_smul]
    exact add_mem h1 h2

end GlobalTheory.SplitLatMatch
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPlaceHyperspecialStableLatticeEqMultipleStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram SphOp hyp)
open GlobalTheory.StdFrame (StdPsi)
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI

theorem _root_.GlobalTheory.T.splitPlace_hyperspecialStable_lattice_eq_multiple : ∀ {D : D7} (V : HSp D) (P : Pl D.host.E) (e : Formalism.L2.Theta.AE D), Formalism.L2.NTheta.IsIdemAt e P → ∀ (M : AddSubgroup (Fin V.rank → (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E))), (∀ a ∈ intAE D, ∀ z ∈ M, a • z ∈ M) → (∀ z ∈ M, finPart D (e + cA D e) • z = z) → (∃ N : ℕ, 0 < N ∧ (∀ y ∈ Formalism.L2.NTheta.LamHat V, ((N : ℕ) : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) • (finPart D (e + cA D e) • y) ∈ M) ∧ ∀ z ∈ M, ((N : ℕ) : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) • z ∈ Formalism.L2.NTheta.LamHat V) → (∀ g : GA D V, g ∈ KsphC V ∅ → SuppF V (e + cA D e) g → ∀ z ∈ M, (finMat D.sp.cm.sig V.gram g).mulVec z ∈ M) → ∃ c : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E), IsUnit c ∧ ∀ z, z ∈ M ↔ (finPart D (e + cA D e) • z = z ∧ c • z ∈ Formalism.L2.NTheta.LamHat V) := by
  first | exact @GlobalTheory.SplitLatMatch.lat_split | exact GlobalTheory.SplitLatMatch.lat_split | (intros; apply GlobalTheory.SplitLatMatch.lat_split <;> assumption)
end
end
