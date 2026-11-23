module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NormStepsLeviOntoS
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NormStepsLeviElt
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NormStepsLeviFrame
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NormStepsMatLift

section

@[expose] public section

noncomputable section

open scoped Classical TensorProduct
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Matrix Formalism.L2.SG.Pf.unitaryCongruence

namespace Formalism.L2.SG.Pf.NormSteps.LeviOntoSPf

namespace MatLiftPf

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} (TR : TypedRed X)

theorem near_one (ηO : ↥(IntAf X.B.I.F X.B.I.E)) (hew : (ηO : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * X.ew = ηO)
    (P : Matrix (Fin D.R.k) (Fin D.R.k) ↥(IntAf X.B.I.F X.B.I.E)) (hP : ∀ v, P.map (TR.res v) = 1) :
    ∃ T : Matrix (Fin D.R.k) (Fin D.R.k) ↥(IntAf X.B.I.F X.B.I.E), ηO • P = ηO • (1 + ((X.B.g : ℕ) : ↥(IntAf X.B.I.F X.B.I.E)) • T) := by
  have h : ∀ i j, ∃ t : ↥(IntAf X.B.I.F X.B.I.E), X.ew * ((P - 1) i j : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) =
      ((X.B.g : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * t := by
    intro i j
    have h0 : ∀ v, TR.res v ((P - 1) i j) = 0 := fun v => by
      have := congrFun (congrFun (hP v) i) j
      simp only [Matrix.map_apply] at this
      rw [Matrix.sub_apply, map_sub, this, Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> simp
    obtain ⟨t, ht, e⟩ := (TR.res_ker _).1 h0
    exact ⟨⟨t, ht⟩, e⟩
  choose T hT using h
  refine ⟨Matrix.of T, ?_⟩
  ext i j
  have e := hT i j
  simp only [Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, Matrix.add_apply, Matrix.sub_apply] at e ⊢
  generalize ((1 : Matrix (Fin D.R.k) (Fin D.R.k) ↥(IntAf X.B.I.F X.B.I.E)) i j) = o at e ⊢
  push_cast at e ⊢
  linear_combination (ηO : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * e -
    ((P i j : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) - (o : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)) * hew

theorem det_near (T : Matrix (Fin D.R.k) (Fin D.R.k) ↥(IntAf X.B.I.F X.B.I.E)) :
    ∃ s0 : ↥(IntAf X.B.I.F X.B.I.E), (1 + ((X.B.g : ℕ) : ↥(IntAf X.B.I.F X.B.I.E)) • T).det = 1 + ((X.B.g : ℕ) : ↥(IntAf X.B.I.F X.B.I.E)) * s0 := by
  set J := Ideal.span {((X.B.g : ℕ) : ↥(IntAf X.B.I.F X.B.I.E))}
  have hm : (Ideal.Quotient.mk J).mapMatrix (1 + ((X.B.g : ℕ) : ↥(IntAf X.B.I.F X.B.I.E)) • T) = 1 := by
    have hg : Ideal.Quotient.mk J ((X.B.g : ℕ) : ↥(IntAf X.B.I.F X.B.I.E)) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)
    ext i j
    rcases eq_or_ne i j with rfl | hij <;> simp [Matrix.add_apply, *]
  have h1 : Ideal.Quotient.mk J ((1 + ((X.B.g : ℕ) : ↥(IntAf X.B.I.F X.B.I.E)) • T).det) = 1 := by
    rw [RingHom.map_det, hm, Matrix.det_one]
  have h2 : (1 + ((X.B.g : ℕ) : ↥(IntAf X.B.I.F X.B.I.E)) • T).det - 1 ∈ J := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, h1, map_one, sub_self]
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 h2
  exact ⟨a, by rw [mul_comm, ha]; ring⟩

theorem right_inv (ηO : ↥(IntAf X.B.I.F X.B.I.E)) (hew : (ηO : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * X.ew = ηO)
    (hj : ∀ s ∈ IntAf X.B.I.F X.B.I.E, ∃ s' ∈ IntAf X.B.I.F X.B.I.E,
      (ηO : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * ((1 + (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * s) * s') = ηO)
    (A B : Matrix (Fin D.R.k) (Fin D.R.k) ↥(IntAf X.B.I.F X.B.I.E)) (hAB : ∀ v, (A * B).map (TR.res v) = 1) :
    ∃ B' : Matrix (Fin D.R.k) (Fin D.R.k) ↥(IntAf X.B.I.F X.B.I.E), ηO • (A * B') = ηO • 1 := by
  obtain ⟨T, hT⟩ := near_one TR ηO hew (A * B) hAB
  obtain ⟨s0, hs0⟩ := det_near (X := X) T
  obtain ⟨s', hs', e⟩ := hj s0 s0.2
  have e' : ηO * ((1 + ((X.B.g : ℕ) : ↥(IntAf X.B.I.F X.B.I.E)) * s0) * ⟨s', hs'⟩) = ηO := Subtype.ext (by simpa using e)
  refine ⟨(⟨s', hs'⟩ : ↥(IntAf X.B.I.F X.B.I.E)) • (B * (1 + ((X.B.g : ℕ) : ↥(IntAf X.B.I.F X.B.I.E)) • T).adjugate), ?_⟩
  have e0 : A * ((⟨s', hs'⟩ : ↥(IntAf X.B.I.F X.B.I.E)) • (B * (1 + ((X.B.g : ℕ) : ↥(IntAf X.B.I.F X.B.I.E)) • T).adjugate)) =
      (⟨s', hs'⟩ : ↥(IntAf X.B.I.F X.B.I.E)) • (A * B * (1 + ((X.B.g : ℕ) : ↥(IntAf X.B.I.F X.B.I.E)) • T).adjugate) := by
    rw [Matrix.mul_smul, Matrix.mul_assoc]
  rw [e0, smul_comm, ← Matrix.smul_mul, hT, Matrix.smul_mul, Matrix.mul_adjugate, hs0, smul_smul, smul_smul]
  congr 1
  linear_combination e'

theorem left_inv (ηO : ↥(IntAf X.B.I.F X.B.I.E)) (hew : (ηO : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * X.ew = ηO)
    (hj : ∀ s ∈ IntAf X.B.I.F X.B.I.E, ∃ s' ∈ IntAf X.B.I.F X.B.I.E,
      (ηO : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * ((1 + (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * s) * s') = ηO)
    (A B : Matrix (Fin D.R.k) (Fin D.R.k) ↥(IntAf X.B.I.F X.B.I.E)) (hAB : ∀ v, (B * A).map (TR.res v) = 1) :
    ∃ B' : Matrix (Fin D.R.k) (Fin D.R.k) ↥(IntAf X.B.I.F X.B.I.E), ηO • (B' * A) = ηO • 1 := by
  obtain ⟨T, hT⟩ := near_one TR ηO hew (B * A) hAB
  obtain ⟨s0, hs0⟩ := det_near (X := X) T
  obtain ⟨s', hs', e⟩ := hj s0 s0.2
  have e' : ηO * ((1 + ((X.B.g : ℕ) : ↥(IntAf X.B.I.F X.B.I.E)) * s0) * ⟨s', hs'⟩) = ηO := Subtype.ext (by simpa using e)
  refine ⟨(⟨s', hs'⟩ : ↥(IntAf X.B.I.F X.B.I.E)) • ((1 + ((X.B.g : ℕ) : ↥(IntAf X.B.I.F X.B.I.E)) • T).adjugate * B), ?_⟩
  have e0 : ((⟨s', hs'⟩ : ↥(IntAf X.B.I.F X.B.I.E)) • ((1 + ((X.B.g : ℕ) : ↥(IntAf X.B.I.F X.B.I.E)) • T).adjugate * B)) * A =
      (⟨s', hs'⟩ : ↥(IntAf X.B.I.F X.B.I.E)) • ((1 + ((X.B.g : ℕ) : ↥(IntAf X.B.I.F X.B.I.E)) • T).adjugate * (B * A)) := by
    rw [Matrix.smul_mul, Matrix.mul_assoc]
  rw [e0, smul_comm, ← Matrix.mul_smul, hT, Matrix.mul_smul, Matrix.adjugate_mul, hs0, smul_smul, smul_smul]
  congr 1
  linear_combination e'

theorem coe_eq (ηO : ↥(IntAf X.B.I.F X.B.I.E)) (P Q : Matrix (Fin D.R.k) (Fin D.R.k) ↥(IntAf X.B.I.F X.B.I.E)) (h : ηO • (P * Q) = ηO • 1) :
    (ηO : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (P.map Subtype.val * Q.map Subtype.val) =
      (ηO : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (1 : Matrix (Fin D.R.k) (Fin D.R.k) (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)) := by
  ext i j
  have := congrArg (fun M : Matrix (Fin D.R.k) (Fin D.R.k) ↥(IntAf X.B.I.F X.B.I.E) => ((M i j : ↥(IntAf X.B.I.F X.B.I.E)) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)) h
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Subring.coe_mul, Matrix.map_apply,
    Matrix.one_apply] at this ⊢
  push_cast at this
  split_ifs at this ⊢ <;> simpa using this

theorem integral_matrix_lift_exists : MatLift TR := by
  intro η hη _ hew _ hj s
  set ηO : ↥(IntAf X.B.I.F X.B.I.E) := ⟨η, hη⟩
  have hs : ∀ i j, ∃ c : ↥(IntAf X.B.I.F X.B.I.E), ∀ v, TR.res v c = (↑(s v) : Matrix (Fin D.R.k) (Fin D.R.k) (TR.Fq v)) i j :=
    fun i j => by
      obtain ⟨c, hc⟩ := TR.res_joint (fun v => (↑(s v) : Matrix (Fin D.R.k) (Fin D.R.k) (TR.Fq v)) i j)
      exact ⟨c, fun v => congrFun hc v⟩
  have hs' : ∀ i j, ∃ c : ↥(IntAf X.B.I.F X.B.I.E), ∀ v,
      TR.res v c = (↑((s v)⁻¹) : Matrix (Fin D.R.k) (Fin D.R.k) (TR.Fq v)) i j :=
    fun i j => by
      obtain ⟨c, hc⟩ := TR.res_joint (fun v => (↑((s v)⁻¹) : Matrix (Fin D.R.k) (Fin D.R.k) (TR.Fq v)) i j)
      exact ⟨c, fun v => congrFun hc v⟩
  choose A hA using hs
  choose B hB using hs'
  have hAm : ∀ v, (Matrix.of A).map (TR.res v) = (↑(s v) : Matrix (Fin D.R.k) (Fin D.R.k) (TR.Fq v)) := fun v => by
    ext i j; simp [hA]
  have hBm : ∀ v, (Matrix.of B).map (TR.res v) = (↑((s v)⁻¹) : Matrix (Fin D.R.k) (Fin D.R.k) (TR.Fq v)) :=
    fun v => by ext i j; simp [hB]
  have hAB : ∀ v, (Matrix.of A * Matrix.of B).map (TR.res v) = 1 := fun v => by
    rw [Matrix.map_mul, hAm, hBm, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hBA : ∀ v, (Matrix.of B * Matrix.of A).map (TR.res v) = 1 := fun v => by
    rw [Matrix.map_mul, hAm, hBm, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  obtain ⟨R', hR'⟩ := right_inv TR ηO hew hj (Matrix.of A) (Matrix.of B) hAB
  obtain ⟨L', hL'⟩ := left_inv TR ηO hew hj (Matrix.of A) (Matrix.of B) hBA
  have e1 : ηO • L' = ηO • R' := by
    calc ηO • L' = L' * (ηO • (1 : Matrix (Fin D.R.k) (Fin D.R.k) ↥(IntAf X.B.I.F X.B.I.E))) := by rw [Matrix.mul_smul, Matrix.mul_one]
      _ = L' * (ηO • (Matrix.of A * R')) := by rw [hR']
      _ = (ηO • (L' * Matrix.of A)) * R' := by rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
      _ = ηO • R' := by rw [hL', Matrix.smul_mul, Matrix.one_mul]
  refine ⟨(Matrix.of A).map Subtype.val, R'.map Subtype.val, fun i j => ⟨(A i j).2, (R' i j).2⟩, ?_, ?_, ?_⟩
  · exact coe_eq ηO _ _ hR'
  · refine coe_eq ηO _ _ ?_
    calc ηO • (R' * Matrix.of A) = (ηO • R') * Matrix.of A := by rw [Matrix.smul_mul]
      _ = (ηO • L') * Matrix.of A := by rw [e1]
      _ = ηO • 1 := by rw [Matrix.smul_mul, hL']
  · intro v
    ext i j
    show resT TR v ((A i j : ↥(IntAf X.B.I.F X.B.I.E)) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) =
      (↑(s v) : Matrix (Fin D.R.k) (Fin D.R.k) (TR.Fq v)) i j
    rw [LeviEltPf.resT_of_mem TR v (A i j).2]
    exact hA i j v

end MatLiftPf

end Formalism.L2.SG.Pf.NormSteps.LeviOntoSPf
end
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NormStepsSIdem

section

@[expose] public section

noncomputable section

open scoped Classical TensorProduct
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Polynomial Formalism.L2.SG.Pf.unitaryCongruence

namespace Formalism.L2.SG.Pf.NormSteps.LeviOntoSPf

namespace SIdemPf

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

def OverG (v : HeightOneSpectrum (𝓞 X.B.I.F)) : Prop := ((X.B.g : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal

theorem val_g (v : HeightOneSpectrum (𝓞 X.B.I.F)) :
    Valued.v ((X.B.g : ℕ) : v.adicCompletion X.B.I.F) = v.intValuation ((X.B.g : ℕ) : 𝓞 X.B.I.F) := by
  have h : ((X.B.g : ℕ) : v.adicCompletion X.B.I.F) =
      ((algebraMap (𝓞 X.B.I.F) X.B.I.F ((X.B.g : ℕ) : 𝓞 X.B.I.F) : X.B.I.F) : v.adicCompletion X.B.I.F) := by
    rw [map_natCast]
    exact (map_natCast (algebraMap X.B.I.F (v.adicCompletion X.B.I.F)) _).symm
  rw [h, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_of_algebraMap]

def eS : Af X.B.I.F :=
  ⟨fun v => if OverG X v then 1 else 0, Filter.Eventually.of_forall fun v => by
    show (if OverG X v then 1 else 0 : v.adicCompletion X.B.I.F) ∈ v.adicCompletionIntegers X.B.I.F
    split_ifs
    · exact one_mem _
    · exact zero_mem _⟩

theorem eS_apply (v : HeightOneSpectrum (𝓞 X.B.I.F)) : eS X v = if OverG X v then 1 else 0 := rfl

def tS : Af X.B.I.F :=
  ⟨fun v => if OverG X v then 0 else ((X.B.g : ℕ) : v.adicCompletion X.B.I.F)⁻¹,
    Filter.Eventually.of_forall fun v => by
      show (if OverG X v then 0 else ((X.B.g : ℕ) : v.adicCompletion X.B.I.F)⁻¹) ∈ v.adicCompletionIntegers X.B.I.F
      split_ifs with h
      · exact zero_mem _
      · rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, val_g]
        have h1 : v.intValuation ((X.B.g : ℕ) : 𝓞 X.B.I.F) = 1 := by
          refine le_antisymm (v.intValuation_le_one _) (not_lt.1 fun hl => h ?_)
          exact (v.intValuation_lt_one_iff_mem _).1 hl
        rw [h1, inv_one]⟩

theorem tS_apply (v : HeightOneSpectrum (𝓞 X.B.I.F)) :
    tS X v = if OverG X v then 0 else ((X.B.g : ℕ) : v.adicCompletion X.B.I.F)⁻¹ := rfl

theorem eS_int : eS X ∈ Formalism.UG.intAd X.B.I.F := fun v => by
  show eS X v ∈ v.adicCompletionIntegers X.B.I.F
  rw [eS_apply]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

theorem natCast_apply (v : HeightOneSpectrum (𝓞 X.B.I.F)) (m : ℕ) :
    ((m : Af X.B.I.F) : Af X.B.I.F) v = (m : v.adicCompletion X.B.I.F) := by
  induction m with
  | zero => rfl
  | succ n ih =>
    rw [Nat.cast_succ, Nat.cast_succ, ← ih]
    rfl

theorem val_g_lt (v : HeightOneSpectrum (𝓞 X.B.I.F)) (h : OverG X v) :
    Valued.v ((X.B.g : ℕ) : v.adicCompletion X.B.I.F) < 1 := by
  rw [val_g]
  exact (v.intValuation_lt_one_iff_mem _).2 h

theorem val_g_eq (v : HeightOneSpectrum (𝓞 X.B.I.F)) (h : ¬ OverG X v) :
    Valued.v ((X.B.g : ℕ) : v.adicCompletion X.B.I.F) = 1 := by
  rw [val_g]
  exact le_antisymm (v.intValuation_le_one _)
    (not_lt.1 fun hl => h ((v.intValuation_lt_one_iff_mem _).1 hl))

theorem tS_int : tS X ∈ Formalism.UG.intAd X.B.I.F := fun v => by
  show tS X v ∈ v.adicCompletionIntegers X.B.I.F
  rw [tS_apply]
  split_ifs with h
  · exact zero_mem _
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, val_g_eq X v h, inv_one]

theorem one_sub_eS : (1 : Af X.B.I.F) - eS X = ((X.B.g : ℕ) : Af X.B.I.F) * tS X := by
  ext v : 1
  show (1 : v.adicCompletion X.B.I.F) - eS X v = ((X.B.g : ℕ) : Af X.B.I.F) v * tS X v
  rw [natCast_apply, eS_apply, tS_apply]
  split_ifs with h
  · simp
  · have hne : ((X.B.g : ℕ) : v.adicCompletion X.B.I.F) ≠ 0 := by
      intro h0
      have := val_g_eq X v h
      rw [h0, map_zero] at this
      exact zero_ne_one this
    rw [sub_zero, mul_inv_cancel₀ hne]

theorem eS_idem : eS X * eS X = eS X := by
  ext v : 1
  show eS X v * eS X v = eS X v
  rw [eS_apply]
  split_ifs <;> simp

theorem unit_on_S (d : ↥(Formalism.UG.intAd X.B.I.F)) :
    ∃ z ∈ Formalism.UG.intAd X.B.I.F, eS X * ((1 + ((X.B.g : ℕ) : Af X.B.I.F) * d) * z) = eS X := by

  have hval : ∀ v, OverG X v →
      Valued.v (1 + ((X.B.g : ℕ) : v.adicCompletion X.B.I.F) * (d : Af X.B.I.F) v) = 1 := by
    intro v hv
    refine Valuation.map_one_add_of_lt _ ?_
    rw [map_mul]
    have hd : Valued.v ((d : Af X.B.I.F) v) ≤ 1 := d.2 v
    calc Valued.v ((X.B.g : ℕ) : v.adicCompletion X.B.I.F) * Valued.v ((d : Af X.B.I.F) v)
        ≤ Valued.v ((X.B.g : ℕ) : v.adicCompletion X.B.I.F) := mul_le_of_le_one_right' hd
      _ < 1 := val_g_lt X v hv
  have hmem : ∀ v, (if OverG X v then (1 + ((X.B.g : ℕ) : v.adicCompletion X.B.I.F) *
      (d : Af X.B.I.F) v)⁻¹ else 0) ∈ v.adicCompletionIntegers X.B.I.F := by
    intro v
    split_ifs with hv
    · rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hval v hv, inv_one]
    · exact zero_mem _
  let z : Af X.B.I.F := ⟨fun v => if OverG X v then (1 + ((X.B.g : ℕ) : v.adicCompletion X.B.I.F) *
      (d : Af X.B.I.F) v)⁻¹ else 0, Filter.Eventually.of_forall hmem⟩
  refine ⟨z, fun v => hmem v, ?_⟩
  ext v : 1
  show eS X v * ((1 + ((X.B.g : ℕ) : Af X.B.I.F) v * (d : Af X.B.I.F) v) * z v) = eS X v
  rw [natCast_apply, eS_apply]
  show _ * (_ * (if OverG X v then _ else 0)) = _
  split_ifs with hv
  · have hne : (1 + ((X.B.g : ℕ) : v.adicCompletion X.B.I.F) * (d : Af X.B.I.F) v) ≠ 0 := by
      intro h0
      have := hval v hv
      rw [h0, map_zero] at this
      exact zero_ne_one this
    rw [mul_inv_cancel₀ hne, mul_one]
  · rw [zero_mul]

def phi : ↥(Formalism.UG.intAd X.B.I.F) →+* X.B.I.E ⊗[X.B.I.F] Af X.B.I.F :=
  (Algebra.TensorProduct.includeRight : Af X.B.I.F →ₐ[X.B.I.F] X.B.I.E ⊗[X.B.I.F] Af X.B.I.F).toRingHom.comp
    (Formalism.UG.intAd X.B.I.F).subtype

theorem phi_apply (a : ↥(Formalism.UG.intAd X.B.I.F)) : phi X a = (1 : X.B.I.E) ⊗ₜ[X.B.I.F] (a : Af X.B.I.F) := rfl

theorem phi_mem (a : ↥(Formalism.UG.intAd X.B.I.F)) : phi X a ∈ IntAf X.B.I.F X.B.I.E :=
  Subring.subset_closure (Set.mem_union_right _ ⟨a, rfl⟩)

theorem integral_of_mem {s : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F} (hs : s ∈ IntAf X.B.I.F X.B.I.E) :
    ∃ p : Polynomial ↥(Formalism.UG.intAd X.B.I.F), p.Monic ∧ p.eval₂ (phi X) s = 0 := by
  show (phi X).IsIntegralElem s
  induction hs using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨⟨x, hx⟩, rfl⟩ | ⟨y, rfl⟩
    · obtain ⟨y, rfl⟩ := hx
      have hi : IsIntegral ℤ (algebraMap (𝓞 X.B.I.E) X.B.I.E y) := y.isIntegral_coe
      obtain ⟨q, hq, hev⟩ := hi
      let f : X.B.I.E →+* X.B.I.E ⊗[X.B.I.F] Af X.B.I.F := (Algebra.TensorProduct.includeLeft :
        X.B.I.E →ₐ[X.B.I.F] X.B.I.E ⊗[X.B.I.F] Af X.B.I.F).toRingHom
      show (phi X).IsIntegralElem (f (algebraMap (𝓞 X.B.I.E) X.B.I.E y))
      refine ⟨q.map (Int.castRingHom ↥(Formalism.UG.intAd X.B.I.F)), hq.map _, ?_⟩
      rw [Polynomial.eval₂_map, show (phi X).comp (Int.castRingHom ↥(Formalism.UG.intAd X.B.I.F)) =
        f.comp (algebraMap ℤ X.B.I.E) from RingHom.ext_int _ _, ← Polynomial.hom_eval₂, hev, map_zero]
    · exact (phi X).isIntegralElem_map
  | zero => simpa using (phi X).isIntegralElem_map (x := 0)
  | one => simpa using (phi X).isIntegralElem_map (x := 1)
  | add x y _ _ hx hy => exact RingHom.IsIntegralElem.add _ hx hy
  | neg x _ hx =>
    have e : -x = phi X (-1) * x := by rw [map_neg, map_one, neg_one_mul]
    rw [e]
    exact RingHom.IsIntegralElem.mul _ (phi X).isIntegralElem_map hx
  | mul x y _ _ hx hy => exact RingHom.IsIntegralElem.mul _ hx hy

theorem eval₂_mem (r : Polynomial ↥(Formalism.UG.intAd X.B.I.F)) {u : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F}
    (hu : u ∈ IntAf X.B.I.F X.B.I.E) : r.eval₂ (phi X) u ∈ IntAf X.B.I.F X.B.I.E := by
  rw [Polynomial.eval₂_eq_sum_range]
  exact Subring.sum_mem _ fun i _ => Subring.mul_mem _ (phi_mem X _) (Subring.pow_mem _ hu _)

theorem near_inv {s : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F} (hs : s ∈ IntAf X.B.I.F X.B.I.E) :
    ∃ w ∈ IntAf X.B.I.F X.B.I.E, ∃ d : ↥(Formalism.UG.intAd X.B.I.F),
      (1 + ((X.B.g : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * s) * w =
        phi X (1 + ((X.B.g : ℕ) : ↥(Formalism.UG.intAd X.B.I.F)) * d) := by
  obtain ⟨p, hp, hps⟩ := integral_of_mem X hs
  have hgphi : phi X ((X.B.g : ℕ) : ↥(Formalism.UG.intAd X.B.I.F)) = ((X.B.g : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) := map_natCast _ _
  have hsc : (p.scaleRoots ((X.B.g : ℕ) : ↥(Formalism.UG.intAd X.B.I.F))).eval₂ (phi X)
      (phi X ((X.B.g : ℕ) : ↥(Formalism.UG.intAd X.B.I.F)) * s) = 0 := Polynomial.scaleRoots_eval₂_eq_zero (phi X) hps

  have hdvd : Polynomial.C ((X.B.g : ℕ) : ↥(Formalism.UG.intAd X.B.I.F)) ∣
      p.scaleRoots ((X.B.g : ℕ) : ↥(Formalism.UG.intAd X.B.I.F)) - Polynomial.X ^ p.natDegree := by
    rw [Polynomial.C_dvd_iff_dvd_coeff]
    intro i
    rw [Polynomial.coeff_sub, Polynomial.coeff_scaleRoots, Polynomial.coeff_X_pow]
    rcases lt_trichotomy i p.natDegree with hi | hi | hi
    · rw [if_neg hi.ne, sub_zero]
      exact Dvd.dvd.mul_left (dvd_pow_self _ (Nat.sub_ne_zero_of_lt hi)) _
    · rw [hi, if_pos rfl, Nat.sub_self, pow_zero, mul_one, hp.coeff_natDegree, sub_self]
      exact dvd_zero _
    · rw [if_neg hi.ne', Polynomial.coeff_eq_zero_of_natDegree_lt hi, zero_mul, sub_zero]
      exact dvd_zero _
  obtain ⟨q, hq⟩ := hdvd
  have hsr : p.scaleRoots ((X.B.g : ℕ) : ↥(Formalism.UG.intAd X.B.I.F)) =
      Polynomial.X ^ p.natDegree + Polynomial.C ((X.B.g : ℕ) : ↥(Formalism.UG.intAd X.B.I.F)) * q := by
    rw [← hq]; ring
  have hP2 : ((p.scaleRoots ((X.B.g : ℕ) : ↥(Formalism.UG.intAd X.B.I.F))).comp (Polynomial.X - 1)).eval₂ (phi X)
      (1 + ((X.B.g : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * s) = 0 := by
    rw [Polynomial.eval₂_comp, Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_one]
    have e : 1 + ((X.B.g : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * s - 1 = phi X ((X.B.g : ℕ) : ↥(Formalism.UG.intAd X.B.I.F)) * s := by
      rw [hgphi]; ring
    rw [e]; exact hsc
  obtain ⟨Q, hQ⟩ := Polynomial.X_dvd_sub_C (p := (p.scaleRoots ((X.B.g : ℕ) : ↥(Formalism.UG.intAd X.B.I.F))).comp (Polynomial.X - 1))
  rw [Polynomial.coeff_zero_eq_eval_zero] at hQ
  have hev := congrArg (Polynomial.eval₂ (phi X) (1 + ((X.B.g : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * s)) hQ
  rw [Polynomial.eval₂_sub, Polynomial.eval₂_C, Polynomial.eval₂_mul, Polynomial.eval₂_X, hP2,
    zero_sub] at hev
  have h0 : ((p.scaleRoots ((X.B.g : ℕ) : ↥(Formalism.UG.intAd X.B.I.F))).comp (Polynomial.X - 1)).eval 0 =
      (-1) ^ p.natDegree + ((X.B.g : ℕ) : ↥(Formalism.UG.intAd X.B.I.F)) * q.eval (-1) := by
    rw [Polynomial.eval_comp, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_one, zero_sub, hsr,
      Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_mul, Polynomial.eval_C]
  refine ⟨phi X ((-1) ^ (p.natDegree + 1)) * Q.eval₂ (phi X) (1 + ((X.B.g : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * s),
    Subring.mul_mem _ (phi_mem X _) (eval₂_mem X Q ?_), (-1) ^ p.natDegree * q.eval (-1), ?_⟩
  · refine Subring.add_mem _ (Subring.one_mem _) (Subring.mul_mem _ ?_ hs)
    rw [← hgphi]; exact phi_mem X _
  · have h2 : ((-1 : ↥(Formalism.UG.intAd X.B.I.F)) ^ p.natDegree) * (-1) ^ p.natDegree = 1 := by
      rw [← mul_pow, neg_one_mul, neg_neg, one_pow]
    calc (1 + ((X.B.g : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * s) * (phi X ((-1) ^ (p.natDegree + 1)) *
          Q.eval₂ (phi X) (1 + ((X.B.g : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * s))
        = phi X ((-1) ^ (p.natDegree + 1)) * ((1 + ((X.B.g : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * s) *
          Q.eval₂ (phi X) (1 + ((X.B.g : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * s)) := by ring
      _ = phi X ((-1) ^ (p.natDegree + 1)) * -(phi X (((p.scaleRoots ((X.B.g : ℕ) : ↥(Formalism.UG.intAd X.B.I.F))).comp
          (Polynomial.X - 1)).eval 0)) := by rw [hev]
      _ = phi X (-((-1) ^ (p.natDegree + 1)) * ((p.scaleRoots ((X.B.g : ℕ) : ↥(Formalism.UG.intAd X.B.I.F))).comp
          (Polynomial.X - 1)).eval 0) := by rw [map_mul, map_neg]; ring
      _ = phi X (1 + ((X.B.g : ℕ) : ↥(Formalism.UG.intAd X.B.I.F)) * ((-1) ^ p.natDegree * q.eval (-1))) := by
          congr 1
          rw [h0, pow_succ]
          linear_combination h2

theorem idempotent_places_exists : SIdem X := by
  have hes : (⟨eS X, eS_int X⟩ : ↥(Formalism.UG.intAd X.B.I.F)) * ⟨eS X, eS_int X⟩ = ⟨eS X, eS_int X⟩ :=
    Subtype.ext (eS_idem X)
  have hone : 1 - (⟨eS X, eS_int X⟩ : ↥(Formalism.UG.intAd X.B.I.F)) = ((X.B.g : ℕ) : ↥(Formalism.UG.intAd X.B.I.F)) * ⟨tS X, tS_int X⟩ :=
    Subtype.ext (by push_cast; exact one_sub_eS X)
  refine ⟨phi X ⟨eS X, eS_int X⟩, phi_mem X _, by rw [← map_mul, hes], ?_,
    ⟨phi X ⟨tS X, tS_int X⟩, phi_mem X _, by
      rw [← map_one (phi X), ← map_sub, hone, map_mul, map_natCast]⟩, ?_⟩
  · rw [phi_apply]
    simp [Formalism.UG.sigR, Algebra.TensorProduct.map_tmul]
  · intro s hs
    obtain ⟨w, hw, d, hwd⟩ := near_inv X hs
    obtain ⟨z, hz, hzd⟩ := unit_on_S X d
    refine ⟨w * phi X ⟨z, hz⟩, Subring.mul_mem _ hw (phi_mem X _), ?_⟩
    have hR : (⟨eS X, eS_int X⟩ : ↥(Formalism.UG.intAd X.B.I.F)) * ((1 + ((X.B.g : ℕ) : ↥(Formalism.UG.intAd X.B.I.F)) * d) * ⟨z, hz⟩) =
        ⟨eS X, eS_int X⟩ := Subtype.ext (by push_cast; exact hzd)
    calc phi X ⟨eS X, eS_int X⟩ * ((1 + ((X.B.g : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * s) * (w * phi X ⟨z, hz⟩))
        = phi X ⟨eS X, eS_int X⟩ * (((1 + ((X.B.g : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * s) * w) * phi X ⟨z, hz⟩) := by ring
      _ = phi X ((⟨eS X, eS_int X⟩ : ↥(Formalism.UG.intAd X.B.I.F)) * ((1 + ((X.B.g : ℕ) : ↥(Formalism.UG.intAd X.B.I.F)) * d) * ⟨z, hz⟩)) := by
          rw [hwd, map_mul, map_mul]
      _ = phi X ⟨eS X, eS_int X⟩ := by rw [hR]

end SIdemPf

end Formalism.L2.SG.Pf.NormSteps.LeviOntoSPf
end
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NormStepsLeviOntoSEnd

section

@[expose] public section

noncomputable section

open scoped Classical TensorProduct
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.PoincareInHH.PoincareSetting

namespace Formalism.L2.SG.Pf.NormSteps

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} (TR : TypedRed X) {u : D.what₂.Word}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)} (cs : ColSys X u what₂)

theorem leviOntoS_of_frame (hF : LeviOntoSPf.FrameOfS X u) : LeviOntoS TR cs :=
  LeviOntoSPf.leviOntoS_of_steps TR u cs (LeviOntoSPf.SIdemPf.idempotent_places_exists X) hF
    (LeviOntoSPf.LeviEltPf.levi_element_exists TR u) (LeviOntoSPf.MatLiftPf.integral_matrix_lift_exists TR)

theorem levi_onto_reduction : LeviOntoS TR cs :=
  leviOntoS_of_frame TR cs (LeviOntoSPf.exact_dual_frame_exists X u)

end Formalism.L2.SG.Pf.NormSteps
end
end
end
