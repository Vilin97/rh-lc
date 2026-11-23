module

public import Development.AbelianVarietyTheory.Definitions.Divisors.RangeShape
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactPseudoUnitaryOffDiagNormSublevelStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.Foundations.ContinuousOfMemCcSmooth
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Matrix.Mul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolyEntriesConjLeftRightMul
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OffDiagBlockNormContInvStatement
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBiFiniteSubspace

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CutoffMulPolyMemCcMat

section

@[expose] public section

open MeasureTheory Matrix GlobalTheory.Orb
open Formalism.REAL (UJ KG toM toMK muK expG inG Jm Kset)
open scoped ContDiff

namespace GlobalTheory.CutoffPoly

theorem contDiff_entry {n : ℕ} (i j : Fin n) : ContDiff ℝ ∞ (fun M : Fin n → Fin n → ℂ => M i j) :=
  (contDiff_apply ℝ (fun _ => ℂ) j).comp (contDiff_apply ℝ (fun _ => (Fin n → ℂ)) i)

theorem contDiff_eval {X σ : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (c : σ → X → ℂ)
    (hc : ∀ s, ContDiff ℝ ∞ (c s)) (P : MvPolynomial σ ℂ) :
    ContDiff ℝ ∞ (fun x => MvPolynomial.eval (fun s => c s x) P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simpa using contDiff_const
  | add p q hp hq => simpa using hp.add hq
  | mul_X p s hp => simpa using hp.mul (hc s)

theorem cutoff_mul_poly_mem_ccMat : ∀ (n : ℕ) (ε : Fin n → Bool) (F : ℝ → ℝ) (R : ℝ), ContDiff ℝ ∞ F → (∀ x, R ≤ x → F x = 0) → ∀ P : MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin n)) ℂ, (fun g : UJ ε => ((F (∑ z : {z : Fin n × Fin n // ε z.1 = true ∧ ε z.2 = false}, ‖(toM g) z.1.1 z.1.2‖ ^ 2) : ℝ) : ℂ) * MvPolynomial.eval (Sum.elim (fun z : Fin n × Fin n => (toM g) z.1 z.2) (fun z : Fin n × Fin n => star ((toM g) z.1 z.2))) P) ∈ CcMat (ujMat ε) := by
  intro n ε F R hF hR P
  refine mem_ccSmooth.2 ⟨?_, fun M : Fin n → Fin n → ℂ =>
    ((F (∑ z : {z : Fin n × Fin n // ε z.1 = true ∧ ε z.2 = false}, ‖M z.1.1 z.1.2‖ ^ 2) : ℝ) : ℂ) *
      MvPolynomial.eval (fun s => Sum.elim (fun (z : Fin n × Fin n) (M : Fin n → Fin n → ℂ) => M z.1 z.2)
        (fun (z : Fin n × Fin n) (M : Fin n → Fin n → ℂ) => star (M z.1 z.2)) s M) P, ?_, ?_⟩
  · refine HasCompactSupport.intro (GlobalTheory.T.isCompact_pseudoUnitary_offDiag_norm_sublevel n ε R) fun g hg => ?_
    have h : R ≤ ∑ z : {z : Fin n × Fin n // ε z.1 = true ∧ ε z.2 = false}, ‖(toM g) z.1.1 z.1.2‖ ^ 2 :=
      (not_le.1 hg).le
    rw [hR _ h]; simp
  · refine ContDiff.mul (Complex.ofRealCLM.contDiff.comp (hF.comp ?_)) (contDiff_eval _ ?_ P)
    · exact ContDiff.sum fun z _ => (contDiff_norm_sq ℂ).comp (contDiff_entry _ _)
    · rintro (z | z)
      · exact contDiff_entry _ _
      · exact Complex.conjCLE.contDiff.comp (contDiff_entry z.1 z.2)
  · intro g
    congr 3
    funext s
    rcases s with z | z <;> rfl

end GlobalTheory.CutoffPoly
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolyEntriesConjLeftRightMulStatement

section

@[expose] public section

open MvPolynomial

theorem _root_.GlobalTheory.T.exists_poly_entries_conj_left_right_mul : ∀ (n : ℕ) (a b : Matrix (Fin n) (Fin n) ℂ) (P : MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin n)) ℂ), ∃ Q : MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin n)) ℂ, Q.totalDegree ≤ P.totalDegree ∧ ∀ g : Matrix (Fin n) (Fin n) ℂ, MvPolynomial.eval (Sum.elim (fun z : Fin n × Fin n => (a * g * b) z.1 z.2) (fun z : Fin n × Fin n => star ((a * g * b) z.1 z.2))) P = MvPolynomial.eval (Sum.elim (fun z : Fin n × Fin n => (g) z.1 z.2) (fun z : Fin n × Fin n => star ((g) z.1 z.2))) Q := by
  first | exact @GlobalTheory.PolyEntryMul.main | exact GlobalTheory.PolyEntryMul.main | (intros; apply GlobalTheory.PolyEntryMul.main <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsLastSide

section

@[expose] public section

open MeasureTheory Matrix GlobalTheory.Orb
open Formalism.REAL (UJ KG toM toMK muK expG inG Jm Kset)
open scoped ContDiff

namespace GlobalTheory.PolyShapeFinite

theorem main : ∀ (n : ℕ) (ε : Fin n → Bool) (F : ℝ → ℝ) (P : MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin n)) ℂ), IsBiFinite (KG ε) (fun g : UJ ε => ((F (∑ z : {z : Fin n × Fin n // ε z.1 = true ∧ ε z.2 = false}, ‖(toM g) z.1.1 z.1.2‖ ^ 2) : ℝ) : ℂ) * MvPolynomial.eval (Sum.elim (fun z : Fin n × Fin n => (toM g) z.1 z.2) (fun z : Fin n × Fin n => star ((toM g) z.1 z.2))) P) := by
  intro n ε F P
  let r : UJ ε → ℝ := fun g => ∑ z : {z : Fin n × Fin n // ε z.1 = true ∧ ε z.2 = false}, ‖(toM g) z.1.1 z.1.2‖ ^ 2
  let ev : UJ ε → ((Fin n × Fin n) ⊕ (Fin n × Fin n)) → ℂ := fun g =>
    Sum.elim (fun z : Fin n × Fin n => (toM g) z.1 z.2) (fun z : Fin n × Fin n => star ((toM g) z.1 z.2))
  let L : MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin n)) ℂ →ₗ[ℂ] (UJ ε → ℂ) :=
    { toFun := fun Q g => ((F (r g) : ℝ) : ℂ) * MvPolynomial.eval (ev g) Q
      map_add' := fun Q Q' => by funext g; simp [mul_add]
      map_smul' := fun c Q => by funext g; simp [MvPolynomial.smul_eq_C_mul, mul_left_comm] }
  unfold IsBiFinite
  have hle : Submodule.span ℂ {φ : UJ ε → ℂ | ∃ k ∈ KG ε, ∃ k' ∈ KG ε, φ = fun g =>
      ((F (r (k * g * k')) : ℝ) : ℂ) * MvPolynomial.eval (ev (k * g * k')) P} ≤
      (MvPolynomial.restrictTotalDegree _ ℂ P.totalDegree).map L := by
    rw [Submodule.span_le]
    rintro φ ⟨k, hk, k', hk', rfl⟩
    obtain ⟨Q, hQ, hQe⟩ := GlobalTheory.T.exists_poly_entries_conj_left_right_mul n (toM k) (toM k') P
    refine ⟨Q, (MvPolynomial.mem_restrictTotalDegree _ _ _).2 hQ, ?_⟩
    funext g
    have h1 : r (k * g * k') = r g := (GlobalTheory.T.offDiagBlockNorm_mul_invariant n ε).2 ⟨k, hk⟩ ⟨k', hk'⟩ g
    have h2 : toM (k * g * k') = toM k * toM g * toM k' := rfl
    have h3 : MvPolynomial.eval (ev (k * g * k')) P = MvPolynomial.eval (ev g) Q := by
      simp only [ev, h2]; exact hQe (toM g)
    show ((F (r g) : ℝ) : ℂ) * MvPolynomial.eval (ev g) Q = _
    rw [h1, h3]
  exact Submodule.finiteDimensional_of_le hle

end GlobalTheory.PolyShapeFinite
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PseudoCoeffShapeSmoothCompactSupport

section

@[expose] public section

open GlobalTheory.Orb GlobalTheory.PsCo.Pc1
open Formalism.REAL (UJ KG toM)

namespace GlobalTheory.ShapeSmoothFinite

theorem continuous_matCoord_ujMat {n : ℕ} (ε : Fin n → Bool) : Continuous (matCoord (ujMat ε)) :=
  (Units.continuous_val (M := Matrix (Fin n) (Fin n) ℂ)).comp continuous_subtype_val

theorem mem_ccMat_and_isBiFinite {n : ℕ} (ε : Fin n → Bool) (d : ℕ) (φ : Mat n → ℂ) (hφ : φ ∈ ShapeM ε d) :
    (fun g : UJ ε => φ (toM g)) ∈ CcMat (ujMat ε) ∧ IsBiFinite (KG ε) (fun g : UJ ε => φ (toM g)) := by
  obtain ⟨h0, hadd, hsmul⟩ := GlobalTheory.isBiFinite_subspace (UJ ε) (KG ε)
  induction hφ using Submodule.span_induction with
  | mem φ h =>
    obtain ⟨H, P, ⟨hH, R, hR⟩, -, rfl⟩ := h
    exact ⟨GlobalTheory.CutoffPoly.cutoff_mul_poly_mem_ccMat n ε H R hH hR P, GlobalTheory.PolyShapeFinite.main n ε H P⟩
  | zero => exact ⟨Submodule.zero_mem _, h0⟩
  | add φ ψ _ _ h h' => exact ⟨Submodule.add_mem _ h.1 h'.1, hadd _ _ h.2 h'.2⟩
  | smul c φ _ h => exact ⟨Submodule.smul_mem _ c h.1, hsmul c _ h.2⟩

theorem stShape : GlobalTheory.PsCo.Pc1.StShape := by
  intro n ε d φ hφ
  obtain ⟨h1, h2⟩ := mem_ccMat_and_isBiFinite ε d φ hφ
  exact ⟨h1, h2, continuous_of_mem_ccSmooth (continuous_matCoord_ujMat ε) h1, (mem_ccSmooth.1 h1).1⟩

end GlobalTheory.ShapeSmoothFinite
end
end
