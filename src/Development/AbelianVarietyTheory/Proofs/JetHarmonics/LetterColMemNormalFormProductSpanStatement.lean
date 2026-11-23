module

public import Development.AbelianVarietyTheory.Definitions.Jets.SameFns
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HatLettersPassDiGIBoundedFactorsStatement
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FrameStartConstantsNormalFormEmptyWord
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
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.MinusId
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.WordMDecompositionSelfAdjoint
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdmissibleRecOfAdmissibleWord
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LetterLiftOfParts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RuleGD
import Mathlib.Algebra.Order.Star.Int

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.FrameStartConstantsNormalFormEmptyWordStatement

section

@[expose] public section

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

theorem _root_.GlobalTheory.T.frameStart_constants_normalForm_empty_word : ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] (d : Q.NFData P A), HatHyp d → ∀ (L : LevelData A P.r) (st : Start A) (s : ℂ), Comparison₂ d L st s → (∀ x ∈ TL.kAlg st, x ∈ Set.range d.κ) ∧ ∀ Y ∈ st.inv, ∃ E ∈ nfSpan d ∅ 0 0 0, L.l0 Y + L.ζb * L.ζi * L.GGi * st.ee Y = d.L.l0 Y + d.L.ζb * d.L.ζi * d.L.GGi * E := by
  first | exact @GlobalTheory.HatNF.start_normalForm | exact GlobalTheory.HatNF.start_normalForm | (intros; apply GlobalTheory.HatNF.start_normalForm <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.WordLDecompositionNfSpan

section

@[expose] public section

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

namespace GlobalTheory.HatNF.WordL

section

variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A]

theorem mem_of_bmon (d : Q.NFData P A) {b : A} (hb : b ∈ bmon d) : b ∈ nfSpan d ∅ 0 0 0 :=
  Submodule.subset_span ⟨b, hb, [], rfl, by simp, by simp⟩

theorem span_eq (d : Q.NFData P A) : nfSpan d ∅ 0 0 0 = Submodule.span ℂ (bmon d : Set A) := by
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro x ⟨b, hb, H, hH, -, rfl⟩
    rw [List.length_eq_zero_iff.mp hH]
    simpa using Submodule.subset_span (R := ℂ) (s := (bmon d : Set A)) hb
  · exact Submodule.span_le.mpr fun b hb => mem_of_bmon d hb

theorem span_mul (d : Q.NFData P A) {x y : A} (hx : x ∈ nfSpan d ∅ 0 0 0) (hy : y ∈ nfSpan d ∅ 0 0 0) :
    x * y ∈ nfSpan d ∅ 0 0 0 := by
  rw [span_eq] at *
  have h := Submodule.mul_mem_mul hx hy
  rw [Submodule.span_mul_span] at h
  refine Submodule.span_mono ?_ h
  rintro _ ⟨a, ha, b, hb, rfl⟩
  exact (bmon d).mul_mem ha hb

theorem kappa_mem (d : Q.NFData P A) (f : M.Ty P → ℂ) : d.κ f ∈ nfSpan d ∅ 0 0 0 :=
  mem_of_bmon d (Submonoid.subset_closure (Or.inl (Or.inl (Or.inr ⟨f, rfl⟩))))

theorem zbi_mem (d : Q.NFData P A) : d.L.ζbi ∈ nfSpan d ∅ 0 0 0 :=
  mem_of_bmon d (Submonoid.subset_closure (Or.inl (Or.inl (Or.inl (by simp)))))

variable {S : Type} [Fintype S] [DecidableEq S]

def BMat (d : Q.NFData P A) (E : SlopeTestRemainingChoices S A) : Prop := ∀ e e', E e e' ∈ nfSpan d ∅ 0 0 0

theorem BMat.mul {d : Q.NFData P A} {E F : SlopeTestRemainingChoices S A} (hE : BMat d E) (hF : BMat d F) : BMat d (E * F) :=
  fun i j => by
    rw [Matrix.mul_apply]
    exact Submodule.sum_mem _ fun k _ => span_mul d (hE i k) (hF k j)

theorem BMat.add {d : Q.NFData P A} {E F : SlopeTestRemainingChoices S A} (hE : BMat d E) (hF : BMat d F) : BMat d (E + F) :=
  fun i j => add_mem (hE i j) (hF i j)

theorem BMat.sub {d : Q.NFData P A} {E F : SlopeTestRemainingChoices S A} (hE : BMat d E) (hF : BMat d F) : BMat d (E - F) :=
  fun i j => sub_mem (hE i j) (hF i j)

theorem BMat.smul {d : Q.NFData P A} {E : SlopeTestRemainingChoices S A} (c : ℂ) (hE : BMat d E) : BMat d (c • E) :=
  fun i j => Submodule.smul_mem _ c (hE i j)

theorem bMat_io {d : Q.NFData P A} {a : A} (ha : a ∈ nfSpan d ∅ 0 0 0) : BMat d (io a : SlopeTestRemainingChoices S A) := fun i j => by
  simp only [io, Matrix.scalar_apply, Matrix.diagonal_apply]
  split_ifs
  · exact ha
  · exact zero_mem _

theorem io_add (a b : A) : (io (a + b) : SlopeTestRemainingChoices S A) = io a + io b := map_add (Matrix.scalar (Ix S)) a b

theorem io_mul (a b : A) : (io (a * b) : SlopeTestRemainingChoices S A) = io a * io b := map_mul (Matrix.scalar (Ix S)) a b

theorem inv_subset {r : ℕ} (L : LevelData A r) (st : Start A) (w : List (Letter ℂ S)) :
    ∀ Y ∈ (ofWord L st w).inv, Y ∈ st.inv := by
  induction w with
  | nil => exact fun Y hY => hY
  | cons l w ih =>
    intro Y hY
    by_cases hp : l.plus
    · have e : ofWord L st (l :: w) = (ofWord L st w).plus L l.intersection_update_fsHerm_neg_one l.pt := by simp [ofWord, hp]
      rw [e] at hY
      exact ih Y hY.1
    · have e : ofWord L st (l :: w) = (ofWord L st w).minus L l.intersection_update_fsHerm_neg_one l.pt := by simp [ofWord, hp]
      rw [e] at hY
      exact ih Y hY.1

theorem comm_id {R : Type*} [Ring R] (l K E α β γ : R) (h1 : β * l = l * β) (h2 : β * K = K * β)
    (h3 : α * K = K * α) :
    α * ((l + K * E) * β - β * (l + K * E)) * γ = K * (α * (E * β - β * E) * γ) := by
  have : (l + K * E) * β - β * (l + K * E) = K * (E * β - β * E) := by
    rw [mul_add, h1, ← mul_assoc β K, h2]; noncomm_ring
  rw [this, ← mul_assoc α K, h3]; simp only [mul_assoc]

end

theorem word_l_shape : ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] (d : Q.NFData P A), HatHyp d → ∀ (L : LevelData A P.r) (st : Start A) (s : ℂ), Comparison₂ d L st s → ∀ (S : Type) [Fintype S] [DecidableEq S], ∀ w : List (Letter ℂ S), admitted st w → ∀ Y ∈ (ofWord L st w).inv, Y + 1 ∈ (ofWord L st w).inv → ∃ E : SlopeTestRemainingChoices S A, (∀ e e', E e e' ∈ nfSpan d ∅ 0 0 0) ∧ (ofWord L st w).l L Y = io (d.L.l0 Y) + kapL d.L * E := by
  intro P A _ _ _ _ d hd L st s hT S _ _ w hA Y hY hY1
  obtain ⟨hk, h0⟩ := GlobalTheory.T.frameStart_constants_normalForm_empty_word P A d hd L st s hT
  obtain ⟨E0, hE0, e0⟩ := h0 Y (inv_subset L st w Y hY)
  obtain ⟨hH, hS, -⟩ := hT
  obtain ⟨-, -, -, -, -, -, -, s1, s2, s3, -, s4, s5⟩ := hS
  have hkap : (kapL L : SlopeTestRemainingChoices S A) = kapL d.L := by simp only [kapL, s1, s2, s4]
  have htz : (tz L : SlopeTestRemainingChoices S A) = tz d.L := by simp only [tz, s3, s5]
  have hl0 : (st.frame : FrameData S A).l L Y = io (d.L.l0 Y) + kapL d.L * io E0 := by
    show io (L.l0 Y) + io (L.ζb * L.ζi * L.GGi) * io (st.ee Y) =
      io (d.L.l0 Y) + io (d.L.ζb * d.L.ζi * d.L.GGi) * io E0
    rw [← io_mul, ← io_add, e0, io_add, io_mul]
  have hsh := (Formalism.FourierDecayAlt.P.l_shape A S P.r L st w hH.starLev hH.start hA).2.2 Y hY hY1
  rw [hl0, hkap, htz] at hsh
  have hc := hd.2.2.1.2.1
  have cζb : ∀ f, Commute (d.κ f) d.L.ζb := fun f => hc f _ (by simp [LevelData.fns])
  have cζi : ∀ f, Commute (d.κ f) d.L.ζi := fun f => hc f _ (by simp [LevelData.fns])
  have cG : ∀ f, Commute (d.κ f) d.L.GGi := fun f => hc f _ (by simp [LevelData.fns])
  have cn : ∀ f, Commute (d.κ f) d.L.nab := fun f => hc f _ (by simp)
  have cio : ∀ (a : A), (∀ f, Commute (d.κ f) a) → ∀ α : SlopeTestRemainingChoices S A, TL.kMat st α → α * io a = io a * α := by
    intro a ha α hα
    refine (Formalism.FourierDecayAlt.P.TLA.L1.io_comm fun i j => ?_).symm.eq
    obtain ⟨f, hf⟩ := hk _ (hα i j)
    rw [← hf]; exact (ha f).symm
  have cK : ∀ α : SlopeTestRemainingChoices S A, TL.kMat st α → α * kapL d.L = kapL d.L * α :=
    cio _ fun f => ((cζb f).mul_right (cζi f)).mul_right (cG f)
  have cl : ∀ α : SlopeTestRemainingChoices S A, TL.kMat st α → α * io (d.L.l0 Y) = io (d.L.l0 Y) * α :=
    cio _ fun f => (cn f).neg_right.sub_right
      ((show Commute (d.κ f) (algebraMap ℂ A (Y + 1 / 2)) from (Algebra.commutes _ _).symm).mul_right
        ((cζb f).mul_right (cG f)))
  have hB : ∀ α : SlopeTestRemainingChoices S A, TL.kMat st α → BMat d α := by
    intro α hα i j
    obtain ⟨f, hf⟩ := hk _ (hα i j)
    rw [← hf]; exact kappa_mem d f
  have hE : BMat d (io E0 : SlopeTestRemainingChoices S A) := bMat_io hE0
  have key : ∀ M ∈ TL.dSpan st (io (d.L.l0 Y) + kapL d.L * io E0 : SlopeTestRemainingChoices S A) (kapL d.L) (tz d.L),
      ∃ E : SlopeTestRemainingChoices S A, BMat d E ∧ M = kapL d.L * E := by
    intro M hM
    induction hM using Submodule.span_induction with
    | mem x hx =>
      rcases hx with ⟨α, β, γ, h1, h2, h3, rfl⟩ | ⟨γ, h, rfl | rfl⟩
      · exact ⟨_, ((hB α h1).mul ((hE.mul (hB β h2)).sub ((hB β h2).mul hE))).mul (hB γ h3),
          comm_id _ _ _ _ _ _ (cl β h2) (cK β h2) (cK α h1)⟩
      · exact ⟨γ, hB γ h, rfl⟩
      · exact ⟨tz d.L * γ, (bMat_io (Submodule.smul_mem _ _ (zbi_mem d))).mul (hB γ h), mul_assoc _ _ _⟩
    | zero => exact ⟨0, fun _ _ => zero_mem _, (mul_zero _).symm⟩
    | add x y _ _ hx hy =>
      obtain ⟨E, hE, rfl⟩ := hx
      obtain ⟨F, hF, rfl⟩ := hy
      exact ⟨E + F, hE.add hF, (mul_add _ _ _).symm⟩
    | smul c x _ hx =>
      obtain ⟨E, hE, rfl⟩ := hx
      exact ⟨c • E, hE.smul c, (mul_smul_comm _ _ _).symm⟩
  obtain ⟨E, hE', e⟩ := key _ hsh
  refine ⟨io E0 + E, hE.add hE', ?_⟩
  rw [sub_eq_iff_eq_add.mp e, mul_add]
  abel

end GlobalTheory.HatNF.WordL
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.WordLDecompositionNfSpanStatement

section

@[expose] public section

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

theorem _root_.GlobalTheory.T.word_l_decomposition_nf_span : ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] (d : Q.NFData P A), HatHyp d → ∀ (L : LevelData A P.r) (st : Start A) (s : ℂ), Comparison₂ d L st s → ∀ (S : Type) [Fintype S] [DecidableEq S], ∀ w : List (Letter ℂ S), admitted st w → ∀ Y ∈ (ofWord L st w).inv, Y + 1 ∈ (ofWord L st w).inv → ∃ E : SlopeTestRemainingChoices S A, (∀ e e', E e e' ∈ nfSpan d ∅ 0 0 0) ∧ (ofWord L st w).l L Y = io (d.L.l0 Y) + kapL d.L * E := by
  first | exact @GlobalTheory.HatNF.WordL.word_l_shape | exact GlobalTheory.HatNF.WordL.word_l_shape | (intros; apply GlobalTheory.HatNF.WordL.word_l_shape <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.WordMDecompositionSelfAdjointStatement

section

@[expose] public section

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

theorem _root_.GlobalTheory.T.word_m_decomposition_self_adjoint : ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] (d : Q.NFData P A), HatHyp d → ∀ (L : LevelData A P.r) (st : Start A) (s : ℂ), Comparison₂ d L st s → ∀ (S : Type) [Fintype S] [DecidableEq S], ∀ w : List (Letter ℂ S), admitted st w → ∀ Y ∈ (ofWord L st w).inv, star Y = Y → Y - 1 ∈ (ofWord L st w).inv → ∃ E : SlopeTestRemainingChoices S A, (∀ e e', E e e' ∈ nfSpan d ∅ 0 0 0) ∧ (ofWord L st w).m L Y = io (d.L.m0 Y) + io (d.L.ζ * d.L.ζbi * d.L.GGi) * E := by
  first | exact @GlobalTheory.HatNF.MShapeNF.mshape | exact GlobalTheory.HatNF.MShapeNF.mshape | (intros; apply GlobalTheory.HatNF.MShapeNF.mshape <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.LetterColMemNormalFormProductSpan

section

@[expose] public section

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

namespace GlobalTheory.HatNF.LetterEntries

open Formalism.FourierDecayAlt.P.RuleGD Formalism.FourierDecayAlt.P.TLA

variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]


omit [StarModule ℂ A] in
theorem gen_mem (d : Q.NFData P A) {T : Set A} {b X : A} (hb : b ∈ bmon d) (hX : X ∈ T) :
    b * d.L.Di * X ∈ nfSpan d T 1 0 1 :=
  Submodule.subset_span ⟨b, hb, [X], rfl, by simpa using hX, by simp⟩


omit [StarModule ℂ A] in
theorem bounded_induction (d : Q.NFData P A) (N : Submodule ℂ A) (hN : ∀ b ∈ bmon d, b ∈ N) {E : A}
    (hE : E ∈ nfSpan d ∅ 0 0 0) : E ∈ N := by
  refine (Submodule.span_le.mpr ?_ : nfSpan d ∅ 0 0 0 ≤ N) hE
  rintro x ⟨b, hb, H, hH, -, rfl⟩
  rw [List.length_eq_zero_iff] at hH
  subst hH
  simpa using hN b hb

omit [StarModule ℂ A] in
theorem bounded_mul_mem (d : Q.NFData P A) {T : Set A} {E b X : A} (hE : E ∈ nfSpan d ∅ 0 0 0) (hb : b ∈ bmon d)
    (hX : X ∈ T) : E * (b * d.L.Di * X) ∈ nfSpan d T 1 0 1 := by
  refine bounded_induction d ((nfSpan d T 1 0 1).comap (LinearMap.mulRight ℂ (b * d.L.Di * X))) ?_ hE
  intro c hc
  have := gen_mem d (mul_mem hc hb) hX
  simpa [mul_assoc] using this

omit [StarModule ℂ A] in
theorem bounded_comm (d : Q.NFData P A) {E f : A} (hE : E ∈ nfSpan d ∅ 0 0 0) (hf : ∀ b ∈ bmon d, Commute b f) :
    f * E = E * f := by
  have := bounded_induction d (LinearMap.ker (LinearMap.mulLeft ℂ f - LinearMap.mulRight ℂ f))
    (fun b hb => by simp [(hf b hb).eq]) hE
  simpa [sub_eq_zero] using this

variable {S : Type} [Fintype S] [DecidableEq S]

omit [StarModule ℂ A] [StarRing A] in
theorem io_mem {N : Submodule ℂ A} {a : A} (ha : a ∈ N) (e e' : Ix S) : (io a : SlopeTestRemainingChoices S A) e e' ∈ N := by
  simp only [io, Matrix.scalar_apply, Matrix.diagonal_apply]
  split_ifs
  · exact ha
  · exact N.zero_mem

omit [StarModule ℂ A] [StarRing A] in
theorem col_mem {N : Submodule ℂ A} {s X k V W : A} {E : SlopeTestRemainingChoices S A} (h1 : s * (X * V + W) ∈ N)
    (h2 : ∀ e e', s * k * E e e' * V ∈ N) (e e' : Ix S) :
    (io s * ((io X + io k * E) * io V + io W) : SlopeTestRemainingChoices S A) e e' ∈ N := by
  have key : io s * ((io X + io k * E) * io V + io W) =
      (io (s * (X * V + W)) : SlopeTestRemainingChoices S A) + io (s * k) * E * io V := by
    simp only [io, map_mul, map_add (f := _)]; noncomm_ring
  rw [key, Matrix.add_apply]
  refine N.add_mem (io_mem h1 e e') ?_
  have : (io (s * k) * E * io V : SlopeTestRemainingChoices S A) e e' = s * k * E e e' * V := by
    simp [io, Matrix.scalar_apply, Matrix.diagonal_mul, Matrix.mul_diagonal]
  rw [this]
  exact h2 e e'

theorem letterCol_mem : ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
    (d : Q.NFData P A), HatHyp d → ∀ (L : LevelData A P.r) (st : Start A) (s : ℂ), Comparison₂ d L st s →
    ∀ (S : Type) [Fintype S] [DecidableEq S], ∀ (l : Letter ℂ S) (w : List (Letter ℂ S)), admitted st (l :: w) →
    ∀ i e e', TL.letterCol L st l w i e e' ∈ nfSpan d (hats d.L) 1 0 1 := by
  intro P A _ _ _ _ d hd0 L st s hT S _ _ l w hA i e e'
  obtain ⟨hnd, hre, hpt, hpw⟩ := hA
  have hnd' : l.intersection_update_fsHerm_neg_one ∉ w.map Letter.intersection_update_fsHerm_neg_one ∧ (w.map Letter.intersection_update_fsHerm_neg_one).Nodup :=
    List.nodup_cons.mp (by simpa only [List.map_cons] using hnd)
  have hpw' := List.pairwise_cons.mp hpw
  have hAw : admitted st w :=
    ⟨hnd'.2, fun l' h => hre l' (by simp [h]), fun l' h => hpt l' (by simp [h]), hpw'.2⟩
  obtain ⟨p0, p1, pm1, -, -⟩ := hpt l (by simp)
  have hd := hpw'.1
  have m0 : l.pt ∈ (ofWord L st w).inv := Formalism.FourierDecayAlt.P.Fr2.mem_inv L st w _ p0 (fun l' hl' =>
    ⟨fun e => hd l' hl' 0 (by norm_num) (by push_cast; linear_combination e),
     fun e => hd l' hl' 1 (by norm_num) (by push_cast; linear_combination e),
     fun e => hd l' hl' (-1) (by norm_num) (by push_cast; linear_combination e)⟩)
  have m1 : l.pt + 1 ∈ (ofWord L st w).inv := Formalism.FourierDecayAlt.P.Fr2.mem_inv L st w _ p1 (fun l' hl' =>
    ⟨fun e => hd l' hl' (-1) (by norm_num) (by push_cast; linear_combination e),
     fun e => hd l' hl' 0 (by norm_num) (by push_cast; linear_combination e),
     fun e => hd l' hl' (-2) (by norm_num) (by push_cast; linear_combination e)⟩)
  have mm1 : l.pt - 1 ∈ (ofWord L st w).inv := Formalism.FourierDecayAlt.P.Fr2.mem_inv L st w _ pm1 (fun l' hl' =>
    ⟨fun e => hd l' hl' 1 (by norm_num) (by push_cast; linear_combination e),
     fun e => hd l' hl' 2 (by norm_num) (by push_cast; linear_combination e),
     fun e => hd l' hl' 0 (by norm_num) (by push_cast; linear_combination e)⟩)
  have hr : star l.pt = l.pt := hre l (by simp)
  obtain ⟨-, hb, -⟩ := GlobalTheory.T.hatLetters_pass_Di_gI_boundedFactors P A d hd0
  obtain ⟨ep, epb, ec, eci, ecb, ecbi, eζ, eζi, eζb, eζbi, eG, eGi, -⟩ := hT.2.1
  have eT : L.Tprod l.pt = d.L.Tprod l.pt := by
    unfold LevelData.Tprod LevelData.Tl; rw [ep, ec, eci]
  have eTv : L.Tvprod l.pt = d.L.Tvprod l.pt := by
    unfold LevelData.Tvprod LevelData.Tvl; rw [epb, ecb, ecbi]
  have eA : L.Ar l.pt = d.L.Ar l.pt := by unfold LevelData.Ar; rw [eT]
  have eB : L.Br l.pt = d.L.Br l.pt := by unfold LevelData.Br; rw [eT]
  have eAv : L.Avr l.pt = d.L.Avr l.pt := by unfold LevelData.Avr; rw [eTv]
  have eBv : L.Bvr l.pt = d.L.Bvr l.pt := by unfold LevelData.Bvr; rw [eTv]
  have hβ : d.L.D * d.L.Dbi ∈ bmon d := Submonoid.subset_closure (by simp [bset])
  have i1 : 1 * d.L.Di * d.L.Dr = d.L.ζi := by
    rw [one_mul, LevelData.Di, mul_assoc, Dri_Dr, mul_one]
  have i2 : d.L.D * d.L.Dbi * d.L.Di * d.L.Drb = d.L.ζbi := by
    have : d.L.Di * d.L.D = 1 := by
      rw [LevelData.D, ← mul_assoc, ← one_mul d.L.Di, i1, d.L.ζi_ζ]
    rw [(hb _ hβ).2.1.eq, ← mul_assoc, this, one_mul, LevelData.Dbi, mul_assoc, Drbi_Drb, mul_one]
  have j1 : d.L.ζi * d.L.Ar l.pt = 1 * d.L.Di * d.L.Ahat l.pt := by
    rw [LevelData.Ahat, ← mul_assoc, i1]
  have j2 : d.L.ζbi * d.L.Avr l.pt = d.L.D * d.L.Dbi * d.L.Di * d.L.Ahatv l.pt := by
    rw [LevelData.Ahatv, ← mul_assoc, i2]
  have hA1 : d.L.Ahat l.pt ∈ hats d.L := by simp [hats]
  have hA2 : d.L.Ahatv l.pt ∈ hats d.L := by simp [hats]
  have hR1 : d.L.R0 l.pt ∈ hats d.L := by simp [hats]
  have hR2 : d.L.R0v l.pt ∈ hats d.L := by simp [hats]
  unfold TL.letterCol
  by_cases hp : l.plus
  · simp only [hp, if_true]
    fin_cases i
    · refine io_mem (a := TL.aP L l.pt) ?_ e e'
      rw [TL.aP, eζi, eA, j1]
      exact gen_mem d (one_mem _) hA1
    · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
      obtain ⟨E, hE, hl⟩ := GlobalTheory.T.word_l_decomposition_nf_span P A d hd0 L st s hT S w hAw l.pt m0 m1
      rw [hl, eζbi, eG, eA, eB, kapL]
      refine col_mem ?_ (fun f f' => ?_) e e'
      · have := gen_mem d hβ hR1
        rwa [LevelData.R0, ← mul_assoc, ← mul_assoc, i2] at this
      · rw [ColumnLift.s1p, bounded_comm d (hE f f') (fun b h => (hb b h).1 _ (by simp [LevelData.fns])), mul_assoc, j1]
        exact bounded_mul_mem d (hE f f') (one_mem _) hA1
  · simp only [hp, Bool.false_eq_true, if_false]
    fin_cases i
    · refine io_mem (a := TL.aM L l.pt) ?_ e e'
      rw [TL.aM, eζbi, eAv, j2]
      exact gen_mem d hβ hA2
    · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
      obtain ⟨E, hE, hl⟩ := GlobalTheory.T.word_m_decomposition_self_adjoint P A d hd0 L st s hT S w hAw l.pt m0 hr mm1
      rw [hl, eζi, eG, eAv, eBv]
      refine col_mem ?_ (fun f f' => ?_) e e'
      · have := gen_mem d (one_mem _) hR2
        rwa [LevelData.R0v, ← mul_assoc, ← mul_assoc, i1] at this
      · rw [ColumnLift.s1m, bounded_comm d (hE f f') (fun b h => (hb b h).1 _ (by simp [LevelData.fns])), mul_assoc, j2]
        exact bounded_mul_mem d (hE f f') hβ hA2

end GlobalTheory.HatNF.LetterEntries
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.LetterColMemNormalFormProductSpanStatement

section

@[expose] public section

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

theorem _root_.GlobalTheory.T.letterCol_mem_normalFormProductSpan : ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] (d : Q.NFData P A), HatHyp d → ∀ (L : LevelData A P.r) (st : Start A) (s : ℂ), Comparison₂ d L st s → ∀ (S : Type) [Fintype S] [DecidableEq S], ∀ (l : Letter ℂ S) (w : List (Letter ℂ S)), admitted st (l :: w) → ∀ i e e', TL.letterCol L st l w i e e' ∈ nfSpan d (hats d.L) 1 0 1 := by
  first | exact @GlobalTheory.HatNF.LetterEntries.letterCol_mem | exact GlobalTheory.HatNF.LetterEntries.letterCol_mem | (intros; apply GlobalTheory.HatNF.LetterEntries.letterCol_mem <;> assumption)
end
end
