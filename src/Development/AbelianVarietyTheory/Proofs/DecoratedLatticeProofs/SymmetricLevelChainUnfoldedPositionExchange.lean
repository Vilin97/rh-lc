module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.AllPositions
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.Prod
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnesRepresent
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MatrixBlockColumnVanishingStep
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymLevelChainTestFunctionAddRowStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Mathlib.RingTheory.Henselian
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralBlockIndicator

section

@[expose] public section

open MeasureTheory Classical

namespace GlobalTheory.BlockFubini

theorem integral_block_indicator (k : Type) [MeasurableSpace k] [Zero k] (ν : Measure k) [SigmaFinite ν] (I : Type) [Fintype I] (P Q R : I → Prop) [DecidablePred P] [DecidablePred Q] [DecidablePred R] (hR : ∀ i, R i ↔ P i ∧ ¬ Q i) (hQ : ∀ i, Q i → P i) (s : Set k) (hs : MeasurableSet s) (_hν : ν s ≠ ⊤) (G : (I → k) → ℂ) (hG : ∀ m : I → k, G m = (if ∀ i, Q i → m i ∈ s then (1 : ℂ) else 0) * G (fun i => if Q i then 0 else m i)) : ∫ e : {i // P i} → k, G (fun i => if h : P i then e ⟨i, h⟩ else 0) ∂(Measure.pi fun _ => ν) = (((ν s).toReal ^ Fintype.card {i // Q i} : ℝ) : ℂ) * ∫ e : {i // R i} → k, G (fun i => if h : R i then e ⟨i, h⟩ else 0) ∂(Measure.pi fun _ => ν) := by
  let σ : {i // Q i} ⊕ {i // R i} ≃ {i // P i} :=
    { toFun := Sum.elim (fun a => ⟨a.1, hQ _ a.2⟩) (fun a => ⟨a.1, ((hR _).1 a.2).1⟩)
      invFun := fun a => if h : Q a.1 then Sum.inl ⟨a.1, h⟩ else Sum.inr ⟨a.1, (hR _).2 ⟨a.2, h⟩⟩
      left_inv := by
        rintro (a | a)
        · simp [a.2]
        · simp [((hR _).1 a.2).2]
      right_inv := by
        intro a
        by_cases h : Q a.1 <;> simp [h] }
  have h1 := measurePreserving_piCongrLeft (α := fun _ : {i // P i} => k) (fun _ => ν) σ
  have h2 := measurePreserving_sumPiEquivProdPi_symm (X := fun _ : {i // Q i} ⊕ {i // R i} => k) (fun _ => ν)
  have h3 := h1.comp h2
  rw [← h3.integral_comp ((MeasurableEquiv.measurableEmbedding _).comp (MeasurableEquiv.measurableEmbedding _))]
  have key : ∀ z : ({i // Q i} → k) × ({i // R i} → k),
      G (fun i => if h : P i then ((MeasurableEquiv.piCongrLeft (fun _ : {i // P i} => k) σ) ∘ (MeasurableEquiv.sumPiEquivProdPi (fun _ : {i // Q i} ⊕ {i // R i} => k)).symm) z ⟨i, h⟩ else 0)
      = (Set.pi Set.univ (fun _ : {i // Q i} => s)).indicator (fun _ => (1:ℂ)) z.1 * G (fun i => if h : R i then z.2 ⟨i, h⟩ else 0) := by
    intro z
    set E := ((MeasurableEquiv.piCongrLeft (fun _ : {i // P i} => k) σ) ∘ (MeasurableEquiv.sumPiEquivProdPi (fun _ : {i // Q i} ⊕ {i // R i} => k)).symm) z with hE
    have e0 : ∀ a, E (σ a) = Sum.elim z.1 z.2 a := by
      intro a
      rw [hE]
      simp only [Function.comp_apply]
      rw [MeasurableEquiv.piCongrLeft_apply_apply]
      cases a <;> rfl
    have e1 : ∀ i (h : Q i), E ⟨i, hQ i h⟩ = z.1 ⟨i, h⟩ := fun i h => e0 (Sum.inl ⟨i, h⟩)
    have e2 : ∀ i (h : R i), E ⟨i, ((hR i).1 h).1⟩ = z.2 ⟨i, h⟩ := fun i h => e0 (Sum.inr ⟨i, h⟩)
    rw [hG]
    congr 1
    · rw [Set.indicator_apply]
      congr 1
      apply propext
      simp only [Set.mem_pi, Set.mem_univ, forall_true_left]
      constructor
      · intro h a
        have := h a.1 a.2
        rwa [dif_pos (hQ _ a.2), e1 _ a.2] at this
      · intro h i hi
        rw [dif_pos (hQ _ hi), e1 _ hi]
        exact h _
    · congr 1
      funext i
      by_cases hq : Q i
      · have : ¬ R i := fun h => ((hR i).1 h).2 hq
        simp [hq, this]
      · by_cases hp : P i
        · have : R i := (hR i).2 ⟨hp, hq⟩
          simp only [hq, if_false, dif_pos hp, dif_pos this]
          exact e2 i this
        · have : ¬ R i := fun h => hp ((hR i).1 h).1
          simp [hq, hp, this]
  simp_rw [key]
  rw [integral_prod_mul (fun x => (Set.pi Set.univ (fun _ : {i // Q i} => s)).indicator (fun _ => (1:ℂ)) x) (fun y : {i // R i} → k => G (fun i => if h : R i then y ⟨i, h⟩ else 0))]
  congr 1
  rw [integral_indicator_const _ (MeasurableSet.univ_pi fun _ => hs)]
  simp [Measure.real, Measure.pi_pi]

end GlobalTheory.BlockFubini
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralBlockIndicatorStatement

section

@[expose] public section

open MeasureTheory Classical

theorem _root_.GlobalTheory.T.integral_pi_block_indicator_eq_pow_mul : ∀ (k : Type) [MeasurableSpace k] [Zero k] (ν : Measure k) [SigmaFinite ν] (I : Type) [Fintype I] (P Q R : I → Prop) [DecidablePred P] [DecidablePred Q] [DecidablePred R], (∀ i, R i ↔ P i ∧ ¬ Q i) → (∀ i, Q i → P i) → ∀ (s : Set k), MeasurableSet s → ν s ≠ ⊤ → ∀ (G : (I → k) → ℂ), (∀ m : I → k, G m = (if ∀ i, Q i → m i ∈ s then (1 : ℂ) else 0) * G (fun i => if Q i then 0 else m i)) → ∫ e : {i // P i} → k, G (fun i => if h : P i then e ⟨i, h⟩ else 0) ∂(Measure.pi fun _ => ν) = (((ν s).toReal ^ Fintype.card {i // Q i} : ℝ) : ℂ) * ∫ e : {i // R i} → k, G (fun i => if h : R i then e ⟨i, h⟩ else 0) ∂(Measure.pi fun _ => ν) := by
  first | exact @GlobalTheory.BlockFubini.integral_block_indicator | exact GlobalTheory.BlockFubini.integral_block_indicator | (intros; apply GlobalTheory.BlockFubini.integral_block_indicator <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MatrixBlockColumnVanishingStepStatement

section

@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

theorem _root_.GlobalTheory.T.matrix_block_column_vanishing_step : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t], S.Pattern t → ∀ (j c : ℕ) (H : j + c = s) (q : Fin c), q.val + 1 ≤ S.ρ → q.val + 2 ≤ c → ∀ (x : Matrix (XIx (Fin κ) t (j + 1) ⊕ Fin c) (XIx (Fin κ) t j ⊕ Fin (c + 1)) k), (∀ r, x (Sum.inl r) (Sum.inr q.succ) = 0) → ∀ w : XIx (Fin κ) t (j + 1) → k, (S.T t).Phi j c H (x + Matrix.of fun r s' => if s' = Sum.inr q.succ then Sum.elim w 0 r else 0) = if ∀ r, valuation k (((S.ϖ ^ (q.val + 2) : kˣ) : k) * w r) < 1 then (S.T t).Phi j c H x else 0 := by
  first | exact @GlobalTheory.SymChain.ExchangeCol.phi_add_col | exact GlobalTheory.SymChain.ExchangeCol.phi_add_col | (intros; apply GlobalTheory.SymChain.ExchangeCol.phi_add_col <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricLevelChainUnfoldedPositionExchange

section

@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

noncomputable section
namespace GlobalTheory.SymChain.ExchangeProof

section Step
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem val_inv_mul_le_one (a : kˣ) (z : k) :
    valuation k (((a⁻¹ : kˣ) : k) * z) ≤ 1 ↔ valuation k z ≤ valuation k (a : k) := by
  have : 0 < valuation k (a : k) := by simp [zero_lt_iff]
  rw [map_mul, Units.val_inv_eq_inv_val, map_inv₀, inv_mul_le_one₀ this]

variable [MeasurableSpace k] [BorelSpace k]


open Classical in
theorem opE_step (ν : Measure k) (hν : IsUnitVol ν) {s κ : ℕ} (S : SymData k s κ) (t : Type) [Fintype t]
    [DecidableEq t] (hP : S.Pattern t) (j c : ℕ) (H : j + c = s) (q : Fin c) (hq : q.val + 1 ≤ S.ρ)
    (hqc : q.val + 2 ≤ c) : ∃ C : ℝ, 0 < C ∧
      opE S.ψ ν (q.val + 2) ((S.T t).Phi j c H) = (C : ℂ) • opE S.ψ ν (q.val + 1) ((S.T t).Phi j c H) := by
  haveI := hν.1
  have := secondCountable k
  have := t2Space k
  set Φ := (S.T t).Phi j c H with hΦ
  let I := (XIx (Fin κ) t (j + 1) ⊕ Fin c) × (XIx (Fin κ) t j ⊕ Fin (c + 1))
  let A : I → Prop := fun i => i.1 = Sum.inr q ∧ i.2.isLeft = true
  let B : I → Prop := fun i => i.2 = Sum.inr q.succ ∧ i.1.isLeft = true
  let R : I → Prop := fun i => Free (q.val + 1) i ∧ ¬ B i
  let a : kˣ := S.ϖ ^ (q.val + 1)
  let b : kˣ := S.ϖ ^ (q.val + 2)
  let sA : Set k := cball a
  let sB : Set k := (fun z => (b : k) * z) ⁻¹' {z | valuation k z < 1}
  have oB : IsOpen sB := IsOpen.preimage (by fun_prop) (by simpa using (valuation k).isOpen_ball 1)
  have sBc : sB ⊆ cball b⁻¹ := fun z hz => by
    have hz : valuation k ((b : k) * z) < 1 := hz
    have : 0 < valuation k (b : k) := by simp [zero_lt_iff]
    rw [map_mul] at hz
    change valuation k z ≤ valuation k ((b⁻¹ : kˣ) : k)
    rw [Units.val_inv_eq_inv_val, map_inv₀]
    have h1 : valuation k z = (valuation k (b : k))⁻¹ * (valuation k (b : k) * valuation k z) := by
      rw [← mul_assoc, inv_mul_cancel₀ this.ne', one_mul]
    rw [h1]; exact mul_le_of_le_one_right' hz.le
  have mA : MeasurableSet sA := (isOpen_cball a).measurableSet
  have mB : MeasurableSet sB := oB.measurableSet
  have fA : ν sA ≠ ⊤ := (isCompact_cball a).measure_lt_top.ne
  have fB : ν sB ≠ ⊤ := ((isCompact_cball b⁻¹).measure_lt_top.trans_le' (measure_mono sBc)).ne
  have pA : 0 < ν sA := (isOpen_cball a).measure_pos ν ⟨0, by simp [sA, cball]⟩
  have pB : 0 < ν sB := oB.measure_pos ν ⟨0, by simp [sB]⟩
  let G : Matrix (XIx (Fin κ) t (j + 1)) (XIx (Fin κ) t j) k → (I → k) → ℂ := fun x₀ m =>
    Φ (basePt c x₀ + Matrix.of fun r s' => m (r, s')) * (S.ψ (-ch (basePt c x₀ + Matrix.of fun r s' => m (r, s'))) : ℂ)
  have hR2 : ∀ i, R i ↔ Free (q.val + 2) i ∧ ¬ A i := by
    rintro ⟨r | r, s' | s'⟩ <;> simp [R, A, B, Free, Fin.ext_iff] <;> omega
  have hR1 : ∀ i, R i ↔ Free (q.val + 1) i ∧ ¬ B i := fun i => Iff.rfl
  have hA : ∀ i, A i → Free (q.val + 2) i := by
    rintro ⟨r | r, s' | s'⟩ h <;> simp_all [A, Free]
  have hB : ∀ i, B i → Free (q.val + 1) i := by
    rintro ⟨r | r, s' | s'⟩ h <;> simp_all [B, Free]
  have gA : ∀ x₀ (m : I → k), G x₀ m = (if ∀ i, A i → m i ∈ sA then (1 : ℂ) else 0) * G x₀ (fun i => if A i then 0 else m i) := by
    intro x₀ m
    let v : XIx (Fin κ) t j → k := fun s' => m (Sum.inr q, Sum.inl s')
    have hx : (basePt c x₀ + Matrix.of fun r s' => m (r, s')) = (basePt c x₀ + Matrix.of fun r s' =>
        (if A (r, s') then 0 else m (r, s'))) + Matrix.of fun r s' => if r = Sum.inr q then Sum.elim v 0 s' else 0 := by
      ext (r | r) (s' | s')
      · simp [A]
      · simp [A]
      · by_cases h : r = q
        · subst h; simp [A, v, basePt]
        · simp [A, h]
      · simp [A]
    have hch : ch (basePt c x₀ + Matrix.of fun r s' => m (r, s')) =
        ch (basePt c x₀ + Matrix.of fun r s' => (if A (r, s') then 0 else m (r, s'))) := by
      simp [ch, A]
    have row0 : ∀ s', (basePt c x₀ + Matrix.of fun r s' => (if A (r, s') then 0 else m (r, s'))) (Sum.inr q) (Sum.inl s') = 0 := by
      intro s'; simp [basePt, A]
    have hiff : (∀ s', valuation k ((((S.ϖ ^ (q.val + 1))⁻¹ : kˣ) : k) * v s') ≤ 1) ↔ ∀ i, A i → m i ∈ sA := by
      constructor
      · rintro h ⟨r, s' | s'⟩ ⟨rfl, hs⟩
        · exact (val_inv_mul_le_one a _).1 (h s')
        · simp at hs
      · intro h s'; exact (val_inv_mul_le_one a _).2 (h (Sum.inr q, Sum.inl s') ⟨rfl, rfl⟩)
    simp only [G]
    rw [hch, hx, hΦ, GlobalTheory.T.symLevelChain_testFunction_add_row k s κ S t hP j c H q hq _ row0 v]
    by_cases hc : ∀ i, A i → m i ∈ sA
    · rw [if_pos (hiff.2 hc), if_pos hc, one_mul]
    · rw [if_neg (fun h => hc (hiff.1 h)), if_neg hc, zero_mul, zero_mul]
  have gB : ∀ x₀ (m : I → k), G x₀ m = (if ∀ i, B i → m i ∈ sB then (1 : ℂ) else 0) * G x₀ (fun i => if B i then 0 else m i) := by
    intro x₀ m
    let w : XIx (Fin κ) t (j + 1) → k := fun r => m (Sum.inl r, Sum.inr q.succ)
    have hx : (basePt c x₀ + Matrix.of fun r s' => m (r, s')) = (basePt c x₀ + Matrix.of fun r s' =>
        (if B (r, s') then 0 else m (r, s'))) + Matrix.of fun r s' => if s' = Sum.inr q.succ then Sum.elim w 0 r else 0 := by
      ext (r | r) (s' | s')
      · simp [B]
      · by_cases h : s' = q.succ
        · subst h; simp [B, w, basePt]
        · simp [B, h]
      · simp [B]
      · simp [B]
    have hch : ch (basePt c x₀ + Matrix.of fun r s' => m (r, s')) =
        ch (basePt c x₀ + Matrix.of fun r s' => (if B (r, s') then 0 else m (r, s'))) := by
      simp [ch, B]
    have col0 : ∀ r, (basePt c x₀ + Matrix.of fun r s' => (if B (r, s') then 0 else m (r, s'))) (Sum.inl r) (Sum.inr q.succ) = 0 := by
      intro r; simp [basePt, B]
    have hiff : (∀ r, valuation k (((S.ϖ ^ (q.val + 2) : kˣ) : k) * w r) < 1) ↔ ∀ i, B i → m i ∈ sB := by
      constructor
      · rintro h ⟨r | r, s'⟩ ⟨rfl, hs⟩
        · exact h r
        · simp at hs
      · intro h r; exact h (Sum.inl r, Sum.inr q.succ) ⟨rfl, rfl⟩
    simp only [G]
    rw [hch, hx, hΦ, GlobalTheory.T.matrix_block_column_vanishing_step k s κ S t hP j c H q hq hqc _ col0 w]
    by_cases hc : ∀ i, B i → m i ∈ sB
    · rw [if_pos (hiff.2 hc), if_pos hc, one_mul]
    · rw [if_neg (fun h => hc (hiff.1 h)), if_neg hc, zero_mul, zero_mul]
  have e2 : ∀ x₀, opE S.ψ ν (q.val + 2) Φ x₀ = (((ν sA).toReal ^ Fintype.card {i // A i} : ℝ) : ℂ) *
      ∫ e : {i // R i} → k, G x₀ (fun i => if h : R i then e ⟨i, h⟩ else 0) ∂(Measure.pi fun _ => ν) :=
    fun x₀ => GlobalTheory.T.integral_pi_block_indicator_eq_pow_mul k ν I (Free (q.val + 2)) A R hR2 hA sA mA fA (G x₀) (gA x₀)
  have e1 : ∀ x₀, opE S.ψ ν (q.val + 1) Φ x₀ = (((ν sB).toReal ^ Fintype.card {i // B i} : ℝ) : ℂ) *
      ∫ e : {i // R i} → k, G x₀ (fun i => if h : R i then e ⟨i, h⟩ else 0) ∂(Measure.pi fun _ => ν) :=
    fun x₀ => GlobalTheory.T.integral_pi_block_indicator_eq_pow_mul k ν I (Free (q.val + 1)) B R hR1 hB sB mB fB (G x₀) (gB x₀)
  have tA : 0 < (ν sA).toReal := ENNReal.toReal_pos pA.ne' fA
  have tB : 0 < (ν sB).toReal := ENNReal.toReal_pos pB.ne' fB
  refine ⟨(ν sA).toReal ^ Fintype.card {i // A i} / (ν sB).toReal ^ Fintype.card {i // B i},
    div_pos (pow_pos tA _) (pow_pos tB _), funext fun x₀ => ?_⟩
  rw [Pi.smul_apply, e2, e1, smul_eq_mul, ← mul_assoc, ← Complex.ofReal_mul, div_mul_cancel₀ _ (pow_pos tB _).ne']

end Step

theorem exchangeAt : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → ∀ (s κ : ℕ) (S : SymData k s κ) (t : Type)
    [Fintype t] [DecidableEq t], S.Pattern t → S.ExchangeAt t ν := by
  intro k _ _ _ _ _ _ ν hν s κ S t _ _ hP j c H p hp1
  induction p, hp1 using Nat.le_induction with
  | base => intro _ _; exact ⟨1, one_pos, by simp⟩
  | succ p hp ih =>
    intro hpc hpρ
    obtain ⟨C, hC, e⟩ := ih (by omega) (by omega)
    obtain ⟨C', hC', e'⟩ := opE_step ν hν S t hP j c H ⟨p - 1, by omega⟩ (by simp; omega) (by simp; omega)
    have h2 : (p - 1) + 2 = p + 1 := by omega
    have h1 : (p - 1) + 1 = p := by omega
    simp only [h1, h2] at e'
    refine ⟨C' * C, mul_pos hC' hC, ?_⟩
    rw [e', e, smul_smul, Complex.ofReal_mul]

end GlobalTheory.SymChain.ExchangeProof
end
end
end
