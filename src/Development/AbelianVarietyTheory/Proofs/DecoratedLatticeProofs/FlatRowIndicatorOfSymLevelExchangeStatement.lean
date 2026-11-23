module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ContrFactor
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.AllPositions
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapRowEqZeroUnlessRowMemDualLatticeStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatRowMapEqRootExchangeOperatorTranslateStatement
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.StandardOrderExtendedBasisApplyLowBlock
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RootExchangeRowUnipotentLatticeFrameConjApplyStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RootExchangeRowUnipotentMemSourceLevelStatement
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FramePositiveSum
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IteratedDepthOneLevelCharOfOneRowFirstBlockStatement

section

@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData

theorem _root_.GlobalTheory.T.iteratedDepthOneLevel_char_of_one_row_first_block : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : Type) [Fintype r] [DecidableEq r] [Fintype t] [DecidableEq t] (P : TypeDatum (k := k) (a := r)) (μ : ℕ → kˣ →* ℂˣ) (hμ : ∀ j, IsTame (μ j)) (j : ℕ) (r₀ : r) (h : (P.iter t μ hμ j).J), (∀ a b, a ≠ Sum.inl r₀ → (h : GL (Ix r t j) k).val a b = (1 : Matrix (Ix r t j) (Ix r t j) k) a b) → (h : GL (Ix r t j) k).val (Sum.inl r₀) (Sum.inl r₀) = 1 → ∃ g : P.J, (g : GL r k).val = (h : GL (Ix r t j) k).val.submatrix Sum.inl Sum.inl ∧ (P.iter t μ hμ j).lam h = P.lam g := by
  have det_eq_one_of_row {k n : Type} [Field k] [Fintype n] [DecidableEq n]
      (M : Matrix n n k) (i : n)
      (h : ∀ a b, a ≠ i → M a b = (1 : Matrix n n k) a b)
      (hii : M i i = 1) : M.det = 1 := by
    have e : M = 1 + replicateCol Unit (Pi.single i (1 : k)) *
        replicateRow Unit (M i - Pi.single i (1 : k)) := by
      ext a b
      by_cases ha : a = i
      · subst ha
        by_cases hb : b = a
        · subst hb
          simp [Matrix.mul_apply, hii]
        · simp [Matrix.mul_apply, hb, Ne.symm hb]
      · simp [Matrix.mul_apply, h a b ha, Pi.single_apply, ha]
    rw [e, det_one_add_replicateCol_mul_replicateRow]
    simp [hii]
  intro k _ _ _ _ r t _ _ _ _ P μ hμ j r₀
  induction j with
  | zero =>
    intro h _ _
    exact ⟨⟨(reGL (ixZero r t)).symm h, h.2⟩, rfl, rfl⟩
  | succ j ih =>
    intro h h1 h2
    let Q := P.iter t μ hμ j
    let h' : Q.stepJ t := ⟨(reGL (ixSucc r t j)).symm h, h.2⟩
    have eh' : (h' : GL (Ix r t j ⊕ t) k).val =
        (h : GL (Ix r t (j + 1)) k).val.submatrix (ixSucc r t j) (ixSucc r t j) := rfl
    let c := Q.corner h'
    have ec : ∀ a b, (c : GL (Ix r t j) k).val a b =
        (h : GL (Ix r t (j + 1)) k).val (ixSucc r t j (.inl a)) (ixSucc r t j (.inl b)) := by
      intro a b
      rw [Q.corner_val]
      rfl
    have hne : ∀ a, a ≠ Sum.inl r₀ → ixSucc r t j (.inl a) ≠ Sum.inl r₀ := by
      intro a ha e
      apply ha
      have : (Sum.inl a : Ix r t j ⊕ t) = Sum.inl (Sum.inl r₀) :=
        (ixSucc r t j).injective (e.trans rfl)
      exact Sum.inl_injective this
    have c1 : ∀ a b, a ≠ Sum.inl r₀ →
        (c : GL (Ix r t j) k).val a b = (1 : Matrix (Ix r t j) (Ix r t j) k) a b := by
      intro a b ha
      rw [ec, h1 _ _ (hne a ha), Matrix.one_apply, Matrix.one_apply]
      simp [(ixSucc r t j).injective.eq_iff]
    have c2 : (c : GL (Ix r t j) k).val (Sum.inl r₀) (Sum.inl r₀) = 1 := by
      rw [ec]
      exact h2
    obtain ⟨g, hg, hl⟩ := ih c c1 c2
    refine ⟨g, ?_, ?_⟩
    · rw [hg]
      ext x y
      exact ec _ _
    · have d1 : Matrix.GeneralLinearGroup.det (c : GL (Ix r t j) k) = 1 := Units.ext (by
        rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]
        exact det_eq_one_of_row _ _ c1 c2)
      have d2 : Matrix.GeneralLinearGroup.det (h' : GL (Ix r t j ⊕ t) k) = 1 := Units.ext (by
        rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one, eh', det_submatrix_equiv_self]
        exact det_eq_one_of_row _ _ h1 h2)
      have e0 : (P.iter t μ hμ (j + 1)).lam h = (Q.step t (μ (j + 1)) (hμ _)).lam h' := rfl
      rw [e0, Q.step_lam _ _ h' c (Q.corner_val h'), ← hl, d1, d2]
      simp [Q]
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricPositionLevelCharacterEqOneSingleRowStatement

section

@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum

theorem _root_.GlobalTheory.T.symmetricPositionLevel_character_eq_one_single_row : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (ϖ : kˣ) (ρ κ l : ℕ) (P : TypeDatum k (Fin κ ⊕ Fin l)), GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsSymLevel ψ ϖ ρ P → ∀ (i₀ : Fin l) (g : P.J), (∀ a b, a ≠ Sum.inr i₀ → (g : GL (Fin κ ⊕ Fin l) k).val a b = (1 : Matrix (Fin κ ⊕ Fin l) (Fin κ ⊕ Fin l) k) a b) → (∀ i : Fin l, i.val = i₀.val + 1 → (g : GL (Fin κ ⊕ Fin l) k).val (Sum.inr i₀) (Sum.inr i) = 0) → P.lam g = 1 := by
  intro k _ _ _ _ ψ ϖ ρ κ l P hP i₀ g h1 h2
  have hs : simpleSum (g : GL (Fin κ ⊕ Fin l) k) = 0 := by
    unfold simpleSum
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    split_ifs with hij
    · by_cases hi : i = i₀
      · subst hi; exact h2 j hij
      · have hne : i ≠ j := by
          intro e; subst e; omega
        rw [h1 _ _ (by simpa using hi)]
        simp [hne]
    · rfl
  have hu : superSum Fin.val (g : GL (Fin κ ⊕ Fin l) k).val.toBlocks₁₁ = 0 := by
    unfold superSum
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
    split_ifs with hab
    · have hne : a ≠ b := by
        intro e; subst e; omega
      rw [Matrix.toBlocks₁₁]
      simp only [Matrix.of_apply]
      rw [h1 _ _ (by simp)]
      simp [hne]
    · rfl
  apply Units.ext
  rw [hP.2 g, hs, hu]
  simp
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatRowIndicatorOfSymLevelExchange

section

@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

noncomputable section
namespace GlobalTheory.LocFlat

theorem lam_rowE_symLevel : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t],
    ∀ j c (H : j + 1 + c = s) (r : ℕ), c = 2 * r → ∀ u : XIx (Fin κ) t j → k,
      ∀ hm : rowE (c + 1 + 1) (r + 1) u ∈ ((S.T t).lev j (c + 1 + 1) (by omega)).J,
      ((S.T t).lev j (c + 1 + 1) (by omega)).lam ⟨_, hm⟩ = 1 := by
  intro k _ _ _ _ s κ S t _ _ j c H r hc u hm
  have hodd := S.odd
  have hsh := GlobalTheory.T.rootExchangeRowUnipotent_latticeFrame_conj_apply k (Fin κ) t S.ϖ j (c + 1 + 1) (s + 1) (by omega) r (by omega) u
  obtain ⟨g, hg, hl⟩ := GlobalTheory.T.iteratedDepthOneLevel_char_of_one_row_first_block k _ t S.P S.μ S.tame j (Sum.inr ⟨r, by omega⟩) ⟨_, hm⟩
    (fun a b ha => by
      have := hsh a b
      rw [if_neg ha, add_zero] at this
      exact this)
    (by
      have := hsh (Sum.inl (Sum.inr ⟨r, by omega⟩)) (Sum.inl (Sum.inr ⟨r, by omega⟩))
      rw [if_pos rfl] at this
      have e := standardOrderExtendedBasis_apply_low_block (Fin κ) t j (c + 1 + 1) (l := s + 1) (by omega) ⟨r, by omega⟩
      simp only at e
      rw [e] at this
      simpa using this)
  have hsym : S.P.lam g = 1 := by
    refine GlobalTheory.T.symmetricPositionLevel_character_eq_one_single_row k S.ψ S.ϖ S.ρ κ (s + 1) S.P S.sym ⟨r, by omega⟩ g (fun a b ha => ?_) (fun i hi => ?_)
    · rw [hg, submatrix_apply]
      have := hsh (Sum.inl a) (Sum.inl b)
      rw [if_neg (fun e => ha (Sum.inl_injective e)), add_zero] at this
      exact this.trans (by simp [Matrix.one_apply])
    · have ei : i = ⟨r + 1, by omega⟩ := Fin.ext hi
      rw [hg, submatrix_apply, ei]
      have := hsh (Sum.inl (Sum.inr ⟨r, by omega⟩)) (Sum.inl (Sum.inr ⟨r + 1, by omega⟩))
      rw [if_pos rfl] at this
      have e := standardOrderExtendedBasis_apply_low_block (Fin κ) t j (c + 1 + 1) (l := s + 1) (by omega) ⟨r + 1, by omega⟩
      simp only at e
      rw [e] at this
      exact this.trans (by simp [Matrix.one_apply])
  exact hl.trans hsym

theorem pureRow_of_exchange : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → ∀ (s κ : ℕ) (S : SymData k s κ) (t : Type)
    [Fintype t] [DecidableEq t], S.Pattern t → S.ExchangeAt t ν → GlobalTheory.LocFlat.PureRow S t ν := by
  intro k _ _ _ _ _ _ ν hν s κ S t _ _ hP hE
  haveI := hν.1
  intro j c H r hc
  have hodd := S.odd
  obtain ⟨C, hC, hEq⟩ := hE j (c + 1) (by omega) (r + 1) (by omega) (by omega) (by omega)
  have HR : (S.T t).Regular := Chain.ofType_regular _ _ _ _ _
  have HL : (S.T t).Laws := Chain.ofType_laws _ _ _ _ _
  set Φ := (S.T t).Phi j (c + 1) (by omega) with hΦ
  set V := volNat ν ((S.T t).bas (j + 1) (c + 1) (by omega)) (Cgrp ((S.T t).lev (j + 1) (c + 1) (by omega)).J 1)
    with hV
  have hVpos : 0 < V :=
    volNat_Cgrp_pos ν (HR.2.2 (j + 1) (c + 1) (by omega)).1 (HR.2.2 (j + 1) (c + 1) (by omega)).2.1 _ 1
  have hom1 : om ((S.T t).mu (j + 1)) 1 1 Φ = Φ := by
    funext z; simp [om, nabs]
  have hentry : ∀ x₀, (S.T t).entry S.ψ ν j c H 1 1 x₀ = ((V⁻¹ : ℝ) : ℂ) * opE S.ψ ν 1 Φ x₀ := by
    intro x₀
    simp only [Chain.entry, xi, flat]
    rw [hom1]
  refine ⟨C * V, mul_pos hC hVpos, fun x => ?_⟩
  by_cases hu : x (Sum.inr ()) ∈ box (XIx (Fin κ) t j) (S.ϖ ^ (r + 1))
  · rw [if_pos hu, mul_one, hentry]
    have hm := GlobalTheory.T.rootExchangeRowUnipotent_mem_sourceLevel k s κ S t hP j c H r hc _ hu
    have hl := lam_rowE_symLevel k s κ S t j c H r hc _ hm
    have hdet : Matrix.GeneralLinearGroup.det (rowE (c + 1 + 1) (r + 1) (x (Sum.inr ()))) = 1 := by
      ext; simp [rowE, lowU, Matrix.det_fromBlocks_zero₁₂]
    have hT := (HL.1 j (c + 1) (by omega)).1 ⟨_, hm⟩
    rw [hl] at hT
    have hfun : (fun z => Φ (z * (rowE (c + 1 + 1) (r + 1) (x (Sum.inr ()))).val)) = Φ := by
      funext z
      have := congrFun hT z
      simpa [om, hdet, nabs] using this
    rw [GlobalTheory.T.flatRowMap_eq_rootExchangeOperator_translate k S.ψ ν S.cond.continuous inferInstance (XIx (Fin κ) t (j + 1)) (XIx (Fin κ) t j) (c + 1)
      (r + 1) (by omega) (by omega) Φ (HR.1 j (c + 1) (by omega)) x]
    erw [hfun]
    rw [congrFun hEq]
    have hV0 : (V : ℂ) ≠ 0 := by exact_mod_cast hVpos.ne'
    rw [Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_inv]
    field_simp
  · rw [if_neg hu, mul_zero, GlobalTheory.T.flatMapRow_eq_zero_unless_row_mem_dualLattice k ν s κ S t j c H r hc x hu]

end GlobalTheory.LocFlat
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatRowIndicatorOfSymLevelExchangeStatement

section

@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

theorem _root_.GlobalTheory.T.flatRowIndicator_of_symLevelExchange : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → ∀ (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t], S.Pattern t → S.ExchangeAt t ν → GlobalTheory.LocFlat.PureRow S t ν := by
  first | exact @GlobalTheory.LocFlat.pureRow_of_exchange | exact GlobalTheory.LocFlat.pureRow_of_exchange | (intros; apply GlobalTheory.LocFlat.pureRow_of_exchange <;> assumption)
end
end
