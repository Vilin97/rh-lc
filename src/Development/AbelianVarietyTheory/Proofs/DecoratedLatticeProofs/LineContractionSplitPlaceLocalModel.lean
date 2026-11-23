module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousKappa
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselLineContractionHeisenbergInvariantStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselLineContractionThetaFunctionIsLocalModelStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergFrameHalfInverse
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilCharacterSplitPlaceExistsContinuousNontrivia
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselLineLinkGramSimilitudeBijective
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HermitianLinkMapAdditiveRationalEquivariant
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalModelBoxProductOrthogonalSumTarget
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SkewAdjointSimilitudeExchangesHalves
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaContractionIsLocalModelSecondVariableStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilCharacterSplitPlaceExistsContinuousNontriviaStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LineRowTranslationHeisenbergSplitPlace

section

@[expose] public section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod
open scoped GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LineRowFrame

variable {D : D7}

theorem half_mul {e : AE D} {l m n : ℕ} {u : Mx D l m} (hu : IsHalf e u) (v : Mx D m n) : IsHalf e (u ⬝ v) := fun i j => by
  simp only [Matrix.mul_apply, Finset.mul_sum, ← mul_assoc, hu i]

theorem mul_half {e : AE D} {l m n : ℕ} (u : Mx D l m) {v : Mx D m n} (hv : IsHalf e v) : IsHalf e (u ⬝ v) := fun i j => by
  simp only [Matrix.mul_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => by rw [mul_left_comm, hv a j]

theorem adj_half {e : AE D} {m n : ℕ} {u : Mx D m n} (hu : IsHalf e u) : IsHalf (cA D e) (adj u) := fun i j => by
  change cA D e * cA D (u j i) = cA D (u j i)
  rw [← map_mul, hu j i]

theorem ofAdj_half {e : AE D} (S T : HSp D) {z : Mx D S.rank T.rank} (hz : IsHalf e z) :
    IsHalf (cA D e) (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj S T z) := fun i j => by
  have h := mul_half (giA T) (half_mul (adj_half hz) (gA S)) i j
  rw [GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj, Matrix.smul_apply, smul_eq_mul, mul_left_comm, h]

theorem xi_mul_hO (S T : HSp D) (x : WO S T) (z : Mx D S.rank T.rank) :
    incA D D.host.xi0 * hO S T x (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj S T z) = (z ⬝ x).trace := by
  conv_rhs => rw [← GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.starAdj_ofAdj S T z]
  rw [hO_eq_trace, GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.starAdj, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, Matrix.mul_assoc,
    Matrix.mul_assoc]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k)

theorem incA_mul_ι (a : D.host.E) (x : k) : incA D a * p.ι x = p.ι (p.pr a * x) := by
  conv_rhs => rw [← p.π_ι x, Place.pr, ← map_mul, p.ι_π, mul_left_comm, Witness.e_ι]

theorem pr_mulVec {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E) (v : Fin n → D.host.E) (r : Fin m) :
    p.pr ((M *ᵥ v) r) = ∑ a, p.pr (M r a) * p.pr (v a) := by

  simp only [Place.pr, Matrix.mulVec, dotProduct, map_sum, map_mul]

theorem line_row : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (ψk : AddChar k Circle), p.IsChar ψ ψk → ∀ (ρ σ : ℕ) (B : BesLev D ρ) (B' : BesLev D σ) (l : Link B B'.L B'.ζ) (S : HSp D) (s : k), s ≠ 0 → ∀ (n n' n'' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype n''] [DecidableEq n''] (FA : Frame k B.A.rank n') (F₀ : Frame k B.V₀.rank (n' ⊕ Unit)) (FS : Frame k S.rank n) (FA' : Frame k B'.A.rank n'') (F₀' : Frame k B'.V₀.rank (n'' ⊕ Unit)), p.IsCoreFrame B s FA F₀ → p.IsCoreFrame B' (s * p.xi) FA' F₀' → ∀ u₀ : n → k, ∃ x : WO S B'.L, p.up FS F₀' (fromRows 0 (Matrix.of fun _ => u₀)) = (B'.o.resT S).symm (0, x) ∧ IsHalf (cA D p.e) ((B.o.resS S).symm (0, l.κ S x)) ∧ ∀ t : Matrix n (n' ⊕ Unit) k, ψ (symplO B.V₀ S (p.up F₀ FS t) ((B.o.resS S).symm (0, l.κ S x))) = ((ψk (-(u₀ ⬝ᵥ fun r => t r (Sum.inr ()))) : Circle) : ℂ) := by
  intro D k _ _ _ _ p ψ hψ ψk hk ρ σ B B' l S s hs n n' n'' _ _ _ _ _ _ FA F₀ FS FA' F₀' h₀ h₀' u₀
  have hxi : p.xi ≠ 0 := (GlobalTheory.LocChar.weil_char_split D k p ψ hψ).2.2.1
  obtain ⟨w, hw⟩ : ∃ w, w = u₀ ᵥ* FS.γ := ⟨_, rfl⟩
  obtain ⟨x, hx⟩ : ∃ x : WO S B'.L, ∀ a c, x a c = p.ι (s * p.xi * p.pr (B'.ζ a) * w c) :=
    ⟨Matrix.of fun a c => p.ι (s * p.xi * p.pr (B'.ζ a) * w c), fun _ _ => rfl⟩
  have hxh : IsHalf p.e x := fun a c => by rw [hx, Witness.e_ι]
  have hy : (B.o.resS S).symm (0, l.κ S x) = l.κ S x ⬝ B.o.pB := by
    rw [OrthDec.resS_symm_apply, Matrix.zero_mul, zero_add]
  have hh : IsHalf (cA D p.e) ((B.o.resS S).symm (0, l.κ S x)) := by
    rw [hy]
    exact half_mul (ofAdj_half B.L S (mul_half _ hxh)) _
  refine ⟨x, ?_, hh, fun t => ?_⟩
  · rw [OrthDec.resT_symm_apply, Matrix.mul_zero, zero_add]
    ext r c
    have e1 : (F₀'.β * (fromRows 0 (Matrix.of fun _ => u₀) : Matrix (n'' ⊕ Unit) n k) * FS.γ) r c = s * p.xi * p.pr (vecB B'.o B'.ζ r) * w c := by
      rw [Matrix.mul_assoc, fromRows_mul, Matrix.zero_mul, Matrix.mul_apply, Fintype.sum_sum_type, ← h₀'.2 r, hw]
      simp [Matrix.mul_apply, Matrix.vecMul, dotProduct]
    change p.ι ((F₀'.β * (fromRows 0 (Matrix.of fun _ => u₀) : Matrix (n'' ⊕ Unit) n k) * FS.γ) r c) = _

    rw [e1, vecB, pr_mulVec, Finset.mul_sum, Finset.sum_mul, map_sum, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hx]
    change _ = incA D (B'.o.iB r a) * _
    rw [incA_mul_ι]
    congr 1
    ring
  · rw [(GlobalTheory.LocSympl.halves_at_split D k p _ _ B.V₀ S F₀ FS ψ ψk hk).2.2.2.1 t _ hh]
    congr 2
    rw [B.o.hO_resS, AddEquiv.apply_symm_apply, hO_eq_trace B.A, adj_zero, Matrix.zero_mul, Matrix.mul_zero,
      Matrix.trace_zero, zero_add]
    refine mul_left_cancel₀ hxi ?_
    have e2 : ∀ a c, p.π (((rat l.τ : Mx D B.L.rank B'.L.rank) ⬝ x) a c) = -(s * p.xi * w c) * p.pr (B.ζ a) := fun a c => by
      have h1 := pr_mulVec p l.τ B'.ζ a
      rw [l.map, Pi.neg_apply, Place.pr, map_neg, map_neg] at h1

      rw [Place.pr, neg_mul, ← mul_neg, h1, Matrix.mul_apply, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [map_mul, hx, p.π_ι]
      change p.pr (l.τ a b) * _ = _
      ring
    have e3 : ∀ c a, p.π ((p.up F₀ FS t ⬝ B.o.jB) c a) = ∑ r, (FS.β * t * F₀.γ) c r * p.pr (B.o.iB r a) := fun c a => by

      rw [Matrix.mul_apply, map_sum]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [map_mul]
      exact congrArg (· * _) (p.π_ι _)
    have e4 : ∀ c, ∑ r, (FS.β * t * F₀.γ) c r * F₀.β r (Sum.inr ()) = (FS.β * t) c (Sum.inr ()) := fun c => by
      rw [← Matrix.mul_apply, Matrix.mul_assoc, F₀.γβ, Matrix.mul_one]
    have e5 : ∑ c, w c * (FS.β * t) c (Sum.inr ()) = u₀ ⬝ᵥ fun r => t r (Sum.inr ()) := by
      change (w ᵥ* (FS.β * t)) (Sum.inr ()) = (u₀ ᵥ* t) (Sum.inr ())
      rw [hw, Matrix.vecMul_vecMul, ← Matrix.mul_assoc, FS.γβ, Matrix.one_mul]
    change p.π (incA D D.host.xi0) * p.π (hO B.L S (p.up F₀ FS t ⬝ B.o.jB) (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj B.L S _)) = _

    rw [← map_mul, xi_mul_hO, Matrix.trace_mul_comm, ← e5, mul_neg, Finset.mul_sum, ← Finset.sum_neg_distrib,
    Matrix.trace, map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_

    rw [Matrix.diag_apply, Matrix.mul_apply, map_sum, ← e4,
    Finset.sum_congr rfl fun a _ => (p.π.map_mul _ _).trans (congrArg₂ (· * ·) (e3 c a) (e2 a c))]
    generalize FS.β * t * F₀.γ = M
    simp only [h₀.2, vecB, pr_mulVec, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun a _ => ?_
    ring

end GlobalTheory.LineRowFrame
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LineRowTranslationHeisenbergSplitPlaceStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.lineRow_translation_heisenberg_splitPlace : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (ψk : AddChar k Circle), p.IsChar ψ ψk → ∀ (ρ σ : ℕ) (B : BesLev D ρ) (B' : BesLev D σ) (l : Link B B'.L B'.ζ) (S : HSp D) (s : k), s ≠ 0 → ∀ (n n' n'' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype n''] [DecidableEq n''] (FA : Frame k B.A.rank n') (F₀ : Frame k B.V₀.rank (n' ⊕ Unit)) (FS : Frame k S.rank n) (FA' : Frame k B'.A.rank n'') (F₀' : Frame k B'.V₀.rank (n'' ⊕ Unit)), p.IsCoreFrame B s FA F₀ → p.IsCoreFrame B' (s * p.xi) FA' F₀' → ∀ u₀ : n → k, ∃ x : WO S B'.L, p.up FS F₀' (fromRows 0 (Matrix.of fun _ => u₀)) = (B'.o.resT S).symm (0, x) ∧ IsHalf (cA D p.e) ((B.o.resS S).symm (0, l.κ S x)) ∧ ∀ t : Matrix n (n' ⊕ Unit) k, ψ (symplO B.V₀ S (p.up F₀ FS t) ((B.o.resS S).symm (0, l.κ S x))) = ((ψk (-(u₀ ⬝ᵥ fun r => t r (Sum.inr ()))) : Circle) : ℂ) := by
  first | exact @GlobalTheory.LineRowFrame.line_row | exact GlobalTheory.LineRowFrame.line_row | (intros; apply GlobalTheory.LineRowFrame.line_row <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLineColumnTranslationHeisenberg

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ContrFrameCol

open GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule GlobalTheory.KappaHalf

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem ι_mul_rat (p : Place D k) {l m r : ℕ} (N : Matrix (Fin r) (Fin l) k) (M : Matrix (Fin l) (Fin m) D.host.E) :
    (N.map p.ι : Mx D r l) * rat M = (N * M.map p.pr).map p.ι := by
  ext i j

  simp only [Matrix.mul_apply, Matrix.map_apply, rat, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [mul_comm, BoxModel.incA_mul_ι, mul_comm]

theorem qB_β (p : Place D k) {n : Type} [Fintype n] [DecidableEq n] {ρ : ℕ} (B : BesLev D ρ) (s : k)
    (FA : Frame k B.A.rank n) (F : Frame k B.V₀.rank (n ⊕ Unit)) (h : p.IsCoreFrame B s FA F) :
    B.o.qB.map p.pr * F.β = fromCols 0 (Matrix.of fun r _ => s * p.pr (B.ζ r)) := by
  have hm : ∀ {a b : ℕ} (M : Matrix (Fin a) (Fin b) D.host.E), M.map p.pr = M.map (BoxModel.prH p) :=
    fun _ => rfl
  ext r c
  rcases c with a | ⟨⟨⟩⟩
  · have : (B.o.qB.map p.pr * F.β) r (Sum.inl a) = (B.o.qB.map p.pr * (B.o.iA.map p.pr * FA.β)) r a := by
      simp only [Matrix.mul_apply (M := B.o.qB.map p.pr), h.1]
    rw [this, ← Matrix.mul_assoc, ← BoxModel.map_pr_mul, B.o.qB_iA, hm]
    simp
  · have h1 : B.o.qB *ᵥ vecB B.o B.ζ = B.ζ := by
      rw [vecB, Matrix.mulVec_mulVec, B.o.qB_iB, Matrix.one_mulVec]
    have h2 : p.pr (B.ζ r) = ∑ j, p.pr (B.o.qB r j) * p.pr (vecB B.o B.ζ j) := by
      conv_lhs => rw [← h1]
      change BoxModel.prH p (∑ j, B.o.qB r j * vecB B.o B.ζ j) = ∑ j, BoxModel.prH p _ * BoxModel.prH p _

      simp only [map_sum, map_mul]
    rw [fromCols_apply_inr, Matrix.of_apply, h2, Finset.mul_sum, Matrix.mul_apply]
    simp only [h.2, Matrix.map_apply]
    exact Finset.sum_congr rfl fun j _ => by ring

theorem line_γ_iA (p : Place D k) {n m : Type} [Fintype n] [DecidableEq n] {ρ : ℕ} (B : BesLev D ρ) (s : k)
    (FA : Frame k B.A.rank n) (F : Frame k B.V₀.rank (n ⊕ Unit)) (h : p.IsCoreFrame B s FA F)
    (y : Matrix m Unit k) :
    fromCols (0 : Matrix m n k) y * F.γ * B.o.iA.map p.pr = 0 := by
  have h1 : fromCols (0 : Matrix m n k) y * F.γ * B.o.iA.map p.pr * FA.β = 0 := by
    ext r a
    have : (fromCols (0 : Matrix m n k) y * F.γ * B.o.iA.map p.pr * FA.β) r a
        = (fromCols (0 : Matrix m n k) y * F.γ * F.β) r (Sum.inl a) := by
      rw [Matrix.mul_assoc (_ * F.γ)]
      simp only [Matrix.mul_apply (M := fromCols (0 : Matrix m n k) y * F.γ), h.1]
    rw [this, Matrix.mul_assoc, F.γβ, Matrix.mul_one]
    simp
  rw [← Matrix.mul_one (_ * B.o.iA.map p.pr), ← FA.βγ, ← Matrix.mul_assoc, h1, Matrix.zero_mul]

theorem xi_mul_hO (L S : HSp D) (Y : WO L S) (z : Mx D L.rank S.rank) :
    incA D D.host.xi0 * hO L S Y (ofAdj L S z) = (z * Y).trace := by
  conv_rhs => rw [← starAdj_ofAdj L S z]
  rw [hO_eq_trace, starAdj, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
  simp only [Matrix.mul_assoc]

theorem link_frames (p : Place D k) {ρ σ : ℕ} (B : BesLev D ρ) (B' : BesLev D σ) (l : Link B B'.L B'.ζ) (s : k)
    {n' n'' : Type} [Fintype n'] [DecidableEq n'] [Fintype n''] [DecidableEq n'']
    (FA : Frame k B.A.rank n') (F₀ : Frame k B.V₀.rank (n' ⊕ Unit))
    (FA' : Frame k B'.A.rank n'') (F₀' : Frame k B'.V₀.rank (n'' ⊕ Unit))
    (h : p.IsCoreFrame B s FA F₀) (h' : p.IsCoreFrame B' (s * p.xi) FA' F₀') :
    B.o.iB.map p.pr * (l.τ.map p.pr * (B'.o.qB.map p.pr * F₀'.β))
      = F₀.β * (Matrix.single (Sum.inr ()) (Sum.inr ()) (-p.xi) : Matrix (n' ⊕ Unit) (n'' ⊕ Unit) k) := by
  rw [qB_β p B' _ FA' F₀' h', ← Matrix.mul_assoc, ← BoxModel.map_pr_mul]
  have h1 : (B.o.iB * l.τ) *ᵥ B'.ζ = -vecB B.o B.ζ := by
    rw [← Matrix.mulVec_mulVec, l.map, Matrix.mulVec_neg, vecB]
  ext r c
  rcases c with a | ⟨⟨⟩⟩
  · simp [Matrix.mul_apply, Matrix.single_apply]
  · have h2 : ∑ j, p.pr ((B.o.iB * l.τ) r j) * p.pr (B'.ζ j) = -p.pr (vecB B.o B.ζ r) := by
      have := congrArg (fun v => BoxModel.prH p (v r)) h1

      simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Pi.neg_apply, map_neg] at this
      exact this
    have h3 : (F₀.β * (Matrix.single (Sum.inr ()) (Sum.inr ()) (-p.xi) : Matrix (n' ⊕ Unit) (n'' ⊕ Unit) k)) r (Sum.inr ())
        = F₀.β r (Sum.inr ()) * -p.xi := by
      simp [Matrix.mul_apply, Matrix.single_apply]
    rw [h3, h.2, Matrix.mul_apply]
    simp only [fromCols_apply_inr, Matrix.of_apply, Matrix.map_apply]
    calc _ = s * p.xi * ∑ j, p.pr ((B.o.iB * l.τ) r j) * p.pr (B'.ζ j) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
      _ = _ := by rw [h2]; ring

theorem frame_col : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (ψk : AddChar k Circle), p.IsChar ψ ψk → ∀ (ρ σ : ℕ) (B : BesLev D ρ) (B' : BesLev D σ) (l : Link B B'.L B'.ζ) (S : HSp D) (s : k), s ≠ 0 → ∀ (n n' n'' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype n''] [DecidableEq n''] (FA : Frame k B.A.rank n') (F₀ : Frame k B.V₀.rank (n' ⊕ Unit)) (FS : Frame k S.rank n) (FA' : Frame k B'.A.rank n'') (F₀' : Frame k B'.V₀.rank (n'' ⊕ Unit)), p.IsCoreFrame B s FA F₀ → p.IsCoreFrame B' (s * p.xi) FA' F₀' → ∀ y₀ : n → k, ∃ x : WO S B'.L, p.up F₀ FS (fromCols 0 (Matrix.of fun r _ => y₀ r)) = (B.o.resS S).symm (0, l.κ S x) ∧ IsHalf (cA D p.e) ((B'.o.resT S).symm (0, x)) ∧ ∀ t : Matrix (n'' ⊕ Unit) n k, ψ (symplO S B'.V₀ (p.up FS F₀' t) ((B'.o.resT S).symm (0, x))) = ((ψk (-(t (Sum.inr ()) ⬝ᵥ y₀)) : Circle) : ℂ) := by
  intro D k _ _ _ _ p ψ hψ ψk hk ρ σ B B' l S s _ n n' n'' _ _ _ _ _ _ FA F₀ FS FA' F₀' h h' y₀
  have hxi : p.xi ≠ 0 := (GlobalTheory.LocChar.weil_char_split D k p ψ hψ).2.2.1
  have hτ : l.τ ≠ 0 := by
    intro h0
    have h1 := l.map
    rw [h0, Matrix.zero_mulVec, eq_comm, neg_eq_zero] at h1
    exact B.line.2 (by rw [h1, Matrix.mulVec_zero, dotProduct_zero])
  obtain ⟨τi, -, hi⟩ := LinkGram.exists_inv_of_rank_one B.line.1 B'.line.1 l.τ hτ
  set M : Matrix n (n' ⊕ Unit) k := fromCols 0 (Matrix.of fun r _ => y₀ r) with hM
  set Y : WO B.L S := p.up F₀ FS M * B.o.jB with hY
  have hYh : IsHalf p.e Y := isHalf_mul_right _ (GlobalTheory.LocSympl.up_half p F₀ FS M)
  have hκ : l.κ S (rat τi * starAdj B.L S Y) = Y := by
    rw [Link.κ, ← Matrix.mul_assoc, ← rat_mul, hi, rat_one, Matrix.one_mul, LinkGram.ofAdj_starAdj]
  refine ⟨rat τi * starAdj B.L S Y, ?_, ?_, fun t => ?_⟩
  · rw [hκ, AddEquiv.eq_symm_apply, OrthDec.resS_apply]
    refine Prod.ext ?_ rfl
    change (FS.β * M * F₀.γ).map p.ι * rat B.o.iA = 0
    rw [ι_mul_rat, Matrix.mul_assoc FS.β, Matrix.mul_assoc FS.β, hM, line_γ_iA p B s FA F₀ h]
    simp
  · rw [OrthDec.resT_symm_apply, Matrix.mul_zero, zero_add]
    exact isHalf_mul_left _ (isHalf_mul_left _ (isHalf_smul _ (isHalf_mul_left _
      (isHalf_mul_right _ (isHalf_cA_adj hYh)))))
  · rw [GlobalTheory.LocSympl.psi_sympl_up p FS F₀' ψ ψk hk, OrthDec.hO_resT _ S, AddEquiv.apply_symm_apply,
      OrthDec.resT_apply]
    have hg := (LinkGram.link_gram D ρ B B'.L B'.ζ B'.line l).1
    have h0 : ∀ u : WO S B'.A, hO S B'.A u 0 = 0 := fun u => by
      rw [hO_eq_trace, adj_zero, Matrix.zero_mul, Matrix.mul_zero, Matrix.trace_zero]
    have h1 := GlobalTheory.LinkKappa.hO_ofAdj B.L B'.L S l.τ _ hg (rat τi * starAdj B.L S Y)
      (B'.o.pB * p.up FS F₀' t)
    rw [Int.cast_one, map_one, one_mul] at h1
    change hO B.L S (l.κ S _) _ = _ at h1
    rw [hκ] at h1
    have h2 := congrArg p.π (xi_mul_hO B.L S Y (rat l.τ * (B'.o.pB * p.up FS F₀' t)))
    rw [h1, map_mul] at h2
    have h3 : p.π (rat l.τ * (B'.o.pB * p.up FS F₀' t) * Y).trace = p.xi * -(t (Sum.inr ()) ⬝ᵥ y₀) := by
      have e1 : rat l.τ * (B'.o.pB * p.up FS F₀' t)
          = (l.τ.map p.pr * (B'.o.qB.map p.pr * (F₀'.β * t * FS.γ))).map p.ι := by
        rw [← BoxModel.rat_mul_ι, ← BoxModel.rat_mul_ι]; rfl
      have e2 : Y = (FS.β * M * F₀.γ * B.o.iB.map p.pr).map p.ι := by
        rw [← ι_mul_rat]; rfl
      have e3 : ∀ {a b : ℕ} (N : Matrix (Fin a) (Fin b) k), (N.map p.ι).map p.π = N := fun N => by
        ext i j; exact p.π_ι _
      rw [AddMonoidHom.map_trace p.π, Matrix.map_mul, e1, e2, e3, e3, ← Matrix.mul_assoc _ _ (B.o.iB.map p.pr),
        Matrix.trace_mul_comm]
      have e4 : B.o.iB.map p.pr * (l.τ.map p.pr * (B'.o.qB.map p.pr * (F₀'.β * t * FS.γ)) * (FS.β * M * F₀.γ))
          = (B.o.iB.map p.pr * (l.τ.map p.pr * (B'.o.qB.map p.pr * F₀'.β))) * (t * (FS.γ * FS.β) * M) * F₀.γ := by
        simp only [Matrix.mul_assoc]
      rw [e4, link_frames p B B' l s FA F₀ FA' F₀' h h', FS.γβ, Matrix.mul_one, Matrix.trace_mul_comm,
        ← Matrix.mul_assoc F₀.γ, ← Matrix.mul_assoc F₀.γ F₀.β, F₀.γβ, Matrix.one_mul, Matrix.trace_single_mul]
      simp [hM, Matrix.mul_apply, dotProduct]
    rw [h3] at h2
    rw [h0, zero_add, mul_left_cancel₀ hxi h2]

end GlobalTheory.ContrFrameCol
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLineColumnTranslationHeisenbergStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.splitPlace_lineColumn_translation_heisenberg : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (ψk : AddChar k Circle), p.IsChar ψ ψk → ∀ (ρ σ : ℕ) (B : BesLev D ρ) (B' : BesLev D σ) (l : Link B B'.L B'.ζ) (S : HSp D) (s : k), s ≠ 0 → ∀ (n n' n'' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype n''] [DecidableEq n''] (FA : Frame k B.A.rank n') (F₀ : Frame k B.V₀.rank (n' ⊕ Unit)) (FS : Frame k S.rank n) (FA' : Frame k B'.A.rank n'') (F₀' : Frame k B'.V₀.rank (n'' ⊕ Unit)), p.IsCoreFrame B s FA F₀ → p.IsCoreFrame B' (s * p.xi) FA' F₀' → ∀ y₀ : n → k, ∃ x : WO S B'.L, p.up F₀ FS (fromCols 0 (Matrix.of fun r _ => y₀ r)) = (B.o.resS S).symm (0, l.κ S x) ∧ IsHalf (cA D p.e) ((B'.o.resT S).symm (0, x)) ∧ ∀ t : Matrix (n'' ⊕ Unit) n k, ψ (symplO S B'.V₀ (p.up FS F₀' t) ((B'.o.resT S).symm (0, x))) = ((ψk (-(t (Sum.inr ()) ⬝ᵥ y₀)) : Circle) : ℂ) := by
  first | exact @GlobalTheory.ContrFrameCol.frame_col | exact GlobalTheory.ContrFrameCol.frame_col | (intros; apply GlobalTheory.ContrFrameCol.frame_col <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LineContractionSplitPlaceLocalModel

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ContrLocProof
open GlobalTheory.ContractionLocal

theorem contrLoc : ∀ (D : D7), GlobalTheory.LocFlat.ContrFactor → ContrLoc D := by
  have hH := GlobalTheory.T.besselLineContraction_heisenberg_invariant
  have hC := GlobalTheory.T.lineRow_translation_heisenberg_splitPlace
  have hD := GlobalTheory.T.splitPlace_lineColumn_translation_heisenberg
  have hL := GlobalTheory.T.besselLine_contraction_thetaFunction_isLocalModel
  have hR := GlobalTheory.T.thetaContraction_isLocalModel_secondVariable
  intro D hCF k _ _ _ _ _ _ p ν hν ψ hψ ψk hk ρ σ B B' l S vL s hs n n' n'' _ _ _ _ _ _ FA F₀ FS FA' F₀' hF hF' T₁ T₂ hT₁ hT₂
  obtain ⟨-, hψk, -, -, -⟩ := GlobalTheory.T.weilCharacter_splitPlace_exists_continuous_nontrivial D k p ψ hψ
  obtain ⟨hψkc, hψk1⟩ := hψk ψk hk
  let Bm := contrBil hψ l S vL T₁ T₂ hT₁.theta hT₂.theta
  have inv1 : ∀ (u₀ : n → k) Ψ₁ Ψ₁' Ψ₂ Ψ₂',
      (∀ x, Ψ₁'.1 x = (ψk (-(u₀ ⬝ᵥ fun r => x r (Sum.inr ()))) : ℂ) * Ψ₁.1 x) →
      (∀ x, Ψ₂'.1 x = Ψ₂.1 (x + fromRows 0 (Matrix.of fun _ => u₀))) → Bm Ψ₁' Ψ₂' = Bm Ψ₁ Ψ₂ := by
    intro u₀ Ψ₁ Ψ₁' Ψ₂ Ψ₂' h1 h2
    obtain ⟨x, hx1, hx2, hx3⟩ := hC D k p ψ hψ ψk hk ρ σ B B' l S s hs n n' n'' FA F₀ FS FA' F₀' hF hF' u₀
    have e1 : T₁ Ψ₁' = heisO ψ B.V₀ S ((B.o.resS S).symm (0, l.κ S x)) (T₁ Ψ₁) :=
      hT₁.modul _ hx2 Ψ₁ Ψ₁' fun t => by rw [h1, hx3]
    have e2 : T₂ Ψ₂' = heisO ψ S B'.V₀ ((B'.o.resT S).symm (0, x)) (T₂ Ψ₂) := by
      rw [← hx1]; exact hT₂.trans _ Ψ₂ Ψ₂' h2
    simp only [Bm, contrBil_apply, e1, e2]
    exact hH D ψ hψ ρ σ B B' l S vL _ _ (hT₁.theta Ψ₁) (hT₂.theta Ψ₂) x
  have inv2 : ∀ (y₀ : n → k) Ψ₁ Ψ₁' Ψ₂ Ψ₂',
      (∀ x, Ψ₁'.1 x = Ψ₁.1 (x + fromCols 0 (Matrix.of fun r _ => y₀ r))) →
      (∀ x, Ψ₂'.1 x = (ψk (-(x (Sum.inr ()) ⬝ᵥ y₀)) : ℂ) * Ψ₂.1 x) → Bm Ψ₁' Ψ₂' = Bm Ψ₁ Ψ₂ := by
    intro y₀ Ψ₁ Ψ₁' Ψ₂ Ψ₂' h1 h2
    obtain ⟨x, hx1, hx2, hx3⟩ := hD D k p ψ hψ ψk hk ρ σ B B' l S s hs n n' n'' FA F₀ FS FA' F₀' hF hF' y₀
    have e1 : T₁ Ψ₁' = heisO ψ B.V₀ S ((B.o.resS S).symm (0, l.κ S x)) (T₁ Ψ₁) := by
      rw [← hx1]; exact hT₁.trans _ Ψ₁ Ψ₁' h1
    have e2 : T₂ Ψ₂' = heisO ψ S B'.V₀ ((B'.o.resT S).symm (0, x)) (T₂ Ψ₂) :=
      hT₂.modul _ hx2 Ψ₂ Ψ₂' fun t => by rw [h2, hx3]
    simp only [Bm, contrBil_apply, e1, e2]
    exact hH D ψ hψ ρ σ B B' l S vL _ _ (hT₁.theta Ψ₁) (hT₂.theta Ψ₂) x
  obtain ⟨Λ, hΛ⟩ := hCF k ψk ν hψkc hψk1 hν n n' n'' (WO B.A S → WO S B'.A → ℂ) Bm inv1 inv2
  obtain ⟨φ₀, φ₀', hφ⟩ := exists_normPair ψk ν hψkc hν n
  have hval : ∀ Ξ₁ Ξ₂ (Ξ : SB (Matrix n n' k × Matrix n'' n k)), (∀ q, Ξ.1 q = Ξ₁.1 q.1 * Ξ₂.1 q.2) →
      Λ Ξ = Bm (colTens φ₀ Ξ₁) (rowTens φ₀' Ξ₂) := by
    intro Ξ₁ Ξ₂ Ξ hq
    obtain ⟨Ξ', hΞ'1, hΞ'2⟩ := hΛ (colTens φ₀ Ξ₁) (rowTens φ₀' Ξ₂)
    have : Ξ' = Ξ := Subtype.ext (funext fun q => by rw [hΞ'1, contr_tens, hφ, mul_one, hq])
    rw [← this, hΞ'2]
  refine ⟨Λ, ⟨fun Ξ₂ v => ?_, fun Ξ₁ u => ?_⟩, hΛ⟩
  · let T : SB (Matrix n n' k) →ₗ[ℂ] (WO B.A S → ℂ) :=
      { toFun := fun Ξ₁ u => Bm (colTens φ₀ Ξ₁) (rowTens φ₀' Ξ₂) u v
        map_add' := fun a b => by funext u; simp only [map_add (f := _), LinearMap.add_apply, Pi.add_apply]
        map_smul' := fun c a => by funext u; simp only [map_smul, LinearMap.smul_apply, Pi.smul_apply, RingHom.id_apply] }
    refine ⟨T, hL D k p ψ hψ ρ σ B B' l S vL s hs n n' FA F₀ FS hF T₁ hT₁ φ₀ _ (hT₂.theta _) v T fun Ξ₁ u => rfl,
      fun Ξ₁ Ξ hq u => ?_⟩
    rw [hval Ξ₁ Ξ₂ Ξ hq]; rfl
  · let T : SB (Matrix n'' n k) →ₗ[ℂ] (WO S B'.A → ℂ) :=
      { toFun := fun Ξ₂ v => Bm (colTens φ₀ Ξ₁) (rowTens φ₀' Ξ₂) u v
        map_add' := fun a b => by funext v; simp only [map_add (f := _), Pi.add_apply]
        map_smul' := fun c a => by funext v; simp only [map_smul, Pi.smul_apply, RingHom.id_apply] }
    refine ⟨T, hR D k p ψ hψ ρ σ B B' l S vL (s * p.xi) ?_ n n'' FS FA' F₀' hF' T₂ hT₂ φ₀' _ (hT₁.theta _) u T
      fun Ξ₂ v => rfl, fun Ξ₂ Ξ hq v => ?_⟩
    · obtain ⟨-, -, hxi, -, -⟩ := GlobalTheory.T.weilCharacter_splitPlace_exists_continuous_nontrivial D k p ψ hψ
      exact mul_ne_zero hs hxi
    rw [hval Ξ₁ Ξ₂ Ξ hq]; rfl
end GlobalTheory.ContrLocProof

end
end
end
