module

public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CoP
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LowerTieTwAt
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsLevelPrimePointModelRealisation
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HeightsranchOne
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LocalBasisRepLatticeIntegralCoordsSpecStatement
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SplitLastBlockActX
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StatementWithTransposeOfBranching
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TilLatticesOfLevel
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.InvTrKEmbGLApply
import Mathlib.Algebra.Order.Star.Int

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RhoVrBrAtEqBrStd

section

@[expose] public section

noncomputable section

namespace GlobalTheory.BranchBlock

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2 Matrix

theorem isBlock_of_mulVec' {E : Type} [Field E] {N n : ℕ} (hN : N = n + 1) {A' : Matrix (Fin N) (Fin N) E}
    {A : Matrix (Fin n) (Fin n) E} {c : E} (h1 : ∀ x, iniH hN (A' *ᵥ x) = A *ᵥ iniH hN x)
    (h2 : ∀ x, (A' *ᵥ x) (Br.iL hN) = c * x (Br.iL hN)) : BranchFormula.IsBlock hN A' A c := by
  have hne : ∀ a : Fin n, Br.iC hN a ≠ Br.iL hN := fun a h => absurd (congrArg Fin.val h) a.2.ne
  refine ⟨fun a b => ?_, fun a => ⟨?_, ?_⟩, ?_⟩
  · have h := congrFun (h1 (Pi.single (Br.iC hN b) 1)) a
    have e : iniH hN (Pi.single (Br.iC hN b) (1 : E)) = Pi.single b 1 := funext fun i => by
      simp only [iniH, Pi.single_apply, (Br.iC_inj hN).eq_iff]
    rw [e, mulVec_single_one, mulVec_single_one] at h
    exact h
  · have h := congrFun (h1 (Pi.single (Br.iL hN) 1)) a
    have e : iniH hN (Pi.single (Br.iL hN) (1 : E)) = 0 := funext fun i => Pi.single_eq_of_ne (hne i) _
    rw [e, mulVec_single_one, mulVec_zero] at h
    exact h
  · have h := h2 (Pi.single (Br.iC hN a) 1)
    rw [mulVec_single_one, Pi.single_eq_of_ne (hne a).symm, mul_zero] at h
    exact h
  · have h := h2 (Pi.single (Br.iL hN) 1)
    rw [mulVec_single_one, Pi.single_eq_same, mul_one] at h
    exact h

theorem rhoVr_brAt_eq_brStd : ∀ {E K ι : Type} [Field E] [Field K] [CharZero K] [Fintype ι] (emb : ι → E →+* K) {N n : ℕ}
    (hN : N = n + 1) (lam : ι → DomWeight N) (sg : ι → DomWeight n), (∀ τ, Br.Interlace hN (lam τ) (sg τ)) →
    (∀ τ, Br.SameShift (lam τ) (sg τ)) → ∀ (t : E) (B' : GL (Fin n) E) (B : GL (Fin N) E),
    (∀ x, iniH hN ((B : Matrix (Fin N) (Fin N) E) *ᵥ x) = (B' : Matrix (Fin n) (Fin n) E) *ᵥ iniH hN x) →
    (∀ x, t * ((B : Matrix (Fin N) (Fin N) E) *ᵥ x) (Br.iL hN) = x (Br.iL hN)) →
    ∀ G : Formalism.L2.DIV.VV K lam, rhoVr emb sg B'⁻¹ (Br.brAt hN lam sg (fun τ => emb τ t) G) =
      Br.brStd hN lam sg (rhoVr emb lam B⁻¹ G) := by
  intro E K ι _ _ _ _ emb N n hN lam sg hI hS t B' B h1 h2 G
  have ht : t ≠ 0 := by
    intro h0
    have h := h2 (Pi.single (Br.iL hN) 1)
    rw [h0, zero_mul, Pi.single_eq_same] at h
    exact zero_ne_one h
  have hBA : ∀ x, (B : Matrix (Fin N) (Fin N) E) *ᵥ (((B⁻¹ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) *ᵥ x) = x := by
    intro x
    rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
  have hAB : ∀ y, ((B'⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ ((B' : Matrix (Fin n) (Fin n) E) *ᵥ y) = y := by
    intro y
    rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
  have hblk : BranchFormula.IsBlock hN ((B⁻¹ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E)
      ((B'⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) t := by
    refine isBlock_of_mulVec' hN (fun x => ?_) (fun x => ?_)
    · have h := h1 (((B⁻¹ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) *ᵥ x)
      rw [hBA] at h
      rw [h, hAB]
    · have h := h2 (((B⁻¹ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) *ᵥ x)
      rw [hBA] at h
      exact h.symm
  have e1 : ∀ {m : ℕ} (g : GL (Fin m) E) (τ : ι) (a b : Fin m),
      ((invTrK (embGL emb g) τ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) a b =
        emb τ (((g⁻¹ : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) b a) := fun g τ a b => rfl
  have key := BranchFormula.brAt_eq_pullback hN hI hS (invTrK (embGL emb B')) (invTrK (embGL emb B))
    (fun τ => emb τ t) (fun τ => (map_ne_zero _).2 ht) (fun τ => by
      refine ⟨fun a b => ?_, fun a => ⟨?_, ?_⟩, ?_⟩ <;> simp only [e1]
      · rw [hblk.1]
      · rw [(hblk.2.1 a).2, map_zero]
      · rw [(hblk.2.1 a).1, map_zero]
      · rw [hblk.2.2]) G
  show rhoK sg (invTrK (embGL emb B'⁻¹)) _ = Br.brStd hN lam sg (rhoK lam (invTrK (embGL emb B⁻¹)) G)
  rw [map_inv (embGL emb), map_inv (embGL emb), map_inv invTrK, map_inv invTrK]
  exact key.symm

end GlobalTheory.BranchBlock
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TrueWeightsEqDescentShiftedWeightsInterlace

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PerQ

theorem trueWeights_built : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (τ : B.fields.Tau), Formalism.MainNotions.product_first_zeroth_parts.lamTr (I.rec7 l Z) u τ = GlobalTheory.Mem.Col2.lamT (B.hcW u) B.R.m τ ∧ Formalism.MainNotions.product_first_zeroth_parts.sgTr (I.rec7 l Z) u τ = (I.perIn u a).sgT τ ∧ Br.Interlace (N_m_succ B.R) (GlobalTheory.Mem.Col2.lamT (B.hcW u) B.R.m τ) ((I.perIn u a).sgT τ) ∧ Br.SameShift (GlobalTheory.Mem.Col2.lamT (B.hcW u) B.R.m τ) ((I.perIn u a).sgT τ) ∧ ((I.rec7 l Z).fm u).SgInterlace := by
  intro B X I _ l Z u a τ
  have hc : Formalism.MainNotions.product_first_zeroth_parts.cTw B.R = (B.R.m : ℤ) * (((B.R.t + 1) / 2 : ℕ) : ℤ) := by
    have h2 : 2 ∣ B.R.t + 1 := B.R.t_odd.add_one.two_dvd
    unfold Formalism.MainNotions.product_first_zeroth_parts.cTw
    rw [Nat.mul_div_assoc _ h2]
    push_cast; rfl
  have key : ∀ {n : ℕ} (w : DomWeight n), Formalism.MainNotions.product_first_zeroth_parts.wSh w (Formalism.MainNotions.product_first_zeroth_parts.cTw B.R) =
      GlobalTheory.Mem.Col2.shW w (-((B.R.m : ℤ) * (((B.R.t + 1) / 2 : ℕ) : ℤ))) := by
    intro n w
    unfold Formalism.MainNotions.product_first_zeroth_parts.wSh GlobalTheory.Mem.Col2.shW
    congr 1
    funext i
    rw [hc]; ring
  have hs : ∀ τ, (I.perIn u a).sg τ = (RowPar.of (B.hcW u τ)).sg := fun τ =>
    congrArg RowPar.sg (B.wts_isOk.hc_row u τ).symm
  have hw := GlobalTheory.LvT.BuiltChain.weights_ok (I.perIn u a) (B.hcW u) B.fields.emb hs
  refine ⟨key _, key _, (hw τ).1, (hw τ).2, fun τ' i => ?_⟩
  obtain ⟨ha, hb⟩ := (hw τ').1 i
  simp only [Br.aBr, Br.bBr, Br.iS, Br.iC, PerIn.sgT, GlobalTheory.Mem.Col2.lamT, GlobalTheory.Mem.Col2.shW] at ha hb
  constructor
  · show (B.wts.sgW τ').w i ≤ (Examples₂.lamOf (B.hcW u τ') B.R.m).w ⟨i.1, _⟩
    change 0 ≤ (Examples₂.lamOf (B.hcW u τ') B.R.m).w ⟨i.1, _⟩ + _ - ((B.wts.sgW τ').w i + _) at hb
    linarith
  · show (Examples₂.lamOf (B.hcW u τ') B.R.m).w ⟨i.1 + 1, _⟩ ≤ (B.wts.sgW τ').w i
    change 0 ≤ (B.wts.sgW τ').w i + _ - ((Examples₂.lamOf (B.hcW u τ') B.R.m).w ⟨i.1 + 1, _⟩ + _) at ha
    linarith

end GlobalTheory.PerQ
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TrueWeightsEqDescentShiftedWeightsInterlaceStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.trueWeights_eq_descentShiftedWeights_interlace : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (τ : B.fields.Tau), Formalism.MainNotions.product_first_zeroth_parts.lamTr (I.rec7 l Z) u τ = GlobalTheory.Mem.Col2.lamT (B.hcW u) B.R.m τ ∧ Formalism.MainNotions.product_first_zeroth_parts.sgTr (I.rec7 l Z) u τ = (I.perIn u a).sgT τ ∧ Br.Interlace (N_m_succ B.R) (GlobalTheory.Mem.Col2.lamT (B.hcW u) B.R.m τ) ((I.perIn u a).sgT τ) ∧ Br.SameShift (GlobalTheory.Mem.Col2.lamT (B.hcW u) B.R.m τ) ((I.perIn u a).sgT τ) ∧ ((I.rec7 l Z).fm u).SgInterlace := by
  exact @GlobalTheory.PerQ.trueWeights_built
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LocalCoordsEvaluationLowerRowMapEqTensorBranchin

section

@[expose] public section

noncomputable section

namespace GlobalTheory.PerQ.Co

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr
  GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix

attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem coP_PtT_eq_blk : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (l0 : I.Law0 l) (u : B.Word) (a : I.ι) (w : B.places.Pl), ∀ φ ∈ ((I.tw l l0 Z).fm u a).Fi (I.rec7 l Z).R.m, ∀ c, GlobalTheory.PerQ.Co.coP I u a w (GlobalTheory.PerQ.PtT (I.rec7 l Z) u a φ) c = Formalism.MainNotions.product_first_zeroth_parts.blk (fun τ => brOne ℂ (Formalism.MainNotions.product_first_zeroth_parts.Nm_succ (I.rec7 l Z).R).symm (Formalism.MainNotions.product_first_zeroth_parts.lamTr (I.rec7 l Z) u τ) (Formalism.MainNotions.product_first_zeroth_parts.sgTr (I.rec7 l Z) u τ)) (GlobalTheory.PerQ.Co.coM I u a w c (φ (((I.tw l l0 Z).fm u a).til c))) := by
  intro B X I hI l Z l0 u a w φ hφ c
  have hV : φ ((I.perIn u a).tilC c) ∈ ValC (Gr B.fields.emb B.embLL (B.R.N B.R.m)) (lamT (B.hcW u) B.R.m) := (hφ _).1
  have hT : ((I.stp u a B.R.m).trTo B.fields.emb B.embLL (I.perIn u a).b0 ((I.perIn u a).tilPt c)) (φ ((I.perIn u a).tilC c)) ∈
      ValC (Gr B.fields.emb B.embLL (B.R.N B.R.m)) (lamT (B.hcW u) B.R.m) :=
    GlobalTheory.LvT.Built.RealM.trFr_mem _ _ _ _ _ hV
  obtain ⟨F, hF⟩ := (GlobalTheory.TilClass.mem_ValC_iff _ _ _ _).1 hT
  have hW := fun τ => GlobalTheory.T.trueWeights_eq_descentShiftedWeights_interlace I hI l Z u a τ
  have hS := GlobalTheory.T.localBasisRepLattice_integralCoords_spec I hI l u a w c
  show actP (I.perIn u a).sgT (invTrK ((embGL (embAt B.embLL B.fields.emb)) (GlobalTheory.PerQ.Co.bP I u a w c)⁻¹))
      (polOf (Gr B.fields.emb B.embLL (B.R.N B.R.m - 1)) (shiftOf (I.perIn u a).sgT) (fr0 B.fields.emb B.embLL (B.R.N B.R.m - 1))
        (fnOf (Gr B.fields.emb B.embLL (B.R.N B.R.m - 1)) (shiftOf (I.perIn u a).sgT) 1
          ((I.perIn u a).br B.fields.emb B.embLL (B.hcW u)
            (polOf (Gr B.fields.emb B.embLL (B.R.N B.R.m)) (shiftOf (lamT (B.hcW u) B.R.m)) (fr0 B.fields.emb B.embLL (B.R.N B.R.m))
              (((I.stp u a B.R.m).trTo B.fields.emb B.embLL (I.perIn u a).b0 ((I.perIn u a).tilPt c)) (φ ((I.perIn u a).tilC c))))))) =
    Formalism.MainNotions.product_first_zeroth_parts.blk (fun τ => brOne ℂ (Formalism.MainNotions.product_first_zeroth_parts.Nm_succ B.R).symm (Formalism.MainNotions.product_first_zeroth_parts.lamTr (I.rec7 l Z) u τ) (Formalism.MainNotions.product_first_zeroth_parts.sgTr (I.rec7 l Z) u τ))
      (actP (lamT (B.hcW u) B.R.m) (invTrK ((embGL (embAt B.embLL B.fields.emb)) (GlobalTheory.PerQ.Co.bM I u a w c)⁻¹))
        (polOf (Gr B.fields.emb B.embLL (B.R.N B.R.m)) (shiftOf (lamT (B.hcW u) B.R.m)) (fr0 B.fields.emb B.embLL (B.R.N B.R.m))
          (((I.stp u a B.R.m).trTo B.fields.emb B.embLL (I.perIn u a).b0 ((I.perIn u a).tilPt c)) (φ ((I.perIn u a).tilC c)))))

  rw [← hF, GlobalTheory.TilClass.polOf_fnOf_one, GlobalTheory.TilClass.polOf_fnOf_one]
  have hlam : Formalism.MainNotions.product_first_zeroth_parts.lamTr (I.rec7 l Z) u = lamT (B.hcW u) B.R.m := funext fun τ => (hW τ).1
  have hsg : Formalism.MainNotions.product_first_zeroth_parts.sgTr (I.rec7 l Z) u = (I.perIn u a).sgT := funext fun τ => (hW τ).2.1
  refine Eq.trans ?_ (GlobalTheory.Proof.FockBlockMonotone.blk_brOne_eq (ι := B.fields.Tau) (Formalism.MainNotions.product_first_zeroth_parts.Nm_succ B.R).symm _ _ _).symm
  rw [hlam, hsg]
  have key := GlobalTheory.BranchBlock.rhoVr_brAt_eq_brStd (embAt B.embLL B.fields.emb) (N_m_succ B.R) (lamT (B.hcW u) B.R.m)
    (I.perIn u a).sgT (fun τ => (hW τ).2.2.1) (fun τ => (hW τ).2.2.2.1) (I.perIn u a).tz _ _ hS.2.1 hS.2.2.1 F
  exact congrArg Subtype.val key

end GlobalTheory.PerQ.Co

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LocalCoordsEvaluationLowerRowMapEqTensorBranchinStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.localCoords_evaluationLowerRowMap_eq_tensor_branching : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (l0 : I.Law0 l) (u : B.Word) (a : I.ι) (w : B.places.Pl), ∀ φ ∈ ((I.tw l l0 Z).fm u a).Fi (I.rec7 l Z).R.m, ∀ c, GlobalTheory.PerQ.Co.coP I u a w (GlobalTheory.PerQ.PtT (I.rec7 l Z) u a φ) c = Formalism.MainNotions.product_first_zeroth_parts.blk (fun τ => brOne ℂ (Formalism.MainNotions.product_first_zeroth_parts.Nm_succ (I.rec7 l Z).R).symm (Formalism.MainNotions.product_first_zeroth_parts.lamTr (I.rec7 l Z) u τ) (Formalism.MainNotions.product_first_zeroth_parts.sgTr (I.rec7 l Z) u τ)) (GlobalTheory.PerQ.Co.coM I u a w c (φ (((I.tw l l0 Z).fm u a).til c))) := by
  first | exact @GlobalTheory.PerQ.Co.coP_PtT_eq_blk | exact GlobalTheory.PerQ.Co.coP_PtT_eq_blk | (intros; apply GlobalTheory.PerQ.Co.coP_PtT_eq_blk <;> assumption)
end
end
