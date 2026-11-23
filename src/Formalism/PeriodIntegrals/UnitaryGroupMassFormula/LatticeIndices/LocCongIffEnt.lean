module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.SecondCoordsSub
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.GlRedEqOneIff
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.GOfPrime
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.ImAInModPSplit
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.CongSpanSingleIff
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
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.SecondCoordsMulVec
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.Imports

section

@[expose] public section

noncomputable section

namespace MassDataIdxFrA

open Matrix

variable {F k : Type} [Field F] [Field k] (O : ValuationSubring F) (π : O →+* k) (γ : O)
  {ι : Type} [Fintype ι] [DecidableEq ι]

theorem clause_iff (hker : RingHom.ker π = Ideal.span {γ}) (Y : Matrix ι ι O) {β : Type} (u : β → ι → F)
    (pos : β → ι) (hu : ∀ b, ∃ z, IntVec O z ∧ u b = Pi.single (pos b) 1 + (γ : F) • z) (s : Set β)
    (w : ι → F) (j : ι) (hw : ∃ z, IntVec O z ∧ w = Pi.single j 1 + (γ : F) • z) :
    CongSpan O γ (u '' s) ((Y.map ((↑) : O → F) - 1) *ᵥ w) ↔
      ∀ i, i ∉ pos '' s → π (Y i j) = if i = j then 1 else 0 := by
  classical
  have hdiv : ∀ a : O, π a = 0 ↔ ∃ c : O, a = γ * c := by
    intro a
    rw [← RingHom.mem_ker, hker, Ideal.mem_span_singleton']
    constructor
    · rintro ⟨c, hc⟩
      exact ⟨c, by rw [← hc, mul_comm]⟩
    · rintro ⟨c, hc⟩
      exact ⟨c, by rw [hc, mul_comm]⟩
  have hsm : ∀ (a : O) (x : ι → F), a • x = (a : F) • x := fun a x => rfl
  obtain ⟨z, hz, rfl⟩ := hw
  set Y' := Y.map ((↑) : O → F) with hY'
  let cO : ι → O := fun i => Y i j - (if i = j then 1 else 0)
  have hcO : ∀ i, (cO i : F) = (Y i j : F) - (if i = j then 1 else 0) := by
    intro i
    by_cases hij : i = j <;> simp [cO, hij]
  have hcol : (Y' - 1) *ᵥ Pi.single j (1 : F) = ∑ i, (cO i : F) • Pi.single i (1 : F) := by
    ext i
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, if_true, hcO]
    simp [Matrix.mulVec, dotProduct, Pi.single_apply, hY', Matrix.one_apply]
  have hint : ∀ i, ((Y' - 1) *ᵥ z) i ∈ O := by
    intro i
    simp only [Matrix.mulVec, dotProduct, Matrix.sub_apply, Matrix.one_apply, hY', Matrix.map_apply]
    refine _root_.sum_mem fun l _ => mul_mem (sub_mem (Y i l).2 ?_) (hz l)
    split_ifs
    · exact one_mem O
    · exact zero_mem O
  have hentry : ∀ i, ((Y' - 1) *ᵥ (Pi.single j 1 + (γ : F) • z)) i =
      (cO i : F) + (γ : F) * ((Y' - 1) *ᵥ z) i := by
    intro i
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hcol,
      Finset.sum_apply]
    simp [Pi.single_apply]
  constructor
  · rintro ⟨W, hW, z', hz', hv⟩ i hi
    have key : ∀ v ∈ Submodule.span O (u '' s), ∃ c : O, v i = (γ : F) * c := by
      intro v hv
      induction hv using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨b, hb, rfl⟩ := hx
        obtain ⟨zb, hzb, hub⟩ := hu b
        refine ⟨⟨zb i, hzb i⟩, ?_⟩
        have hne : i ≠ pos b := fun h => hi ⟨b, hb, h.symm⟩
        simp [hub, Pi.single_apply, hne]
      | zero => exact ⟨0, by simp⟩
      | add x y _ _ hx hy =>
        obtain ⟨c1, h1⟩ := hx
        obtain ⟨c2, h2⟩ := hy
        exact ⟨c1 + c2, by rw [Pi.add_apply, h1, h2]; push_cast; ring⟩
      | smul a x _ hx =>
        obtain ⟨c, h⟩ := hx
        refine ⟨a * c, ?_⟩
        rw [hsm, Pi.smul_apply, smul_eq_mul, h]
        push_cast
        ring
    obtain ⟨c, hc⟩ := key W hW
    have hvi := congrFun hv i
    rw [hentry i, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hc] at hvi
    have hO : cO i = γ * ⟨(c : F) + z' i - ((Y' - 1) *ᵥ z) i,
        sub_mem (add_mem c.2 (hz' i)) (hint i)⟩ := by
      apply Subtype.ext
      show (cO i : F) = (γ : F) * ((c : F) + z' i - ((Y' - 1) *ᵥ z) i)
      linear_combination hvi
    have h0 := (hdiv _).2 ⟨_, hO⟩
    simp only [cO, map_sub, sub_eq_zero] at h0
    rw [h0]
    split_ifs <;> simp
  · intro hcond
    have hsel : ∀ i, i ∈ pos '' s → ∃ b, b ∈ s ∧ pos b = i := fun i hi => hi
    choose bsel hbs hpos using hsel
    have hout : ∀ i, i ∉ pos '' s → ∃ e : O, cO i = γ * e := by
      intro i hi
      apply (hdiv _).1
      simp only [cO, map_sub, hcond i hi]
      split_ifs <;> simp
    choose dsel hdsel using hout
    choose zb hzb hub using hu
    refine ⟨∑ i, (if h : i ∈ pos '' s then cO i • u (bsel i h) else 0), ?_,
      ∑ i, ((if h : i ∈ pos '' s then 0 else (dsel i h : F) • Pi.single i (1 : F)) -
        (if h : i ∈ pos '' s then (cO i : F) • zb (bsel i h) else 0)) + (Y' - 1) *ᵥ z, ?_, ?_⟩
    · refine _root_.sum_mem fun i _ => ?_
      split_ifs with h
      · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨bsel i h, hbs i h, rfl⟩)
      · exact Submodule.zero_mem _
    · intro l
      rw [Pi.add_apply, Finset.sum_apply]
      refine add_mem (_root_.sum_mem fun i _ => ?_) (hint l)
      rw [Pi.sub_apply]
      refine sub_mem ?_ ?_
      · split_ifs with h
        · exact zero_mem O
        · rw [Pi.smul_apply, smul_eq_mul]
          exact mul_mem (dsel i h).2 (by rw [Pi.single_apply]; split_ifs; exacts [one_mem O, zero_mem O])
      · split_ifs with h
        · rw [Pi.smul_apply, smul_eq_mul]
          exact mul_mem (cO i).2 (hzb _ l)
        · exact zero_mem O
    · rw [Matrix.mulVec_add, Matrix.mulVec_smul, hcol, smul_add, Finset.smul_sum, ← add_assoc,
        ← Finset.sum_add_distrib]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases h : i ∈ pos '' s
      · simp only [h, dif_pos, hsm, hub, hpos i h, sub_zero, zero_sub, smul_add, smul_neg, smul_smul]
        rw [mul_comm]
        abel
      · simp only [h, dif_neg, not_false_eq_true, sub_zero, zero_add, smul_smul]
        rw [hdsel i h]
        push_cast
        rfl

end MassDataIdxFrA
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.LocCongIffEnt

section

@[expose] public section

noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge MassDataIdxStIm MassDataIdxRed MassDataIdxSpl Matrix
  MassDataIdxFrA
open scoped TensorProduct

section Loc

variable {D : D7} (X : HidaSetting D) (p : TypX X) (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p)
  (Q : GL (IdxD D) (FpX X p))

theorem locCong_iff_ent (hθ : IsSplitEquiv X p θ) (π : Op X p →+* ZMod (gOf p))
    (hker : RingHom.ker π = Ideal.span {((gOf p : ℕ) : Op X p)}) (hS : SplitA X p θ Q) (hA : AdaptA X p θ Q)
    (x : HAp X p) (Y : GL (IdxD D) (Op X p))
    (hY : ((glRed (algebraMap (Op X p) (FpX X p)) Y : GL (IdxD D) (FpX X p)) :
        Matrix (IdxD D) (IdxD D) (FpX X p)) =
      ((Q⁻¹ : GL (IdxD D) (FpX X p)) : Matrix (IdxD D) (IdxD D) (FpX X p)) *
        Matrix.reindex (idxEquiv X) (idxEquiv X) (cmp1 X.B.I.cm.sig X.B.I.J θ x) *
        (Q : Matrix (IdxD D) (IdxD D) (FpX X p))) :
    LocCong X p x ↔ EntA X p π Y := by
  have : Fact (gOf p).Prime := ⟨gOf_prime X p⟩
  obtain ⟨hE1, hZ1, hB1, hE2, hZ2, hB2⟩ := hA
  set O := OvA X p
  set M := ((HA.mat (FpX X p) X.B.I.cm.sig X.B.I.J x : GL (Fin X.B.I.n) (TpX X p)) :
    Matrix (Fin X.B.I.n) (Fin X.B.I.n) (TpX X p))
  set Ym := (Y : Matrix (IdxD D) (IdxD D) (Op X p))
  set Yi := ((Y⁻¹ : GL (IdxD D) (Op X p)) : Matrix (IdxD D) (IdxD D) (Op X p))
  have hYm : ((Q⁻¹ : GL (IdxD D) (FpX X p)) : Matrix (IdxD D) (IdxD D) (FpX X p)) *
      Matrix.reindex (idxEquiv X) (idxEquiv X) (M.map fun t => (θ t).1) *
      (Q : Matrix (IdxD D) (IdxD D) (FpX X p)) = Ym.map ((↑) : O → FpX X p) := hY.symm
  have hZ : Yi.map ((↑) : O → FpX X p) * (((Q⁻¹ : GL (IdxD D) (FpX X p)) : Matrix (IdxD D) (IdxD D) (FpX X p)) *
      Matrix.reindex (idxEquiv X) (idxEquiv X) (cmp1 X.B.I.cm.sig X.B.I.J θ x) *
      (Q : Matrix (IdxD D) (IdxD D) (FpX X p))) = 1 := by
    rw [← hY]
    have h1 : Yi * Ym = 1 := by
      simp only [Yi, Ym]; rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have h2 := congrArg (fun A => A.map (algebraMap (Op X p) (FpX X p))) h1
    simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at h2
    exact h2
  have c1 : ∀ u, crd1 X p θ Q ((M - 1) *ᵥ u) = (Ym.map ((↑) : O → FpX X p) - 1) *ᵥ crd1 X p θ Q u := by
    intro u
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, firstCoords_sub, firstCoords_mulVec, hYm, Matrix.sub_mulVec, Matrix.one_mulVec]
  have c2 : ∀ u, crd2 X p θ Q ((M - 1) *ᵥ u) = (Yiᵀ.map ((↑) : O → FpX X p) - 1) *ᵥ crd2 X p θ Q u := by
    intro u
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, secondCoords_sub, secondCoords_mulVec X p θ Q hθ x _ hZ, Matrix.sub_mulVec,
      Matrix.one_mulVec, Matrix.transpose_map]

  have hsplit : ∀ S y, InModP X p X.B.g S y ↔ CongSpan O (gA X p) (crd1 X p θ Q '' S) (crd1 X p θ Q y) ∧
      CongSpan O (gA X p) (crd2 X p θ Q '' S) (crd2 X p θ Q y) := fun S y => (imA_inModP_Bg X p S y).trans (hS S y)

  have ce : ∀ a : Fin D.R.rS, InModP X p X.B.g ((fun b => PI.FinKW.vecV X.B.I p.1 (X.e0 b)) '' {b | b.1 < a.1})
      ((M - 1) *ᵥ PI.FinKW.vecV X.B.I p.1 (X.e0 a)) ↔
      (∀ i, i ∉ (Sum.inl '' {b : Fin D.R.rS | b.1 < a.1} : Set (IdxD D)) →
        π (Ym i (Sum.inl a)) = if i = Sum.inl a then 1 else 0) ∧
      (∀ i, i ∉ (fposA (D := D) '' {b : Fin D.R.rS | b.1 < a.1}) →
        π (Yi (fposA a) i) = if i = fposA a then 1 else 0) := by
    intro a
    rw [hsplit, Set.image_image, Set.image_image, c1, c2]
    refine and_congr ?_ ?_
    · exact clause_iff O π (gA X p) hker Ym _ (fun b => (Sum.inl b : IdxD D)) (fun b => hE1 b) _ _ _ (hE1 a)
    · have := clause_iff O π (gA X p) hker Yiᵀ _ (fposA (D := D)) (fun b => hE2 b) {b : Fin D.R.rS | b.1 < a.1}
        _ (fposA a) (hE2 a)
      simpa only [Matrix.transpose_apply] using this

  have cz : InModP X p X.B.g (Set.range fun b => PI.FinKW.vecV X.B.I p.1 (X.e0 b))
      ((M - 1) *ᵥ PI.FinKW.vecV X.B.I p.1 X.z0) ↔
      (∀ i, i ∉ (Sum.inl '' Set.univ : Set (IdxD D)) → π (Ym i zI) = if i = zI then 1 else 0) ∧
      (∀ i, i ∉ (fposA (D := D) '' Set.univ) → π (Yi zI i) = if i = zI then 1 else 0) := by
    rw [hsplit, ← Set.image_univ, Set.image_image, Set.image_image, c1, c2]
    refine and_congr ?_ ?_
    · exact clause_iff O π (gA X p) hker Ym _ (fun b => (Sum.inl b : IdxD D)) (fun b => hE1 b) _ _ _ hZ1
    · obtain ⟨z, hz, hz'⟩ := hZ2
      have hw : ∃ z', IntVec O z' ∧ -crd2 X p θ Q (PI.FinKW.vecV X.B.I p.1 X.z0) =
          Pi.single zI 1 + ((gA X p : O) : FpX X p) • z' :=
        ⟨-z, fun i => by simpa using neg_mem (hz i), by rw [hz', neg_add, neg_neg, smul_neg]⟩
      have hneg : (Yiᵀ.map ((↑) : O → FpX X p) - 1) *ᵥ crd2 X p θ Q (PI.FinKW.vecV X.B.I p.1 X.z0) =
          -((Yiᵀ.map ((↑) : O → FpX X p) - 1) *ᵥ -crd2 X p θ Q (PI.FinKW.vecV X.B.I p.1 X.z0)) := by
        rw [Matrix.mulVec_neg, neg_neg]
      rw [hneg, congSpan_neg]
      have := clause_iff O π (gA X p) hker Yiᵀ _ (fposA (D := D)) (fun b => hE2 b) Set.univ _ zI hw
      simpa only [Matrix.transpose_apply] using this

  have cw : ∀ j : Fin D.R.k, InModP X p X.B.g ((Set.range fun b => PI.FinKW.vecV X.B.I p.1 (X.e0 b)) ∪
      (fun j => PI.FinKW.vecV X.B.I p.1 (X.bw j)) '' {j' | j'.1 < j.1})
      ((M - 1) *ᵥ PI.FinKW.vecV X.B.I p.1 (X.bw j)) ↔
      (∀ i, i ∉ (posW (r := D.R.rS) j : Set (IdxD D)) → π (Ym i (wI j)) = if i = wI j then 1 else 0) := by
    intro j
    have h0 : crd2 X p θ Q ((M - 1) *ᵥ PI.FinKW.vecV X.B.I p.1 (X.bw j)) = 0 := by
      rw [c2]
      have : crd2 X p θ Q (PI.FinKW.vecV X.B.I p.1 (X.bw j)) = 0 := by
        unfold crd2; rw [hB2 j]
        have : ((0 : Fin X.B.I.n → FpX X p) ∘ (idxEquiv X).symm) = 0 := rfl
        rw [this, Matrix.mulVec_zero, Matrix.mulVec_zero]
      rw [this, Matrix.mulVec_zero]
    rw [hsplit, h0, c1]
    simp only [congSpan_zero, and_true]
    let u : Fin D.R.rS ⊕ Fin D.R.k → IdxD D → FpX X p :=
      Sum.elim (fun b => crd1 X p θ Q (PI.FinKW.vecV X.B.I p.1 (X.e0 b)))
        (fun j' => crd1 X p θ Q (PI.FinKW.vecV X.B.I p.1 (X.bw j')))
    let pos : Fin D.R.rS ⊕ Fin D.R.k → IdxD D := Sum.elim Sum.inl wI
    let s : Set (Fin D.R.rS ⊕ Fin D.R.k) := Set.range Sum.inl ∪ Sum.inr '' {j' | j'.1 < j.1}
    have hset : crd1 X p θ Q '' ((Set.range fun b => PI.FinKW.vecV X.B.I p.1 (X.e0 b)) ∪
        (fun j => PI.FinKW.vecV X.B.I p.1 (X.bw j)) '' {j' | j'.1 < j.1}) = u '' s := by
      ext v; simp only [u, s, Set.mem_image, Set.mem_union, Set.mem_range, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨x, (⟨y, rfl⟩ | ⟨b, hb, rfl⟩), rfl⟩
        · exact ⟨Sum.inl y, Or.inl ⟨y, rfl⟩, rfl⟩
        · exact ⟨Sum.inr b, Or.inr ⟨b, hb, rfl⟩, rfl⟩
      · rintro ⟨c, (⟨y, rfl⟩ | ⟨b, hb, rfl⟩), rfl⟩
        · exact ⟨_, Or.inl ⟨y, rfl⟩, rfl⟩
        · exact ⟨_, Or.inr ⟨b, hb, rfl⟩, rfl⟩
    have hpos : pos '' s = posW (r := D.R.rS) j := by
      ext v; simp [pos, s, posW]
    rw [hset]
    have hu : ∀ b, ∃ z, IntVec O z ∧ u b = Pi.single (pos b) 1 + ((gA X p : O) : FpX X p) • z := by
      rintro (b | j')
      · exact hE1 b
      · exact hB1 j'
    have := clause_iff O π (gA X p) hker Ym u pos hu s _ (wI j) (hB1 j)
    rw [hpos] at this
    exact this
  unfold LocCong EntA
  rw [forall_congr' ce, cz, forall_congr' cw, forall_and]
  constructor
  · rintro ⟨⟨hP, hQ⟩, ⟨hR, hS'⟩, hT⟩; exact ⟨hP, hR, hT, hQ, hS'⟩
  · rintro ⟨hP, hR, hT, hQ, hS'⟩; exact ⟨⟨hP, hQ⟩, ⟨hR, hS'⟩, hT⟩

end Loc

end MassDataIdxSteps
end
end
end
