module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.FirstCoordsMulVec
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.ParabolicImageOfBasisAdapted
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.FrAIntReindex
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.ImAInModPSplit
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.GlRedEqOneIff
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.ParabolicReductionImage
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.ReductionImageOfLocalMod
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.StRedOfSplit
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.GOfPrime
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.ImASubKpp
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
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.StKHolds
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.SecondCoordsSub
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.LocCongIffEnt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.LocDegOneBelow
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.SplitTransport
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.SecondCoordsSmulInteger
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.SecondCoordsTensorSmul
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.ReductionImageOfFrame

section

@[expose] public section

noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge MassDataIdxStIm MassDataIdxRed

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I)

def StFrameA (p : TypX X) : Prop :=
  ∃ π : Op X p →+* ZMod (gOf p), Function.Surjective π ∧
    RingHom.ker π = Ideal.span {((gOf p : ℕ) : Op X p)} ∧
  ∃ K : Subgroup (HAp X p), (K : Set (HAp X p)) = KvX X p ∧
    ∃ ψ : K →* GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Op X p), Function.Surjective ψ ∧
      (∀ x : K, (∀ i j, ((ψ x : Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Op X p))
        - 1) i j ∈ Ideal.span {((gOf p : ℕ) : Op X p)}) ↔ (x : HAp X p) ∈ KgX X p) ∧
      ∃ c, ∀ x : K, LocCong X p x ↔
        (glRed π c)⁻¹ * glRed π (ψ x) * glRed π c ∈ nuG (ZMod (gOf p)) D.R.rS D.R.k

theorem reduction_image_of_frame (p : TypX X) (h : StFrameA X p) : LevelReductionImage X hb p := by
  obtain ⟨π, hπ, hker, K, hKc, ψ, hψ, hP, c, hc⟩ := h
  have : Fact (gOf p).Prime := ⟨gOf_prime X p⟩
  set ρ₀ : K →* GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (ZMod (gOf p)) :=
    (MulAut.conj (glRed π c)⁻¹).toMonoidHom.comp ((glRed π).comp ψ) with hρ₀
  have hval : ∀ x : K, ρ₀ x = (glRed π c)⁻¹ * glRed π (ψ x) * glRed π c := by
    intro x; simp [hρ₀]
  have hk₀ : ∀ x : K, ρ₀ x = 1 ↔ (x : HAp X p) ∈ KgX X p := by
    intro x
    rw [hρ₀, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
      MonoidHom.comp_apply, glRed_eq_one_iff, hker]
    exact hP x
  have hon : Function.Surjective ρ₀ := by
    have h := (MulEquiv.surjective (MulAut.conj (glRed π c)⁻¹)).comp
      ((glRed_surjective π hπ (isUnit_of_map π hπ)).comp hψ)
    exact h
  refine ⟨K, hKc, ρ₀, hon, hk₀, (nuG (ZMod (gOf p)) D.R.rS D.R.k).comap ρ₀, ?_, ?_, 1, ?_⟩
  · ext y
    rw [stImAloc_holds X hb p]
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨?_, (hc x).2 ((hval x) ▸ hx)⟩
      rw [← hKc]; exact x.2
    · rintro ⟨hy, hcy⟩
      have hyK : y ∈ K := by rw [← hKc] at hy; exact hy
      refine ⟨⟨y, hyK⟩, ?_, rfl⟩
      show ρ₀ ⟨y, hyK⟩ ∈ nuG (ZMod (gOf p)) D.R.rS D.R.k
      rw [hval]; exact (hc ⟨y, hyK⟩).1 hcy
  · intro x hx
    show ρ₀ x ∈ nuG (ZMod (gOf p)) D.R.rS D.R.k
    rw [MonoidHom.mem_ker.mp hx]; exact one_mem _
  · rw [Subgroup.map_comap_eq_self_of_surjective hon]
    ext z; simp

end MassDataIdxSteps
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.ReductionImageOfTransitive

section

@[expose] public section

noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge MassDataIdxStIm MassDataIdxRed MassDataIdxSpl Matrix

section Loc

variable {D : D7} (X : HidaSetting D)

def TransA (p : TypX X) (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p)
    (Q : GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (FpX X p)) (π : Op X p →+* ZMod (gOf p)) : Prop :=
  ∀ x : HAp X p, x ∈ KvX X p → ∀ Y : GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Op X p),
    ((glRed (algebraMap (Op X p) (FpX X p)) Y : GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (FpX X p)) :
        Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (FpX X p)) =
      ((Q⁻¹ : GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (FpX X p)) :
          Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (FpX X p)) *
        Matrix.reindex (idxEquiv X) (idxEquiv X) (cmp1 X.B.I.cm.sig X.B.I.J θ x) *
        (Q : Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (FpX X p)) →
    (LocCong X p x ↔ glRed π Y ∈ nuG (ZMod (gOf p)) D.R.rS D.R.k)

def StTransA (p : TypX X) : Prop :=
  ∃ θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p, IsSplitEquiv X p θ ∧
    ∃ Q : GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (FpX X p), LatBasis X p θ (reindex₂ X p Q) ∧
      ∃ π : Op X p →+* ZMod (gOf p), Function.Surjective π ∧
        RingHom.ker π = Ideal.span {((gOf p : ℕ) : Op X p)} ∧ TransA X p θ Q π

theorem stFrameA_of_trans (hC : LatCoreX) (p : TypX X) (h : StTransA X p) : StFrameA X p := by
  obtain ⟨θ, hθ, Q, hL, π, hπ, hker, hT⟩ := h
  obtain ⟨ψ, hψ, hk, hform⟩ := hC X p θ hθ Q hL (stK_holds X p).choose (stK_holds X p).choose_spec.1
  refine ⟨π, hπ, hker, (stK_holds X p).choose, (stK_holds X p).choose_spec.1, ψ, hψ, hk, 1, fun x => ?_⟩
  rw [map_one, inv_one, one_mul, mul_one]
  have hx : (x : HAp X p) ∈ KvX X p :=
    (Set.ext_iff.mp (stK_holds X p).choose_spec.1 (x : HAp X p)).1 x.2
  exact hT x hx (ψ x) (hform x)

end Loc

end MassDataIdxSteps
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.ReductionImageOfAdapted

section

@[expose] public section

noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge MassDataIdxStIm MassDataIdxRed MassDataIdxSpl Matrix
  MassDataIdxFrA
open scoped TensorProduct

section Pos

variable {r k : ℕ}

theorem frA_condE (a : Fin r) (i : Formalism.FourierDecayAlt.S3.Idx r k) :
    (∀ a' : Fin (r + 1), a' < Fin.castSucc a → i ≠ pe a') ↔ i ∉ (Sum.inl '' {b : Fin r | b.1 < a.1}) := by
  constructor
  · rintro h ⟨b, hb, hbi⟩
    exact h (Fin.castSucc b) (Fin.castSucc_lt_castSucc_iff.mpr hb) (by rw [pe_castSucc]; exact hbi.symm)
  · intro h a' ha' hi
    apply h
    have ha2 : (a' : ℕ) < a.1 := ha'
    refine ⟨⟨a', by omega⟩, ha2, ?_⟩
    rw [hi, pe_inl_of_lt ha']

theorem frA_condZ (i : Formalism.FourierDecayAlt.S3.Idx r k) :
    (∀ a' : Fin (r + 1), a' < Fin.last r → i ≠ pe a') ↔ i ∉ (Sum.inl '' Set.univ) := by
  constructor
  · rintro h ⟨b, -, hbi⟩
    exact h (Fin.castSucc b) (Fin.castSucc_lt_last b) (by rw [pe_castSucc]; exact hbi.symm)
  · intro h a' ha' hi
    apply h
    refine ⟨⟨a', ha'⟩, trivial, ?_⟩
    rw [hi, pe_inl_of_lt ha']

theorem frA_condF (a : Fin r) (i : Formalism.FourierDecayAlt.S3.Idx r k) :
    (∀ a' : Fin (r + 1), a' < Fin.castSucc a → i ≠ pf a') ↔
      i ∉ ((fun b : Fin r => (Sum.inr (Sum.inr (Fin.rev b)) : Formalism.FourierDecayAlt.S3.Idx r k)) '' {b : Fin r | b.1 < a.1}) := by
  constructor
  · rintro h ⟨b, hb, hbi⟩
    exact h (Fin.castSucc b) (Fin.castSucc_lt_castSucc_iff.mpr hb) (by rw [pf_castSucc]; exact hbi.symm)
  · intro h a' ha' hi
    apply h
    have ha2 : (a' : ℕ) < a.1 := ha'
    refine ⟨⟨a', by omega⟩, ha2, ?_⟩
    rw [hi, pf_of_lt ha']

theorem frA_condFZ (i : Formalism.FourierDecayAlt.S3.Idx r k) :
    (∀ a' : Fin (r + 1), a' < Fin.last r → i ≠ pf a') ↔
      i ∉ ((fun b : Fin r => (Sum.inr (Sum.inr (Fin.rev b)) : Formalism.FourierDecayAlt.S3.Idx r k)) '' Set.univ) := by
  constructor
  · rintro h ⟨b, -, hbi⟩
    exact h (Fin.castSucc b) (Fin.castSucc_lt_last b) (by rw [pf_castSucc]; exact hbi.symm)
  · intro h a' ha' hi
    apply h
    refine ⟨⟨a', ha'⟩, trivial, ?_⟩
    rw [hi, pf_of_lt ha']

end Pos

section Loc

variable {D : D7} (X : HidaSetting D) (p : TypX X)

theorem ent_iff_nuG (π : Op X p →+* ZMod (gOf p)) (Y : GL (IdxD D) (Op X p)) :
    EntA X p π Y ↔ glRed π Y ∈ nuG (ZMod (gOf p)) D.R.rS D.R.k := by
  have : Fact (gOf p).Prime := ⟨gOf_prime X p⟩
  open Formalism.FourierDecayAlt.S3 Formalism.DoubleCosetMeasures in
  have colW_iff {K : Type} [Field K] {r k : ℕ} (m : Matrix (Idx r k) (Idx r k) K) :
      ColW m ↔ ∀ i : Fin k, ∀ j, j ∉ posW (r := r) i → m j (wI i) = if j = wI i then 1 else 0 := by
    unfold ColW
    refine forall_congr' fun i => ?_
    rw [mem_span_single]
    refine forall_congr' fun j => forall_congr' fun _ => ?_
    have e : (m *ᵥ Pi.single (wI i) (1 : K)) j = m j (wI i) := by rw [Matrix.mulVec_single_one]; rfl
    rw [Pi.sub_apply, sub_eq_zero, e, Pi.single_apply]

  have par_uni_iff_flags {K : Type} [Field K] {r k : ℕ} (x y : Matrix (Idx r k) (Idx r k) K) (hxy : x * y = 1) (hyx : y * x = 1) :
      Par IsUpUni x ↔ ColC x ∧ ColW x ∧ RowC y := by
    constructor
    · intro hx
      have hu : Par (fun h => IsUnit h.det) x := by
        obtain ⟨h11, h33, h21, h31, h32, h, hh, h22⟩ := hx
        exact ⟨h11, h33, h21, h31, h32, h, uni_unit hh, h22⟩
      obtain ⟨hC, hR⟩ := (par_iff_flags x y hxy hyx).1 hu
      refine ⟨hC, ?_, hR⟩
      obtain ⟨h11, h33, h21, h31, h32, h, hh, h22⟩ := hx
      rw [colW_iff]
      intro i j hj
      rcases j with a | (j | u) | c
      · exact absurd (Or.inl ⟨a, rfl⟩) hj
      · have e := congrFun (congrFun h22 (Sum.inl j)) (Sum.inl i)
        simp only [b22, midEmb, Matrix.of_apply, Matrix.fromBlocks_apply₁₁] at e
        have hji : ¬ j < i := fun hlt => hj (Or.inr ⟨j, hlt, rfl⟩)
        show x (wI j) (wI i) = _
        rw [show x (wI j) (wI i) = h j i from e]
        by_cases hij : j = i
        · subst hij; simp [hh.2 j, wI]
        · have hlt : i < j := lt_of_le_of_ne (not_lt.1 hji) (Ne.symm hij)
          rw [hh.1 hlt]
          have : (wI j : Idx r k) ≠ wI i := by
            intro e'; apply hij; simpa [wI] using e'
          simp [wI, hij]
      · have e := congrFun (congrFun h22 (Sum.inr u)) (Sum.inl i)
        simp only [b22, midEmb, Matrix.of_apply, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply] at e
        have e' : x (Sum.inr (Sum.inl (Sum.inr u))) (wI i) = 0 := e
        rw [e']; simp [wI]
      · have e := congrFun (congrFun h32 c) (Sum.inl i)
        simp only [b32, Matrix.of_apply, Matrix.zero_apply] at e
        have e' : x (Sum.inr (Sum.inr c)) (wI i) = 0 := e
        rw [e']; simp [wI]
    · rintro ⟨hC, hW, hR⟩
      obtain ⟨h11, h33, h21, h31, h32, h, -, h22⟩ := (par_iff_flags x y hxy hyx).2 ⟨hC, hR⟩
      refine ⟨h11, h33, h21, h31, h32, h, ⟨fun j i hlt => ?_, fun i => ?_⟩, h22⟩
      ·
        have e := congrFun (congrFun h22 (Sum.inl j)) (Sum.inl i)
        simp only [b22, midEmb, Matrix.of_apply, Matrix.fromBlocks_apply₁₁] at e
        rw [← e]
        have hnot : (wI j : Idx r k) ∉ posW (r := r) i := by
          rintro (⟨a, ha⟩ | ⟨j', hj', he⟩)
          · simp [wI] at ha
          · have : j' = j := by simpa [wI] using he
            subst this
            exact absurd hlt (not_lt.2 (le_of_lt hj'))
        have := (colW_iff x).1 hW i (wI j) hnot
        rw [show x (wI j) (wI i) = x (Sum.inr (Sum.inl (Sum.inl j))) (Sum.inr (Sum.inl (Sum.inl i))) from rfl] at this
        rw [this]
        have hne : (wI j : Idx r k) ≠ wI i := by
          intro e'; have : j = i := by simpa [wI] using e'
          exact absurd hlt (by rw [this]; exact lt_irrefl _)
        simp [hne]
      · have e := congrFun (congrFun h22 (Sum.inl i)) (Sum.inl i)
        simp only [b22, midEmb, Matrix.of_apply, Matrix.fromBlocks_apply₁₁] at e
        rw [← e]
        have hnot : (wI i : Idx r k) ∉ posW (r := r) i := by
          rintro (⟨a, ha⟩ | ⟨j', hj', he⟩)
          · simp [wI] at ha
          · have : j' = i := by simpa [wI] using he
            subst this
            exact lt_irrefl j' hj'
        have := (colW_iff x).1 hW i (wI i) hnot
        have h1 : x (wI i) (wI i) = 1 := by simpa using this
        exact h1

  have mem_nuG_iff_flags {K : Type} [Field K] {r k : ℕ} (g : GL (Idx r k) K) :
      g ∈ nuG K r k ↔ ColFlag (g : Matrix (Idx r k) (Idx r k) K) ∧ ColW (g : Matrix (Idx r k) (Idx r k) K) ∧
        RowFlag ((g⁻¹ : GL (Idx r k) K) : Matrix (Idx r k) (Idx r k) K) := by
    rw [colFlag_iff, rowFlag_iff]
    exact par_uni_iff_flags _ _ (by rw [← Units.val_mul, mul_inv_cancel, Units.val_one])
      (by rw [← Units.val_mul, inv_mul_cancel, Units.val_one])
  rw [mem_nuG_iff_flags, colFlag_iff', colW_iff, rowFlag_iff', ← map_inv, Fin.forall_fin_succ',
    Fin.forall_fin_succ']
  simp only [pe_castSucc, pe_last, pf_castSucc, pf_last]
  simp only [frA_condE, frA_condZ, frA_condF, frA_condFZ]
  unfold EntA
  constructor
  · rintro ⟨hP, hR, hT, hQ, hS⟩
    exact ⟨⟨hP, hR⟩, hT, ⟨hQ, hS⟩⟩
  · rintro ⟨⟨hP, hR⟩, hT, ⟨hQ, hS⟩⟩
    exact ⟨hP, hR, hT, hQ, hS⟩

variable (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p) (Q : GL (IdxD D) (FpX X p))

theorem transA_of (hθ : IsSplitEquiv X p θ) (π : Op X p →+* ZMod (gOf p))
    (hker : RingHom.ker π = Ideal.span {((gOf p : ℕ) : Op X p)}) (hS : SplitA X p θ Q) (hA : AdaptA X p θ Q) :
    TransA X p θ Q π := fun x _ Y hY =>
  (locCong_iff_ent X p θ Q hθ π hker hS hA x Y hY).trans (ent_iff_nuG X p π Y)

def StAdaptA : Prop :=
  ∃ θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p, IsSplitEquiv X p θ ∧
    ∃ Q : GL (IdxD D) (FpX X p), LatBasis X p θ (reindex₂ X p Q) ∧ SplitA X p θ Q ∧ AdaptA X p θ Q

theorem stFrameA_of_adapt (hC : LatCoreX) (h : StAdaptA X p) : StFrameA X p := by
  obtain ⟨θ, hθ, Q, hL, hS, hA⟩ := h
  have hres : ResArith X p := by
    have hgp : Fact (gOf p).Prime := ⟨gOf_prime X p⟩
    have hmem : ((gOf p : ℕ) : 𝓞 X.B.I.F) ∈ p.1.asIdeal := by
      have hty := (mem_typSet X.B.I.F (D.host.g 0) (D.host.g 1) (D.host.g_prime 0).ne_zero
        (D.host.g_prime 1).ne_zero p.1).1 p.2
      unfold gOf
      split_ifs with h
      · exact h
      · exact hty.resolve_left h
    have hsplit : {w : IsDedekindDomain.HeightOneSpectrum (𝓞 X.B.I.E) |
        ((gOf p : ℕ) : 𝓞 X.B.I.E) ∈ w.asIdeal}.ncard = Module.finrank ℚ X.B.I.E := by
      unfold gOf
      split_ifs
      · exact MassDataIdxRes.split_transport X.ιE _ (D.nd.g_split 0)
      · exact MassDataIdxRes.split_transport X.ιE _ (D.nd.g_split 1)
    obtain ⟨he, hf⟩ := MassDataIdxRes.locDeg_one_below (F := X.B.I.F) (E := X.B.I.E) (gOf p) hsplit p.1 hmem
    obtain ⟨hc, hn⟩ := MassDataIdxRes.arith_of_loc (gOf p) p.1 hmem he hf
    exact ⟨hc, hmem, hn⟩

  obtain ⟨π, hπ, hker⟩ := stResZ_of X p hres
  exact stFrameA_of_trans X hC p ⟨θ, hθ, Q, hL, π, hπ, hker, transA_of X p θ Q hθ π hker hS hA⟩

theorem reduction_image_of_adapted (hb : AdBridgeIso X.B.I) (hC : LatCoreX) (h : StAdaptA X p) : LevelReductionImage X hb p :=
  reduction_image_of_frame X hb p (stFrameA_of_adapt X p hC h)

end Loc

end MassDataIdxSteps
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.ReductionImageOfAdaptedMod

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

abbrev mQJ : Matrix (IdxD D) (IdxD D) (FpX X p) :=
  (Q : Matrix (IdxD D) (IdxD D) (FpX X p))ᵀ * (Matrix.reindex (idxEquiv X) (idxEquiv X) (jm1 X.B.I.J θ))ᵀ

theorem mQJ_unit : IsUnit (mQJ X p θ Q).det := by
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_transpose, Matrix.det_reindex_self]
  exact (Units.isUnit (Matrix.GeneralLinearGroup.det Q)).mul (isUnit_det_split_form X p θ)

theorem secondCoords_eq_mulVec (v : Fin X.B.I.n → TpX X p) :
    crd2 X p θ Q v = mQJ X p θ Q *ᵥ (pr2 θ v ∘ (idxEquiv X).symm) := by
  unfold crd2; rw [Matrix.mulVec_mulVec]

theorem crd_surj (a b : IdxD D → FpX X p) : ∃ x, crd1 X p θ Q x = a ∧ crd2 X p θ Q x = b := by
  set w1 := (Q : Matrix (IdxD D) (IdxD D) (FpX X p)) *ᵥ a
  set w2 := (mQJ X p θ Q)⁻¹ *ᵥ b
  refine ⟨fun j => θ.symm (w1 (idxEquiv X j), w2 (idxEquiv X j)), ?_, ?_⟩
  · have : pr1 θ (fun j => θ.symm (w1 (idxEquiv X j), w2 (idxEquiv X j))) ∘ (idxEquiv X).symm = w1 := by
      funext i; simp [pr1]
    unfold crd1; rw [this, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mulVec]
  · have : pr2 θ (fun j => θ.symm (w1 (idxEquiv X j), w2 (idxEquiv X j))) ∘ (idxEquiv X).symm = w2 := by
      funext i; simp [pr2]
    rw [secondCoords_eq_mulVec, this, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (mQJ_unit X p θ Q), Matrix.one_mulVec]

theorem crd_inj (x : Fin X.B.I.n → TpX X p) (h1 : crd1 X p θ Q x = 0) (h2 : crd2 X p θ Q x = 0) : x = 0 := by
  have e1 : pr1 θ x ∘ (idxEquiv X).symm = 0 := by
    have := congrArg (fun v => (Q : Matrix (IdxD D) (IdxD D) (FpX X p)) *ᵥ v) h1
    simp only [crd1, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mulVec, Matrix.mulVec_zero] at this
    exact this
  have e2 : pr2 θ x ∘ (idxEquiv X).symm = 0 := by
    have := congrArg (fun v => (mQJ X p θ Q)⁻¹ *ᵥ v) h2
    simp only [secondCoords_eq_mulVec, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (mQJ_unit X p θ Q),
      Matrix.one_mulVec, Matrix.mulVec_zero] at this
    exact this
  funext j
  have a1 := congrFun e1 (idxEquiv X j)
  have a2 := congrFun e2 (idxEquiv X j)
  simp only [Function.comp_apply, Equiv.symm_apply_apply, Pi.zero_apply] at a1 a2
  have : θ (x j) = 0 := Prod.ext a1 a2
  simpa using congrArg θ.symm this

theorem oEp_int (hL : LatBasis X p θ (reindex₂ X p Q)) (t : TpX X p) (ht : t ∈ OEp X p) :
    (θ t).1 ∈ OvA X p ∧ (θ t).2 ∈ OvA X p := by
  obtain ⟨j⟩ : Nonempty (IdxD D) := ⟨zI⟩
  obtain ⟨x1, hx1a, hx1b⟩ := crd_surj X p θ Q (Pi.single j 1) 0
  obtain ⟨x2, hx2a, hx2b⟩ := crd_surj X p θ Q 0 (Pi.single j 1)
  have hint : IntVec (OvA X p) (Pi.single j (1 : FpX X p)) := fun i => by
    by_cases h : i = j
    · subst h; simp [ValuationSubring.one_mem]
    · simp [h, ValuationSubring.zero_mem]
  have hz : IntVec (OvA X p) (0 : IdxD D → FpX X p) := fun _ => ValuationSubring.zero_mem _
  have l1 := imA_lat_OEp X p ht ((latCrd_of X p θ Q hL x1).2 ⟨hx1a ▸ hint, hx1b ▸ hz⟩)
  have l2 := imA_lat_OEp X p ht ((latCrd_of X p θ Q hL x2).2 ⟨hx2a ▸ hz, hx2b ▸ hint⟩)
  have c1 := ((latCrd_of X p θ Q hL _).1 l1).1 j
  have c2 := ((latCrd_of X p θ Q hL _).1 l2).2 j
  rw [firstCoords_tensor_smul, hx1a] at c1
  rw [secondCoords_tensor_smul, hx2b] at c2
  simp at c1 c2
  exact ⟨c1, c2⟩

def OEpSplit : Prop := θ.symm (1, 0) ∈ OEp X p ∧ θ.symm (0, 1) ∈ OEp X p

theorem splitA_of_lat (hL : LatBasis X p θ (reindex₂ X p Q)) (hO : OEpSplit X p θ) : SplitA X p θ Q :=
  splitA_of X p θ Q (oEp_int X p θ Q hL) hO.1 hO.2 (latCrd_of X p θ Q hL) (crd_inj X p θ Q) (crd_surj X p θ Q)

theorem reduction_image_of_adapted_mod (hb : AdBridgeIso X.B.I) (hC : LatCoreX)
    (h : ∃ θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p, IsSplitEquiv X p θ ∧ OEpSplit X p θ ∧
      ∃ Q : GL (IdxD D) (FpX X p), LatBasis X p θ (reindex₂ X p Q) ∧ AdaptA X p θ Q) : LevelReductionImage X hb p := by
  obtain ⟨θ, hθ, hO, Q, hL, hA⟩ := h
  exact reduction_image_of_adapted X p hb hC ⟨θ, hθ, Q, hL, splitA_of_lat X p θ Q hL hO, hA⟩

end Loc

end MassDataIdxSteps
end
end
end
