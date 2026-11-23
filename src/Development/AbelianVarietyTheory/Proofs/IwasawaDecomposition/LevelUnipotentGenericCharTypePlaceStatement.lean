module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DatVtEq
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsLevel
public import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeCharTameAtOfFactorsThroughResidue
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSplitPlaceComponentHeckeCharResidueStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceResidueMapUnitCharacterStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StdMaximalCompactReductionPropertiesStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StdMaximalCompactReductionPropertiesStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypePlaceLevelPlacesDistinctUnderlyingStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StdFrameLevelCharacterAtTypePlaceEq

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.MtIn
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.DIV

namespace GlobalTheory.MtChr

theorem sum_supEdge_castLE {R : Type} [AddCommMonoid R] {n r : ℕ} (hr : r ≤ n) (f : Fin n → Fin n → R) :
    (∑ i : Fin r, ∑ j : Fin r, if supEdge i j then f (Fin.castLE hr i) (Fin.castLE hr j) else 0) =
      ∑ a : Fin n, ∑ b : Fin n, if a.val + 1 = b.val ∧ b.val < r then f a b else 0 := by
  refine Fintype.sum_of_injective (Fin.castLE hr) (Fin.castLE_injective hr) _ _ ?_ ?_
  · intro a ha
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [if_neg]
    rintro ⟨h1, h2⟩
    exact ha ⟨⟨a.val, by omega⟩, Fin.ext rfl⟩
  · intro i
    refine Fintype.sum_of_injective (Fin.castLE hr) (Fin.castLE_injective hr) _ _ ?_ ?_
    · intro b hb
      rw [if_neg]
      rintro ⟨h1, h2⟩
      exact hb ⟨⟨b.val, h2⟩, Fin.ext rfl⟩
    · intro j
      by_cases hh : supEdge i j
      · have h' : j.val = i.val + 1 := hh
        rw [if_pos hh, if_pos (by simp only [Fin.val_castLE]; exact ⟨h'.symm, j.2⟩)]
      · have h' : ¬ j.val = i.val + 1 := hh
        rw [if_neg hh, if_neg (by simp only [Fin.val_castLE]; exact fun e => h' e.1.symm)]

theorem blkOf_eq_one_iff {n r t : ℕ} (a : Fin n) (ha : a.val < r + t) : blkOf r t a = 1 ↔ r ≤ a.val := by
  unfold blkOf
  by_cases h : a.val < r
  · simp only [h, if_true]; omega
  · simp only [h, if_false]
    rw [Nat.div_eq_of_lt (by omega)]
    omega

theorem edgeSum_supEdge_one {κ : Type} [CommRing κ] {r : ℕ} : edgeSum (κ := κ) (supEdge (r := r)) 1 = 0 := by
  unfold edgeSum
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  split_ifs with hh
  · rw [Units.val_one, Matrix.one_apply_ne]
    intro e; rw [e] at hh; unfold supEdge at hh; omega
  · rfl

theorem det_map_subtype {O k : Type} [CommRing O] [CommRing k] (φ : O →+* k) {n : ℕ} (M : Matrix (Fin n) (Fin n) O)
    (N : Matrix (Fin n) (Fin n) k) (hMN : ∀ a b, N a b = φ (M a b)) (p q : Fin n → Prop) [DecidablePred p] [DecidablePred q]
    (hpq : ∀ a, p a ↔ q a) :
    φ (Matrix.of fun a b : {y // q y} => M a.1 b.1).det = (N.submatrix (Subtype.val : {a // p a} → Fin n) Subtype.val).det := by
  rw [RingHom.map_det]
  rw [← Matrix.det_submatrix_equiv_self (Equiv.subtypeEquivRight hpq) (φ.mapMatrix _)]
  congr 1
  ext a b
  exact (hMN a.1 b.1).symm

end GlobalTheory.MtChr


theorem GlobalTheory.MtChr.levChar_std_uni : ∀ (D : D7) (hr : D.R.r ≤ D.R.nV) (Pg Q : Finset (Pl D.host.E)) (ψ : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ) (chi xi : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (s : ReciprocityTheory.Aut.SplitPlace D.host.E) (φ : s.v.adicCompletionIntegers (maximalRealSubfield D.host.E) →+* kP s.w), (∀ x, φ x = 0 ↔ Valued.v (x : s.v.adicCompletion (maximalRealSubfield D.host.E)) < 1) → (∀ κ ∈ ReciprocityTheory.Aut.Umax D.host.E D.R.nV, ∀ a b, ∃ h : (s.loc D.R.nV κ).val a b ∈ s.v.adicCompletionIntegers (maximalRealSubfield D.host.E), (redFn (1 : GL (Fin D.R.nV) (EAf D)) s.w (km D D.R.nV κ)).val a b = φ ⟨_, h⟩) → s.w ∈ Pg → (∀ PP ∈ Pg, PP ≠ s.w → ¬ NG.OverPl PP s.v) → (∀ PP ∈ Q, ¬ NG.OverPl PP s.v) → ∀ (ψ₀ : AddChar (s.v.adicCompletion (maximalRealSubfield D.host.E)) ℂ) (ξ : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ →* ℂˣ), (∀ x : s.v.adicCompletionIntegers (maximalRealSubfield D.host.E), ψ₀ (x : s.v.adicCompletion (maximalRealSubfield D.host.E)) = ψ s.w (-φ x)) → (∀ (u : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ) (x : s.v.adicCompletionIntegers (maximalRealSubfield D.host.E)) (w : (kP s.w)ˣ), (x : s.v.adicCompletion (maximalRealSubfield D.host.E)) = u → φ x = w → ξ u = (chi s.w)⁻¹ w) → ∀ κ (h : κ ∈ stdJ (datV D D.R.nV hr Pg Q (P0 Pg D.R.r ψ) chi xi)), ReciprocityTheory.Aut.TrivOutside {s.v} κ → ∀ u : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ, (u : s.v.adicCompletion (maximalRealSubfield D.host.E)) = NG.detDD s D.R.r (s.loc D.R.nV κ) → ((stdX (datV D D.R.nV hr Pg Q (P0 Pg D.R.r ψ) chi xi) ⟨κ, h⟩ : ℂˣ) : ℂ) = ψ₀ (NG.supDiag s D.R.r (s.loc D.R.nV κ)) * ξ u := by
  intro D hr Pg Q ψ chi xi s φ hφ0 hred hsw hPg hQ ψ₀ ξ hψ₀ hξ κ h htriv u hu
  set Ld := GlobalTheory.MtIn.datV D D.R.nV hr Pg Q (P0 Pg D.R.r ψ) chi xi
  set x := km D D.R.nV κ
  have hL : x ∈ lev D.sp.cm 1 1 Ld := h
  have hpar : x ∈ parLev D.sp.cm 1 1 Ld := hL.1
  have hP0 : rTup 1 Ld x ∈ (P0 Pg D.R.r ψ).conj.H := hL.2
  obtain ⟨-, hStU, hout, -⟩ := GlobalTheory.T.stdMaximalCompact_reduction_properties D D.R.nV
  have hU : κ ∈ ReciprocityTheory.Aut.Umax D.host.E D.R.nV := (hStU κ).1 (parLev_St hpar)
  have hg : ∀ PP ∈ Pg, redFn 1 PP x ∈ blockTri (blkOf D.R.r D.R.t) := fun PP hP => parLev_g hpar hP
  have triv : ∀ PP : Pl D.host.E, ¬ NG.OverPl PP s.v → redFn 1 PP x = 1 := by
    intro PP hn
    refine hout κ hU {s.v} (PP.under (𝓞 (maximalRealSubfield D.host.E))) PP htriv rfl ?_
    intro hv
    rw [Set.mem_singleton_iff] at hv
    exact hn (hv ▸ rfl)
  choose hint hredv using hred κ hU
  let ι := (s.v.adicCompletionIntegers (maximalRealSubfield D.host.E)).subtype
  let M' : Matrix (Fin D.R.nV) (Fin D.R.nV) (s.v.adicCompletionIntegers (maximalRealSubfield D.host.E)) :=
    fun a b => ⟨_, hint a b⟩

  let Sn : s.v.adicCompletionIntegers (maximalRealSubfield D.host.E) :=
    ∑ a : Fin D.R.nV, ∑ b : Fin D.R.nV, if a.val + 1 = b.val ∧ b.val < D.R.r then M' a b else 0
  have hSn : (Sn : s.v.adicCompletion (maximalRealSubfield D.host.E)) = NG.supDiag s D.R.r (s.loc D.R.nV κ) := by
    show ι Sn = _

    simp only [Sn, map_sum]
    unfold NG.supDiag
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    split_ifs
    · rfl
    · exact map_zero ι
  have hφSn : φ Sn = edgeSum supEdge (upperLeftBlock hr (redFn 1 s.w x)) := by
    unfold edgeSum
    rw [upper_block_val_submatrix hr (blockTri_blkOf_le _ _ (hg s.w hsw))]
    simp only [Matrix.submatrix_apply]
    refine Eq.trans ?_ (GlobalTheory.MtChr.sum_supEdge_castLE hr (fun a b => (redFn (1 : GL (Fin D.R.nV) (EAf D)) s.w x).val a b)).symm

    simp only [Sn, map_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    split_ifs
    · exact (hredv a b).symm
    · exact map_zero φ

  let Md : Matrix {y : Fin D.R.nV // D.R.r ≤ y.val} {y : Fin D.R.nV // D.R.r ≤ y.val}
      (s.v.adicCompletionIntegers (maximalRealSubfield D.host.E)) := fun a b => M' a.1 b.1
  have hdet : (Md.det : s.v.adicCompletion (maximalRealSubfield D.host.E)) = (u : s.v.adicCompletion (maximalRealSubfield D.host.E)) := by
    rw [hu]
    show ι Md.det = _
    rw [RingHom.map_det]
    unfold NG.detDD
    rfl
  have hφdet' : φ Md.det = (((redFn 1 s.w x).val).submatrix (Subtype.val : {a : Fin D.R.nV // blkOf D.R.r D.R.t a = 1} → Fin D.R.nV) Subtype.val).det :=
    GlobalTheory.MtChr.det_map_subtype φ M' _ hredv _ _ (fun a => GlobalTheory.MtChr.blkOf_eq_one_iff a (lt_of_lt_of_eq a.2 rfl))
  have hφdet : φ Md.det = ((dBlk (blkOf D.R.r D.R.t) 1 (redFn 1 s.w x) : (kP s.w)ˣ) : kP s.w) :=
    hφdet'.trans (diag_block_det_val 1 (hg s.w hsw)).symm
  have hξu := hξ u Md.det _ hdet hφdet

  have hA : ((ext1 (P0 Pg D.R.r ψ).conj.H (P0 Pg D.R.r ψ).conj.chi (rTup 1 Ld x) : ℂˣ) : ℂ) =
      (ψ s.w (edgeSum supEdge (upperLeftBlock hr (redFn 1 s.w x))))⁻¹ := by
    erw [extendOne_of_mem _ hP0]
    show (((P0 Pg D.R.r ψ).chi⁻¹ ⟨_, hP0⟩ : ℂˣ) : ℂ) = _
    rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val]
    congr 1
    show (((∏ PP : ↥Pg, (addCharHom (ψ PP.1) (supHom (kP PP.1) D.R.r)).comp (LevelP.prj _ PP)) ⟨_, hP0⟩ : ℂˣ) : ℂ) = _
    rw [MonoidHom.finsetProd_apply, Fintype.prod_eq_single ⟨s.w, hsw⟩]
    · rfl
    · intro PP hne
      apply Units.ext
      show ψ PP.1 (edgeSum supEdge (upperLeftBlock hr (redFn 1 PP.1 x))) = 1
      rw [triv PP.1 (hPg PP.1 PP.2 (fun e => hne (Subtype.ext e)))]
      unfold upperLeftBlock
      rw [blockDiagonalExtendByOnePrimeField_one, GlobalTheory.MtChr.edgeSum_supEdge_one, AddChar.map_zero_eq_one]
  have hB : (∏ PP ∈ Pg, ∏ c ∈ Finset.range 1, (chi PP)⁻¹ (dBlk (blkOf D.R.r D.R.t) (c + 1) (redFn 1 PP x))) =
      (chi s.w)⁻¹ (dBlk (blkOf D.R.r D.R.t) 1 (redFn 1 s.w x)) := by
    rw [Finset.prod_eq_single_of_mem s.w hsw]
    · rw [Finset.prod_range_one]
    · intro PP hP hne
      rw [Finset.prod_range_one, triv PP (hPg PP hP hne)]
      unfold dBlk
      rw [blockDiagonalExtendByOnePrimeField_one, map_one]
  have hC : (∏ PP ∈ Q, xi PP (dBlk (blk2 D.R.r) 1 (redFn 1 PP x))) = 1 := by
    refine Finset.prod_eq_one fun PP hP => ?_
    rw [triv PP (hQ PP hP)]
    unfold dBlk
    rw [blockDiagonalExtendByOnePrimeField_one, map_one]
  show ((ext1 (P0 Pg D.R.r ψ).conj.H (P0 Pg D.R.r ψ).conj.chi (rTup 1 Ld x) *
      (∏ PP ∈ Pg, ∏ c ∈ Finset.range 1, (chi PP)⁻¹ (dBlk (blkOf D.R.r D.R.t) (c + 1) (redFn 1 PP x))) *
      ∏ PP ∈ Q, xi PP (dBlk (blk2 D.R.r) 1 (redFn 1 PP x)) : ℂˣ) : ℂ) = _
  rw [hB, hC, mul_one, Units.val_mul, hA, hξu, ← hSn, hψ₀, AddChar.map_neg_eq_inv, hφSn]
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StdFrameLevelCharacterAtTypePlaceEqStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.MtIn
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.stdFrameLevelCharacter_at_typePlace_eq : ∀ (D : D7) (hr : D.R.r ≤ D.R.nV) (Pg Q : Finset (Pl D.host.E)) (ψ : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ) (chi xi : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (s : ReciprocityTheory.Aut.SplitPlace D.host.E) (φ : s.v.adicCompletionIntegers (maximalRealSubfield D.host.E) →+* kP s.w), (∀ x, φ x = 0 ↔ Valued.v (x : s.v.adicCompletion (maximalRealSubfield D.host.E)) < 1) → (∀ κ ∈ ReciprocityTheory.Aut.Umax D.host.E D.R.nV, ∀ a b, ∃ h : (s.loc D.R.nV κ).val a b ∈ s.v.adicCompletionIntegers (maximalRealSubfield D.host.E), (redFn (1 : GL (Fin D.R.nV) (EAf D)) s.w (km D D.R.nV κ)).val a b = φ ⟨_, h⟩) → s.w ∈ Pg → (∀ PP ∈ Pg, PP ≠ s.w → ¬ NG.OverPl PP s.v) → (∀ PP ∈ Q, ¬ NG.OverPl PP s.v) → ∀ (ψ₀ : AddChar (s.v.adicCompletion (maximalRealSubfield D.host.E)) ℂ) (ξ : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ →* ℂˣ), (∀ x : s.v.adicCompletionIntegers (maximalRealSubfield D.host.E), ψ₀ (x : s.v.adicCompletion (maximalRealSubfield D.host.E)) = ψ s.w (-φ x)) → (∀ (u : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ) (x : s.v.adicCompletionIntegers (maximalRealSubfield D.host.E)) (w : (kP s.w)ˣ), (x : s.v.adicCompletion (maximalRealSubfield D.host.E)) = u → φ x = w → ξ u = (chi s.w)⁻¹ w) → ∀ κ (h : κ ∈ stdJ (datV D D.R.nV hr Pg Q (P0 Pg D.R.r ψ) chi xi)), ReciprocityTheory.Aut.TrivOutside {s.v} κ → ∀ u : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ, (u : s.v.adicCompletion (maximalRealSubfield D.host.E)) = NG.detDD s D.R.r (s.loc D.R.nV κ) → ((stdX (datV D D.R.nV hr Pg Q (P0 Pg D.R.r ψ) chi xi) ⟨κ, h⟩ : ℂˣ) : ℂ) = ψ₀ (NG.supDiag s D.R.r (s.loc D.R.nV κ)) * ξ u := by
  first | exact @GlobalTheory.MtChr.levChar_std_uni | exact GlobalTheory.MtChr.levChar_std_uni | (intros; apply GlobalTheory.MtChr.levChar_std_uni <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelUnipotentGenericCharTypePlace

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.MtIn
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TypeLevelUni

@[reducible] def unitsDiv : DivisibleBy (Additive ℂˣ) ℤ where
  div a n := if n = 0 then 0 else
    Additive.ofMul (Units.mk0 (Complex.exp (Complex.log ((Additive.toMul a : ℂˣ) : ℂ) / n)) (Complex.exp_ne_zero _))
  div_zero a := if_pos rfl
  div_cancel {n} a hn := by
    rw [if_neg hn]
    apply Additive.toMul.injective
    rw [toMul_zsmul, toMul_ofMul]
    ext
    rw [Units.val_zpow_eq_zpow_val, Units.val_mk0, ← Complex.exp_int_mul,
      mul_div_cancel₀ _ (Int.cast_ne_zero.mpr hn), Complex.exp_log (Units.ne_zero _)]

def charUnit {A : Type} [AddCommGroup A] (ψ : AddChar A ℂ) (x : A) : ℂˣ :=
  ⟨ψ x, ψ (-x), by rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one],
    by rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]⟩

theorem addChar_extend {K : Type} [Ring K] (S : Subring K) (ψ : AddChar S ℂ) :
    ∃ ψ₀ : AddChar K ℂ, ∀ x : S, ψ₀ x = ψ x := by
  let _ := unitsDiv
  let g : S →ₗ[ℤ] Additive ℂˣ := AddMonoidHom.toIntLinearMap
    { toFun := fun x => Additive.ofMul (charUnit ψ x)
      map_zero' := by
        apply Additive.toMul.injective
        ext
        simp [charUnit, AddChar.map_zero_eq_one]
      map_add' := fun x y => by
        apply Additive.toMul.injective
        ext
        simp [charUnit, AddChar.map_add_eq_mul] }
  let f : S →ₗ[ℤ] K := (S.subtype : S →+* K).toAddMonoidHom.toIntLinearMap
  obtain ⟨h, hh⟩ := (Module.Baer.of_divisible (Additive ℂˣ)).extension_property f Subtype.val_injective g
  refine ⟨{ toFun := fun x => ((Additive.toMul (h x) : ℂˣ) : ℂ)
            map_zero_eq_one' := by simp
            map_add_eq_mul' := fun x y => by simp [map_add (f := _)] }, fun x => ?_⟩
  have e := congrArg (fun φ => ((Additive.toMul (φ x) : ℂˣ) : ℂ)) hh
  simpa [f, g, charUnit] using e

theorem exists_localAddChar_lifting_residueChar : ∀ (D : D7) (s : ReciprocityTheory.Aut.SplitPlace D.host.E) (φ : s.v.adicCompletionIntegers (maximalRealSubfield D.host.E) →+* kP s.w), Function.Surjective φ → (∀ x, φ x = 0 ↔ Valued.v (x : s.v.adicCompletion (maximalRealSubfield D.host.E)) < 1) → ∀ ψ' : AddChar (kP s.w) ℂ, ψ' ≠ 1 → ∃ ψ₀ : AddChar (s.v.adicCompletion (maximalRealSubfield D.host.E)) ℂ, NG.IsPsi0 s ψ₀ ∧ ∀ x : s.v.adicCompletionIntegers (maximalRealSubfield D.host.E), ψ₀ (x : s.v.adicCompletion (maximalRealSubfield D.host.E)) = ψ' (φ x) := by
  intro D s φ hφs hφ0 ψ' hne
  obtain ⟨ψ₀, h⟩ := addChar_extend (s.v.adicCompletionIntegers (maximalRealSubfield D.host.E)).toSubring
    (ψ'.compAddMonoidHom φ.toAddMonoidHom)
  refine ⟨ψ₀, ⟨fun x hx => ?_, ?_⟩, fun x => h x⟩
  · have hx1 : x ∈ s.v.adicCompletionIntegers (maximalRealSubfield D.host.E) :=
      (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 hx.le
    have e1 := h ⟨x, hx1⟩
    have e2 : φ ⟨x, hx1⟩ = 0 := (hφ0 ⟨x, hx1⟩).2 hx
    rw [show ψ₀ x = ψ₀ ((⟨x, hx1⟩ : (s.v.adicCompletionIntegers (maximalRealSubfield D.host.E)).toSubring) :
      s.v.adicCompletion (maximalRealSubfield D.host.E)) from rfl, e1]
    show ψ' (φ ⟨x, hx1⟩) = 1
    rw [e2, AddChar.map_zero_eq_one]
  · obtain ⟨y, hy⟩ : ∃ y, ψ' y ≠ 1 := by
      by_contra hc
      push_neg at hc
      apply hne
      ext y
      rw [hc y, AddChar.one_apply]
    obtain ⟨x, rfl⟩ := hφs y
    refine ⟨x, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 x.2, ?_⟩
    have e1 := h x
    rw [show ψ₀ (x : s.v.adicCompletion (maximalRealSubfield D.host.E)) =
      ψ₀ ((x : (s.v.adicCompletionIntegers (maximalRealSubfield D.host.E)).toSubring) :
        s.v.adicCompletion (maximalRealSubfield D.host.E)) from rfl, e1]
    exact hy

theorem levelUni_typePlace : ∀ (D : D7) (T : Type) (L : LevCh D T) (μ0 : T), L.Is μ0 → (∀ PP, PP ∈ L.Pg ↔ ∃ k v, PP = D.naut.plGw k v) → ∀ (i : Fin D.R.m) (t : T) (hr : D.R.r ≤ D.R.nV) (ψ : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ), IsGenericPsi L.Pg ψ → ∀ s : ReciprocityTheory.Aut.SplitPlace D.host.E, s.w ∈ L.Pg → ∃ (ψ₀ : AddChar (s.v.adicCompletion (maximalRealSubfield D.host.E)) ℂ) (ξ : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ →* ℂˣ), NG.IsPsi0 s ψ₀ ∧ NG.IsCompAt (L.C.mu0 i * L.xiH t) s ξ ∧ NG.LevelUni (stdJ (datV D D.R.nV hr L.Pg (L.Q t) (P0 L.Pg D.R.r ψ) (L.chi ((i : ℕ) + 1)) (L.xiR t))) (stdX (datV D D.R.nV hr L.Pg (L.Q t) (P0 L.Pg D.R.r ψ) (L.chi ((i : ℕ) + 1)) (L.xiR t))) s D.R.r ψ₀ ξ := by
  intro D T L μ0 hL hPg i t hr ψ hψ s hs
  obtain ⟨-, -, -, h4⟩ := GlobalTheory.T.stdMaximalCompact_reduction_properties D D.R.nV
  obtain ⟨φ, hφs, hφ0, hφa, hφk⟩ := h4 s
  obtain ⟨hoffG, hoffQ, -, hunr⟩ := GlobalTheory.T.typePlace_levelPlaces_distinct_underlying D T L μ0 hL hPg t s hs
  let ψ' : AddChar (kP s.w) ℂ := (ψ s.w).compAddMonoidHom (negAddMonoidHom)
  have hne : ψ' ≠ 1 := by
    intro h1
    apply hψ s.w hs
    ext y
    have := congrArg (fun f : AddChar (kP s.w) ℂ => f (-y)) h1
    simpa [ψ'] using this
  obtain ⟨ψ₀, hP0, hψ₀⟩ := exists_localAddChar_lifting_residueChar D s φ hφs hφ0 ψ' hne
  have hres : IsRes (L.C.mu0 i * L.xiH t) s.w (L.chi ((i : ℕ) + 1) s.w)⁻¹ := by
    intro a k u hk hu
    have h1 := hL.chi i s.w hs a k u hk hu
    have ha : a ∉ s.w.asIdeal := by
      intro hm
      have : (u : kP s.w) = 0 := by rw [hu]; exact Ideal.Quotient.eq_zero_iff_mem.2 hm
      exact u.ne_zero this
    have hunit : IsUnitAt s.w (atFin s.w k) := by
      have e := GlobalTheory.ChainOnto.TameRes.val_alg s.w (k : D.host.E)
      show Valued.v (algebraMap D.host.E (s.w.adicCompletion D.host.E) (k : D.host.E)) = 1
      rw [e, hk]
      exact GlobalTheory.ChainOnto.TameRes.valuation_eq_one_of_not_mem s.w a ha
    have h2 : (L.xiH t).locK s.w k = 1 := hunr _ hunit
    have e : (L.C.mu0 i * L.xiH t).locK s.w k = (L.C.mu0 i).locK s.w k * (L.xiH t).locK s.w k := rfl
    rw [e, h2, mul_one]
    exact h1
  obtain ⟨ξ, hξc, hξr⟩ := GlobalTheory.T.exists_splitPlaceComponent_heckeChar_residue D s φ hφs hφ0 hφa _ _ hres
  refine ⟨ψ₀, ξ, hP0, hξc, ⟨GlobalTheory.T.split_place_residue_map_unit_character D hr L.Pg (L.Q t) ψ (L.chi ((i : ℕ) + 1)) (L.xiR t) s φ hφ0 hφk hs hoffG hoffQ, ?_⟩⟩
  intro κ h hκ u hu
  refine GlobalTheory.T.stdFrameLevelCharacter_at_typePlace_eq D hr L.Pg (L.Q t) ψ (L.chi ((i : ℕ) + 1)) (L.xiR t) s φ hφ0 hφk hs hoffG hoffQ ψ₀ ξ ?_ hξr κ h hκ u hu
  intro x
  rw [hψ₀ x]
  rfl

end GlobalTheory.TypeLevelUni

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelUnipotentGenericCharTypePlaceStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.MtIn
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.levelUnipotent_genericChar_typePlace : ∀ (D : D7) (T : Type) (L : LevCh D T) (μ0 : T), L.Is μ0 → (∀ PP, PP ∈ L.Pg ↔ ∃ k v, PP = D.naut.plGw k v) → ∀ (i : Fin D.R.m) (t : T) (hr : D.R.r ≤ D.R.nV) (ψ : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ), IsGenericPsi L.Pg ψ → ∀ s : ReciprocityTheory.Aut.SplitPlace D.host.E, s.w ∈ L.Pg → ∃ (ψ₀ : AddChar (s.v.adicCompletion (maximalRealSubfield D.host.E)) ℂ) (ξ : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ →* ℂˣ), NG.IsPsi0 s ψ₀ ∧ NG.IsCompAt (L.C.mu0 i * L.xiH t) s ξ ∧ NG.LevelUni (stdJ (datV D D.R.nV hr L.Pg (L.Q t) (P0 L.Pg D.R.r ψ) (L.chi ((i : ℕ) + 1)) (L.xiR t))) (stdX (datV D D.R.nV hr L.Pg (L.Q t) (P0 L.Pg D.R.r ψ) (L.chi ((i : ℕ) + 1)) (L.xiR t))) s D.R.r ψ₀ ξ := by
  first | exact @GlobalTheory.TypeLevelUni.levelUni_typePlace | exact GlobalTheory.TypeLevelUni.levelUni_typePlace | (intros; apply GlobalTheory.TypeLevelUni.levelUni_typePlace <;> assumption)
end
end
