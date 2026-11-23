module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.Tactic.Continuity
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdmissibleLagrangianTransverseField

section

@[expose] public section

open Matrix

namespace GlobalTheory

theorem lagr_functional_kills_image {k : Type} [Field k] (c : k →+* k) {n : ℕ}
    (S A C : Matrix (Fin n) (Fin n) k)
    (hiso : Aᵀ * S * C.map c + Cᵀ * S * A.map c = 0)
    (u : Fin n → k) (hu : A *ᵥ u = 0) (w : Fin n → k) :
    ((C *ᵥ u) ᵥ* S) ⬝ᵥ (c ∘ (A *ᵥ w)) = 0 := by
  have h := congrArg (fun M => u ⬝ᵥ (M *ᵥ (c ∘ w))) hiso
  simp only [add_mulVec, dotProduct_add, dotProduct_mulVec, zero_mulVec, dotProduct_zero] at h
  have e1 : u ᵥ* (Aᵀ * S * C.map c) = 0 := by
    rw [← vecMul_vecMul, ← vecMul_vecMul, vecMul_transpose, hu, zero_vecMul, zero_vecMul]
  have e2 : u ᵥ* (Cᵀ * S * A.map c) ⬝ᵥ (c ∘ w) = ((C *ᵥ u) ᵥ* S) ⬝ᵥ (c ∘ (A *ᵥ w)) := by
    rw [← vecMul_vecMul, ← dotProduct_mulVec, ← vecMul_vecMul, vecMul_transpose]
    congr 1
    funext i
    exact (RingHom.map_mulVec c A w i).symm
  rw [e1, zero_dotProduct, zero_add, e2] at h
  exact h

def lagrRankOne {k : Type} [Field k] {n : ℕ} (S : Matrix (Fin n) (Fin n) k) (j : Fin n) :
    Matrix (Fin n) (Fin n) k :=
  Matrix.of fun a b => if a = j then S b j else 0

theorem lagrRankOne_adm {k : Type} [Field k] (c : k →+* k) {n : ℕ}
    (S : Matrix (Fin n) (Fin n) k) (hS : Sᵀ = -S.map c) (j : Fin n) :
    (lagrRankOne S j)ᵀ * S + S * (lagrRankOne S j).map c = 0 := by
  ext a b
  have h1 : c (S b j) = - S j b := by
    have h2 : Sᵀ b j = (-S.map c) b j := by rw [hS]
    rw [transpose_apply, Matrix.neg_apply, Matrix.map_apply] at h2
    rw [h2, neg_neg]
  have h3 : ∀ l, c (if l = j then S b j else 0) = if l = j then c (S b j) else 0 := by
    intro l; split_ifs <;> simp
  simp [Matrix.mul_apply, lagrRankOne, h3, h1]

theorem lagrRankOne_mulVec {k : Type} [Field k] {n : ℕ}
    (S : Matrix (Fin n) (Fin n) k) (j : Fin n) (v : Fin n → k) :
    lagrRankOne S j *ᵥ v = Pi.single j ((v ᵥ* S) j) := by
  funext a
  by_cases h : a = j
  · subst h; simp [lagrRankOne, mulVec, vecMul, dotProduct, mul_comm]
  · simp [lagrRankOne, mulVec, dotProduct, h]

theorem lagr_step {k : Type} [Field k] (c : k →+* k) {n : ℕ}
    (S : Matrix (Fin n) (Fin n) k) (hSu : IsUnit S.det)
    (A C : Matrix (Fin n) (Fin n) k)
    (hinj : ∀ u : Fin n → k, A *ᵥ u = 0 → C *ᵥ u = 0 → u = 0)
    (hiso : Aᵀ * S * C.map c + Cᵀ * S * A.map c = 0)
    (u : Fin n → k) (hu0 : u ≠ 0) (hu : A *ᵥ u = 0) :
    ∃ j : Fin n, (∀ w, (A + lagrRankOne S j * C) *ᵥ w = 0 → A *ᵥ w = 0) ∧
      (A + lagrRankOne S j * C) *ᵥ u ≠ 0 := by
  have hx : C *ᵥ u ≠ 0 := fun h => hu0 (hinj u hu h)
  have hxS : (C *ᵥ u) ᵥ* S ≠ 0 := by
    intro h
    have hI : Function.Injective fun v : Fin n → k => v ᵥ* S :=
      vecMul_injective_iff_isUnit.mpr ((isUnit_iff_isUnit_det S).mpr hSu)
    apply hx
    apply hI
    simp only [h, zero_vecMul]
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hxS
  simp only [Pi.zero_apply] at hj
  refine ⟨j, ?_, ?_⟩
  · intro w hw
    rw [add_mulVec, ← mulVec_mulVec, lagrRankOne_mulVec] at hw
    set t := ((C *ᵥ w) ᵥ* S) j with ht
    have hAw : A *ᵥ w = - Pi.single j t := eq_neg_of_add_eq_zero_left hw
    have hφ := lagr_functional_kills_image c S A C hiso u hu w
    have hc : (c ∘ (A *ᵥ w)) = Pi.single j (-(c t)) := by
      rw [hAw]
      funext i
      by_cases hi : i = j
      · subst hi; simp
      · simp [hi]
    rw [hc, dotProduct_single] at hφ
    have hct : c t = 0 := by
      rcases mul_eq_zero.mp hφ with h | h
      · exact absurd h hj
      · exact neg_eq_zero.mp h
    have ht0 : t = 0 := (map_eq_zero c).mp hct
    rw [hAw, ht0, Pi.single_zero, neg_zero]
  · rw [add_mulVec, ← mulVec_mulVec, lagrRankOne_mulVec, hu, zero_add]
    intro h
    have := congrFun h j
    simp only [Pi.single_eq_same, Pi.zero_apply] at this
    exact hj this

theorem lagr_iso_update {k : Type} [Field k] (c : k →+* k) {n : ℕ}
    (S A C X : Matrix (Fin n) (Fin n) k)
    (hX : Xᵀ * S + S * X.map c = 0)
    (hiso : Aᵀ * S * C.map c + Cᵀ * S * A.map c = 0) :
    (A + X * C)ᵀ * S * C.map c + Cᵀ * S * (A + X * C).map c = 0 := by
  have e : (A + X * C)ᵀ * S * C.map c + Cᵀ * S * (A + X * C).map c =
      (Aᵀ * S * C.map c + Cᵀ * S * A.map c) + Cᵀ * (Xᵀ * S + S * X.map c) * C.map c := by
    rw [Matrix.map_add c (map_add c)]
    simp only [transpose_add, transpose_mul, Matrix.map_mul, Matrix.mul_add,
      Matrix.add_mul, Matrix.mul_assoc]
    abel
  rw [e, hiso, hX, Matrix.mul_zero, Matrix.zero_mul, add_zero]

theorem transpose_mul_add_mul_map_eq_zero_add {k : Type} [Field k] (c : k →+* k) {n : ℕ}
    (S X Y : Matrix (Fin n) (Fin n) k)
    (hX : Xᵀ * S + S * X.map c = 0) (hY : Yᵀ * S + S * Y.map c = 0) :
    (X + Y)ᵀ * S + S * (X + Y).map c = 0 := by
  have e : (X + Y)ᵀ * S + S * (X + Y).map c = (Xᵀ * S + S * X.map c) + (Yᵀ * S + S * Y.map c) := by
    rw [Matrix.map_add c (map_add c)]
    simp only [transpose_add, Matrix.mul_add, Matrix.add_mul]
    abel
  rw [e, hX, hY, add_zero]

theorem lagrangian_transverse_field :
    ∀ {k : Type} [Field k] (c : k →+* k), (∀ x, c (c x) = x) → (2 : k) ≠ 0 →
    ∀ {n : ℕ} (S : Matrix (Fin n) (Fin n) k), IsUnit S.det → Sᵀ = -S.map c →
    ∀ (A C : Matrix (Fin n) (Fin n) k), (∀ u : Fin n → k, A *ᵥ u = 0 → C *ᵥ u = 0 → u = 0) →
      Aᵀ * S * C.map c + Cᵀ * S * A.map c = 0 →
      ∃ X : Matrix (Fin n) (Fin n) k, Xᵀ * S + S * X.map c = 0 ∧ IsUnit (A + X * C).det := by
  intro k _ c _ _ n S hSu hS A C hinj hiso
  suffices H : ∀ m : ℕ, ∀ A : Matrix (Fin n) (Fin n) k,
      Module.finrank k (LinearMap.ker A.mulVecLin) < m →
      (∀ u : Fin n → k, A *ᵥ u = 0 → C *ᵥ u = 0 → u = 0) →
      Aᵀ * S * C.map c + Cᵀ * S * A.map c = 0 →
      ∃ X : Matrix (Fin n) (Fin n) k, Xᵀ * S + S * X.map c = 0 ∧ IsUnit (A + X * C).det from
    H _ A (Nat.lt_succ_self _) hinj hiso
  intro m
  induction m with
  | zero => intro A h; exact absurd h (Nat.not_lt_zero _)
  | succ m ih =>
    intro A hm hinj hiso
    by_cases hdet : IsUnit A.det
    · exact ⟨0, by simp, by simpa using hdet⟩
    · have hd : A.det = 0 := by simpa [isUnit_iff_ne_zero] using hdet
      obtain ⟨u, hu0, hu⟩ := exists_mulVec_eq_zero_iff.mpr hd
      obtain ⟨j, hker, hne⟩ := lagr_step c S hSu A C hinj hiso u hu0 hu
      have hX1 := lagrRankOne_adm c S hS j
      have hlt : LinearMap.ker (A + lagrRankOne S j * C).mulVecLin <
          LinearMap.ker A.mulVecLin := by
        refine lt_of_le_of_ne ?_ ?_
        · intro w hw
          simp only [LinearMap.mem_ker, mulVecLin_apply] at hw ⊢
          exact hker w hw
        · intro heq
          apply hne
          have hmem : u ∈ LinearMap.ker A.mulVecLin := by
            simpa [LinearMap.mem_ker, mulVecLin_apply] using hu
          rw [← heq] at hmem
          rw [LinearMap.mem_ker, mulVecLin_apply] at hmem
          exact hmem
      have hfin := Submodule.finrank_lt_finrank_of_lt hlt
      have hinj' : ∀ w : Fin n → k, (A + lagrRankOne S j * C) *ᵥ w = 0 → C *ᵥ w = 0 → w = 0 := by
        intro w h1 h2
        apply hinj w _ h2
        rw [add_mulVec, ← mulVec_mulVec, h2, mulVec_zero, add_zero] at h1
        exact h1
      obtain ⟨X2, hX2, hdet2⟩ := ih (A + lagrRankOne S j * C) (by omega) hinj'
        (lagr_iso_update c S A C _ hX1 hiso)
      refine ⟨lagrRankOne S j + X2, transpose_mul_add_mul_map_eq_zero_add c S _ _ hX1 hX2, ?_⟩
      rwa [Matrix.add_mul, ← add_assoc]

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdmissibleLagrangianTransverseFieldStatement

section

@[expose] public section

open Matrix

theorem _root_.GlobalTheory.T.exists_admissible_lagrangian_transverse_field : ∀ {k : Type} [Field k] (c : k →+* k), (∀ x, c (c x) = x) → (2 : k) ≠ 0 →
    ∀ {n : ℕ} (S : Matrix (Fin n) (Fin n) k), IsUnit S.det → Sᵀ = -S.map c →
    ∀ (A C : Matrix (Fin n) (Fin n) k), (∀ u : Fin n → k, A *ᵥ u = 0 → C *ᵥ u = 0 → u = 0) →
      Aᵀ * S * C.map c + Cᵀ * S * A.map c = 0 →
      ∃ X : Matrix (Fin n) (Fin n) k, Xᵀ * S + S * X.map c = 0 ∧ IsUnit (A + X * C).det := by
  first | exact @GlobalTheory.lagrangian_transverse_field | exact GlobalTheory.lagrangian_transverse_field | (intros; apply GlobalTheory.lagrangian_transverse_field <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdmissibleIsUnitDetLocalInvolution

section

@[expose] public section

open Matrix

namespace GlobalTheory.LocalLift

def invEquiv {O : Type} [CommRing O] (c : O →+* O) (hc : ∀ x, c (c x) = x) : O ≃+* O :=
  { c with invFun := c, left_inv := hc, right_inv := hc }

noncomputable def resInv {O : Type} [CommRing O] [IsLocalRing O] (c : O →+* O) (hc : ∀ x, c (c x) = x) :
    IsLocalRing.ResidueField O →+* IsLocalRing.ResidueField O :=
  (IsLocalRing.ResidueField.mapEquiv (invEquiv c hc)).toRingHom

theorem resInv_residue {O : Type} [CommRing O] [IsLocalRing O] (c : O →+* O)
    (hc : ∀ x, c (c x) = x) (x : O) :
    resInv c hc (IsLocalRing.residue O x) = IsLocalRing.residue O (c x) := by
  simp only [resInv, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    IsLocalRing.ResidueField.mapEquiv_apply, IsLocalRing.ResidueField.map_residue]
  rfl

theorem lift_of_field
    (hF : ∀ {k : Type} [Field k] (c : k →+* k), (∀ x, c (c x) = x) → (2 : k) ≠ 0 →
      ∀ {n : ℕ} (S : Matrix (Fin n) (Fin n) k), IsUnit S.det → Sᵀ = -S.map c →
      ∀ (A C : Matrix (Fin n) (Fin n) k), (∀ u : Fin n → k, A *ᵥ u = 0 → C *ᵥ u = 0 → u = 0) →
        Aᵀ * S * C.map c + Cᵀ * S * A.map c = 0 →
        ∃ X : Matrix (Fin n) (Fin n) k, Xᵀ * S + S * X.map c = 0 ∧ IsUnit (A + X * C).det) :
    ∀ {O : Type} [CommRing O] [IsLocalRing O] (c : O →+* O), (∀ x, c (c x) = x) → IsUnit (2 : O) →
    ∀ {n : ℕ} (S : Matrix (Fin n) (Fin n) O), IsUnit S.det → Sᵀ = -S.map c →
    ∀ (A B C D : Matrix (Fin n) (Fin n) O), IsUnit (Matrix.fromBlocks A B C D).det →
      (Matrix.fromBlocks A B C D)ᵀ * Matrix.fromBlocks 0 S S 0 * (Matrix.fromBlocks A B C D).map c =
        Matrix.fromBlocks 0 S S 0 →
      ∃ X : Matrix (Fin n) (Fin n) O, Xᵀ * S + S * X.map c = 0 ∧ IsUnit (A + X * C).det := by
  intro O _ _ c hc h2 n S hS hSc A B C D hdet hU
  set π := IsLocalRing.residue O with hπ
  set cb := resInv c hc with hcbdef
  have hcb : ∀ x, cb (π x) = π (c x) := resInv_residue c hc
  have hcbM : ∀ M : Matrix (Fin n) (Fin n) O, (M.map c).map π = (M.map π).map cb := by
    intro M; ext i j; simp [hcb]
  have hcbb : ∀ x, cb (cb x) = x := by
    intro x; obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective x
    show cb (cb (π y)) = π y
    rw [hcb, hcb, hc]
  have h2k : (2 : IsLocalRing.ResidueField O) ≠ 0 := by
    have := (h2.map π).ne_zero; rwa [map_ofNat] at this
  have hSk : IsUnit (S.map π).det := by
    have := hS.map π; rwa [RingHom.map_det] at this
  have hSck : (S.map π)ᵀ = -(S.map π).map cb := by
    rw [← hcbM, ← Matrix.transpose_map, hSc]; ext i j; simp
  have h11 : Aᵀ * S * C.map c + Cᵀ * S * A.map c = 0 := by
    rw [fromBlocks_transpose, fromBlocks_map, fromBlocks_multiply, fromBlocks_multiply] at hU
    have := (Matrix.fromBlocks_inj.1 hU).1
    simp only [Matrix.mul_zero, Matrix.zero_mul, zero_add, add_zero] at this
    rw [add_comm]; simpa [Matrix.mul_assoc] using this
  have hinj : ∀ u, (A.map π) *ᵥ u = 0 → (C.map π) *ᵥ u = 0 → u = 0 := by
    intro u hA hC
    have hd : ((fromBlocks A B C D).map π).det ≠ 0 := by
      have := (hdet.map π).ne_zero; rwa [RingHom.map_det] at this
    have := Matrix.eq_zero_of_mulVec_eq_zero hd (v := Sum.elim u 0) (by
      rw [fromBlocks_map, fromBlocks_mulVec]; ext (i | i) <;> simp [hA, hC])
    funext i; simpa using congrFun this (Sum.inl i)
  have hiso : (A.map π)ᵀ * S.map π * (C.map π).map cb + (C.map π)ᵀ * S.map π * (A.map π).map cb = 0 := by
    have : (Aᵀ * S * C.map c + Cᵀ * S * A.map c).map π = 0 := by rw [h11]; ext; simp
    rw [Matrix.map_add _ (map_add π), Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul,
      Matrix.transpose_map, Matrix.transpose_map, hcbM, hcbM] at this
    exact this
  obtain ⟨Xb, hXadm, hXunit⟩ := hF cb hcbb h2k (S.map π) hSk hSck (A.map π) (C.map π) hinj hiso

  obtain ⟨X0, hX0⟩ : ∃ X0 : Matrix (Fin n) (Fin n) O, X0.map π = Xb :=
    ⟨Xb.map (fun x => (IsLocalRing.residue_surjective x).choose), by
      ext i j; exact (IsLocalRing.residue_surjective (Xb i j)).choose_spec⟩
  obtain ⟨h, hh⟩ := h2.exists_right_inv
  have hch : c h = h := by
    have h' : c 2 * c h = 1 := by rw [← map_mul, hh, map_one]
    rw [map_ofNat] at h'
    calc c h = (h * 2) * c h := by rw [mul_comm h 2, hh, one_mul]
      _ = h * (2 * c h) := by ring
      _ = h := by rw [h', mul_one]
  set Z0 := X0ᵀ * S with hZ0
  set Z := h • (Z0 + (Z0.map c)ᵀ) with hZ
  have hZh : (Z.map c)ᵀ = Z := by
    ext i j; simp only [hZ, Matrix.transpose_apply, Matrix.map_apply, Matrix.smul_apply,
      Matrix.add_apply, smul_eq_mul, map_mul, map_add, hch, hc]; ring
  set X := (Z * S⁻¹)ᵀ with hX
  have hSt : (S.map c)ᵀ = -S := by
    have : S.map c = -Sᵀ := by rw [hSc, neg_neg]
    rw [this, Matrix.transpose_neg, Matrix.transpose_transpose]
  have hSinv : S * (S⁻¹.map c)ᵀ = -1 := by
    have h1 : (S⁻¹.map c) * (S.map c) = 1 := by
      rw [← Matrix.map_mul, Matrix.nonsing_inv_mul S hS]; exact Matrix.map_one _ (map_zero c) (map_one c)
    have h2' := congrArg Matrix.transpose h1
    rw [Matrix.transpose_mul, Matrix.transpose_one, hSt, Matrix.neg_mul] at h2'
    rw [← neg_neg (S * _), h2']
  have hXS : Xᵀ * S = Z := by
    rw [hX, Matrix.transpose_transpose, Matrix.mul_assoc, Matrix.nonsing_inv_mul S hS, Matrix.mul_one]
  have hXc : X.map c = (S⁻¹.map c)ᵀ * Z := by
    rw [hX, Matrix.transpose_map, Matrix.map_mul, Matrix.transpose_mul, hZh]
  refine ⟨X, ?_, ?_⟩
  · rw [hXS, hXc, ← Matrix.mul_assoc, hSinv, Matrix.neg_mul, Matrix.one_mul, add_neg_cancel]
  · have hSbt : ((S.map π).map cb)ᵀ = -S.map π := by
      have : (S.map π).map cb = -(S.map π)ᵀ := by rw [hSck, neg_neg]
      rw [this, Matrix.transpose_neg, Matrix.transpose_transpose]
    have hZb : ((Xbᵀ * S.map π).map cb)ᵀ = Xbᵀ * S.map π := by
      rw [Matrix.map_mul, Matrix.transpose_mul, hSbt, ← Matrix.transpose_map, Matrix.transpose_transpose,
        Matrix.neg_mul]
      exact (eq_neg_of_add_eq_zero_left hXadm).symm
    have hZ0b : Z0.map π = Xbᵀ * S.map π := by
      rw [hZ0, Matrix.map_mul, Matrix.transpose_map, hX0]
    have hZm : Z.map π = π h • (Z0.map π + ((Z0.map c).map π)ᵀ) := by
      ext i j
      simp only [hZ, Matrix.map_apply, Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply,
        smul_eq_mul, map_mul, map_add]
    have hZπ : Z.map π = Xbᵀ * S.map π := by
      have h2h : π h * 2 = 1 := by rw [← map_ofNat π 2, ← map_mul, mul_comm, hh, map_one]
      rw [hZm, hcbM, hZ0b, hZb, ← two_smul (IsLocalRing.ResidueField O) (Xbᵀ * S.map π), smul_smul, h2h,
        one_smul]
    have hXπ : X.map π = Xb := by
      have hmm : (X.map π)ᵀ * S.map π = (Xᵀ * S).map π := by
        ext i j

        simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, map_sum, map_mul]
      have e : (X.map π)ᵀ * S.map π = Xbᵀ * S.map π := by
        calc (X.map π)ᵀ * S.map π = (Xᵀ * S).map π := hmm
          _ = Z.map π := by rw [hXS]
          _ = Xbᵀ * S.map π := hZπ
      have e' := congrArg (· * (S.map π)⁻¹) e
      simp only [Matrix.mul_nonsing_inv_cancel_right _ _ hSk] at e'
      exact Matrix.transpose_inj.1 e'
    apply isUnit_of_map_unit π
    rw [RingHom.map_det, RingHom.mapMatrix_apply, Matrix.map_add _ (map_add π), Matrix.map_mul, hXπ]
    exact hXunit

theorem exists_admissible_isUnit_det :
    ∀ {O : Type} [CommRing O] [IsLocalRing O] (c : O →+* O), (∀ x, c (c x) = x) → IsUnit (2 : O) →
    ∀ {n : ℕ} (S : Matrix (Fin n) (Fin n) O), IsUnit S.det → Sᵀ = -S.map c →
    ∀ (A B C D : Matrix (Fin n) (Fin n) O), IsUnit (Matrix.fromBlocks A B C D).det →
      (Matrix.fromBlocks A B C D)ᵀ * Matrix.fromBlocks 0 S S 0 * (Matrix.fromBlocks A B C D).map c =
        Matrix.fromBlocks 0 S S 0 →
      ∃ X : Matrix (Fin n) (Fin n) O, Xᵀ * S + S * X.map c = 0 ∧ IsUnit (A + X * C).det :=
  lift_of_field GlobalTheory.T.exists_admissible_lagrangian_transverse_field

end GlobalTheory.LocalLift
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdmissibleIsUnitDetLocalInvolutionStatement

section

@[expose] public section

open Matrix

theorem _root_.GlobalTheory.T.exists_admissible_isUnit_det_local_involution : ∀ {O : Type} [CommRing O] [IsLocalRing O] (c : O →+* O), (∀ x, c (c x) = x) → IsUnit (2 : O) →
    ∀ {n : ℕ} (S : Matrix (Fin n) (Fin n) O), IsUnit S.det → Sᵀ = -S.map c →
    ∀ (A B C D : Matrix (Fin n) (Fin n) O), IsUnit (Matrix.fromBlocks A B C D).det →
      (Matrix.fromBlocks A B C D)ᵀ * Matrix.fromBlocks 0 S S 0 * (Matrix.fromBlocks A B C D).map c =
        Matrix.fromBlocks 0 S S 0 →
      ∃ X : Matrix (Fin n) (Fin n) O, Xᵀ * S + S * X.map c = 0 ∧ IsUnit (A + X * C).det := by
  first | exact @GlobalTheory.LocalLift.exists_admissible_isUnit_det | exact GlobalTheory.LocalLift.exists_admissible_isUnit_det | (intros; apply GlobalTheory.LocalLift.exists_admissible_isUnit_det <;> assumption)
end
end
