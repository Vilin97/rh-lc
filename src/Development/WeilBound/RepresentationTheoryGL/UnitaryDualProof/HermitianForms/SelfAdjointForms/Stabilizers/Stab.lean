module

public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.SelfAdjointForms.Stabilizers.AnnAnti
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.SelfAdjointForms.Stabilizers.ConjCircleEqOne
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.SelfAdjointForms.Stabilizers.ExistsBallPf
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalizedAbsCharacterization
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
import Mathlib.RingTheory.Henselian
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

-- Source module: Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.SelfAdjointForms.Stabilizers.VmvMulVecApply

section

@[expose] public section

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.BZMir ValuativeRel

namespace PositivityTheory.RgUd.Form.LeviSmoothness.stab

open PositivityTheory.RgUd.Form PositivityTheory.RgUd.Form.ColumnElementGluing PositivityTheory.RgUd.Form.LeviSmoothness

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem vmv_sq {m : ℕ} (η : Fin (m + 1) → k) :
    vecMulVec (xi0 k m) η * vecMulVec (xi0 k m) η = η (Fin.last m) • vecMulVec (xi0 k m) η := by
  ext i j
  simp [Matrix.mul_apply, vecMulVec_apply, xi0, Pi.single_apply, mul_comm, mul_left_comm]

theorem inv_pair {m : ℕ} (E : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (a c : k) (hE : E * E = a • E)
    (hc : c * (1 + a) = 1) : (1 + E) * (1 - c • E) = 1 ∧ (1 - c • E) * (1 + E) = 1 := by
  have h : E = c • E + (c * a) • E := by
    rw [← add_smul, ← mul_one_add, hc, one_smul]
  constructor
  · rw [add_mul, one_mul, mul_sub, mul_one, mul_smul_comm, hE, smul_smul]
    have h2 : E - (c * a) • E = c • E := by
      rw [sub_eq_iff_eq_add]
      exact h
    rw [sub_add_eq_add_sub, add_sub_assoc, h2, sub_self, add_zero]
  · rw [sub_mul, one_mul, mul_add, mul_one, smul_mul_assoc, hE, smul_smul, ← h, add_sub_cancel_right]

def gU {m : ℕ} (η : Fin (m + 1) → k) (hη : 1 + η (Fin.last m) ≠ 0) : GL (Fin (m + 1)) k :=
  ⟨1 + vecMulVec (xi0 k m) η, 1 - (1 + η (Fin.last m))⁻¹ • vecMulVec (xi0 k m) η,
    (inv_pair _ _ _ (vmv_sq η) (inv_mul_cancel₀ hη)).1, (inv_pair _ _ _ (vmv_sq η) (inv_mul_cancel₀ hη)).2⟩

theorem gU_val {m : ℕ} (η : Fin (m + 1) → k) (hη : 1 + η (Fin.last m) ≠ 0) :
    ((gU η hη : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) = 1 + vecMulVec (xi0 k m) η := rfl

theorem gU_inv_val {m : ℕ} (η : Fin (m + 1) → k) (hη : 1 + η (Fin.last m) ≠ 0) :
    (((gU η hη)⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) =
      1 - (1 + η (Fin.last m))⁻¹ • vecMulVec (xi0 k m) η := rfl

theorem gU_transpose {m : ℕ} (η : Fin (m + 1) → k) (hη : 1 + η (Fin.last m) ≠ 0) :
    ((gU η hη : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k)ᵀ *ᵥ xi0 k m = xi0 k m + η := by
  funext i
  simp [gU_val, Matrix.transpose_add, Matrix.add_mulVec, Matrix.transpose_vecMulVec, Matrix.mulVec,
    dotProduct, vecMulVec_apply, xi0, Pi.single_apply]
  by_cases h : i = Fin.last m
  · subst h
    simp
  · simp [h, Matrix.one_apply_ne (Ne.symm h)]

theorem gU_det {m : ℕ} (η : Fin (m + 1) → k) (hη : 1 + η (Fin.last m) ≠ 0) :
    ((Matrix.GeneralLinearGroup.det (gU η hη) : kˣ) : k) = 1 + η (Fin.last m) := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, gU_val, vecMulVec_eq Unit,
    det_one_add_replicateCol_mul_replicateRow]
  simp [xi0, dotProduct_single]

theorem val_dot_le {n : ℕ} (a x : Fin n → k) (γ : ValueGroupWithZero k) (ha : ∀ i, valuation k (a i) ≤ 1)
    (hx : ∀ i, valuation k (x i) ≤ γ) : valuation k (a ⬝ᵥ x) ≤ γ := by
  simp only [dotProduct]
  refine Valuation.map_sum_le _ (fun i _ => ?_)
  rw [Valuation.map_mul]
  calc _ ≤ 1 * γ := mul_le_mul' (ha i) (hx i)
    _ = γ := one_mul γ

theorem vmv_mulVec_apply {m : ℕ} (u v w : Fin (m + 1) → k) (i : Fin (m + 1)) :
    (vecMulVec u v *ᵥ w) i = u i * (v ⬝ᵥ w) := by
  simp [mulVec, vecMulVec, dotProduct, Finset.mul_sum, mul_assoc]

theorem mem_ball_of {m : ℕ} (c : k) (η x : Fin (m + 1) → k) (hc : valuation k c ≤ 1) (hη : ∀ i, valuation k (η i) ≤ 1)
    (s : kˣ) (hx : x ∈ ball (m + 1) s) : (1 + c • vecMulVec (xi0 k m) η) *ᵥ x ∈ ball (m + 1) s := by
  have hx' : ∀ i, valuation k (x i) ≤ valuation k (s : k) := hx
  show ∀ i, valuation k (((1 + c • vecMulVec (xi0 k m) η) *ᵥ x) i) ≤ valuation k (s : k)
  intro i
  rw [Matrix.add_mulVec, Matrix.one_mulVec, Pi.add_apply, Matrix.smul_mulVec, Pi.smul_apply,
    vmv_mulVec_apply, smul_eq_mul]
  refine Valuation.map_add_le _ (hx' i) ?_
  rw [Valuation.map_mul, Valuation.map_mul]
  have hu : valuation k (xi0 k m i) ≤ 1 := by
    unfold xi0
    rw [Pi.single_apply]
    split_ifs <;> simp
  have hd := val_dot_le η x _ hη hx'
  calc _ ≤ 1 * (1 * valuation k (s : k)) := mul_le_mul' hc (mul_le_mul' hu hd)
    _ = _ := by rw [one_mul, one_mul]

theorem good_nbhd_pf {m : ℕ} (K : Subgroup (GL (Fin (m + 1)) k)) (hK : IsOpen (K : Set (GL (Fin (m + 1)) k))) :
    ∃ D ∈ nhds (0 : Fin (m + 1) → k), ∀ η ∈ D, ∃ g ∈ K, nabs k (Matrix.GeneralLinearGroup.det g) = 1 ∧
      (∀ s : kˣ, pre g⁻¹ (ball (m + 1) s) = ball (m + 1) s) ∧
      ((g⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k)ᵀ *ᵥ xi0 k m = xi0 k m + η := by
  have hv : {x : k | valuation k x < 1} ∈ nhds (0 : k) :=
    (IsValuativeTopology.mem_nhds_zero_iff _).2 ⟨1, fun x hx => by simpa using hx⟩
  have hS : {η : Fin (m + 1) → k | ∀ i, valuation k (η i) < 1} ∈ nhds (0 : Fin (m + 1) → k) := by
    simp only [Set.setOf_forall]
    refine Filter.iInter_mem.2 fun i => ?_
    have h1 : (fun η : Fin (m + 1) → k => η i) ⁻¹' {x : k | valuation k x < 1} ∈
        nhds (0 : Fin (m + 1) → k) :=
      ((continuous_apply i).tendsto (0 : Fin (m + 1) → k)) hv
    exact h1
  obtain ⟨U, hU, hUK⟩ := isOpen_induced_iff.1 hK
  let F : (Fin (m + 1) → k) →
      Matrix (Fin (m + 1)) (Fin (m + 1)) k × (Matrix (Fin (m + 1)) (Fin (m + 1)) k)ᵐᵒᵖ :=
    fun η => (1 + vecMulVec (xi0 k m) η,
      MulOpposite.op (1 - (1 + η (Fin.last m))⁻¹ • vecMulVec (xi0 k m) η))
  have hF : ContinuousAt F 0 := by
    have hE : Continuous fun η : Fin (m + 1) → k => vecMulVec (xi0 k m) η :=
      Continuous.matrix_vecMulVec continuous_const continuous_id
    have h2 : ContinuousAt (fun η : Fin (m + 1) → k => (1 + η (Fin.last m))⁻¹) 0 :=
      ContinuousAt.inv₀ (continuous_const.add (continuous_apply _)).continuousAt (by simp)
    have h3 : ContinuousAt
        (fun η : Fin (m + 1) → k => 1 - (1 + η (Fin.last m))⁻¹ • vecMulVec (xi0 k m) η) 0 :=
      continuousAt_const.sub (h2.smul hE.continuousAt)
    exact ContinuousAt.prodMk (continuous_const.add hE).continuousAt
      (MulOpposite.continuous_op.continuousAt.comp h3)
  have h0 : F 0 ∈ U := by
    have h1 : (1 : GL (Fin (m + 1)) k) ∈ (K : Set (GL (Fin (m + 1)) k)) := K.one_mem
    rw [← hUK] at h1
    have e : F 0 = Units.embedProduct _ (1 : GL (Fin (m + 1)) k) :=
      Prod.ext (by simp [F]) (MulOpposite.unop_injective (by simp [F]))
    rw [e]
    exact h1
  refine ⟨F ⁻¹' U ∩ {η | ∀ i, valuation k (η i) < 1},
    Filter.inter_mem (hF.preimage_mem_nhds (hU.mem_nhds h0)) hS, ?_⟩
  rintro η ⟨hηU, hηv⟩
  have hl : valuation k (1 + η (Fin.last m)) = 1 := Valuation.map_one_add_of_lt _ (hηv _)
  have hne : 1 + η (Fin.last m) ≠ 0 := by
    intro h
    rw [h, map_zero] at hl
    exact zero_ne_one hl
  have hη1 : ∀ i, valuation k (η i) ≤ 1 := fun i => (hηv i).le
  refine ⟨(gU η hne)⁻¹, ?_, ?_, ?_, ?_⟩
  · apply K.inv_mem
    have e : Units.embedProduct _ (gU η hne) = F η :=
      Prod.ext (gU_val η hne) (MulOpposite.unop_injective (gU_inv_val η hne))
    have h1 : gU η hne ∈ Units.embedProduct _ ⁻¹' U := by
      show Units.embedProduct _ (gU η hne) ∈ U
      rw [e]
      exact hηU
    rw [hUK] at h1
    exact h1
  · rw [GlobalTheory.SplitWeil.nabs_eq_one_iff, map_inv, Units.val_inv_eq_inv_val, gU_det, map_inv₀, hl, inv_one]
  · intro s
    rw [inv_inv]
    ext x
    simp only [pre, AddSubgroup.mem_comap, LinearMap.toAddMonoidHom_coe, Matrix.mulVecLin_apply, gU_val]
    constructor
    · intro hx
      have hc' : valuation k (-(1 + η (Fin.last m))⁻¹) ≤ 1 := by
        rw [Valuation.map_neg, map_inv₀, hl, inv_one]
      have hmul : (1 + (-(1 + η (Fin.last m))⁻¹) • vecMulVec (xi0 k m) η) *
          (1 + vecMulVec (xi0 k m) η) = 1 := by
        rw [neg_smul, ← sub_eq_add_neg]
        exact (inv_pair _ _ _ (vmv_sq η) (inv_mul_cancel₀ hne)).2
      have h1 := mem_ball_of _ η _ hc' hη1 s hx
      rwa [Matrix.mulVec_mulVec, hmul, Matrix.one_mulVec] at h1
    · intro hx
      have h1 := mem_ball_of 1 η x (map_one (valuation k)).le hη1 s hx
      rwa [one_smul] at h1
  · rw [inv_inv]
    exact gU_transpose η hne

end PositivityTheory.RgUd.Form.LeviSmoothness.stab
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.SelfAdjointForms.Stabilizers.Stab

section

@[expose] public section

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.BZMir ValuativeRel

namespace PositivityTheory.RgUd.Form.LeviSmoothness.stab

open PositivityTheory.RgUd.Form PositivityTheory.RgUd.Form.ColumnElementGluing PositivityTheory.RgUd.Form.LeviSmoothness

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section
variable {ψ : AddChar k Circle} {m N : ℕ} {h : m + 2 ≤ N} {V : Type} [AddCommGroup V] [Module ℂ V]
  {π : Representation ℂ (GL (Fin N) k) V} {s : ℝ} {B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ}

private theorem exists_tr_lemma {n : ℕ} (C D : AddSubgroup (Fin n → k)) (hC : IsCompact (C : Set (Fin n → k)))
    (hD : IsOpen (D : Set (Fin n → k))) :
    ∃ T : Finset (Fin n → k), IsTr C D T ∧ T.card = D.relIndex C := by
  classical
  have : CompactSpace C := isCompact_iff_compactSpace.mp hC
  have hfin : Finite (C ⧸ D.addSubgroupOf C) :=
    AddSubgroup.quotient_finite_of_isOpen _ (hD.preimage continuous_subtype_val)
  have := Fintype.ofFinite (C ⧸ D.addSubgroupOf C)
  let f : (C ⧸ D.addSubgroupOf C) → Fin n → k := fun q => ((Quotient.out q : C) : Fin n → k)
  have hf : Function.Injective f := by
    intro q q' e
    have e' : Quotient.out q = Quotient.out q' := Subtype.ext e
    rw [← QuotientAddGroup.out_eq' q, ← QuotientAddGroup.out_eq' q', e']
  refine ⟨Finset.univ.image f, ⟨fun t ht => ?_, fun a ha => ?_⟩, ?_⟩
  · obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 ht
    exact (Quotient.out q).2
  · set q : C ⧸ D.addSubgroupOf C := QuotientAddGroup.mk ⟨a, ha⟩ with hqd
    have hq : -(Quotient.out q) + ⟨a, ha⟩ ∈ D.addSubgroupOf C :=
      QuotientAddGroup.eq.1 (QuotientAddGroup.out_eq' q)
    refine ⟨f q, ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩, ?_⟩
    · have hm := AddSubgroup.mem_addSubgroupOf.1 hq
      have e : a - f q = -((Quotient.out q : C) : Fin n → k) + a := by
        simp only [f]
        abel
      rw [e]
      simpa using hm
    · rintro y ⟨hy, hyd⟩
      obtain ⟨q', -, rfl⟩ := Finset.mem_image.1 hy
      congr 1
      rw [← QuotientAddGroup.out_eq' q', hqd]
      apply QuotientAddGroup.eq.2
      rw [AddSubgroup.mem_addSubgroupOf]
      have e : -((Quotient.out q' : C) : Fin n → k) + a = a - f q' := by
        simp only [f]
        abel
      simpa [e] using hyd
  · rw [Finset.card_image_of_injective _ hf, Finset.card_univ, AddSubgroup.relIndex, AddSubgroup.index_eq_card,
      Nat.card_eq_fintype_card]

theorem key' (hB : Lv ψ h π s B) (K : Subgroup (GL (Fin (m + 1)) k)) (D : Set (Fin (m + 1) → k))
    (hDK : ∀ η ∈ D, ∃ g ∈ K, nabs k (Matrix.GeneralLinearGroup.det g) = 1 ∧
      (∀ s : kˣ, pre g⁻¹ (ball (m + 1) s) = ball (m + 1) s) ∧
      ((g⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k)ᵀ *ᵥ xi0 k m = xi0 k m + η)
    {A₀ A : AddSubgroup (Fin (m + 1) → k)} (hA₀ : IsLat A₀) (hA : IsLat A) (h0 : A₀ ≤ A) (hAD : (ann ψ A : Set _) ⊆ D)
    (r : kˣ) (hAr : A ≤ ball (m + 1) r) (hr : IsLat (ball (m + 1) r)) (v w : V) (hv : FixK (by omega) π K v)
    (hw : FixK (by omega) π K w) :
    ((A₀.relIndex A : ℕ) : ℂ) * B (avg ψ h π (xi0 k m) A v) w =
      ((A₀.relIndex (ball (m + 1) r) : ℕ) : ℂ) * B (avg ψ h π (xi0 k m) (ball (m + 1) r) v) w := by
  obtain ⟨T, hT, hTc⟩ := exists_tr_lemma (ball (m + 1) r) A hr.1 hA.2
  have hAc := ann_isLat_pf hB.cont hB.ne hA
  have hrc := ann_isLat_pf hB.cont hB.ne hr
  obtain ⟨R, hR, -⟩ := exists_tr_lemma (ann ψ A) (ann ψ (ball (m + 1) r)) hAc.1 hrc.2
  have hdec := avg_decomp_pf (h := h) (π := π) hB.cont hB.ne hB.smooth (xi0 k m) hA hr hAr hR hT v
  have hterm : ∀ η ∈ R, B (avg ψ h π (xi0 k m + η) (ball (m + 1) r) v) w =
      B (avg ψ h π (xi0 k m) (ball (m + 1) r) v) w := by
    intro η hη
    obtain ⟨g, hg, hdet, hpre, hxi⟩ := hDK η (hAD (hR.1 η hη))
    have hc := avg_conj (h := h) hB.cont hB.smooth g (xi0 k m) hr v
    rw [hxi, hpre r, hv g hg] at hc
    calc B (avg ψ h π (xi0 k m + η) (ball (m + 1) r) v) w
        = B (π (blkAt k (m + 1) N (by omega) g) (avg ψ h π (xi0 k m) (ball (m + 1) r) v))
            (π (blkAt k (m + 1) N (by omega) g) w) := by rw [hc, hw g hg]
      _ = B (avg ψ h π (xi0 k m) (ball (m + 1) r) v) w := form_inv hB g hdet _ _
  have e := congrArg (fun x => B x w) hdec

  simp only [map_smul, map_sum, LinearMap.smul_apply, LinearMap.sum_apply,
  smul_eq_mul] at e
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul] at e
  have hR0 : (R.card : ℂ) ≠ 0 := by
    obtain ⟨t, ⟨ht, -⟩, -⟩ := hR.2 0 (ann ψ A).zero_mem
    exact Nat.cast_ne_zero.2 (Finset.card_ne_zero_of_mem ht)
  have e2 : B (avg ψ h π (xi0 k m) A v) w = (T.card : ℂ) * B (avg ψ h π (xi0 k m) (ball (m + 1) r) v) w := by
    apply mul_left_cancel₀ hR0
    rw [e]
    ring
  rw [e2, hTc, ← mul_assoc, ← Nat.cast_mul, AddSubgroup.relIndex_mul_relIndex _ _ _ h0 hAr]

theorem stab' (hB : Lv ψ h π s B) (K : Subgroup (GL (Fin (m + 1)) k)) (hK : IsOpen (K : Set (GL (Fin (m + 1)) k)))
    {A₀ : AddSubgroup (Fin (m + 1) → k)} (hA₀ : IsLat A₀) :
    ∃ A₁, IsLat A₁ ∧ A₀ ≤ A₁ ∧ ∀ v w, FixK (by omega) π K v → FixK (by omega) π K w → ∀ A, IsLat A → A₁ ≤ A →
      ((A₀.relIndex A : ℕ) : ℂ) * B (avg ψ h π (xi0 k m) A v) w =
        ((A₀.relIndex A₁ : ℕ) : ℂ) * B (avg ψ h π (xi0 k m) A₁ v) w := by
  obtain ⟨D, hD, hDK⟩ := good_nbhd_pf K hK
  obtain ⟨A₁, hA₁, h01, hA₁D⟩ := exists_big_pf hB.cont hB.ne D hD hA₀
  refine ⟨A₁, hA₁, h01, fun v w hv hw A hA h1A => ?_⟩
  obtain ⟨r, hAr, hr⟩ := exists_ball_pf hA
  rw [key' hB K D hDK hA₀ hA (h01.trans h1A) (fun x hx => hA₁D (ann_anti h1A hx)) r hAr hr v w hv hw,
    key' hB K D hDK hA₀ hA₁ h01 hA₁D r (h1A.trans hAr) hr v w hv hw]

end

end PositivityTheory.RgUd.Form.LeviSmoothness.stab
end
end
end
