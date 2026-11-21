module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.FlatMemLatIffStdLat
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.NsmulApplyMemOfMemTensorLat
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsSmulMemOfMemSpanFraction
public import ReciprocityTheory.SemistableReduction.ExistsIntSmulMemSpan
public import ReciprocityTheory.SemistableReduction.SemiDegCB
public import ReciprocityTheory.SemistableReduction.SemiDegCE
public import ReciprocityTheory.DualLattices.SmallLevelClassSet

@[expose] public section

namespace GlobalTheory.TensorLat

open NumberField Complex ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.GeometryOfNumbersTheory (stdLat)
open scoped nonZeroDivisors

theorem relIndex_eq_of_hom {M M' : Type*} [AddCommGroup M] [AddCommGroup M']
    {A₁ A₂ : AddSubgroup M} {B₁ B₂ : AddSubgroup M'} (f : M →+ M')
    (hf : ∀ v ∈ A₂, f v ∈ B₂) (hker : ∀ v ∈ A₂, f v ∈ B₁ ↔ v ∈ A₁)
    (hsurj : ∀ u ∈ B₂, ∃ v ∈ A₂, u - f v ∈ B₁) : A₁.relIndex A₂ = B₁.relIndex B₂ := by
  have h1 : A₁ ⊓ A₂ = B₁.comap f ⊓ A₂ := by
    ext v
    simp only [AddSubgroup.mem_inf, AddSubgroup.mem_comap]
    exact ⟨fun h => ⟨(hker v h.2).2 h.1, h.2⟩, fun h => ⟨(hker v h.2).1 h.1, h.2⟩⟩
  have h2 : B₁ ⊔ A₂.map f = B₁ ⊔ B₂ := by
    refine le_antisymm (sup_le_sup_left ?_ _) (sup_le le_sup_left fun u hu => ?_)
    · rintro _ ⟨v, hv, rfl⟩
      exact hf v hv
    · obtain ⟨v, hv, h⟩ := hsurj u hu
      exact AddSubgroup.mem_sup.2 ⟨_, h, f v, ⟨v, hv, rfl⟩, sub_add_cancel _ _⟩
  rw [← AddSubgroup.inf_relIndex_right, h1, AddSubgroup.inf_relIndex_right,
    AddSubgroup.relIndex_comap, ← AddSubgroup.relIndex_sup_left, h2,
    AddSubgroup.relIndex_sup_left]

theorem relIndex_pi_univ {ι : Type*} [Fintype ι] {G : ι → Type*} [∀ i, AddCommGroup (G i)]
    (L' L : ∀ i, AddSubgroup (G i)) :
    (AddSubgroup.pi Set.univ L').relIndex (AddSubgroup.pi Set.univ L) =
      ∏ i, (L' i).relIndex (L i) := by
  let f : (AddSubgroup.pi Set.univ L) →+ (∀ i, L i ⧸ (L' i).addSubgroupOf (L i)) :=
    { toFun := fun x i => QuotientAddGroup.mk ⟨x.1 i, x.2 i (Set.mem_univ i)⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hf : Function.Surjective f := fun y =>
    ⟨⟨fun i => (y i).out, fun i _ => (y i).out.2⟩, funext fun i => (y i).out_eq⟩
  have hc : (AddSubgroup.pi Set.univ L').addSubgroupOf (AddSubgroup.pi Set.univ L) = f.ker := by
    ext x
    rw [AddMonoidHom.mem_ker, funext_iff, AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_pi]
    refine forall_congr' fun i => ?_
    change _ ↔ (QuotientAddGroup.mk ⟨x.1 i, x.2 i (Set.mem_univ i)⟩ :
      L i ⧸ (L' i).addSubgroupOf (L i)) = 0
    simp [AddSubgroup.mem_addSubgroupOf]
  rw [AddSubgroup.relIndex, hc, AddSubgroup.index_ker, AddMonoidHom.range_eq_top.2 hf,
    AddSubgroup.card_top, Nat.card_pi]
  rfl

theorem card_eq_relIndex_of_reps {M : Type*} [AddCommGroup M] {A B : AddSubgroup M} {R : Finset M}
    (hR : ∀ y ∈ R, y ∈ B) (hR' : ∀ y ∈ B, ∃! r ∈ R, y - r ∈ A) : R.card = A.relIndex B := by
  rw [← Fintype.card_coe, ← Nat.card_eq_fintype_card]
  refine Nat.card_eq_of_bijective
    (fun y : R => (QuotientAddGroup.mk ⟨y, hR y y.2⟩ : B ⧸ A.addSubgroupOf B)) ⟨?_, ?_⟩
  · intro y y' h
    have h1 : (y : M) - y' ∈ A := by
      simpa [AddSubgroup.mem_addSubgroupOf] using QuotientAddGroup.eq_iff_sub_mem.1 h
    exact Subtype.ext ((hR' y (hR y y.2)).unique ⟨y.2, by simp⟩ ⟨y'.2, h1⟩)
  · intro q
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective q
    obtain ⟨r, ⟨hr, h⟩, -⟩ := hR' y y.2
    refine ⟨⟨r, hr⟩, (QuotientAddGroup.eq_iff_sub_mem.2 ?_).symm⟩
    simpa [AddSubgroup.mem_addSubgroupOf] using h

theorem exists_reps_of_relIndex_ne_zero {M : Type*} [AddCommGroup M] {A B : AddSubgroup M}
    (h : A.relIndex B ≠ 0) :
    ∃ R : Finset M, (∀ y ∈ R, y ∈ B) ∧ ∀ y ∈ B, ∃! r ∈ R, y - r ∈ A := by
  classical
  haveI : Fintype (B ⧸ A.addSubgroupOf B) := AddSubgroup.fintypeOfIndexNeZero h
  refine ⟨Finset.univ.image fun q : B ⧸ A.addSubgroupOf B => (q.out : M), ?_, fun y hy => ?_⟩
  · intro y hy
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hy
    exact q.out.2
  · have key : ∀ q : B ⧸ A.addSubgroupOf B,
        y - (q.out : M) ∈ A ↔ QuotientAddGroup.mk ⟨y, hy⟩ = q := fun q => by
      conv_rhs => rw [← QuotientAddGroup.out_eq' q, QuotientAddGroup.eq_iff_sub_mem]
      simp [AddSubgroup.mem_addSubgroupOf]
    refine ⟨_, ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), (key _).2 rfl⟩, ?_⟩
    rintro r ⟨hr, h⟩
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hr
    rw [(key q).1 h]

section Period

variable {E : Type} [Field E] [NumberField E]

end Period

section Index

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

end Index

section Modulus

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

variable [IsGalois ℚ E]

variable {K : Type*} [Field K] [Algebra E K]

end Modulus

namespace LocalLatticeSplit

open ReciprocityTheory.MultiplicativeHeights.SemiDegIdx

noncomputable section

def consZero (K : Type) [Field K] (k : ℕ) : (Fin k → K) →ₗ[K] (Fin (k + 1) → K) where
  toFun y := Fin.cons 0 y
  map_add' x y := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  map_smul' a x := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp

theorem consZero_injective (K : Type) [Field K] (k : ℕ) : Function.Injective (consZero K k) := by
  intro x y h
  funext i
  simpa [consZero] using congrFun h i.succ

theorem consZero_tail (K : Type) [Field K] {k : ℕ} (x : Fin (k + 1) → K) (hx : x 0 = 0) :
    consZero K k (Fin.tail x) = x := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [consZero, hx]
  · simp [consZero, Fin.tail]

theorem single_mem_intVec (K : Type) [Field K] [NumberField K] {k : ℕ} (i : Fin k) {a : K}
    (ha : a ∈ (1 : Submodule (𝓞 K) K)) : Pi.single i a ∈ intVec K k := by
  classical
  simp only [intVec, Submodule.mem_pi, Set.mem_univ, forall_const]
  intro j
  by_cases h : j = i
  · subst h
    simpa using ha
  · simp [h]

theorem consZero_mem_intVec (K : Type) [Field K] [NumberField K] {k : ℕ} {y : Fin k → K} :
    consZero K k y ∈ intVec K (k + 1) ↔ y ∈ intVec K k := by
  simp only [mem_intVec]
  constructor
  · intro h i
    simpa [consZero] using h i.succ
  · intro h i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [consZero]
    · simpa [consZero] using h j

theorem lattice_split (K : Type) [Field K] [NumberField K] : ∀ (k : ℕ)
    (X : Submodule (𝓞 K) (Fin k → K)), X.FG → intVec K k ≤ X →
    ∃ (C : Fin k → Submodule (𝓞 K) K) (z : Fin k → Fin k → K),
      (∀ i, (C i).FG) ∧ (∀ i, 1 ≤ C i) ∧ (∀ j i : Fin k, i < j → z j i = 0) ∧
      (∀ j, z j j = 1) ∧
      (∀ t : Fin k → K, (∀ i, t i ∈ C i) → ∑ i, t i • z i ∈ X) ∧
      (∀ x ∈ X, ∃ t : Fin k → K, (∀ i, t i ∈ C i) ∧ x = ∑ i, t i • z i) ∧
      (intVec K k).toAddSubgroup.relIndex X.toAddSubgroup =
        ∏ i, (1 : Submodule (𝓞 K) K).toAddSubgroup.relIndex (C i).toAddSubgroup
  | 0, X, _, _ => by
    refine ⟨Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun j => j.elim0,
      fun j => j.elim0, fun t _ => ?_, fun x _ => ⟨Fin.elim0, fun i => i.elim0, ?_⟩, ?_⟩
    · convert X.zero_mem using 1
    · ext i
      exact i.elim0
    · simp only [Finset.univ_eq_empty, Finset.prod_empty]
      rw [AddSubgroup.relIndex_eq_one]
      intro x _
      rw [Submodule.mem_toAddSubgroup, mem_intVec]
      intro i
      exact i.elim0
  | k + 1, X, hfg, hstd => by
    let p0 : (Fin (k + 1) → K) →ₗ[K] K := LinearMap.proj (φ := fun _ : Fin (k + 1) => K) 0
    set C0 := X.map (p0.restrictScalars (𝓞 K)) with hC0
    have hC0fg : C0.FG := hfg.map _
    have hC01 : 1 ≤ C0 := by
      intro a ha
      exact Submodule.mem_map.2 ⟨Pi.single 0 a, hstd (single_mem_intVec K 0 ha), by simp [p0]⟩
    obtain ⟨v, hv1, hv⟩ : ∃ v : Fin (k + 1) → K, p0 v = 1 ∧ ∀ t ∈ C0, t • v ∈ X :=
      exists_section_of_image X p0 hC0fg hC01
    let cz : (Fin k → K) →ₗ[𝓞 K] (Fin (k + 1) → K) :=
      (consZero K k).restrictScalars (𝓞 K)
    let X' : Submodule (𝓞 K) (Fin k → K) := X.comap cz
    have hX'fg : X'.FG := by
      apply Submodule.fg_of_fg_map_injective cz (consZero_injective K k)
      exact hfg.of_le (Submodule.map_comap_le _ _)
    have hstd' : intVec K k ≤ X' := fun y hy =>
      hstd ((consZero_mem_intVec K).2 hy)
    obtain ⟨C', z', hfg', h1', htri', hdiag', hin', hdec', hidx'⟩ :=
      lattice_split K k X' hX'fg hstd'
    let C : Fin (k + 1) → Submodule (𝓞 K) K := Fin.cons C0 C'
    let z : Fin (k + 1) → Fin (k + 1) → K := Fin.cons v fun j => consZero K k (z' j)
    have hsum : ∀ t : Fin (k + 1) → K,
        ∑ i, t i • z i = t 0 • v + consZero K k (∑ j, t j.succ • z' j) := by
      intro t
      set_option synthInstance.maxHeartbeats 100000 in
        rw [Fin.sum_univ_succ, map_sum]
      simp [z, map_smul]
    refine ⟨C, z, fun i => Fin.cases hC0fg hfg' i, fun i => Fin.cases hC01 h1' i, ?_, ?_, ?_, ?_, ?_⟩
    · intro j i hij
      induction j using Fin.cases with
      | zero => exact absurd hij (Fin.not_lt_zero i)
      | succ j =>
        induction i using Fin.cases with
        | zero => rfl
        | succ i => exact htri' j i (Fin.succ_lt_succ_iff.1 hij)
    · intro j
      induction j using Fin.cases with
      | zero => exact hv1
      | succ j => exact hdiag' j
    · intro t ht
      rw [hsum]
      refine X.add_mem (hv _ (ht 0)) ?_
      exact hin' (fun j => t j.succ) (fun j => ht j.succ)
    · intro x hx
      have ht0 : x 0 ∈ C0 := Submodule.mem_map.2 ⟨x, hx, rfl⟩
      set y := x - x 0 • v with hy
      have hyX : y ∈ X := X.sub_mem hx (hv _ ht0)
      have hy0 : y 0 = 0 := by
        have : p0 v = v 0 := rfl
        simp [hy, ← this, hv1]
      have hyX' : Fin.tail y ∈ X' := by
        show cz (Fin.tail y) ∈ X
        exact (consZero_tail K y hy0).symm ▸ hyX
      obtain ⟨t', ht', hyt⟩ := hdec' _ hyX'
      refine ⟨Fin.cons (x 0) t', fun i => Fin.cases ht0 ht' i, ?_⟩
      rw [hsum]
      simp only [Fin.cons_zero, Fin.cons_succ]
      rw [← hyt, consZero_tail K y hy0, hy]
      abel
    · have hA : (intVec K (k + 1)).toAddSubgroup.map p0.toAddMonoidHom =
          (1 : Submodule (𝓞 K) K).toAddSubgroup := by
        ext a
        simp only [AddSubgroup.mem_map, Submodule.mem_toAddSubgroup]
        constructor
        · rintro ⟨x, hx, rfl⟩
          exact mem_intVec.1 hx 0
        · intro ha
          exact ⟨Pi.single 0 a, single_mem_intVec K 0 ha, by simp [p0]⟩
      have hB : X.toAddSubgroup.map p0.toAddMonoidHom = C0.toAddSubgroup := by
        ext a
        simp [C0, Submodule.mem_map]
      have hAk : (intVec K (k + 1)).toAddSubgroup ⊓ p0.toAddMonoidHom.ker =
          (intVec K k).toAddSubgroup.map (consZero K k).toAddMonoidHom := by
        ext x
        simp only [AddSubgroup.mem_inf, AddSubgroup.mem_map, Submodule.mem_toAddSubgroup,
          AddMonoidHom.mem_ker]
        constructor
        · rintro ⟨hx, h0⟩
          refine ⟨Fin.tail x, ?_, consZero_tail K x h0⟩
          rw [← consZero_mem_intVec K, consZero_tail K x h0]
          exact hx
        · rintro ⟨y, hy, rfl⟩
          exact ⟨(consZero_mem_intVec K).2 hy, rfl⟩
      have hBk : X.toAddSubgroup ⊓ p0.toAddMonoidHom.ker =
          X'.toAddSubgroup.map (consZero K k).toAddMonoidHom := by
        ext x
        simp only [AddSubgroup.mem_inf, AddSubgroup.mem_map, Submodule.mem_toAddSubgroup,
          AddMonoidHom.mem_ker]
        constructor
        · rintro ⟨hx, h0⟩
          refine ⟨Fin.tail x, ?_, consZero_tail K x h0⟩
          show cz (Fin.tail x) ∈ X
          exact (consZero_tail K x h0).symm ▸ hx
        · rintro ⟨y, hy, rfl⟩
          exact ⟨hy, rfl⟩
      rw [relIndex_eq_map_mul_ker p0.toAddMonoidHom
          ((Submodule.toAddSubgroup_le _ _).2 hstd), hA, hB, hAk, hBk,
        AddSubgroup.relIndex_map_map_of_injective _ _ (consZero_injective K k), hidx',
        Fin.prod_univ_succ]
      rfl


end
end LocalLatticeSplit

section IndexIdeal

open ReciprocityTheory.MultiplicativeHeights.SemiDegIdx ReciprocityTheory.PGsh

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

theorem exists_coe_eq_span_det_of_intVec_le (X : Submodule (𝓞 K) (Fin n → K)) (hfg : X.FG)
    (hstd : intVec K n ≤ X) :
    ∃ J : FractionalIdeal (𝓞 K)⁰ K, (J : Submodule (𝓞 K) K) = Submodule.span (𝓞 K)
        {d | ∃ v : Fin n → Fin n → K, (∀ i, v i ∈ X) ∧ d = (Matrix.of v).det} ∧
      FractionalIdeal.absNorm J * ((intVec K n).toAddSubgroup.relIndex X.toAddSubgroup : ℚ) = 1 := by
  obtain ⟨C, z, hfgC, h1, htri, hdiag, hin, hdec, hidx⟩ :=
    LocalLatticeSplit.lattice_split K n X hfg hstd
  let CF : Fin n → FractionalIdeal (𝓞 K)⁰ K := fun i =>
    ⟨C i, FractionalIdeal.isFractional_of_fg (hfgC i)⟩
  refine ⟨∏ i, CF i, ?_, ?_⟩
  · rw [coe_prod_frac]
    change ∏ i, C i = _
    refine le_antisymm ?_ (Submodule.span_le.2 ?_)
    · rw [prod_eq_span_prod]
      refine Submodule.span_mono fun x hx => ?_
      obtain ⟨t, ht, rfl⟩ := (Set.mem_fintype_prod _ _).1 hx
      refine ⟨fun i => t i • z i, fun i => smul_mem_of_split hin i (ht i), ?_⟩
      have : (Matrix.of fun i => t i • z i) = Matrix.diagonal t * rowMat z := by
        ext i j
        simp [rowMat, Matrix.diagonal_mul]
      rw [this, Matrix.det_mul, det_rowMat z htri hdiag, Matrix.det_diagonal, mul_one]
    · rintro _ ⟨v, hv, rfl⟩
      choose T hT hTv using fun i => hdec (v i) (hv i)
      have : Matrix.of v = Matrix.of T * rowMat z := by
        ext i j
        rw [Matrix.of_apply, hTv i]
        simp [rowMat, Matrix.mul_apply, Finset.sum_apply]
      rw [this, Matrix.det_mul, det_rowMat z htri hdiag, mul_one, ← Matrix.det_transpose]
      exact det_mem_prod_sub C _ fun i j => hT j i
  · rw [hidx, map_prod, Nat.cast_prod, ← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun i _ => absNorm_mul_relIndex_one (C i) (hfgC i) (h1 i)

theorem exists_coe_eq_span_det {Λ Λ' : Submodule (𝓞 K) (Fin n → K)} (hle : Λ ≤ Λ') (hfg : Λ'.FG)
    (hsp : Submodule.span K (Λ : Set (Fin n → K)) = ⊤) :
    ∃ J J' : FractionalIdeal (𝓞 K)⁰ K, J ≠ 0 ∧ J' ≠ 0 ∧
      (J : Submodule (𝓞 K) K) = Submodule.span (𝓞 K)
        {d | ∃ v : Fin n → Fin n → K, (∀ i, v i ∈ Λ) ∧ d = (Matrix.of v).det} ∧
      (J' : Submodule (𝓞 K) K) = Submodule.span (𝓞 K)
        {d | ∃ v : Fin n → Fin n → K, (∀ i, v i ∈ Λ') ∧ d = (Matrix.of v).det} ∧
      FractionalIdeal.absNorm J =
        (Λ.toAddSubgroup.relIndex Λ'.toAddSubgroup : ℚ) * FractionalIdeal.absNorm J' := by
  classical
  choose d hd0 hd using fun k : Fin n => exists_smul_mem_of_mem_span_fraction (K := K) Λ
    (Pi.single k (1 : K)) (hsp ▸ Submodule.mem_top)
  set δ : K := algebraMap (𝓞 K) K (∏ k, d k) with hδ
  have hδ0 : δ ≠ 0 := by simpa [hδ, Finset.prod_ne_zero_iff] using hd0
  let μ : (Fin n → K) →ₗ[𝓞 K] (Fin n → K) := (LinearMap.lsmul K _ δ).restrictScalars (𝓞 K)
  have hμ : ∀ x, μ x = δ • x := fun _ => rfl
  have hinj : Function.Injective μ := smul_right_injective _ hδ0
  have hsurj : Function.Surjective μ := fun x => ⟨δ⁻¹ • x, by rw [hμ, smul_inv_smul₀ hδ0]⟩
  have hstd : intVec K n ≤ Λ.comap μ := by
    intro x hx
    choose c hc using fun k => Submodule.mem_one.1 (mem_intVec.1 hx k)
    have : x = ∑ k, c k • (Pi.single k (1 : K) : Fin n → K) := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply, Algebra.smul_def, hc]
    rw [this]
    refine Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ ?_
    rw [Submodule.mem_comap, hμ, hδ, algebraMap_smul,
      ← Finset.prod_erase_mul _ _ (Finset.mem_univ k), mul_smul]
    exact Λ.smul_mem _ (hd k)
  have key : ∀ Y : Submodule (𝓞 K) (Fin n → K), Λ ≤ Y → Y.FG →
      ∃ J : FractionalIdeal (𝓞 K)⁰ K, (J : Submodule (𝓞 K) K) = Submodule.span (𝓞 K)
        {d | ∃ v : Fin n → Fin n → K, (∀ i, v i ∈ Y) ∧ d = (Matrix.of v).det} ∧
      FractionalIdeal.absNorm J * ((intVec K n).toAddSubgroup.relIndex
        (Y.comap μ).toAddSubgroup : ℚ) = |Algebra.norm ℚ (δ ^ n)| := by
    intro Y hY hYfg
    obtain ⟨J, hJ, hN⟩ := exists_coe_eq_span_det_of_intVec_le (Y.comap μ)
      (Submodule.fg_of_fg_map_injective μ hinj
        (by rwa [Submodule.map_comap_eq_of_surjective hsurj]))
      (hstd.trans (Submodule.comap_mono hY))
    refine ⟨FractionalIdeal.spanSingleton _ (δ ^ n) * J, ?_, ?_⟩
    · rw [FractionalIdeal.coe_mul, FractionalIdeal.coe_spanSingleton, hJ, Submodule.span_mul_span,
        Set.singleton_mul]
      congr 1
      ext x
      constructor
      · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
        refine ⟨δ • v, hv, ?_⟩
        change _ = (δ • Matrix.of v).det
        rw [Matrix.det_smul, Fintype.card_fin]
      · rintro ⟨v, hv, rfl⟩
        refine ⟨_, ⟨δ⁻¹ • v, fun i => ?_, rfl⟩, ?_⟩
        · rw [Submodule.mem_comap, hμ, Pi.smul_apply, smul_inv_smul₀ hδ0]
          exact hv i
        · change _ * (δ⁻¹ • Matrix.of v).det = _
          rw [Matrix.det_smul, Fintype.card_fin, inv_pow, mul_inv_cancel_left₀ (pow_ne_zero _ hδ0)]
    · rw [map_mul, mul_assoc, hN, mul_one, FractionalIdeal.absNorm_span_singleton]
  obtain ⟨J, hJ, hN⟩ := key Λ le_rfl (hfg.of_le hle)
  obtain ⟨J', hJ', hN'⟩ := key Λ' hle hfg
  have hn0 : |Algebra.norm ℚ (δ ^ n)| ≠ 0 :=
    abs_ne_zero.2 (Algebra.norm_ne_zero_iff.2 (pow_ne_zero _ hδ0))
  have hidx : (Λ.comap μ).toAddSubgroup.relIndex (Λ'.comap μ).toAddSubgroup =
      Λ.toAddSubgroup.relIndex Λ'.toAddSubgroup := by
    change (Λ.toAddSubgroup.comap μ.toAddMonoidHom).relIndex
      (Λ'.toAddSubgroup.comap μ.toAddMonoidHom) = _
    rw [AddSubgroup.relIndex_comap, AddSubgroup.map_comap_eq_self_of_surjective hsurj]
  have htower := AddSubgroup.relIndex_mul_relIndex (intVec K n).toAddSubgroup
    (Λ.comap μ).toAddSubgroup (Λ'.comap μ).toAddSubgroup hstd (Submodule.comap_mono hle)
  refine ⟨J, J', ?_, ?_, hJ, hJ', ?_⟩
  · rintro rfl
    rw [map_zero, zero_mul] at hN
    exact hn0 hN.symm
  · rintro rfl
    rw [map_zero, zero_mul] at hN'
    exact hn0 hN'.symm
  · rw [← htower, hidx, Nat.cast_mul, ← hN] at hN'
    refine mul_right_cancel₀ (right_ne_zero_of_mul (hN ▸ hn0)) ?_
    linear_combination -hN'

attribute [local instance] extModR

end IndexIdeal

section Main

open ReciprocityTheory.PGsh

attribute [local instance] extModR

end Main

end GlobalTheory.TensorLat
