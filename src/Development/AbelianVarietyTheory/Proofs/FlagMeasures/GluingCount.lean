module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BasisOfIsCompl
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsBasisFgMaximalOrderSpanningFree
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsEqZpowMulUnit
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RelIndexSpanLatticeMatrixDetNorm
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
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DualInterSelfDualHermitianLatticeSubspace
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameLatticeGramDetAndMinorsOrbitInvariantStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetFrameClassProperties
import Mathlib.Order.CompletePartialOrder

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardDiscriminantModuleIntegralOverlatticeSpan

section

@[expose] public section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.DiscOver

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

def gram (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) {ι : Type} (w : ι → Fin n → E) :
    Matrix ι ι E := Matrix.of fun a b => hf L Hm (w b) (w a)

def comb {n m : ℕ} (w : Fin m → Fin n → E) (A : Matrix (Fin m) (Fin m) E) : Fin m → Fin n → E :=
  fun j => ∑ i, A i j • w i

theorem hf_addl (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (a b y : Fin n → E) :
    hf L Hm (a + b) y = hf L Hm a y + hf L Hm b y := by
  simp [hf, add_mul, Finset.sum_add_distrib]

theorem hf_smull (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (c : E) (a y : Fin n → E) :
    hf L Hm (c • a) y = c * hf L Hm a y := by
  simp [hf, Finset.mul_sum, mul_assoc]

theorem hf_addr (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (a b y : Fin n → E) :
    hf L Hm y (a + b) = hf L Hm y a + hf L Hm y b := by
  simp [hf, mul_add, Finset.sum_add_distrib]

theorem hf_smulr (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (c : E) (a y : Fin n → E) :
    hf L Hm y (c • a) = L.cj c * hf L Hm y a := by
  simp only [hf, Finset.mul_sum, Pi.smul_apply, smul_eq_mul, map_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hf_suml (L : LocE F E) {n m : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (t : Fin m → E)
    (w : Fin m → Fin n → E) (y : Fin n → E) :
    hf L Hm (∑ i, t i • w i) y = ∑ i, t i * hf L Hm (w i) y := by
  induction (Finset.univ : Finset (Fin m)) using Finset.induction_on with
  | empty => simp [hf]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hf_addl, hf_smull, ih]

theorem hf_sumr (L : LocE F E) {n m : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (t : Fin m → E)
    (w : Fin m → Fin n → E) (y : Fin n → E) :
    hf L Hm y (∑ i, t i • w i) = ∑ i, L.cj (t i) * hf L Hm y (w i) := by
  induction (Finset.univ : Finset (Fin m)) using Finset.induction_on with
  | empty => simp [hf]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hf_addr, hf_smulr, ih]

theorem gram_comb (L : LocE F E) {n m : ℕ} (Hm : Matrix (Fin n) (Fin n) E)
    (w : Fin m → Fin n → E) (A : Matrix (Fin m) (Fin m) E) :
    gram L Hm (comb w A) = cT L A * (gram L Hm w * A) := by
  ext a b
  simp only [gram, comb, Matrix.of_apply, hf_sumr, hf_suml, Matrix.mul_apply, cT]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem det_cT (L : LocE F E) {m : ℕ} (A : Matrix (Fin m) (Fin m) E) :
    (cT L A).det = L.cj A.det := by
  have : cT L A = ((L.cj : E →+* E).mapMatrix A).transpose := by ext i j; rfl
  rw [this, Matrix.det_transpose, ← RingHom.map_det]; rfl

theorem comb_comb {n m : ℕ} (w : Fin m → Fin n → E) (A B : Matrix (Fin m) (Fin m) E) :
    comb (comb w A) B = comb w (A * B) := by
  funext j
  simp only [comb, Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by rw [mul_comm]

theorem comb_one {n m : ℕ} (w : Fin m → Fin n → E) : comb w 1 = w := by
  funext j
  simp [comb, Matrix.one_apply, ite_smul]

theorem sum_comb {n m : ℕ} (w : Fin m → Fin n → E) (A : Matrix (Fin m) (Fin m) E) (s : Fin m → E) :
    ∑ j, s j • comb w A j = ∑ i, (A.mulVec s) i • w i := by
  simp only [comb, Finset.smul_sum, smul_smul, Matrix.mulVec, dotProduct, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by rw [mul_comm]

theorem hf_gram (L : LocE F E) {n m : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (t : Fin m → E)
    (w : Fin m → Fin n → E) (a : Fin m) :
    hf L Hm (∑ i, t i • w i) (w a) = ((gram L Hm w).mulVec t) a := by
  rw [hf_suml]
  simp only [gram, Matrix.mulVec, dotProduct, Matrix.of_apply]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem li_of_gram (L : LocE F E) {n m : ℕ} (Hm : Matrix (Fin n) (Fin n) E)
    (w : Fin m → Fin n → E) (hu : IsUnit (gram L Hm w).det) : LinearIndependent E w := by
  rw [Fintype.linearIndependent_iff]
  intro t ht
  have h0 : (gram L Hm w).mulVec t = 0 := by
    funext a
    rw [← hf_gram, ht]; simp [hf]
  have h1 : t = (gram L Hm w)⁻¹.mulVec ((gram L Hm w).mulVec t) := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]
  intro i
  rw [h1, h0]; simp

theorem mem_spanO (L : LocE F E) {n m : ℕ} (w : Fin m → Fin n → E) (x : Fin n → E) :
    x ∈ Submodule.span L.O (Set.range w) ↔ ∃ s : Fin m → E, (∀ i, s i ∈ L.O) ∧ ∑ i, s i • w i = x := by
  rw [Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨s, hs⟩
    exact ⟨fun i => s i, fun i => (s i).2, hs⟩
  · rintro ⟨s, h, hs⟩
    exact ⟨fun i => ⟨s i, h i⟩, hs⟩

theorem dual_iff (L : LocE F E) {n m : ℕ} (Hm : Matrix (Fin n) (Fin n) E)
    (w : Fin m → Fin n → E) (hu : IsUnit (gram L Hm w).det) (x : Fin n → E) :
    (x ∈ Submodule.span E (Set.range w) ∧ ∀ a, hf L Hm x (w a) ∈ L.O) ↔
      x ∈ Submodule.span L.O (Set.range (comb w (gram L Hm w)⁻¹)) := by
  rw [mem_spanO, Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨⟨t, rfl⟩, h⟩
    refine ⟨(gram L Hm w).mulVec t, fun a => ?_, ?_⟩
    · rw [← hf_gram]; exact h a
    · rw [sum_comb, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]
  · rintro ⟨s, hs, rfl⟩
    rw [sum_comb]
    refine ⟨⟨_, rfl⟩, fun a => ?_⟩
    rw [hf_gram, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]
    exact hs a

theorem det_mem (O : Subring E) {m : ℕ} (A : Matrix (Fin m) (Fin m) E) (h : ∀ i j, A i j ∈ O) :
    A.det ∈ O := by
  have : A = O.subtype.mapMatrix (Matrix.of fun i j => (⟨A i j, h i j⟩ : O)) := by ext i j; rfl
  rw [this, ← RingHom.map_det]
  exact Subtype.property _

theorem adj_mem (O : Subring E) {m : ℕ} (A : Matrix (Fin m) (Fin m) E) (h : ∀ i j, A i j ∈ O)
    (i j : Fin m) : A.adjugate i j ∈ O := by
  have : A = O.subtype.mapMatrix (Matrix.of fun i j => (⟨A i j, h i j⟩ : O)) := by ext i j; rfl
  rw [this, ← RingHom.map_adjugate]
  exact Subtype.property _

theorem disc_fin [IsNonarchimedeanLocalField F] [CharZero F] (L : LocE F E) {n : ℕ}
    (Hm : Matrix (Fin n) (Fin n) E) (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ) {m : ℕ}
    (v : Fin m → Fin n → E) (c : F) (hc : c ≠ 0) (hG : (gram L Hm v).det = algebraMap F E c)
    (Mh Md : Submodule L.O (Fin n → E)) (h1 : Submodule.span L.O (Set.range v) ≤ Mh)
    (h2 : ∀ x ∈ Mh, x ∈ Submodule.span E (Set.range v))
    (h3 : ∀ x ∈ Mh, ∀ y ∈ Mh, hf L Hm x y ∈ L.O)
    (h4 : ∀ x, x ∈ Md ↔ x ∈ Submodule.span E (Set.range v) ∧ ∀ y ∈ Mh, hf L Hm x y ∈ L.O) :
    0 ≤ vE L ϖ (algebraMap F E c) ∧ Mh.toAddSubgroup.relIndex Md.toAddSubgroup *
      ((Submodule.span L.O (Set.range v)).toAddSubgroup.relIndex Mh.toAddSubgroup) ^ 2 =
      resQ ϖ ^ (2 * (vE L ϖ (algebraMap F E c)).toNat) ∧
      (∀ x ∈ Md, algebraMap F E c • x ∈ Submodule.span L.O (Set.range v)) ∧
      ∃ b : Fin m → Fin n → E, Md = Submodule.span L.O (Set.range b) := by
  obtain ⟨-, hcj, -, hPIR, hint, -, hq, -⟩ := GlobalTheory.UnramOrder.order_facts L ϖ hϖ
  obtain ⟨hadd, -, hpos, -⟩ := GlobalTheory.UnramVal.vE_valuation L ϖ hϖ
  have hcu : IsUnit (algebraMap F E c) := (IsUnit.mk0 c hc).map _
  have hu : IsUnit (gram L Hm v).det := hG ▸ hcu
  have hv : ∀ a, v a ∈ Mh := fun a => h1 (Submodule.subset_span ⟨a, rfl⟩)
  have hle : Mh ≤ Submodule.span L.O (Set.range (comb v (gram L Hm v)⁻¹)) := fun x hx =>
    (dual_iff L Hm v hu x).1 ⟨h2 x hx, fun a => h3 x hx _ (hv a)⟩
  have hfg : Mh.FG :=
    Submodule.FG.of_le (Submodule.fg_span (Set.finite_range _)) hle
  have hsp : Submodule.span E (Mh : Set (Fin n → E)) = Submodule.span E (Set.range v) := by
    apply le_antisymm
    · exact Submodule.span_le.2 h2
    · apply Submodule.span_mono; rintro _ ⟨a, rfl⟩; exact hv a
  obtain ⟨b, hb, hMh⟩ := GlobalTheory.OrderBasis.order_basis L v (li_of_gram L Hm v hu) Mh hfg hsp
  have hbm : ∀ a, b a ∈ Mh := fun a => hMh ▸ Submodule.subset_span ⟨a, rfl⟩
  have hA : ∀ j, ∃ s : Fin m → E, (∀ i, s i ∈ L.O) ∧ ∑ i, s i • b i = v j := fun j =>
    (mem_spanO L b _).1 (hMh ▸ hv j)
  choose s hs hsv using hA
  set A : Matrix (Fin m) (Fin m) E := Matrix.of fun i j => s j i with hAdef
  have hvA : v = comb b A := by funext j; exact (hsv j).symm
  have hdet : (gram L Hm b).det * (A.det * L.cj A.det) = algebraMap F E c := by
    rw [← hG, hvA, gram_comb, Matrix.det_mul, Matrix.det_mul, det_cT]; ring
  obtain ⟨-, -, cA, hcA⟩ := hcj A.det (det_mem _ A fun i j => hs j i)
  have hprod : IsUnit ((gram L Hm b).det * (A.det * L.cj A.det)) := hdet ▸ hcu
  have hub : IsUnit (gram L Hm b).det := isUnit_of_mul_isUnit_left hprod
  have hnt : Nontrivial E := by
    have := L.free
    exact Module.nontrivial_of_finrank_pos (R := F) (by rw [L.rank]; norm_num)
  have hcA0 : (cA : F) ≠ 0 := by
    intro h0
    have := isUnit_of_mul_isUnit_right hprod
    rw [hcA, h0, map_zero] at this
    exact not_isUnit_zero this
  set c0 : F := c / cA with hc0def
  have hc0 : c0 ≠ 0 := div_ne_zero hc hcA0
  have hcc : c = c0 * cA := by rw [hc0def]; field_simp
  have hdb : (gram L Hm b).det = algebraMap F E c0 := by
    have hAu : IsUnit (algebraMap F E cA) := (IsUnit.mk0 _ hcA0).map _
    apply hAu.mul_right_cancel
    rw [← map_mul, ← hcc, ← hdet, hcA]
  have hc0int : c0 ∈ 𝒪[F] := (hint c0).1
    (hdb ▸ det_mem _ _ fun i j => h3 _ (hbm j) _ (hbm i))
  have hv0 := (hpos c0 hc0).2 hc0int
  have hvA0 := (hpos cA hcA0).2 cA.2
  have hvc : vE L ϖ (algebraMap F E c) = vE L ϖ (algebraMap F E c0) + vE L ϖ (algebraMap F E cA) := by
    rw [← hadd c0 cA hc0 hcA0, ← hcc]
  have hspb : Submodule.span E (Set.range b) = Submodule.span E (Set.range v) := by
    rw [← hsp, hMh, Submodule.span_span_of_tower]
  have hMd : Md = Submodule.span L.O (Set.range (comb b (gram L Hm b)⁻¹)) := by
    ext x
    rw [h4, ← dual_iff L Hm b hub, hspb]
    refine and_congr_right fun _ => ⟨fun h a => h _ (hbm a), fun h y hy => ?_⟩
    obtain ⟨t, ht, rfl⟩ := (mem_spanO L b _).1 (hMh ▸ hy)
    rw [hf_sumr]
    exact L.O.sum_mem fun i _ => L.O.mul_mem (hcj _ (ht i)).1 (h i)
  have hbd : b = comb (comb b (gram L Hm b)⁻¹) (gram L Hm b) := by
    rw [comb_comb, Matrix.nonsing_inv_mul _ hub, comb_one]
  have hud : IsUnit (gram L Hm (comb b (gram L Hm b)⁻¹)).det := by
    rw [gram_comb, Matrix.mul_nonsing_inv _ hub, mul_one, det_cT]
    exact (Matrix.isUnit_nonsing_inv_det _ hub).map _
  have hMM : Mh ≤ Md := fun x hx => (h4 x).2 ⟨h2 x hx, h3 x hx⟩
  obtain ⟨-, -, e1⟩ := GlobalTheory.HL.FrameIndex.relIndex_span_matrix L ϖ hϖ b hb A cA hcA0 hcA Mh
    (Submodule.span L.O (Set.range v)) hMh (by rw [hvA]; rfl)
  obtain ⟨-, -, e2⟩ := GlobalTheory.HL.FrameIndex.relIndex_span_matrix L ϖ hϖ _ (li_of_gram L Hm _ hud) (gram L Hm b) (c0 * c0)
    (mul_ne_zero hc0 hc0) (by rw [hdb, AlgEquiv.commutes, map_mul]) Md Mh hMd
    (by rw [hMh]; exact congrArg (fun w => Submodule.span L.O (Set.range w)) hbd)
  rw [AddSubgroup.relIndex_eq_one.2 (Submodule.toAddSubgroup_mono h1)] at e1
  rw [AddSubgroup.relIndex_eq_one.2 (Submodule.toAddSubgroup_mono hMM), hadd c0 c0 hc0 hc0] at e2
  refine ⟨by omega, ?_, ?_, _, hMd⟩
  · obtain ⟨k0, hk0⟩ := Int.eq_ofNat_of_zero_le hv0
    obtain ⟨kA, hkA⟩ := Int.eq_ofNat_of_zero_le hvA0
    rw [hvc, hk0, hkA]
    rw [hkA] at e1
    rw [hk0] at e2
    have : ((k0 : ℤ) + kA).toNat = k0 + kA := by omega
    rw [this]
    apply Nat.cast_injective (R := ℝ)
    push_cast
    rw [e1, e2, ← Nat.cast_add, zpow_natCast, zpow_natCast]
    push_cast
    ring
  · intro x hx
    have hx' := (dual_iff L Hm v hu x).1 ⟨((h4 x).1 hx).1, fun a => ((h4 x).1 hx).2 _ (hv a)⟩
    obtain ⟨t, ht, rfl⟩ := (mem_spanO L _ _).1 hx'
    have hadj : algebraMap F E c • (gram L Hm v)⁻¹ = (gram L Hm v).adjugate := by
      rw [← hG, Matrix.inv_def, smul_smul, Ring.mul_inverse_cancel _ hu, one_smul]
    rw [sum_comb, mem_spanO]
    refine ⟨(gram L Hm v).adjugate.mulVec t, fun i => ?_, ?_⟩
    · simp only [Matrix.mulVec, dotProduct]
      exact L.O.sum_mem fun j _ => L.O.mul_mem
        (adj_mem _ (gram L Hm v) (fun i j => h3 _ (hv j) _ (hv i)) i j) (ht j)
    · rw [← hadj, Matrix.smul_mulVec, Finset.smul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [smul_smul]; rfl

theorem disc_overlattice : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → ∀ ϖ : 𝒪[F], Irreducible ϖ → ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (v : ι → Fin n → E) (c : F), c ≠ 0 → (Matrix.of fun a b => hf L Hm (v b) (v a)).det = algebraMap F E c → ∀ Mh Md : Submodule L.O (Fin n → E), Submodule.span L.O (Set.range v) ≤ Mh → (∀ x ∈ Mh, x ∈ Submodule.span E (Set.range v)) → (∀ x ∈ Mh, ∀ y ∈ Mh, hf L Hm x y ∈ L.O) → (∀ x, x ∈ Md ↔ x ∈ Submodule.span E (Set.range v) ∧ ∀ y ∈ Mh, hf L Hm x y ∈ L.O) → 0 ≤ vE L ϖ (algebraMap F E c) ∧ Mh.toAddSubgroup.relIndex Md.toAddSubgroup * ((Submodule.span L.O (Set.range v)).toAddSubgroup.relIndex Mh.toAddSubgroup) ^ 2 = resQ ϖ ^ (2 * (vE L ϖ (algebraMap F E c)).toNat) ∧ (∀ x ∈ Md, algebraMap F E c • x ∈ Submodule.span L.O (Set.range v)) ∧ ∃ b : ι → Fin n → E, Md = Submodule.span L.O (Set.range b) := by
  intro F _ _ _ _ _ E _ _ _ L n Hm _ ϖ hϖ ι _ _ v c hc hG Mh Md h1 h2 h3 h4
  let e := (Fintype.equivFin ι).symm
  have hr : Set.range (v ∘ e) = Set.range v := e.surjective.range_comp v
  have hG' : (gram L Hm (v ∘ e)).det = algebraMap F E c := by
    rw [← hG, ← Matrix.det_submatrix_equiv_self e]; rfl
  have := disc_fin L Hm ϖ hϖ (v ∘ e) c hc hG' Mh Md (by rwa [hr]) (by rwa [hr]) h3 (by rwa [hr])
  rw [hr] at this
  obtain ⟨a1, a2, a3, b, hb⟩ := this
  exact ⟨a1, a2, a3, b ∘ e.symm, by rw [e.symm.surjective.range_comp b]; exact hb⟩

end GlobalTheory.DiscOver
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardDiscriminantModuleIntegralOverlatticeSpanStatement

section

@[expose] public section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.card_discriminantModule_integralOverlattice_span : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → ∀ ϖ : 𝒪[F], Irreducible ϖ → ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (v : ι → Fin n → E) (c : F), c ≠ 0 → (Matrix.of fun a b => hf L Hm (v b) (v a)).det = algebraMap F E c → ∀ Mh Md : Submodule L.O (Fin n → E), Submodule.span L.O (Set.range v) ≤ Mh → (∀ x ∈ Mh, x ∈ Submodule.span E (Set.range v)) → (∀ x ∈ Mh, ∀ y ∈ Mh, hf L Hm x y ∈ L.O) → (∀ x, x ∈ Md ↔ x ∈ Submodule.span E (Set.range v) ∧ ∀ y ∈ Mh, hf L Hm x y ∈ L.O) → 0 ≤ vE L ϖ (algebraMap F E c) ∧ Mh.toAddSubgroup.relIndex Md.toAddSubgroup * ((Submodule.span L.O (Set.range v)).toAddSubgroup.relIndex Mh.toAddSubgroup) ^ 2 = resQ ϖ ^ (2 * (vE L ϖ (algebraMap F E c)).toNat) ∧ (∀ x ∈ Md, algebraMap F E c • x ∈ Submodule.span L.O (Set.range v)) ∧ ∃ b : ι → Fin n → E, Md = Submodule.span L.O (Set.range b) := by
  first | exact @GlobalTheory.DiscOver.disc_overlattice | exact GlobalTheory.DiscOver.disc_overlattice | (intros; apply GlobalTheory.DiscOver.disc_overlattice <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.GluingCount

section

@[expose] public section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.Gluing

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem resQ_ne_zero [IsNonarchimedeanLocalField F] (ϖ : 𝒪[F]) (h : Irreducible ϖ) :
    resQ ϖ ≠ 0 := by
  unfold resQ
  rw [← (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 h]
  have : Finite (𝒪[F] ⧸ IsLocalRing.maximalIdeal 𝒪[F]) := inferInstanceAs (Finite 𝓀[F])
  exact Nat.card_pos.ne'

theorem encard_le [IsNonarchimedeanLocalField F] [CharZero F] {L : LocE F E} {n : ℕ}
    {Hm : Matrix (Fin n) (Fin n) E} (h : IsHermND L Hm) {m : ℕ} {y : Fin m → Fin n → E}
    (hy : LinearIndependent E y) {Y : Submodule E (Fin n → E)}
    (hY : Submodule.span E (Set.range y) = Y) (hc : Y ⊔ perp L Hm Y = ⊤)
    (Mh Λ₀ Md : Submodule L.O (Fin n → E))
    (hMd : ∀ x, x ∈ Md ↔ x ∈ Y ∧ ∀ z ∈ Mh, hf L Hm x z ∈ L.O)
    {ι : Type} [Fintype ι] (b : ι → Fin n → E) (hb : Md = Submodule.span L.O (Set.range b))
    (hN : Mh.toAddSubgroup.relIndex Md.toAddSubgroup ≠ 0) :
    {Λ : Submodule L.O (Fin n → E) | IsSD L Hm Λ ∧ Λ ⊓ Y.restrictScalars L.O = Mh ∧
      Λ ⊓ (perp L Hm Y).restrictScalars L.O = Λ₀}.encard ≤
      ((Mh.toAddSubgroup.relIndex Md.toAddSubgroup ^ Fintype.card ι : ℕ) : ℕ∞) := by
  set T := {Λ : Submodule L.O (Fin n → E) | IsSD L Hm Λ ∧ Λ ⊓ Y.restrictScalars L.O = Mh ∧
      Λ ⊓ (perp L Hm Y).restrictScalars L.O = Λ₀} with hT
  rcases T.eq_empty_or_nonempty with h0 | ⟨Λ₁, hΛ₁⟩
  · simp [h0]
  have hsym : ∀ x v, hf L Hm x v ∈ L.O → hf L Hm v x ∈ L.O := fun x v hx => by
    rw [← DualInter.cj_hf h]
    exact GlobalTheory.UnramOrder.cj_mem L hx
  have hM : ∀ Λ ∈ T, ∀ x, x ∈ Mh ↔ x ∈ Λ ∧ x ∈ Y := fun Λ hΛ x => by
    rw [← hΛ.2.1]; rfl
  have h0 : ∀ Λ ∈ T, ∀ x, x ∈ Λ₀ ↔ x ∈ Λ ∧ x ∈ perp L Hm Y := fun Λ hΛ x => by
    rw [← hΛ.2.2]; rfl
  have hproj : ∀ Λ ∈ T, ∀ l ∈ Λ, ∀ w ∈ perp L Hm Y, l - w ∈ Y → l - w ∈ Md := by
    intro Λ hΛ l hl w hw hlw
    refine (hMd _).2 ⟨hlw, fun z hz => ?_⟩
    have hz' := (hM Λ hΛ z).1 hz
    rw [DualInter.sub_l, hw z hz'.2, sub_zero]
    exact (hΛ.1.2 z).2 hz'.1 l hl
  have hbM : ∀ i, b i ∈ Md := fun i => hb ▸ Submodule.subset_span ⟨i, rfl⟩
  have hlift : ∀ Λ : T, ∀ i, ∃ a ∈ Λ.1, a - b i ∈ perp L Hm Y ∧
      ∃ c ∈ Λ₁, c - (a - b i) ∈ Y := by
    intro Λ i
    obtain ⟨-, -, h3, -⟩ := DualInter.dual_inter L Hm h Λ.1 Λ.2.1 m y hy
    obtain ⟨-, h2, -, -⟩ := DualInter.dual_inter L Hm h Λ₁ hΛ₁.1 m y hy
    rw [hY] at h2 h3
    obtain ⟨a, ha, hab⟩ := (h3 (b i)).1 fun x hx hxY =>
      hsym _ _ (((hMd _).1 (hbM i)).2 x ((hM _ Λ.2 x).2 ⟨hx, hxY⟩))
    obtain ⟨c, hc, hca⟩ := (h2 (a - b i)).1 fun x hx hxY => by
      rw [DualInter.sub_r, hxY _ ((hMd _).1 (hbM i)).1, sub_zero]
      exact (Λ.2.1.2 a).2 ha x ((h0 _ Λ.2 x).1 ((h0 _ hΛ₁ x).2 ⟨hx, hxY⟩)).1
    exact ⟨a, ha, by simpa using (perp L Hm Y).neg_mem hab, c, hc, by simpa using Y.neg_mem hca⟩
  choose a ha hab c hc1 hca using hlift
  have hle : ∀ Λ Λ' : T, (∀ i, a Λ i ∈ Λ'.1) → Λ.1 ≤ Λ'.1 := by
    intro Λ Λ' hi l hl
    obtain ⟨u, hu, w, hw, huw⟩ := Submodule.mem_sup.1 (hc ▸ Submodule.mem_top : l ∈ Y ⊔ perp L Hm Y)
    have hu' : l - w = u := by rw [← huw]; simp
    have h1 := hproj _ Λ.2 l hl w hw (hu' ▸ hu)
    rw [hb] at h1
    obtain ⟨s, hs⟩ := (Submodule.mem_span_range_iff_exists_fun L.O).1 h1
    have h2 : l - ∑ i, s i • a Λ i ∈ Λ₀ := by
      refine (h0 _ Λ.2 _).2 ⟨Λ.1.sub_mem hl (Λ.1.sum_mem fun i _ => Λ.1.smul_mem _ (ha Λ i)), ?_⟩
      have : l - ∑ i, s i • a Λ i = w - ∑ i, s i • (a Λ i - b i) := by
        simp only [smul_sub, Finset.sum_sub_distrib, hs]; abel
      rw [this]
      exact Submodule.sub_mem _ hw (Submodule.sum_mem _ fun i _ =>
        Submodule.smul_mem _ (s i : E) (hab Λ i))
    have h3 := Λ'.1.add_mem ((h0 _ Λ'.2 _).1 h2).1
      (Λ'.1.sum_mem (t := Finset.univ) fun i _ => Λ'.1.smul_mem (s i) (hi i))
    rwa [sub_add_cancel] at h3
  let Q := Md.toAddSubgroup ⧸ Mh.toAddSubgroup.addSubgroupOf Md.toAddSubgroup
  have hQ : Nat.card Q = Mh.toAddSubgroup.relIndex Md.toAddSubgroup := rfl
  have : Finite Q := Nat.finite_of_card_ne_zero (hQ ▸ hN)
  let Φ : T → ι → Q := fun Λ i =>
    QuotientAddGroup.mk ⟨c Λ i - (a Λ i - b i), hproj _ hΛ₁ _ (hc1 Λ i) _ (hab Λ i) (hca Λ i)⟩
  have key : ∀ Λ Λ' : T, Φ Λ = Φ Λ' → ∀ i, a Λ i ∈ Λ'.1 := by
    intro Λ Λ' he i
    have h1 : -(c Λ i - (a Λ i - b i)) + (c Λ' i - (a Λ' i - b i)) ∈ Mh :=
      QuotientAddGroup.eq.1 (congrFun he i)
    have h2 : a Λ i - a Λ' i ∈ Λ₀ := by
      refine (h0 _ hΛ₁ _).2 ⟨?_, ?_⟩
      · have := Λ₁.add_mem ((hM _ hΛ₁ _).1 h1).1 (Λ₁.sub_mem (hc1 Λ i) (hc1 Λ' i))
        convert this using 1; abel
      · have := (perp L Hm Y).sub_mem (hab Λ i) (hab Λ' i)
        convert this using 1; abel
    have h3 := Λ'.1.add_mem ((h0 _ Λ'.2 _).1 h2).1 (ha Λ' i)
    rwa [sub_add_cancel] at h3
  have hinj : Function.Injective Φ := fun Λ Λ' he =>
    Subtype.ext (le_antisymm (hle _ _ (key _ _ he)) (hle _ _ (key _ _ he.symm)))
  have : Finite T := Finite.of_injective Φ hinj
  have h4 := Nat.card_le_card_of_injective Φ hinj
  rw [Nat.card_fun, hQ, Nat.card_eq_fintype_card (α := ι)] at h4
  rw [← (Set.toFinite T).cast_ncard_eq, ← Nat.card_coe_set_eq]
  exact_mod_cast h4

theorem gluing_count : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ C, S.IsCls C → ∀ p ∈ C, ∀ Mh Λ₀ : Submodule L.O S.V, S.Mof p.1 p.2 ≤ Mh → (({Λ : Submodule L.O S.V | IsSD L S.Hm Λ ∧ S.sat Λ = Mh ∧ Λ ⊓ S.W0.restrictScalars L.O = Λ₀}.encard : ℕ∞) : ℝ≥0∞) ≤ (S.q : ℝ≥0∞) ^ (2 * S.a.toNat * (2 * r + 2)) := by
  intro F _ _ _ _ _ E _ _ _ L r k S C hC p hp Mh Λ₀ hM
  rcases {Λ : Submodule L.O S.V | IsSD L S.Hm Λ ∧ S.sat Λ = Mh ∧
    Λ ⊓ S.W0.restrictScalars L.O = Λ₀}.eq_empty_or_nonempty with h0 | ⟨Λ₁, hΛ₁⟩
  · simp [h0]
  obtain ⟨n, hn, n', hn', rfl⟩ := hC
  rw [((GlobalTheory.HL.FrameClass.frame_classes L r k S _ _).2.1 p hp).2] at hM
  obtain ⟨⟨c, hc0, hca, hdet⟩, -, hsp⟩ := GlobalTheory.T.frameLattice_gramDet_and_minors_orbit_invariant L r k S n hn n' hn'
  obtain ⟨hli, hcompl, -⟩ := GlobalTheory.FrameBasic.main L r k S
  have hMh : ∀ x, x ∈ Mh ↔ x ∈ Λ₁ ∧ x ∈ S.ME := fun x => by rw [← hΛ₁.2.1]; rfl
  let Md : Submodule L.O S.V :=
    { carrier := {x | x ∈ S.ME ∧ ∀ z ∈ Mh, hf L S.Hm x z ∈ L.O}
      zero_mem' := ⟨S.ME.zero_mem, fun z _ => by simp [hf]⟩
      add_mem' := by
        rintro u v ⟨hu, hu'⟩ ⟨hv, hv'⟩
        refine ⟨S.ME.add_mem hu hv, fun z hz => ?_⟩
        have : hf L S.Hm (u + v) z = hf L S.Hm u z + hf L S.Hm v z :=
          (DualInter.hfL L S.Hm z).map_add u v
        rw [this]
        exact L.O.add_mem (hu' z hz) (hv' z hz)
      smul_mem' := by
        rintro s u ⟨hu, hu'⟩
        refine ⟨S.ME.smul_mem (s : E) hu, fun z hz => ?_⟩
        have : hf L S.Hm (s • u) z = s * hf L S.Hm u z := DualInter.smul_l L S.Hm s u z
        rw [this]
        exact L.O.mul_mem s.2 (hu' z hz) }
  obtain ⟨-, hidx, -, b, hb⟩ := GlobalTheory.T.card_discriminantModule_integralOverlattice_span L S.Hm S.herm S.ϖ S.ϖ_irr _ c hc0 hdet Mh Md
    (by rw [Set.Sum.elim_range]; exact hM)
    (fun x hx => by rw [hsp]; exact ((hMh x).1 hx).2)
    (fun x hx z hz => (hΛ₁.1.2 z).2 ((hMh z).1 hz).1 x ((hMh x).1 hx).1)
    (fun x => by rw [hsp]; rfl)
  rw [hca] at hidx
  have hq : resQ S.ϖ ^ (2 * S.a.toNat) ≠ 0 := pow_ne_zero _ (resQ_ne_zero _ S.ϖ_irr)
  have hN : Mh.toAddSubgroup.relIndex Md.toAddSubgroup ≠ 0 := fun h => hq (by rw [← hidx, h, zero_mul])
  have hNle : Mh.toAddSubgroup.relIndex Md.toAddSubgroup ≤ S.q ^ (2 * S.a.toNat) :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero hq) (Dvd.intro _ hidx)
  have hY : Submodule.span E (Set.range (Sum.elim S.f S.f' ∘ finSumFinEquiv.symm)) = S.ME := by
    rw [finSumFinEquiv.symm.surjective.range_comp, Set.Sum.elim_range, Submodule.span_union]
    have : {i : Fin (r + 1) | (i : ℕ) < r + 1} = Set.univ := Set.eq_univ_of_forall fun i => i.2
    simp only [Frames.ME, Frames.spanTo, this, Set.image_univ]
  have h1 := encard_le S.herm (hli.comp _ finSumFinEquiv.symm.injective) hY hcompl.sup_eq_top
    Mh Λ₀ Md (fun _ => Iff.rfl) b hb hN
  have h2 : Mh.toAddSubgroup.relIndex Md.toAddSubgroup ^ Fintype.card (Fin (r + 1) ⊕ Fin (r + 1))
      ≤ S.q ^ (2 * S.a.toNat * (2 * r + 2)) := by
    rw [pow_mul, show Fintype.card (Fin (r + 1) ⊕ Fin (r + 1)) = 2 * r + 2 by simp; ring]
    exact Nat.pow_le_pow_left hNle _
  have h3 := h1.trans (Nat.cast_le.2 h2)
  have h4 := ENat.toENNReal_le.2 h3
  rw [ENat.toENNReal_coe, Nat.cast_pow] at h4
  exact h4

end GlobalTheory.HL.Gluing
end
end
