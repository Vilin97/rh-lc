module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueFixedPointOfAdicContraction
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DvdOfForallSubMulMem
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsSystemOfParametersInsert
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Order.Preorder.Chain
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.SetTheory.ZFC.PSet
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.HaveILetI
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
public import Mathlib.Algebra.CharP.Basic
public import Mathlib.Algebra.CharP.Frobenius
public import Mathlib.Algebra.CharP.Reduced
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.FieldTheory.KummerPolynomial
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsDVROfClosedSubringPrincipal
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsIntegrallyClosedPowerSeries
import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.AdicCompletion.Topology
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.Topology.Sheaves.Presheaf
public import ReciprocityTheory.AdicCompleteness.IsAdicCompleteComapConstantCoeff
public import ReciprocityTheory.CommutativeAlgebra.SaturatedChains.Integral

-- Source module: Development.AbelianVarietyTheory.Proofs.UnitaryExistence.GraphRingMono

section

@[expose] public section

open IsLocalRing Polynomial

namespace GlobalTheory.PBasis

variable {k : Type} [Field k]

def graphRing (p : ℕ) {Q : Type} [CommRing Q] (f : k →+* Q) (g : k → Q) (B : Set k) :
    Subring (k × Q) :=
  Subring.closure (Set.range (fun x : k => (x ^ p, f x)) ∪ (fun b => (b, g b)) '' B)

def Indep (p : ℕ) (B : Set k) : Prop :=
  ∀ (Q : Type) [CommRing Q] (f : k →+* Q) (g : k → Q), (∀ b ∈ B, g b ^ p = f b) →
    ∀ z ∈ graphRing p f g B, z.1 = 0 → z.2 = 0

lemma graphRing_mono (p : ℕ) {Q : Type} [CommRing Q] (f : k →+* Q) (g : k → Q) {B C : Set k}
    (h : B ⊆ C) : graphRing p f g B ≤ graphRing p f g C :=
  Subring.closure_mono (Set.union_subset_union_right _ (Set.image_mono h))

lemma map_graphRing (p : ℕ) {Q : Type} [CommRing Q] (f : k →+* Q) (g : k → Q) (B : Set k) :
    (graphRing p f g B).map (RingHom.fst k Q) =
      Subring.closure (Set.range (fun x : k => x ^ p) ∪ B) := by
  unfold graphRing
  rw [RingHom.map_closure, Set.image_union, ← Set.range_comp, Set.image_image]
  congr 2
  simp

lemma indep_empty {p : ℕ} (hp : p.Prime) (h0 : (p : k) = 0) : Indep p (∅ : Set k) := by
  haveI := Fact.mk hp
  haveI : CharP k p := (CharP.charP_iff_prime_eq_zero hp).2 h0
  intro Q _ f g _ z hz h1
  have : graphRing p f g ∅ ≤ ((frobenius k p).prod f).range := by
    unfold graphRing
    rw [Subring.closure_le]
    rintro _ (⟨x, rfl⟩ | ⟨x, hx, _⟩)
    · exact ⟨x, by simp [frobenius_def]⟩
    · exact hx.elim
  obtain ⟨x, rfl⟩ := this hz
  have hx : x ^ p = 0 := by simpa [frobenius_def] using h1
  have : x = 0 := pow_eq_zero_iff hp.ne_zero |>.1 hx
  simp [this]

lemma indep_sUnion (p : ℕ) (c : Set (Set k)) (hc : IsChain (· ⊆ ·) c) (hne : c.Nonempty)
    (h : ∀ B ∈ c, Indep p B) : Indep p (⋃₀ c) := by
  intro Q _ f g hg z hz h1
  haveI : Nonempty c := hne.to_subtype
  have hdir : Directed (· ≤ ·) (fun B : c => graphRing p f g B.1) := by
    intro B C
    rcases hc.total B.2 C.2 with h | h
    · exact ⟨C, graphRing_mono p f g h, le_rfl⟩
    · exact ⟨B, le_rfl, graphRing_mono p f g h⟩
  have : graphRing p f g (⋃₀ c) ≤ ⨆ B : c, graphRing p f g B.1 := by
    rw [graphRing, Subring.closure_le]
    rintro _ (⟨x, rfl⟩ | ⟨x, ⟨B, hB, hx⟩, rfl⟩)
    · obtain ⟨B, hB⟩ := hne
      exact le_iSup (fun B : c => graphRing p f g B.1) ⟨B, hB⟩
        (Subring.subset_closure (Or.inl ⟨x, rfl⟩))
    · exact le_iSup (fun B : c => graphRing p f g B.1) ⟨B, hB⟩
        (Subring.subset_closure (Or.inr ⟨x, hx, rfl⟩))
  obtain ⟨B, hB⟩ := (Subring.mem_iSup_of_directed hdir).1 (this hz)
  exact h B.1 B.2 Q f g (fun b hb => hg b ⟨B.1, B.2, hb⟩) z hB h1

def powField {p : ℕ} (hp : p ≠ 0) (B : Set k) : Subfield k where
  toSubring := Subring.closure (Set.range (fun x : k => x ^ p) ∪ B)
  inv_mem' := by
    intro x hx
    change x ∈ Subring.closure (Set.range (fun x : k => x ^ p) ∪ B) at hx
    change x⁻¹ ∈ Subring.closure (Set.range (fun x : k => x ^ p) ∪ B)
    rcases eq_or_ne x 0 with rfl | hx0
    · simpa using hx
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp
    have : x⁻¹ = x ^ n * (x⁻¹) ^ (n + 1) := by
      rw [pow_succ, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hx0]; simp
    rw [this]
    exact mul_mem (pow_mem hx n) (Subring.subset_closure (Or.inl ⟨x⁻¹, rfl⟩))

lemma indep_insert {p : ℕ} (hp : p.Prime) (h0 : (p : k) = 0) {B : Set k} (hB : Indep p B) {a : k}
    (ha : a ∉ Subring.closure (Set.range (fun x : k => x ^ p) ∪ B)) : Indep p (insert a B) := by
  haveI := Fact.mk hp
  haveI : CharP k p := (CharP.charP_iff_prime_eq_zero hp).2 h0
  intro Q _ f g hg z hz h1
  have hga : g a ^ p = f a := hg a (Set.mem_insert _ _)
  have hI := hB Q f g (fun b hb => hg b (Set.mem_insert_of_mem _ hb))
  set S := graphRing p f g B with hS
  let K := powField hp.ne_zero B
  have hK : ∀ s : S, (s : k × Q).1 ∈ K := by
    intro s
    change _ ∈ Subring.closure (Set.range (fun x : k => x ^ p) ∪ B)
    rw [← map_graphRing p f g B]
    exact ⟨s, s.2, rfl⟩
  let ψ : S →+* K := ((RingHom.fst k Q).comp S.subtype).codRestrict K hK
  have hψ : Function.Injective ψ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro s hs
    have h1 : (s : k × Q).1 = 0 := congrArg Subtype.val hs
    exact Subtype.ext (Prod.ext h1 (hI s s.2 h1))
  let ev : S[X] →+* k × Q := eval₂RingHom S.subtype (a, g a)
  have hle : graphRing p f g (insert a B) ≤ ev.range := by
    rw [graphRing, Subring.closure_le]
    rintro _ (⟨x, rfl⟩ | ⟨x, rfl | hx, rfl⟩)
    · exact ⟨C ⟨_, Subring.subset_closure (Or.inl ⟨x, rfl⟩)⟩, by simp [ev]⟩
    · exact ⟨X, by simp [ev]⟩
    · exact ⟨C ⟨_, Subring.subset_closure (Or.inr ⟨x, hx, rfl⟩)⟩, by simp [ev]⟩
  obtain ⟨P, rfl⟩ := hle hz
  let c : S := ⟨(a ^ p, f a), Subring.subset_closure (Or.inl ⟨a, rfl⟩)⟩
  have hq : (X ^ p - C c : S[X]).Monic := monic_X_pow_sub_C c hp.ne_zero
  have hevq : ev (X ^ p - C c) = 0 := by
    simp [ev, c, hga]
  have hR : ev (P %ₘ (X ^ p - C c)) = ev P := by
    conv_rhs => rw [← modByMonic_add_div P (X ^ p - C c)]
    rw [map_add (f := _), map_mul, hevq, zero_mul, add_zero]
  have hirr : Irreducible (X ^ p - C (ψ c) : K[X]) := by
    apply X_pow_sub_C_irreducible_of_prime hp
    intro b hb
    have h2 : (b : k) ^ p = a ^ p := congrArg Subtype.val hb
    have h3 : (b : k) = a := frobenius_inj k p h2
    exact ha (h3 ▸ b.2)
  have haev : ∀ T : S[X], aeval a (T.map ψ) = (ev T).1 := by
    intro T
    rw [aeval_def, eval₂_map]
    change _ = RingHom.fst k Q (eval₂ S.subtype (a, g a) T)
    rw [hom_eval₂]
    rfl
  have hmapq : (X ^ p - C c : S[X]).map ψ = X ^ p - C (ψ c) := by simp
  have hmin : X ^ p - C (ψ c) = minpoly K a :=
    minpoly.eq_of_irreducible_of_monic hirr (by rw [← hmapq, haev, hevq]; rfl)
      (monic_X_pow_sub_C _ hp.ne_zero)
  have hdvd : (X ^ p - C c : S[X]).map ψ ∣ (P %ₘ (X ^ p - C c)).map ψ := by
    rw [hmapq, hmin]
    exact minpoly.dvd K a (by rw [haev, hR, h1])
  haveI : Nontrivial S := ψ.domain_nontrivial
  have hz0 : (P %ₘ (X ^ p - C c)).map ψ = 0 := by
    apply eq_zero_of_dvd_of_degree_lt hdvd
    rw [degree_map_eq_of_injective hψ, degree_map_eq_of_injective hψ]
    exact degree_modByMonic_lt P hq
  rw [Polynomial.map_eq_zero_iff hψ] at hz0
  rw [← hR, hz0, map_zero]
  rfl

theorem exists_pBasis : ∀ (k : Type) [Field k] (p : ℕ), p.Prime → (p : k) = 0 → ∃ B : Set k, Subring.closure (Set.range (fun x : k => x ^ p) ∪ B) = ⊤ ∧ ∀ (Q : Type) [CommRing Q] (f : k →+* Q) (g : k → Q), (∀ b ∈ B, g b ^ p = f b) → ∃ σ : k →+* Q, (∀ x, σ (x ^ p) = f x) ∧ ∀ b ∈ B, σ b = g b := by
  intro k _ p hp h0
  obtain ⟨B, -, hB⟩ := zorn_subset_nonempty {B : Set k | Indep p B}
    (fun c hc hch hne => ⟨⋃₀ c, indep_sUnion p c hch hne hc, fun s hs => Set.subset_sUnion_of_mem hs⟩)
    ∅ (indep_empty hp h0)
  have htop : Subring.closure (Set.range (fun x : k => x ^ p) ∪ B) = ⊤ := by
    rw [eq_top_iff]
    intro a _
    by_contra ha
    have := hB.le_of_ge (indep_insert hp h0 hB.prop ha) (Set.subset_insert a B)
    exact ha (Subring.subset_closure (Or.inr (this (Set.mem_insert a B))))
  refine ⟨B, htop, fun Q _ f g hg => ?_⟩
  have hI := hB.prop Q f g hg
  set S := graphRing p f g B with hS
  let φ : S →+* k := (RingHom.fst k Q).comp S.subtype
  have hφ : Function.Bijective φ := by
    constructor
    · set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
      intro s hs
      exact Subtype.ext (Prod.ext hs (hI s s.2 hs))
    · intro x
      have : x ∈ S.map (RingHom.fst k Q) := by
        rw [hS, map_graphRing, htop]; trivial
      obtain ⟨s, hs, rfl⟩ := this
      exact ⟨⟨s, hs⟩, rfl⟩
  let e := RingEquiv.ofBijective φ hφ
  have key : ∀ s : S, ((RingHom.snd k Q).comp S.subtype).comp e.symm.toRingHom (s : k × Q).1 = (s : k × Q).2 := by
    intro s
    have : e.symm (s : k × Q).1 = s := e.symm_apply_apply s
    change ((e.symm (s : k × Q).1 : S) : k × Q).2 = _
    rw [this]
  refine ⟨((RingHom.snd k Q).comp S.subtype).comp e.symm.toRingHom, fun x => ?_, fun b hb => ?_⟩
  · exact key ⟨(x ^ p, f x), Subring.subset_closure (Or.inl ⟨x, rfl⟩)⟩
  · exact key ⟨(b, g b), Subring.subset_closure (Or.inr ⟨b, hb, rfl⟩)⟩

end GlobalTheory.PBasis
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CohenStructureFiniteOverNormalCompleteSubring

section

@[expose] public section

open IsLocalRing MvPowerSeries

namespace GlobalTheory.CohenStructure

theorem isDomain_mvPowerSeries (R : Type) [CommRing R] [IsDomain R] (n : ℕ) :
    IsDomain (MvPowerSeries (Fin n) R) :=
  NoZeroDivisors.to_isDomain _

theorem isIntegrallyClosed_mvPowerSeries (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] (n : ℕ) : IsIntegrallyClosed (MvPowerSeries (Fin n) R) := by
  induction n with
  | zero => exact IsIntegrallyClosed.of_equiv (isEmptyEquiv (Fin 0) R).toRingEquiv.symm
  | succ n ih =>
    have := isDomain_mvPowerSeries R n
    have := GlobalTheory.PowerSeriesNormal.isIntegrallyClosed_powerSeries (MvPowerSeries (Fin n) R)
    exact IsIntegrallyClosed.of_equiv (finSuccEquiv R n).toRingEquiv.symm

theorem isAdicComplete_of_ringEquiv {A B : Type} [CommRing A] [CommRing B] [IsLocalRing A]
    [IsLocalRing B] (e : A ≃+* B) [h : IsAdicComplete (maximalIdeal A) A] :
    IsAdicComplete (maximalIdeal B) B := by
  rw [← map_ringEquiv_maximalIdeal e, IsAdicComplete.congr_ringEquiv]
  exact h

theorem isAdicComplete_mvPowerSeries (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal R) R] (n : ℕ) :
    IsAdicComplete (maximalIdeal (MvPowerSeries (Fin n) R)) (MvPowerSeries (Fin n) R) := by
  induction n with
  | zero => exact isAdicComplete_of_ringEquiv (isEmptyEquiv (Fin 0) R).toRingEquiv.symm
  | succ n ih =>
    have := ReciprocityTheory.P1.isAdicComplete_ps (R := MvPowerSeries (Fin n) R)
    exact isAdicComplete_of_ringEquiv (finSuccEquiv R n).toRingEquiv.symm

theorem finite_quotient_of_pow_le {A S : Type} [CommRing A] [CommRing S] [Algebra A S]
    [IsNoetherianRing S] {I J : Ideal S} (h : ∀ s : S, ∃ a : A, s - algebraMap A S a ∈ I) {N : ℕ}
    (hN : I ^ N ≤ J) : Module.Finite A (S ⧸ J) := by
  have key : ∀ N : ℕ, ∃ F : Submodule A S, F.FG ∧ F ⊔ (I ^ N).restrictScalars A = ⊤ := by
    intro N
    induction N with
    | zero => exact ⟨⊥, Submodule.fg_bot, by simp⟩
    | succ N ih =>
      obtain ⟨F, hF, hF'⟩ := ih
      obtain ⟨G, hG⟩ : (I ^ N).FG := IsNoetherian.noetherian _
      refine ⟨F ⊔ Submodule.span A (G : Set S), hF.sup (Submodule.fg_span G.finite_toSet), ?_⟩
      rw [eq_top_iff, ← hF', sup_assoc]
      refine sup_le_sup_left (fun x hx => ?_) _
      have hx' : x ∈ Submodule.span S (G : Set S) := hG.ge hx
      obtain ⟨c, -, rfl⟩ := Submodule.mem_span_finset.1 hx'
      refine sum_mem fun y hy => ?_
      obtain ⟨a, ha⟩ := h (c y)
      have : c y • y = a • y + y * (c y - algebraMap A S a) := by
        rw [Algebra.smul_def a, smul_eq_mul]; ring
      rw [this]
      refine Submodule.add_mem_sup (Submodule.smul_mem _ _ (Submodule.subset_span hy)) ?_
      rw [pow_succ]
      exact Ideal.mul_mem_mul (hG.le (Ideal.subset_span hy)) ha
  obtain ⟨F, hF, hF'⟩ := key N
  have : Module.Finite A F := Module.Finite.iff_fg.2 hF
  refine Module.Finite.of_surjective ((Ideal.Quotient.mkₐ A J).toLinearMap ∘ₗ F.subtype) fun s => ?_
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective s
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 (hF'.ge (Submodule.mem_top (x := s)))
  exact ⟨⟨y, hy⟩, Ideal.Quotient.eq.2 (by simpa using hN hz)⟩

theorem injective_of_ringKrullDim_eq {A S : Type} [CommRing A] [IsDomain A] [CommRing S]
    [Algebra A S] [Module.Finite A S] {n : ℕ} (hA : ringKrullDim A = n) (hS : ringKrullDim S = n) :
    Function.Injective (algebraMap A S) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro r hr
  by_contra hr0
  have h1 := ReciprocityTheory.CA.ringKrullDim_quotient_eq_quotient_comap_of_isIntegral (A := A) (⊥ : Ideal S)
  have h2 := ringKrullDim_succ_le_of_surjective
    (Ideal.Quotient.mk ((⊥ : Ideal S).comap (algebraMap A S))) Ideal.Quotient.mk_surjective
    (mem_nonZeroDivisors_of_ne_zero hr0) (Ideal.Quotient.eq_zero_iff_mem.2 hr)
  rw [← h1, ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot S), hA, hS] at h2
  norm_cast at h2
  omega

theorem exists_finite_injective_of_isAdicComplete :
    ∀ (S : Type) [CommRing S] [IsDomain S] [IsLocalRing S] [CharZero S] (p : ℕ), p.Prime →
      (p : S) ∈ maximalIdeal S → IsNoetherianRing S → IsAdicComplete (maximalIdeal S) S →
      ∃ (A : Type) (_ : CommRing A) (_ : IsDomain A) (_ : IsLocalRing A) (i : A →+* S),
        Function.Injective i ∧ i.Finite ∧ IsNoetherianRing A ∧ IsIntegrallyClosed A ∧
          IsAdicComplete (maximalIdeal A) A := by
  intro S _ _ _ _ p hp h0 hn hc
  have hp0 : (p : S) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  obtain ⟨B, hB, hB'⟩ := GlobalTheory.PBasis.exists_pBasis (ResidueField S) p hp
    (by rw [← map_natCast (residue S), residue_eq_zero_iff]; exact h0)
  obtain ⟨Λ, h1, h2, h3⟩ := CoeffSubring.exists_coeffSubring hp hp0 h0 hB hB'
  obtain ⟨_, hm, hΛ⟩ := GlobalTheory.isDVR_of_closed_subring_principal S Λ p (by simpa using hp0) (by simpa using h0) hc h1 h2 h3
  obtain ⟨n, x, hx, hd, N, hN⟩ := GlobalTheory.exists_systemOfParameters_insert S p hp0 h0
  let A := MvPowerSeries (Fin n) Λ
  let φ : A →ₐ[Λ] S := mvEvalAdic Λ (maximalIdeal S) x hx
  letI : Algebra A S := φ.toRingHom.toAlgebra
  have : IsDomain A := isDomain_mvPowerSeries Λ n
  have hA := isAdicComplete_mvPowerSeries Λ n
  have hle : (maximalIdeal A).map (algebraMap A S) ≤ maximalIdeal S := by
    refine Ideal.map_le_iff_le_comap.2 fun g hg => ?_
    have h4 := algHom_sub_constantCoeff_mem φ (K := maximalIdeal S)
      (fun j => by simpa [φ] using hx j) g
    have h5 := FormalIsogeny.mem_maximalIdeal_iff_constantCoeff.1 hg
    rw [hm, Ideal.mem_span_singleton] at h5
    obtain ⟨c, hc⟩ := h5
    have h6 : algebraMap Λ S (constantCoeff g) ∈ maximalIdeal S := by
      rw [hc, map_mul, map_natCast]
      exact Ideal.mul_mem_right _ _ h0
    have h7 := add_mem h4 h6
    rwa [sub_add_cancel] at h7
  have hge : maximalIdeal S ^ N ≤ (maximalIdeal A).map (algebraMap A S) := by
    refine hN.trans (Ideal.span_le.2 ?_)
    rintro _ (rfl | ⟨i, rfl⟩)
    · rw [← map_natCast (algebraMap A S)]
      refine Ideal.mem_map_of_mem _ (FormalIsogeny.mem_maximalIdeal_iff_constantCoeff.2 ?_)
      rw [map_natCast, hm]
      exact Ideal.mem_span_singleton_self _
    · rw [← mvEvalAdic_X (A := Λ) (maximalIdeal S) x hx i]
      exact Ideal.mem_map_of_mem (algebraMap A S)
        (FormalIsogeny.mem_maximalIdeal_iff_constantCoeff.2 (by simp))
  have : IsHausdorff ((maximalIdeal A).map (algebraMap A S)) S :=
    IsHausdorff.of_isLocalRing _ _ (ne_top_of_le_ne_top (maximalIdeal.isMaximal _).ne_top hle)
  have : Module.Finite A (S ⧸ (maximalIdeal A).map (algebraMap A S)) := by
    refine finite_quotient_of_pow_le (fun s => ?_) hge
    obtain ⟨a, ha, h⟩ := h1 s
    refine ⟨C ⟨a, ha⟩, ?_⟩
    rwa [show algebraMap A S (C ⟨a, ha⟩) = a from mvEvalAdic_C _ x hx _]
  have hfin : Module.Finite A S := FormalIsogeny.finite_of_finite_quotient_map (maximalIdeal A)
  refine ⟨A, inferInstance, inferInstance, inferInstance, algebraMap A S,
    injective_of_ringKrullDim_eq (n := n + 1) ?_ (by rw [hd]; norm_cast), hfin, inferInstance,
    isIntegrallyClosed_mvPowerSeries Λ n, hA⟩
  rw [FormalIsogeny.ringKrullDim_mvPowerSeries, IsDiscreteValuationRing.ringKrullDim_eq_one,
    Nat.card_eq_fintype_card, Fintype.card_fin, add_comm]
  norm_cast

end GlobalTheory.CohenStructure
end
end
