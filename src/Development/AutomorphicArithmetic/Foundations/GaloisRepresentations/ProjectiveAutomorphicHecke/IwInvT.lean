module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HeckePairTop
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwDomMul
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwHeckePairIwC
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwHkApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwMemIwC
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTracePowRestrictNeZero

section

@[expose] public section

noncomputable section

open ValuativeRel GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.GLDoubling

namespace GlobalTheory.IwahoriUnit

section Gen

variable {G : Type} [Group G]

def cosets (I : Subgroup G) (x : G) : Set (G ⧸ I) :=
  (QuotientGroup.mk : G → G ⧸ I) '' DoubleCoset.doubleCoset x I I

theorem cosets_eq_orbit (I : Subgroup G) (x : G) : cosets I x = MulAction.orbit I (x : G ⧸ I) := by
  ext q
  constructor
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := DoubleCoset.mem_doubleCoset.1 hg
    refine ⟨⟨a, ha⟩, ?_⟩
    show ((a * x : G) : G ⧸ I) = ((a * x * b : G) : G ⧸ I)
    rw [QuotientGroup.mk_mul_of_mem _ hb]
  · rintro ⟨a, rfl⟩
    exact ⟨a * x * 1, DoubleCoset.mem_doubleCoset.2 ⟨a, a.2, 1, one_mem _, rfl⟩, by rw [mul_one]; rfl⟩

variable {E V : Type} [Field E] [AddCommGroup V] [Module E V]

theorem fixed_eq_fixd (π : Representation E G V) (I : Subgroup G) : fixed π I = UpperTheory.V.Hi.fixd π I := by
  ext v
  constructor
  · intro h u hu
    simpa using h ⟨u, hu⟩
  · intro h u
    simpa using h u u.2

theorem hk_apply (π : Representation E G V) (I : Subgroup G) (x : G) (h : (cosets I x).Finite)
    (v : UpperTheory.V.Hi.fixd π I) :
    (UpperTheory.V.AlgebraTools.hk π I x v : V) = ∑ᶠ q ∈ cosets I x, π q.out v := by
  rw [cosets_eq_orbit] at h ⊢
  have : Finite (MulAction.orbit I (x : G ⧸ I)) := h
  have := Fintype.ofFinite (MulAction.orbit I (x : G ⧸ I))
  rw [UpperTheory.V.AlgebraTools.hk, (UpperTheory.V.AlgebraTools.hkApply E G V π I I x h).1 v, UpperTheory.V.Hi.dc,
    ← finsum_set_coe_eq_finsum_mem, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, LinearMap.sum_apply]

end Gen

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {N : ℕ}

theorem finite_cosets (x : GL (Fin N) k) : (cosets (iwahori k (Fin N)) x).Finite := by
  rw [cosets_eq_orbit, ← (UpperTheory.V.AlgebraTools.memIwC k N ⊤).2.1]
  exact (UpperTheory.V.AlgebraTools.heckePairIwC k N ⊤).1 x

theorem dom_of_antitone {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) {ν : Fin N → ℤ} (hν : Antitone ν) :
    UpperTheory.V.AlgebraTools.Dom (fun i => ϖ ^ ν i) := by
  intro i j hij
  have h1 : valuation k (ϖ : k) ≤ 1 := (hϖ ▸ uniformizer_lt_one).le
  have h0 : 0 < valuation k (ϖ : k) := (Valuation.pos_iff _).2 ϖ.ne_zero
  simp only [Units.val_zpow_eq_zpow_val, map_zpow₀]
  exact zpow_le_zpow_right_of_le_one₀ h0 h1 (hν hij)

theorem torusElt_pow (ϖ : kˣ) (ν : Fin N → ℤ) (m : ℕ) :
    torusElt k (Fin N) ϖ ν ^ m = diagT k (Fin N) ((fun i => ϖ ^ ν i) ^ m) := by
  rw [map_pow]; rfl

theorem dom_pow {t : Fin N → kˣ} (ht : UpperTheory.V.AlgebraTools.Dom t) (m : ℕ) : UpperTheory.V.AlgebraTools.Dom (t ^ m) := by
  intro i j hij
  simp only [Pi.pow_apply, Units.val_pow_eq_pow_val, map_pow]
  exact pow_le_pow_left₀ zero_le' (ht i j hij) m

theorem exists_equiv_doubleCoset (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (N : ℕ) (ϖ : kˣ) (hϖ : valuation k (ϖ : k) = uniformizer k)
    (ν : Fin N → ℤ) (hν : Antitone ν) (E V : Type) [Field E] [CharZero E] [AddCommGroup V] [Module E V]
    (π : Representation E (GL (Fin N) k) V) :
    (∀ m : ℕ, (cosets (iwahori k (Fin N)) (torusElt k (Fin N) ϖ ν ^ m)).Finite) ∧
    ∃ T : fixed π (iwahori k (Fin N)) ≃ₗ[E] fixed π (iwahori k (Fin N)),
      (∀ v, (T v : V) = ∑ᶠ q ∈ cosets (iwahori k (Fin N)) (torusElt k (Fin N) ϖ ν), π q.out v) ∧
      ∀ (m : ℕ) v, ((T ^ m) v : V) =
        ∑ᶠ q ∈ cosets (iwahori k (Fin N)) (torusElt k (Fin N) ϖ ν ^ m), π q.out v := by
  refine ⟨fun m => finite_cosets _, ?_⟩
  have hd := dom_of_antitone hϖ hν
  have hq : IsUnit ((GlobalTheory.SplitWeil.resCard k : ℕ) : E) := by
    refine IsUnit.mk0 _ (Nat.cast_ne_zero.2 ?_)
    exact Nat.card_pos.ne'
  obtain ⟨hmul, hunit, -⟩ := UpperTheory.V.AlgebraTools.domMul k N ⊤ E V π
  rw [(UpperTheory.V.AlgebraTools.memIwC k N ⊤).2.1] at hmul hunit
  rw [fixed_eq_fixd]
  have hone : UpperTheory.V.AlgebraTools.hk π (iwahori k (Fin N)) (diagT k (Fin N) 1) = 1 := by
    have h := hmul 1 1 UpperTheory.V.AlgebraTools.dom_one UpperTheory.V.AlgebraTools.dom_one
    rw [mul_one] at h
    exact (hunit hq 1 UpperTheory.V.AlgebraTools.dom_one).mul_left_cancel (h.trans (mul_one _).symm)
  have hpow : ∀ m : ℕ, UpperTheory.V.AlgebraTools.hk π (iwahori k (Fin N)) (diagT k (Fin N) fun i => ϖ ^ ν i) ^ m =
      UpperTheory.V.AlgebraTools.hk π (iwahori k (Fin N)) (diagT k (Fin N) ((fun i => ϖ ^ ν i) ^ m)) := by
    intro m
    induction m with
    | zero => rw [pow_zero, pow_zero, hone]
    | succ m ih => rw [pow_succ, pow_succ, ih, hmul _ _ (dom_pow hd m) hd]
  have hb := (Module.End.isUnit_iff _).1 (hunit hq _ hd)
  refine ⟨LinearEquiv.ofBijective _ hb, fun v => hk_apply π _ _ (finite_cosets _) v, fun m v => ?_⟩
  rw [← hk_apply π _ _ (finite_cosets _) v, torusElt_pow, ← hpow]
  congr 1
  rw [LinearEquiv.pow_apply, Module.End.pow_apply]
  rfl

end GlobalTheory.IwahoriUnit
end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.IwInvT

section

@[expose] public section

noncomputable section

open Formalism.UG GlobalTheory.PRep GlobalTheory.IwahoriUnit
open scoped Classical

namespace UpperTheory.Gal.CertificateRingHomMap

variable {G : Type} [Group G]

private def cfun (K : Subgroup G) : Submodule ℂ (G → ℂ) where
  carrier := {f | (∀ g, ∀ b ∈ K, f (g * b) = f g) ∧ ∃ S : Finset G, ∀ g, f g ≠ 0 → ∃ s ∈ S, ∃ b ∈ K, g = s * b}
  zero_mem' := ⟨fun _ _ _ => rfl, ∅, fun _ h => (h rfl).elim⟩
  add_mem' := by
    rintro f f' ⟨hf, S, hS⟩ ⟨hf', S', hS'⟩
    refine ⟨fun g b hb => by simp [hf g b hb, hf' g b hb], S ∪ S', fun g hg => ?_⟩
    by_cases h : f g = 0
    · obtain ⟨s, hs, e⟩ := hS' g (by simpa [h] using hg)
      exact ⟨s, Finset.mem_union_right _ hs, e⟩
    · obtain ⟨s, hs, e⟩ := hS g h
      exact ⟨s, Finset.mem_union_left _ hs, e⟩
  smul_mem' := by
    rintro c f ⟨hf, S, hS⟩
    exact ⟨fun g b hb => by simp [hf g b hb], S, fun g hg => hS g fun h => hg (by simp [h])⟩

private def lrep (K : Subgroup G) : Representation ℂ G (cfun K) where
  toFun x :=
    { toFun := fun f => ⟨fun g => f.1 (x⁻¹ * g), fun g b hb => (congrArg f.1 (mul_assoc _ _ _).symm).trans (f.2.1 _ b hb), by
        obtain ⟨S, hS⟩ := f.2.2
        refine ⟨S.image (x * ·), fun g hg => ?_⟩
        obtain ⟨s, hs, b, hb, e⟩ := hS _ hg
        exact ⟨x * s, Finset.mem_image_of_mem _ hs, b, hb, by rw [mul_assoc, ← e, mul_inv_cancel_left]⟩⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_one' := LinearMap.ext fun f => Subtype.ext (funext fun g => by simp)
  map_mul' x y := LinearMap.ext fun f => Subtype.ext (funext fun g => by simp [mul_assoc])

private theorem exists_conv_inv (K : Subgroup G) (hK : IsCommensurated K) (t : G) (hfin : ∀ x, (cosets K x).Finite)
    (T : fixed (lrep K) K ≃ₗ[ℂ] fixed (lrep K) K) (hT : ∀ v, (T v : cfun K) = ∑ᶠ q ∈ cosets K t, lrep K q.out v) :
    ∃ φ ∈ Hecke ℂ K, conv K φ (dosetInd ℂ K t) = dosetInd ℂ K 1 := by
  have toH : ∀ v : fixed (lrep K) K, v.1.1 ∈ Hecke ℂ K := fun v => by
    refine ⟨fun a b g => ?_, ?_⟩
    · have h := congrFun (congrArg Subtype.val (GlobalTheory.LGrp.mem_fixed.1 v.2 a⁻¹ (inv_mem a.2))) g
      rw [v.1.2.1 _ b b.2]
      simpa [lrep] using h
    · obtain ⟨S, hS⟩ := v.1.2.2
      refine ⟨S, fun g hg => ?_⟩
      obtain ⟨s, hs, b, hb, e⟩ := hS g hg
      exact ⟨s, hs, 1, ⟨b, hb⟩, by simpa using e⟩
  have ofH : ∀ f ∈ Hecke ℂ K, ∃ v : fixed (lrep K) K, v.1.1 = f := fun f hf => by
    obtain ⟨h1, S, hS⟩ := hf
    refine ⟨⟨⟨f, fun g b hb => by simpa using h1 1 ⟨b, hb⟩ g, S.biUnion fun s => (hfin s).toFinset.image Quotient.out, fun g hg => ?_⟩,
      GlobalTheory.LGrp.mem_fixed.2 fun a ha => Subtype.ext (funext fun g => ?_)⟩, rfl⟩
    · obtain ⟨s, hs, a, b, e⟩ := hS g hg
      obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K g
      refine ⟨(g : G ⧸ K).out, Finset.mem_biUnion.2 ⟨s, hs, Finset.mem_image_of_mem _ ((hfin s).mem_toFinset.2
        ⟨g, DoubleCoset.mem_doubleCoset.2 ⟨a, a.2, b, b.2, e⟩, rfl⟩)⟩, k⁻¹, inv_mem k.2, by rw [hk]; simp⟩
    · simpa [lrep] using h1 ⟨a⁻¹, inv_mem ha⟩ 1 g
  have hTc : ∀ v, (T v).1.1 = conv K (dosetInd ℂ K t) v.1.1 := fun v => by
    funext g
    rw [hT, finsum_mem_eq_finite_toFinset_sum _ (hfin t), Submodule.coe_sum, Finset.sum_apply, conv,
      finsum_eq_sum_of_support_subset (s := (hfin t).toFinset)]
    · refine Finset.sum_congr rfl fun q hq => ?_
      obtain ⟨y, hy, rfl⟩ := (hfin t).mem_toFinset.1 hq
      obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K y
      obtain ⟨a, ha, b, hb, e⟩ := DoubleCoset.mem_doubleCoset.1 hy
      have : (y : G ⧸ K).out ∈ DoubleCoset.doubleCoset t (K : Set G) K :=
        DoubleCoset.mem_doubleCoset.2 ⟨a, ha, b * k, mul_mem hb k.2, by rw [hk, e, mul_assoc]⟩
      rw [dosetInd, Set.indicator_of_mem this, Pi.one_apply, one_mul]
      rfl
    · intro q hq
      have h : dosetInd ℂ K t q.out ≠ 0 := left_ne_zero_of_mul hq
      exact Finset.mem_coe.2 ((hfin t).mem_toFinset.2 ⟨q.out, Set.mem_of_indicator_ne_zero h, q.out_eq'⟩)
  have ht := Final.DosetIndMem G K ℂ t
  have h1 := Final.DosetIndMem G K ℂ 1
  obtain ⟨e, he⟩ := ofH _ h1
  have hφ := toH (T.symm e)
  have h2 : conv K (dosetInd ℂ K t) (T.symm e).1.1 = dosetInd ℂ K 1 := by rw [← hTc, T.apply_symm_apply, he]
  refine ⟨_, hφ, ?_⟩
  obtain ⟨u, hu⟩ := ofH _ (Final.HeckeConvMem G K ℂ hK _ hφ _ ht)
  rw [← hu, ← he]
  congr 2
  apply T.injective
  refine Subtype.ext (Subtype.ext ?_)
  rw [hTc, hTc, hu, he, ← Final.HeckeAssoc G K ℂ hK _ ht _ hφ _ ht, h2,
    (Final.HeckeUnit G K ℂ _ ht).1, (Final.HeckeUnit G K ℂ _ ht).2]

private theorem comm_of_fin (K : Subgroup G) (hfin : ∀ x, (cosets K x).Finite) : IsCommensurated K := by
  intro g
  have h := hfin g
  rw [cosets_eq_orbit] at h
  have e : (K.map (MulAut.conj g).toMonoidHom).subgroupOf K = MulAction.stabilizer K (g : G ⧸ K) := by
    ext k
    rw [Subgroup.mem_subgroupOf, MulAction.mem_stabilizer_iff, Subgroup.mem_map_equiv]
    show _ ↔ ((k.1 * g : G) : G ⧸ K) = g
    rw [eq_comm, QuotientGroup.eq]
    simp [mul_assoc]
  rw [Subgroup.relIndex, e, MulAction.index_stabilizer]
  exact ((Set.ncard_pos h).2 ⟨_, MulAction.mem_orbit_self _⟩).ne'


open ValuativeRel GlobalTheory.SmGL GlobalTheory.GLDoubling in
theorem iwInvT (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ϖ : kˣ)
    (hϖ : valuation k (ϖ : k) = uniformizer k) (ν : Fin n → ℤ) (hν : Antitone ν) :
    ∃ φ ∈ Hecke ℂ (iwahori k (Fin n)), conv (iwahori k (Fin n)) φ (dosetInd ℂ (iwahori k (Fin n)) (torusElt k (Fin n) ϖ ν)) =
      dosetInd ℂ (iwahori k (Fin n)) 1 := by
  obtain ⟨-, T, hT, -⟩ := exists_equiv_doubleCoset k n ϖ hϖ ν hν ℂ _ (lrep (iwahori k (Fin n)))
  exact exists_conv_inv _ (comm_of_fin _ finite_cosets) _ finite_cosets T hT

end UpperTheory.Gal.CertificateRingHomMap
end
end
end
