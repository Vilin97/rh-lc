module

public import Development.AbelianVarietyTheory.Definitions.Divisors.PointSide
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumDoubleCosetFoldIntermediateSubgroup
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
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumDoubleCosetFoldIntermediateSubgroupStatement

section

@[expose] public section

open GlobalTheory.LKCount

theorem _root_.GlobalTheory.T.finsum_doubleCoset_fold_intermediate_subgroup : ∀ {G : Type} [Group G] (Γ' T K : Subgroup G) (F : G → ℂ), Γ' ≤ T → (∀ t ∈ T, ∀ x, ∀ k ∈ K, F (t * x * k) = F x) → (∀ x : G, ((Γ' ⊓ K.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G).Finite) → {q : DoubleCoset.Quotient (Γ' : Set G) (K : Set G) | F (Quotient.out q) ≠ 0}.Finite → ∑ᶠ q : DoubleCoset.Quotient (Γ' : Set G) (K : Set G), ((Nat.card (Γ' ⊓ K.map (MulAut.conj (Quotient.out q)).toMonoidHom : Subgroup G) : ℕ) : ℂ)⁻¹ * F (Quotient.out q) = ∑ᶠ y : DoubleCoset.Quotient (T : Set G) (K : Set G), ((massC Γ' T (T ⊓ K.map (MulAut.conj (Quotient.out y)).toMonoidHom) : ℚ) : ℂ) * F (Quotient.out y) := by
  first | exact @GlobalTheory.finsum_fold_intermediate | exact GlobalTheory.finsum_fold_intermediate | (intros; apply GlobalTheory.finsum_fold_intermediate <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedCentralizerMassNeZeroOfMemSupport

section

@[expose] public section

open GlobalTheory.LKCount

namespace GlobalTheory

theorem massC_ne_zero_of_support {G : Type} [Group G] (Γ' T K : Subgroup G) (F : G → ℂ) (hΓT : Γ' ≤ T)
    (hF : ∀ t ∈ T, ∀ x, ∀ k ∈ K, F (t * x * k) = F x)
    (hfin : ∀ x : G, ((Γ' ⊓ K.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G).Finite)
    (hsupp : {q : DoubleCoset.Quotient (Γ' : Set G) (K : Set G) | F (Quotient.out q) ≠ 0}.Finite)
    (y : G) (hy : F y ≠ 0) :
    massC Γ' T (T ⊓ K.map (MulAut.conj y).toMonoidHom) ≠ 0 := by
  have memconj : ∀ (L : Subgroup G) (a x : G), x ∈ L.map (MulAut.conj a).toMonoidHom ↔ a⁻¹ * x * a ∈ L := by
    intro L a x
    rw [Subgroup.mem_map_equiv]
    simp [MulAut.conj_symm_apply]
  have memconjT : ∀ (L : Subgroup T) (a x : T), x ∈ L.map (MulAut.conj a).toMonoidHom ↔ a⁻¹ * x * a ∈ L := by
    intro L a x
    rw [Subgroup.mem_map_equiv]
    simp [MulAut.conj_symm_apply]
  set C := T ⊓ K.map (MulAut.conj y).toMonoidHom with hC
  set A : Subgroup T := Γ'.subgroupOf T
  set B : Subgroup T := C.subgroupOf T

  let φ : DoubleCoset.Quotient (A : Set T) (B : Set T) → DoubleCoset.Quotient (Γ' : Set G) (K : Set G) :=
    fun q => DoubleCoset.mk Γ' K (((Quotient.out q : T) : G) * y)
  have hφS : ∀ q, φ q ∈ {q : DoubleCoset.Quotient (Γ' : Set G) (K : Set G) | F (Quotient.out q) ≠ 0} := by
    intro q
    show F (Quotient.out (DoubleCoset.mk Γ' K (((Quotient.out q : T) : G) * y))) ≠ 0
    obtain ⟨h, hh, k, hk, he⟩ := DoubleCoset.mk_out_eq_mul Γ' K (((Quotient.out q : T) : G) * y)
    rw [he, hF h (hΓT hh) _ k hk]
    have := hF ((Quotient.out q : T) : G) (Quotient.out q).2 y 1 K.one_mem
    rw [mul_one] at this
    rw [this]; exact hy
  have hφinj : Function.Injective φ := by
    intro q1 q2 h12
    rw [← DoubleCoset.out_eq' (H := A) (K := B) q1, ← DoubleCoset.out_eq' (H := A) (K := B) q2]
    obtain ⟨g, hg, k, hk, he⟩ := (@DoubleCoset.eq _ _ Γ' K _ _).1 h12
    set t1 : T := Quotient.out q1
    set t2 : T := Quotient.out q2
    have hgT : g ∈ T := hΓT hg
    have hs : y * k * y⁻¹ = ((t1 : G))⁻¹ * g⁻¹ * (t2 : G) := by
      have ht2 : (t2 : G) = g * ((t1 : G) * y) * k * y⁻¹ := by rw [← he]; group
      rw [ht2]; group
    have hsT : y * k * y⁻¹ ∈ T := by
      rw [hs]; exact T.mul_mem (T.mul_mem (T.inv_mem t1.2) (T.inv_mem hgT)) t2.2
    have hsC : y * k * y⁻¹ ∈ C := by
      refine ⟨hsT, (memconj K y _).2 ?_⟩
      simpa [mul_assoc] using hk
    rw [DoubleCoset.eq]
    refine ⟨⟨g, hgT⟩, ?_, ⟨y * k * y⁻¹, hsT⟩, ?_, ?_⟩
    · simpa [A, Subgroup.mem_subgroupOf] using hg
    · simpa [B, Subgroup.mem_subgroupOf] using hsC
    · apply Subtype.ext
      simp only [Subgroup.coe_mul]
      rw [hs]; group
  haveI : Finite {q : DoubleCoset.Quotient (Γ' : Set G) (K : Set G) | F (Quotient.out q) ≠ 0} := hsupp.to_subtype
  haveI hQ : Finite (DoubleCoset.Quotient (A : Set T) (B : Set T)) :=
    Finite.of_injective (fun q => (⟨φ q, hφS q⟩ : {q : DoubleCoset.Quotient (Γ' : Set G) (K : Set G) | F (Quotient.out q) ≠ 0}))
      (fun a b h => hφinj (congrArg Subtype.val h))

  have hpos : ∀ q : DoubleCoset.Quotient (A : Set T) (B : Set T),
      0 < ((Nat.card (A ⊓ B.map (MulAut.conj (Quotient.out q)).toMonoidHom : Subgroup T) : ℕ) : ℚ)⁻¹ := by
    intro q
    set t : T := Quotient.out q
    haveI : Finite ↥(Γ' ⊓ K.map (MulAut.conj ((t : G) * y)).toMonoidHom) := (hfin ((t : G) * y)).to_subtype
    have hmem : ∀ x : ↥(A ⊓ B.map (MulAut.conj t).toMonoidHom),
        ((x : T) : G) ∈ Γ' ⊓ K.map (MulAut.conj ((t : G) * y)).toMonoidHom := by
      intro x
      have hx := x.2
      rw [Subgroup.mem_inf] at hx
      obtain ⟨hxA, hxB⟩ := hx
      rw [memconjT] at hxB
      have hxC : ((t⁻¹ * (x : T) * t : T) : G) ∈ C := hxB
      refine ⟨hxA, (memconj K _ _).2 ?_⟩
      have := (memconj K y _).1 hxC.2
      simpa [mul_assoc] using this
    haveI : Finite ↥(A ⊓ B.map (MulAut.conj t).toMonoidHom) :=
      Finite.of_injective (fun x => (⟨((x : T) : G), hmem x⟩ : ↥(Γ' ⊓ K.map (MulAut.conj ((t : G) * y)).toMonoidHom)))
        (by intro a b h; apply Subtype.ext; apply Subtype.ext; have h' := congrArg Subtype.val h; exact h')
    exact inv_pos.mpr (Nat.cast_pos.mpr Nat.card_pos)
  haveI := Fintype.ofFinite (DoubleCoset.Quotient (A : Set T) (B : Set T))
  unfold massC
  rw [finsum_eq_sum_of_fintype]
  exact ne_of_gt (Finset.sum_pos (fun q _ => hpos q) Finset.univ_nonempty)

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedCentralizerMassNeZeroOfMemSupportStatement

section

@[expose] public section

open GlobalTheory.LKCount

theorem _root_.GlobalTheory.T.twistedCentralizerMass_ne_zero_of_mem_support : ∀ {G : Type} [Group G] (Γ' T K : Subgroup G) (F : G → ℂ), Γ' ≤ T → (∀ t ∈ T, ∀ x, ∀ k ∈ K, F (t * x * k) = F x) → (∀ x : G, ((Γ' ⊓ K.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G).Finite) → {q : DoubleCoset.Quotient (Γ' : Set G) (K : Set G) | F (Quotient.out q) ≠ 0}.Finite → ∀ y : G, F y ≠ 0 → massC Γ' T (T ⊓ K.map (MulAut.conj y).toMonoidHom) ≠ 0 := by
  first | exact @GlobalTheory.massC_ne_zero_of_support | exact GlobalTheory.massC_ne_zero_of_support | (intros; apply GlobalTheory.massC_ne_zero_of_support <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexNeZeroOpenCompact

section

@[expose] public section

open GlobalTheory.LKCount

noncomputable section
open scoped Classical

namespace GlobalTheory.LKCountPoint

section Gen
variable {G : Type} [Group G]

theorem mem_map_conj {K : Subgroup G} {a z : G} :
    z ∈ K.map (MulAut.conj a).toMonoidHom ↔ a⁻¹ * z * a ∈ K := by
  rw [Subgroup.mem_map_equiv]
  simp [MulAut.conj_symm_apply]

theorem map_conj_map_conj (K : Subgroup G) (a b : G) :
    (K.map (MulAut.conj a).toMonoidHom).map (MulAut.conj b).toMonoidHom =
      K.map (MulAut.conj (b * a)).toMonoidHom := by
  ext z
  simp only [mem_map_conj, mul_inv_rev, mul_assoc]

theorem map_conj_inf_of_mem {T : Subgroup G} {t : G} (ht : t ∈ T) (K : Subgroup G) :
    (T ⊓ K).map (MulAut.conj t).toMonoidHom = T ⊓ K.map (MulAut.conj t).toMonoidHom := by
  ext z
  simp only [mem_map_conj, Subgroup.mem_inf]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    have := T.mul_mem (T.mul_mem ht h1) (T.inv_mem ht)
    simpa [mul_assoc] using this
  · rintro ⟨h1, h2⟩
    exact ⟨T.mul_mem (T.mul_mem (T.inv_mem ht) h1) ht, h2⟩

theorem relIndex_inf_inf_ne_zero (H : Subgroup G) {U K : Subgroup G} (h : U.relIndex K ≠ 0) :
    (H ⊓ U).relIndex (H ⊓ K) ≠ 0 := by
  have := Subgroup.relIndex_inter_ne_zero h H
  rwa [inf_comm U H, inf_comm K H] at this

end Gen

section Prod
variable {G₁ G₂ : Type} [Group G₁] [Group G₂]

theorem prod_map_conj (A : Subgroup G₁) (B : Subgroup G₂) (x : G₁ × G₂) :
    (A.prod B).map (MulAut.conj x).toMonoidHom =
      (A.map (MulAut.conj x.1).toMonoidHom).prod (B.map (MulAut.conj x.2).toMonoidHom) := by
  ext z
  simp only [mem_map_conj, Subgroup.mem_prod, Prod.fst_mul, Prod.snd_mul, Prod.fst_inv, Prod.snd_inv]

theorem twCent_prod (θ₁ : G₁ →* G₁) (θ₂ : G₂ →* G₂) (a : G₁) (b : G₂) :
    GlobalTheory.BCT.twCent (θ₁.prodMap θ₂) (a, b) = (GlobalTheory.BCT.twCent θ₁ a).prod (GlobalTheory.BCT.twCent θ₂ b) := by
  ext z
  rw [Subgroup.mem_prod]
  show z * (a, b) = (a, b) * (θ₁.prodMap θ₂) z ↔ z.1 * a = a * θ₁ z.1 ∧ z.2 * b = b * θ₂ z.2
  rw [Prod.ext_iff]
  exact Iff.rfl

theorem relIndex_prod (A C : Subgroup G₁) (B D : Subgroup G₂) :
    (A.prod B).relIndex (C.prod D) = A.relIndex C * B.relIndex D := by
  have e : (A.prod B).subgroupOf (C.prod D) =
      ((A.subgroupOf C).prod (B.subgroupOf D)).comap (Subgroup.prodEquiv C D).toMonoidHom := by
    ext z
    exact Iff.rfl
  rw [Subgroup.relIndex, e, Subgroup.index_comap_of_surjective _ (Subgroup.prodEquiv C D).surjective,
    Subgroup.index_prod]
  rfl

theorem vol_prod (C₁ H₁ : Subgroup G₁) (C₂ H₂ : Subgroup G₂) :
    vol (C₁.prod C₂) (H₁.prod H₂) = vol C₁ H₁ * vol C₂ H₂ := by
  unfold vol
  rw [relIndex_prod, relIndex_prod]
  push_cast
  rw [div_mul_div_comm]

theorem stab_eq {Γ : Type} [Group Γ] (ι₁ : Γ →* G₁) (ι₂ : Γ →* G₂) (K₁ : Subgroup G₁) (K₂ : Subgroup G₂)
    (x : G₁ × G₂) :
    stab ι₁ ι₂ K₁ K₂ x = ((K₁.prod K₂).map (MulAut.conj x).toMonoidHom).comap (ι₁.prod ι₂) := by
  rw [prod_map_conj]
  ext g
  exact Iff.rfl

theorem card_stab {Γ : Type} [Group Γ] (ι₁ : Γ →* G₁) (ι₂ : Γ →* G₂) (K₁ : Subgroup G₁) (K₂ : Subgroup G₂)
    (hι : Function.Injective (ι₁.prod ι₂)) (x : G₁ × G₂) :
    Nat.card (stab ι₁ ι₂ K₁ K₂ x) =
      Nat.card ((ι₁.prod ι₂).range ⊓ (K₁.prod K₂).map (MulAut.conj x).toMonoidHom : Subgroup (G₁ × G₂)) := by
  rw [stab_eq, ← Subgroup.map_comap_eq]
  exact Nat.card_congr (Subgroup.equivMapOfInjective _ _ hι).toEquiv

theorem finite_inter {Γ : Type} [Group Γ] (ι₁ : Γ →* G₁) (ι₂ : Γ →* G₂) (K₁ : Subgroup G₁) (K₂ : Subgroup G₂)
    (x : G₁ × G₂) (h : Finite (stab ι₁ ι₂ K₁ K₂ x)) :
    (((ι₁.prod ι₂).range ⊓ (K₁.prod K₂).map (MulAut.conj x).toMonoidHom : Subgroup (G₁ × G₂)) :
      Set (G₁ × G₂)).Finite := by
  rw [← Subgroup.map_comap_eq, ← stab_eq, Subgroup.coe_map]
  exact Set.Finite.image _ (Set.toFinite _)

end Prod

section Core
variable {G : Type} [Group G]

theorem map_conj_one (A : Subgroup G) : A.map (MulAut.conj (1 : G)).toMonoidHom = A := by
  ext z
  simp [mem_map_conj]

theorem vol_self (A : Subgroup G) : vol A A = 1 := by
  simp [vol, Subgroup.relIndex_self]

theorem fold_sum (Γ' T K : Subgroup G) (F : G → ℂ) (hΓT : Γ' ≤ T)
    (hF : ∀ t ∈ T, ∀ x, ∀ k ∈ K, F (t * x * k) = F x)
    (hfin : ∀ x : G, ((Γ' ⊓ K.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G).Finite)
    (hsupp : {q : DoubleCoset.Quotient (Γ' : Set G) (K : Set G) | F (Quotient.out q) ≠ 0}.Finite) :
    ∑ᶠ q : DoubleCoset.Quotient (Γ' : Set G) (K : Set G),
        ((Nat.card (Γ' ⊓ K.map (MulAut.conj (Quotient.out q)).toMonoidHom : Subgroup G) : ℕ) : ℂ)⁻¹ *
          F (Quotient.out q) =
      ∑ᶠ y : DoubleCoset.Quotient (T : Set G) (K : Set G),
        ((massC Γ' T (T ⊓ K.map (MulAut.conj (Quotient.out y)).toMonoidHom) : ℚ) : ℂ) * F (Quotient.out y) :=
  GlobalTheory.T.finsum_doubleCoset_fold_intermediate_subgroup Γ' T K F hΓT hF hfin hsupp

theorem massC_ne_zero_of_ne (Γ' T K : Subgroup G) (F : G → ℂ) (hΓT : Γ' ≤ T)
    (hF : ∀ t ∈ T, ∀ x, ∀ k ∈ K, F (t * x * k) = F x)
    (hfin : ∀ x : G, ((Γ' ⊓ K.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G).Finite)
    (hsupp : {q : DoubleCoset.Quotient (Γ' : Set G) (K : Set G) | F (Quotient.out q) ≠ 0}.Finite)
    (y : G) (hy : F y ≠ 0) :
    massC Γ' T (T ⊓ K.map (MulAut.conj y).toMonoidHom) ≠ 0 :=
  GlobalTheory.T.twistedCentralizerMass_ne_zero_of_mem_support Γ' T K F hΓT hF hfin hsupp y hy

variable [TopologicalSpace G] [IsTopologicalGroup G]

end Core

end GlobalTheory.LKCountPoint
end
end
end
