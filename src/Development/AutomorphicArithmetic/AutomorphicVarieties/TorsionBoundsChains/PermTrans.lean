module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.FaceDSingle
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.RepresentationTheory.Coinduced
public import Mathlib.RepresentationTheory.Homological.GroupHomology.Basic
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
public import Mathlib.RepresentationTheory.Homological.GroupHomology.Functoriality
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.FaceDSingle
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.Shapiro
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.RingTheory.RegularLocalRing.Defs
import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.Shapiro
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.Transport

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.MapNsmul

section

@[expose] public section

open CategoryTheory UpperTheory.V.KH

theorem UpperTheory.V.KH.mapNsmul :
    ∀ (G : Type) [Group G] (A B : Rep ℤ G) (f : A ⟶ B) (g : B ⟶ A) (n j : ℕ),
      (∀ a, g.hom (f.hom a) = n • a) → Subsingleton (groupHomology B j) →
      ∀ z : groupHomology A j, n • z = 0 := by
  intro G _ A B f g n j h hB z
  have hc : groupHomology.chainsMap (MonoidHom.id G) (f ≫ g) =
      n • 𝟙 (groupHomology.inhomogeneousChains A) := by
    ext i : 1
    apply ModuleCat.hom_ext
    refine DFunLike.ext _ _ fun c => ?_
    refine Finsupp.ext fun y => ?_
    simp [h]
  have hm : groupHomology.map (MonoidHom.id G) (f ≫ g) j = n • 𝟙 (groupHomology A j) := by
    simp only [groupHomology.map, hc]
    change (HomologicalComplex.homologyFunctor _ _ j).map _ = _
    rw [Functor.map_nsmul, CategoryTheory.Functor.map_id]
    rfl
  have e1 : (groupHomology.map (MonoidHom.id G) (f ≫ g) j).hom z = n • z := by
    rw [hm]
    rfl
  rw [← e1, groupHomology.map_id_comp]
  have e2 : (groupHomology.map (MonoidHom.id G) f j).hom z = 0 :=
    Subsingleton.elim (α := groupHomology B j) _ _
  simp [e2]
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.ImportsAlt

section

@[expose] public section

open CategoryTheory UpperTheory.V.KH

theorem UpperTheory.V.KH.kill :
    ∀ (S : Type) [Group S] [Finite S] (j : ℕ) (z : HZ S (j + 1)), Nat.card S • z = 0 := by
  intro S _ _ j z
  classical
  haveI : Fintype S := Fintype.ofFinite S
  let v : S →₀ ℤ := ∑ s : S, Finsupp.single s 1
  have hv : ∀ g : S, perm S S g v = v := by
    intro g

    simp only [v, map_sum, perm_single]
    exact Fintype.sum_equiv (MulAction.toPerm g) _ _ (fun _ => rfl)
  let fi : (Rep.trivial ℤ S ℤ).ρ.IntertwiningMap (permRep S S).ρ :=
    ⟨LinearMap.toSpanSingleton ℤ _ v, fun g => by
      apply LinearMap.ext_ring
      simp [Rep.trivial_ρ, permRep, hv]⟩
  let gi : (permRep S S).ρ.IntertwiningMap (Rep.trivial ℤ S ℤ).ρ :=
    ⟨aug S, fun g => by
      apply Finsupp.lhom_ext
      intro x c
      simp [Rep.trivial_ρ, permRep, perm_single, aug_single]⟩
  have hcomp : ∀ a : Rep.trivial ℤ S ℤ,
      (Rep.Hom.hom (Rep.ofHom gi)) ((Rep.Hom.hom (Rep.ofHom fi)) a) = Nat.card S • a := by
    intro a
    change aug S (a • v) = Nat.card S • a

    simp only [v, map_smul, map_sum, aug_single, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    nsmul_eq_mul, Nat.card_eq_fintype_card, mul_one]
    ring
  have hsub : Subsingleton (groupHomology (permRep S S) (j + 1)) := by
    obtain ⟨e⟩ := shapiro S S (1 : S) (j + 1)
    haveI : Subsingleton (MulAction.stabilizer S (1 : S)) := by
      constructor
      rintro ⟨a, ha⟩ ⟨b, hb⟩
      have ha' : a * 1 = 1 := ha
      have hb' : b * 1 = 1 := hb
      simp only [mul_one] at ha' hb'
      subst ha' hb'
      rfl
    have hz := ModuleCat.isZero_iff_subsingleton.mp
      (isZero_groupHomology_succ_of_subsingleton
        (Rep.trivial ℤ (MulAction.stabilizer S (1 : S)) ℤ) j)
    exact e.injective.subsingleton
  exact mapNsmul S (Rep.trivial ℤ S ℤ) (permRep S S) (Rep.ofHom fi) (Rep.ofHom gi) (Nat.card S) (j + 1) hcomp hsub z
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.Subquot

section

@[expose] public section

open CategoryTheory UpperTheory.V.KH

theorem UpperTheory.V.KH.subquot :
    ∀ (ι Z H : Type) [Finite ι] [AddCommGroup Z] [AddCommGroup H] (i : Z →+ (ι →₀ ℤ)) (q : Z →+ H)
      (n : ℕ), 1 ≤ n → Function.Injective i → Function.Surjective q → (∀ h : H, n • h = 0) →
      CardLe H (n ^ Nat.card ι) := by
  intro ι Z H _ _ _ i q n hn hi hq hk
  classical
  have := Fintype.ofFinite ι
  let i' : Z →ₗ[ℤ] (ι →₀ ℤ) := i.toIntLinearMap
  have hi' : Function.Injective i' := hi
  have : Module.Finite ℤ Z := Module.Finite.of_injective i' hi'
  have : Module.Free ℤ Z :=
    Module.Free.of_equiv (LinearEquiv.ofInjective i' hi').symm
  have hr : Module.finrank ℤ Z ≤ Nat.card ι := by
    have h := LinearMap.finrank_le_finrank_of_injective hi'
    rwa [Module.finrank_finsupp_self, ← Nat.card_eq_fintype_card] at h
  let b := Module.finBasis ℤ Z
  let f : (Fin (Module.finrank ℤ Z) → Fin n) → H := fun c => ∑ k, (((c k : ℕ) : ℤ)) • q (b k)
  have hn0 : (0 : ℤ) < n := by exact_mod_cast hn
  have hf : Function.Surjective f := by
    intro h
    obtain ⟨z, rfl⟩ := hq h
    refine ⟨fun k => ⟨(b.repr z k % n).toNat, ?_⟩, ?_⟩
    · have h1 := Int.emod_nonneg (b.repr z k) hn0.ne'
      have h2 := Int.emod_lt_of_pos (b.repr z k) hn0
      omega
    · set_option synthInstance.maxHeartbeats 100000 in
        conv_rhs => rw [← b.sum_repr z, map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      have h1 := Int.emod_nonneg (b.repr z k) hn0.ne'
      rw [map_zsmul]
      simp only [Int.toNat_of_nonneg h1]
      have h3 : (n : ℤ) • q (b k) = 0 := by rw [natCast_zsmul]; exact hk _
      conv_rhs => rw [← Int.emod_add_ediv_mul (b.repr z k) n, add_smul, mul_smul, h3, smul_zero,
        add_zero]
  refine ⟨Finite.of_surjective f hf, (Nat.card_le_card_of_surjective f hf).trans ?_⟩
  rw [Nat.card_fun, Nat.card_fin, Nat.card_fin]
  exact Nat.pow_le_pow_right hn hr
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.FinGroup

section

@[expose] public section

open CategoryTheory UpperTheory.V.KH

theorem UpperTheory.V.KH.finGroup :
    ∀ (S : Type) [Group S] [Finite S] (j : ℕ),
      CardLe (HZ S (j + 1)) (Nat.card S ^ (Nat.card S ^ (j + 1))) := by
  intro S _ _ j
  have hi : Function.Injective (groupHomology.iCycles (Rep.trivial ℤ S ℤ) (j + 1)).hom :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  have hq : Function.Surjective (groupHomology.π (Rep.trivial ℤ S ℤ) (j + 1)).hom :=
    fun x => groupHomology_induction_on x fun y => ⟨y, rfl⟩
  have h := subquot (Fin (j + 1) → S) (groupHomology.cycles (Rep.trivial ℤ S ℤ) (j + 1))
    (HZ S (j + 1)) (groupHomology.iCycles (Rep.trivial ℤ S ℤ) (j + 1)).hom.toAddMonoidHom
    (groupHomology.π (Rep.trivial ℤ S ℤ) (j + 1)).hom.toAddMonoidHom (Nat.card S)
    Nat.card_pos hi hq (kill S j)
  rwa [Nat.card_fun, Nat.card_fin] at h
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.PermTrans

section

@[expose] public section

open CategoryTheory UpperTheory.V.KH

theorem UpperTheory.V.KH.permTrans :
    ∀ (G X : Type) [Group G] [MulAction G X] [MulAction.IsPretransitive G X] [Nonempty X] (s j : ℕ),
      StabLe G X s → CardLe (groupHomology (permRep G X) (j + 1)) (s ^ (s ^ (j + 1))) := by
  intro G X _ _ _ _ s j hs
  obtain ⟨x⟩ := ‹Nonempty X›
  obtain ⟨hfin, hcard⟩ := hs x
  haveI := hfin
  obtain ⟨e⟩ := shapiro G X x (j + 1)
  have h1 := finGroup (MulAction.stabilizer G x) j
  have hpos : 0 < Nat.card (MulAction.stabilizer G x) := Nat.card_pos
  have hle : Nat.card (MulAction.stabilizer G x) ^ Nat.card (MulAction.stabilizer G x) ^ (j + 1)
      ≤ s ^ s ^ (j + 1) := by
    have hs1 : 0 < s := lt_of_lt_of_le hpos hcard
    calc Nat.card (MulAction.stabilizer G x) ^ Nat.card (MulAction.stabilizer G x) ^ (j + 1)
        ≤ s ^ Nat.card (MulAction.stabilizer G x) ^ (j + 1) := Nat.pow_le_pow_left hcard _
      _ ≤ s ^ s ^ (j + 1) := Nat.pow_le_pow_right hs1 (Nat.pow_le_pow_left hcard _)
  exact transport.2.1 _ _ e.symm.toEquiv _ (transport.2.2.2 _ _ _ hle h1)
end
end
