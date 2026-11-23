module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Presheaf
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.RingTheory.IsTensorProduct
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteTypeAwayOfAtPrime

section

@[expose] public section

namespace GlobalTheory.Desc

open scoped TensorProduct

theorem finiteType_away_of_pow_mul_mem {R C : Type} [CommRing R] [CommRing C] [Algebra R C]
    (s : Finset C) (x : C) (h : ∀ c : C, ∃ n : ℕ, x ^ n * c ∈ Algebra.adjoin R (s : Set C)) :
    Algebra.FiniteType R (Localization.Away x) := by
  classical
  let φ := IsScalarTower.toAlgHom R C (Localization.Away x)
  let u : Localization.Away x := IsLocalization.Away.invSelf x
  have hu : φ x * u = 1 := IsLocalization.Away.mul_invSelf x
  refine ⟨⟨insert u (s.image φ), ?_⟩⟩
  rw [eq_top_iff]
  rintro y -
  have hU : u ∈ Algebra.adjoin R ((insert u (s.image φ) : Finset _) : Set (Localization.Away x)) :=
    Algebra.subset_adjoin (by simp)
  have hB : ∀ b ∈ Algebra.adjoin R (s : Set C),
      φ b ∈ Algebra.adjoin R ((insert u (s.image φ) : Finset _) : Set (Localization.Away x)) := by
    intro b hb
    have : φ b ∈ (Algebra.adjoin R (s : Set C)).map φ := ⟨b, hb, rfl⟩
    rw [AlgHom.map_adjoin] at this
    refine Algebra.adjoin_mono ?_ this
    intro z hz
    simp only [Finset.coe_insert, Finset.coe_image]
    exact Or.inr hz
  obtain ⟨m, c, hc⟩ := IsLocalization.Away.surj x y
  obtain ⟨n, hn⟩ := h c
  have hc' : y * φ x ^ m = φ c := hc
  have : y = φ (x ^ n * c) * u ^ (n + m) := by
    rw [map_mul, map_pow, ← hc']
    calc y = y * (φ x * u) ^ (n + m) := by rw [hu]; simp
      _ = _ := by ring
  rw [this]
  exact mul_mem (hB _ hn) (pow_mem hU _)

theorem exists_pow_mul_mem_of_finiteType_away {R C : Type} [CommRing R] [CommRing C] [Algebra R C]
    (f : R) (h : Algebra.FiniteType R (Localization.Away (algebraMap R C f))) :
    ∃ s : Finset C, ∀ c : C, ∃ n : ℕ, algebraMap R C f ^ n * c ∈ Algebra.adjoin R (s : Set C) := by
  classical
  set x := algebraMap R C f with hx
  let φ := algebraMap C (Localization.Away x)
  obtain ⟨t, ht⟩ := h.out
  choose m a ha using fun y : Localization.Away x => IsLocalization.Away.surj x y
  refine ⟨t.image a, fun c => ?_⟩
  set B := Algebra.adjoin R ((t.image a : Finset C) : Set C) with hB
  have hxB : x ∈ B := B.algebraMap_mem f
  have key : ∀ y ∈ Algebra.adjoin R (t : Set (Localization.Away x)),
      ∃ n : ℕ, ∃ b ∈ B, y * φ x ^ n = φ b := by
    intro y hy
    induction hy using Algebra.adjoin_induction with
    | mem y hy =>
      exact ⟨m y, a y, Algebra.subset_adjoin (by simpa using ⟨y, hy, rfl⟩), ha y⟩
    | algebraMap r =>
      exact ⟨0, algebraMap R C r, B.algebraMap_mem r, by
        rw [pow_zero, mul_one]; exact IsScalarTower.algebraMap_apply R C _ r⟩
    | add y z _ _ hy hz =>
      obtain ⟨n, b, hb, e⟩ := hy
      obtain ⟨k, d, hd, e'⟩ := hz
      refine ⟨n + k, b * x ^ k + d * x ^ n,
        add_mem (mul_mem hb (pow_mem hxB _)) (mul_mem hd (pow_mem hxB _)), ?_⟩
      rw [map_add (f := _), map_mul, map_mul, map_pow, map_pow, ← e, ← e']
      ring
    | mul y z _ _ hy hz =>
      obtain ⟨n, b, hb, e⟩ := hy
      obtain ⟨k, d, hd, e'⟩ := hz
      refine ⟨n + k, b * d, mul_mem hb hd, ?_⟩
      rw [map_mul, ← e, ← e']
      ring
  obtain ⟨n, b, hb, e⟩ := key (φ c) (by rw [ht]; trivial)
  rw [← map_pow, ← map_mul] at e
  obtain ⟨k, hk⟩ := IsLocalization.Away.exists_of_eq x e
  refine ⟨k + n, ?_⟩
  have : x ^ (k + n) * c = x ^ k * b := by rw [← hk]; ring
  rw [this]
  exact mul_mem (pow_mem hxB _) hb

theorem exists_smul_mem_of_finiteType_tensor {R C : Type} [CommRing R] [CommRing C] [Algebra R C]
    (M : Submonoid R) (h : Algebra.FiniteType (Localization M) (Localization M ⊗[R] C)) :
    ∃ s : Finset C, ∀ c : C, ∃ r ∈ M, algebraMap R C r * c ∈ Algebra.adjoin R (s : Set C) := by
  classical
  let φ : C →ₐ[R] Localization M ⊗[R] C := Algebra.TensorProduct.includeRight
  have hloc : IsLocalizedModule M (TensorProduct.mk R (Localization M) C 1) :=
    (isLocalizedModule_iff_isBaseChange M (Localization M) _).2
      (TensorProduct.isBaseChange R C (Localization M))
  have hφ : ∀ c, TensorProduct.mk R (Localization M) C 1 c = φ c := fun _ => rfl
  obtain ⟨t, ht⟩ := h.out
  choose p hp using fun y => IsLocalizedModule.surj M (TensorProduct.mk R (Localization M) C 1) y
  refine ⟨t.image fun y => (p y).1, fun c => ?_⟩
  set B := Algebra.adjoin R ((t.image (fun y => (p y).1) : Finset C) : Set C) with hB
  have key : ∀ y ∈ Algebra.adjoin (Localization M) (t : Set (Localization M ⊗[R] C)),
      ∃ r ∈ M, ∃ b ∈ B, r • y = φ b := by
    intro y hy
    induction hy using Algebra.adjoin_induction with
    | mem y hy =>
      exact ⟨(p y).2, (p y).2.2, (p y).1, Algebra.subset_adjoin (by simpa using ⟨y, hy, rfl⟩), hp y⟩
    | algebraMap q =>
      obtain ⟨⟨a, r⟩, e⟩ := IsLocalization.surj M q
      refine ⟨r, r.2, algebraMap R C a, B.algebraMap_mem a, ?_⟩
      rw [φ.commutes, Algebra.smul_def, IsScalarTower.algebraMap_apply R (Localization M),
        IsScalarTower.algebraMap_apply R (Localization M) _ a, ← map_mul, mul_comm]
      exact congrArg _ e
    | add y z _ _ hy hz =>
      obtain ⟨n, hn, b, hb, e⟩ := hy
      obtain ⟨k, hk, d, hd, e'⟩ := hz
      refine ⟨n * k, mul_mem hn hk, k • b + n • d,
        add_mem (B.smul_mem hb _) (B.smul_mem hd _), ?_⟩
      rw [map_add (f := _), map_smul, map_smul, ← e, ← e', smul_add, smul_smul, smul_smul, mul_comm k n]
    | mul y z _ _ hy hz =>
      obtain ⟨n, hn, b, hb, e⟩ := hy
      obtain ⟨k, hk, d, hd, e'⟩ := hz
      refine ⟨n * k, mul_mem hn hk, b * d, mul_mem hb hd, ?_⟩
      rw [map_mul, ← e, ← e', smul_mul_smul_comm]
  obtain ⟨r, hr, b, hb, e⟩ := key (φ c) (by rw [ht]; trivial)
  rw [← map_smul, ← hφ, ← hφ] at e
  obtain ⟨k, hk⟩ := IsLocalizedModule.exists_of_eq (S := M) e
  refine ⟨k * r, mul_mem k.2 hr, ?_⟩
  have : algebraMap R C (k * r) * c = (k : R) • b := by
    rw [← Algebra.smul_def, mul_smul]; exact hk
  rw [this]
  exact B.smul_mem hb _

theorem exists_mul_mem_of_mul_mem {R C : Type} [CommRing R] [CommRing C] [IsDomain C] [Algebra R C]
    (B : Subalgebra R C) [IsNoetherianRing B] (x : C) (hx : x ≠ 0) (M : Submonoid R)
    (h : ∀ c : C, ∃ r ∈ M, algebraMap R C r * c ∈ B) :
    ∃ g ∈ M, ∀ c : C, x * c ∈ B → algebraMap R C g * c ∈ B := by
  classical
  let J : Ideal B := (Ideal.span {x}).comap B.val
  obtain ⟨t, ht⟩ : J.FG := IsNoetherian.noetherian J
  choose r hrM hr using h
  have hJ : ∀ b : B, ∃ c : C, b ∈ J → (b : C) = x * c := by
    intro b
    by_cases hb : b ∈ J
    · obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.mem_comap.1 hb)
      exact ⟨c, fun _ => by rw [mul_comm]; exact hc.symm⟩
    · exact ⟨0, fun h => absurd h hb⟩
  choose q hq using hJ
  refine ⟨∏ b ∈ t, r (q b), prod_mem fun b _ => hrM _, ?_⟩
  set g := ∏ b ∈ t, r (q b) with hg
  have key : ∀ b ∈ Ideal.span (t : Set B), ∃ c : C, (b : C) = x * c ∧ algebraMap R C g * c ∈ B := by
    intro b hb
    induction hb using Submodule.span_induction with
    | mem b hb =>
      refine ⟨q b, hq b (ht ▸ Ideal.subset_span hb), ?_⟩
      rw [hg, ← Finset.prod_erase_mul t _ hb, map_mul, mul_assoc]
      exact mul_mem (B.algebraMap_mem _) (hr _)
    | zero => exact ⟨0, by simp, by simp⟩
    | add y z _ _ hy hz =>
      obtain ⟨c, e, hc⟩ := hy
      obtain ⟨d, e', hd⟩ := hz
      exact ⟨c + d, by rw [mul_add, ← e, ← e']; rfl, by rw [mul_add]; exact add_mem hc hd⟩
    | smul a y _ hy =>
      obtain ⟨c, e, hc⟩ := hy
      refine ⟨a * c, by rw [mul_left_comm, ← e]; rfl, ?_⟩
      rw [mul_left_comm]
      exact mul_mem a.2 hc
  intro c hc
  obtain ⟨d, e, hd⟩ := key ⟨x * c, hc⟩ (by
    rw [ht]
    exact Ideal.mem_comap.2 (Ideal.mem_span_singleton'.2 ⟨c, mul_comm _ _⟩))
  rw [mul_left_cancel₀ hx e]
  exact hd

theorem exists_finiteType_away_of_atPrime (R C : Type) [CommRing R] [IsNoetherianRing R]
    [CommRing C] [IsDomain C] [Algebra R C] (f : R) (𝔭 : Ideal R) [𝔭.IsPrime]
    (hf : algebraMap R C f ≠ 0)
    (h₁ : Algebra.FiniteType R (Localization.Away (algebraMap R C f)))
    (h₂ : Algebra.FiniteType (Localization.AtPrime 𝔭)
      (TensorProduct R (Localization.AtPrime 𝔭) C)) :
    ∃ g : R, g ∉ 𝔭 ∧ Algebra.FiniteType R (Localization.Away (algebraMap R C g)) := by
  classical
  obtain ⟨s₁, hs₁⟩ := exists_pow_mul_mem_of_finiteType_away f h₁
  obtain ⟨s₂, hs₂⟩ := exists_smul_mem_of_finiteType_tensor 𝔭.primeCompl h₂
  let B := Algebra.adjoin R ((s₁ ∪ s₂ : Finset C) : Set C)
  have hB₁ : Algebra.adjoin R (s₁ : Set C) ≤ B := Algebra.adjoin_mono (by simp)
  have hB₂ : Algebra.adjoin R (s₂ : Set C) ≤ B := Algebra.adjoin_mono (by simp)
  have : IsNoetherianRing B := isNoetherianRing_of_fg ⟨s₁ ∪ s₂, rfl⟩
  obtain ⟨g, hg, hgB⟩ := exists_mul_mem_of_mul_mem B _ hf 𝔭.primeCompl fun c =>
    (hs₂ c).imp fun r hr => ⟨hr.1, hB₂ hr.2⟩
  refine ⟨g, hg, finiteType_away_of_pow_mul_mem (s₁ ∪ s₂) _ fun c => ?_⟩
  have key : ∀ (n : ℕ) (c : C), algebraMap R C f ^ n * c ∈ B → algebraMap R C g ^ n * c ∈ B := by
    intro n
    induction n with
    | zero => intro c hc; simpa using hc
    | succ n ih =>
      intro c hc
      rw [pow_succ, mul_assoc] at hc
      have h := ih _ hc
      rw [mul_left_comm] at h
      rw [pow_succ', mul_assoc]
      exact hgB _ h
  obtain ⟨n, hn⟩ := hs₁ c
  exact ⟨n, key n c (hB₁ hn)⟩

end GlobalTheory.Desc
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteTypeAwayOfAtPrimeStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

theorem _root_.GlobalTheory.T.exists_finiteType_away_of_finiteType_atPrime : ∀ (R C : Type) [CommRing R] [IsNoetherianRing R] [CommRing C] [IsDomain C] [Algebra R C] (f : R) (𝔭 : Ideal R) [𝔭.IsPrime], algebraMap R C f ≠ 0 → Algebra.FiniteType R (Localization.Away (algebraMap R C f)) → Algebra.FiniteType (Localization.AtPrime 𝔭) (TensorProduct R (Localization.AtPrime 𝔭) C) → ∃ g : R, g ∉ 𝔭 ∧ Algebra.FiniteType R (Localization.Away (algebraMap R C g)) := by
  first | exact @GlobalTheory.Desc.exists_finiteType_away_of_atPrime | exact GlobalTheory.Desc.exists_finiteType_away_of_atPrime | (intros; apply GlobalTheory.Desc.exists_finiteType_away_of_atPrime <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallyOfFiniteTypeNearGenerisationOfPoint

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.USpread

theorem lft_of_pullback {X V P S T Y : Scheme.{0}} (j : X ⟶ V) (q : V ⟶ P) (s : S ⟶ P) (t : T ⟶ S)
    (u : Y ⟶ X) (b : Y ⟶ T) [LocallyOfFiniteType j] [LocallyOfFiniteType (pullback.snd q s)]
    (h : IsPullback u b (j ≫ q) (t ≫ s)) : LocallyOfFiniteType b := by
  have h1 := (IsPullback.of_hasPullback j (pullback.fst q s)).paste_vert (IsPullback.of_hasPullback q s)
  have h2 := (IsPullback.of_hasPullback (pullback.snd j (pullback.fst q s) ≫ pullback.snd q s) t).paste_horiz h1
  rw [← h.isoIsPullback_hom_snd _ _ h2]
  infer_instance

theorem exists_to_stalk (R : Type) [CommRing R] (x : Sp R) [x.asIdeal.IsPrime] :
    ∃ t : Sp (Localization.AtPrime x.asIdeal) ⟶ Spec ((Sp R).presheaf.stalk x),
      t ≫ (Sp R).fromSpecStalk x =
        Spec.map (CommRingCat.ofHom (algebraMap R (Localization.AtPrime x.asIdeal))) := by
  let y : PrimeSpectrum R := x
  haveI := StructureSheaf.IsLocalization.to_stalk R y
  let e := IsLocalization.algEquiv (R := R) y.asIdeal.primeCompl
    ((Spec.structureSheaf R).presheaf.stalk y) (Localization.AtPrime y.asIdeal)
  refine ⟨Spec.map (CommRingCat.ofHom e.toRingEquiv.toRingHom), ?_⟩
  have := Spec.fromSpecStalk_eq' (CommRingCat.of R) x
  erw [this, ← Spec.map_comp]
  congr 1
  ext r
  exact e.commutes r

theorem away_finiteType (R : Type) [CommRing R] (f : R) (P A : Scheme.{0})
    (p : P ⟶ Sp R) (ιA : A ⟶ P) (a : A ⟶ Sp (Localization.Away f))
    (h : IsPullback ιA a p (GlobalTheory.Desc.awayMap f)) [LocallyOfFiniteType a]
    (C : Type) [CommRing C] [Algebra R C] (j : Sp C ⟶ P) [IsOpenImmersion j]
    (hj : j ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R C))) :
    Algebra.FiniteType R (Localization.Away (algebraMap R C f)) := by
  let D := Localization.Away (algebraMap R C f)
  have hu : IsUnit (algebraMap R D f) := by
    rw [IsScalarTower.algebraMap_apply R C D]
    exact IsLocalization.Away.algebraMap_isUnit _
  let ψ : Localization.Away f →+* D := IsLocalization.Away.lift f hu
  have hψ : ψ.comp (algebraMap R (Localization.Away f)) = algebraMap R D :=
    IsLocalization.Away.lift_comp f hu
  let k : Sp D ⟶ Sp C := Spec.map (CommRingCat.ofHom (algebraMap C D))
  haveI : IsOpenImmersion k := IsOpenImmersion.of_isLocalization (algebraMap R C f)
  have hψ' : Spec.map (CommRingCat.ofHom ψ) ≫ GlobalTheory.Desc.awayMap f =
      Spec.map (CommRingCat.ofHom (algebraMap R D)) := by
    rw [← hψ, CommRingCat.ofHom_comp, Spec.map_comp]
  have w : (k ≫ j) ≫ p = Spec.map (CommRingCat.ofHom ψ) ≫ GlobalTheory.Desc.awayMap f := by
    rw [hψ', Category.assoc, hj, IsScalarTower.algebraMap_eq R C D, CommRingCat.ofHom_comp,
      Spec.map_comp]
  haveI : IsOpenImmersion (GlobalTheory.Desc.awayMap f) := IsOpenImmersion.of_isLocalization f
  haveI : IsOpenImmersion ιA := MorphismProperty.of_isPullback h.flip ‹_›
  let l := h.lift _ _ w
  have hl : l ≫ ιA = k ≫ j := h.lift_fst _ _ w
  haveI : IsOpenImmersion (l ≫ ιA) := by rw [hl]; infer_instance
  haveI : IsOpenImmersion l := IsOpenImmersion.of_comp l ιA
  have : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap R D))) := by
    rw [← hψ', ← h.lift_snd _ _ w]
    change LocallyOfFiniteType ((l ≫ a) ≫ _)
    infer_instance
  exact RingHom.finiteType_algebraMap.1
    ((HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 this)

theorem ne_zero (R : Type) [CommRing R] (f : R) (P A : Scheme.{0}) [IsIntegral P] [Nonempty A]
    (p : P ⟶ Sp R) (ιA : A ⟶ P) (a : A ⟶ Sp (Localization.Away f))
    (h : IsPullback ιA a p (GlobalTheory.Desc.awayMap f))
    (C : Type) [CommRing C] [Algebra R C] [Nonempty (Sp C)] (j : Sp C ⟶ P) [IsOpenImmersion j]
    (hj : j ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R C))) :
    algebraMap R C f ≠ 0 := by
  intro h0
  haveI : IsOpenImmersion (GlobalTheory.Desc.awayMap f) := IsOpenImmersion.of_isLocalization f
  haveI : IsOpenImmersion ιA := MorphismProperty.of_isPullback h.flip ‹_›
  obtain ⟨y, ⟨c, hc⟩, ⟨t, ht⟩⟩ := nonempty_preirreducible_inter
    j.isOpenEmbedding.isOpen_range ιA.isOpenEmbedding.isOpen_range
    (Set.range_nonempty _) (Set.range_nonempty _)
  have h1 : p y = PrimeSpectrum.comap (algebraMap R C) c := by
    rw [← hc, ← Scheme.Hom.comp_apply, hj]; rfl
  have h2 : p y = PrimeSpectrum.comap (algebraMap R (Localization.Away f)) (a t) := by
    rw [← ht, ← Scheme.Hom.comp_apply, h.w, Scheme.Hom.comp_apply]; rfl
  have h3 : f ∈ (PrimeSpectrum.comap (algebraMap R C) c).asIdeal := by
    change algebraMap R C f ∈ c.asIdeal
    rw [h0]; exact zero_mem _
  rw [← h1, h2] at h3
  exact (a t).isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h3
    (IsLocalization.Away.algebraMap_isUnit f))

theorem affine_case (R : Type) [CommRing R] [IsNoetherianRing R] (f : R) (P A : Scheme.{0})
    [IsIntegral P] [Nonempty A]
    (p : P ⟶ Sp R) (ιA : A ⟶ P) (a : A ⟶ Sp (Localization.Away f))
    (h : IsPullback ιA a p (GlobalTheory.Desc.awayMap f)) [LocallyOfFiniteType a]
    (x : Sp R) (V : P.Opens)
    [LocallyOfFiniteType (Limits.pullback.snd (V.ι ≫ p) ((Sp R).fromSpecStalk x))]
    (C : Type) [CommRing C] [IsDomain C] [Algebra R C] (j : Sp C ⟶ V) [IsOpenImmersion j]
    (hj : (j ≫ V.ι) ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R C)))
    (c : Sp C) (hc : (p ((j ≫ V.ι) c)).asIdeal ≤ x.asIdeal) :
    ∃ W : P.Opens, (j ≫ V.ι) c ∈ W ∧ W ≤ V ∧ LocallyOfFiniteType (W.ι ≫ p) := by
  haveI : Nonempty (Sp C) := ⟨c⟩
  haveI := x.isPrime
  have h1 := ne_zero R f P A p ιA a h C (j ≫ V.ι) hj
  have h2 := away_finiteType R f P A p ιA a h C (j ≫ V.ι) hj
  obtain ⟨t, ht⟩ := exists_to_stalk R x
  have hpb := (isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct R (Localization.AtPrime x.asIdeal) C)).flip
  rw [← hj, ← ht, Category.assoc] at hpb
  have h3 := (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1
    (lft_of_pullback _ _ _ _ _ _ hpb)
  have h4 : Algebra.FiniteType (Localization.AtPrime x.asIdeal)
      (TensorProduct R (Localization.AtPrime x.asIdeal) C) := RingHom.finiteType_algebraMap.1 h3
  obtain ⟨g, hg, hft⟩ := GlobalTheory.T.exists_finiteType_away_of_finiteType_atPrime R C f x.asIdeal h1 h2 h4
  let D := Localization.Away (algebraMap R C g)
  let k : Sp D ⟶ Sp C := Spec.map (CommRingCat.ofHom (algebraMap C D))
  haveI : IsOpenImmersion k := IsOpenImmersion.of_isLocalization (algebraMap R C g)
  have h5 : p ((j ≫ V.ι) c) = PrimeSpectrum.comap (algebraMap R C) c := by
    rw [← Scheme.Hom.comp_apply, hj]; rfl
  refine ⟨(k ≫ j ≫ V.ι).opensRange, ?_, ?_, ?_⟩
  · have : c ∈ Set.range (PrimeSpectrum.comap (algebraMap C D)) := by
      rw [PrimeSpectrum.localization_away_comap_range D (algebraMap R C g)]
      intro hgc
      apply hg
      apply hc
      rw [h5]
      exact hgc
    obtain ⟨d, hd⟩ := this
    exact ⟨d, by rw [Scheme.Hom.comp_apply, ← hd]; rfl⟩
  · rintro _ ⟨d, rfl⟩
    rw [← Category.assoc, Scheme.Hom.comp_apply]
    exact ((k ≫ j) d).2
  · have : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap R D))) :=
      (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).2
        (RingHom.finiteType_algebraMap.2 hft)
    have e : (k ≫ j ≫ V.ι) ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R D)) := by
      rw [Category.assoc, hj, IsScalarTower.algebraMap_eq R C D, CommRingCat.ofHom_comp,
        Spec.map_comp]
    rw [← Scheme.Hom.isoOpensRange_inv_comp, Category.assoc, e]
    infer_instance

theorem locally_finiteType_near : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (f : R) (P A : Scheme.{0}) [IsIntegral P] [Nonempty A] (p : P ⟶ Sp R) (ιA : A ⟶ P) (a : A ⟶ Sp (Localization.Away f)), IsPullback ιA a p (GlobalTheory.Desc.awayMap f) → LocallyOfFiniteType a → ∀ (x : Sp R) (V : P.Opens), LocallyOfFiniteType (Limits.pullback.snd (V.ι ≫ p) ((Sp R).fromSpecStalk x)) → ∀ z : P, z ∈ V → (p z).asIdeal ≤ x.asIdeal → ∃ W : P.Opens, z ∈ W ∧ W ≤ V ∧ LocallyOfFiniteType (W.ι ≫ p) := by
  intro R _ _ f P A _ _ p ιA a h ha x V hV z hz hzx
  obtain ⟨_, ⟨W₀, hW₀, rfl⟩, hzW, hWV⟩ :=
    P.isBasis_affineOpens.exists_subset_of_mem_open hz V.isOpen
  replace hW₀ : IsAffineOpen W₀ := hW₀
  haveI : Nonempty W₀ := ⟨⟨z, hzW⟩⟩
  have hr : Set.range hW₀.fromSpec ⊆ Set.range V.ι := by
    rw [hW₀.range_fromSpec, Scheme.Opens.range_ι]; exact hWV
  let j := IsOpenImmersion.lift V.ι hW₀.fromSpec hr
  have hj : j ≫ V.ι = hW₀.fromSpec := IsOpenImmersion.lift_fac _ _ _
  haveI : IsOpenImmersion (j ≫ V.ι) := by rw [hj]; infer_instance
  haveI : IsOpenImmersion j := IsOpenImmersion.of_comp j V.ι
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (hW₀.fromSpec ≫ p)
  letI : Algebra R Γ(P, W₀) := φ.hom.toAlgebra
  obtain ⟨c, hc⟩ : z ∈ Set.range hW₀.fromSpec := by rw [hW₀.range_fromSpec]; exact hzW
  have hc' : (j ≫ V.ι) c = z := by rw [hj]; exact hc
  have := affine_case R f P A p ιA a h x V Γ(P, W₀) j (by rw [hj, ← hφ]; rfl) c
    (by erw [hc']; exact hzx)
  erw [hc'] at this
  exact this

end GlobalTheory.USpread
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallyOfFiniteTypeNearGenerisationOfPointStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

theorem _root_.GlobalTheory.T.locallyOfFiniteType_near_generisation_of_point : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (f : R) (P A : Scheme.{0}) [IsIntegral P] [Nonempty A] (p : P ⟶ Sp R) (ιA : A ⟶ P) (a : A ⟶ Sp (Localization.Away f)), IsPullback ιA a p (awayMap f) → LocallyOfFiniteType a → ∀ (x : Sp R) (V : P.Opens), LocallyOfFiniteType (Limits.pullback.snd (V.ι ≫ p) ((Sp R).fromSpecStalk x)) → ∀ z : P, z ∈ V → (p z).asIdeal ≤ x.asIdeal → ∃ W : P.Opens, z ∈ W ∧ W ≤ V ∧ LocallyOfFiniteType (W.ι ≫ p) := by
  first | exact @GlobalTheory.USpread.locally_finiteType_near | exact GlobalTheory.USpread.locally_finiteType_near | (intros; apply GlobalTheory.USpread.locally_finiteType_near <;> assumption)
end
end
