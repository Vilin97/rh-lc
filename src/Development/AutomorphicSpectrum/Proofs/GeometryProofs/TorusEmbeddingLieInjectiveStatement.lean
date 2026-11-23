module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCocharLie
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCocharLieLieModel
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
import Mathlib.RingTheory.RegularLocalRing.Defs
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
public import Mathlib.RingTheory.Nakayama
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsCocharacterLieModelStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelExistsUniqueSemilinear
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelFiniteProjectiveStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CharValMultiplicativeStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.KillsOverOfAdicCompletionStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.KillsOverSquareZeroLiftStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorusKernelPrimeQuotientStatement
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.ReduceModChar
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Development.AutomorphicSpectrum.Proofs.AlgebraProofs.MemMaxSmulTopIff

section

@[expose] public section

open Matrix Filter Topology
open scoped BigOperators ComplexOrder

namespace GlobalTheory.CompanionTheory.CommAlg.SatOfInj

theorem mem_max_smul_top_iff {R M : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [AddCommGroup M] [Module R M] {π : R} (hπ : Irreducible π) (x : M) :
    x ∈ IsLocalRing.maximalIdeal R • (⊤ : Submodule R M) ↔ ∃ z : M, x = π • z := by
  rw [IsDiscreteValuationRing.irreducible_iff_uniformizer π |>.mp hπ,
    Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨z, -, rfl⟩
    exact ⟨z, rfl⟩
  · rintro ⟨z, rfl⟩
    exact ⟨z, trivial, rfl⟩

theorem eq_zero_of_smul {R M : Type} [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M]
    [Module.IsTorsionFree R M] {a : R} (ha : a ≠ 0) {z : M} (h : a • z = 0) : z = 0 :=
  (smul_eq_zero.mp h).resolve_left ha

theorem pow_step {R P E : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [AddCommGroup P] [Module R P] [AddCommGroup E] [Module R E] [Module.IsTorsionFree R E]
    (f : P →ₗ[R] E) {π : R} (hπ : Irreducible π)
    (hf : ∀ x : P, f x ∈ IsLocalRing.maximalIdeal R • (⊤ : Submodule R E) →
      x ∈ IsLocalRing.maximalIdeal R • (⊤ : Submodule R P))
    (n : ℕ) : ∀ (y : E), π ^ n • y ∈ LinearMap.range f → y ∈ LinearMap.range f := by
  induction n with
  | zero => intro y hy; simpa using hy
  | succ n ih =>
    intro y hy
    obtain ⟨x, hx⟩ := hy
    have hmem : f x ∈ IsLocalRing.maximalIdeal R • (⊤ : Submodule R E) := by
      rw [mem_max_smul_top_iff hπ]
      exact ⟨π ^ n • y, by rw [hx, pow_succ', mul_smul]⟩
    obtain ⟨x', rfl⟩ := (mem_max_smul_top_iff hπ x).mp (hf x hmem)
    refine ih y ⟨x', ?_⟩
    have h0 : π • (f x' - π ^ n • y) = 0 := by
      rw [smul_sub, ← map_smul, hx, pow_succ', mul_smul, sub_self]
    exact sub_eq_zero.mp (eq_zero_of_smul hπ.ne_zero h0)

theorem sat_of_inj_mod : ∀ (R P E : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [AddCommGroup P] [Module R P] [Module.Finite R P] [AddCommGroup E] [Module R E]
    [Module.IsTorsionFree R E] [Module.IsTorsionFree R P] (f : P →ₗ[R] E),
    (∀ x : P, f x ∈ IsLocalRing.maximalIdeal R • (⊤ : Submodule R E) →
      x ∈ IsLocalRing.maximalIdeal R • (⊤ : Submodule R P)) →
    Function.Injective f ∧ ∀ (a : R) (y : E), a ≠ 0 → a • y ∈ LinearMap.range f →
      y ∈ LinearMap.range f := by
  intro R P E _ _ _ _ _ _ _ _ _ _ f hf
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  refine ⟨?_, ?_⟩
  · rw [← LinearMap.ker_eq_bot]
    refine Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (IsLocalRing.maximalIdeal R) _
      (IsNoetherian.noetherian _) ?_ (IsLocalRing.maximalIdeal_le_jacobson _)
    intro x hx
    have hx0 : f x = 0 := hx
    have hmem : f x ∈ IsLocalRing.maximalIdeal R • (⊤ : Submodule R E) := by
      rw [hx0]; exact Submodule.zero_mem _
    obtain ⟨x', rfl⟩ := (mem_max_smul_top_iff hπ x).mp (hf x hmem)
    have hx' : f x' = 0 := by
      rw [map_smul] at hx0
      exact eq_zero_of_smul hπ.ne_zero hx0
    exact Submodule.smul_mem_smul
      ((IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ ▸ Ideal.mem_span_singleton_self π)
      (LinearMap.mem_ker.mpr hx')
  · intro a y ha hy
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hπ
    have h1 : π ^ n • ((u : R) • y) ∈ LinearMap.range f := by
      rw [smul_smul, mul_comm]
      exact hy
    have h2 := pow_step f hπ hf n _ h1
    have h3 := Submodule.smul_mem _ ((u⁻¹ : Rˣ) : R) h2
    rwa [smul_smul, Units.inv_mul, one_smul] at h3

end GlobalTheory.CompanionTheory.CommAlg.SatOfInj
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorusInjectiveLieMap

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.TsClosed

theorem spMap_comp_eq {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, ← Spec.map_comp]
  rfl

variable {S : Scheme.{0}} {X : Type} [AddCommGroup X] {G : Over S} [GrpObj G]

theorem exists_transport (u : splitTorus S X ⟶ G) {A : Type} [CommRing A] {a a' : Sp A ⟶ S} (e : a = a')
    (t : Over.mk a ⟶ splitTorus S X) :
    ∃ t' : Over.mk a' ⟶ splitTorus S X, (∀ χ, charVal t' χ = charVal t χ) ∧ (t' ≫ u = 1 → t ≫ u = 1) := by
  subst e
  exact ⟨t, fun _ => rfl, id⟩

theorem killsOver_comp (u : splitTorus S X ⟶ G) (Y : AddSubgroup X) {B B' : Type} [CommRing B] [CommRing B']
    (b : Sp B ⟶ S) (c : B →+* B') (h : KillsOver u Y b) : KillsOver u Y (spMap c ≫ b) := by
  intro A _ g t ht
  have e : spMap g ≫ spMap c ≫ b = spMap (g.comp c) ≫ b := by
    rw [← Category.assoc, spMap_comp_eq]
  obtain ⟨t', h1, h2⟩ := exists_transport u e t
  exact h2 (h A (g.comp c) t' fun y hy => by rw [h1]; exact ht y hy)

theorem killsOver_pow (u : splitTorus S X ⟶ G) [IsMonHom u] (Y : AddSubgroup X) {R : Type} [CommRing R]
    [IsLocalRing R] (b : Sp R ⟶ S) (h : KillsOver u Y (spMap (IsLocalRing.residue R) ≫ b)) (n : ℕ) :
    KillsOver u Y (spMap (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1))) ≫ b) := by
  induction n with
  | zero =>
    let c : IsLocalRing.ResidueField R →+* R ⧸ (IsLocalRing.maximalIdeal R ^ (0 + 1)) :=
      Ideal.Quotient.lift _ (Ideal.Quotient.mk _)
        (fun a ha => Ideal.Quotient.eq_zero_iff_mem.2 (by simpa using ha))
    have hc : c.comp (IsLocalRing.residue R) = Ideal.Quotient.mk _ := by
      ext x; rfl
    have key := killsOver_comp u Y _ c h
    rw [← Category.assoc, spMap_comp_eq, hc] at key
    exact key
  | succ n ih =>
    have hJ : IsLocalRing.maximalIdeal R ^ (n + 1 + 1) ≠ ⊤ := by
      intro e
      have h1 : IsLocalRing.maximalIdeal R ^ (n + 1 + 1) ≤ IsLocalRing.maximalIdeal R :=
        Ideal.pow_le_self (by omega)
      rw [e] at h1
      exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top (top_le_iff.1 h1)
    haveI : Nontrivial (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1 + 1)) :=
      Ideal.Quotient.nontrivial_iff.2 hJ
    haveI : IsLocalRing (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1 + 1)) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
    let I : Ideal (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1 + 1)) :=
      (IsLocalRing.maximalIdeal R ^ (n + 1)).map (Ideal.Quotient.mk _)
    have hI : I ^ 2 = ⊥ := by
      simp only [I]
      rw [← Ideal.map_pow, ← pow_mul, Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]
      exact Ideal.pow_le_pow_right (by omega)
    refine GlobalTheory.T.killsOver_square_zero_lift S G X u Y _ _ I hI ?_
    let c : R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 1)) →+*
        (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1 + 1)) ⧸ I :=
      Ideal.Quotient.lift _ ((Ideal.Quotient.mk I).comp (Ideal.Quotient.mk _))
        (fun a ha => Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ ha))
    have hc : c.comp (Ideal.Quotient.mk _) = (Ideal.Quotient.mk I).comp (Ideal.Quotient.mk _) := by
      ext x; rfl
    have key := killsOver_comp u Y _ c ih
    rw [← Category.assoc, spMap_comp_eq, hc, ← spMap_comp_eq, Category.assoc] at key
    exact key

theorem diff_injective_mod_pi : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (S : Scheme.{0}) (b : Sp R ⟶ S) (G : Over S) [GrpObj G] [IsSeparated G.hom] (X : Type) [AddCommGroup X] [Module.Finite ℤ X] (u : splitTorus S X ⟶ G) [IsMonHom u], (∀ (A : Type) [CommRing A] (g : K →+* A) (t : Over.mk (spMap g ≫ spMap (algebraMap R K) ≫ b) ⟶ splitTorus S X), t ≫ u = 1 → t = 1) → ∀ M : LieModel (splitTorus S X) (spMap (IsLocalRing.residue R) ≫ b) (X →+ IsLocalRing.ResidueField R), IsCocharLie M → ∀ δ, M.pt δ ≫ u = 1 → δ = 0 := by
  intro R K _ _ _ _ _ _ S b G _ _ X _ _ u _ hK M hM δ hδ
  by_contra hne
  obtain ⟨l, hl, ψ, hψ, hk⟩ := GlobalTheory.T.torus_kernel_prime_quotient S G X u (IsLocalRing.ResidueField R)
    (spMap (IsLocalRing.residue R) ≫ b) M hM δ hne hδ
  have hR := GlobalTheory.T.killsOver_of_adic_completion S G X u ψ.ker R b (killsOver_pow u ψ.ker b hk)
  have hKk := killsOver_comp u ψ.ker b (algebraMap R K) hR
  haveI := Fact.mk hl
  obtain ⟨-, -, h1, -, hex, -⟩ := GlobalTheory.T.charVal_multiplicative S X (AddMonoidAlgebra K (ZMod l))
    (spMap (algebraMap K (AddMonoidAlgebra K (ZMod l))) ≫ spMap (algebraMap R K) ≫ b)
  let w : Multiplicative X →* AddMonoidAlgebra K (ZMod l) :=
    (AddMonoidAlgebra.of K (ZMod l)).comp (AddMonoidHom.toMultiplicative ψ)
  obtain ⟨t, ht⟩ := hex w
  have hu : t ≫ u = 1 := hKk _ (algebraMap K (AddMonoidAlgebra K (ZMod l))) t fun y hy => by
    rw [ht]
    have hy0 : ψ y = 0 := hy
    simp [w, hy0, AddMonoidAlgebra.one_def]
  have ht1 := hK _ (algebraMap K (AddMonoidAlgebra K (ZMod l))) t hu
  obtain ⟨χ, hχ⟩ := hψ 1
  have key := ht χ
  rw [ht1, h1] at key
  simp only [w, MonoidHom.comp_apply, AddMonoidHom.toMultiplicative_apply_apply, toAdd_ofAdd, hχ] at key
  rw [AddMonoidAlgebra.one_def, AddMonoidAlgebra.of_apply, AddMonoidAlgebra.single_left_inj one_ne_zero] at key
  exact zero_ne_one key

end GlobalTheory.CompanionTheory.Ar.TsClosed
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorusInjectiveLieMapStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.torus_injective_lie_map : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (S : Scheme.{0}) (b : Sp R ⟶ S) (G : Over S) [GrpObj G] [IsSeparated G.hom] (X : Type) [AddCommGroup X] [Module.Finite ℤ X] (u : splitTorus S X ⟶ G) [IsMonHom u], (∀ (A : Type) [CommRing A] (g : K →+* A) (t : Over.mk (spMap g ≫ spMap (algebraMap R K) ≫ b) ⟶ splitTorus S X), t ≫ u = 1 → t = 1) → ∀ M : LieModel (splitTorus S X) (spMap (IsLocalRing.residue R) ≫ b) (X →+ IsLocalRing.ResidueField R), IsCocharLie M → ∀ δ, M.pt δ ≫ u = 1 → δ = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.TsClosed.diff_injective_mod_pi | exact GlobalTheory.CompanionTheory.Ar.TsClosed.diff_injective_mod_pi | (intros; apply GlobalTheory.CompanionTheory.Ar.TsClosed.diff_injective_mod_pi <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorusEmbeddingLieInjective

section

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.TorusSat

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

theorem pt_zero {S : Scheme.{0}} {R : Type} [CommRing R] {G : Over S} [GrpObj G] {x : Sp R ⟶ S} {E : Type}
    [AddCommGroup E] [Module R E] (M : LieModel G x E) : M.pt 0 = 1 := by
  have h := M.add 0 0
  rw [add_zero] at h
  exact left_eq_mul.mp h

theorem exists_div {R X : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [AddCommGroup X] {π : R}
    (hπ : Irreducible π) (δ : X →+ R) (h : ∀ χ, IsLocalRing.residue R (δ χ) = 0) :
    ∃ δ' : X →+ R, δ = π • δ' := by
  have hd : ∀ χ, ∃ r, δ χ = π * r := fun χ => by
    have hm : δ χ ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.residue_eq_zero_iff _).mp (h χ)
    rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ] at hm
    exact Ideal.mem_span_singleton'.mp hm |>.imp fun r hr => by rw [← hr, mul_comm]
  choose f hf using hd
  refine ⟨AddMonoidHom.mk' f fun a b => ?_, ?_⟩
  · apply mul_left_cancel₀ hπ.ne_zero
    rw [mul_add, ← hf, ← hf, ← hf, map_add (f := _)]
  · ext χ
    simp [hf]

theorem lie_torus_saturated : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (S : Scheme.{0}) (b : Sp R ⟶ S) (G : Over S) [GrpObj G] [IsCommMonObj G] [IsSeparated G.hom] [Smooth G.hom] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (u : splitTorus S X ⟶ G) [IsMonHom u], (∀ (A : Type) [CommRing A] (g : K →+* A) (t : Over.mk (spMap g ≫ spMap (algebraMap R K) ≫ b) ⟶ splitTorus S X), t ≫ u = 1 → t = 1) → ∀ (MT : LieModel (splitTorus S X) b (X →+ R)), IsCocharLie MT → ∀ (E : Type) [AddCommGroup E] [Module R E] (M : LieModel G b E) (A : (X →+ R) →ₗ[R] E), (∀ δ, M.pt (A δ) = MT.pt δ ≫ u) → Function.Injective A ∧ ∀ (a : R) (y : E), a ≠ 0 → a • y ∈ LinearMap.range A → y ∈ LinearMap.range A := by
  intro R K _ _ _ _ _ _ S b G _ _ _ _ X _ _ _ u _ hgen MT hMT E _ _ M A hA
  obtain ⟨hEf, hEp⟩ := GlobalTheory.T.lie_model_finite_projective S G R b E M
  obtain ⟨Mk, hMk⟩ := GlobalTheory.T.exists_cocharacter_lie_model S X (IsLocalRing.ResidueField R) (spMap (IsLocalRing.residue R) ≫ b)
  obtain ⟨Ek, i1, i2, ⟨MG⟩⟩ := lieModel_exists S G (IsLocalRing.ResidueField R) (spMap (IsLocalRing.residue R) ≫ b)
  obtain ⟨j, hj, -⟩ := LieBaseChange.existsUnique_semilinear_lifts S G R _ (IsLocalRing.residue R) b E Ek M MG
  obtain ⟨jT, hjT, -⟩ := LieBaseChange.existsUnique_semilinear_lifts S (splitTorus S X) R _
    (IsLocalRing.residue R) b (X →+ R) (X →+ IsLocalRing.ResidueField R) MT Mk
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hcπ : IsLocalRing.residue R π = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff]
    exact hπ.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self π
  have key : ∀ δ, A δ ∈ IsLocalRing.maximalIdeal R • (⊤ : Submodule R E) →
      δ ∈ IsLocalRing.maximalIdeal R • (⊤ : Submodule R (X →+ R)) := by
    intro δ hδ
    obtain ⟨z, hz⟩ := (GlobalTheory.CompanionTheory.CommAlg.SatOfInj.mem_max_smul_top_iff hπ _).mp hδ
    have h0 : j (A δ) = 0 := by
      rw [hz, map_smulₛₗ, hcπ, zero_smul]
    have a1 := hj (A δ)
    have a2 := hjT δ
    rw [Category.comp_id] at a1 a2
    rw [h0, pt_zero, hA, Over.comp_left] at a1
    have h1 : Mk.pt (jT δ) ≫ u = 1 := by
      apply Over.OverMorphism.ext
      rw [Over.comp_left, a2, Category.assoc, a1]
    have h2 : jT δ = 0 := GlobalTheory.T.torus_injective_lie_map R K S b G X u hgen Mk hMk _ h1
    have h3 : ∀ χ, IsLocalRing.residue R (δ χ) = 0 := by
      intro χ
      have e := GlobalTheory.CompanionTheory.Ar.TorusModel.charVal_comp (dualMap (IsLocalRing.residue R)) (MT.pt δ) (Mk.pt (jT δ)) a2 χ
      rw [hMk, hMT, h2] at e
      have e2 := congrArg TrivSqZeroExt.snd e
      simpa [dualMap] using e2.symm
    obtain ⟨δ', rfl⟩ := exists_div hπ δ h3
    exact (GlobalTheory.CompanionTheory.CommAlg.SatOfInj.mem_max_smul_top_iff hπ _).mpr ⟨δ', rfl⟩
  have e := addMonoidHomLequivInt (A := X) (B := R) R
  haveI : Module.Free R (X →+ R) := Module.Free.of_equiv e.symm
  haveI : Module.Finite R (X →+ R) := Module.Finite.equiv e.symm
  haveI : Module.IsTorsionFree R E := inferInstance
  exact GlobalTheory.CompanionTheory.CommAlg.SatOfInj.sat_of_inj_mod R (X →+ R) E A key

end GlobalTheory.CompanionTheory.Ar.TorusSat
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorusEmbeddingLieInjectiveStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.torus_embedding_lie_injective : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (S : Scheme.{0}) (b : Sp R ⟶ S) (G : Over S) [GrpObj G] [IsCommMonObj G] [IsSeparated G.hom] [Smooth G.hom] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (u : splitTorus S X ⟶ G) [IsMonHom u], (∀ (A : Type) [CommRing A] (g : K →+* A) (t : Over.mk (spMap g ≫ spMap (algebraMap R K) ≫ b) ⟶ splitTorus S X), t ≫ u = 1 → t = 1) → ∀ (MT : LieModel (splitTorus S X) b (X →+ R)), IsCocharLie MT → ∀ (E : Type) [AddCommGroup E] [Module R E] (M : LieModel G b E) (A : (X →+ R) →ₗ[R] E), (∀ δ, M.pt (A δ) = MT.pt δ ≫ u) → Function.Injective A ∧ ∀ (a : R) (y : E), a ≠ 0 → a • y ∈ LinearMap.range A → y ∈ LinearMap.range A := by
  first | exact @GlobalTheory.CompanionTheory.Ar.TorusSat.lie_torus_saturated | exact GlobalTheory.CompanionTheory.Ar.TorusSat.lie_torus_saturated | (intros; apply GlobalTheory.CompanionTheory.Ar.TorusSat.lie_torus_saturated <;> assumption)
end
end
