module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GermSys
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.TotallySplit
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.CharacteristicPolynomialFreeGeneratorsStatement
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FormalHermitianActionPairingStatement
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FormalIsomorphismTransportStatement
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.LocalRing.Module
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FormalGermBaseChangeStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HeightCharFreeGeometricStatement
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.FactPrimes

-- Source module: Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.FreeModuleNakayamaDescent

section

@[expose] public section

open NumberField

namespace PositivityTheory.Xgn.FreeNakayamaDescent
open TensorProduct Module

theorem descent (A S M : Type) [CommRing A] [CommRing S] [Algebra A S] [Module.FaithfullyFlat A S]
    [Finite (MaximalSpectrum A)] [AddCommGroup M] [Module A M] [Module.Finite A M] (r : ℕ)
    (b : Basis (Fin r) S (S ⊗[A] M)) : Nonempty (Basis (Fin r) A M) := by
  haveI : Module.Free S (S ⊗[A] M) := Module.Free.of_basis b
  haveI : Module.Flat A M := Module.Flat.of_flat_tensorProduct A M S
  have hrk : ∀ p : PrimeSpectrum A, rankAtStalk M p = r := by
    intro p
    obtain ⟨q, rfl⟩ := PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := A) (B := S) p
    haveI : Nontrivial S := q.nontrivial
    rw [← rankAtStalk_baseChange, rankAtStalk_eq_finrank_of_free]
    simp [finrank_eq_card_basis b]
  apply nonempty_basis_of_flat_of_finrank_eq A M r
  intro P
  haveI := P.2
  letI := Ideal.Quotient.field P.1
  have h := rankAtStalk_baseChange (R := A) (M := M) (S := A ⧸ P.1) ⟨⊥, Ideal.isPrime_bot⟩
  rw [hrk, rankAtStalk_eq_finrank_of_free] at h
  simpa using h

theorem basis_of_tower (k S T ι : Type) [Field k] [CommRing S] [Algebra k S] [AddCommGroup T]
    [Module k T] [Module S T] [IsScalarTower k S T] [Fintype ι] (c : Basis ι k S) (r : ℕ)
    (y : Fin r → T) (hli : LinearIndependent k (fun q : Fin r × ι => c q.2 • y q.1))
    (hsp : Submodule.span k (Set.range fun q : Fin r × ι => c q.2 • y q.1) = ⊤) :
    Nonempty (Basis (Fin r) S T) := by
  refine ⟨Basis.mk (v := y) ?_ ?_⟩
  · rw [Fintype.linearIndependent_iff] at hli ⊢
    intro g hg j
    have := hli (fun q => c.repr (g q.1) q.2) (by
      rw [Fintype.sum_prod_type, ← hg]
      refine Finset.sum_congr rfl fun j _ => ?_
      conv_rhs => rw [← c.sum_repr (g j), Finset.sum_smul]
      simp only [smul_assoc])
    apply c.repr.injective
    ext i
    simpa using this (j, i)
  · intro t _
    have ht : t ∈ Submodule.span k (Set.range fun q : Fin r × ι => c q.2 • y q.1) := by
      rw [hsp]; trivial
    have hle : Submodule.span k (Set.range fun q : Fin r × ι => c q.2 • y q.1) ≤
        (Submodule.span S (Set.range y)).restrictScalars k := by
      rw [Submodule.span_le]
      rintro _ ⟨q, rfl⟩
      exact Submodule.smul_mem (Submodule.span S (Set.range y)) (c q.2)
        (Submodule.subset_span (Set.mem_range_self q.1))
    exact hle ht

theorem abstract_descent (F k A S M N ι : Type) [Field F] [Field k] [CommRing A] [CommRing S]
    [Algebra F k] [Algebra F A] [Algebra F S] [Algebra k S] [Algebra A S]
    [IsScalarTower F k S] [IsScalarTower F A S] [Algebra.IsPushout F k A S]
    [Module.FaithfullyFlat A S]
    [AddCommGroup M] [Module F M] [Module A M] [IsScalarTower F A M] [Module.Finite F M]
    [AddCommGroup N] [Module k N] [Fintype ι] (b : Basis ι F A)
    (e : k ⊗[F] M ≃ₗ[k] N) (act : ι → N →ₗ[k] N)
    (hact : ∀ i m, act i (e (1 ⊗ₜ m)) = e (1 ⊗ₜ (b i • m))) (r : ℕ) (x : Fin r → N)
    (hli : LinearIndependent k (fun q : Fin r × ι => act q.2 (x q.1)))
    (hsp : Submodule.span k (Set.range fun q : Fin r × ι => act q.2 (x q.1)) = ⊤) :
    ∃ x0 : Fin r → M, LinearIndependent F (fun q : Fin r × ι => b q.2 • x0 q.1) ∧
      Submodule.span F (Set.range fun q : Fin r × ι => b q.2 • x0 q.1) = ⊤ := by
  haveI : Module.Finite F A := Module.Finite.of_basis b
  haveI : IsArtinianRing A := IsArtinianRing.of_finite F A
  haveI : Module.Finite A M := Module.Finite.of_restrictScalars_finite F A M
  have ibc : IsBaseChange k (IsScalarTower.toAlgHom F A S).toLinearMap := Algebra.IsPushout.out
  let c : Basis ι k S := ibc.basis b
  have hc : ∀ i, c i = algebraMap A S (b i) := fun i => ibc.basis_apply b i
  let g : S ⊗[A] M ≃ₗ[k] N := (Algebra.IsPushout.cancelBaseChange F k A S M).trans e
  have hg : ∀ i (n : N), g.symm (act i n) = c i • g.symm n := by
    intro i n
    obtain ⟨t, rfl⟩ := e.surjective n
    induction t with
    | add u v hu hv => simp only [map_add (f := _), hu, hv, smul_add]
    | tmul s m =>
      have h1 : (s ⊗ₜ[F] m : k ⊗[F] M) = s • (1 ⊗ₜ[F] m) := by simp [smul_tmul']
      rw [h1, map_smul, map_smul, hact, map_smul, map_smul, smul_comm, hc]
      congr 1
      simp [g, smul_tmul', ← smul_tmul, Algebra.smul_def]
  obtain ⟨bS⟩ := basis_of_tower k S (S ⊗[A] M) ι c r (fun j => g.symm (x j))
    (by
      have := hli.map' g.symm.toLinearMap g.symm.ker
      have h2 : (fun q : Fin r × ι => c q.2 • g.symm (x q.1)) =
          g.symm.toLinearMap ∘ (fun q : Fin r × ι => act q.2 (x q.1)) := by
        funext q
        simp [hg]
      rw [h2]
      exact this)
    (by
      have : (fun q : Fin r × ι => c q.2 • g.symm (x q.1)) =
          g.symm.toLinearMap ∘ (fun q : Fin r × ι => act q.2 (x q.1)) := by
        funext q
        simp [hg]
      rw [this, Set.range_comp, ← Submodule.map_span, hsp, Submodule.map_top]
      exact g.symm.range)
  obtain ⟨bA⟩ := descent A S M r bS
  refine ⟨bA, ?_⟩
  have : (fun q : Fin r × ι => b q.2 • bA q.1) = b.smulTower' bA := by
    funext q
    exact (Basis.smulTower'_apply b bA q).symm
  rw [this]
  exact ⟨Basis.linearIndependent _, Basis.span_eq _⟩

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
theorem matrix_descent (F k A n ι : Type) [Field F] [Field k] [CommRing A]
    [Algebra F k] [Algebra F A] [Fintype n] [DecidableEq n] [Fintype ι] (b : Basis ι F A)
    (φ : A →ₐ[F] Matrix n n F) (r : ℕ) (x : Fin r → n → k)
    (hli : LinearIndependent k
      (fun q : Fin r × ι => ((φ (b q.2)).map (algebraMap F k)).mulVec (x q.1)))
    (hsp : Submodule.span k (Set.range fun q : Fin r × ι =>
      ((φ (b q.2)).map (algebraMap F k)).mulVec (x q.1)) = ⊤) :
    ∃ x0 : Fin r → n → F, LinearIndependent F (fun q : Fin r × ι => (φ (b q.2)).mulVec (x0 q.1)) ∧
      Submodule.span F (Set.range fun q : Fin r × ι => (φ (b q.2)).mulVec (x0 q.1)) = ⊤ := by
  letI : Module A (n → F) := Module.compHom (n → F) φ.toRingHom
  have hs : ∀ (a : A) (m : n → F), a • m = (φ a).mulVec m := fun _ _ => rfl
  haveI : IsScalarTower F A (n → F) := ⟨fun c a m => by
    rw [hs, hs, map_smul, Matrix.smul_mulVec]⟩
  haveI : Algebra.IsPushout F k A (A ⊗[F] k) := Algebra.IsPushout.symm inferInstance
  exact abstract_descent F k A (A ⊗[F] k) (n → F) (n → k) ι b
    (TensorProduct.piScalarRight F k k n)
    (fun i => ((φ (b i)).map (algebraMap F k)).mulVecLin)
    (by
      intro i m
      funext a
      simp [hs, Matrix.mulVec, dotProduct, Algebra.smul_def]) r x hli hsp

theorem int_descent (F k O n ι : Type) [Field F] [Field k] [CommRing O]
    [Algebra F k] [Fintype n] [DecidableEq n] [Fintype ι] (β : Basis ι ℤ O)
    (ρ : O →+* Matrix n n F) (r : ℕ) (x : Fin r → n → k)
    (hli : LinearIndependent k
      (fun q : Fin r × ι => ((ρ (β q.2)).map (algebraMap F k)).mulVec (x q.1)))
    (hsp : Submodule.span k (Set.range fun q : Fin r × ι =>
      ((ρ (β q.2)).map (algebraMap F k)).mulVec (x q.1)) = ⊤) :
    ∃ x0 : Fin r → n → F, LinearIndependent F (fun q : Fin r × ι => (ρ (β q.2)).mulVec (x0 q.1)) ∧
      Submodule.span F (Set.range fun q : Fin r × ι => (ρ (β q.2)).mulVec (x0 q.1)) = ⊤ := by
  let φ : F ⊗[ℤ] O →ₐ[F] Matrix n n F :=
    Algebra.TensorProduct.lift (Algebra.ofId F _) ρ.toIntAlgHom
      (fun c y => Algebra.commute_algebraMap_left c _)
  let b := Algebra.TensorProduct.basis F β
  have hb : ∀ i, φ (b i) = ρ (β i) := by
    intro i
    simp only [φ, b, Algebra.TensorProduct.basis_apply]
    refine (Algebra.TensorProduct.lift_tmul _ _ _ _ _).trans ?_
    rw [map_one, one_mul]
    rfl
  have := matrix_descent F k _ n _ b φ r x
    (by simpa only [hb] using hli) (by simpa only [hb] using hsp)
  simpa only [hb] using this

theorem lift_basis (R n κ : Type) [CommRing R] [IsLocalRing R] [Fintype n] [DecidableEq n]
    [Fintype κ] (v : κ → n → R)
    (hli : LinearIndependent (IsLocalRing.ResidueField R)
      (fun q => fun a => IsLocalRing.residue R (v q a)))
    (hsp : Submodule.span (IsLocalRing.ResidueField R)
      (Set.range fun q => fun a => IsLocalRing.residue R (v q a)) = ⊤) :
    LinearIndependent R v ∧ Submodule.span R (Set.range v) = ⊤ := by
  classical
  let b0 := Basis.mk hli hsp.ge
  let σ : n ≃ κ := (Pi.basisFun (IsLocalRing.ResidueField R) n).indexEquiv b0
  have h0 := ((Pi.basisFun (IsLocalRing.ResidueField R) n).reindex σ).is_basis_iff_det.1 ⟨hli, hsp⟩
  rw [((Pi.basisFun R n).reindex σ).is_basis_iff_det]
  rw [Basis.det_apply] at h0 ⊢
  rw [← isUnit_map_iff (IsLocalRing.residue R), RingHom.map_det]
  convert h0 using 2
  ext i j
  simp [Basis.toMatrix_apply]

end PositivityTheory.Xgn.FreeNakayamaDescent

theorem PositivityTheory.Xgn.free_module_nakayama_descent : ∀ (E : Type) [Field E] [NumberField E] (R k : Type) [CommRing R] [IsLocalRing R] [Field k] (f : R →+* k) [IsLocalHom f] (n : Type) [Fintype n] [DecidableEq n] (r : ℕ) (ρ : 𝓞 E →+* Matrix n n R), (∃ x : Fin r → n → k, LinearIndependent k (fun q : Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 E) => ((ρ (RingOfIntegers.basis E q.2)).map f).mulVec (x q.1)) ∧ Submodule.span k (Set.range fun q : Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 E) => ((ρ (RingOfIntegers.basis E q.2)).map f).mulVec (x q.1)) = ⊤) → ∃ x : Fin r → n → R, LinearIndependent R (fun q : Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 E) => (ρ (RingOfIntegers.basis E q.2)).mulVec (x q.1)) ∧ Submodule.span R (Set.range fun q : Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 E) => (ρ (RingOfIntegers.basis E q.2)).mulVec (x q.1)) = ⊤ := by
  intro E _ _ R k _ _ _ f _ n _ _ r ρ ⟨x, hli, hsp⟩
  letI : Algebra (IsLocalRing.ResidueField R) k := (IsLocalRing.ResidueField.lift f).toAlgebra
  let ρ0 : 𝓞 E →+* Matrix n n (IsLocalRing.ResidueField R) :=
    (IsLocalRing.residue R).mapMatrix.comp ρ
  have hb : ∀ a, ρ0 a = (ρ a).map (IsLocalRing.residue R) := fun _ => rfl
  have hb' : ∀ a, (ρ0 a).map (algebraMap (IsLocalRing.ResidueField R) k) = (ρ a).map f := by
    intro i
    rw [hb, Matrix.map_map]
    rfl
  obtain ⟨x0, h1, h2⟩ := PositivityTheory.Xgn.FreeNakayamaDescent.int_descent
    (IsLocalRing.ResidueField R) k _ n _ (RingOfIntegers.basis E) ρ0 r x
    (by simpa only [hb'] using hli) (by simpa only [hb'] using hsp)
  choose y hy using fun j a => IsLocalRing.residue_surjective (R := R) (x0 j a)
  refine ⟨y, ?_⟩
  have key : (fun q : Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 E) => fun a =>
      IsLocalRing.residue R ((ρ (RingOfIntegers.basis E q.2)).mulVec (y q.1) a)) =
      fun q => (ρ0 (RingOfIntegers.basis E q.2)).mulVec (x0 q.1) := by
    funext q a
    rw [hb, RingHom.map_mulVec]
    congr 1
    funext a
    exact hy _ _
  apply PositivityTheory.Xgn.FreeNakayamaDescent.lift_basis
  · rw [key]; exact h1
  · rw [key]; exact h2
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.AlgebraProofs.RepresentationBasisLinearIndependent

section

@[expose] public section

open NumberField

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem free_of_free_over_field : ∀ (E : Type) [Field E] [NumberField E] (R k : Type) [CommRing R] [IsLocalRing R] [Field k] (f : R →+* k) [IsLocalHom f] (n : Type) [Fintype n] [DecidableEq n] (r : ℕ) (ρ : 𝓞 E →+* Matrix n n R), (∃ x : Fin r → n → k, LinearIndependent k (fun q : Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 E) => ((ρ (RingOfIntegers.basis E q.2)).map f).mulVec (x q.1)) ∧ Submodule.span k (Set.range fun q : Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 E) => ((ρ (RingOfIntegers.basis E q.2)).map f).mulVec (x q.1)) = ⊤) → ∃ x : Fin r → n → R, LinearIndependent R (fun q : Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 E) => (ρ (RingOfIntegers.basis E q.2)).mulVec (x q.1)) ∧ Submodule.span R (Set.range fun q : Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 E) => (ρ (RingOfIntegers.basis E q.2)).mulVec (x q.1)) = ⊤ :=
  @PositivityTheory.Xgn.free_module_nakayama_descent

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.AlgebraProofs.RepresentationBasisLinearIndependentStatement

section

@[expose] public section

open NumberField

theorem _root_.GlobalTheory.T.representation_basis_linear_independent : ∀ (E : Type) [Field E] [NumberField E] (R k : Type) [CommRing R] [IsLocalRing R] [Field k] (f : R →+* k) [IsLocalHom f] (n : Type) [Fintype n] [DecidableEq n] (r : ℕ) (ρ : 𝓞 E →+* Matrix n n R), (∃ x : Fin r → n → k, LinearIndependent k (fun q : Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 E) => ((ρ (RingOfIntegers.basis E q.2)).map f).mulVec (x q.1)) ∧ Submodule.span k (Set.range fun q : Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 E) => ((ρ (RingOfIntegers.basis E q.2)).map f).mulVec (x q.1)) = ⊤) → ∃ x : Fin r → n → R, LinearIndependent R (fun q : Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 E) => (ρ (RingOfIntegers.basis E q.2)).mulVec (x q.1)) ∧ Submodule.span R (Set.range fun q : Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 E) => (ρ (RingOfIntegers.basis E q.2)).mulVec (x q.1)) = ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.free_of_free_over_field | exact GlobalTheory.CompanionTheory.Ar.Flat.free_of_free_over_field | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.free_of_free_over_field <;> assumption)
end
end

-- Source module: Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.HodgeFreeEveryStalk

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace PositivityTheory.Xgn.HodgeFreeStalk

abbrev eqv (R : Type) [CommRing R] (d : ℕ) : ((Fin d ⊕ Fin d) → R) ≃ₗ[R] (Fin d → R) × (Fin d → R) :=
  LinearEquiv.sumArrowLequivProdArrow (Fin d) (Fin d) R R

noncomputable def hm {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O] (B : Germ.FB R d O)
    (a : O) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) R :=
  Matrix.fromBlocks (rho B a) 0 (-(bil (B.ad a) 1 1).transpose) (rho B (star a)).transpose

section
variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]

theorem rhoH_eqv (B : Germ.FB R d O) (a : O) (v : (Fin d ⊕ Fin d) → R) :
    rhoH B a (eqv R d v) = eqv R d ((hm B a).mulVec v) := by
  rw [rhoH_apply, hm, Matrix.fromBlocks_mulVec]
  refine Prod.ext ?_ ?_
  · funext i
    simp [Function.comp_def, LinearEquiv.sumArrowLequivProdArrow, Equiv.sumArrowEquivProdArrow]
  · funext i
    simp [Function.comp_def, LinearEquiv.sumArrowLequivProdArrow, Equiv.sumArrowEquivProdArrow,
      Matrix.neg_mulVec, sub_eq_neg_add]

theorem conj_eq (B : Germ.FB R d O) (a : O) :
    (eqv R d).conj (Matrix.toLin' (hm B a)) = rhoH B a := by
  refine LinearMap.ext fun y => ?_
  obtain ⟨v, rfl⟩ := (eqv R d).surjective y
  rw [rhoH_eqv, LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply, Matrix.toLin'_apply]

theorem charpoly_eq [Nontrivial R] (B : Germ.FB R d O) (a : O) : (rhoH B a).charpoly = (hm B a).charpoly := by
  rw [← conj_eq, LinearEquiv.charpoly_conj, Matrix.charpoly_toLin']

theorem hm_map {R₂ : Type} [CommRing R₂] {f : R →+* R₂} {B : Germ.FB R d O} {B₂ : Germ.FB R₂ d O}
    (h : IsMapOf f B B₂) (a : O) : hm B₂ a = (hm B a).map f := by
  ext (i | i) (j | j) <;> simp [hm, rho, lin, bil, h.act, h.ad, MvPowerSeries.coeff_map]

theorem exists_hom (B : Germ.FB R d O) :
    ∃ ρ : O →+* Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) R, ∀ a, ρ a = hm B a := by
  obtain ⟨ρH, hρ⟩ := (GlobalTheory.T.formal_hermitian_action_pairing R d O B).1
  have key : ∀ a, hm B a = LinearMap.toMatrix' ((eqv R d).symm.conj (ρH a)) := fun a => by
    rw [hρ, ← conj_eq, LinearEquiv.conj_symm_conj, LinearMap.toMatrix'_toLin']
  refine ⟨⟨⟨⟨hm B, ?_⟩, fun a b => ?_⟩, ?_, fun a b => ?_⟩, fun _ => rfl⟩
  · rw [key, map_one, Module.End.one_eq_id, LinearEquiv.conj_id, LinearMap.toMatrix'_id]
  · simp only [key]
    rw [map_mul, Module.End.mul_eq_comp, LinearEquiv.conj_comp, LinearMap.toMatrix'_comp]
  · simp only [key, map_zero]
  · simp only [key, map_add (f := _)]

end

section
variable {E : Type} [Field E] [NumberField E] [StarRing (𝓞 E)] {R : Type} [CommRing R] {d : ℕ}

theorem hfree_iff (B : Germ.FB R d (𝓞 E)) (r : ℕ) : HFree B r ↔ ∃ x : Fin r → (Fin d ⊕ Fin d) → R,
    LinearIndependent R (fun q : Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 E) =>
      (hm B (RingOfIntegers.basis E q.2)).mulVec (x q.1)) ∧
    Submodule.span R (Set.range fun q : Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 E) =>
      (hm B (RingOfIntegers.basis E q.2)).mulVec (x q.1)) = ⊤ := by
  have key : ∀ x : Fin r → (Fin d ⊕ Fin d) → R,
      (LinearIndependent R (fun q : Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 E) =>
        rhoH B (RingOfIntegers.basis E q.2) (eqv R d (x q.1))) ∧
      Submodule.span R (Set.range fun q : Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 E) =>
        rhoH B (RingOfIntegers.basis E q.2) (eqv R d (x q.1))) = ⊤) ↔
      (LinearIndependent R (fun q : Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 E) =>
        (hm B (RingOfIntegers.basis E q.2)).mulVec (x q.1)) ∧
      Submodule.span R (Set.range fun q : Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 E) =>
        (hm B (RingOfIntegers.basis E q.2)).mulVec (x q.1)) = ⊤) := by
    intro x
    have e : (fun q : Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 E) =>
        rhoH B (RingOfIntegers.basis E q.2) (eqv R d (x q.1))) = (eqv R d).toLinearMap ∘
        (fun q : Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 E) =>
          (hm B (RingOfIntegers.basis E q.2)).mulVec (x q.1)) := by
      funext q
      exact rhoH_eqv _ _ _
    rw [e, LinearMap.linearIndependent_iff _ (eqv R d).ker, Set.range_comp, ← Submodule.map_span,
      Submodule.map_eq_top_iff]
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨y, rfl⟩ : ∃ y : Fin r → (Fin d ⊕ Fin d) → R, (fun i => eqv R d (y i)) = x :=
      ⟨fun i => (eqv R d).symm (x i), funext fun i => (eqv R d).apply_symm_apply _⟩
    exact ⟨y, (key y).1 hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨fun i => eqv R d (x i), (key x).2 hx⟩

theorem hchar_map [Nontrivial R] {R₂ : Type} [CommRing R₂] [Nontrivial R₂] {f : R →+* R₂} {B : Germ.FB R d (𝓞 E)}
    {B₂ : Germ.FB R₂ d (𝓞 E)} (h : IsMapOf f B B₂) {r : ℕ} (hB : HChar B r) : HChar B₂ r := by
  intro a
  rw [charpoly_eq, hm_map h, Matrix.charpoly_map, ← charpoly_eq, hB a, Polynomial.map_pow, Polynomial.map_map,
    Subsingleton.elim (f.comp (Int.castRingHom R)) (Int.castRingHom R₂)]

theorem hchar_of_map [Nontrivial R] {R₂ : Type} [CommRing R₂] [Nontrivial R₂] {f : R →+* R₂}
    (hf : Function.Injective f) {B : Germ.FB R d (𝓞 E)}
    {B₂ : Germ.FB R₂ d (𝓞 E)} (h : IsMapOf f B B₂) {r : ℕ} (hB : HChar B₂ r) : HChar B r := by
  intro a
  apply Polynomial.map_injective f hf
  rw [charpoly_eq, ← Matrix.charpoly_map, ← hm_map h, ← charpoly_eq, hB a, Polynomial.map_pow, Polynomial.map_map,
    Subsingleton.elim (f.comp (Int.castRingHom R)) (Int.castRingHom R₂)]

theorem hchar_iso [Nontrivial R] {B B₂ : Germ.FB R d (𝓞 E)} {φ ψ : Germ.Pt R 1 d} {lam : Germ.PS R 2 d}
    (h : GlobalTheory.CompanionTheory.Ar.Conj.IsIso B B₂ φ ψ lam) {r : ℕ} (hB : HChar B r) : HChar B₂ r := by
  intro a
  obtain ⟨-, -, hb, -, hc, -⟩ := GlobalTheory.T.formal_isomorphism_transport R d (𝓞 E) B B₂ φ ψ lam h
  have e : (LinearEquiv.ofBijective (transH φ ψ lam) hb).conj (rhoH B₂ a) = rhoH B a := by
    refine LinearMap.ext fun y => ?_
    obtain ⟨v, rfl⟩ := (LinearEquiv.ofBijective (transH φ ψ lam) hb).surjective y
    rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
    exact (LinearMap.congr_fun (hc a) v).symm
  rw [← hB a, ← e, LinearEquiv.charpoly_conj]

theorem hfree_of_map [IsLocalRing R] {k : Type} [Field k] {f : R →+* k} [IsLocalHom f] {B : Germ.FB R d (𝓞 E)}
    {B₂ : Germ.FB k d (𝓞 E)} (h : IsMapOf f B B₂) {r : ℕ} (hB : HFree B₂ r) : HFree B r := by
  obtain ⟨ρ, hρ⟩ := exists_hom B
  have := GlobalTheory.T.representation_basis_linear_independent E R k f (Fin d ⊕ Fin d) r ρ
  simp only [hρ, ← hm_map h] at this
  exact (hfree_iff B r).2 (this ((hfree_iff B₂ r).1 hB))

theorem hfree_char0 [IsLocalRing R] {k : Type} [Field k] [CharZero k] (f : R →+* k) [IsLocalHom f]
    {B : Germ.FB R d (𝓞 E)} {r : ℕ} (hB : HChar B r) : HFree B r := by
  obtain ⟨ρ, hρ⟩ := exists_hom B
  have h1 := GlobalTheory.T.representation_basis_linear_independent E R k f (Fin d ⊕ Fin d) r ρ
  let ρk : 𝓞 E →+* Module.End k ((Fin d ⊕ Fin d) → k) :=
    ((Matrix.toLinAlgEquiv' (R := k) (n := Fin d ⊕ Fin d)).toRingEquiv.toRingHom.comp f.mapMatrix).comp ρ
  have hk : ∀ a, ρk a = Matrix.toLin' ((ρ a).map f) := fun a => rfl
  have h2 := GlobalTheory.T.characteristic_polynomial_free_generators E k ((Fin d ⊕ Fin d) → k) r ρk (fun a => by
    rw [hk, Matrix.charpoly_toLin', Matrix.charpoly_map, hρ, ← charpoly_eq, hB a, Polynomial.map_pow,
      Polynomial.map_map, Subsingleton.elim (f.comp (Int.castRingHom R)) (Int.castRingHom k)])
  simp only [hk, Matrix.toLin'_apply] at h2
  have h3 := h1 h2
  simp only [hρ] at h3
  exact (hfree_iff B r).2 h3

end

theorem at_point (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)]
    (hs : ∀ a : 𝓞 E, star a = H.bar a) (X : Scheme.{0}) (t : SAB H X) (d r : ℕ) (hP : PowFns t) (z : X)
    (g : GermAt t (S := X.presheaf.stalk z) (X.fromSpecStalk z) d) (hc : HChar g.B r)
    (hF : ∀ p : ℕ, p.Prime → (p : X.residueField z) = 0 → FibPF t z) : HFree g.B r := by
  obtain ⟨p, hp⟩ := CharP.exists (IsLocalRing.ResidueField (X.presheaf.stalk z))
  rcases CharP.char_is_prime_or_zero (IsLocalRing.ResidueField (X.presheaf.stalk z)) p with hpp | rfl
  · have h0 : (p : IsLocalRing.ResidueField (X.presheaf.stalk z)) = 0 := CharP.cast_eq_zero _ p
    obtain ⟨k, _, _, x, rfl, hx⟩ := hF p hpp h0
    let f : X.presheaf.stalk (x (IsLocalRing.closedPoint k)) →+* k := (Scheme.stalkClosedPointTo x).hom
    have : IsLocalHom f := inferInstanceAs (IsLocalHom (Scheme.stalkClosedPointTo x).hom)
    have hpk : (p : k) = 0 := by
      by_contra hne
      have hu : IsUnit (f p) := by rw [map_natCast]; exact Ne.isUnit hne
      have hu' := (isUnit_of_map_unit f _ hu).map (IsLocalRing.residue _)
      rw [map_natCast, h0] at hu'
      exact not_isUnit_zero hu'
    have : Fact p.Prime := ⟨hpp⟩
    have : CharP k p := (CharP.charP_iff_prime_eq_zero hpp).2 hpk
    obtain ⟨g₂, hm₂, -⟩ := GlobalTheory.T.formal_germ_base_change E H hs X t _ k f _ d g
    have e : spMap f ≫ X.fromSpecStalk (x (IsLocalRing.closedPoint k)) = x :=
      Scheme.Spec_stalkClosedPointTo_fromSpecStalk x
    have hx' : GeomPF t (spMap f ≫ X.fromSpecStalk (x (IsLocalRing.closedPoint k))) := by
      rw [e]; exact hx
    exact hfree_of_map hm₂ (GlobalTheory.T.height_char_free_geometric E H hs X t hP k p _ hx' d r g₂ (hchar_map hm₂ hc))
  · have := CharP.charP_to_charZero (IsLocalRing.ResidueField (X.presheaf.stalk z))
    exact hfree_char0 (IsLocalRing.residue (X.presheaf.stalk z)) hc

end PositivityTheory.Xgn.HodgeFreeStalk

open PositivityTheory.Xgn.HodgeFreeStalk in
theorem PositivityTheory.Xgn.hodge_free_every_stalk : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X : Scheme.{0}) (t : SAB H X) (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Sp Ω ⟶ X) (d r : ℕ) (M : LieModel t.G ξ (Fin d → Ω)) (S : GermSys t ξ M), PowFns t → IsCptGen ξ → HChar S.g₀.B r → (∀ (q : Cpt ξ) (p : ℕ), p.Prime → (p : X.residueField q.1) = 0 → FibPF t q.1) → ∀ q : Cpt ξ, HFree (S.g q).B r := by
  intro E _ _ _ H _ hs X t Ω _ _ ξ d r M S hP hξ hc hF q
  exact at_point E H hs X t d r hP q.1 (S.g q)
    (hchar_of_map (hξ.inj q) (S.mapK q) (hchar_iso (S.iso q) hc)) (hF q)
end
end
