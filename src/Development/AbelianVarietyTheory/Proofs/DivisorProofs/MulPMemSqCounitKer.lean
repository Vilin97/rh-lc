module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CotangentMapInjectiveOfSquarePresentationAtPointStatement
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.Ideal.Quotient.Operations
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
public import Mathlib.Algebra.MvPolynomial.Rename
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftSquarePresentationOfFlatStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalFactorAtAugmentationCounitalComulStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.PadicActionConstInjective
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FiniteFaithfullyFlatKer
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMulPEqOfTranslInvariant
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslCoactionFreeCoassocCounital
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DUnitMemRangeOfMemKerIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigOfOmegaInjectiveOfEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupMulPUnitFibreEqLevelOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquarePresentationOfCounitalComulStatement
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPresentationSquareAtPointOfLocalFactor

section

@[expose] public section

open scoped TensorProduct

namespace GlobalTheory

theorem sqloc_present : ∀ (k A : Type) [CommRing k] [CommRing A] [Algebra k A] (ε : A →ₐ[k] k) (e : A), ε e = 1 → IsIdempotentElem e → (∃ (s : ℕ) (φ : MvPolynomial (Fin s) k →ₐ[k] (A ⧸ Ideal.span {1 - e})) (g : Fin s → MvPolynomial (Fin s) k), Function.Surjective φ ∧ RingHom.ker φ = Ideal.span (Set.range g)) → ∀ (r : ℕ) (a : Fin r → A), Function.Surjective (MvPolynomial.aeval a : MvPolynomial (Fin r) k →ₐ[k] A) → ∃ (s : ℕ) (y : Fin s → A) (g : Fin s ⊕ Fin r → MvPolynomial (Fin s ⊕ Fin r) k), (∀ i, MvPolynomial.aeval (Sum.elim y a) (g i) = 0) ∧ RingHom.ker (MvPolynomial.aeval (Sum.elim y a) : MvPolynomial (Fin s ⊕ Fin r) k →ₐ[k] A) ≤ Ideal.span (Set.range g) ⊔ RingHom.ker (ε.comp (MvPolynomial.aeval (Sum.elim y a) : MvPolynomial (Fin s ⊕ Fin r) k →ₐ[k] A)) * RingHom.ker (MvPolynomial.aeval (Sum.elim y a) : MvPolynomial (Fin s ⊕ Fin r) k →ₐ[k] A) := by
  intro k A _ _ _ ε e he hidem ⟨s, φ, g', hφ, hker⟩ r a ha
  classical
  choose y hy using fun i : Fin s => Ideal.Quotient.mk_surjective (I := Ideal.span {1 - e}) (φ (MvPolynomial.X i))
  choose h hh using fun j : Fin r => hφ (Ideal.Quotient.mk (Ideal.span {1 - e}) (a j))
  set Ψ : MvPolynomial (Fin s ⊕ Fin r) k →ₐ[k] A := MvPolynomial.aeval (Sum.elim y a) with hΨ
  have hΨsurj : Function.Surjective Ψ := by
    intro x
    obtain ⟨p, hp⟩ := ha x
    refine ⟨MvPolynomial.rename Sum.inr p, ?_⟩
    rw [hΨ, MvPolynomial.aeval_rename, Sum.elim_comp_inr]
    exact hp
  obtain ⟨u, hu⟩ := hΨsurj e
  set κ : MvPolynomial (Fin s ⊕ Fin r) k →ₐ[k] MvPolynomial (Fin s) k :=
    MvPolynomial.aeval (Sum.elim MvPolynomial.X h) with hκdef
  have hκ : (Ideal.Quotient.mkₐ k (Ideal.span {1 - e})).comp Ψ = φ.comp κ := by
    apply MvPolynomial.algHom_ext
    intro i
    rcases i with i | j
    · simp [hΨ, hκdef, hy]
    · simp [hΨ, hκdef, hh]
  have hκF : ∀ F, Ideal.Quotient.mk (Ideal.span {1 - e}) (Ψ F) = φ (κ F) := by
    intro F
    have := congrArg (fun f => f F) hκ
    simpa using this
  let G : Fin s ⊕ Fin r → MvPolynomial (Fin s ⊕ Fin r) k :=
    Sum.elim (fun i => MvPolynomial.rename Sum.inl (g' i))
      (fun j => MvPolynomial.X (Sum.inr j) - MvPolynomial.rename Sum.inl (h j))
  have hκr : ∀ p, κ (MvPolynomial.rename Sum.inl p) = p := by
    intro p
    rw [hκdef, MvPolynomial.aeval_rename, Sum.elim_comp_inl, MvPolynomial.aeval_X_left_apply]
  have hκX : ∀ j, κ (MvPolynomial.X (Sum.inr j)) = h j := by
    intro j
    rw [hκdef, MvPolynomial.aeval_X, Sum.elim_inr]
  have hg'ker : ∀ i, φ (g' i) = 0 := by
    intro i
    have : g' i ∈ RingHom.ker φ := hker ▸ Ideal.subset_span ⟨i, rfl⟩
    simpa using this
  have hΨG : ∀ i, Ideal.Quotient.mk (Ideal.span {1 - e}) (Ψ (G i)) = 0 := by
    intro i
    rw [hκF]
    rcases i with i | j
    · simp only [G, Sum.elim_inl, hκr, hg'ker]
    · simp only [G, Sum.elim_inr, map_sub, hκr, hκX, sub_self, map_zero]
  have hΨuG : ∀ i, Ψ (u * G i) = 0 := by
    intro i
    have hm : Ψ (G i) ∈ Ideal.span {1 - e} := Ideal.Quotient.eq_zero_iff_mem.mp (hΨG i)
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hm
    rw [map_mul, hu, ← hc]
    have h0 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, hidem.eq, sub_self]
    calc e * (c * (1 - e)) = c * (e * (1 - e)) := by ring
      _ = 0 := by rw [h0, mul_zero]
  refine ⟨s, y, fun i => u * G i, hΨuG, ?_⟩
  rw [← hΨ]
  intro F hF
  rw [RingHom.mem_ker] at hF

  have hFG : F ∈ Ideal.span (Set.range G) := by
    have hq : (Ideal.Quotient.mkₐ k (Ideal.span (Set.range G))).comp
        ((MvPolynomial.rename Sum.inl).comp κ) = Ideal.Quotient.mkₐ k (Ideal.span (Set.range G)) := by
      apply MvPolynomial.algHom_ext
      intro i
      rcases i with i | j
      · simp only [AlgHom.comp_apply, hκdef, MvPolynomial.aeval_X, Sum.elim_inl,
          MvPolynomial.rename_X]
      · simp only [AlgHom.comp_apply, hκX, Ideal.Quotient.mkₐ_eq_mk]
        rw [Ideal.Quotient.eq]
        rw [← neg_sub, neg_mem_iff]
        exact Ideal.subset_span ⟨Sum.inr j, rfl⟩
    have h1 : F - MvPolynomial.rename Sum.inl (κ F) ∈ Ideal.span (Set.range G) := by
      have := congrArg (fun f => f F) hq
      simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk] at this
      rw [← neg_sub, neg_mem_iff]
      exact Ideal.Quotient.eq.mp this
    have hmem : κ F ∈ Ideal.span (Set.range g') := by
      rw [← hker, RingHom.mem_ker, ← hκF, hF, map_zero]
    have h2 : MvPolynomial.rename Sum.inl (κ F) ∈ Ideal.span (Set.range G) := by
      have := Ideal.mem_map_of_mem (MvPolynomial.rename (R := k) (Sum.inl : Fin s → Fin s ⊕ Fin r)) hmem
      rw [Ideal.map_span] at this
      refine Ideal.span_mono ?_ this
      rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨Sum.inl i, rfl⟩
    have := Ideal.add_mem _ h1 h2
    simpa using this
  have hsplit : F = u * F + (1 - u) * F := by ring
  rw [hsplit]
  refine Submodule.add_mem_sup ?_ ?_
  · obtain ⟨c, hc⟩ := (Ideal.mem_span_range_iff_exists_fun).mp hFG
    refine (Ideal.mem_span_range_iff_exists_fun).mpr ⟨c, ?_⟩
    rw [← hc, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  · apply Ideal.mul_mem_mul
    · rw [RingHom.mem_ker]
      simp [hu, he]
    · exact hF

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPresentationSquareAtPointOfLocalFactorStatement

section

@[expose] public section

open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_presentation_square_at_point_of_localFactor : ∀ (k A : Type) [CommRing k] [CommRing A] [Algebra k A] (ε : A →ₐ[k] k) (e : A), ε e = 1 → IsIdempotentElem e → (∃ (s : ℕ) (φ : MvPolynomial (Fin s) k →ₐ[k] (A ⧸ Ideal.span {1 - e})) (g : Fin s → MvPolynomial (Fin s) k), Function.Surjective φ ∧ RingHom.ker φ = Ideal.span (Set.range g)) → ∀ (r : ℕ) (a : Fin r → A), Function.Surjective (MvPolynomial.aeval a : MvPolynomial (Fin r) k →ₐ[k] A) → ∃ (s : ℕ) (y : Fin s → A) (g : Fin s ⊕ Fin r → MvPolynomial (Fin s ⊕ Fin r) k), (∀ i, MvPolynomial.aeval (Sum.elim y a) (g i) = 0) ∧ RingHom.ker (MvPolynomial.aeval (Sum.elim y a) : MvPolynomial (Fin s ⊕ Fin r) k →ₐ[k] A) ≤ Ideal.span (Set.range g) ⊔ RingHom.ker (ε.comp (MvPolynomial.aeval (Sum.elim y a) : MvPolynomial (Fin s ⊕ Fin r) k →ₐ[k] A)) * RingHom.ker (MvPolynomial.aeval (Sum.elim y a) : MvPolynomial (Fin s ⊕ Fin r) k →ₐ[k] A) := by
  first | exact @GlobalTheory.sqloc_present | exact GlobalTheory.sqloc_present | (intros; apply GlobalTheory.sqloc_present <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulPFlatStatement

section

@[expose] public section

open scoped TensorProduct

theorem _root_.GlobalTheory.T.mulP_flat' : ∀ (p : ℕ) (R : Type) [CommRing R] (G : GlobalTheory.PDivGroup p R) (n : ℕ), RingHom.Flat ((G.mulP n : G.A n →ₐ[R] G.A (n + 1)) : G.A n →+* G.A (n + 1)) := by
  intro p R _ G n
  obtain ⟨hassoc, hcounit, hsurj⟩ := G.transl_free n
  obtain ⟨-, -, hff, -⟩ :=
    GlobalTheory.HopfQuot.finite_faithfullyFlat_ker (G.transl n) hassoc hcounit hsurj
  let B := AlgHom.equalizer (G.transl n)
    (Algebra.TensorProduct.includeLeft : G.A (n + 1) →ₐ[R] G.A (n + 1) ⊗[R] G.A 1)
  let f : G.A n →ₐ[R] B := AlgHom.codRestrict
    (G.mulP n : G.A n →ₐ[R] G.A (n + 1)) B (fun a => G.transl_mulP n a)
  have hf : Function.Bijective f := by
    refine ⟨fun a b h => GlobalTheory.PDivGroup.Test.mulP_injective G n
      (congrArg Subtype.val h), fun y => ?_⟩
    obtain ⟨a, ha⟩ := G.exists_mulP_eq_of_transl_eq n y.1 y.2
    exact ⟨a, Subtype.ext ha⟩
  have hB : RingHom.Flat (algebraMap B (G.A (n + 1))) := by
    rw [RingHom.flat_algebraMap_iff]
    infer_instance
  have hflat : RingHom.Flat (f : G.A n →+* B) := RingHom.Flat.of_bijective hf
  convert RingHom.Flat.comp hflat hB using 1
  exact RingHom.ext fun a => rfl
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatCastSmulMemAugIdealSqSupMapMulPStatement

section

@[expose] public section

open scoped TensorProduct
open Coalgebra GlobalTheory.PDiv in

theorem _root_.GlobalTheory.T.natCast_smul_mem_augIdealSq_sup_map_mulP : ∀ (p : ℕ) (R : Type) [CommRing R] (G : GlobalTheory.PDivGroup p R) (n : ℕ), ∀ a ∈ RingHom.ker (Bialgebra.counitAlgHom R (G.A (n + 1))), (p : R) • a ∈ RingHom.ker (Bialgebra.counitAlgHom R (G.A (n + 1))) ^ 2 ⊔ (RingHom.ker (Bialgebra.counitAlgHom R (G.A n))).map ((G.mulP n : G.A n →ₐ[R] G.A (n + 1)) : G.A n →+* G.A (n + 1)) := by
  intro p R _ G n a ha
  have ha₀ : counit (R := R) a = 0 := ha
  have hres : G.res n a ∈ RingHom.ker (Bialgebra.counitAlgHom R (G.A n)) := by
    change counit (R := R) (G.res n a) = 0
    rw [CoalgHomClass.counit_comp_apply, ha₀]
  have hmap : mulBy R (G.A (n + 1)) p a ∈ (RingHom.ker (Bialgebra.counitAlgHom R (G.A n))).map
      ((G.mulP n : G.A n →ₐ[R] G.A (n + 1)) : G.A n →+* G.A (n + 1)) := by
    rw [← G.mulP_res n a]
    exact Ideal.mem_map_of_mem _ hres
  have hdiff : mulBy R (G.A (n + 1)) p a - (p : R) • a ∈
      RingHom.ker (Bialgebra.counitAlgHom R (G.A (n + 1))) ^ 2 := by
    have hd : dUnit (R := R) (mulBy R (G.A (n + 1)) p a - (p : R) • a) = 0 := by
      change GlobalTheory.AugCot.d (Bialgebra.counitAlgHom R (G.A (n + 1)))
        (mulBy R (G.A (n + 1)) p a - (p : R) • a) = 0
      rw [map_sub, map_smul]
      change dUnit (R := R) (mulBy R (G.A (n + 1)) p a) - (p : R) • dUnit (R := R) a = 0
      rw [← cotMap_d, cotMap_mulBy, sub_self]
    have h := (GlobalTheory.AugCot.d_eq_zero_iff _ _).1 hd
    have hc : Bialgebra.counitAlgHom R (G.A (n + 1))
        (mulBy R (G.A (n + 1)) p a - (p : R) • a) = 0 := by
      change counit (R := R) (mulBy R (G.A (n + 1)) p a - (p : R) • a) = 0
      rw [map_sub, map_smul, CoalgHomClass.counit_comp_apply, ha₀, smul_zero, sub_zero]
    rwa [hc, map_zero, sub_zero] at h
  have hsmul : (p : R) • a = mulBy R (G.A (n + 1)) p a - (mulBy R (G.A (n + 1)) p a - (p : R) • a) :=
    (sub_sub_cancel _ _).symm
  rw [hsmul]
  exact sub_mem (Ideal.mem_sup_right hmap) (Ideal.mem_sup_left hdiff)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupMulPUnitFibreEqLevelOneStatement

section

@[expose] public section

open scoped TensorProduct

theorem _root_.GlobalTheory.T.pDivGroup_mulP_unit_fiber_eq_level_one : ∀ (p : ℕ) (R k : Type) [CommRing R] [CommRing k] [Algebra R k], Function.Surjective (algebraMap R k) → ∀ (G : GlobalTheory.PDivGroup p R) (n : ℕ), Function.Surjective (fun a : G.A (n + 1) => ((1 : k) ⊗ₜ[R] G.resOne n a : k ⊗[R] G.A 1)) ∧ ∀ a : G.A (n + 1), ((1 : k) ⊗ₜ[R] G.resOne n a : k ⊗[R] G.A 1) = 0 ↔ a ∈ (RingHom.ker ((algebraMap R k).comp (Bialgebra.counitAlgHom R (G.A n) : G.A n →+* R))).map ((G.mulP n : G.A n →ₐ[R] G.A (n + 1)) : G.A n →+* G.A (n + 1)) := by
  exact @GlobalTheory.fibre_statement
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulPMemSqCounitKer

section

@[expose] public section

open scoped TensorProduct

theorem GlobalTheory.PDivGroup.mulP_mem_sq_counit : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsLocalRing O], (p : O) ≠ 0 → ¬IsUnit (p : O) → (∀ a : O, ∃ b : O, b ^ p = a) → ∀ (G : GlobalTheory.PDivGroup p O) (n : ℕ) (b : G.A n), G.mulP n b ∈ RingHom.ker (Bialgebra.counitAlgHom O (G.A (n + 1))) ^ 2 → b ∈ RingHom.ker (Bialgebra.counitAlgHom O (G.A n)) ^ 2 := by
  intro p hp O _ _ _ hp0 hpu hroot G n b hb

  have hpk : ((p : ℕ) : IsLocalRing.ResidueField O) = 0 := by
    rw [← map_natCast (IsLocalRing.residue O), IsLocalRing.residue_eq_zero_iff]
    exact (IsLocalRing.mem_maximalIdeal _).2 hpu
  haveI : CharP (IsLocalRing.ResidueField O) p := (CharP.charP_iff_prime_eq_zero hp.out).2 hpk
  haveI : ExpChar (IsLocalRing.ResidueField O) p := ExpChar.prime hp.out
  haveI : PerfectRing (IsLocalRing.ResidueField O) p :=
    PerfectRing.ofSurjective _ p (fun y => by
      obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective y
      obtain ⟨c, hc⟩ := hroot a
      exact ⟨IsLocalRing.residue O c, by rw [frobenius_def, ← map_pow, hc]⟩)

  letI : Algebra (G.A n) (G.A (n + 1)) :=
    ((G.mulP n : G.A n →ₐ[O] G.A (n + 1)) : G.A n →+* G.A (n + 1)).toAlgebra
  haveI : IsScalarTower O (G.A n) (G.A (n + 1)) :=
    IsScalarTower.of_algebraMap_eq fun c => ((G.mulP n : G.A n →ₐ[O] G.A (n + 1)).commutes c).symm
  haveI : Module.Flat (G.A n) (G.A (n + 1)) := GlobalTheory.T.mulP_flat' p O G n
  have hε : ∀ b : G.A n, Bialgebra.counitAlgHom O (G.A (n + 1)) (algebraMap (G.A n) (G.A (n + 1)) b) =
      Bialgebra.counitAlgHom O (G.A n) b := fun b => by
    rw [Bialgebra.counitAlgHom_apply, Bialgebra.counitAlgHom_apply]
    exact CoalgHomClass.counit_comp_apply (G.mulP n) b
  have hker : (RingHom.ker (Bialgebra.counitAlgHom O (G.A (n + 1)))).comap (algebraMap (G.A n) (G.A (n + 1))) =
      RingHom.ker (Bialgebra.counitAlgHom O (G.A n)) := by
    ext b
    rw [Ideal.mem_comap, RingHom.mem_ker, RingHom.mem_ker, hε]

  obtain ⟨ρ, hρ⟩ : ∃ ρ : G.A (n + 1) →+* IsLocalRing.ResidueField O ⊗[O] G.A 1,
      ∀ a, ρ a = 1 ⊗ₜ G.resOne n a :=
    ⟨(Algebra.TensorProduct.includeRight : G.A 1 →ₐ[O] IsLocalRing.ResidueField O ⊗[O] G.A 1).toRingHom.comp
      ((G.resOne n : G.A (n + 1) →ₐ[O] G.A 1) : G.A (n + 1) →+* G.A 1), fun _ => rfl⟩
  have hπs : Function.Surjective (algebraMap O (IsLocalRing.ResidueField O)) := by
    rw [IsLocalRing.ResidueField.algebraMap_eq]; exact IsLocalRing.residue_surjective
  have hπk : RingHom.ker (algebraMap O (IsLocalRing.ResidueField O)) = IsLocalRing.maximalIdeal O := by
    rw [IsLocalRing.ResidueField.algebraMap_eq, IsLocalRing.ker_residue]
  have hfib := GlobalTheory.T.pDivGroup_mulP_unit_fiber_eq_level_one p O (IsLocalRing.ResidueField O) hπs G n
  have hρs : Function.Surjective ρ := fun h => by
    obtain ⟨a, ha⟩ := hfib.1 h
    exact ⟨a, by rw [hρ]; exact ha⟩
  have hkerρ : RingHom.ker ρ = (RingHom.ker ((algebraMap O (IsLocalRing.ResidueField O)).comp
      ((Bialgebra.counitAlgHom O (G.A (n + 1)) : G.A (n + 1) →+* O).comp (algebraMap (G.A n) (G.A (n + 1)))))).map
      (algebraMap (G.A n) (G.A (n + 1))) := by
    have hcomp : (algebraMap O (IsLocalRing.ResidueField O)).comp
        ((Bialgebra.counitAlgHom O (G.A (n + 1)) : G.A (n + 1) →+* O).comp (algebraMap (G.A n) (G.A (n + 1)))) =
        (algebraMap O (IsLocalRing.ResidueField O)).comp (Bialgebra.counitAlgHom O (G.A n) : G.A n →+* O) :=
      RingHom.ext fun b => by
        simp only [RingHom.comp_apply, RingHom.coe_coe]
        rw [hε]
    rw [hcomp]
    ext a
    rw [RingHom.mem_ker, hρ]
    exact hfib.2 a
  have hρalg : ∀ c : O, ρ (algebraMap O (G.A (n + 1)) c) =
      algebraMap (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O ⊗[O] G.A 1)
        (algebraMap O (IsLocalRing.ResidueField O) c) := fun c => by
    rw [hρ, AlgHomClass.commutes, ← IsScalarTower.algebraMap_apply]
    exact (Algebra.TensorProduct.includeRight.commutes c)
  have hεH : ∀ a, Bialgebra.counitAlgHom (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O ⊗[O] G.A 1) (ρ a) =
      algebraMap O (IsLocalRing.ResidueField O) (Bialgebra.counitAlgHom O (G.A (n + 1)) a) := fun a => by
    rw [hρ, Bialgebra.counitAlgHom_apply, Bialgebra.counitAlgHom_apply, TensorProduct.counit_tmul,
      CoalgHomClass.counit_comp_apply, Algebra.smul_def, mul_comm]
    simp

  have hlaws : (∀ a : IsLocalRing.ResidueField O ⊗[O] G.A 1, TensorProduct.lid (IsLocalRing.ResidueField O) _
      (LinearMap.rTensor _ (Bialgebra.counitAlgHom (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O ⊗[O] G.A 1)).toLinearMap
        (Bialgebra.comulAlgHom (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O ⊗[O] G.A 1) a)) = a) ∧
      (∀ a : IsLocalRing.ResidueField O ⊗[O] G.A 1, TensorProduct.rid (IsLocalRing.ResidueField O) _
      (LinearMap.lTensor _ (Bialgebra.counitAlgHom (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O ⊗[O] G.A 1)).toLinearMap
        (Bialgebra.comulAlgHom (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O ⊗[O] G.A 1) a)) = a) := by
    constructor
    · intro a
      rw [Bialgebra.comulAlgHom_apply]
      erw [Coalgebra.rTensor_counit_comul]
      simp
    · intro a
      rw [Bialgebra.comulAlgHom_apply]
      erw [Coalgebra.lTensor_counit_comul]
      simp
  obtain ⟨e, he1, hei, ε', Δ', hlaws', hnil⟩ := GlobalTheory.T.localFactor_at_augmentation_counital_comul _ _ _ _ hlaws
  have hpres := GlobalTheory.T.exists_square_presentation_of_counit_isNilpotent_ker p _ _ ε' Δ' hlaws' hnil

  obtain ⟨r, f₀, hf₀⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1
    (inferInstance : Algebra.FiniteType O (G.A (n + 1)))
  have hfa : f₀ = MvPolynomial.aeval (fun i => f₀ (MvPolynomial.X i)) :=
    MvPolynomial.algHom_ext fun i => by rw [MvPolynomial.aeval_X]
  have hmap : ∀ {τ : Type} (x : τ → G.A (n + 1)) (q : MvPolynomial τ O),
      MvPolynomial.aeval (fun j => ρ (x j)) (MvPolynomial.map (algebraMap O (IsLocalRing.ResidueField O)) q) =
        ρ (MvPolynomial.aeval x q) := by
    intro τ x q
    rw [MvPolynomial.aeval_def, MvPolynomial.aeval_def, MvPolynomial.eval₂_map, MvPolynomial.eval₂_comp_left]
    congr 1
    exact RingHom.ext fun c => (hρalg c).symm
  have haH : Function.Surjective (MvPolynomial.aeval (fun i => ρ (f₀ (MvPolynomial.X i))) :
      MvPolynomial (Fin r) (IsLocalRing.ResidueField O) →ₐ[IsLocalRing.ResidueField O] _) := fun h => by
    obtain ⟨y, rfl⟩ := hρs h
    obtain ⟨q, rfl⟩ := hf₀ y
    exact ⟨_, (hmap (fun i => f₀ (MvPolynomial.X i)) q).trans (by rw [← hfa])⟩
  obtain ⟨s, y, g, hg0, hgker⟩ := GlobalTheory.T.exists_presentation_square_at_point_of_localFactor _ _ _ e he1 hei hpres r _ haH
  choose yt hyt using fun i => hρs (y i)
  obtain ⟨x, hxd⟩ : ∃ x : Fin s ⊕ Fin r → G.A (n + 1), x = Sum.elim yt (fun i => f₀ (MvPolynomial.X i)) := ⟨_, rfl⟩
  have hx : (fun j => ρ (x j)) = Sum.elim y (fun i => ρ (f₀ (MvPolynomial.X i))) := by
    funext j
    cases j <;> simp [hxd, hyt]
  have hxs : Function.Surjective (MvPolynomial.aeval x : MvPolynomial (Fin s ⊕ Fin r) (G.A n) →ₐ[G.A n] G.A (n + 1)) := by
    intro z
    obtain ⟨q, rfl⟩ := hf₀ z
    refine ⟨MvPolynomial.map (algebraMap O (G.A n)) (MvPolynomial.rename Sum.inr q), ?_⟩
    rw [MvPolynomial.aeval_map_algebraMap, MvPolynomial.aeval_rename, hfa, hxd]
    rfl
  haveI : Module.FinitePresentation O (G.A (n + 1)) := Module.finitePresentation_of_projective _ _
  haveI : Algebra.FinitePresentation O (G.A (n + 1)) := Algebra.FinitePresentation.of_finitePresentation _ _
  haveI : Algebra.FinitePresentation (G.A n) (G.A (n + 1)) :=
    Algebra.FinitePresentation.of_restrict_scalars_finitePresentation O _ _
  have hFG : (RingHom.ker (MvPolynomial.aeval x : MvPolynomial (Fin s ⊕ Fin r) (G.A n) →ₐ[G.A n] G.A (n + 1))).FG :=
    Algebra.FinitePresentation.ker_fG_of_surjective _ hxs
  obtain ⟨f, hf0, hfker⟩ := GlobalTheory.T.lift_square_presentation_of_flat_alt O (G.A n) (G.A (n + 1)) (IsLocalRing.ResidueField O) _ (Fin s ⊕ Fin r)
    (Bialgebra.counitAlgHom O (G.A (n + 1))) (algebraMap O (IsLocalRing.ResidueField O)) ρ
    (Bialgebra.counitAlgHom (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O ⊗[O] G.A 1)) x
    hπs hπk hρalg hεH hkerρ hxs hFG g (by rw [hx]; exact hg0) (by rw [hx]; exact hgker)
  have hpt : ∀ a ∈ RingHom.ker (Bialgebra.counitAlgHom O (G.A (n + 1))), (p : O) • a ∈
      RingHom.ker (Bialgebra.counitAlgHom O (G.A (n + 1))) ^ 2 ⊔
        ((RingHom.ker (Bialgebra.counitAlgHom O (G.A (n + 1)))).comap (algebraMap (G.A n) (G.A (n + 1)))).map
          (algebraMap (G.A n) (G.A (n + 1))) := by
    rw [hker]
    exact GlobalTheory.T.natCast_smul_mem_augIdealSq_sup_map_mulP p O G n
  have := GlobalTheory.T.cotangent_map_injective_of_square_presentation_at_point O (G.A n) (G.A (n + 1)) (Fin s ⊕ Fin r) (Bialgebra.counitAlgHom O (G.A (n + 1))) x f (p : O)
    hp0 hxs hf0 hfker hpt b hb
  rwa [hker] at this
end
end
