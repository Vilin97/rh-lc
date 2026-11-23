module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRetractionMulP
public import Development.AbelianVarietyTheory.Definitions.Divisors.FibreRankCompOfSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubsingletonOfResidueFieldFibres
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Linter.HaveILetI
import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMulPowFibreRankEqPDivGroup

section

@[expose] public section

open CategoryTheory Coalgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.HTPair
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.PDivGroup

theorem exists_mulPow_fibreRank_eq (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O]
    (G : _root_.GlobalTheory.PDivGroup p O) (k m : ℕ) :
    ∃ (r : G.A (k + m) →ₐc[O] G.A k) (μ : G.A k →ₐc[O] G.A (k + m)), Function.Surjective r ∧
      RingHom.ker r = torsionIdeal (R := O) (A := G.A (k + m)) (p ^ k) ∧
      (∀ a, μ (r a) = mulBy (R := O) (A := G.A (k + m)) (p ^ m) a) ∧
      ∀ q, fibreRank (μ : G.A k →ₐ[O] G.A (k + m)).toLinearMap q = fibreDim (G.A k) q := by
  obtain ⟨r, hr, hk⟩ := G.exists_res_le (m := k) (n := k + m) (by omega)
  have hle : RingHom.ker r ≤ RingHom.ker (mulBy (R := O) (A := G.A (k + m)) (p ^ m)) := by
    rw [hk]
    refine (kerIdeal_le_ker_iff _
      (mulBy (R := O) (A := G.A (k + m)) (p ^ m) : G.A (k + m) →ₐ[O] G.A (k + m))).2 fun c => ?_
    change mulBy (R := O) (A := G.A (k + m)) (p ^ m)
      (mulBy (R := O) (A := G.A (k + m)) (p ^ k) c) = _
    rw [mulBy_mulBy, ← pow_add, add_comm m k, mulBy_pow_self]
  let μ := liftSurj r hr (mulBy (R := O) (A := G.A (k + m)) (p ^ m)) hle
  have hμ : ∀ a, μ (r a) = mulBy (R := O) (A := G.A (k + m)) (p ^ m) a :=
    liftSurj_apply r hr _ hle
  refine ⟨r, μ, hr, hk, hμ, fun q => ?_⟩
  obtain ⟨f, hf, hfk⟩ := G.exists_res_le (m := m) (n := k + m) (by omega)
  have hker : kerIdeal μ = RingHom.ker (f : G.A (k + m) →ₐ[O] G.A m) := by
    rw [← kerIdeal_comp_of_surjective μ hr, show μ.comp r =
      mulBy (R := O) (A := G.A (k + m)) (p ^ m) from BialgHom.ext hμ]
    exact hfk.symm
  have h1 := fibreDim_eq_ker_mul_range μ q
  rw [hker, fibreDim_congr (Ideal.quotientKerAlgEquivOfSurjective
    (f := (f : G.A (k + m) →ₐ[O] G.A m)) hf).toLinearEquiv, fibreDim_eq, fibreDim_eq,
    add_mul, pow_add, mul_comm (p ^ (k * G.height))] at h1
  rw [fibreDim_eq]
  have hp : 0 < p ^ (m * G.height) := pow_pos (Fact.out : p.Prime).pos _
  exact (Nat.eq_of_mul_eq_mul_left hp h1).symm

end GlobalTheory.PDivGroup
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearMapFibreRankSplitCompSurjective

section

@[expose] public section

open CategoryTheory Coalgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.HTPair
open scoped TensorProduct

namespace GlobalTheory.FibreRanks

theorem fibre_ranks : ∀ (O : Type) [CommRing O] (M : Type) [AddCommGroup M] [Module O M] (N : Type) [AddCommGroup N] [Module O N] (K : Type) [AddCommGroup K] [Module O K] [Module.Finite O M] [Module.Finite O N] (f : M →ₗ[O] N), (∀ (ρ : N →ₗ[O] M), (∀ m, ρ (f m) = m) → ∀ q, fibreRank f q = fibreDim M q) ∧ (∀ (g : N →ₗ[O] K) (q : PrimeSpectrum O), fibreRank g q = fibreDim N q → fibreRank (g ∘ₗ f) q = fibreRank f q) ∧ ((∀ q, fibreRank f q = fibreDim N q) → Function.Surjective f) ∧ (∀ [Module.Free O M] (q : PrimeSpectrum O), fibreDim M q = Module.finrank O M) := by
  intro O _ M _ _ N _ _ K _ _ _ _ f
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ρ hρ q
    have hinj : Function.Injective (f.baseChange q.asIdeal.ResidueField) := by
      apply Function.LeftInverse.injective (g := ρ.baseChange q.asIdeal.ResidueField)
      intro x
      rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp]
      have : ρ ∘ₗ f = LinearMap.id := LinearMap.ext hρ
      rw [this]
      simp
    exact LinearMap.finrank_range_of_inj hinj
  · intro g q hg
    have hker := LinearMap.finrank_range_add_finrank_ker (g.baseChange q.asIdeal.ResidueField)
    have h0 : Module.finrank q.asIdeal.ResidueField
        (LinearMap.ker (g.baseChange q.asIdeal.ResidueField)) = 0 := by
      unfold fibreRank fibreDim at hg
      omega
    have hinj : Function.Injective (g.baseChange q.asIdeal.ResidueField) := by
      rw [← LinearMap.ker_eq_bot]
      exact Submodule.finrank_eq_zero.mp h0
    unfold fibreRank
    rw [LinearMap.baseChange_comp, LinearMap.range_comp]
    exact (Submodule.equivMapOfInjective _ hinj _).finrank_eq.symm
  · intro h
    exact surjective_of_fibre_rank O M N f h
  · intro _ q
    haveI : Nontrivial O := by
      by_contra hn
      rw [not_nontrivial_iff_subsingleton] at hn
      exact q.isPrime.ne_top (Subsingleton.elim _ _)
    exact Module.finrank_baseChange

end GlobalTheory.FibreRanks
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFibreDimQuotientPDivGroupLevelStatement

section

@[expose] public section

open CategoryTheory Coalgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.HTPair
open scoped TensorProduct

theorem _root_.GlobalTheory.T.torsion_fibreDim_quotient_pDivGroupLevel :
    ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] (G : PDivGroup p O) (k m : ℕ),
      1 ≤ k → ∀ (B : Type) [CommRing B] [HopfAlgebra O B] [IsCocomm O B] [Module.Finite O B]
        [Module.Projective O B] (j : B →ₐc[O] G.A (k + m)) (ρ : G.A (k + m) →ₗ[O] B),
        (∀ b, ρ (j b) = b) → torsionIdeal (R := O) (A := G.A (k + m)) p ≤ kerIdeal j →
        ∀ q : PrimeSpectrum O,
          fibreDim (B ⧸ torsionIdeal (R := O) (A := B) (p ^ m)) q = p ^ (m * G.height) := by
  intro p _ O _ G k m hk B _ _ _ _ _ j ρ hρ hj q
  obtain ⟨r, μ, hr, hker, hμ, hμq⟩ := G.exists_mulPow_fibreRank_eq p O k m
  let jₗ := (j : B →ₐ[O] G.A (k + m)).toLinearMap
  let rjₗ := ((r.comp j) : B →ₐ[O] G.A k).toLinearMap
  let μₗ := (μ : G.A k →ₐ[O] G.A (k + m)).toLinearMap
  let mul := mulBy (R := O) (A := B) (p ^ m)
  let mulₗ := (mul : B →ₐ[O] B).toLinearMap
  have hjq : fibreRank jₗ q = fibreDim B q :=
    (FibreRanks.fibre_ranks O B (G.A (k + m)) (G.A (k + m)) jₗ).1 ρ hρ q
  have hlevel := fibreDim_eq_ker_mul_range j q
  rw [show fibreRank (j : B →ₐ[O] G.A (k + m)).toLinearMap q = _ from hjq, G.fibreDim_eq]
    at hlevel
  have hres := fibreDim_eq_ker_mul_range (r.comp j) q
  rw [G.fibreDim_eq] at hres
  have hle : RingHom.ker r ≤ kerIdeal j := by
    rw [hker]
    exact (torsionIdeal_le_of_dvd (dvd_pow_self p (by omega : k ≠ 0))).trans hj
  let J := kerIdeal (r.comp j)
  let φ : G.A (k + m) →ₐ[O] G.A k ⧸ J := (Ideal.Quotient.mkₐ O J).comp r
  have hφ : Function.Surjective φ := (Ideal.Quotient.mkₐ_surjective O J).comp hr
  have hkerφ : RingHom.ker φ = kerIdeal j := by
    have hcomap : RingHom.ker φ = J.comap (r : G.A (k + m) →ₐ[O] G.A k) := by
      ext a
      simp [φ, RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]
    rw [hcomap, show J = Ideal.map (r : G.A (k + m) →ₐ[O] G.A k) (kerIdeal j) from
      kerIdeal_comp r j, Ideal.comap_map_of_surjective (r : G.A (k + m) →ₐ[O] G.A k) hr,
      sup_eq_left]
    exact hle
  let e : (G.A (k + m) ⧸ kerIdeal j) ≃ₗ[O] (G.A k ⧸ J) :=
    ((Ideal.quotientEquivAlgOfEq O hkerφ).symm.trans
      (Ideal.quotientKerAlgEquivOfSurjective hφ)).toLinearEquiv
  rw [← fibreDim_congr e q] at hres
  have hmul := fibreDim_eq_ker_mul_range mul q
  have hlin : jₗ ∘ₗ mulₗ = μₗ ∘ₗ rjₗ := by
    ext b
    change j (mulBy (R := O) (A := B) (p ^ m) b) = μ (r (j b))
    rw [map_mulBy, hμ]
  have hrank : fibreRank mulₗ q = fibreRank rjₗ q := by
    rw [← (FibreRanks.fibre_ranks O B B (G.A (k + m)) mulₗ).2.1 jₗ q hjq, hlin,
      (FibreRanks.fibre_ranks O B (G.A k) (G.A (k + m)) rjₗ).2.1 μₗ q (hμq q)]
  change fibreDim B q = fibreDim (B ⧸ kerIdeal mul) q * fibreRank mulₗ q at hmul
  rw [hrank] at hmul
  change fibreDim (B ⧸ kerIdeal mul) q = _
  have hp : 0 < p ^ (k * G.height) := pow_pos (Fact.out : p.Prime).pos _
  have hpow : p ^ ((k + m) * G.height) = p ^ (m * G.height) * p ^ (k * G.height) := by
    rw [Nat.add_mul, pow_add, mul_comm]
  refine (Nat.eq_of_mul_eq_mul_right hp ?_).symm
  rw [← hpow, hlevel, hmul, hres]
  ring
end
end
