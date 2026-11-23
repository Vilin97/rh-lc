module

public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOfFinOrderFbar
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NotDvdDiscrIffRamificationIdx
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.LeOfFiniteSplitNotSplitBauer
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMulGaloisConjEqPrimeImagQuadraticStatement
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.NumberTheory.RamificationInertia.Inertia
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEqAlt
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TwDefs
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NcardPrimesOverOfStabilizer
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RayClassFieldSplitsInOfIsRayPrimeStatement
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.NormNum.Parity
import Formalism.ConjugateSelfDual.Statement
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.GaloisValuations.GlobalA
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSpanEqOneModOfSplitsInRayClassField

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.Mem.RaySplit

open GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem.Fld

theorem exists_span_eq_of_splits (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (𝔮 : Ideal (𝓞 K)) (hR : GlobalTheory.Mem.Fld.IsRayField K L 𝔮) (𝔭 : HeightOneSpectrum (𝓞 K)) (hnd : ¬ 𝔭.asIdeal ∣ 𝔮)
    (hs : (𝔭.asIdeal.primesOver (𝓞 L)).ncard = Module.finrank K L) :
    ∃ π : 𝓞 K, 𝔭.asIdeal = Ideal.span {π} ∧ π - 1 ∈ 𝔮 := by
  have := hR.1
  have := 𝔭.isPrime
  have := 𝔭.isMaximal
  have hcop : IsCoprime 𝔭.asIdeal 𝔮 := by
    rw [Ideal.isCoprime_iff_sup_eq]
    by_contra h
    exact hnd (Ideal.dvd_iff_le.2 (le_sup_right.trans (𝔭.isMaximal.eq_of_le h le_sup_left).symm.le))
  obtain ⟨σ, P, hP, hPo, hσ⟩ := exists_isFrob L 𝔭
  have hne : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot P
  have hPm : P.IsMaximal := hP.isMaximal hne
  have hef := (GlobalTheory.Bauer.ncard_eq_finrank_iff K L 𝔭).1 hs P ⟨hP, hPo⟩
  have hf : 𝔭.asIdeal.inertiaDeg' P = 1 := by
    rw [Ideal.inertiaDeg'_eq_inertiaDeg]
    exact Nat.eq_one_of_mul_eq_one_left hef
  have hN : Ideal.absNorm P = Ideal.absNorm 𝔭.asIdeal := by
    rw [Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver P 𝔭.asIdeal 𝔭.isPrime 𝔭.ne_bot, hf, pow_one]
  have : Finite (𝓞 L ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot _ hne
  letI := Ideal.Quotient.field P
  letI := Fintype.ofFinite (𝓞 L ⧸ P)
  have hpow : ∀ x : 𝓞 L, x ^ Ideal.absNorm 𝔭.asIdeal - x ∈ P := fun x => by
    rw [← Ideal.Quotient.eq, map_pow, ← hN, Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
    exact FiniteField.pow_card _
  have hin : InInertia L 𝔭 σ := ⟨P, hP, hPo, fun x => by
    have := add_mem (hσ x) (hpow x)
    rwa [sub_add_sub_cancel] at this⟩
  have hσ1 : σ = 1 := hR.2.1 𝔭 hnd σ hin
  have hχ : ∀ χ : (L ≃ₐ[K] L) →* ℂˣ, heckeIdeal L χ 𝔭.asIdeal = 1 := fun χ => by
    rw [heckeIdeal_asIdeal, heckeVal_of_unramIn L χ (hR.2.1 𝔭 hnd) ⟨P, hP, hPo, hσ⟩, hσ1, map_one, Units.val_one]
  obtain ⟨α, β, hab, he⟩ := (hR.2.2.2 𝔭.asIdeal 𝔭.ne_bot hcop).1 hχ
  have hα : α ∈ 𝔭.asIdeal * Ideal.span {β} := he ▸ Ideal.mem_span_singleton_self α
  obtain ⟨π, hπ, rfl⟩ := Ideal.mem_mul_span_singleton.1 hα
  have hβ0 : Ideal.span {β} ≠ (0 : Ideal (𝓞 K)) := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hab.2.1
  have hsp : 𝔭.asIdeal = Ideal.span {π} := by
    refine mul_right_cancel₀ hβ0 ?_
    rw [he, Ideal.span_singleton_mul_span_singleton]
  refine ⟨π, hsp, ?_⟩
  obtain ⟨i, hi, j, hj, hij⟩ := Ideal.isCoprime_iff_exists.1 hab.2.2.2.1
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hi
  have h1 : (π - 1) * β ∈ 𝔮 := by
    have := hab.2.2.2.2.1
    rwa [show π * β - β = (π - 1) * β by ring] at this
  have h2 : π - 1 = c * ((π - 1) * β) + (π - 1) * j := by
    linear_combination (π - 1) * hij.symm
  rw [h2]
  exact add_mem (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ hj)

end GlobalTheory.Mem.RaySplit
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSpanEqOneModOfSplitsInRayClassFieldStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial


theorem _root_.GlobalTheory.T.exists_span_eq_one_mod_of_splits_in_rayClassField : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (𝔮 : Ideal (𝓞 K)),
    GlobalTheory.Mem.Fld.IsRayField K L 𝔮 → ∀ 𝔭 : HeightOneSpectrum (𝓞 K), ¬ 𝔭.asIdeal ∣ 𝔮 →
      (𝔭.asIdeal.primesOver (𝓞 L)).ncard = Module.finrank K L →
        ∃ π : 𝓞 K, 𝔭.asIdeal = Ideal.span {π} ∧ π - 1 ∈ 𝔮 := by
  first | exact @GlobalTheory.Mem.RaySplit.exists_span_eq_of_splits | exact GlobalTheory.Mem.RaySplit.exists_span_eq_of_splits | (intros; apply GlobalTheory.Mem.RaySplit.exists_span_eq_of_splits <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitsCompletelyOverIntermediateOfSplitsOverRat

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.SplitTower

theorem splits_completely_of_intermediate :
    ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (p : ℕ), p.Prime →
    ((Ideal.span {(p : ℤ)}).primesOver (𝓞 L)).ncard = Module.finrank ℚ L →
      ∀ 𝔭 : HeightOneSpectrum (𝓞 K), (p : 𝓞 K) ∈ 𝔭.asIdeal → (𝔭.asIdeal.primesOver (𝓞 L)).ncard = Module.finrank K L := by
  intro K L _ _ _ _ _ p hp hcount 𝔭 hp𝔭
  rw [GlobalTheory.Bauer.ncard_eq_finrank_iff K L 𝔭]
  set P : Ideal ℤ := Ideal.span {(p : ℤ)} with hPdef
  have hPmax : P.IsMaximal := by
    exact PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
  haveI := hPmax
  haveI : Fintype (P.primesOver (𝓞 L)) := (IsDedekindDomain.primesOver_finite P (𝓞 L)).fintype
  have hsum := Ideal.sum_ramification_inertia_eq_finrank P (𝓞 L)
  rw [NumberField.RingOfIntegers.rank] at hsum
  have h1 : (P.primesOver (𝓞 L)).ncard = ∑ _q : P.primesOver (𝓞 L), 1 := by
    rw [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_univ, ← Nat.card_eq_fintype_card,
      Nat.card_coe_set_eq]
  have hall : ∀ Q ∈ P.primesOver (𝓞 L), Q.ramificationIdx ℤ * Q.inertiaDeg ℤ = 1 := by
    rw [← hsum, h1, Finset.sum_eq_sum_iff_of_le] at hcount
    · intro Q hQ
      exact (hcount ⟨Q, hQ⟩ (Finset.mem_univ _)).symm
    · rintro ⟨Q, hQ, _⟩ -
      exact Nat.mul_pos (Ideal.ramificationIdx_pos (R := _) Q) (Ideal.inertiaDeg_pos Q _)
  intro Q hQ
  obtain ⟨hQp, hQ𝔭⟩ := hQ
  haveI := 𝔭.isPrime
  haveI h𝔭P : 𝔭.asIdeal.LiesOver P := by
    refine ⟨hPmax.eq_of_le (Ideal.IsPrime.comap _).ne_top ?_⟩
    rw [hPdef, Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap]
    simpa using hp𝔭
  haveI : Q.LiesOver P := Ideal.LiesOver.trans Q 𝔭.asIdeal P
  have h := hall Q ⟨hQp, inferInstance⟩
  rw [Ideal.ramificationIdx_tower 𝔭.asIdeal Q, Ideal.inertiaDeg_tower 𝔭.asIdeal Q] at h
  refine Nat.eq_one_of_dvd_one ?_
  rw [← h]
  exact ⟨𝔭.asIdeal.ramificationIdx ℤ * 𝔭.asIdeal.inertiaDeg ℤ, by ring⟩

end GlobalTheory.SplitTower
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitsCompletelyOverIntermediateOfSplitsOverRatStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial


theorem _root_.GlobalTheory.T.splits_completely_over_intermediate_of_splits_over_rat : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (p : ℕ), p.Prime →
    ((Ideal.span {(p : ℤ)}).primesOver (𝓞 L)).ncard = Module.finrank ℚ L →
      ∀ 𝔭 : HeightOneSpectrum (𝓞 K), (p : 𝓞 K) ∈ 𝔭.asIdeal → (𝔭.asIdeal.primesOver (𝓞 L)).ncard = Module.finrank K L := by
  first | exact @GlobalTheory.SplitTower.splits_completely_of_intermediate | exact GlobalTheory.SplitTower.splits_completely_of_intermediate | (intros; apply GlobalTheory.SplitTower.splits_completely_of_intermediate <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RayClassFieldHostConductorIsRayClassField

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.ParRayMax

@[reducible] def algQb (D : D7) (jE : D.host.E →+* Qb) : Algebra D.host.K Qb :=
  (jE.comp (algebraMap D.host.K D.host.E)).toAlgebra

def toIF (D : D7) (jE : D.host.E →+* Qb) (L : Fld) (h : KQbar D jE ≤ L) :
    @IntermediateField D.host.K Qb _ _ (algQb D jE) :=
  letI := algQb D jE
  { L.toSubfield with algebraMap_mem' := fun x => h ⟨x.1, x.2, rfl⟩ }



theorem exists_embedded (hray : GlobalTheory.Published.RayClassFieldSt) (D : D7) (jE : D.host.E →+* Qb) :
    ∃ (M : Fld) (h : KQbar D jE ≤ M) (hf : FiniteDimensional ℚ M),
      letI := GlobalTheory.ParRay.algK D jE h
      haveI := GlobalTheory.ParRay.nfOf hf
      GlobalTheory.Mem.Fld.IsRayField D.host.K M (GlobalTheory.Mem.RaySplit.condIdeal D.host) := by
  obtain ⟨M, _, _, _, hM⟩ := GlobalTheory.Published.rayClassFieldSt_iff_isRayField.1 hray D.host.K _
    (GlobalTheory.Mem.RaySplit.condIdeal_ne_bot D.host)
  letI := algQb D jE
  let ψ : M →ₐ[D.host.K] Qb := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  let M1 : Fld := (ψ : M →+* Qb).toRatAlgHom.fieldRange
  have hψ : ∀ x : D.host.K, ψ (algebraMap D.host.K M x) = jE x := fun x => ψ.commutes x
  have hK : KQbar D jE ≤ M1 := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨algebraMap D.host.K M ⟨x, hx⟩, hψ ⟨x, hx⟩⟩
  let e₀ : M ≃ₐ[ℚ] M1 := AlgEquiv.ofInjectiveField (ψ : M →+* Qb).toRatAlgHom
  have hf : FiniteDimensional ℚ M1 := e₀.toLinearEquiv.finiteDimensional
  refine ⟨M1, hK, hf, ?_⟩
  letI := GlobalTheory.ParRay.algK D jE hK
  haveI := GlobalTheory.ParRay.nfOf hf
  exact hM.of_algEquiv (AlgEquiv.ofRingEquiv (f := e₀.toRingEquiv) fun x => Subtype.ext (hψ x))




theorem le_of_rayAdm (D : D7) (jE : D.host.E →+* Qb) (M : Fld) (h : KQbar D jE ≤ M) (hf : FiniteDimensional ℚ M)
    (hM : letI := GlobalTheory.ParRay.algK D jE h; haveI := GlobalTheory.ParRay.nfOf hf;
      GlobalTheory.Mem.Fld.IsRayField D.host.K M (GlobalTheory.Mem.RaySplit.condIdeal D.host))
    (L : Fld) (hL : RayAdm (KQbar D jE) (D.host.QS * D.host.q * D.host.d) L) : L ≤ M := by
  have h2K := GlobalTheory.Mem.RaySplit.finrank_K D.host
  have h3K := GlobalTheory.Mem.RaySplit.isEmpty_real D.host
  letI := GlobalTheory.ParRay.algK D jE h
  haveI := GlobalTheory.ParRay.nfOf hf
  letI := algQb D jE
  obtain ⟨hKL, hfL, hspl⟩ := hL
  let mkE : ∀ (X : Fld) (hX : KQbar D jE ≤ X), X ≃+* toIF D jE X hX := fun X hX =>
    { toFun := fun x => ⟨x.1, x.2⟩, invFun := fun x => ⟨x.1, x.2⟩, left_inv := fun _ => rfl,
      right_inv := fun _ => rfl, map_mul' := fun _ _ => rfl, map_add' := fun _ _ => rfl }
  let R := toIF D jE M h
  let L' := toIF D jE L hKL
  let eR : M ≃ₐ[D.host.K] R := AlgEquiv.ofRingEquiv (f := mkE M h) fun x => rfl
  let eL : L ≃+* L' := mkE L hKL
  haveI : NumberField R := { to_finiteDimensional := (eR.toRingEquiv.toRatAlgEquiv).toLinearEquiv.finiteDimensional }
  haveI : NumberField L' := { to_finiteDimensional := eL.toRatAlgEquiv.toLinearEquiv.finiteDimensional }
  have hR : GlobalTheory.Mem.Fld.IsRayField D.host.K R (GlobalTheory.Mem.RaySplit.condIdeal D.host) := hM.of_algEquiv eR
  have hab : IsAbelianGalois D.host.K R := hR.1
  have key : ∀ 𝔭 : HeightOneSpectrum (𝓞 D.host.K), ¬ 𝔭.asIdeal ∣ GlobalTheory.Mem.RaySplit.condIdeal D.host →
      (𝔭.asIdeal.primesOver (𝓞 R)).ncard = Module.finrank D.host.K R →
        ∃ π : 𝓞 D.host.K, 𝔭.asIdeal = Ideal.span {π} ∧ π - 1 ∈ GlobalTheory.Mem.RaySplit.condIdeal D.host :=
    fun 𝔭 h1 h2 => GlobalTheory.T.exists_span_eq_one_mod_of_splits_in_rayClassField D.host.K R _ hR 𝔭 h1 h2
  have hle : L' ≤ R := by
    refine @GlobalTheory.Bauer.le_of_finite_split_not_split D.host.K Qb _ _ _ _ R L' _ _ hab.toIsGalois
      ((Ideal.finite_factors (GlobalTheory.Mem.RaySplit.condIdeal_ne_bot D.host)).subset ?_)
    rintro 𝔭 ⟨hpr, hRs, hLs⟩
    by_contra hnd
    apply hLs
    rw [GlobalTheory.Bauer.ncard_eq_ncard_primesOver] at hRs ⊢
    obtain ⟨π, hπ, hπ1⟩ := key 𝔭 hnd hRs
    obtain ⟨σ, hσ⟩ := GlobalTheory.T.exists_mul_galois_conj_eq_prime_imagQuadratic D.host.K h3K h2K
      (jE.comp (algebraMap D.host.K D.host.E)) π (Ideal.absNorm 𝔭.asIdeal) (congrArg Ideal.absNorm hπ).symm
    have hray : IsRayPrime (KQbar D jE) (D.host.QS * D.host.q * D.host.d) (Ideal.absNorm 𝔭.asIdeal) := by
      refine ⟨hpr, jE ((π : D.host.K) : D.host.E), ⟨_, (π : D.host.K).2, rfl⟩, ?_, ?_, σ, hσ⟩
      · exact (RingOfIntegers.isIntegral_coe π).map (jE.comp (algebraMap D.host.K D.host.E)).toIntAlgHom
      · obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 hπ1
        have hm0 : ((D.host.QS * D.host.q * D.host.d : ℕ) : Qb) ≠ 0 := by
          exact_mod_cast GlobalTheory.Mem.RaySplit.cond_ne_zero D.host
        have e : (jE ((π : D.host.K) : D.host.E) - 1) / ((D.host.QS * D.host.q * D.host.d : ℕ) : Qb) =
            (jE.comp (algebraMap D.host.K D.host.E)) (y : D.host.K) := by
          rw [div_eq_iff hm0]
          have e1 := congrArg ((jE.comp (algebraMap D.host.K D.host.E)).comp (algebraMap (𝓞 D.host.K) D.host.K)) hy
          simp only [map_mul, map_sub, map_one, map_natCast] at e1
          exact e1.symm
        rw [e]
        exact (RingOfIntegers.isIntegral_coe y).map (jE.comp (algebraMap D.host.K D.host.E)).toIntAlgHom
    have hsp := hspl _ hray
    have h1 : ((Ideal.span {((Ideal.absNorm 𝔭.asIdeal : ℕ) : ℤ)}).primesOver (𝓞 L')).ncard = Module.finrank ℚ L' := by
      rw [← GlobalTheory.HostSplit.ncard_placesOver L' hpr, ← finrank_eq_of_equiv eL]
      exact (ncard_places_of_equiv eL _).symm.trans hsp
    exact GlobalTheory.T.splits_completely_over_intermediate_of_splits_over_rat D.host.K L' _ hpr h1 𝔭 (Ideal.absNorm_mem 𝔭.asIdeal)
  exact fun x hx => hle hx

theorem rayField_isRay : GlobalTheory.Published.RayClassFieldSt → ∀ (D : D7) (jE : D.host.E →+* Qb),
    ∃ (h : KQbar D jE ≤ MrayC D jE) (hf : FiniteDimensional ℚ (MrayC D jE)),
      letI := GlobalTheory.ParRay.algK D jE h
      haveI := GlobalTheory.ParRay.nfOf hf
      IsGalois D.host.K (MrayC D jE) ∧ (∀ σ τ : MrayC D jE ≃ₐ[D.host.K] MrayC D jE, σ * τ = τ * σ) ∧
      (∀ p : ℕ, p.Prime → (p : ℤ) ∣ NumberField.discr (MrayC D jE) → p ∣ D.host.QS * D.host.q * D.host.d) ∧
      ∀ p, IsRayPrime (KQbar D jE) (D.host.QS * D.host.q * D.host.d) p → SplitsIn (MrayC D jE) p := by
  intro hray D jE
  obtain ⟨M, h, hf, hM⟩ := exists_embedded hray D jE
  have hsplit := GlobalTheory.T.rayClassField_splitsIn_of_isRayPrime D jE M h hf hM
  have heq : MrayC D jE = M :=
    le_antisymm (iSup₂_le fun L hL => le_of_rayAdm D jE M h hf hM L hL) (le_rayField ⟨h, hf, hsplit⟩)
  generalize MrayC D jE = X at heq ⊢
  subst heq
  refine ⟨h, hf, ?_⟩
  letI := GlobalTheory.ParRay.algK D jE h
  haveI := GlobalTheory.ParRay.nfOf hf
  exact ⟨GlobalTheory.Mem.RaySplit.isGalois_of_ray hM, GlobalTheory.Mem.RaySplit.comm_of_ray hM, GlobalTheory.Mem.RaySplit.unr_of_ray hM, hsplit⟩

end GlobalTheory.ParRayMax

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RayClassFieldHostConductorIsRayClassFieldStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

theorem _root_.GlobalTheory.T.rayClassFieldHostConductor_isRayClassField : GlobalTheory.Published.RayClassFieldSt → ∀ (D : D7) (jE : D.host.E →+* Qb),
    ∃ (h : KQbar D jE ≤ MrayC D jE) (hf : FiniteDimensional ℚ (MrayC D jE)),
      letI := GlobalTheory.ParRay.algK D jE h
      haveI := GlobalTheory.ParRay.nfOf hf
      IsGalois D.host.K (MrayC D jE) ∧ (∀ σ τ : MrayC D jE ≃ₐ[D.host.K] MrayC D jE, σ * τ = τ * σ) ∧
      (∀ p : ℕ, p.Prime → (p : ℤ) ∣ NumberField.discr (MrayC D jE) → p ∣ D.host.QS * D.host.q * D.host.d) ∧
      ∀ p, IsRayPrime (KQbar D jE) (D.host.QS * D.host.q * D.host.d) p → SplitsIn (MrayC D jE) p := by
  first | exact @GlobalTheory.ParRayMax.rayField_isRay | exact GlobalTheory.ParRayMax.rayField_isRay | (intros; apply GlobalTheory.ParRayMax.rayField_isRay <;> assumption)
end
end
