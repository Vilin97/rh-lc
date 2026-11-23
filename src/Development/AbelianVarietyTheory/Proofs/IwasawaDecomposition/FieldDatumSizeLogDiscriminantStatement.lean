module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
import Mathlib.Tactic
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ClassNumberLeAbsDiscrOfFinrankEqTwo
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SmulCommClassGalIntegers
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
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
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsImagQuadraticHost
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LFunctionPositiveConductorFourEight
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.NormComparisonConstants
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjugateEmbApply
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.HeckeIdealEqOfRay
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.LogRootDiscrLeOfNatCastMemDifferentIdeal
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.NatCastMulFinrankMemDifferentIdeal
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.WeberSetSubsetRayField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DiscFieldEqTorsionField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DvdDiscrTorsionField
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.InFibreLoc
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.RingTheory.Ideal.Prime
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTorsionParamLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnramInIffDifferentIdealEqTop
import Formalism.LocalRingCardinality.ConjSqrtMinusD
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat

-- Source module: Development.AbelianVarietyTheory.Proofs.HeightProofs.AbelianUnramIn

section

@[expose] public section

set_option autoImplicit false

open NumberField IsDedekindDomain GlobalTheory.FieldSize

namespace GlobalTheory.FieldSize.WeberUnram


set_option autoImplicit false in
open NumberField IsDedekindDomain in
theorem _root_.GlobalTheory.FieldSize.WeberUnram.of_algHom {K M R : Type} [Field K] [NumberField K]
    [Field M] [Algebra K M] [Field R] [NumberField R]
    [Algebra K R] [IsAbelianGalois K R] (f : M →ₐ[K] R) :
    ∃ (_ : NumberField M) (_ : IsAbelianGalois K M),
      ∀ 𝔭 : HeightOneSpectrum (𝓞 K), _root_.GlobalTheory.NT.UnramIn R 𝔭 →
        _root_.GlobalTheory.NT.UnramIn M 𝔭 := by
  have hab : IsAbelianGalois K M := IsAbelianGalois.of_algHom f
  letI : Algebra M R := f.toRingHom.toAlgebra
  haveI : IsScalarTower K M R := IsScalarTower.of_algebraMap_eq (fun x => (f.commutes x).symm)
  haveI : CharZero M := charZero_of_injective_algebraMap (algebraMap K M).injective
  haveI : FiniteDimensional K M := FiniteDimensional.left K M R
  haveI : FiniteDimensional ℚ M := Module.Finite.trans K M
  haveI nf : NumberField M := ⟨⟩
  exact ⟨nf, hab, fun 𝔭 h => _root_.GlobalTheory.RayMaximal.unramIn_of_tower (L := M) (M := R) h⟩

end GlobalTheory.FieldSize.WeberUnram
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsIsRayIntermediateField

section

@[expose] public section

set_option autoImplicit false

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory.Mem GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.FieldSize
open scoped IntermediateField

namespace GlobalTheory.FieldSize.SmallField

theorem exists_isRay_intermediateField (hR : GlobalTheory.NT.RayField) (K : IntermediateField ℚ ℂ) [NumberField K]
    (𝔮 : Ideal (𝓞 K)) (h𝔮 : 𝔮 ≠ ⊥) :
    ∃ (R : IntermediateField K ℂ) (_ : NumberField R) (_ : IsAbelianGalois K R), IsRay R 𝔮 := by
  obtain ⟨M, _, _, _, hM⟩ := GlobalTheory.Mem.Fld.rayField_iff.1 hR K 𝔮 h𝔮
  have := hM.1
  let f : M →ₐ[K] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  let e : M ≃ₐ[K] f.fieldRange := AlgEquiv.ofInjectiveField f
  have : FiniteDimensional K f.fieldRange := e.toLinearEquiv.finiteDimensional
  have : NumberField f.fieldRange := NumberField.of_module_finite K f.fieldRange
  have h := hM.of_algEquiv e
  exact ⟨f.fieldRange, inferInstance, h.1, h.2⟩

end GlobalTheory.FieldSize.SmallField

namespace GlobalTheory.FieldSize

open SmallField GlobalTheory.Mem.BaseExt

end GlobalTheory.FieldSize
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPrimeDvdNatCastMem

section

@[expose] public section

namespace GlobalTheory.PrimeDvdNatCastMem

theorem exists_prime_dvd_natCast_mem {O : Type} [CommRing O] (P : Ideal O) [hP : Ideal.IsPrime P]
    (m : ℕ) : m ≠ (0 : ℕ) → (↑m : O) ∈ P → ∃ (p : ℕ), Nat.Prime p ∧ p ∣ m ∧ (↑p : O) ∈ P := by
  apply LevelTowerAlt.LocalPrimeBound.exists_prime_mem <;> assumption

end GlobalTheory.PrimeDvdNatCastMem
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FieldDatumSizeLogDiscriminant

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host GlobalTheory.NT GlobalTheory.Mem GlobalTheory.Mem.Fld GlobalTheory.FieldSize
open scoped IntermediateField

namespace GlobalTheory.Mem.Fld.TorsionSize

theorem exists_prime_dvd_mem {O : Type} [CommRing O] (P : Ideal O) [hP : P.IsPrime] (m : ℕ) :
    m ≠ 0 → (m : O) ∈ P → ∃ p : ℕ, p.Prime ∧ p ∣ m ∧ (p : O) ∈ P := by
  first
  | exact @_root_.GlobalTheory.PrimeDvdNatCastMem.exists_prime_dvd_natCast_mem
  | exact _root_.GlobalTheory.PrimeDvdNatCastMem.exists_prime_dvd_natCast_mem
  | (apply _root_.GlobalTheory.PrimeDvdNatCastMem.exists_prime_dvd_natCast_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.PrimeDvdNatCastMem.exists_prime_dvd_natCast_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PrimeDvdNatCastMem.exists_prime_dvd_natCast_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PrimeDvdNatCastMem.exists_prime_dvd_natCast_mem ..)

theorem unramIn_of_discr (H M : Type) [Field H] [NumberField H] [Field M] [NumberField M]
    [Algebra H M] [IsGalois H M] (n : ℕ)
    (h : ∀ p : ℕ, p.Prime → p ∣ (discr M).natAbs → p ∣ n)
    (𝔭 : HeightOneSpectrum (𝓞 H)) (hn : (n : 𝓞 H) ∉ 𝔭.asIdeal) : UnramIn M 𝔭 := by
  rintro σ ⟨P, hP, hPo, hσ⟩
  have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot P
  have hnd : ¬ P ∣ differentIdeal (𝓞 H) (𝓞 M) := by
    intro hd
    have h1 : Ideal.absNorm P ∣ (discr M).natAbs := by
      rw [natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow H (𝓞 H) M (𝓞 M)]
      exact (map_dvd Ideal.absNorm hd).mul_right _
    obtain ⟨p, hp, hpd, hpP⟩ := exists_prime_dvd_mem P (Ideal.absNorm P)
      (by rwa [Ne, Ideal.absNorm_eq_zero_iff]) (Ideal.absNorm_mem P)
    obtain ⟨k, hk⟩ := h p hp (hpd.trans h1)
    apply hn
    rw [hPo.over, Ideal.mem_comap, map_natCast, hk, Nat.cast_mul]
    exact P.mul_mem_right _ hpP
  have hI := (GlobalTheory.UnramDiscr.not_dvd_iff_inertia H M P hP0).1 hnd
  have : σ ∈ Ideal.inertia Gal(M/H) P := fun x => hσ x
  rw [hI] at this
  exact Subgroup.mem_bot.1 this

theorem log_rootDiscr_le (K H M : Type) [Field K] [NumberField K] [Field H] [NumberField H]
    [Field M] [NumberField M] [Algebra K H] [Algebra H M] [IsGalois K H] [IsGalois H M] (d : ℕ)
    (hd : 0 < d) (hK : Module.finrank ℚ K = 2) (hdK : (discr K).natAbs = d)
    (hu : ∀ 𝔭 : HeightOneSpectrum (𝓞 K), UnramIn H 𝔭)
    (h : ∀ p : ℕ, p.Prime → p ∣ (discr M).natAbs → p ∣ 6 * d ∨ p ∣ (discr H).natAbs) :
    Real.log |((discr M : ℤ) : ℝ)| / Module.finrank ℚ M ≤
      Real.log d / 2 + Real.log ((6 * d * Module.finrank H M : ℕ) : ℝ) := by
  have hH := (GlobalTheory.UnramDiscr.unramIn_iff_natAbs_discr K H).1 hu
  rw [hdK] at hH
  have h' : ∀ p : ℕ, p.Prime → p ∣ (discr M).natAbs → p ∣ 6 * d := by
    intro p hp hpd
    rcases h p hp hpd with h1 | h1
    · exact h1
    · rw [hH] at h1
      exact (hp.dvd_of_dvd_pow h1).mul_left 6
  have h1 := GlobalTheory.DifferentBound.natCast_mul_finrank_mem_differentIdeal H M (6 * d) (by omega)
    (unramIn_of_discr H M (6 * d) h')
  have h2 := GlobalTheory.log_rootDiscr_le_of_natCast_mem_differentIdeal H M _
    (Nat.mul_pos (by omega) Module.finrank_pos) h1
  refine h2.trans (add_le_add_left (le_of_eq ?_) _)
  have h3 : |((discr H : ℤ) : ℝ)| = (d : ℝ) ^ Module.finrank K H := by
    rw [← Int.cast_abs, ← Int.natCast_natAbs, hH]; push_cast; rfl
  have h4 : (Module.finrank K H : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  rw [h3, Real.log_pow, ← Module.finrank_mul_finrank ℚ K H, hK]
  push_cast
  field_simp

theorem exists_algHom_ray (hR : RayField) (K : IntermediateField ℚ ℂ) [NumberField K]
    [_root_.NumberField.IsTotallyComplex K] (hK : Module.finrank ℚ K = 2) (hd : discr K < -4) (L : PeriodPair)
    (hL : ∀ z : ℂ, z ∈ L.lattice ↔ ∃ a : 𝓞 K, ((a : K) : ℂ) = z) (H : IntermediateField ℚ ℂ)
    (hH : H = K ⊔ ℚ⟮(GlobalTheory.latticeCurve L).j⟯) [Algebra K H]
    (hKH : ∀ x : K, ((algebraMap K H x : H) : ℂ) = x) (n : ℕ) (ho : Odd n) (h3 : 3 ≤ n) :
    ∃ (R : IntermediateField K ℂ) (_ : NumberField R) (_ : IsAbelianGalois K R),
      IsRay R (Ideal.span {(n : 𝓞 K)}) ∧ Nonempty (H →ₐ[K] R) := by
  have hn : Ideal.span {(n : 𝓞 K)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact Nat.cast_ne_zero.2 (by omega)
  obtain ⟨R, _, _, hRay⟩ := SmallField.exists_isRay_intermediateField hR K _ hn
  have hsub := InRay.weberSet_subset K hK hd L hL n ho h3 R hRay
  have hle : H ≤ R.restrictScalars ℚ := by
    rw [hH]
    refine sup_le (fun x hx => R.algebraMap_mem (⟨x, hx⟩ : K)) ?_
    rw [IntermediateField.adjoin_simple_le_iff, GlobalTheory.Published.latticeCurve_j_eq, mul_div_assoc]
    exact mul_mem (ofNat_mem _ 1728) (hsub (Set.mem_insert _ _))
  exact ⟨R, inferInstance, inferInstance, hRay,
    ⟨{ toRingHom := (IntermediateField.inclusion hle).toRingHom
       commutes' := fun x => Subtype.ext (hKH x) }⟩⟩

theorem invariantField (hR : RayField) (K : IntermediateField ℚ ℂ) [NumberField K]
    [_root_.NumberField.IsTotallyComplex K] (hK : Module.finrank ℚ K = 2) (hd : discr K < -4) (L : PeriodPair)
    (hL : ∀ z : ℂ, z ∈ L.lattice ↔ ∃ a : 𝓞 K, ((a : K) : ℂ) = z) (H : IntermediateField ℚ ℂ)
    (hH : H = K ⊔ ℚ⟮(GlobalTheory.latticeCurve L).j⟯) [Algebra K H]
    (hKH : ∀ x : K, ((algebraMap K H x : H) : ℂ) = x) :
    ∃ (_ : NumberField H) (_ : IsGalois K H), (∀ 𝔭 : HeightOneSpectrum (𝓞 K), UnramIn H 𝔭) ∧
      Module.finrank K H ≤ 9 * (discr K).natAbs := by
  obtain ⟨R, _, _, hRay, ⟨f⟩⟩ := exists_algHom_ray hR K hK hd L hL H hH hKH 3 (by decide) le_rfl
  obtain ⟨S, _, _, hSay, ⟨g⟩⟩ :=
    exists_algHom_ray hR K hK hd L hL H hH hKH 5 (by decide) (by norm_num)
  obtain ⟨hN, hA, hf⟩ := WeberUnram.of_algHom f
  obtain ⟨-, -, hg⟩ := WeberUnram.of_algHom g
  refine ⟨hN, inferInstance, fun 𝔭 => ?_, ?_⟩
  · by_cases h : 𝔭.asIdeal ∣ Ideal.span {((3 : ℕ) : 𝓞 K)}
    · refine hg 𝔭 (hSay.1 𝔭 fun h' => 𝔭.isPrime.ne_top ?_)
      rw [Ideal.dvd_span_singleton] at h h'
      rw [Ideal.eq_top_iff_one]
      have := sub_mem (𝔭.asIdeal.mul_mem_left 2 h) h'
      convert this using 1
      norm_num
    · exact hf 𝔭 (hRay.1 𝔭 h)
  · have hn : Ideal.span {((3 : ℕ) : 𝓞 K)} ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]
      exact Nat.cast_ne_zero.2 (by omega)
    have h1 := RayDegree.finrank_le K R _ hn hRay
    have he : IsEmpty (K →+* ℝ) := ⟨fun φ => by
      refine IsTotallyComplex.complexEmbedding_not_isReal (Complex.ofRealHom.comp φ) ?_
      rw [ComplexEmbedding.isReal_iff]
      ext x
      simp⟩
    rw [Fintype.card_eq_zero, Ideal.absNorm_span_natCast, RingOfIntegers.rank, hK] at h1
    have h2 : Module.finrank K H ≤ Module.finrank K R :=
      LinearMap.finrank_le_finrank_of_injective (f := f.toLinearMap) f.toRingHom.injective
    have h3 := GlobalTheory.classNumber_le_abs_discr_of_finrank_eq_two K hK
    have h4 : classNumber K ≤ (discr K).natAbs := by
      rw [← Int.cast_abs, ← Int.natCast_natAbs] at h3
      exact_mod_cast h3
    omega

theorem isGalois_torsion (F H M : IntermediateField ℚ ℂ) [NumberField F] [NumberField H]
    [NumberField M] (A : WeierstrassCurve F) (hFH : F ≤ H) (hHM : H ≤ M)
    (hM : M = H ⊔ IntermediateField.adjoin ℚ (torsionCoords (A.baseChange ℂ) 12)) :
    letI : Algebra H M := (IntermediateField.inclusion hHM).toAlgebra
    IsGalois H M := by
  letI : Algebra H M := (IntermediateField.inclusion hHM).toAlgebra
  letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
  letI : Algebra F M := (IntermediateField.inclusion (hFH.trans hHM)).toAlgebra
  haveI : IsScalarTower F H M := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower F M ℂ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower H M ℂ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower F H ℂ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  refine TorsionRam.isGalois A (fun z hz => ⟨⟨z, ?_⟩, rfl⟩) fun T h1 h2 z => ?_
  · rw [hM]
    exact (le_sup_right : _ ≤ H ⊔ _) (IntermediateField.subset_adjoin ℚ _ hz)
  · let T' : IntermediateField ℚ ℂ := (T.map (algebraMap M ℂ)).toIntermediateField
      fun q => by simp
    have hT : M ≤ T' := by
      refine hM.le.trans (sup_le (fun x hx => ⟨_, h1 ⟨x, hx⟩, rfl⟩) ?_)
      rw [IntermediateField.adjoin_le_iff]
      intro x hx
      have hxM : x ∈ M := by
        rw [hM]
        exact (le_sup_right : _ ≤ H ⊔ _) (IntermediateField.subset_adjoin ℚ _ hx)
      exact ⟨⟨x, hxM⟩, h2 _ hx, rfl⟩
    obtain ⟨y, hy, hyz⟩ := hT z.2
    have : y = z := Subtype.ext hyz
    exact this ▸ hy

theorem card_GL_le : Nat.card (GL (Fin 2) (ZMod 12)) ≤ 20736 := by
  have h := Nat.card_le_card_of_injective
    (fun g : GL (Fin 2) (ZMod 12) => (g : Matrix (Fin 2) (Fin 2) (ZMod 12))) Units.val_injective
  refine h.trans (le_of_eq ?_)
  change Nat.card (Fin 2 → Fin 2 → ZMod 12) = _
  simp

theorem log_le_twenty {x : ℝ} (h0 : 0 < x) (hx : x ≤ 2 ^ 20) : Real.log x ≤ 20 := by
  have h1 : Real.log x ≤ Real.log (2 ^ 20) := Real.log_le_log h0 hx
  rw [Real.log_pow] at h1
  have := Real.log_two_lt_d9
  push_cast at h1
  linarith

theorem sz_discField : RayField → ∀ (P : Pre) (δ : FieldDat P),
    Sz δ.M' (Real.log P.host.d + 20) (3 * Real.log P.host.d + 20) := by
  intro hR P δ
  obtain ⟨K, _, _, hK, hdK, hd4, -, hO, -⟩ := exists_hostK P.R P.host
  obtain ⟨_, _, L, hL, hF, -, hg⟩ := δ.good
  unfold FieldDat.M'
  set d := P.host.d with hd
  set A := δ.curve
  have hd0 : 0 < d := by omega
  have hs : P.host.φ₀ P.host.sqrtMinusD ∈ K := by
    obtain ⟨a, ha⟩ := (hO _).1 ⟨(-1, 2), rfl⟩
    have : P.host.φ₀ P.host.sqrtMinusD = ((a : K) : ℂ) := by
      rw [ha]; push_cast; ring
    rw [this]; exact (a : K).2
  have hKe : ℚ⟮GlobalTheory.Published.sqrtNegNat d⟯ = K := by
    ext z
    rw [GlobalTheory.Published.mem_adjoin_sqrtNegNat_iff (K := K) hd0 hK (x := ⟨_, hs⟩)
      (Subtype.ext (by
        push_cast
        rw [← map_pow, P.host.sqrtMinusD_sq]; simp [hd]))]
    exact ⟨fun ⟨y, hy⟩ => hy ▸ y.2, fun h => ⟨⟨z, h⟩, rfl⟩⟩
  have hL' : ∀ z : ℂ, z ∈ L.lattice ↔ ∃ a : 𝓞 K, ((a : K) : ℂ) = z := by
    intro z
    rw [hL z, hKe]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨⟨⟨z, h1⟩, (isIntegral_algHom_iff (K.val.toRingHom.toIntAlgHom)
        Subtype.val_injective).1 h2⟩, rfl⟩
    · rintro ⟨a, rfl⟩
      exact ⟨(a : K).2, (isIntegral_algHom_iff (K.val.toRingHom.toIntAlgHom)
        Subtype.val_injective).2 a.2⟩
  have hH : hilbertField d δ.jField = K ⊔ ℚ⟮(GlobalTheory.latticeCurve L).j⟯ := by
    rw [hilbertField, hKe, ← hF]
  rw [DiscRoot.discField_eq_torsionField]
  have hKH : K ≤ hilbertField d δ.jField := hH ▸ le_sup_left
  letI : Algebra K (hilbertField d δ.jField) := (IntermediateField.inclusion hKH).toAlgebra
  obtain ⟨_, _, hu, hdeg⟩ := invariantField hR K hK hd4 L hL' _ hH fun _ => rfl
  obtain ⟨hfin, hM⟩ := TorsionDegree.finrank_torsionField_le d δ.jField A
  haveI : NumberField (torsionField d A) := ⟨⟩
  have hHM := hilbertField_le_torsionField d A
  letI : Algebra (hilbertField d δ.jField) (torsionField d A) :=
    (IntermediateField.inclusion hHM).toAlgebra
  haveI : IsGalois (hilbertField d δ.jField) (torsionField d A) :=
    isGalois_torsion δ.jField (hilbertField d δ.jField) (torsionField d A) A le_sup_right hHM rfl
  have hdn : (discr K).natAbs = d := by rw [hdK]; simp
  have hrd := log_rootDiscr_le K (hilbertField d δ.jField) (torsionField d A) d hd0 hK hdn hu
    (TorsionRam.dvd_discr_torsionField d δ.jField A hg)
  have hM' := hM.trans (Nat.mul_le_mul_left _ card_GL_le)
  have hrel : Module.finrank (hilbertField d δ.jField) (torsionField d A) ≤ 20736 := by
    rw [← (letI : Module.Free (hilbertField d δ.jField) (torsionField d A) := Module.Free.of_divisionRing _ _; Module.finrank_mul_finrank ℚ (hilbertField d δ.jField) (torsionField d A))] at hM'
    exact Nat.le_of_mul_le_mul_left hM' Module.finrank_pos
  rw [← Module.finrank_mul_finrank ℚ K (hilbertField d δ.jField), hK] at hM'
  rw [hdn] at hdeg
  have hdR : (0 : ℝ) < d := Nat.cast_pos.2 hd0
  have hlog : 0 ≤ Real.log d := Real.log_natCast_nonneg d
  have key : ∀ m : ℕ, 0 < m → m ≤ d * 2 ^ 20 → Real.log m ≤ Real.log d + 20 := by
    intro m h0 hm
    have h1 : Real.log m ≤ Real.log (d * 2 ^ 20) :=
      Real.log_le_log (Nat.cast_pos.2 h0) (by exact_mod_cast hm)
    rw [Real.log_mul hdR.ne' (by positivity)] at h1
    have := log_le_twenty (x := 2 ^ 20) (by positivity) le_rfl
    linarith
  have hM2 : Module.finrank ℚ (torsionField d A) ≤ d * 2 ^ 20 :=
    hM'.trans ((Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hdeg)).trans
      (by clear * -; omega))
  refine ⟨hfin, key _ Module.finrank_pos hM2, hrd.trans ?_⟩
  have := key (6 * d * Module.finrank (hilbertField d δ.jField) (torsionField d A))
    (Nat.mul_pos (by omega) Module.finrank_pos)
    ((Nat.mul_le_mul_left _ hrel).trans (by clear * -; omega))
  linarith

end GlobalTheory.Mem.Fld.TorsionSize
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FieldDatumSizeLogDiscriminantStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host GlobalTheory.NT GlobalTheory.Mem GlobalTheory.Mem.Fld GlobalTheory.FieldSize
open scoped IntermediateField

theorem _root_.GlobalTheory.T.field_datum_size_log_discriminant : RayField → ∀ (P : Pre) (δ : FieldDat P), Sz δ.M' (Real.log P.host.d + 20) (3 * Real.log P.host.d + 20) := by
  first | exact @GlobalTheory.Mem.Fld.TorsionSize.sz_discField | exact GlobalTheory.Mem.Fld.TorsionSize.sz_discField | (intros; apply GlobalTheory.Mem.Fld.TorsionSize.sz_discField <;> assumption)
end
end
