module

public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.MemPowSub
public import Mathlib.NumberTheory.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
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
public import Mathlib.FieldTheory.LinearDisjoint
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.MemPowSub
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.SqSubLeNormSub
public import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRingHomAdicCompletionUnder
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsNormFromBaseChangeBaseChangeProperties
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsAdmissiblePlacesContainingPrimeSupersetMon
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsSupersetMemSUnits
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.KummerGalois
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
public import Mathlib.RingTheory.Adjoin.PowerBasis
public import Mathlib.RingTheory.Norm.Basic
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SUnitMemKummerNormsOfLocalNormsStatement
import Mathlib.FieldTheory.KummerExtension
import Mathlib.Tactic.Basify
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Tactic.ENatToNat

-- Source module: Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsPushoutPrimitiveRoot

section

@[expose] public section

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem isField_tensor_of_coprime (F A B : Type) [Field F] [Field A] [Field B] [Algebra F A]
    [Algebra F B] (h : Nat.Coprime (Module.finrank F A) (Module.finrank F B)) :
    IsField (A ⊗[F] B) := by
  refine IntermediateField.LinearDisjoint.isField_of_forall F A B ?_
  intro K _ _ fa fb
  apply IntermediateField.LinearDisjoint.of_finrank_coprime
  have ha : Module.finrank F A = Module.finrank F fa.fieldRange :=
    (AlgEquiv.ofInjectiveField fa).toLinearEquiv.finrank_eq
  have hb : Module.finrank F B = Module.finrank F fb.fieldRange :=
    (AlgEquiv.ofInjectiveField fb).toLinearEquiv.finrank_eq
  rwa [← ha, ← hb]

theorem coprime_finrank_cyclotomic (p : ℕ) (hp : p.Prime) (F A : Type) [Field F] [Field A]
    [Algebra F A] [IsCyclotomicExtension {p} F A] : Nat.Coprime (Module.finrank F A) p := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Module.Finite F A := IsCyclotomicExtension.finite {p} F A
  have hζ := IsCyclotomicExtension.zeta_spec p F A
  have hdvd : minpoly F (IsCyclotomicExtension.zeta p F A) ∣ cyclotomic p F := by
    apply minpoly.dvd
    rw [aeval_def, ← eval_map, map_cyclotomic]
    haveI : NeZero (p : A) := hζ.neZero'
    exact (isRoot_cyclotomic_iff.mpr hζ)
  have hle := natDegree_le_of_dvd hdvd (cyclotomic_ne_zero p F)
  rw [natDegree_cyclotomic, Nat.totient_prime hp] at hle
  have hfr : Module.finrank F A = (minpoly F (IsCyclotomicExtension.zeta p F A)).natDegree := by
    rw [(hζ.powerBasis F).finrank, ← (hζ.powerBasis F).natDegree_minpoly,
      IsPrimitiveRoot.powerBasis_gen]
  have hpos : 0 < Module.finrank F A := Module.finrank_pos
  have h1 := hp.pos
  exact (Nat.coprime_of_lt_prime hpos.ne' (by omega) hp).symm

theorem exists_pushout_primitiveRoot : ∀ (p : ℕ) (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E], p.Prime → p ≠ 2 → Module.finrank F E = p → ∃ (F' E' : Type) (_ : Field F') (_ : NumberField F') (_ : Field E') (_ : NumberField E') (_ : Algebra F F') (_ : Algebra F' E') (_ : Algebra E E') (_ : Algebra F E') (_ : IsScalarTower F F' E') (_ : IsScalarTower F E E') (ζ : F'), Algebra.IsPushout F F' E E' ∧ IsTotallyComplex F' ∧ IsGalois F' E' ∧ IsPrimitiveRoot ζ p ∧ Module.finrank F' E' = p ∧ Nat.Coprime (Module.finrank F F') p := by
  intro p F E _ _ _ _ _ _ hp h2 hdeg
  haveI : NeZero p := ⟨hp.ne_zero⟩
  let A : Type := CyclotomicField p F
  haveI : IsCyclotomicExtension {p} F A := CyclotomicField.isCyclotomicExtension p F
  haveI : NumberField A := IsCyclotomicExtension.numberField {p} F A
  have hco := coprime_finrank_cyclotomic p hp F A
  have hf : IsField (A ⊗[F] E) := isField_tensor_of_coprime F A E (by rwa [hdeg])
  letI : Field (A ⊗[F] E) := hf.toField
  letI : Algebra E (A ⊗[F] E) := Algebra.TensorProduct.rightAlgebra
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : Module.Finite A (A ⊗[F] E) := inferInstance
  haveI : NumberField (A ⊗[F] E) := NumberField.of_module_finite A (A ⊗[F] E)
  have hζ := IsCyclotomicExtension.zeta_spec p F A
  have hr : Module.finrank A (A ⊗[F] E) = p := by
    rw [Module.finrank_baseChange, hdeg]
  have h3 : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm h2)
  refine ⟨A, A ⊗[F] E, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    IsCyclotomicExtension.zeta p F A, inferInstance, ?_, ?_, hζ, hr, hco⟩
  · exact NumberField.nrRealPlaces_eq_zero_iff.mp
      (InfinitePlace.IsPrimitiveRoot.nrRealPlaces_eq_zero_of_two_lt h3 hζ)
  · apply IsGalois.of_card_aut_eq_finrank
    apply le_antisymm
    · rw [Nat.card_eq_fintype_card]; exact AlgEquiv.card_le
    · rw [Module.finrank_baseChange, ← IsGalois.card_aut_eq_finrank]
      refine Nat.card_le_card_of_injective
        (fun g : E ≃ₐ[F] E => (Algebra.TensorProduct.congr (AlgEquiv.refl : A ≃ₐ[A] A) g)) ?_
      intro g h hgh
      ext x
      have := DFunLike.congr_fun hgh ((1 : A) ⊗ₜ[F] x)
      simp only [Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul] at this
      exact (algebraMap E (A ⊗[F] E)).injective this

end GlobalTheory.CNorm
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemUnitsLocalKummerNormsOfBaseChangeNorm

section

@[expose] public section

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem isUnit_of_norm_ne_zero {L A : Type} [Field L] [CommRing A] [Algebra L A]
    [Module.Finite L A] (y : A) (h : Algebra.norm L y ≠ 0) : IsUnit y := by
  have h1 : IsUnit (Algebra.lmul L A y) := by
    rw [LinearMap.isUnit_iff_isUnit_det]
    exact isUnit_iff_ne_zero.mpr (by rwa [Algebra.norm_apply] at h)
  obtain ⟨z, hz⟩ := ((Module.End.isUnit_iff _).mp h1).surjective 1
  exact IsUnit.of_mul_eq_one z (by simpa using hz)

theorem IsKum.nonempty_tensor_equiv {p : ℕ} {F E : Type} [Field F] [Field E] [Algebra F E]
    {ζ δ : F} {θ : E} {σ : E ≃ₐ[F] E} (h : IsKum p ζ δ θ σ) (L : Type) [Field L] [Algebra F L] :
    Nonempty ((L ⊗[F] E) ≃ₐ[L] AdjoinRoot (X ^ p - C (algebraMap F L δ) : L[X])) := by
  have hp := h.prime
  have hmin := h.minpoly_eq
  have hint : IsIntegral F θ :=
    ⟨X ^ p - C δ, monic_X_pow_sub_C δ hp.ne_zero, by simp [h.pow]⟩
  let pb : PowerBasis F E := PowerBasis.ofAdjoinEqTop hint h.gen
  have hgen : pb.gen = θ := PowerBasis.ofAdjoinEqTop_gen hint h.gen
  set g : L[X] := X ^ p - C (algebraMap F L δ) with hg
  have hroot : AdjoinRoot.root g ^ p = algebraMap F (AdjoinRoot g) δ := by
    have := AdjoinRoot.eval₂_root g
    rw [hg, eval₂_sub, eval₂_X_pow, eval₂_C, sub_eq_zero] at this
    rw [IsScalarTower.algebraMap_apply F L (AdjoinRoot g)]
    exact this
  let ψ : E →ₐ[F] AdjoinRoot g := pb.lift (AdjoinRoot.root g) (by
    rw [hgen, hmin]; simp [hroot])
  have hψ : ψ θ = AdjoinRoot.root g := (congrArg _ hgen.symm).trans (pb.lift_gen _ _)
  let a : (L ⊗[F] E) →ₐ[L] AdjoinRoot g :=
    Algebra.TensorProduct.lift (Algebra.ofId L _) ψ (fun _ _ => Commute.all _ _)
  let b : AdjoinRoot g →ₐ[L] (L ⊗[F] E) :=
    AdjoinRoot.liftAlgHom g (Algebra.ofId L _) ((1 : L) ⊗ₜ[F] θ) (by
      rw [hg, eval₂_sub, eval₂_X_pow, eval₂_C, sub_eq_zero, Algebra.TensorProduct.tmul_pow,
        one_pow, h.pow]
      change _ = algebraMap L (L ⊗[F] E) (algebraMap F L δ)
      rw [← IsScalarTower.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply',])
  have hb : b (AdjoinRoot.root g) = (1 : L) ⊗ₜ[F] θ := AdjoinRoot.liftAlgHom_root ..
  have ha : a ((1 : L) ⊗ₜ[F] θ) = AdjoinRoot.root g := by
    simp [a, hψ]
  refine ⟨AlgEquiv.ofAlgHom a b ?_ ?_⟩
  · apply AdjoinRoot.algHom_ext
    simp [ha, hb]
  · apply Algebra.TensorProduct.ext
    · exact Subsingleton.elim _ _
    · apply pb.algHom_ext
      rw [hgen]
      simp [ha, hb]

theorem mem_kNorm_of_tNorm : ∀ (p : ℕ) (F E L : Type) [Field F] [CharZero F] [Field E] [Algebra F E] [Field L] [Algebra F L] (ζ δ : F) (θ : E) (σ : E ≃ₐ[F] E), IsKum p ζ δ θ σ → ∀ x : Fˣ, TNorm F E L (x : F) → x ∈ kNorm p (algebraMap F L) δ := by
  intro p F E L _ _ _ _ _ _ ζ δ θ σ h x ⟨y, hy⟩
  obtain ⟨e⟩ := h.nonempty_tensor_equiv L
  have : Module.Finite L (AdjoinRoot (X ^ p - C (algebraMap F L δ) : L[X])) :=
    (AdjoinRoot.powerBasis' (monic_X_pow_sub_C _ h.prime.ne_zero)).finite
  have hn : Algebra.norm L (e y) = algebraMap F L x := by
    rw [Algebra.norm_eq_of_algEquiv, hy]
  have hu : IsUnit (e y) := isUnit_of_norm_ne_zero _ (by
    rw [hn]; exact (_root_.map_ne_zero _).mpr x.ne_zero)
  rw [mem_kNorm]
  exact ⟨hu.unit, hn⟩

end GlobalTheory.CNorm
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemUnitsLocalKummerNormsOfBaseChangeNormStatement

section

@[expose] public section

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

theorem _root_.GlobalTheory.T.mem_unitsLocalKummerNorms_of_baseChange_norm : ∀ (p : ℕ) (F E L : Type) [Field F] [CharZero F] [Field E] [Algebra F E] [Field L] [Algebra F L] (ζ δ : F) (θ : E) (σ : E ≃ₐ[F] E), IsKum p ζ δ θ σ → ∀ x : Fˣ, TNorm F E L (x : F) → x ∈ kNorm p (algebraMap F L) δ := by
  first | exact @GlobalTheory.CNorm.mem_kNorm_of_tNorm | exact GlobalTheory.CNorm.mem_kNorm_of_tNorm | (intros; apply GlobalTheory.CNorm.mem_kNorm_of_tNorm <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.NpOfFinrankPrimeOfIsPrimitiveRoot

section

@[expose] public section

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem exists_isKum_of_finrank_prime (p : ℕ) (F E : Type) [Field F] [Field E] [Algebra F E]
    [IsGalois F E] (ζ : F) (hp : p.Prime) (hζ : IsPrimitiveRoot ζ p)
    (hr : Module.finrank F E = p) :
    ∃ (δ : F) (θ : E) (σ : E ≃ₐ[F] E), IsKum p ζ δ θ σ := by
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (hr ▸ hp.pos)
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : IsCyclic (E ≃ₐ[F] E) :=
    isCyclic_of_prime_card (p := p) (by rw [IsGalois.card_aut_eq_finrank, hr])
  have hK : (primitiveRoots (Module.finrank F E) F).Nonempty :=
    ⟨ζ, by rw [hr, mem_primitiveRoots hp.pos]; exact hζ⟩
  obtain ⟨θ, ⟨δ, hδ⟩, hθ⟩ := exists_root_adjoin_eq_top_of_isCyclic F E hK
  have hirr := irreducible_X_pow_sub_C_of_root_adjoin_eq_top hδ.symm hθ
  rw [hr] at hirr hδ
  have hmin : (X ^ p - C δ : F[X]) = minpoly F θ :=
    minpoly.eq_of_irreducible_of_monic hirr (by simp [hδ]) (monic_X_pow_sub_C _ hp.ne_zero)
  obtain ⟨σ, hσ⟩ := minpoly.exists_algEquiv_of_root' (K := F) (L := E) (x := algebraMap F E ζ * θ)
    (y := θ) (Algebra.IsAlgebraic.isAlgebraic θ) (by
      rw [← hmin]
      rw [map_sub, map_pow, aeval_X, aeval_C, mul_pow, ← map_pow, hζ.pow_eq_one, map_one, one_mul,
        hδ, sub_self])
  refine ⟨δ, θ, σ, hp, hζ, (X_pow_sub_C_irreducible_iff_of_prime hp).1 hirr, hδ.symm, hσ, ?_⟩
  rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
    (Algebra.IsAlgebraic.isAlgebraic θ), hθ, IntermediateField.top_toSubalgebra]

theorem np_of_finrank_prime_of_isPrimitiveRoot : ∀ (p : ℕ) (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [_root_.NumberField.IsTotallyComplex F] [IsGalois F E] (ζ : F), p.Prime → IsPrimitiveRoot ζ p → Module.finrank F E = p → NP F E := by
  intro p F E _ _ _ _ _ _ _ ζ hp hζ hr x hx hloc
  classical
  obtain ⟨δ, θ, σ, hk⟩ := exists_isKum_of_finrank_prime p F E ζ hp hζ hr
  have hδ0 : δ ≠ 0 := fun h => hk.nonpow 0 (by rw [h, zero_pow hp.ne_zero])
  obtain ⟨S₁, -, hS₁⟩ := exists_superset_mem_sUnits F {Units.mk0 δ hδ0, Units.mk0 x hx} ∅
  obtain ⟨S, hS, hadm⟩ := (exists_admissiblePlaces_superset_and_mono p F hp.pos).1 S₁
  have hfin : Units.mk0 x hx ∈ finNorm p F δ S := by
    simp only [finNorm, Subgroup.mem_iInf]
    intro v _
    exact GlobalTheory.T.mem_unitsLocalKummerNorms_of_baseChange_norm p F E (v.adicCompletion F) ζ δ θ σ hk (Units.mk0 x hx) (hloc.1 v)
  have hx' := GlobalTheory.T.sUnit_mem_kummerNorms_of_local_norms p F ζ (Units.mk0 δ hδ0) S hp hζ hadm (hS₁ S hS _ (by simp))
    hk.nonpow (Units.mk0 x hx) (hS₁ S hS _ (by simp)) hfin
  obtain ⟨y, hy⟩ := (mem_kNorm p (RingHom.id F) δ _).1 hx'
  obtain ⟨-, -, -, -, -, ⟨e⟩, -⟩ := kummer_galois p F E ζ δ θ σ hk
  refine ⟨e.symm y, ?_⟩
  rw [Algebra.norm_eq_of_algEquiv]
  exact hy

end GlobalTheory.CNorm
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.NpOfOddPrimeDegree

section

@[expose] public section

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem tNorm_baseChange_of_ringHom (F F' E E' K K' : Type) [Field F] [Field F'] [Field E]
    [Field E'] [Algebra F F'] [Algebra F E] [Algebra F' E'] [Algebra E E'] [Algebra F E']
    [IsScalarTower F F' E'] [IsScalarTower F E E'] [Algebra.IsPushout F F' E E']
    [FiniteDimensional F E] [Field K] [Algebra F K] [Field K'] [Algebra F' K'] (φ : K →+* K')
    (hφ : ∀ x : F, φ (algebraMap F K x) = algebraMap F' K' (algebraMap F F' x)) (x : F)
    (h : TNorm F E K x) : TNorm F' E' K' (algebraMap F F' x) := by
  letI : Algebra F K' := ((algebraMap F' K').comp (algebraMap F F')).toAlgebra
  haveI : IsScalarTower F F' K' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  obtain ⟨y₀, hy₀⟩ := h
  let ψ : K →ₐ[F] K' := { φ with commutes' := hφ }
  let y : K' ⊗[F] E := Algebra.TensorProduct.map ψ (AlgHom.id F E) y₀
  have hy : Algebra.norm K' y = algebraMap F K' x := by
    rw [tensor_norm_map ψ y₀, hy₀, AlgHom.commutes]
  let e₁ : K' ⊗[F'] (F' ⊗[F] E) ≃ₐ[K'] K' ⊗[F] E :=
    Algebra.TensorProduct.cancelBaseChange F F' K' K' E
  let e₂ : K' ⊗[F'] (F' ⊗[F] E) ≃ₐ[K'] K' ⊗[F'] E' :=
    Algebra.TensorProduct.congr AlgEquiv.refl (Algebra.IsPushout.equiv F F' E E')
  refine ⟨(e₁.symm.trans e₂) y, ?_⟩
  rw [Algebra.norm_eq_of_algEquiv, hy, ← IsScalarTower.algebraMap_apply]

theorem exists_norm_eq_of_coprime_pow {F E : Type} [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] {m n : ℕ} (hc : Nat.Coprime m n) {x : F} (hx : x ≠ 0) {a b : E}
    (ha : Algebra.norm F a = x ^ m) (hb : Algebra.norm F b = x ^ n) :
    ∃ y : E, Algebra.norm F y = x := by
  refine ⟨a ^ (Nat.gcdA m n) * b ^ (Nat.gcdB m n), ?_⟩
  rw [map_mul, Algebra.norm_zpow, Algebra.norm_zpow, ha, hb, ← zpow_natCast, ← zpow_natCast,
    ← zpow_mul, ← zpow_mul, ← zpow_add₀ hx, ← Nat.gcd_eq_gcd_ab, hc]
  simp

theorem np_of_odd_prime_degree : ∀ (p : ℕ) (F E : Type) [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] [IsGalois F E],
    p.Prime → p ≠ 2 → Module.finrank F E = p → NP F E := by
  intro p F E _ _ _ _ _ _ hp h2 hd x hx hl
  obtain ⟨F', E', _, _, _, _, _, _, _, _, _, _, ζ, hpo, htc, hg, hζ, hd', hc⟩ :=
    exists_pushout_primitiveRoot p F E hp h2 hd
  have hl' : LocNorm F' E' (algebraMap F F' x) := by
    refine ⟨fun w => ?_, fun a => ?_⟩
    · obtain ⟨φ, hφ⟩ := GlobalTheory.QNorm.exists_ringHom_adicCompletion_under F F' w
      exact tNorm_baseChange_of_ringHom F F' E E' _ _ φ hφ x (hl.1 _)
    · exfalso
      let ψ : F' →+* ℂ := Complex.ofRealHom.comp (algebraMap F' ℝ)
      apply IsTotallyComplex.complexEmbedding_not_isReal ψ
      rw [ComplexEmbedding.isReal_iff]
      ext y
      simp [ψ]
  obtain ⟨b, hb⟩ :=
    np_of_finrank_prime_of_isPrimitiveRoot p F' E' ζ hp hζ hd' _ (by simpa using hx) hl'
  have h1 : Algebra.norm F (Algebra.norm E b) = x ^ Module.finrank F F' := by
    rw [Algebra.norm_norm, ← Algebra.norm_norm (S := F'), hb, Algebra.norm_algebraMap]
  have h3 : Algebra.norm F (algebraMap F E x) = x ^ p := by
    rw [Algebra.norm_algebraMap, hd]
  exact exists_norm_eq_of_coprime_pow hc hx h1 h3

end GlobalTheory.CNorm
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.NpOfOddPrimeDegreeStatement

section

@[expose] public section

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

theorem _root_.GlobalTheory.T.np_of_odd_prime_degree' : ∀ (p : ℕ) (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E], p.Prime → p ≠ 2 → Module.finrank F E = p → NP F E := by
  first | exact @GlobalTheory.CNorm.np_of_odd_prime_degree | exact GlobalTheory.CNorm.np_of_odd_prime_degree | (intros; apply GlobalTheory.CNorm.np_of_odd_prime_degree <;> assumption)
end
end
