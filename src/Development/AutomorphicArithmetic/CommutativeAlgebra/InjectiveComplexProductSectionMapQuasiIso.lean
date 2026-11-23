module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsImageCocycleSemilinearSheafComplexMapStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypercohomologyMappingConeSecondVariableExactStatement
public import Development.AutomorphicArithmetic.CommutativeAlgebra.BconeDefs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrPreservesHomology
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictScalarsInjectiveSheafAcyclicStatement
public import Development.AutomorphicArithmetic.CommutativeAlgebra.AcyMiddleOfShortExact
public import Development.AutomorphicArithmetic.CommutativeAlgebra.SubsingletonHypercohomologyFreeOfSubsingletonCoh
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
public import Development.AutomorphicArithmetic.CommutativeAlgebra.BijectiveSemiMapOfLocallySurjectiveOnCocycles
public import Development.AutomorphicArithmetic.CommutativeAlgebra.BijectiveSemiMapOpOfBijectiveCochainPushforward
public import Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsBijectiveCohomologyClassProductAdjunction
public import Development.AutomorphicArithmetic.CommutativeAlgebra.InjectiveProductPushforwardOfInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChainsBasicStatement
public import Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsPrimitiveFreeOfAcyLocallyExact
public import Development.AutomorphicArithmetic.CommutativeAlgebra.SubsingletonCohomologyClassOfBoundedOfCyclesLift
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Development.AutomorphicArithmetic.CupPullbacks.ConstCompSingle

-- Source module: Development.AutomorphicArithmetic.CommutativeAlgebra.AcyMappingConeSemiMapOfInjective

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Bc

set_option backward.isDefEq.respectTransparency false in
theorem UpperTheory.acy_mappingCone_semiMap_of_injective :
    ∀ (R : Type) [CommRing R] (L B : Cx R), (∀ s, Injective (L.X s)) → (∀ s, Injective (B.X s)) → ∀ (ρ : SemiMap L B) (Q : Scheme.{0} → Prop) (s : ℤ), Acy Q ((mappingCone ρ.toZ).X s) := by
  intro R _ L B hL hB ρ Q s
  have key : ∀ (I : Shv R), Injective I → Acy Q ((restr (Int.castRingHom R)).obj I) := by
    intro I hI P _ n hn
    exact UpperTheory.subsingleton_hypercohomology_free_of_subsingleton_cohomology _ P n (GlobalTheory.T.restrictScalars_injective_sheaf_acyclic ℤ R _ I P n hn)
  exact UpperTheory.acy_middle_of_shortExact Q _ (mappingCone.triangleRotateShortComplexSplitting ρ.toZ s).shortExact
    (key _ (hB s)) (key _ (hL (s + 1)))
end
end

-- Source module: Development.AutomorphicArithmetic.CommutativeAlgebra.SubsingletonCohomologyClassChainsOfAcyLocallyExa

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Bc

theorem UpperTheory.subsingleton_cohomologyClass_chains_of_acy_locally_exact :
    ∀ (C : Cx ℤ) (a : ℤ) [C.IsStrictlyGE a] (E : Spc), (∀ s, Acy (fun U => Nonempty (Sx E 0 U)) (C.X s)) → (∀ (U : Scheme.{0}), Nonempty (Sx E 0 U) → ∀ (n : ℤ) (b : Sec (C.X n) U), Sec.map (C.d n (n + 1)) b = 0 → Loc U fun V g => ∃ c : Sec (C.X (n - 1)) V, Sec.map (C.d (n - 1) n) c = Sec.res g b) → ∀ n : ℤ, Subsingleton (CohomologyClass ((chains ℤ).obj E) C n) := by
  intro C a _ E hAcy hLoc n
  haveI : IsStrictlyLE ((chains ℤ).obj E) 0 := (GlobalTheory.T.chains_map_and_d_eq_sum_neg_one_pow_smul_delta ℤ).1 E
  refine UpperTheory.subsingleton_cohomologyClass_of_bounded_of_cycles_lift ((chains ℤ).obj E) C a ?_ n
  intro p j f hf
  rcases le_or_gt p 0 with hp | hp
  · obtain ⟨m, rfl⟩ := Int.exists_eq_neg_ofNat hp
    have hmono : ∀ {V U : Scheme.{0}} (g : V ⟶ U), Nonempty (Sx E 0 U) → Nonempty (Sx E 0 V) := by
      intro V U g hx
      obtain ⟨x⟩ := hx
      exact ⟨((E.obj (op (SimplexCategory.mk 0))).map g.op) x⟩
    have hsupp : Supp (fun U => Nonempty (Sx E 0 U)) (E.obj (op (SimplexCategory.mk m))) := by
      intro U hx
      obtain ⟨x⟩ := hx
      exact ⟨((E.map (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk m) 0).op).app (op U)) x⟩
    have hf' : ((chainsXIso ℤ E m).inv ≫ f) ≫ C.d j (j + 1) = 0 := by
      rw [Category.assoc, hf, comp_zero]
    obtain ⟨g, hg⟩ := UpperTheory.exists_primitive_free_of_acy_locally_exact C a (fun U => Nonempty (Sx E 0 U)) hmono hAcy hLoc
      (E.obj (op (SimplexCategory.mk m))) hsupp j _ hf'
    refine ⟨(chainsXIso ℤ E m).hom ≫ g, ?_⟩
    rw [Category.assoc, hg, Iso.hom_inv_id_assoc]
  · refine ⟨0, ?_⟩
    have hz : IsZero (((chains ℤ).obj E).X p) :=
      ((chains ℤ).obj E).isZero_of_isStrictlyLE 0 p hp
    rw [zero_comp]
    exact (hz.eq_of_src _ _).symm
end
end

-- Source module: Development.AutomorphicArithmetic.CommutativeAlgebra.InjectiveComplexProductSectionMapQuasiIso

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf

private theorem rcx_ge (R : Type) [CommRing R] (L : Cx R) [L.IsStrictlyGE 0] :
    ((rcx (Int.castRingHom R)).obj L).IsStrictlyGE 0 := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  exact (restr (Int.castRingHom R)).map_isZero (L.isZero_of_isStrictlyGE 0 i hi)

private theorem semi_bij (R : Type) [CommRing R] (L B : Cx R) [L.IsStrictlyGE 0] [B.IsStrictlyGE 0]
    (hL : ∀ s, Injective (L.X s)) (hB : ∀ s, Injective (B.X s)) (ρ : SemiMap L B) (E : Spc)
    (hs : ∀ (T : Scheme.{0}), Nonempty (Sx E 0 T) → ∀ (n : ℤ) (b : Sec (B.X n) T), Sec.map (B.d n (n + 1)) b = 0 →
      Loc T fun V g => ∃ (a : Sec (L.X n) V) (c : Sec (B.X (n - 1)) V), Sec.map (L.d n (n + 1)) a = 0 ∧
        ρ.app V n a = Sec.res g b + Sec.map (B.d (n - 1) n) c)
    (hi : ∀ (T : Scheme.{0}), Nonempty (Sx E 0 T) → ∀ (n : ℤ) (a : Sec (L.X n) T), Sec.map (L.d n (n + 1)) a = 0 →
      (∃ c : Sec (B.X (n - 1)) T, ρ.app T n a = Sec.map (B.d (n - 1) n) c) →
      Loc T fun V g => ∃ a' : Sec (L.X (n - 1)) V, Sec.map (L.d (n - 1) n) a' = Sec.res g a) (n : ℤ) :
    Function.Bijective (ρ.op.app E n) := by
  have gL := rcx_ge R L
  have gB := rcx_ge R B
  apply UpperTheory.bijective_semiMap_op_of_bijective_cochain_pushforward
  haveI hC : (mappingCone ρ.toZ).IsStrictlyGE (-1) := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    rw [mappingCone.isZero_X_iff]
    exact ⟨((rcx (Int.castRingHom R)).obj L).isZero_of_isStrictlyGE 0 _ (by omega),
      ((rcx (Int.castRingHom R)).obj B).isZero_of_isStrictlyGE 0 _ (by omega)⟩
  have hQ : ∀ {V U : Scheme.{0}} (a : V ⟶ U), Nonempty (Sx E 0 U) → Nonempty (Sx E 0 V) :=
    fun a ⟨x⟩ => ⟨Sx.res a x⟩
  have hsub : ∀ m, Subsingleton (CohomologyClass ((chains ℤ).obj E) (mappingCone ρ.toZ) m) :=
    UpperTheory.subsingleton_cohomologyClass_chains_of_acy_locally_exact (mappingCone ρ.toZ) (-1) E (UpperTheory.acy_mappingCone_semiMap_of_injective R L B hL hB ρ _)
      (UpperTheory.bijective_semiMap_of_locally_surjective_on_cocycles R L B ρ (fun T => Nonempty (Sx E 0 T)) hQ hs hi)
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by ring⟩
  constructor
  · have ex := (GlobalTheory.T.hypercohomology_mappingCone_second_variable_exact ℤ ((chains ℤ).obj E) ρ.toZ m).2.2
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨y, rfl⟩ := (ex x).1 hx
    rw [Subsingleton.elim y 0, map_zero]
  · have ex := (GlobalTheory.T.hypercohomology_mappingCone_second_variable_exact ℤ ((chains ℤ).obj E) ρ.toZ (m + 1)).1
    intro x
    exact (ex x).1 (Subsingleton.elim _ _)

theorem UpperTheory.injectiveComplex_productSection_map_quasiIso :
    ∀ (R : Type) [CommRing R] (W : Scheme.{0}) (L I : Cx R) [L.IsStrictlyGE 0] [I.IsStrictlyGE 0],
        (∀ s, Injective (L.X s)) → (∀ s, Injective (I.X s)) →
        ∀ (ψ : ∀ (T : Scheme.{0}) (s : ℤ), Sec (L.X s) T →+ Sec (I.X s) (W ⨯ T)),
        (∀ {T' T : Scheme.{0}} (g : T' ⟶ T) (s : ℤ) (a : Sec (L.X s) T), Sec.res (prod.map (𝟙 W) g) (ψ T s a) = ψ T' s (Sec.res g a)) →
        (∀ (T : Scheme.{0}) (s t : ℤ) (a : Sec (L.X s) T), Sec.map (I.d s t) (ψ T s a) = ψ T t (Sec.map (L.d s t) a)) →
        ∀ Z : Scheme.{0} → Prop, (∀ {T' T : Scheme.{0}}, (T' ⟶ T) → Z T → Z T') →
        (∀ (T : Scheme.{0}), Z T → ∀ (n : ℤ) (b : Sec (I.X n) (W ⨯ T)), Sec.map (I.d n (n + 1)) b = 0 →
          Loc T fun V g => ∃ (a : Sec (L.X n) V) (c : Sec (I.X (n - 1)) (W ⨯ V)), Sec.map (L.d n (n + 1)) a = 0 ∧
            ψ V n a = Sec.res (prod.map (𝟙 W) g) b + Sec.map (I.d (n - 1) n) c) →
        (∀ (T : Scheme.{0}), Z T → ∀ (n : ℤ) (a : Sec (L.X n) T), Sec.map (L.d n (n + 1)) a = 0 →
          (∃ c : Sec (I.X (n - 1)) (W ⨯ T), ψ T n a = Sec.map (I.d (n - 1) n) c) →
          Loc T fun V g => ∃ a' : Sec (L.X (n - 1)) V, Sec.map (L.d (n - 1) n) a' = Sec.res g a) →
        ∀ E : Spc, (∀ T : Scheme.{0}, Nonempty (Sx E 0 T) → Z T) →
        ∃ Φ : ∀ n : ℤ, CohomologyClass ((chains R).obj E) L n →+ CohomologyClass ((chains R).obj (sch.obj W ⨯ E)) I n,
          (∀ n, Function.Bijective (Φ n)) ∧
          ∀ (n : ℤ) (α : Cocycle ((chains R).obj E) L n),
            (∃ β : Cocycle ((chains R).obj (sch.obj W ⨯ E)) I n, Φ n (CohomologyClass.mk α) = CohomologyClass.mk β ∧
              ∀ (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (T : Scheme.{0}) (y : Sx (sch.obj W ⨯ E) p T),
                ev β.1 p s h T y = Sec.res (prod.lift (show T ⟶ W from y.map prod.fst) (𝟙 T)) (ψ T s (ev α.1 p s h T (y.map prod.snd)))) := by
  intro R _ W L I _ _ hL hI ψ hψn hψc Z hZ hs hi E hE
  let ρ : SemiMap L (UpperTheory.Bc.Bc W I) :=
    { app := fun T s => ψ T s
      nat := fun g s a => hψn g s a
      comm := fun T s t a => hψc T s t a }
  haveI : (UpperTheory.Bc.Bc W I).IsStrictlyGE 0 := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro i hi'
    exact Functor.map_isZero (UpperTheory.Bc.pw R W) (I.isZero_of_isStrictlyGE 0 i hi')
  have hB : ∀ s, Injective ((UpperTheory.Bc.Bc W I).X s) := fun s => by
    haveI := hI s
    exact UpperTheory.injective_productPushforward_of_injective R W (I.X s)
  have hbij := semi_bij R L (UpperTheory.Bc.Bc W I) hL hB ρ E
    (fun T hT n b hb => hs T (hE T hT) n b hb) (fun T hT n a ha hc => hi T (hE T hT) n a ha hc)
  choose Θ hΘ hΘf using fun n => UpperTheory.exists_bijective_cohomologyClass_product_adjunction R W I E n
  refine ⟨fun n => (Θ n).comp (ρ.op.app E n), fun n => (hΘ n).comp (hbij n), ?_⟩
  intro n α
  obtain ⟨β', hβ'⟩ := (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap R R ρ).1 E n α
  have e1 := (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap R R ρ).2 E n α β' hβ'
  obtain ⟨β, hβ, hβf⟩ := hΘf n β'
  refine ⟨β, ?_, ?_⟩
  · show Θ n (ρ.op.app E n (CohomologyClass.mk α)) = _
    rw [e1, hβ]
  · intro p s h T y
    rw [hβf p s h T y, hβ' p s h T]
    rfl
end
end
