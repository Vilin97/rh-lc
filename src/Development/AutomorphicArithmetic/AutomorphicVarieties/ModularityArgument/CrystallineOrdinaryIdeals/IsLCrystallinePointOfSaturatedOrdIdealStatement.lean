module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsInertiaInfiniteCyclotomic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.ChosenFrobeniusIsFrobeniusStatement
public import Mathlib.NumberTheory.Padics.PadicIntegers
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
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
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FiniteCohomology
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.UnitaryThreeReflectionRight
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Mathlib.RingTheory.Filtration
public import Mathlib.RingTheory.HopkinsLevitzki
import ReciprocityTheory.GaloisValuations.GlobalA
import Mathlib.RingTheory.PicardGroup
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.GaloisSubgroupLBasicPropertiesStatement
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.IsLCrystallineConjByInvariant
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.OrdinaryIdealSaturatorsMapAlgHomStatement
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TriDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.TriangularConjOfOrdIdealEqBot
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.TriangularRankThreeCrystallineAfterPushStatement
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.PtCont
import Mathlib.NumberTheory.Padics.LocalField
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.ExistsFiniteLocalLiftOfSaturatedIdealStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

theorem _root_.GlobalTheory.T.exists_finite_local_lift_of_saturated_ideal : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [Algebra ℤ_[l] O] (R : Type) [CommRing R] [Algebra O R] [IsNoetherianRing R] (J : Ideal R) (d : R), (l : R) ∣ d → (∀ a, d * a ∈ J → a ∈ J) → ∀ (B : Type) [CommRing B] [IsLocalRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra O B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] O B] [IsScalarTower ℤ_[l] ℚ_[l] B] (f : R →ₐ[O] B), J ≤ RingHom.ker f → ∃ (B' : Type) (_ : CommRing B') (_ : IsLocalRing B') (_ : Algebra ℚ_[l] B') (_ : Module.Finite ℚ_[l] B') (_ : Algebra O B') (_ : Algebra ℤ_[l] B') (_ : IsScalarTower ℤ_[l] O B') (_ : IsScalarTower ℤ_[l] ℚ_[l] B') (f' : R →ₐ[O] B') (q : B' →ₐ[ℚ_[l]] B), J ≤ RingHom.ker f' ∧ (∀ a, q (f' a) = f a) ∧ ∀ b, f' d * b = 0 → q b = 0 := by
  intro l _ O _ _ R _ _ _ J d _ hreg B _ _ _ _ _ _ _ _ f hJf
  classical
  let M0 : Ideal R := (IsLocalRing.maximalIdeal B).comap f
  let RM := Localization.AtPrime M0
  have hgu : ∀ y : M0.primeCompl, IsUnit ((f : R →+* B) (y : R)) := by
    intro y
    have hy := Ideal.mem_primeCompl_iff.1 y.2
    by_contra h
    exact hy (show (y : R) ∈ M0 from (IsLocalRing.mem_maximalIdeal _).2 h)
  let g : RM →+* B := IsLocalization.lift (M := M0.primeCompl) (S := RM) (g := (f : R →+* B)) hgu
  have hg : ∀ r : R, g (algebraMap R RM r) = f r := fun r => IsLocalization.lift_eq hgu r
  let α : O →+* RM := (algebraMap R RM).comp (algebraMap O R)
  let ψ : ℤ_[l] →+* RM := α.comp (algebraMap ℤ_[l] O)
  have hfψ : ∀ y : ℤ_[l], g (ψ y) = algebraMap ℚ_[l] B (algebraMap ℤ_[l] ℚ_[l] y) := by
    intro y
    show g (algebraMap R RM (algebraMap O R (algebraMap ℤ_[l] O y))) = _
    rw [hg, f.commutes, ← IsScalarTower.algebraMap_apply ℤ_[l] O B y,
      ← IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] B y]
  have hψu : ∀ y : nonZeroDivisors ℤ_[l], IsUnit (ψ y) := by
    intro y
    have hy0 : algebraMap ℤ_[l] ℚ_[l] y ≠ 0 := by
      intro h
      exact nonZeroDivisors.coe_ne_zero y
        ((IsFractionRing.injective ℤ_[l] ℚ_[l]) (h.trans (map_zero _).symm))
    have hr : IsUnit (f (algebraMap O R (algebraMap ℤ_[l] O y))) := by
      rw [← hg]
      have := (isUnit_iff_ne_zero.2 hy0).map (algebraMap ℚ_[l] B)
      rw [← hfψ y] at this
      exact this
    exact (IsLocalization.AtPrime.isUnit_to_map_iff RM M0 _).2
      (Ideal.mem_primeCompl_iff.2 (fun h => ((IsLocalRing.mem_maximalIdeal _).1 h) hr))
  let φ : ℚ_[l] →+* RM := IsLocalization.lift (M := nonZeroDivisors ℤ_[l]) (S := ℚ_[l]) hψu
  have hφ : ∀ y : ℤ_[l], φ (algebraMap ℤ_[l] ℚ_[l] y) = ψ y := fun y => IsLocalization.lift_eq hψu y
  have hgφ : g.comp φ = algebraMap ℚ_[l] B := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors ℤ_[l])
    ext y
    simp only [RingHom.comp_apply, hφ, hfψ]
  haveI : IsArtinianRing B := IsArtinianRing.of_finite ℚ_[l] B
  obtain ⟨N0, hN0⟩ := (isArtinianRing_iff_isNilpotent_maximalIdeal B).1 this
  have hmaxg : ∀ x ∈ IsLocalRing.maximalIdeal RM ^ N0, g x = 0 := by
    intro x hx
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal M0 RM, ← Ideal.map_pow] at hx
    have hle : Ideal.map (algebraMap R RM) (M0 ^ N0) ≤ RingHom.ker g := by
      rw [Ideal.map_le_iff_le_comap]
      intro r hr
      rw [Ideal.mem_comap, RingHom.mem_ker, hg]
      have h1 : f r ∈ (M0 ^ N0).map f := Ideal.mem_map_of_mem f hr
      rw [Ideal.map_pow] at h1
      have h2 : (M0.map f) ^ N0 ≤ IsLocalRing.maximalIdeal B ^ N0 :=
        Ideal.pow_right_mono Ideal.map_comap_le N0
      have h3 := h2 h1
      rw [hN0, Submodule.zero_eq_bot, Ideal.mem_bot] at h3
      exact h3
    exact RingHom.mem_ker.1 (hle hx)
  let J' : Ideal RM := J.map (algebraMap R RM)
  have hJg : ∀ x ∈ J', g x = 0 := by
    intro x hx
    have hle : J' ≤ RingHom.ker g := by
      rw [Ideal.map_le_iff_le_comap]
      intro r hr
      rw [Ideal.mem_comap, RingHom.mem_ker, hg]
      exact RingHom.mem_ker.1 (hJf hr)
    exact RingHom.mem_ker.1 (hle hx)
  have hreg' : ∀ a : RM, algebraMap R RM d * a ∈ J' → a ∈ J' := by
    intro a ha
    obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective M0.primeCompl a
    simp only at ha ⊢
    rw [IsLocalization.mul_mk'_eq_mk'_of_mul, IsLocalization.mk'_mem_map_algebraMap_iff] at ha
    obtain ⟨t, ht, htJ⟩ := ha
    rw [IsLocalization.mk'_mem_map_algebraMap_iff]
    refine ⟨t, ht, hreg _ ?_⟩
    rw [mul_left_comm]
    exact htJ
  obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul (IsLocalRing.maximalIdeal RM)
    (Submodule.span RM {Ideal.Quotient.mk J' (algebraMap R RM d)})
  have hkey : ∀ c : RM, algebraMap R RM d * c ∈ J' ⊔ IsLocalRing.maximalIdeal RM ^ (N0 + k) →
      g c = 0 := by
    intro c hc
    obtain ⟨j, hj, y, hy, hjy⟩ := Submodule.mem_sup.1 hc
    have hx1 : Ideal.Quotient.mk J' (algebraMap R RM d * c) ∈
        (IsLocalRing.maximalIdeal RM ^ (N0 + k)) • (⊤ : Submodule RM (RM ⧸ J')) := by
      rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem, ← hjy, map_add (f := _),
        Ideal.Quotient.eq_zero_iff_mem.2 hj, zero_add]
      exact Ideal.mem_map_of_mem _ hy
    have hx2 : Ideal.Quotient.mk J' (algebraMap R RM d * c) ∈
        Submodule.span RM {Ideal.Quotient.mk J' (algebraMap R RM d)} := by
      have : Ideal.Quotient.mk J' (algebraMap R RM d * c) =
          c • Ideal.Quotient.mk J' (algebraMap R RM d) := by
        rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, mul_comm c]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
    have hx3 := hk (N0 + k) (by omega)
    have h5 : Ideal.Quotient.mk J' (algebraMap R RM d * c) ∈
        IsLocalRing.maximalIdeal RM ^ (N0 + k - k) • (IsLocalRing.maximalIdeal RM ^ k • ⊤ ⊓
          Submodule.span RM {Ideal.Quotient.mk J' (algebraMap R RM d)}) := by
      rw [← hx3]
      exact Submodule.mem_inf.2 ⟨hx1, hx2⟩
    rw [Nat.add_sub_cancel] at h5
    have hx4 : Ideal.Quotient.mk J' (algebraMap R RM d * c) ∈ IsLocalRing.maximalIdeal RM ^ N0 •
        Submodule.span RM {Ideal.Quotient.mk J' (algebraMap R RM d)} :=
      Submodule.smul_mono le_rfl inf_le_right h5
    obtain ⟨a, ha, hav⟩ := Submodule.mem_smul_span_singleton.1 hx4
    have hdiff : algebraMap R RM d * (c - a) ∈ J' := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, mul_sub, map_sub, ← hav, Algebra.smul_def,
        Ideal.Quotient.algebraMap_eq, ← map_mul, mul_comm a, sub_self]
    have hca : c - a ∈ J' := hreg' _ hdiff
    have hc : c = (c - a) + a := by ring
    rw [hc, map_add (f := _), hJg _ hca, hmaxg _ ha, add_zero]
  let I : Ideal RM := J' ⊔ IsLocalRing.maximalIdeal RM ^ (N0 + k)
  have hIg : ∀ x ∈ I, g x = 0 := by
    intro x hx
    obtain ⟨j, hj, y, hy, rfl⟩ := Submodule.mem_sup.1 hx
    rw [map_add (f := _), hJg _ hj, hmaxg _ (Ideal.pow_le_pow_right (by omega) hy), add_zero]
  have hIne : I ≠ ⊤ := by
    intro h
    have h1 : (1 : RM) ∈ I := by rw [h]; exact Submodule.mem_top
    have := hIg 1 h1
    simp at this
  haveI : Nontrivial (RM ⧸ I) := Ideal.Quotient.nontrivial_iff.2 hIne
  haveI hloc : IsLocalRing (RM ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  letI aQ : Algebra ℚ_[l] (RM ⧸ I) := ((Ideal.Quotient.mk I).comp φ).toAlgebra
  letI aO : Algebra O (RM ⧸ I) := ((Ideal.Quotient.mk I).comp α).toAlgebra
  letI aZ : Algebra ℤ_[l] (RM ⧸ I) := ((Ideal.Quotient.mk I).comp ψ).toAlgebra
  haveI t1 : @IsScalarTower ℤ_[l] O (RM ⧸ I) _ aO.toSMul aZ.toSMul := IsScalarTower.of_algebraMap_eq (fun x => rfl)
  haveI t2 : IsScalarTower ℤ_[l] ℚ_[l] (RM ⧸ I) := IsScalarTower.of_algebraMap_eq (fun x => by
    show Ideal.Quotient.mk I (ψ x) = Ideal.Quotient.mk I (φ (algebraMap ℤ_[l] ℚ_[l] x))
    rw [hφ])
  let f' : R →ₐ[O] (RM ⧸ I) :=
    { (Ideal.Quotient.mk I).comp (algebraMap R RM) with commutes' := fun o => rfl }
  let q : (RM ⧸ I) →ₐ[ℚ_[l]] B :=
    { Ideal.Quotient.lift I g hIg with
      commutes' := fun c => by
        show Ideal.Quotient.lift I g hIg (Ideal.Quotient.mk I (φ c)) = algebraMap ℚ_[l] B c
        rw [Ideal.Quotient.lift_mk]
        exact RingHom.congr_fun hgφ c }
  have hmaxQ : IsLocalRing.maximalIdeal (RM ⧸ I) ≤
      (IsLocalRing.maximalIdeal RM).map (Ideal.Quotient.mk I) := by
    intro x hx
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    apply Ideal.mem_map_of_mem
    by_contra hy
    simp only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at hx hy
    exact hx (hy.map _)
  have hnil : IsLocalRing.maximalIdeal (RM ⧸ I) ^ (N0 + k) = ⊥ := by
    rw [eq_bot_iff]
    calc IsLocalRing.maximalIdeal (RM ⧸ I) ^ (N0 + k)
        ≤ ((IsLocalRing.maximalIdeal RM).map (Ideal.Quotient.mk I)) ^ (N0 + k) :=
          Ideal.pow_right_mono hmaxQ _
      _ = (IsLocalRing.maximalIdeal RM ^ (N0 + k)).map (Ideal.Quotient.mk I) :=
          (Ideal.map_pow _ _ _).symm
      _ ≤ I.map (Ideal.Quotient.mk I) := Ideal.map_mono le_sup_right
      _ = ⊥ := Ideal.map_quotient_self I
  haveI hart : IsArtinianRing (RM ⧸ I) := by
    rw [isArtinianRing_iff_isNilpotent_maximalIdeal]
    exact ⟨N0 + k, by rw [hnil]; rfl⟩
  have hfin : Module.Finite ℚ_[l] (RM ⧸ I) := by
    haveI : Module.Finite ℚ_[l] ((RM ⧸ I) ⧸ Ring.jacobson (RM ⧸ I)) := by
      rw [IsLocalRing.ringJacobson_eq_maximalIdeal]
      have hle : IsLocalRing.maximalIdeal (RM ⧸ I) ≤ (IsLocalRing.maximalIdeal B).comap q := by
        intro x hx
        rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
        intro hu
        have hx0 : x ^ (N0 + k) = 0 := by
          have := Ideal.pow_mem_pow hx (N0 + k)
          rw [hnil] at this
          exact (Ideal.mem_bot).1 this
        have := hu.pow (N0 + k)
        rw [← map_pow, hx0, map_zero] at this
        exact not_isUnit_zero this
      have hcomap : (IsLocalRing.maximalIdeal B).comap (q : (RM ⧸ I) →+* B) ≤
          IsLocalRing.maximalIdeal (RM ⧸ I) :=
        IsLocalRing.le_maximalIdeal (Ideal.comap_ne_top _ (Ideal.IsMaximal.ne_top inferInstance))
      have hinj : Function.Injective (Ideal.quotientMap (IsLocalRing.maximalIdeal B)
          (q : (RM ⧸ I) →+* B) hle) := Ideal.quotientMap_injective' hcomap
      haveI : Module.Finite ℚ_[l] (B ⧸ IsLocalRing.maximalIdeal B) :=
        Module.Finite.of_surjective (Ideal.Quotient.mkₐ ℚ_[l] (IsLocalRing.maximalIdeal B)).toLinearMap
          (Ideal.Quotient.mkₐ_surjective ℚ_[l] (IsLocalRing.maximalIdeal B))
      exact Module.Finite.of_injective
        (Ideal.quotientMapₐ (IsLocalRing.maximalIdeal B) q hle).toLinearMap hinj
    exact IsSemiprimaryRing.finite_of_isArtinian ℚ_[l] (RM ⧸ I) (RM ⧸ I)
  refine ⟨RM ⧸ I, inferInstance, hloc, aQ, hfin, aO, aZ, t1, t2, f', q, ?_, ?_, ?_⟩
  · intro x hx
    rw [RingHom.mem_ker]
    show Ideal.Quotient.mk I (algebraMap R RM x) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hx)
  · intro a
    show Ideal.Quotient.lift I g hIg (Ideal.Quotient.mk I (algebraMap R RM a)) = f a
    rw [Ideal.Quotient.lift_mk, hg]
  · intro b hb
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective b
    show Ideal.Quotient.lift I g hIg (Ideal.Quotient.mk I c) = 0
    rw [Ideal.Quotient.lift_mk]
    apply hkey
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul]
    exact hb
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.IsLCrystallineConjByInvariantStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

theorem _root_.GlobalTheory.T.isLCrystalline_conjBy_invariant : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O) (B : Type) [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra O B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] O B] [IsScalarTower ℤ_[l] ℚ_[l] B] (r : GQ l →* GG (m := 3) (R := B)) (h : GL (Fin 3) B), HasMult D.η r → (∀ a b, QCont l fun g => (r g).mat a b) → D.IsLCr (conjBy h r) → D.IsLCr r := by
  first | exact @GlobalTheory.LCrConj.main | exact GlobalTheory.LCrConj.main | (intros; apply GlobalTheory.LCrConj.main <;> assumption)
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.TriangularConjOfOrdIdealEqBotStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

theorem _root_.GlobalTheory.T.triangular_conj_of_ordIdeal_eq_bot : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O) (B : Type) [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra O B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] O B] [IsScalarTower ℤ_[l] ℚ_[l] B] [IsLocalRing B] [TopologicalSpace B] [IsModuleTopology ℚ_[l] B] [IsTopologicalRing B] (r : GQ l →* GG (m := 3) (R := B)), HasMult D.η r → (∀ a b, QCont l fun g => (r g).mat a b) → GlobalTheory.OrdLoc.ordIdeal D r = ⊥ → ∃ (h : GL (Fin 3) B) (ρ : ↥D.HL →* GL (Fin 3) B) (κ : Fin 3 → ↥D.HL →* Bˣ) (x y z : ↥D.HL → B), (∀ g, ρ g = (conjBy h r g).left) ∧ (∀ i, Continuous fun g => (κ i g : B)) ∧ (∀ g : ↥D.HL, (g : GQ l) ∈ Iq l → ∀ i, κ i g = cycA l l B (g : GQ l) ^ ((D.e : ℤ) * wt1 i)) ∧ Continuous z ∧ (∀ g, (ρ g : Matrix (Fin 3) (Fin 3) B) = triM (fun i => κ i g) (x g) (y g) (z g)) ∧ x ∈ Z1 (chRep (κ 0 / κ 1)) ∧ y ∈ Z1 (chRep (κ 1 / κ 2)) ∧ ∀ hσ : GlobalTheory.OrdLoc.fr D ∈ D.HL, (∃ v : Bˣ, GlobalTheory.OrdLoc.dd D r 0 = v * (((κ 0 / κ 1) ⟨_, hσ⟩ : Bˣ) - (cycA l l B (GlobalTheory.OrdLoc.fr D) : B))) ∧ ∃ v : Bˣ, GlobalTheory.OrdLoc.dd D r 1 = v * (((κ 1 / κ 2) ⟨_, hσ⟩ : Bˣ) - (cycA l l B (GlobalTheory.OrdLoc.fr D) : B)) := by
  first | exact @GlobalTheory.OrdLoc.triangular_of_ordIdeal_eq_bot | exact GlobalTheory.OrdLoc.triangular_of_ordIdeal_eq_bot | (intros; apply GlobalTheory.OrdLoc.triangular_of_ordIdeal_eq_bot <;> assumption)
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.IsLCrystallinePointOfSaturatedOrdIdeal

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

namespace GlobalTheory.OrdLocPt

theorem main : LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O) (U : _root_.UpperTheory.V.U3.Univ (_root_.UpperTheory.V.U3.GCond.noCondition O D.η D.Ψ)) (B : Type) [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra O B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] O B] [IsScalarTower ℤ_[l] ℚ_[l] B] [IsLocalRing B] (f : U.R →ₐ[O] B), GlobalTheory.OrdLoc.IY D U ≤ RingHom.ker f → D.IsLCr (push f U.r.hom) := by
  intro hP l _ O _ _ _ _ _ _ _ D U B _ _ _ _ _ _ _ _ f hf

  have hord : GlobalTheory.OrdLoc.ordIdeal D U.r.hom ≤ GlobalTheory.OrdLoc.IY D U := fun a ha => ⟨0, by simpa using ha⟩
  have hdiv : (l : U.R) ∣ GlobalTheory.OrdLoc.del D U.r.hom :=
    ⟨GlobalTheory.OrdLoc.dd D U.r.hom 0 * GlobalTheory.OrdLoc.dd D U.r.hom 1, by unfold GlobalTheory.OrdLoc.del; ring⟩
  have hsat : ∀ a, GlobalTheory.OrdLoc.del D U.r.hom * a ∈ GlobalTheory.OrdLoc.IY D U → a ∈ GlobalTheory.OrdLoc.IY D U := by
    rintro a ⟨n, hn⟩
    exact ⟨n + 1, by rw [pow_succ, mul_assoc]; exact hn⟩
  obtain ⟨B', _, _, _, _, _, _, _, _, f', q, hJ, hqf, hkill⟩ :=
    GlobalTheory.T.exists_finite_local_lift_of_saturated_ideal U.R (GlobalTheory.OrdLoc.IY D U) (GlobalTheory.OrdLoc.del D U.r.hom) hdiv hsat B f hf
  letI : TopologicalSpace B' := moduleTopology ℚ_[l] B'
  haveI : IsModuleTopology ℚ_[l] B' := ⟨rfl⟩
  haveI : IsTopologicalRing B' := IsModuleTopology.isTopologicalRing ℚ_[l] B'
  obtain ⟨hnat, -, hdel⟩ := GlobalTheory.T.ordinaryIdeal_saturators_map_algHom D f' U.r.hom
  have hzero : GlobalTheory.OrdLoc.ordIdeal D (push f' U.r.hom) = ⊥ := by
    rw [← hnat, Ideal.map_eq_bot_iff_le_ker]
    exact hord.trans hJ
  have hmult' : HasMult D.η (push f' U.r.hom) := fun g => U.r.hasMult g
  have hcont' : ∀ a b, QCont l fun g => (push f' U.r.hom g).mat a b := fun a b =>
    (ptCont U.R B' f').1 (GQ l) (fun g => (U.r.hom g).mat a b) (U.r.cont a b)
  obtain ⟨h, ρ, κ, x, y, z, hρ, hκc, hκI, hz, hρM, hx, hy, hσd⟩ :=
    GlobalTheory.T.triangular_conj_of_ordIdeal_eq_bot D B' (push f' U.r.hom) hmult' hcont' hzero
  obtain ⟨⟨hσ, hcl⟩, -⟩ := GlobalTheory.T.chosenFrobenius_isFrobenius D
  obtain ⟨-, -, hφ, -, -⟩ := GlobalTheory.T.galoisSubgroupL_basic_properties D
  obtain ⟨⟨v0, hv0⟩, ⟨v1, hv1⟩⟩ := hσd hσ
  have hdel' : f' (GlobalTheory.OrdLoc.del D U.r.hom) = (l : B') * GlobalTheory.OrdLoc.dd D (push f' U.r.hom) 0 *
      GlobalTheory.OrdLoc.dd D (push f' U.r.hom) 1 := hdel
  have hcr := GlobalTheory.T.triangular_rank_three_crystalline_after_push hP D.HL.subtype hφ q D.e D.e_pos κ hκc hκI x y z ρ hz hρM hx hy ⟨_, hσ⟩ hcl
    (fun b hb => hkill b (by
      have hb' : ((((κ 0 / κ 1) ⟨_, hσ⟩ : B'ˣ) : B') - (cycA l l B' (GlobalTheory.OrdLoc.fr D) : B')) * b = 0 := hb
      rw [hdel', hv0]
      linear_combination ((l : B') * (v0 : B') * GlobalTheory.OrdLoc.dd D (push f' U.r.hom) 1) * hb'))
    (fun b hb => hkill b (by
      have hb' : ((((κ 1 / κ 2) ⟨_, hσ⟩ : B'ˣ) : B') - (cycA l l B' (GlobalTheory.OrdLoc.fr D) : B')) * b = 0 := hb
      rw [hdel', hv1]
      linear_combination ((l : B') * GlobalTheory.OrdLoc.dd D (push f' U.r.hom) 0 * (v1 : B')) * hb'))
  have hmult : HasMult D.η (push f U.r.hom) := fun g => U.r.hasMult g
  have hcont : ∀ a b, QCont l fun g => (push f U.r.hom g).mat a b := fun a b =>
    (ptCont U.R B f).1 (GQ l) (fun g => (U.r.hom g).mat a b) (U.r.cont a b)
  have hqf' : (q : B' →+* B).comp (f' : U.R →+* B') = (f : U.R →+* B) := RingHom.ext hqf
  refine GlobalTheory.T.isLCrystalline_conjBy_invariant D B (push f U.r.hom) (Matrix.GeneralLinearGroup.map (q : B' →+* B) h) hmult hcont
    ⟨(Matrix.GeneralLinearGroup.map (q : B' →+* B)).comp ρ, fun g => ?_, hcr⟩
  have e1 : GG.map (q : B' →+* B) (conjBy h (push f' U.r.hom) (g : GQ l)) =
      conjBy (Matrix.GeneralLinearGroup.map (q : B' →+* B) h) (push f U.r.hom) (g : GQ l) := by
    simp only [conjBy, push, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv,
      GG.map_map, hqf']
    congr 2 <;> simp [GG.ofGL, GG.map, SemidirectProduct.map_inl]
  rw [MonoidHom.comp_apply, hρ g, ← e1]
  rfl

end GlobalTheory.OrdLocPt
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.IsLCrystallinePointOfSaturatedOrdIdealStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

theorem _root_.GlobalTheory.T.isLCrystalline_point_of_saturatedOrdIdeal : LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O) (U : _root_.UpperTheory.V.U3.Univ (_root_.UpperTheory.V.U3.GCond.noCondition O D.η D.Ψ)) (B : Type) [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra O B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] O B] [IsScalarTower ℤ_[l] ℚ_[l] B] [IsLocalRing B] (f : U.R →ₐ[O] B), GlobalTheory.OrdLoc.IY D U ≤ RingHom.ker f → D.IsLCr (push f U.r.hom) := by
  first | exact @GlobalTheory.OrdLocPt.main | exact GlobalTheory.OrdLocPt.main | (intros; apply GlobalTheory.OrdLocPt.main <;> assumption)
end
end
