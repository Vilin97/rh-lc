module

public import ReciprocityTheory.GaloisValuations.Global
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.IneAbs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.IsClassFieldHilbert
public import Mathlib.FieldTheory.Galois.Abelian
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.KwRamSplit
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.UnramIff
import GroundTheory.GlobalFields.ExistenceTheorem.ExistsIsAbelianGaloisRangeIdeleClassNormEqOfFini
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.KwRamSub

section

@[expose] public section

open NumberField IsDedekindDomain IntermediateField UpperTheory.V.Kum UpperTheory.V.CF
open scoped Pointwise

theorem UpperTheory.V.CF.kwRamSub :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosed Ω] (L : IntermediateField ℚ Ω) [NumberField L] [IsAbelianGalois ℚ L] (M : ℕ), 0 < M → (∀ p : ℕ, p.Prime → ¬ p ∣ M → UnramAt L p) → ∃ (n : ℕ) (ζ : Ω), IsPrimitiveRoot ζ (M ^ n) ∧ L ≤ ℚ⟮ζ⟯ := by
  intro Ω _ _ _ L _ _ M hM hram
  obtain ⟨n, ⟨g⟩⟩ := kwRam L M hM hram
  haveI : NeZero (M ^ n) := ⟨by positivity⟩
  haveI : NeZero ((M ^ n : ℕ) : ℚ) := ⟨by exact_mod_cast (show M ^ n ≠ 0 by positivity)⟩
  haveI : IsCyclotomicExtension {M ^ n} ℚ (CyclotomicField (M ^ n) ℚ) := by
    convert CyclotomicField.isCyclotomicExtension (M ^ n) ℚ
    · rfl
  haveI : NumberField (CyclotomicField (M ^ n) ℚ) :=
    IsCyclotomicExtension.numberField {M ^ n} ℚ _
  have hgal : IsGalois ℚ L := IsAbelianGalois.toIsGalois
  obtain ⟨ξ, hξ⟩ : ∃ z : CyclotomicField (M ^ n) ℚ, IsPrimitiveRoot z (M ^ n) :=
    ⟨_, IsCyclotomicExtension.zeta_spec _ ℚ _⟩
  let ψ : CyclotomicField (M ^ n) ℚ →ₐ[ℚ] Ω := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨n, ψ ξ, hξ.map_of_injective ψ.injective, ?_⟩
  have hnorm : (ψ.comp g).fieldRange = L :=
    @AlgHom.fieldRange_of_normal ℚ Ω _ _ _ L
      (by convert hgal.to_normal; all_goals first | rfl | exact Subsingleton.elim _ _) (ψ.comp g)
  rw [← hnorm]
  intro x hx
  obtain ⟨y, rfl⟩ := AlgHom.mem_fieldRange.mp hx
  have hy : g y ∈ Algebra.adjoin ℚ {ξ} := by
    rw [IsCyclotomicExtension.adjoin_primitive_root_eq_top hξ]
    trivial
  have hψ : ψ (g y) ∈ Algebra.adjoin ℚ {ψ ξ} := by
    rw [← Set.image_singleton, ← AlgHom.map_adjoin]
    exact ⟨g y, hy, rfl⟩
  exact IntermediateField.algebra_adjoin_le_adjoin ℚ {ψ ξ} hψ
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.KwAbsRam

section

@[expose] public section

open NumberField IsDedekindDomain IntermediateField Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Kum UpperTheory.V.CF
open scoped Pointwise

private theorem abelian_ramification_cyclotomic_bound (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (V : Subgroup (G ℚ Ω))
    (hV : IsOpen (V : Set (G ℚ Ω))) (hc : commutator (G ℚ Ω) ≤ V) (M : ℕ) (hM : 0 < M)
    (hI : ∀ A : ValuationSubring Ω, ¬ A.valuation (M : Ω) < 1 → Ine (F := ℚ) A ≤ V) :
    ∃ n : ℕ, ∀ g : G ℚ Ω, (∀ ζ : Ω, ζ ^ M ^ n = 1 → g ζ = ζ) → g ∈ V := by
  classical
  haveI : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  set L : IntermediateField ℚ Ω := IntermediateField.fixedField V with hLdef
  have hVc : IsClosed (V : Set (G ℚ Ω)) := Subgroup.isClosed_of_isOpen V hV
  have hLV : L.fixingSubgroup = V :=
    InfiniteGalois.fixingSubgroup_fixedField ⟨V, hVc⟩
  haveI : FiniteDimensional ℚ L := by
    rw [← InfiniteGalois.isOpen_iff_finite]
    rw [hLV]
    exact hV
  have hVn : V.Normal := by
    constructor
    intro v hv g
    have hcm : g * v * g⁻¹ * v⁻¹ ∈ V :=
      hc (Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top v))
    have : g * v * g⁻¹ = (g * v * g⁻¹ * v⁻¹) * v := by group
    rw [this]
    exact V.mul_mem hcm hv
  haveI : IsGalois ℚ L := by
    have := (InfiniteGalois.normal_iff_isGalois L).1 (by rw [hLV]; exact hVn)
    convert this
  have hres : ∀ σ : G ℚ Ω, resTo ℚ L Ω σ = 1 ↔ σ ∈ V := by
    intro σ
    rw [← hLV, IntermediateField.mem_fixingSubgroup_iff]
    constructor
    · intro h x hx
      have := resTo_commutes ℚ L Ω σ ⟨x, hx⟩
      rw [h] at this
      simpa using this.symm
    · intro h
      ext x
      have := resTo_commutes ℚ L Ω σ x
      have h2 : σ (algebraMap L Ω x) = algebraMap L Ω x := h x.1 x.2
      rw [h2] at this
      simpa using this
  haveI : IsMulCommutative Gal(L/ℚ) := by
    refine ⟨⟨fun a b => ?_⟩⟩
    obtain ⟨g, rfl⟩ := resTo_surjective ℚ L Ω a
    obtain ⟨h, rfl⟩ := resTo_surjective ℚ L Ω b
    have hcm : g * h * g⁻¹ * h⁻¹ ∈ V :=
      hc (Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top h))
    have h1 := (hres _).2 hcm
    simp only [map_mul, map_inv] at h1
    show resTo ℚ L Ω g * resTo ℚ L Ω h = resTo ℚ L Ω h * resTo ℚ L Ω g
    calc resTo ℚ L Ω g * resTo ℚ L Ω h
        = (resTo ℚ L Ω g * resTo ℚ L Ω h * (resTo ℚ L Ω g)⁻¹ * (resTo ℚ L Ω h)⁻¹) *
            (resTo ℚ L Ω h * resTo ℚ L Ω g) := by group
      _ = resTo ℚ L Ω h * resTo ℚ L Ω g := by rw [h1, one_mul]
  haveI : IsAbelianGalois ℚ L := ⟨⟩
  have hunr : ∀ p : ℕ, Nat.Prime p → ¬ p ∣ M → UnramAt L p := by
    intro p hp hpM
    rw [(unramIff.1 L p hp)]
    intro w hpw
    obtain ⟨A, hA⟩ := exists_isPlaceOver (F := L) Ω w
    rw [← ineAbs ℚ L Ω A w hA]
    have hAV : Ine (F := ℚ) A ≤ V := by
      apply hI
      intro hlt
      have hMw : ((M : 𝓞 L)) ∈ w.asIdeal := by
        rw [← hA]
        simpa using hlt
      have hcop : Nat.Coprime p M := (Nat.Prime.coprime_iff_not_dvd hp).2 hpM
      have h1 : (1 : 𝓞 L) ∈ w.asIdeal := by
        have := Nat.gcd_eq_gcd_ab p M
        rw [hcop] at this
        have e : ((1 : ℤ) : 𝓞 L) = ((p : ℤ) : 𝓞 L) * ((Nat.gcdA p M : ℤ) : 𝓞 L)
            + ((M : ℤ) : 𝓞 L) * ((Nat.gcdB p M : ℤ) : 𝓞 L) := by
          rw [← Int.cast_mul, ← Int.cast_mul, ← Int.cast_add]
          congr 1
        simp only [Int.cast_one, Int.cast_natCast] at e
        rw [e]
        exact w.asIdeal.add_mem (w.asIdeal.mul_mem_right _ hpw) (w.asIdeal.mul_mem_right _ hMw)
      exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)
    rw [eq_bot_iff]
    rintro x ⟨y, hy, rfl⟩
    exact (hres y).2 (hAV hy)
  obtain ⟨n, ζ, hζ, hLζ⟩ := kwRamSub Ω L M hM hunr
  refine ⟨n, fun g hg => ?_⟩
  let S : Subgroup (G ℚ Ω) := MulAction.stabilizer (G ℚ Ω) ζ
  have hζS : ζ ∈ IntermediateField.fixedField S := by
    rw [IntermediateField.mem_fixedField_iff]
    intro f hf
    exact hf
  have hLS : L ≤ IntermediateField.fixedField S :=
    hLζ.trans (IntermediateField.adjoin_simple_le_iff.2 hζS)
  have hgS : g ∈ S := hg ζ hζ.pow_eq_one
  rw [← hLV]
  exact (IntermediateField.le_iff_le S L).1 hLS hgS

theorem UpperTheory.V.CF.kwAbsRam :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (V : Subgroup (G ℚ Ω)), IsOpen (V : Set (G ℚ Ω)) → commutator (G ℚ Ω) ≤ V → ∀ M : ℕ, 0 < M → (∀ A : ValuationSubring Ω, ¬ A.valuation (M : Ω) < 1 → Ine (F := ℚ) A ≤ V) → ∃ n : ℕ, ∀ g : G ℚ Ω, (∀ ζ : Ω, ζ ^ M ^ n = 1 → g ζ = ζ) → g ∈ V := by
  intro Ω _ alg _ V hV hc M hM hI
  have hch : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  obtain rfl : alg = DivisionRing.toRatAlgebra := Subsingleton.elim _ _
  exact abelian_ramification_cyclotomic_bound Ω V hV hc M hM hI
end
end
