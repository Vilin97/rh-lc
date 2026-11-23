module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorsTrivial
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
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
public import Mathlib.Algebra.Field.Equiv
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.Jacobson.Ring
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionStrictHenselisationClosedFibrePointStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorsTrivialIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSpecialisationToStrictlyHenselian
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpreadTorsorToEtaleAlgebraStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMaximalOverClosedPointClosedFibre

section

@[expose] public section

open IsLocalRing Polynomial

namespace GlobalTheory

theorem exists_maximal_over_closedPt : ∀ (T E : Type) [CommRing T] [IsLocalRing T] [CommRing E] [Algebra (Polynomial T) E]
    [Algebra.FiniteType (Polynomial T) E] (Q : Ideal E) [Q.IsPrime],
    Q.comap (algebraMap (Polynomial T) E) =
      (IsLocalRing.maximalIdeal T).map (Polynomial.C : T →+* Polynomial T) →
    ∃ y : Ideal E, y.IsMaximal ∧ Q ≤ y ∧
      y.comap (algebraMap (Polynomial T) E) ≠
        (IsLocalRing.maximalIdeal T).map (Polynomial.C : T →+* Polynomial T) ∧
      (y.comap (algebraMap (Polynomial T) E)).comap (Polynomial.C : T →+* Polynomial T) =
        IsLocalRing.maximalIdeal T := by
  intro T E _ _ _ _ _ Q hQp hQ
  set P : Ideal T[X] := (maximalIdeal T).map (C : T →+* T[X]) with hPdef
  set f := algebraMap T[X] E with hfdef
  obtain ⟨y, hy, hQy⟩ := Ideal.exists_le_maximal Q hQp.ne_top
  have hPy : P ≤ y.comap f := hQ ▸ Ideal.comap_mono hQy

  letI : Field (T ⧸ maximalIdeal T) := Ideal.Quotient.field _
  have eP := Ideal.polynomialQuotientEquivQuotientPolynomial (maximalIdeal T)
  haveI : IsJacobsonRing (T[X] ⧸ P) := isJacobsonRing_of_surjective ⟨eP.toRingHom, eP.surjective⟩
  have hPnf : ¬ P.IsMaximal := by
    intro hm
    have hf : IsField (T[X] ⧸ P) := (Ideal.Quotient.maximal_ideal_iff_isField_quotient P).1 hm
    exact Polynomial.not_isField (T ⧸ maximalIdeal T) (MulEquiv.isField hf eP.toMulEquiv)

  let φ : T[X] ⧸ P →+* E ⧸ y := Ideal.quotientMap y f hPy
  have hcomp : φ.comp (Ideal.Quotient.mk P) = (Ideal.Quotient.mk y).comp f := Ideal.quotientMap_comp_mk hPy
  have hft : φ.FiniteType := by
    apply RingHom.FiniteType.of_comp_finiteType (f := Ideal.Quotient.mk P)
    rw [hcomp]
    exact RingHom.FiniteType.comp (RingHom.FiniteType.of_surjective _ Ideal.Quotient.mk_surjective)
      (RingHom.finiteType_algebraMap.mpr inferInstance)
  letI : Field (E ⧸ y) := Ideal.Quotient.field y
  letI : Algebra (T[X] ⧸ P) (E ⧸ y) := φ.toAlgebra
  haveI : Algebra.FiniteType (T[X] ⧸ P) (E ⧸ y) := hft
  haveI : Module.Finite (T[X] ⧸ P) (E ⧸ y) := finite_of_finite_type_of_isJacobsonRing _ _
  have hker : (RingHom.ker φ).IsMaximal := by
    have := Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := T[X] ⧸ P) (⊥ : Ideal (E ⧸ y))
    change (Ideal.comap φ ⊥).IsMaximal at this
    rwa [← RingHom.ker_eq_comap_bot] at this
  have hyc : y.comap f = (RingHom.ker φ).comap (Ideal.Quotient.mk P) := by
    ext x
    rw [Ideal.mem_comap, Ideal.mem_comap, RingHom.mem_ker, ← RingHom.comp_apply, hcomp, RingHom.comp_apply,
      Ideal.Quotient.eq_zero_iff_mem]
  have hymax : (y.comap f).IsMaximal := by
    rw [hyc]; exact Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
  refine ⟨y, hy, hQy, fun h => hPnf (h ▸ hymax), ?_⟩
  have hle : maximalIdeal T ≤ (y.comap f).comap C := by
    intro a ha
    exact hPy (Ideal.mem_map_of_mem _ ha)
  have hne : (y.comap f).comap (C : T →+* T[X]) ≠ ⊤ := (Ideal.comap_isPrime C (y.comap f)).ne_top
  exact ((maximalIdeal.isMaximal T).eq_of_le hne hle).symm

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMaximalOverClosedPointClosedFibreStatement

section

@[expose] public section

open IsLocalRing Polynomial

theorem _root_.GlobalTheory.T.exists_maximal_over_closedPoint_closedFibre : ∀ (T E : Type) [CommRing T] [IsLocalRing T] [CommRing E] [Algebra (Polynomial T) E]
    [Algebra.FiniteType (Polynomial T) E] (Q : Ideal E) [Q.IsPrime],
    Q.comap (algebraMap (Polynomial T) E) =
      (IsLocalRing.maximalIdeal T).map (Polynomial.C : T →+* Polynomial T) →
    ∃ y : Ideal E, y.IsMaximal ∧ Q ≤ y ∧
      y.comap (algebraMap (Polynomial T) E) ≠
        (IsLocalRing.maximalIdeal T).map (Polynomial.C : T →+* Polynomial T) ∧
      (y.comap (algebraMap (Polynomial T) E)).comap (Polynomial.C : T →+* Polynomial T) =
        IsLocalRing.maximalIdeal T := by
  first | (exact @GlobalTheory.exists_maximal_over_closedPt) | (exact GlobalTheory.exists_maximal_over_closedPt) | (intros; apply GlobalTheory.exists_maximal_over_closedPt  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSpecialisationToStrictlyHenselianStatement

section

@[expose] public section

open IsLocalRing Polynomial

theorem _root_.GlobalTheory.T.exists_specialisation_to_strictlyHenselian : ∀ (R S O : Type) [CommRing R] [CommRing S] [IsLocalRing S] [CommRing O]
    [HenselianLocalRing O] [IsSepClosed (IsLocalRing.ResidueField O)] [Algebra R S] [Algebra R O]
    (Q y : Ideal R) [Q.IsPrime] [y.IsPrime], Q ≤ y →
    (IsLocalRing.maximalIdeal S).comap (algebraMap R S) = y →
    (IsLocalRing.maximalIdeal O).comap (algebraMap R O) = Q →
    Module.Flat R S → GlobalTheory.LocAcyc.LocPiecesEtale R S → Nonempty (S →ₐ[R] O) := by
  first | exact @GlobalTheory.Specialise.specialisation_exists | exact GlobalTheory.Specialise.specialisation_exists | (intros; apply GlobalTheory.Specialise.specialisation_exists <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyGenericOfKeyClosedPts

section

@[expose] public section

open IsLocalRing Polynomial

noncomputable section

namespace GlobalTheory.LocAcyc

private theorem spread_torsor : ∀ (T O : Type) [CommRing T] [CommRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O]
    (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale φ →
    ∀ (q : ℕ), 0 < q → ∀ (D : Type) [CommRing D] [Algebra (GlobalTheory.LocAcyc.GenFib T O) D]
      (act : Multiplicative (ZMod q) →* (D ≃ₐ[GlobalTheory.LocAcyc.GenFib T O] D)),
      GlobalTheory.LocAcyc.IsZModTorsor (GlobalTheory.LocAcyc.GenFib T O) D q act →
    ∃ (E : Type) (_ : CommRing E) (_ : Algebra (Polynomial T) E) (_ : Algebra T E)
      (_ : IsScalarTower T (Polynomial T) E) (_ : Algebra.Etale (Polynomial T) E)
      (ψ : E →ₐ[Polynomial T] O) (DE : Type) (_ : CommRing DE)
      (_ : Algebra (GlobalTheory.LocAcyc.GenFib T E) DE)
      (actE : Multiplicative (ZMod q) →* (DE ≃ₐ[GlobalTheory.LocAcyc.GenFib T E] DE)),
      GlobalTheory.LocAcyc.IsZModTorsor (GlobalTheory.LocAcyc.GenFib T E) DE q actE ∧
      ∀ s : DE →+* GlobalTheory.LocAcyc.GenFib T O,
        (∀ e : E, s (algebraMap (GlobalTheory.LocAcyc.GenFib T E) DE (algebraMap E _ e)) =
          algebraMap O (GlobalTheory.LocAcyc.GenFib T O) (ψ e)) →
        Nonempty (D →ₐ[GlobalTheory.LocAcyc.GenFib T O] GlobalTheory.LocAcyc.GenFib T O) := GlobalTheory.T.spread_torsor_to_etale_algebra
private theorem exists_maximal_over_closedPt : ∀ (T E : Type) [CommRing T] [IsLocalRing T] [CommRing E] [Algebra (Polynomial T) E]
    [Algebra.FiniteType (Polynomial T) E] (Q : Ideal E) [Q.IsPrime],
    Q.comap (algebraMap (Polynomial T) E) =
      (IsLocalRing.maximalIdeal T).map (Polynomial.C : T →+* Polynomial T) →
    ∃ y : Ideal E, y.IsMaximal ∧ Q ≤ y ∧
      y.comap (algebraMap (Polynomial T) E) ≠
        (IsLocalRing.maximalIdeal T).map (Polynomial.C : T →+* Polynomial T) ∧
      (y.comap (algebraMap (Polynomial T) E)).comap (Polynomial.C : T →+* Polynomial T) =
        IsLocalRing.maximalIdeal T := GlobalTheory.T.exists_maximal_over_closedPoint_closedFibre
private theorem section_at_closedPt : GlobalTheory.LocAcyc.KeyClosedPts →
    ∀ (T E : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing E]
      [Algebra (Polynomial T) E] [Algebra T E] [IsScalarTower T (Polynomial T) E]
      [Algebra.Etale (Polynomial T) E], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (y : Ideal E) [y.IsPrime],
      (y.comap (algebraMap (Polynomial T) E)).comap (Polynomial.C : T →+* Polynomial T) =
        IsLocalRing.maximalIdeal T →
      y.comap (algebraMap (Polynomial T) E) ≠
        (IsLocalRing.maximalIdeal T).map (Polynomial.C : T →+* Polynomial T) →
    ∀ (q : ℕ), 0 < q → IsUnit (q : T) →
    ∀ (DE : Type) [CommRing DE] [Algebra (GlobalTheory.LocAcyc.GenFib T E) DE]
      (actE : Multiplicative (ZMod q) →* (DE ≃ₐ[GlobalTheory.LocAcyc.GenFib T E] DE)),
      GlobalTheory.LocAcyc.IsZModTorsor (GlobalTheory.LocAcyc.GenFib T E) DE q actE →
    ∃ (S : Type) (_ : CommRing S) (_ : IsLocalRing S) (_ : Algebra E S) (_ : Algebra T S)
      (_ : IsScalarTower T E S),
      (IsLocalRing.maximalIdeal S).comap (algebraMap E S) = y ∧ Module.Flat E S ∧
      GlobalTheory.LocAcyc.LocPiecesEtale E S ∧
      ∃ s : DE →+* GlobalTheory.LocAcyc.GenFib T S,
        ∀ e : E, s (algebraMap (GlobalTheory.LocAcyc.GenFib T E) DE (algebraMap E _ e)) =
          algebraMap S (GlobalTheory.LocAcyc.GenFib T S) (algebraMap E S e) := GlobalTheory.T.exists_section_strictHenselisation_closedFibre_point
private theorem specialisation_map : ∀ (R S O : Type) [CommRing R] [CommRing S] [IsLocalRing S] [CommRing O]
    [HenselianLocalRing O] [IsSepClosed (IsLocalRing.ResidueField O)] [Algebra R S] [Algebra R O]
    (Q y : Ideal R) [Q.IsPrime] [y.IsPrime], Q ≤ y →
    (IsLocalRing.maximalIdeal S).comap (algebraMap R S) = y →
    (IsLocalRing.maximalIdeal O).comap (algebraMap R O) = Q →
    Module.Flat R S → GlobalTheory.LocAcyc.LocPiecesEtale R S → Nonempty (S →ₐ[R] O) := GlobalTheory.T.exists_specialisation_to_strictlyHenselian

theorem keyGeneric_of_keyClosedPts : KeyClosedPts → KeyGeneric := by
  intro hC T O _ _ _ _ _ _ _ _ hAIC P _ φ hφ hSH hP hPeq q hq hqu
  rw [torsorsTrivial_iff]
  intro D _ _ act hD
  obtain ⟨E, _, _, _, _, _, ψ, DE, _, _, actE, hDE, hred⟩ := spread_torsor T O P φ hφ hSH.2.2.2 q hq D act hD

  set Q : Ideal E := (maximalIdeal O).comap ψ.toRingHom with hQdef
  haveI : Q.IsPrime := Ideal.comap_isPrime _ _
  have hloc : (maximalIdeal O).comap φ = maximalIdeal (Localization.AtPrime P) := by
    haveI := hSH.2.2.1
    apply le_antisymm
    · exact IsLocalRing.le_maximalIdeal (Ideal.comap_ne_top _ (Ideal.IsMaximal.ne_top inferInstance))
    · intro x hx
      rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      exact (IsLocalRing.mem_maximalIdeal _).1 hx (isUnit_of_map_unit φ x hu)
  have hQP : Q.comap (algebraMap (Polynomial T) E) = P := by
    rw [hQdef, Ideal.comap_comap]
    have h1 : ψ.toRingHom.comp (algebraMap (Polynomial T) E) = φ.comp (algebraMap (Polynomial T) _) := by
      rw [hφ]; exact ψ.comp_algebraMap
    rw [h1, ← Ideal.comap_comap, hloc]
    exact Localization.AtPrime.under_maximalIdeal (R := Polynomial T) (I := P)
  obtain ⟨y, hymax, hQy, hyne, hyT⟩ := exists_maximal_over_closedPt T E Q (hQP.trans hPeq)
  haveI : y.IsPrime := hymax.isPrime
  obtain ⟨S, _, _, _, _, _, hSy, hSflat, hSpieces, s, hs⟩ :=
    section_at_closedPt hC T E hAIC y hyT hyne q hq hqu DE actE hDE
  letI : Algebra E O := ψ.toRingHom.toAlgebra
  haveI : HenselianLocalRing O := hSH.1
  haveI : IsSepClosed (ResidueField O) := hSH.2.1
  obtain ⟨σ⟩ := specialisation_map E S O Q y hQy hSy rfl hSflat hSpieces
  have hσT : ∀ t : T, σ (algebraMap T S t) = algebraMap T O t := by
    intro t
    rw [IsScalarTower.algebraMap_apply T E S, σ.commutes, IsScalarTower.algebraMap_apply T (Polynomial T) E]
    change ψ (algebraMap (Polynomial T) E _) = _
    rw [ψ.commutes, ← IsScalarTower.algebraMap_apply]
  have hM : Algebra.algebraMapSubmonoid S (nonZeroDivisors T) ≤
      (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)).comap σ.toRingHom := by
    rintro _ ⟨t, ht, rfl⟩
    exact ⟨t, ht, (hσT t).symm⟩
  let m : GenFib T S →+* GenFib T O := IsLocalization.map (GenFib T O) σ.toRingHom hM
  refine hred (m.comp s) fun e => ?_
  rw [RingHom.comp_apply, hs e]
  simp only [m, IsLocalization.map_eq]
  change algebraMap O (GenFib T O) (σ (algebraMap E S e)) = _
  rw [σ.commutes]
  rfl

end GlobalTheory.LocAcyc
end
end
end
