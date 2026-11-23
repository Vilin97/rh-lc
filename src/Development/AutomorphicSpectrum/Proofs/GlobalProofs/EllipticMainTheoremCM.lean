module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
public import ReciprocityTheory.NeutralLocalFields.Reciprocity
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
public import ReciprocityTheory.ClassFieldTheory.GlobalClassField.AsGabLim
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArtinMapAbelianUnique
public import GroundTheory.GlobalFields.ComplexMultiplication.AnalyticUniformization
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsConjEqOnAlgebraicClosure
public import GroundTheory.GlobalFields.ComplexMultiplication.ClassGroupActionLattice
public import GroundTheory.GlobalFields.ComplexMultiplication.IdeleAction
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsAnalyticUniformizationOfIsAnalyticIso
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GalStarComplexMultiplicationPoints
public import GroundTheory.GlobalFields.ComplexMultiplication.ReductionMap
public import GroundTheory.GlobalFields.ComplexMultiplication.IdeleActionQuotient
public import GroundTheory.GlobalFields.ComplexMultiplication.MainTheorem

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AbelianizationEqOfForallAbRestrictEq

section

@[expose] public section

open NumberField
open scoped nonZeroDivisors
open scoped GlobalTheory.Idele

namespace GlobalTheory.CompanionTheory.GaloisAb

theorem abelianization_eq_of_forall_abRestrict_eq :
    ∀ (K : Type) [Field K] [NumberField K] (a b : Field.absoluteGaloisGroupAbelianization K),
      (∀ (L : IntermediateField K (AlgebraicClosure K)) (h : Neutral.B1.IsFiniteAbelian K L),
        Neutral.B1.abRestrict K L h a = Neutral.B1.abRestrict K L h b) → a = b := by
  intro K _ _ a b hab
  exact ReciprocityTheory.DiscreteGroups.GlobalClassField.abRestrict_ext hab

end GlobalTheory.CompanionTheory.GaloisAb
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArtinMapAbelianUniqueStatement

section

@[expose] public section

open NumberField
open scoped nonZeroDivisors
open scoped GlobalTheory.Idele

theorem _root_.GlobalTheory.T.artin_map_abelian_unique : ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (Art Art' : Neutral.B1.IdeleClassGroup K →* Field.absoluteGaloisGroupAbelianization K), Neutral.B1.IsGlobalArtinMap K Art → Neutral.B1.IsGlobalArtinMap K Art' → ∀ (L : IntermediateField K (AlgebraicClosure K)) (h : Neutral.B1.IsFiniteAbelian K L) (c : Neutral.B1.IdeleClassGroup K), Neutral.B1.abRestrict K L h (Art c) = Neutral.B1.abRestrict K L h (Art' c) := by
  first | exact @GlobalTheory.CompanionTheory.ArtinUniq.abRestrict_eq | exact GlobalTheory.CompanionTheory.ArtinUniq.abRestrict_eq | (intros; apply GlobalTheory.CompanionTheory.ArtinUniq.abRestrict_eq <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsAnalyticIsoOfIsAnalyticUniformization

section

@[expose] public section

open NumberField
open scoped nonZeroDivisors
open scoped GlobalTheory.Idele

noncomputable section

namespace GlobalTheory.CompanionTheory.EllipticUniformization

theorem exists_analyticIso_of_isAnalyticUniformization (Λ : Submodule ℤ ℂ)
    (E : WeierstrassCurve ℂ) (f : ℂ →+ E.toAffine.Point)
    (hf : GroundTheory.Global.Elliptic.IsAnalyticUniformization Λ f) :
    ∃ ξ : (ℂ ⧸ Λ.toAddSubgroup) ≃+ E.toAffine.Point,
      GlobalTheory.EllipticCM.IsAnalyticIso ξ ∧ ∀ z : ℂ, ξ (QuotientAddGroup.mk z) = f z := by
  let φ : (ℂ ⧸ Λ.toAddSubgroup) →+ E.toAffine.Point :=
    QuotientAddGroup.lift Λ.toAddSubgroup f fun z hz => (hf.map_eq_zero_iff z).2 hz
  have hφ : ∀ z : ℂ, φ (QuotientAddGroup.mk z) = f z := fun z => rfl
  have hinj : Function.Injective φ := by
    refine (injective_iff_map_eq_zero φ).2 fun x hx => ?_
    obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective x
    rw [hφ] at hx
    exact (QuotientAddGroup.eq_zero_iff z).2 ((hf.map_eq_zero_iff z).1 hx)
  have hsurj : Function.Surjective φ := fun P => by
    obtain ⟨z, rfl⟩ := hf.surjective P
    exact ⟨QuotientAddGroup.mk z, hφ z⟩
  let ξ : (ℂ ⧸ Λ.toAddSubgroup) ≃+ E.toAffine.Point :=
    AddEquiv.ofBijective φ ⟨hinj, hsurj⟩
  have hξ : ∀ z : ℂ, ξ (QuotientAddGroup.mk z) = f z := fun z => rfl
  refine ⟨ξ, fun z hz => ?_, hξ⟩
  have hz0 : f z ≠ 0 := fun h => hz ((hf.map_eq_zero_iff z).1 h)
  obtain ⟨X, Y, hX, hY, hev⟩ := hf.analyticAt_affine z hz0
  refine ⟨X, Y, hX, hY, hev.mono fun w hw => ?_⟩
  obtain ⟨h, hw⟩ := hw
  exact ⟨h, (hξ w).trans hw⟩

end GlobalTheory.CompanionTheory.EllipticUniformization
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdealLatticeToAddSubgroupEqIdealSub

section

@[expose] public section

open NumberField
open scoped nonZeroDivisors
open scoped GlobalTheory.Idele

namespace GlobalTheory.CompanionTheory.EllipticDict

theorem idealLattice_toAddSubgroup_eq_idealSub :
    ∀ {K : Type} [Field K] [NumberField K] [Algebra K ℂ] (I : FractionalIdeal (𝓞 K)⁰ K),
      (GroundTheory.Global.Elliptic.idealLattice (algebraMap K ℂ) I).toAddSubgroup =
        GlobalTheory.EllipticCM.idealSub I := by
  intro K _ _ _ I
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩

end GlobalTheory.CompanionTheory.EllipticDict
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InvSmulEqFinitePartInvSmul

section

@[expose] public section

open NumberField
open scoped nonZeroDivisors
open scoped GlobalTheory.Idele

namespace GlobalTheory.CompanionTheory.EllipticCM

theorem ord_eq_ord_vw_finitePart {K : Type} [Field K] [NumberField K]
    (s : GroundTheory.Global.IdeleGroup K) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    GroundTheory.Global.IdeleGroup.ord v s =
      GlobalTheory.Idele.ord_vw (GlobalTheory.EllipticCM.finitePart (K := K) s) v :=
  rfl

theorem coe_smul_eq_finitePart_smul {K : Type} [Field K] [NumberField K]
    (s : GroundTheory.Global.IdeleGroup K) (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ((s • 𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) =
      (GlobalTheory.EllipticCM.finitePart (K := K) s) • (𝔞 : FractionalIdeal (𝓞 K)⁰ K) := by
  refine GlobalTheory.Idele.eq_of_count_eq (Units.ne_zero _)
    (GlobalTheory.Idele.smul_ne_zero _ (Units.ne_zero _)) fun v => ?_
  rw [GroundTheory.Global.IdeleGroup.count_smul, GlobalTheory.Idele.count_smul _ (Units.ne_zero _),
    ord_eq_ord_vw_finitePart]

theorem inv_smul_eq_finitePart_inv_smul {K : Type} [Field K] [NumberField K]
    (s : GroundTheory.Global.IdeleGroup K) (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ((s⁻¹ • 𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) =
      (GlobalTheory.EllipticCM.finitePart (K := K) s)⁻¹ • (𝔞 : FractionalIdeal (𝓞 K)⁰ K) :=
  coe_smul_eq_finitePart_smul s⁻¹ 𝔞

end GlobalTheory.CompanionTheory.EllipticCM
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MapPointEqPointMapRing

section

@[expose] public section

open NumberField
open scoped nonZeroDivisors
open scoped GlobalTheory.Idele

namespace GlobalTheory.CompanionTheory.ConjPointDict

theorem mapPoint_eq_pointMapRing : ∀ [DecidableEq ℂ] (X : WeierstrassCurve ℂ) (σ : ℂ →+* ℂ)
    (P : X.toAffine.Point), GlobalTheory.ConjPoint.mapPoint X σ P = GroundTheory.Global.pointMapRing σ X P := by
  intro _ X σ P
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  · obtain ⟨h', e⟩ := GroundTheory.Global.pointMapRing_some σ X h
    rw [e]
    rfl

end GlobalTheory.CompanionTheory.ConjPointDict
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmulQuotientInvMkEqMkIffMulEquiv

section

@[expose] public section

open NumberField
open scoped nonZeroDivisors
open scoped GlobalTheory.Idele

namespace GlobalTheory.CompanionTheory.IdeleQuot

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

variable {K : Type} [Field K] [NumberField K]

theorem finitePart_apply (s : GroundTheory.Global.IdeleGroup K) (v : HeightOneSpectrum (𝓞 K)) :
    ((GlobalTheory.EllipticCM.finitePart (K := K) s : (FiniteAdeleRing (𝓞 K) K)ˣ) :
      FiniteAdeleRing (𝓞 K) K) v =
      (GroundTheory.Global.IdeleGroup.finiteProj v s : v.adicCompletion K) := by
  rw [GroundTheory.Global.IdeleGroup.coe_finiteProj]
  rfl

theorem finitePart_inv (s : GroundTheory.Global.IdeleGroup K) :
    GlobalTheory.EllipticCM.finitePart (K := K) s⁻¹ = (GlobalTheory.EllipticCM.finitePart (K := K) s)⁻¹ :=
  map_inv (Units.map (MonoidHom.snd (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K))) s

theorem ord_vw_finitePart (s : GroundTheory.Global.IdeleGroup K) (v : HeightOneSpectrum (𝓞 K)) :
    GlobalTheory.Idele.ord_vw (GlobalTheory.EllipticCM.finitePart (K := K) s) v =
      GroundTheory.Global.IdeleGroup.ord v s :=
  rfl

theorem coe_smul_eq_finitePart_smul (s : GroundTheory.Global.IdeleGroup K)
    (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ((s • 𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) =
      GlobalTheory.EllipticCM.finitePart (K := K) s • (𝔞 : FractionalIdeal (𝓞 K)⁰ K) :=
  GlobalTheory.Idele.eq_of_count_eq (Units.ne_zero _) (GlobalTheory.Idele.smul_ne_zero _ 𝔞.ne_zero) fun v => by
    rw [GroundTheory.Global.IdeleGroup.count_smul, GlobalTheory.Idele.count_smul _ 𝔞.ne_zero, ord_vw_finitePart]

theorem smulQuotient_inv_mk_eq_mk_iff_mulEquiv :
    ∀ {K : Type} [Field K] [NumberField K] (s : GroundTheory.Global.IdeleGroup K)
      (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x y : K),
      GroundTheory.Global.IdeleGroup.smulQuotient s⁻¹ 𝔞 (Submodule.Quotient.mk x) =
          Submodule.Quotient.mk y ↔
        GlobalTheory.Idele.mulEquiv (GlobalTheory.EllipticCM.finitePart (K := K) s)⁻¹ 𝔞.ne_zero rfl
          (Submodule.Quotient.mk x) = Submodule.Quotient.mk y := by
  intro K _ _ s 𝔞 x y
  rw [GroundTheory.Global.IdeleGroup.smulQuotient_mk_eq_mk_iff, GlobalTheory.Idele.mulEquiv_mk_eq_mk_iff]
  refine forall_congr' fun v => ?_
  rw [← finitePart_inv, finitePart_apply s⁻¹ v, coe_smul_eq_finitePart_smul]
  rfl

end GlobalTheory.CompanionTheory.IdeleQuot
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GlobalProofs.EllipticMainTheoremCM

section

@[expose] public section

open NumberField
open scoped nonZeroDivisors GlobalTheory.Idele

namespace GlobalTheory.CompanionTheory.Hypotheses₂

theorem ellipticMainTheoremCM : GlobalTheory.Published.EllipticMainTheoremCM := by
  classical
  intro K _ _ _ _ h2 Art hArt σ s hs X _ 𝔞 h𝔞 ξ hξ
  obtain ⟨Art₀, hArt₀, hlink⟩ := GlobalTheory.CompanionTheory.EllipticCM.exists_globalArtinMap_tied K h2
  have hEq : Art = Art₀ := MonoidHom.ext fun c =>
    GlobalTheory.CompanionTheory.GaloisAb.abelianization_eq_of_forall_abRestrict_eq K _ _ fun L h =>
      GlobalTheory.T.artin_map_abelian_unique K Art Art₀ hArt hArt₀ L h c
  subst hEq
  have hfound := hlink σ s hs
  let 𝔞u : (FractionalIdeal (𝓞 K)⁰ K)ˣ := Units.mk0 𝔞 h𝔞
  have hf := GlobalTheory.CompanionTheory.EllipticCM.isAnalyticUniformization_of_isAnalyticIso h2 X 𝔞 h𝔞 ξ hξ
  obtain ⟨f', ⟨hf', hrel⟩, -⟩ :=
    GroundTheory.Global.Elliptic.main_theorem_complexMultiplication h2 σ s hfound 𝔞u hf
  have hid : ((s⁻¹ • 𝔞u : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) =
      (GlobalTheory.EllipticCM.finitePart (K := K) s)⁻¹ • 𝔞 :=
    GlobalTheory.CompanionTheory.EllipticCM.inv_smul_eq_finitePart_inv_smul s 𝔞u
  rw [hid] at hf'
  have hex := GlobalTheory.CompanionTheory.EllipticUniformization.exists_analyticIso_of_isAnalyticUniformization _ _ f' hf'
  rw [GlobalTheory.CompanionTheory.EllipticDict.idealLattice_toAddSubgroup_eq_idealSub] at hex
  obtain ⟨ξ', hξ', hξf⟩ := hex
  refine GlobalTheory.EllipticCM.transports_of_exists h𝔞 rfl hξ' fun x => ?_
  obtain ⟨t, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _
    (GlobalTheory.Idele.mulEquiv (GlobalTheory.EllipticCM.finitePart (K := K) s)⁻¹ h𝔞 rfl (Submodule.Quotient.mk t))
  rw [← hy]
  have hq := (GlobalTheory.CompanionTheory.IdeleQuot.smulQuotient_inv_mk_eq_mk_iff_mulEquiv s 𝔞u t y).2 hy.symm
  have h3 := hrel t y hq
  rw [GlobalTheory.CompanionTheory.ConjPointDict.mapPoint_eq_pointMapRing, GlobalTheory.EllipticCM.torsionIncl_mk,
    GlobalTheory.EllipticCM.torsionIncl_mk, hξf, h3]
  rfl

end GlobalTheory.CompanionTheory.Hypotheses₂
end
end
