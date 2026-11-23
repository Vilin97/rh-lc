module

public import Development.AbelianVarietyTheory.Definitions.Divisors.PointShiftSt
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EigenvectorLieDegree
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniqueExtendRingOfIntegersHom
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.InjectiveOfSumEq
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieAlgebraEigenDecompositionCMSignature
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieLatticeFgAndSpanEqTopRingOfIntegers
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.NonemptyPolAVGenericFibreWithLieBasis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSelfDualLatticeCmHomomorphismsDefinite
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndexIdealMulConjEqGramDetSelfDualStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndexIdealRankOneTensorImageEqMap
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Basify
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSelfDualLatticeCmHomomorphismsDefiniteStatement

section

@[expose] public section

open NumberField

theorem _root_.GlobalTheory.T.exists_selfDual_lattice_cmHomomorphisms_definite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E),
    GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H → ∀ (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p : ℕ)
    (X : GlobalTheory.CM.CMObj H K ρ σ₁ p 0) (gP : Matrix (Fin p) (Fin p) (𝓞 E)) (gQ : Matrix (Fin 0) (Fin 0) (𝓞 E)),
    GlobalTheory.FlatCM.IsGram X gP gQ →
    ∃ Λ : Submodule (𝓞 E) (Fin p → E), Λ.FG ∧ (∀ x : Fin p → 𝓞 E, (fun a => (x a : E)) ∈ Λ) ∧
      (∀ barE : E →+* E, (∀ x : 𝓞 E, barE x = ((H.bar x : 𝓞 E) : E)) →
        ∀ d : Fin p → E, d ∈ Λ ↔ ∀ c ∈ Λ, ∃ y : 𝓞 E, (y : E) = ∑ a, ∑ b, c a * (gP a b : E) * barE (d b)) ∧
      ∀ (FP : GlobalTheory.CM.GenFib (X.A true).pol) (FB : GlobalTheory.CM.GenFib X.B.pol)
        (MP : Fin p → ((Fin FP.P₀.g → K) →ₗ[K] (Fin FB.P₀.g → K))),
        (∀ a, FP.IsDiffOf FB (GlobalTheory.FlatCM.phiP X a) (MP a)) →
        ∀ τ : 𝓞 E →+* 𝓞 K, τ H.rt = ρ → ∀ τE : E →+* K, (∀ x : 𝓞 E, τE x = ((τ x : 𝓞 K) : K)) →
          FB.eigLat X.B.t.act τ = Submodule.span (𝓞 K)
            {w | ∃ c ∈ Λ, ∃ e ∈ FP.eigLat (X.A true).t.act τ, w = ∑ a, τE (c a) • MP a e} := by
  first | exact @GlobalTheory.FlatCM.HomLat.exists_selfDual_lieSpan | exact GlobalTheory.FlatCM.HomLat.exists_selfDual_lieSpan | (intros; apply GlobalTheory.FlatCM.HomLat.exists_selfDual_lieSpan <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndexIdealRankOneTensorImageEqMapStatement

section

@[expose] public section

open NumberField

theorem _root_.GlobalTheory.T.indexIdeal_rankOne_tensor_image_eq_map : ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] (τ : 𝓞 E →+* 𝓞 K) (τE : E →+* K),
    (∀ x : 𝓞 E, τE x = ((τ x : 𝓞 K) : K)) → ∀ (p m n : ℕ) (ell : Submodule (𝓞 K) (Fin m → K))
    (M : Fin p → ((Fin m → K) →ₗ[K] (Fin n → K))) (Λ : Submodule (𝓞 E) (Fin p → E)),
    ell.FG → ReciprocityTheory.GeometryOfNumbersTheory.latRank K ell = 1 → (∀ a, Function.Injective (M a)) →
    iSupIndep (fun a => Submodule.span K ((ell.map ((M a).restrictScalars (𝓞 K)) : Submodule (𝓞 K) (Fin n → K)) : Set (Fin n → K))) →
    Λ.FG → (∀ x : Fin p → 𝓞 E, (fun a => (x a : E)) ∈ Λ) →
    GlobalTheory.FlatCM.idx K p (Submodule.span (𝓞 K) {w | ∃ c ∈ Λ, ∃ e ∈ ell, w = ∑ a, τE (c a) • M a e})
                 (⨆ a, ell.map ((M a).restrictScalars (𝓞 K))) =
      (GlobalTheory.FlatCM.idx E p Λ (Submodule.span (𝓞 E) (Set.range fun a => (Pi.single a (1 : E) : Fin p → E)))).map τ := by
  first | exact @GlobalTheory.IdxTensor.idx_image_eq_map | exact GlobalTheory.IdxTensor.idx_image_eq_map | (intros; apply GlobalTheory.IdxTensor.idx_image_eq_map <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmDefiniteLieIndexIdealEqNormIdeal

section

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory GlobalTheory.CM GlobalTheory.FlatCM

noncomputable section

namespace GlobalTheory.FlatCM.IdealZero

theorem idealSt_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E),
    GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H → ∀ (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p : ℕ)
    (X : GlobalTheory.CM.CMObj H K ρ σ₁ p 0) (gP : Matrix (Fin p) (Fin p) (𝓞 E)) (gQ : Matrix (Fin 0) (Fin 0) (𝓞 E)),
    GlobalTheory.FlatCM.IsGram X gP gQ →
    ∃ 𝔫 : Ideal (𝓞 E), 𝔫 * 𝔫.map (H.bar : 𝓞 E →+* 𝓞 E) = Ideal.span {gP.det} ∧
      ∀ (FP : GlobalTheory.CM.GenFib (X.A true).pol) (FB : GlobalTheory.CM.GenFib X.B.pol)
        (MP : Fin p → ((Fin FP.P₀.g → K) →ₗ[K] (Fin FB.P₀.g → K))),
        (∀ a, FP.IsDiffOf FB (GlobalTheory.FlatCM.phiP X a) (MP a)) →
        ∀ τ : 𝓞 E →+* 𝓞 K, τ H.rt = ρ →
          GlobalTheory.FlatCM.idx K p (FB.eigLat X.B.t.act τ) (GlobalTheory.FlatCM.subP FP FB MP τ) = 𝔫.map τ := by
  intro E _ _ _ H hH K _ _ ρ σ₁ p X gP gQ hg
  obtain ⟨Λ, hfg, hstd, hdual, hdesc⟩ := GlobalTheory.T.exists_selfDual_lattice_cmHomomorphisms_definite E H hH K ρ σ₁ p X gP gQ hg
  have hbinj : Function.Injective ((algebraMap (𝓞 E) E).comp (H.bar : 𝓞 E →+* 𝓞 E)) :=
    (RingOfIntegers.coe_injective (K := E)).comp (GlobalTheory.CM.ringOfIntegers_hom_injective _)
  let barE : E →+* E := IsFractionRing.lift hbinj
  have hbarE : ∀ x : 𝓞 E, barE x = ((H.bar x : 𝓞 E) : E) := fun x => IsFractionRing.lift_algebraMap hbinj x
  refine ⟨_, GlobalTheory.T.index_ideal_mul_conj_eq_gram_det_selfDual E _ barE hbarE p gP Λ hfg hstd (hdual barE hbarE), ?_⟩
  intro FP FB MP hMP τ hτ
  have hτinj : Function.Injective ((algebraMap (𝓞 K) K).comp τ) :=
    (RingOfIntegers.coe_injective (K := K)).comp (GlobalTheory.CM.ringOfIntegers_hom_injective _)
  let τE : E →+* K := IsFractionRing.lift hτinj
  have hτE : ∀ x : 𝓞 E, τE x = ((τ x : 𝓞 K) : K) := fun x => IsFractionRing.lift_algebraMap hτinj x
  classical
  let FA : ∀ b, GenFib (X.A b).pol := fun b => match b with
    | true => FP
    | false => (GenFib.nonempty_of_baseChange GlobalTheory.polBaseChange_holds K (X.A false).pol).some
  let M : ∀ k : Fin p ⊕ Fin 0, (Fin (FA k.isLeft).P₀.g → K) →ₗ[K] (Fin FB.P₀.g → K) := fun k => match k with
    | .inl a => MP a
    | .inr a => a.elim0
  obtain ⟨-, -, hinj, hind, -⟩ :=
    GlobalTheory.CM.Indep.letters_independent GlobalTheory.thetaUnifAV_all GlobalTheory.abelianSchemeLaws_all.1 E H K ρ σ₁ p 0 X FA FB M
      (fun k => match k with
        | .inl a => hMP a
        | .inr a => a.elim0)
  have hfgA : (FP.eigLat (X.A true).t.act τ).FG :=
    Submodule.FG.of_le (LieLattice.lieLat_fg_and_span_eq_top K _ FP).1
      (Submodule.span_mono fun c ⟨u, hu, _⟩ => ⟨u, hu⟩)
  have hrk : latRank K (FP.eigLat (X.A true).t.act τ) = 1 := by
    rw [(GlobalTheory.CM.EigDec.eigen_decomposition E H K ρ (X.A true) FP 1 0 X.split X.typeP X.ρ_sq).1 τ, if_pos hτ]
  rw [subP, hdesc FP FB MP hMP τ hτ τE hτE]
  exact GlobalTheory.T.indexIdeal_rankOne_tensor_image_eq_map E K τ τE hτE p _ _ _ MP Λ hfgA hrk (fun a => hinj (.inl a))
    (iSupIndep.comp hind (f := fun a : Fin p => ((Sum.inl a : Fin p ⊕ Fin 0), τ)) fun a b e => by simpa using e)
    hfg hstd

end GlobalTheory.FlatCM.IdealZero

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmDefiniteLieIndexIdealEqNormIdealStatement

section

@[expose] public section

open NumberField

theorem _root_.GlobalTheory.T.cmDefinite_lieIndex_ideal_eq_norm_ideal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E),
    GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H → ∀ (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p : ℕ)
    (X : GlobalTheory.CM.CMObj H K ρ σ₁ p 0) (gP : Matrix (Fin p) (Fin p) (𝓞 E)) (gQ : Matrix (Fin 0) (Fin 0) (𝓞 E)),
    GlobalTheory.FlatCM.IsGram X gP gQ →
    ∃ 𝔫 : Ideal (𝓞 E), 𝔫 * 𝔫.map (H.bar : 𝓞 E →+* 𝓞 E) = Ideal.span {gP.det} ∧
      ∀ (FP : GlobalTheory.CM.GenFib (X.A true).pol) (FB : GlobalTheory.CM.GenFib X.B.pol)
        (MP : Fin p → ((Fin FP.P₀.g → K) →ₗ[K] (Fin FB.P₀.g → K))),
        (∀ a, FP.IsDiffOf FB (GlobalTheory.FlatCM.phiP X a) (MP a)) →
        ∀ τ : 𝓞 E →+* 𝓞 K, τ H.rt = ρ →
          GlobalTheory.FlatCM.idx K p (FB.eigLat X.B.t.act τ) (GlobalTheory.FlatCM.subP FP FB MP τ) = 𝔫.map τ := by
  first | exact @GlobalTheory.FlatCM.IdealZero.idealSt_zero | exact GlobalTheory.FlatCM.IdealZero.idealSt_zero | (intros; apply GlobalTheory.FlatCM.IdealZero.idealSt_zero <;> assumption)
end
end
