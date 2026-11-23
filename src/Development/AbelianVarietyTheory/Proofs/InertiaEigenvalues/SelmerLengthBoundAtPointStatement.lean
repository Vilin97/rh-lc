module

public import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Formalism.AdmissibleDesigns.KernelLengthHigherColumns
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CycZBridge
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.KrullDimension.PID
public import Mathlib.RingTheory.OrderOfVanishing.Basic
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthInvariantsLtTop
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalDualityClassFieldFactsOfArtinTateEulerStatement
public import Formalism.AdmissibleDesigns.StatementOneBFromUnramified

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteLengthInvariantsNegTwistKmodO

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.WeaklyAdmissibleFiltrations

noncomputable section

namespace GlobalTheory.FinInvKO

theorem isFiniteLength_of_killed {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {M : Type} [AddCommGroup M] [Module O M] [Module.Finite O M] {c : O}
    (hc : c ≠ 0) (h : ∀ x : M, c • x = 0) : IsFiniteLength O M := by
  have hfl := isFiniteLength_quotient_span_singleton O (mem_nonZeroDivisors_of_ne_zero hc)
  rw [isFiniteLength_iff_isNoetherian_isArtinian] at hfl ⊢
  refine ⟨inferInstance, ?_⟩
  have ht : Module.IsTorsionBySet O M (Ideal.span {c}) :=
    (Module.isTorsionBySet_span_singleton_iff c).mpr (fun x => h x)
  letI := ht.module
  haveI : IsScalarTower O (O ⧸ Ideal.span {c}) M := ht.isScalarTower
  haveI : IsArtinianRing (O ⧸ Ideal.span {c}) := isArtinian_of_tower O hfl.2
  haveI : Module.Finite (O ⧸ Ideal.span {c}) M := Module.Finite.of_restrictScalars_finite O _ _
  exact isArtinian_of_surjective_algebraMap (R := O ⧸ Ideal.span {c}) Ideal.Quotient.mk_surjective

theorem length_lt_top_of_killed {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (S : Submodule O (KmodO O)) {c : O} (hc : c ≠ 0) (h : ∀ x ∈ S, c • x = 0) :
    Module.length O S < ⊤ := by
  have hc' : algebraMap O (FractionRing O) c ≠ 0 := by
    simpa using (IsFractionRing.injective O (FractionRing O)).ne hc
  let x₀ : KmodO O := Submodule.Quotient.mk ((algebraMap O (FractionRing O) c)⁻¹)
  let ψ : O →ₗ[O] KmodO O := LinearMap.toSpanSingleton O _ x₀
  have hS : S ≤ LinearMap.range ψ := by
    intro x hx
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have h1 := h _ hx
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h1
    obtain ⟨a, ha⟩ := h1
    have ha' : algebraMap O (FractionRing O) a = algebraMap O (FractionRing O) c * y := by
      rw [← Algebra.smul_def]; exact ha
    refine ⟨a, ?_⟩
    simp only [ψ, LinearMap.toSpanSingleton_apply, x₀, ← Submodule.Quotient.mk_smul]
    congr 1
    rw [Algebra.smul_def, ha', mul_comm (algebraMap O (FractionRing O) c) y, mul_assoc,
      mul_inv_cancel₀ hc', mul_one]
  have hk : ∀ z : LinearMap.range ψ, c • z = 0 := by
    rintro ⟨_, a, rfl⟩
    ext1
    simp only [SetLike.val_smul, ψ, LinearMap.toSpanSingleton_apply, x₀, ← Submodule.Quotient.mk_smul,
      smul_smul, Submodule.coe_zero]
    rw [Submodule.Quotient.mk_eq_zero]
    refine ⟨a, ?_⟩
    rw [Algebra.linearMap_apply, Algebra.smul_def, map_mul, mul_comm (algebraMap O (FractionRing O) c), mul_assoc, mul_inv_cancel₀ hc', mul_one]
  have hfl := isFiniteLength_of_killed hc hk
  exact lt_of_le_of_lt (Module.length_le_of_injective (Submodule.inclusion hS) (Submodule.inclusion_injective hS))
    (lt_top_iff_ne_top.2 (Module.length_ne_top_iff.2 hfl))

theorem finiteLength_invariants_negTwist_KmodO : ∀ (D : D7) (i : D.nd.Loc), ∀ w ∈ placesOver D.host.E (D.nd.l i), ∀ e : ℕ, 0 < e →
    Module.length (D.nd.O i) ↥(Representation.invariants
      ((Formalism.MainNotions.N.Glob.KOtw D.nd i (e : ℤ)).comp (decS D.nd w))) < ⊤ := by
  intro D i w hw e he
  obtain ⟨g, hgI, hg⟩ := GlobalTheory.EpsInertia.epsAll D i w hw 1
  have hgD : g ∈ Dec (F := D.host.E) (D.nd.plOm.1 w) := hgI.1
  have hp : (D.nd.l i).Prime := (D.nd.lPrime i).out
  haveI : CharZero (FractionRing (D.nd.O i)) :=
    (D.nd.embK i).charZero_iff (D.nd.embK i).injective |>.1 inferInstance
  haveI : CharZero (D.nd.O i) := (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))).charZero
  have hle : 1 ≤ (1 + D.nd.l i ^ D.nd.s0 i) ^ e := Nat.one_le_pow _ _ (by omega)
  have hlt : 1 < (1 + D.nd.l i ^ D.nd.s0 i) ^ e :=
    Nat.one_lt_pow he.ne' (by have := pow_pos hp.pos (D.nd.s0 i); omega)
  have hc : (((1 + D.nd.l i ^ D.nd.s0 i) ^ e - 1 : ℕ) : D.nd.O i) ≠ 0 :=
    Nat.cast_ne_zero.2 (by omega)
  refine length_lt_top_of_killed _ hc fun v hv => ?_
  have h1 := hv ⟨g, hgD⟩
  change ((((Glob.epsO D.nd i) ^ (-(e : ℤ))) g : (D.nd.O i)ˣ) : D.nd.O i) • v = v at h1
  have hu : ((Glob.epsO D.nd i g : (D.nd.O i)ˣ) : D.nd.O i) = 1 + (D.nd.l i : D.nd.O i) ^ D.nd.s0 i := by
    simp [Glob.epsO, hg]
  have h2 : (((Glob.epsO D.nd i g) ^ e : (D.nd.O i)ˣ) : D.nd.O i) • v = v := by
    conv_lhs => rw [← h1]
    rw [smul_smul, ← Units.val_mul, MonoidHom.zpow_apply, ← zpow_natCast, ← zpow_add, add_neg_cancel,
      zpow_zero, Units.val_one, one_smul]
  rw [Nat.cast_sub hle, Nat.cast_one, sub_smul, one_smul, Nat.cast_pow, Nat.cast_add, Nat.cast_one,
    Nat.cast_pow, ← hu, ← Units.val_pow_eq_pow_val, h2, sub_self]

end GlobalTheory.FinInvKO
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelmerLengthBoundAtPoint

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.WeaklyAdmissibleFiltrations

namespace GlobalTheory.SelmerBoundAtPoint

theorem finCore : Formalism.MainNotions.N.K.H0.FinCore :=
  ⟨fun {D} i r ρ π g2 w hw => GlobalTheory.FiniteTwistInvariants.main D i r ρ π g2 w hw,
   fun {D} i w hw e he => GlobalTheory.FinInvKO.finiteLength_invariants_negTwist_KmodO D i w hw e he⟩




theorem main : GlobalTheory.Published.GlobalArtinReciprocity → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (dc : TruncatedSeriesCountingIdentities.Decl D i) (lenRow : HeightOneSpectrum (𝓞 D.host.E) → ℚ) (e' : HeightOneSpectrum (𝓞 D.host.E) → ℕ) (cB : ℕ), TruncatedSeriesCountingIdentities.admG1 i r → TruncatedSeriesCountingIdentities.admG2 i r ρ π → TruncatedSeriesCountingIdentities.admG3 i r ρ π → TruncatedSeriesCountingIdentities.admG4 i r → TruncatedSeriesCountingIdentities.admG5 i r → TruncatedSeriesCountingIdentities.TameGeneratorConditions i → TruncatedSeriesCountingIdentities.admG6 i r → TruncatedSeriesCountingIdentities.admBK i → LargeLevelLemmas.BlochKatoAnnihilators i → TruncatedSeriesCountingIdentities.FamilyContinuous i r → TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π → TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL i → LargeLevelLemmas.tateH1FinitenessAtPlacesOver i → TruncatedSeriesCountingIdentities.LocalCoefficientCompatibility i → LargeLevelLemmas.adm51 i r ρ π → EmbeddingTypes.UnramifiedTrivialH1f i dc → TruncatedSeriesCountingIdentities.LengthBoundAtPlaces i r ρ π dc lenRow → TruncatedSeriesCountingIdentities.LiftExponentAtPlaces i r dc e' → EmbeddingTypes.admTB i r π dc cB → TruncatedSeriesCountingIdentities.GlobalLatticeIndexTheorem i ρ π dc lenRow e' cB := by
  intro hA hT hE D i r ρ π dc lenRow e' cB g1 g2 g3 g4 g5 g5x g6 bk bka ct dcm font fin tie a51 unr hR hL hTB
  have : Fact ReciprocityTheory.ChartRestriction.T2.Core := ⟨GlobalTheory.T.local_duality_class_field_facts_of_artin_tate_euler hA hT hE⟩
  have : Fact Formalism.MainNotions.N.K.H0.FinCore := ⟨finCore⟩
  exact Formalism.MainNotions.N.K.Closed.theorem_n5_from_inputs i r ρ π dc lenRow e' cB g1 g2 g3 g4 g5 g5x g6 bk bka ct dcm font fin
    tie a51 (Formalism.MainNotions.N.K.StD.unramified_input_of_admitted i dc unr) hR hL hTB

end GlobalTheory.SelmerBoundAtPoint
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelmerLengthBoundAtPointStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.WeaklyAdmissibleFiltrations

theorem _root_.GlobalTheory.T.globalLatticeIndexTheorem_of_lengthBoundAtPlaces : GlobalTheory.Published.GlobalArtinReciprocity → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (dc : TruncatedSeriesCountingIdentities.Decl D i) (lenRow : HeightOneSpectrum (𝓞 D.host.E) → ℚ) (e' : HeightOneSpectrum (𝓞 D.host.E) → ℕ) (cB : ℕ), TruncatedSeriesCountingIdentities.admG1 i r → TruncatedSeriesCountingIdentities.admG2 i r ρ π → TruncatedSeriesCountingIdentities.admG3 i r ρ π → TruncatedSeriesCountingIdentities.admG4 i r → TruncatedSeriesCountingIdentities.admG5 i r → TruncatedSeriesCountingIdentities.TameGeneratorConditions i → TruncatedSeriesCountingIdentities.admG6 i r → TruncatedSeriesCountingIdentities.admBK i → LargeLevelLemmas.BlochKatoAnnihilators i → TruncatedSeriesCountingIdentities.FamilyContinuous i r → TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π → TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL i → LargeLevelLemmas.tateH1FinitenessAtPlacesOver i → TruncatedSeriesCountingIdentities.LocalCoefficientCompatibility i → LargeLevelLemmas.adm51 i r ρ π → EmbeddingTypes.UnramifiedTrivialH1f i dc → TruncatedSeriesCountingIdentities.LengthBoundAtPlaces i r ρ π dc lenRow → TruncatedSeriesCountingIdentities.LiftExponentAtPlaces i r dc e' → EmbeddingTypes.admTB i r π dc cB → TruncatedSeriesCountingIdentities.GlobalLatticeIndexTheorem i ρ π dc lenRow e' cB := by
  first | exact @GlobalTheory.SelmerBoundAtPoint.main | exact GlobalTheory.SelmerBoundAtPoint.main | (intros; apply GlobalTheory.SelmerBoundAtPoint.main <;> assumption)
end
end
