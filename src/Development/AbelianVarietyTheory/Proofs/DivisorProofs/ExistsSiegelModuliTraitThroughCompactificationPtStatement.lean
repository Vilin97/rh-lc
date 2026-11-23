module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitExistsAfterFiniteExtensionOfCompleteDVRStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
public import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Properties
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
import Mathlib.Order.CompletePartialOrder
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Degenerations.MorAlgSt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import ReciprocityTheory.AnalyticForms.RegularLocalRings.JacChartA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl
import Mathlib.Tactic.Linter.Style
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMinAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormalizationBlowupIsIsoDense

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

noncomputable section

namespace GlobalTheory.BlowOpen

theorem exists_specializes_of_dense {X : Type} [TopologicalSpace X] [QuasiSober X] [NoetherianSpace X] (S : Set X)
    (hSo : IsOpen S) (hSd : Dense S) (x : X) : ∃ w ∈ S, w ⤳ x := by
  classical
  have hC := irreducibleComponent_mem_irreducibleComponents x
  have hCi : IsIrreducible (irreducibleComponent x) := isIrreducible_irreducibleComponent
  have hCc : IsClosed (irreducibleComponent x) := isClosed_of_mem_irreducibleComponents _ hC
  have hη : IsGenericPoint hCi.genericPoint (irreducibleComponent x) := by
    simpa [hCc.closure_eq] using hCi.isGenericPoint_genericPoint_closure
  let F := ⋃ C' ∈ (irreducibleComponents X \ {irreducibleComponent x}), C'
  have hFc : IsClosed F := (NoetherianSpace.finite_irreducibleComponents.diff).isClosed_biUnion
    (fun C' h => isClosed_of_mem_irreducibleComponents C' h.1)
  have hηF : hCi.genericPoint ∉ F := by
    simp only [F, Set.mem_iUnion]
    rintro ⟨C', ⟨hC', hne⟩, hηC'⟩
    have hsub : irreducibleComponent x ⊆ C' := fun y hy =>
      (hη.specializes hy).mem_closed (isClosed_of_mem_irreducibleComponents C' hC') hηC'
    exact hne (Set.mem_singleton_iff.2 (hC.eq_of_le hC'.1 hsub).symm)
  obtain ⟨w, hwF, hwS⟩ := hSd.inter_open_nonempty Fᶜ hFc.isOpen_compl ⟨_, hηF⟩
  have hwC : w ∈ irreducibleComponent x := by
    by_contra h
    apply hwF
    simp only [F, Set.mem_iUnion]
    refine ⟨irreducibleComponent w, ⟨irreducibleComponent_mem_irreducibleComponents w, fun e => h ?_⟩,
      mem_irreducibleComponent⟩
    rw [← Set.mem_singleton_iff.1 e]; exact mem_irreducibleComponent
  exact ⟨_, (hη.specializes hwC).mem_open hSo hwS, hη.specializes mem_irreducibleComponent⟩

theorem exists_specializes_of_dense_scheme (N : Scheme.{0}) [IsLocallyNoetherian N] (W : Set N) (hWo : IsOpen W)
    (hWd : Dense W) (n : N) : ∃ w ∈ W, w ⤳ n := by
  obtain ⟨_, ⟨O, hO, rfl⟩, hnO, -⟩ := N.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ n) isOpen_univ
  haveI : IsNoetherianRing Γ(N, O) := IsLocallyNoetherian.component_noetherian ⟨O, hO⟩
  obtain ⟨w, hw, hwn⟩ := @exists_specializes_of_dense (O : Set N) _ O.isOpen.isOpenEmbedding_subtypeVal.quasiSober
    (noetherianSpace_of_isAffineOpen O hO) (Subtype.val ⁻¹' W : Set (O : Set N)) (hWo.preimage continuous_subtype_val)
    (hWd.preimage O.isOpen.isOpenMap_subtype_val) ⟨n, hnO⟩
  exact ⟨w, hw, hwn.map continuous_subtype_val⟩

end GlobalTheory.BlowOpen
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelModuliTraitThroughCompactificationPt

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.TChart

theorem exists_complete_dvr_of_local (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] :
    ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W)
      (_ : IsAdicComplete (maximalIdeal W) W) (ψ : A →+* W), Function.Injective ψ ∧ IsLocalHom ψ := by
  by_cases h : IsField A
  · letI := h.toField
    refine ⟨PowerSeries A, inferInstance, inferInstance, inferInstance, ?_, PowerSeries.C,
      RingHom.injective _, inferInstance⟩
    rw [PowerSeries.maximalIdeal_eq_span_X]; infer_instance
  · obtain ⟨O, _, _, _, _, φ, h1, h2⟩ := GlobalTheory.exists_complete_discreteValuationRing_dominating A h
    exact ⟨O, inferInstance, inferInstance, inferInstance, inferInstance, φ, h1, h2⟩

theorem exists_trait_at : ∀ {g n : ℕ} (F : SFam g n (zetaAway n)) (S : Scheme.{0}) (s : S ⟶ Sp (cycAway n))
    [LocallyOfFiniteType s] [IsLocallyNoetherian S] (j : F.X ⟶ S) [IsOpenImmersion j], 3 ≤ n → Dense (Set.range j) →
    j ≫ s = F.s → ∀ x : S, ∃ (T : GlobalTheory.Poinc.Trait F) (ξT : Sp T.V ⟶ S) (b : cycAway n →+* T.V),
      ξT (closedPoint T.V) = x ∧ jK T.V ≫ ξT = T.y ≫ j ∧ ξT ≫ s = spMap b := by
  intro g n F S s _ _ j _ _ hd hjs x
  haveI := F.smooth
  haveI : Smooth F.s := SmoothOfRelativeDimension.smooth (g * (g + 1) / 2) F.s
  haveI : Flat F.s := inferInstance
  obtain ⟨_, ⟨y0, rfl⟩, hw⟩ :=
    GlobalTheory.BlowOpen.exists_specializes_of_dense_scheme S _ j.isOpenEmbedding.isOpen_range hd x
  obtain ⟨y1, hy1, e1⟩ := Flat.generalizingMap F.s (genericPoint_specializes (F.s y0))
  have hη : j y1 ⤳ x := (hy1.map j.continuous).trans hw
  obtain ⟨q, hq⟩ : j y1 ∈ Set.range (S.fromSpecStalk x) := by rw [Scheme.range_fromSpecStalk]; exact hη
  haveI : q.asIdeal.IsPrime := q.isPrime
  haveI : IsLocalRing (S.presheaf.stalk x ⧸ q.asIdeal) := .of_surjective' _ Ideal.Quotient.mk_surjective
  obtain ⟨W, _, _, _, hWc, ψ, hψi, hψl⟩ := exists_complete_dvr_of_local (S.presheaf.stalk x ⧸ q.asIdeal)
  haveI : IsLocalHom (Ideal.Quotient.mk q.asIdeal) := .of_surjective _ Ideal.Quotient.mk_surjective
  let ψ' : S.presheaf.stalk x →+* W := ψ.comp (Ideal.Quotient.mk q.asIdeal)
  haveI : IsLocalHom ψ' := RingHom.isLocalHom_comp _ _
  let ξ0 : Sp W ⟶ S := spMap ψ' ≫ S.fromSpecStalk x
  have hξc : ξ0 (closedPoint W) = x := by
    show S.fromSpecStalk x (spMap ψ' (closedPoint W)) = x
    have e : spMap ψ' (closedPoint W) = closedPoint (S.presheaf.stalk x) := IsLocalRing.comap_closedPoint ψ'
    rw [e]
    exact Scheme.fromSpecStalk_closedPoint
  have hξg : ξ0 (⊥ : PrimeSpectrum W) = j y1 := by
    show S.fromSpecStalk x (spMap ψ' (⊥ : PrimeSpectrum W)) = j y1
    have : spMap ψ' (⊥ : PrimeSpectrum W) = q := by
      apply PrimeSpectrum.ext
      show Ideal.comap ψ' ⊥ = q.asIdeal
      rw [← RingHom.ker_eq_comap_bot, RingHom.ker_comp_of_injective _ hψi, Ideal.mk_ker]
    rw [this, hq]
  have hjKbot : ∀ pt : Sp (FractionRing W), jK W pt = (⊥ : PrimeSpectrum W) := fun pt => by
    apply PrimeSpectrum.ext
    have hpt : pt = (⊥ : PrimeSpectrum (FractionRing W)) := Subsingleton.elim (α := PrimeSpectrum (FractionRing W)) _ _
    subst hpt
    show Ideal.comap (algebraMap W (FractionRing W)) ⊥ = ⊥
    exact (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective W (FractionRing W))
  have hrange : Set.range (jK W ≫ ξ0) ⊆ Set.range j := by
    rintro _ ⟨pt, rfl⟩
    rw [Scheme.Hom.comp_apply, hjKbot, hξg]
    exact ⟨y1, rfl⟩
  let y : Sp (FractionRing W) ⟶ F.X := IsOpenImmersion.lift j (jK W ≫ ξ0) hrange
  have hy : y ≫ j = jK W ≫ ξ0 := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨θ, hθ⟩ := Spec.map_surjective (ξ0 ≫ s)
  let b0 : cycAway n →+* W := θ.hom
  have hb0 : spMap b0 = ξ0 ≫ s := hθ
  have hb0i : Function.Injective b0 := by
    have h1 : (spMap b0) (⊥ : PrimeSpectrum W) = genericPoint (Sp (cycAway n)) := by
      rw [hb0]
      exact (Scheme.Hom.comp_apply ξ0 s _).trans (by rw [hξg, ← Scheme.Hom.comp_apply, hjs, e1])
    rw [genericPoint_eq_bot_of_affine] at h1
    rw [RingHom.injective_iff_ker_eq_bot, RingHom.ker_eq_comap_bot]
    exact congrArg PrimeSpectrum.asIdeal h1
  haveI : CharZero W := charZero_of_injective_ringHom hb0i
  have hBase : GlobalTheory.Mum.Base W := ⟨⟨inferInstance, inferInstance, inferInstance, hWc⟩, inferInstance⟩
  obtain ⟨T, f, fK, -, hfl, -, hcomp, hTy⟩ := GlobalTheory.T.traitExistsAfterFiniteExtension_of_completeDVR g n (cycAway n) (zetaAway n) F W hBase inferInstance y
  haveI := hfl
  refine ⟨T, spMap f ≫ ξ0, f.comp b0, ?_, ?_, ?_⟩
  · show ξ0 (spMap f (closedPoint T.V)) = x
    have e : spMap f (closedPoint T.V) = closedPoint W := IsLocalRing.comap_closedPoint f
    rw [e, hξc]
  · have key : jK T.V ≫ spMap f = spMap fK ≫ jK W := by
      simp only [jK, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 2
      ext a
      exact (hcomp a).symm
    rw [hTy, Category.assoc, hy, ← Category.assoc, key, Category.assoc]
  · rw [Category.assoc, ← hb0]
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

end GlobalTheory.TChart
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelModuliTraitThroughCompactificationPtStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_siegelModuli_trait_through_compactification_pt : ∀ {g n : ℕ} (F : SFam g n (zetaAway n)) (S : Scheme.{0}) (s : S ⟶ Sp (cycAway n)) [LocallyOfFiniteType s] [IsLocallyNoetherian S] (j : F.X ⟶ S) [IsOpenImmersion j], 3 ≤ n → Dense (Set.range j) → j ≫ s = F.s → ∀ x : S, ∃ (T : GlobalTheory.Poinc.Trait F) (ξT : Sp T.V ⟶ S) (b : cycAway n →+* T.V), ξT (closedPoint T.V) = x ∧ jK T.V ≫ ξT = T.y ≫ j ∧ ξT ≫ s = spMap b := by
  first | exact @GlobalTheory.TChart.exists_trait_at | exact GlobalTheory.TChart.exists_trait_at | (intros; apply GlobalTheory.TChart.exists_trait_at <;> assumption)
end
end
