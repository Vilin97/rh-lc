module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsTjCorrDiagModel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPIsogPull
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullbackKernelOfKernelPair
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtensionOverNormalQuasiProjectiveBaseStatement
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.QuasiAffine
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Tactic.Linter.Style
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsTjCorrDiagModel
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompEqOneOfTransl
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePointsClosureGenericCorrespondenceFstStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePointsClosureGenericCorrespondenceSndStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorCorrespondenceExtendSourceDvrStatement
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsIsoStalkMapOfFlatOfSurjectiveOnStalks
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProperOfCompleteDVRLiftGeneric
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsQProjOverCompOfIsFiniteNoetherianBase
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsReducedNormalModelGenericCorrespondence
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDvrExtensionTargetGenericCorrespondence

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

namespace GlobalTheory.UPel.HT.ES.ValExt

theorem exists_ext_target : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CharZero R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → (p : R) ∈ IsLocalRing.maximalIdeal R → ∀ (r : ℤ) (w : Ideal (𝓞 D.F)) (j c : ℕ), w.IsMaximal → uIdeal D r ≤ w → j ≤ D.n → (∃ e : ℕ, c = p ^ e ∧ (0 < j → 0 < e)) → D.m = 1 → ∀ M : Model b N, ∀ (Y₀ : Scheme.{0}) (s₀ t₀ : Y₀ ⟶ M.X) (gs gt : Y₀ ⟶ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).toScheme) (o₀ o₀' : Obj b N (s₀ ≫ M.s)) (ms₀ : ObjMap o₀ M.univ s₀) (mt₀ : ObjMap o₀' M.univ t₀) (ψ₀ : o₀.A ⟶ o₀'.A), s₀ ≫ M.s = t₀ ≫ M.s → gs ≫ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).ι = s₀ → gt ≫ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).ι = t₀ → IsFinite gs → Etale gs → IsFinite gt → Etale gt → IsPIsog c o₀ o₀' ψ₀ → IsTj r w j o₀ o₀' ψ₀ → ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (y : Sp V ⟶ M.X) (x : Sp K ⟶ Y₀), spMap (algebraMap V K) ≫ y = x ≫ s₀ → ∃ z : Sp V ⟶ M.X, spMap (algebraMap V K) ≫ z = x ≫ t₀ :=
  of_ext GlobalTheory.UPel.HT.ES.IsogDVR.exists_isPIsog_extend_dvr

end GlobalTheory.UPel.HT.ES.ValExt
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDvrExtensionTargetGenericCorrespondenceStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

theorem _root_.GlobalTheory.T.exists_dvr_extension_target_generic_correspondence : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CharZero R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → (p : R) ∈ IsLocalRing.maximalIdeal R → ∀ (r : ℤ) (w : Ideal (𝓞 D.F)) (j c : ℕ), w.IsMaximal → uIdeal D r ≤ w → j ≤ D.n → (∃ e : ℕ, c = p ^ e ∧ (0 < j → 0 < e)) → D.m = 1 → ∀ M : Model b N, ∀ (Y₀ : Scheme.{0}) (s₀ t₀ : Y₀ ⟶ M.X) (gs gt : Y₀ ⟶ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).toScheme) (o₀ o₀' : Obj b N (s₀ ≫ M.s)) (ms₀ : ObjMap o₀ M.univ s₀) (mt₀ : ObjMap o₀' M.univ t₀) (ψ₀ : o₀.A ⟶ o₀'.A), s₀ ≫ M.s = t₀ ≫ M.s → gs ≫ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).ι = s₀ → gt ≫ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).ι = t₀ → IsFinite gs → Etale gs → IsFinite gt → Etale gt → IsPIsog c o₀ o₀' ψ₀ → IsTj r w j o₀ o₀' ψ₀ → ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (y : Sp V ⟶ M.X) (x : Sp K ⟶ Y₀), spMap (algebraMap V K) ≫ y = x ≫ s₀ → ∃ z : Sp V ⟶ M.X, spMap (algebraMap V K) ≫ z = x ≫ t₀ := by
  first | (exact @GlobalTheory.UPel.HT.ES.ValExt.exists_ext_target) | (exact GlobalTheory.UPel.HT.ES.ValExt.exists_ext_target) | (intros; apply GlobalTheory.UPel.HT.ES.ValExt.exists_ext_target  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFibreCorrespondenceOfIsFiniteFirst

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

namespace GlobalTheory.FibreCrit

theorem exists_generization_mem {Y : Scheme.{0}} [IsLocallyNoetherian Y] {O : Set Y} (hO : IsOpen O)
    (hd : Dense O) (y : Y) : ∃ e0 : Y, e0 ⤳ y ∧ e0 ∈ O := by
  obtain ⟨U, hU, hyU, -⟩ := exists_isAffineOpen_mem_and_subset (X := Y) (U := ⊤) (x := y) trivial
  have : IsAffine U := hU
  have : IsNoetherian U.toScheme := {}
  obtain ⟨y', rfl⟩ : y ∈ Set.range U.ι := by rw [Scheme.Opens.range_ι]; exact hyU
  have hC := irreducibleComponent_mem_irreducibleComponents y'
  obtain ⟨o, ho, hne, hoC⟩ :=
    TopologicalSpace.NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent _ hC
  obtain ⟨_, ⟨w, hwo, rfl⟩, hwO⟩ :=
    hd.inter_open_nonempty _ (U.ι.isOpenEmbedding.isOpenMap _ ho) (hne.image _)
  have hg := hC.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ hC)
  exact ⟨U.ι hC.1.genericPoint, (hg.specializes mem_irreducibleComponent).map U.ι.continuous,
    ((hg.specializes (hoC hwo)).map U.ι.continuous).mem_open hO hwO⟩

theorem spMap_algebraMap_apply (V K : Type) [CommRing V] [IsDomain V] [Field K] [Algebra V K]
    [IsFractionRing V K] (p : Sp K) : spMap (algebraMap V K) p = (⊥ : PrimeSpectrum V) := by
  refine PrimeSpectrum.ext ?_
  show Ideal.comap (algebraMap V K) p.asIdeal = ⊥
  rw [(Ideal.eq_bot_or_top p.asIdeal).resolve_right p.isPrime.ne_top, ← RingHom.ker_eq_comap_bot]
  exact (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective V K)

end GlobalTheory.FibreCrit

namespace GlobalTheory.FibreCrit

theorem finite_fibre_of_isFinite : ∀ (X Y₀ Y : Scheme.{0}) (s t : Y ⟶ X) (i : Y₀ ⟶ Y), IsFinite s → IsOpenImmersion i → IsDominant i → IsLocallyNoetherian Y → (∀ z : X, {u : X | ∃ (V K : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : Field K) (_ : Algebra V K) (_ : IsFractionRing V K) (y' z' : Sp V ⟶ X) (x : Sp K ⟶ Y₀), spMap (algebraMap V K) ≫ y' = x ≫ i ≫ s ∧ spMap (algebraMap V K) ≫ z' = x ≫ i ≫ t ∧ y' (IsLocalRing.closedPoint V) = u ∧ z' (IsLocalRing.closedPoint V) = z}.Finite) → ∀ z : X, {y : Y | t y = z}.Finite := by
  intro X Y₀ Y s t i hs hi hd hY hfin z
  refine (s.finite_preimage (hfin z)).subset ?_
  intro y hy
  simp only [Set.mem_ofPred_eq] at hy
  obtain ⟨e0, he0y, he0i⟩ := exists_generization_mem i.isOpenEmbedding.isOpen_range i.denseRange y
  obtain ⟨V, _, _, _, g, hg0, hg1⟩ : ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V)
      (_ : IsDiscreteValuationRing V) (g : Sp V ⟶ Y),
      g (⊥ : PrimeSpectrum V) ∈ Set.range i ∧ g (IsLocalRing.closedPoint V) = y := by
    by_cases he : e0 = y
    · subst he
      have hpt : ∀ q, (spMap (algebraMap (Y.residueField e0) (PowerSeries (Y.residueField e0))) ≫
          Y.fromSpecResidueField e0) q = e0 := fun q => by
        have h := Set.mem_range_self (f := Y.fromSpecResidueField e0)
          (spMap (algebraMap (Y.residueField e0) (PowerSeries (Y.residueField e0))) q)
        rw [Scheme.range_fromSpecResidueField] at h
        rw [Scheme.Hom.comp_apply]
        exact h
      exact ⟨PowerSeries (Y.residueField e0), inferInstance, inferInstance, inferInstance,
        spMap (algebraMap (Y.residueField e0) (PowerSeries (Y.residueField e0))) ≫
          Y.fromSpecResidueField e0, (hpt _).symm ▸ he0i, hpt _⟩
    · obtain ⟨O, hO, hV, -, f, hf0, hf1⟩ :=
        GlobalTheory.exists_complete_discreteValuationRing_of_specializes he0y he
      exact ⟨O, inferInstance, hO, hV, f, hf0 ▸ he0i, hf1⟩
  have hr : Set.range (spMap (algebraMap V (FractionRing V)) ≫ g) ⊆ Set.range i := by
    rintro _ ⟨q, rfl⟩
    rw [Scheme.Hom.comp_apply, spMap_algebraMap_apply V (FractionRing V) q]
    exact hg0
  refine ⟨V, FractionRing V, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, g ≫ s, g ≫ t, IsOpenImmersion.lift i _ hr, ?_, ?_, ?_, ?_⟩
  · exact (congrArg (· ≫ s) (IsOpenImmersion.lift_fac i _ hr)).symm.trans (Category.assoc _ _ _)
  · exact (congrArg (· ≫ t) (IsOpenImmersion.lift_fac i _ hr)).symm.trans (Category.assoc _ _ _)
  · exact (Scheme.Hom.comp_apply g s _).trans (congrArg s hg1)
  · exact ((Scheme.Hom.comp_apply g t _).trans (congrArg t hg1)).trans hy

end GlobalTheory.FibreCrit
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFibreCorrespondenceOfIsFiniteFirstStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

theorem _root_.GlobalTheory.T.finite_fibre_correspondence_of_isFinite_first : ∀ (X Y₀ Y : Scheme.{0}) (s t : Y ⟶ X) (i : Y₀ ⟶ Y), IsFinite s → IsOpenImmersion i → IsDominant i → IsLocallyNoetherian Y → (∀ z : X, {u : X | ∃ (V K : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : Field K) (_ : Algebra V K) (_ : IsFractionRing V K) (y' z' : Sp V ⟶ X) (x : Sp K ⟶ Y₀), spMap (algebraMap V K) ≫ y' = x ≫ i ≫ s ∧ spMap (algebraMap V K) ≫ z' = x ≫ i ≫ t ∧ y' (IsLocalRing.closedPoint V) = u ∧ z' (IsLocalRing.closedPoint V) = z}.Finite) → ∀ z : X, {y : Y | t y = z}.Finite := by
  first | (exact @GlobalTheory.FibreCrit.finite_fibre_of_isFinite) | (exact GlobalTheory.FibreCrit.finite_fibre_of_isFinite) | (intros; apply GlobalTheory.FibreCrit.finite_fibre_of_isFinite  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperOfDvrLiftThroughFiniteCorrespondence

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

namespace GlobalTheory.FiniteCoverProper

theorem isProper_of_lift_through_finite : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (X Y₀ Y : Scheme.{0}) (τ : X ⟶ Sp R) (s t : Y ⟶ X) (i : Y₀ ⟶ Y), IsQProjOver τ → IsFinite s → IsOpenImmersion i → IsDominant i → t ≫ τ = s ≫ τ → (∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (y : Sp V ⟶ X) (x : Sp K ⟶ Y₀), spMap (algebraMap V K) ≫ y = x ≫ i ≫ t → ∃ z : Sp V ⟶ X, spMap (algebraMap V K) ≫ z = x ≫ i ≫ s) → IsProper t := by
  intro R _ _ X Y₀ Y τ s t i hτ hs hi hd ht h
  have hX : IsLocallyNoetherian X := by
    obtain ⟨N, j, hj, -, e⟩ := hτ
    have : IsProper (PSpace.str R N) := isProper_str R N
    have : LocallyOfFiniteType τ := by rw [← e]; infer_instance
    have : IsLocallyNoetherian (Sp R) :=
      inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of R)))
    exact LocallyOfFiniteType.isLocallyNoetherian τ
  have hsep : IsSeparated τ := by
    obtain ⟨N, j, hj, -, e⟩ := hτ
    have : IsProper (PSpace.str R N) := isProper_str R N
    have : IsImmersion j := hj
    rw [← e]; infer_instance
  have hY : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian s
  have hq : IsQProjOver (t ≫ τ) := ht ▸ GlobalTheory.isQProjOver_comp_of_isFinite_general s hτ
  refine GlobalTheory.ValuativeGeneric.isProper_of_lift_generic R Y X t τ hsep hq ?_
  intro V K _ _ _ _ _ _ _ x y hx hxy
  have hgen : genericPoints Y ⊆ Set.range i := GlobalTheory.genericPoints_subset_range_of_isDominant i
  have hr : Set.range x ⊆ Set.range i := hx.trans hgen
  have hx₀ : IsOpenImmersion.lift i x hr ≫ i = x := IsOpenImmersion.lift_fac i x hr
  obtain ⟨z, hz⟩ := h V K y (IsOpenImmersion.lift i x hr) (by rw [← Category.assoc, hx₀, hxy])
  have hE : ValuativeCriterion.Existence s :=
    (UniversallyClosed.eq_valuativeCriterion ▸ (inferInstance : UniversallyClosed s) :
      (ValuativeCriterion.Existence ⊓ @QuasiCompact) s).1
  have hw : x ≫ s = Spec.map (CommRingCat.ofHom (algebraMap V K)) ≫ z := by
    rw [← hx₀, Category.assoc]; exact hz.symm
  obtain ⟨⟨x', hx', -⟩⟩ := (hE { R := V, K := K, i₁ := x, i₂ := z, commSq := ⟨hw⟩ }).exists_lift
  exact ⟨x', hx'⟩

end GlobalTheory.FiniteCoverProper
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperOfDvrLiftThroughFiniteCorrespondenceStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

theorem _root_.GlobalTheory.T.isProper_of_dvr_lift_through_finite_correspondence : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (X Y₀ Y : Scheme.{0}) (τ : X ⟶ Sp R) (s t : Y ⟶ X) (i : Y₀ ⟶ Y), IsQProjOver τ → IsFinite s → IsOpenImmersion i → IsDominant i → t ≫ τ = s ≫ τ → (∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (y : Sp V ⟶ X) (x : Sp K ⟶ Y₀), spMap (algebraMap V K) ≫ y = x ≫ i ≫ t → ∃ z : Sp V ⟶ X, spMap (algebraMap V K) ≫ z = x ≫ i ≫ s) → IsProper t := by
  first | (exact @GlobalTheory.FiniteCoverProper.isProper_of_lift_through_finite) | (exact GlobalTheory.FiniteCoverProper.isProper_of_lift_through_finite) | (intros; apply GlobalTheory.FiniteCoverProper.isProper_of_lift_through_finite  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsReducedNormalModelGenericCorrespondenceStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

theorem _root_.GlobalTheory.T.isReduced_normalModel_generic_correspondence : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CharZero R] (b : Base D R) (N : ℕ), (p : R) ∈ IsLocalRing.maximalIdeal R → ∀ (M : Model b N) (Y₀ : Scheme.{0}) (s₀ : Y₀ ⟶ M.X) (gs : Y₀ ⟶ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).toScheme), gs ≫ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).ι = s₀ → Etale gs → ∀ (Y : Scheme.{0}) (s : Y ⟶ M.X) (i : Y₀ ⟶ Y), IsOpenImmersion i → i ≫ s = s₀ → Flat (s ≫ M.s) → (∀ (S : Scheme.{0}) (f : S ⟶ Y), IsUnit ((p : ℕ) : Γ(S, ⊤)) → ∃ f₀ : S ⟶ Y₀, f₀ ≫ i = f) → IsReduced Y := by
  first | (exact @GlobalTheory.UPel.HT.ES.isReduced_normalModel_of_generic) | (exact GlobalTheory.UPel.HT.ES.isReduced_normalModel_of_generic) | (intros; apply GlobalTheory.UPel.HT.ES.isReduced_normalModel_of_generic  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagModelValueIndependent

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

noncomputable section

namespace GlobalTheory.ExtT

theorem exists_finite_extension : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CharZero R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → (p : R) ∈ IsLocalRing.maximalIdeal R → ∀ (r : ℤ) (w : Ideal (𝓞 D.F)) (j c : ℕ), w.IsMaximal → uIdeal D r ≤ w → j ≤ D.n → (∃ e : ℕ, c = p ^ e ∧ (0 < j → 0 < e)) → D.m = 1 → ∀ M : Model b N, ∀ (Y₀ : Scheme.{0}) (s₀ t₀ : Y₀ ⟶ M.X) (gs gt : Y₀ ⟶ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).toScheme) (o₀ o₀' : Obj b N (s₀ ≫ M.s)) (ms₀ : ObjMap o₀ M.univ s₀) (mt₀ : ObjMap o₀' M.univ t₀) (ψ₀ : o₀.A ⟶ o₀'.A), s₀ ≫ M.s = t₀ ≫ M.s → gs ≫ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).ι = s₀ → gt ≫ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).ι = t₀ → IsFinite gs → Etale gs → IsFinite gt → Etale gt → IsPIsog c o₀ o₀' ψ₀ → IsTj r w j o₀ o₀' ψ₀ → ∀ (Y : Scheme.{0}) (s : Y ⟶ M.X) (i : Y₀ ⟶ Y), IsOpenImmersion i → IsDominant i → i ≫ s = s₀ → IsFinite s → (∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)) → Flat (s ≫ M.s) → IsLocallyNoetherian Y → (∀ (S : Scheme.{0}) (f : S ⟶ Y), IsUnit ((p : ℕ) : Γ(S, ⊤)) → ∃ f₀ : S ⟶ Y₀, f₀ ≫ i = f) → ∃ t : Y ⟶ M.X, i ≫ t = t₀ ∧ t ≫ M.s = s ≫ M.s ∧ IsFinite t := by
  intro p _ D R _ _ _ _ b N hN hNp hpm r w j c hw hu hj hc hm M Y₀ s₀ t₀ gs gt o₀ o₀' ms₀ mt₀ ψ₀ hst hgs hgt hfs
    hes hft het hiso htj Y s i hio hid his hsf hnorm hflat hln hfac
  have hred : IsReduced Y := GlobalTheory.T.isReduced_normalModel_generic_correspondence p D R b N hpm M Y₀ s₀ gs hgs hes Y s i hio his hflat hfac
  have hval : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K]
      [IsFractionRing V K] (y : Sp V ⟶ Y) (x : Sp K ⟶ Y₀), spMap (algebraMap V K) ≫ y = x ≫ i →
      ∃ z : Sp V ⟶ M.X, spMap (algebraMap V K) ≫ z = x ≫ t₀ := by
    intro V K _ _ _ _ _ _ y x hy
    exact GlobalTheory.T.exists_dvr_extension_target_generic_correspondence p D R b N hN hNp hpm r w j c hw hu hj hc hm M Y₀ s₀ t₀ gs gt o₀ o₀' ms₀ mt₀ ψ₀ hst hgs hgt hfs hes hft het hiso htj V K (y ≫ s) x (by rw [← Category.assoc, hy, Category.assoc, his])
  have hqf : ∀ y : Y, {z : M.X | ∃ (V K : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V)
      (_ : Field K) (_ : Algebra V K) (_ : IsFractionRing V K) (y' : Sp V ⟶ Y) (z' : Sp V ⟶ M.X)
      (x : Sp K ⟶ Y₀), spMap (algebraMap V K) ≫ y' = x ≫ i ∧ spMap (algebraMap V K) ≫ z' = x ≫ t₀ ∧
      y' (IsLocalRing.closedPoint V) = y ∧ z' (IsLocalRing.closedPoint V) = z}.Finite := by
    intro y
    refine (GlobalTheory.T.finite_points_closure_genericCorrespondence_fst p D R b N hN hNp hpm r w j c hw hu hj hc hm M Y₀ s₀ t₀ gs gt o₀ o₀' ms₀ mt₀ ψ₀ hst hgs hgt hfs hes hft het hiso htj (s y)).subset ?_
    rintro z ⟨V, K, i1, i2, i3, i4, i5, i6, y', z', x, h1, h2, h3, h4⟩
    exact ⟨V, K, i1, i2, i3, i4, i5, i6, y' ≫ s, z', x, by rw [← Category.assoc, h1, Category.assoc, his], h2,
      by rw [← h3]; rfl, h4⟩
  obtain ⟨t, hit, htσ⟩ := GlobalTheory.T.extension_over_normal_quasi_projective_base R Y₀ Y M.X i (s ≫ M.s) M.s t₀ hio hid hln hred hnorm M.qproj
    (by rw [reassoc_of% his, hst]) hval hqf
  have hP : IsProper t := GlobalTheory.T.isProper_of_dvr_lift_through_finite_correspondence R M.X Y₀ Y M.s s t i M.qproj hsf hio hid htσ (fun V K _ _ _ _ _ _ y x hy => by
    obtain ⟨z, hz⟩ := GlobalTheory.T.harrisTaylor_correspondence_extend_source_dvr p D R b N hN hNp hpm r w j c hw hu hj hc hm M Y₀ s₀ t₀ gs gt o₀ o₀' ms₀ mt₀ ψ₀ hst hgs hgt hfs hes hft het hiso htj V K y x (by rw [hy, hit])
    exact ⟨z, by rw [hz, his]⟩)
  have hC : ∀ z : M.X, {y : Y | t y = z}.Finite := GlobalTheory.T.finite_fibre_correspondence_of_isFinite_first M.X Y₀ Y s t i hsf hio hid hln (fun z => by
    simpa only [his, hit] using GlobalTheory.T.finite_points_closure_genericCorrespondence_snd p D R b N hN hNp hpm r w j c hw hu hj hc hm M Y₀ s₀ t₀ gs gt o₀ o₀' ms₀ mt₀ ψ₀ hst hgs hgt hfs hes hft het hiso htj z)
  haveI : LocallyQuasiFinite t := LocallyQuasiFinite.of_finite_preimage_singleton t hC
  exact ⟨t, hit, htσ, IsFinite.of_isProper_of_locallyQuasiFinite t⟩

end GlobalTheory.ExtT
end
end
end
