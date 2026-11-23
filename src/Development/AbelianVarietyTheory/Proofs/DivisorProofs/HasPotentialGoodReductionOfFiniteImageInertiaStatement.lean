module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFieldOfValues
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisRepresentationTateModuleBaseChangeEqOneIffStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemeBaseChangeFieldAndCommStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResiduePerfectAndCharStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinsetFixingPointLocallyFiniteType

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtFin

theorem exists_finset_fix : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (A : Over (Sp K)),
    LocallyOfFiniteType A.hom → ∀ x : ptOver K Ω ⟶ A, ∃ s : Finset Ω, ∀ σ : Ω ≃ₐ[K] Ω,
      (∀ a ∈ s, σ a = a) → specAut σ ≫ x = x := by
  classical
  intro K Ω _ _ _ A hA x
  haveI := hA
  obtain ⟨⟨p, φ⟩, hx⟩ := (Scheme.SpecToEquivOfField Ω A.left).symm.surjective x.left
  simp only [Scheme.SpecToEquivOfField_symm_apply] at hx
  have hxs : x.left ≫ A.hom = spMap (algebraMap K Ω) := Over.w x
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (A.left.fromSpecResidueField p ≫ A.hom)
  have hess := GlobalTheory.SS.essFiniteType_residueField_of_locallyOfFiniteType A.hom p ψ hψ
  rw [← hx, Category.assoc, ← hψ, ← Spec.map_comp, Spec.map_inj] at hxs
  letI : Algebra K (A.left.residueField p) := ψ.hom.toAlgebra
  haveI : Algebra.EssFiniteType K (A.left.residueField p) := hess
  let fa : A.left.residueField p →ₐ[K] Ω :=
    { φ.hom with commutes' := fun c => congrArg (fun g => g.hom c) hxs }
  refine ⟨(Algebra.EssFiniteType.finset K (A.left.residueField p)).image fa, fun σ hσ => ?_⟩
  have e : (σ : Ω →ₐ[K] Ω).comp fa = fa :=
    Algebra.EssFiniteType.algHom_ext Ω _ _ fun c hc => hσ _ (Finset.mem_image_of_mem _ hc)
  apply Over.OverMorphism.ext
  change spMap (σ : Ω →+* Ω) ≫ x.left = x.left
  rw [← hx, ← Category.assoc, ← Spec.map_comp]
  congr 2
  ext c
  exact congrArg (fun g => g c) e

end GlobalTheory.PtFin
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinsetFixingPointLocallyFiniteTypeStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_finset_fixing_point_locallyFiniteType : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (A : Over (Sp K)), LocallyOfFiniteType A.hom → ∀ x : ptOver K Ω ⟶ A, ∃ s : Finset Ω, ∀ σ : Ω ≃ₐ[K] Ω, (∀ a ∈ s, σ a = a) → specAut σ ≫ x = x := by
  first | exact @GlobalTheory.PtFin.exists_finset_fix | exact GlobalTheory.PtFin.exists_finset_fix | (intros; apply GlobalTheory.PtFin.exists_finset_fix <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtensionKillingFiniteTateModuleImag

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbVarRedCut

theorem exists_finiteDimensional_galTate_eq_one : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω]
    [Algebra.IsAlgebraic K Ω] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], LocallyOfFiniteType A.hom →
    ∀ (l : ℕ) [Fact l.Prime] (I : Set (Ω ≃ₐ[K] Ω)), (galTate A l '' I).Finite →
      ∃ L : IntermediateField K Ω, FiniteDimensional K L ∧
        ∀ σ ∈ I, (∀ a ∈ L, σ a = a) → galTate A l σ = 1 := by
  intro K Ω _ _ _ _ A _ _ hA l _ I hI
  classical
  have key : ∀ s : Module.End ℤ_[l] (Tate l (ptOver K Ω ⟶ A)), ∃ F : Finset Ω,
      ∀ σ : Ω ≃ₐ[K] Ω, galTate A l σ = s → (∀ a ∈ F, σ a = a) → s = 1 := by
    intro s
    by_cases hs : s = 1
    · exact ⟨∅, fun _ _ _ => hs⟩
    · have hex : ∃ (t : Tate l (ptOver K Ω ⟶ A)) (n : ℕ), (s t).lev n ≠ t.lev n := by
        by_contra h
        push_neg at h
        exact hs (LinearMap.ext fun t => Tate.ext fun n => h t n)
      obtain ⟨t, n, htn⟩ := hex
      obtain ⟨F, hF⟩ := GlobalTheory.T.exists_finset_fixing_point_locallyFiniteType K Ω A hA (t.lev n)
      refine ⟨F, fun σ hσ hfix => ?_⟩
      exfalso
      apply htn
      rw [← hσ, lev_galTate]
      exact hF σ hfix
  choose F hF using key
  refine ⟨IntermediateField.adjoin K ((hI.toFinset.biUnion F : Finset Ω) : Set Ω), ?_, ?_⟩
  · exact IntermediateField.finiteDimensional_adjoin fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  · intro σ hσ hfix
    refine hF (galTate A l σ) σ rfl fun a ha => hfix a (IntermediateField.subset_adjoin _ _ ?_)
    rw [Finset.mem_coe]
    exact Finset.mem_biUnion.2 ⟨_, hI.mem_toFinset.2 ⟨σ, hσ, rfl⟩, ha⟩

end GlobalTheory.AbVarRedCut
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtensionKillingFiniteTateModuleImagStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_finite_extension_killing_finite_tateModule_image : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], LocallyOfFiniteType A.hom → ∀ (l : ℕ) [Fact l.Prime] (I : Set (Ω ≃ₐ[K] Ω)), (galTate A l '' I).Finite → ∃ L : IntermediateField K Ω, FiniteDimensional K L ∧ ∀ σ ∈ I, (∀ a ∈ L, σ a = a) → galTate A l σ = 1 := by
  first | exact @GlobalTheory.AbVarRedCut.exists_finiteDimensional_galTate_eq_one | exact GlobalTheory.AbVarRedCut.exists_finiteDimensional_galTate_eq_one | (intros; apply GlobalTheory.AbVarRedCut.exists_finiteDimensional_galTate_eq_one <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDiscreteValuationRingOfIsAbove

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.AbVarRed

theorem isDiscreteValuationRing_of_isAbove :
    ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
      [IsFractionRing R K] (L : Type) [Field L] [Algebra K L] [FiniteDimensional K L]
      (V : ValuationSubring L), IsAbove R K V.toSubring → IsDiscreteValuationRing V := by
  intro R K _ _ _ _ _ _ L _ _ _ V h
  letI : Algebra R L := ((algebraMap K L).comp (algebraMap R K)).toAlgebra
  have : IsScalarTower R K L := .of_algebraMap_eq fun _ => rfl
  have memV : ∀ a : K, algebraMap K L a ∈ V ↔ a ∈ (algebraMap R K).range := fun a => by
    rw [← h]; rfl
  let W : Subalgebra R L :=
    { V.toSubring with
      algebraMap_mem' := fun r => (memV (algebraMap R K r)).2 ⟨r, rfl⟩ }
  have hVn : IsNoetherianRing V := (GlobalTheory.krullAkizuki K W).1
  have hnf : ¬ IsField V := by
    intro hf
    apply IsDiscreteValuationRing.not_isField R
    have hs : Function.Surjective (algebraMap R K) := fun x => by
      by_cases hx : x = 0
      · exact ⟨0, by simp [hx]⟩
      have hxL : algebraMap K L x ≠ 0 := (map_ne_zero _).2 hx
      have hmem : algebraMap K L x ∈ V := by
        rcases V.mem_or_inv_mem (algebraMap K L x) with h1 | h1
        · exact h1
        · obtain ⟨y, hy⟩ := hf.mul_inv_cancel (a := (⟨_, h1⟩ : V))
            (fun e => inv_ne_zero hxL (congrArg Subtype.val e))
          have hy' : (algebraMap K L x)⁻¹ * (y : L) = 1 := congrArg Subtype.val hy
          have : (y : L) = algebraMap K L x := by
            rw [← inv_inv (algebraMap K L x)]
            exact eq_inv_of_mul_eq_one_right hy'
          exact this ▸ y.2
      exact (memV x).1 hmem
    exact (RingEquiv.ofBijective (algebraMap R K) ⟨IsFractionRing.injective R K, hs⟩).toMulEquiv.isField
      (Field.toIsField K)
  have hval : ValuationRing V := inferInstance
  exact ((IsDiscreteValuationRing.TFAE V hnf).out 2 1).mp hval

end GlobalTheory.AbVarRed
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDiscreteValuationRingOfIsAboveStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.isDiscreteValuationRing_of_isAbove_alt : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (L : Type) [Field L] [Algebra K L] [FiniteDimensional K L] (V : ValuationSubring L), IsAbove R K V.toSubring → IsDiscreteValuationRing V := by
  first | exact @GlobalTheory.AbVarRed.isDiscreteValuationRing_of_isAbove | exact GlobalTheory.AbVarRed.isDiscreteValuationRing_of_isAbove | (intros; apply GlobalTheory.AbVarRed.isDiscreteValuationRing_of_isAbove <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasPotentialGoodReductionOfFiniteImageInertia

section

@[expose] public section

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem restrictScalars_mem_inertia_of_mem {K L Ω : Type} [Field K] [Field L] [Field Ω] [Algebra K L]
    [Algebra L Ω] [Algebra K Ω] [IsScalarTower K L Ω] (V : ValuationSubring Ω) (σ : Ω ≃ₐ[L] Ω)
    (h : σ ∈ inertia L V) : σ.restrictScalars K ∈ inertia K V := by
  rw [mem_inertia_iff] at h ⊢
  refine ⟨?_, h.2⟩
  have h1 := h.1
  ext x
  conv_rhs => rw [← h1]
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  rfl

theorem hasPotentialGoodReduction_of_finite_image_inertia : NeronOggShafarevichSt → ∀ (R K Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [PerfectField (ResidueField R)] [Field K] [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (V : ValuationSubring Ω), IsAbove R K V.toSubring → ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (l : ℕ) [Fact l.Prime], (l : ResidueField R) ≠ 0 → (galTate A l '' (inertia K V : Set (Ω ≃ₐ[K] Ω))).Finite → HasPotentialGoodReduction R K A := by
  intro hN R K Ω _ _ _ _ _ _ _ _ _ hs V hV A _ _ hA l _ hl hfin
  haveI : Algebra.IsSeparable K Ω := hs.separable
  haveI : IsSepClosed Ω := hs.sep_closed
  haveI : IsProper A.hom := hA.proper
  obtain ⟨L, hL, hfix⟩ := GlobalTheory.T.exists_finite_extension_killing_finite_tateModule_image K Ω A inferInstance l _ hfin
  let W : ValuationSubring L := V.comap (algebraMap L Ω)
  have hW : IsAbove R K W.toSubring := by
    unfold IsAbove at hV ⊢
    rw [← hV]
    ext x
    rfl
  haveI : IsDiscreteValuationRing W := GlobalTheory.T.isDiscreteValuationRing_of_isAbove_alt R K L W hW
  have hr : (algebraMap W L).range = W.toSubring := by
    ext x
    exact ⟨fun ⟨y, hy⟩ => hy ▸ y.2, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩
  have hW' : IsAbove R K (algebraMap W L).range := hr ▸ hW
  obtain ⟨hp, hm⟩ := GlobalTheory.T.residue_perfect_and_char_alt R K L W hW'
  obtain ⟨hab, hc⟩ := GlobalTheory.T.isAbelianScheme_and_comm_baseChange_field K L A hA
  haveI : IsSepClosure L Ω := ⟨inferInstance, Algebra.isSeparable_tower_top_of_isSeparable K L Ω⟩
  have hV' : IsAbove W L V.toSubring := by
    unfold IsAbove
    rw [hr]
    rfl
  refine ⟨L, W, inferInstance, inferInstance, hL, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, hW', ?_⟩
  refine (hN.iff_tateUnramified hV' hab l (hm l hl)).2 fun σ hσ => ?_
  rw [GlobalTheory.T.galoisRepresentationTateModule_baseChange_eq_one_iff K L Ω A l σ]
  exact hfix _ (restrictScalars_mem_inertia_of_mem V σ hσ) fun a ha => σ.commutes ⟨a, ha⟩

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasPotentialGoodReductionOfFiniteImageInertiaStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.hasPotentialGoodReduction_of_finite_image_inertia_alt : NeronOggShafarevichSt → ∀ (R K Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [PerfectField (ResidueField R)] [Field K] [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (V : ValuationSubring Ω), IsAbove R K V.toSubring → ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (l : ℕ) [Fact l.Prime], (l : ResidueField R) ≠ 0 → (galTate A l '' (inertia K V : Set (Ω ≃ₐ[K] Ω))).Finite → HasPotentialGoodReduction R K A := by
  first | exact @GlobalTheory.hasPotentialGoodReduction_of_finite_image_inertia | exact GlobalTheory.hasPotentialGoodReduction_of_finite_image_inertia | (intros; apply GlobalTheory.hasPotentialGoodReduction_of_finite_image_inertia <;> assumption)
end
end
