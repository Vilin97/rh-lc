module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteIndexSubgroupAutExtendSepClosureStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisSmulEqValuationSubringOverDvrStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInjectivePointsLargerFieldGalois
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
public import Mathlib.GroupTheory.Index
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.MapSmulOfIsHausdorff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadTie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisRepresentationTateModuleBaseChangeEqOneIffStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertiaLiftOfPurelyInseparableStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemeBaseChangeFieldAndCommStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResiduePerfectAndCharStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SepClosureFiniteExtPowMemRangeStatement
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasPotentialGoodReductionOfFiniteImageInertiaStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInjectivePointsLargerFieldGaloisStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_injective_points_larger_field_galois : ∀ (K Ω Ω' : Type) [Field K] [Field Ω] [Field Ω'] [Algebra K Ω] [Algebra K Ω'] (j : Ω →ₐ[K] Ω') (A : Over (Sp K)) [GrpObj A], ∃ f : (ptOver K Ω ⟶ A) →* (ptOver K Ω' ⟶ A), Function.Injective f ∧ ∀ (σ : Ω ≃ₐ[K] Ω) (σ' : Ω' ≃ₐ[K] Ω'), (∀ x, σ' (j x) = j (σ x)) → ∀ x, f (specAut σ ≫ x) = specAut σ' ≫ f x := by
  first | exact @GlobalTheory.Published.AbVarRed.exists_injective_ptOver_galois | exact GlobalTheory.Published.AbVarRed.exists_injective_ptOver_galois | (intros; apply GlobalTheory.Published.AbVarRed.exists_injective_ptOver_galois <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteImageOfMapEqOneOnInfFiniteIndex

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem finite_image_of_map_eq_one_on_inf_finiteIndex :
    ∀ (G M : Type) [Group G] [Monoid M] (ρ : G →* M) (I H : Subgroup G), H.FiniteIndex →
      (∀ σ ∈ I, σ ∈ H → ρ σ = 1) → (ρ '' (I : Set G)).Finite := by
  intro G M _ _ ρ I H hH hρ
  haveI : Finite (G ⧸ H) := Subgroup.finite_quotient_of_finiteIndex
  classical
  let f : G ⧸ H → M := fun q => if h : ∃ σ ∈ I, (σ : G ⧸ H) = q then ρ h.choose else 1
  apply (Set.finite_range f).subset
  rintro _ ⟨σ, hσ, rfl⟩
  refine ⟨(σ : G ⧸ H), ?_⟩
  have h : ∃ τ ∈ I, (τ : G ⧸ H) = σ := ⟨σ, hσ, rfl⟩
  simp only [f, dif_pos h]
  obtain ⟨hτI, hτ⟩ := h.choose_spec
  rw [QuotientGroup.eq] at hτ
  have h1 : ρ (h.choose⁻¹ * σ) = 1 := hρ _ (I.mul_mem (I.inv_mem hτI) hσ) hτ
  calc ρ h.choose = ρ h.choose * ρ (h.choose⁻¹ * σ) := by rw [h1, _root_.mul_one]
    _ = ρ σ := by rw [← map_mul, _root_.mul_inv_cancel_left]

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteImageOfMapEqOneOnInfFiniteIndexStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.finite_image_of_map_eq_one_on_inf_finiteIndex' : ∀ (G M : Type) [Group G] [Monoid M] (ρ : G →* M) (I H : Subgroup G), H.FiniteIndex → (∀ σ ∈ I, σ ∈ H → ρ σ = 1) → (ρ '' (I : Set G)).Finite := by
  first | exact @GlobalTheory.finite_image_of_map_eq_one_on_inf_finiteIndex | exact GlobalTheory.finite_image_of_map_eq_one_on_inf_finiteIndex | (intros; apply GlobalTheory.finite_image_of_map_eq_one_on_inf_finiteIndex <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertiaConjMemSmul

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem inertia_conj_mem_smul : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (V : ValuationSubring Ω)
    (g σ : Ω ≃ₐ[K] Ω), σ ∈ inertia K V → g * σ * g⁻¹ ∈ inertia K (g • V) := by
  intro K Ω _ _ _ V g σ hσ
  rw [mem_inertia_iff] at hσ ⊢
  obtain ⟨h1, h2⟩ := hσ

  have hn : ∀ z : Ω, V.valuation z < 1 → (g • V).valuation (g z) < 1 := by
    intro z hz
    rw [← ValuationSubring.mem_nonunits_iff, ValuationSubring.mem_nonunits_iff_or] at hz ⊢
    rcases hz with hz | hz
    · left; simp [hz]
    · right
      rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
      intro h
      apply hz
      have : (g⁻¹ • (g z)⁻¹) = z⁻¹ := by
        change g⁻¹ ((g z)⁻¹) = z⁻¹
        rw [map_inv₀]
        simp
      rwa [this] at h
  refine ⟨?_, ?_⟩
  · rw [mul_smul, mul_smul, inv_smul_smul, h1]
  · intro x hx
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem] at hx
    set y := g⁻¹ • x with hy
    have hxy : x = g y := by simp [hy]
    have : (g * σ * g⁻¹) x - x = g (σ y - y) := by
      rw [map_sub, hxy]
      simp
    rw [this]
    exact hn _ (h2 y hx)

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertiaConjMemSmulStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.inertia_conj_mem_smul' : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (V : ValuationSubring Ω) (g σ : Ω ≃ₐ[K] Ω), σ ∈ inertia K V → g * σ * g⁻¹ ∈ inertia K (g • V) := by
  first | exact @GlobalTheory.inertia_conj_mem_smul | exact GlobalTheory.inertia_conj_mem_smul | (intros; apply GlobalTheory.inertia_conj_mem_smul <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteImageInertiaOfPotentialGoodReduction

section

@[expose] public section

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem galTate_eq_one_of_embedding {K Ω Ω' : Type} [Field K] [Field Ω] [Field Ω'] [Algebra K Ω] [Algebra K Ω']
    (j : Ω →ₐ[K] Ω') (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A] (l : ℕ) [Fact l.Prime]
    (σ : Ω ≃ₐ[K] Ω) (σ' : Ω' ≃ₐ[K] Ω') (h : ∀ x, σ' (j x) = j (σ x)) (h1 : galTate A l σ' = 1) :
    galTate A l σ = 1 := by
  obtain ⟨f, hf, hc⟩ := GlobalTheory.T.exists_injective_points_larger_field_galois K Ω Ω' j A
  refine LinearMap.ext fun t => Tate.ext fun n => hf ?_
  have e := congrArg (fun u => u.lev n) (LinearMap.congr_fun h1 (Tate.map l f t))
  exact (hc σ σ' h (t.lev n)).trans e

theorem finite_image_inertia_of_goodReduction_baseChange (h : NeronOggShafarevichSt) (R K Ω : Type) [CommRing R]
    [IsDomain R] [IsDiscreteValuationRing R] [PerfectField (ResidueField R)] [Field K] [Algebra R K]
    [IsFractionRing R K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (V : ValuationSubring Ω)
    (hV : IsAbove R K V.toSubring) (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A] (hA : IsAbelianScheme A)
    (l : ℕ) [Fact l.Prime] (hl : (l : ResidueField R) ≠ 0)
    (L W Ω' : Type) [Field L] [Algebra K L] [FiniteDimensional K L] [CommRing W] [IsDomain W]
    [IsDiscreteValuationRing W] [Algebra W L] [IsFractionRing W L] [Field Ω'] [Algebra L Ω'] [IsSepClosure L Ω']
    [Algebra K Ω'] [IsScalarTower K L Ω'] (hW : IsAbove R K (algebraMap W L).range)
    (hg : HasGoodReduction W L ((Over.pullback (spMap (algebraMap K L))).obj A)) :
    (galTate A l '' (inertia K V : Set (Ω ≃ₐ[K] Ω))).Finite := by
  haveI : IsSepClosed Ω' := IsSepClosure.sep_closed L
  haveI : Algebra.IsSeparable K Ω := IsSepClosure.separable
  haveI : IsGalois K Ω := inferInstance
  let j : Ω →ₐ[K] Ω' := IsSepClosed.lift
  obtain ⟨V', hV'⟩ := exists_isAbove W L Ω'
  obtain ⟨hp, hm⟩ := GlobalTheory.T.residue_perfect_and_char_alt R K L W hW
  obtain ⟨hAL, hc⟩ := GlobalTheory.T.isAbelianScheme_and_comm_baseChange_field K L A hA
  have hT := (h.iff_tateUnramified hV' hAL l (hm l hl)).1 hg
  have hV'' : IsAbove R K (V'.comap (j : Ω →+* Ω')).toSubring := by
    unfold IsAbove at hW hV' ⊢
    rw [← hW, ← hV']
    ext x
    change j (algebraMap K Ω x) ∈ V' ↔ algebraMap L Ω' (algebraMap K L x) ∈ V'
    rw [j.commutes, ← IsScalarTower.algebraMap_apply]
  obtain ⟨H, hH, hext⟩ := GlobalTheory.T.exists_finiteIndex_subgroup_aut_extend_sepClosure K L Ω Ω' j
  obtain ⟨g, hgV⟩ := GlobalTheory.T.exists_galois_smul_eq_valuationSubring_over_dvr R K Ω V _ hV hV''
  have key : ∀ σ ∈ inertia K (V'.comap (j : Ω →+* Ω')), σ ∈ H → galTate A l σ = 1 := by
    intro σ hσ hσH
    obtain ⟨σ', hσ'⟩ := hext σ hσH
    have h1 := GlobalTheory.T.inertia_lift_of_purelyInseparable_alt K L Ω Ω' j (GlobalTheory.T.sepClosure_exists_pow_mem_range_of_finiteDimensional K L Ω Ω' j) V' σ σ' hσ' hσ
    have h2 := (GlobalTheory.T.galoisRepresentationTateModule_baseChange_eq_one_iff K L Ω' A l σ').1 (hT σ' h1)
    exact galTate_eq_one_of_embedding j A l σ (σ'.restrictScalars K) hσ' h2
  refine GlobalTheory.T.finite_image_of_map_eq_one_on_inf_finiteIndex' _ _ (galTate A l) (inertia K V) (H.comap (MulAut.conj g).toMonoidHom) ?_ ?_
  · constructor
    rw [Subgroup.index_comap_of_surjective _ (MulAut.conj g).surjective]
    exact hH.index_ne_zero
  · intro σ hσ hσH
    have h1 := key (g * σ * g⁻¹) (hgV ▸ GlobalTheory.T.inertia_conj_mem_smul' K Ω V g σ hσ) hσH
    have e : σ = g⁻¹ * (g * σ * g⁻¹) * g := by group
    rw [e, map_mul, map_mul, h1, _root_.mul_one, ← map_mul, inv_mul_cancel, map_one]

theorem finite_image_inertia_of_potentialGoodReduction : NeronOggShafarevichSt → ∀ (R K Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [PerfectField (ResidueField R)] [Field K] [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (V : ValuationSubring Ω), IsAbove R K V.toSubring → ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (l : ℕ) [Fact l.Prime], (l : ResidueField R) ≠ 0 → HasPotentialGoodReduction R K A → (galTate A l '' (inertia K V : Set (Ω ≃ₐ[K] Ω))).Finite := by
  intro h R K Ω _ _ _ _ _ _ _ _ _ _ V hV A _ _ hA l _ hl hP
  obtain ⟨L, W, _, _, _, _, _, _, _, _, hW, hg⟩ := hP
  exact finite_image_inertia_of_goodReduction_baseChange h R K Ω V hV A hA l hl L W (SeparableClosure L) hW hg

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteImageInertiaOfPotentialGoodReductionStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.finite_image_inertia_of_potentialGoodReduction_alt : NeronOggShafarevichSt → ∀ (R K Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [PerfectField (ResidueField R)] [Field K] [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (V : ValuationSubring Ω), IsAbove R K V.toSubring → ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (l : ℕ) [Fact l.Prime], (l : ResidueField R) ≠ 0 → HasPotentialGoodReduction R K A → (galTate A l '' (inertia K V : Set (Ω ≃ₐ[K] Ω))).Finite := by
  exact @GlobalTheory.finite_image_inertia_of_potentialGoodReduction
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PotentialGoodReductionOfNeronOggShafarevich

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem potentialGoodReduction_of_neronOggShafarevich :
    GlobalTheory.Published.NeronOggShafarevichSt → GlobalTheory.Published.PotentialGoodReductionSt := by
  intro h R K Ω _ _ _ _ _ _ _ _ _ _ V hV A _ _ hA l _ hl
  exact ⟨GlobalTheory.T.finite_image_inertia_of_potentialGoodReduction_alt h R K Ω V hV A hA l hl, GlobalTheory.T.hasPotentialGoodReduction_of_finite_image_inertia_alt h R K Ω V hV A hA l hl⟩

end GlobalTheory
end
end
