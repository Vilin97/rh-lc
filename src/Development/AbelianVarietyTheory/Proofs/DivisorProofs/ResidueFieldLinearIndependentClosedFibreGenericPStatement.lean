module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsLocalizedModuleResBasicOpenOfQcqs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeSendsClosedFibreGenericPointDvrStatement
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
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
public import Mathlib.RingTheory.Ideal.Height
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Flat.TorsionFree
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfSmallExtension
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PushoutResidueLinearIndependentStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalFunctionAppOfPreservesGenericPoint
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqMapMaximalIdealOfRingKrullDimEqOne

section

@[expose] public section

open IsLocalRing

namespace GlobalTheory

theorem eq_map_maximalIdeal_of_ringKrullDim_eq_one (R A : Type) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [CommRing A] [IsDomain A] [Algebra R A] [Module.Flat R A]
    (p : Ideal A) [p.IsPrime] :
    (maximalIdeal R).map (algebraMap R A) ≤ p → ringKrullDim (Localization.AtPrime p) = 1 →
      IsDomain (A ⧸ (maximalIdeal R).map (algebraMap R A)) →
      p = (maximalIdeal R).map (algebraMap R A) := by
  intro hle hdim hdom
  set I := (maximalIdeal R).map (algebraMap R A) with hI
  haveI : I.IsPrime := (Ideal.Quotient.isDomain_iff_prime I).1 hdom
  have hp1 : p.height = 1 := by
    have h := IsLocalization.AtPrime.ringKrullDim_eq_height p (Localization.AtPrime p)
    rw [hdim] at h
    exact_mod_cast h.symm
  haveI : p.FiniteHeight := by
    rw [Ideal.finiteHeight_iff]; right; rw [hp1]; exact ENat.one_ne_top
  haveI : I.FiniteHeight := Ideal.finiteHeight_of_le hle (Ideal.IsPrime.ne_top ‹_›)

  have hIne : I ≠ ⊥ := by
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
    have hmem : ϖ ∈ maximalIdeal R := by
      rw [hϖ.maximalIdeal_eq]; exact Ideal.mem_span_singleton_self ϖ
    have hreg : IsSMulRegular A ϖ :=
      Module.Flat.isSMulRegular_of_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hϖ.ne_zero)
    have hne : algebraMap R A ϖ ≠ 0 := by
      intro h0
      have : ϖ • (1 : A) = ϖ • (0 : A) := by rw [Algebra.smul_def, mul_one, h0, smul_zero]
      exact one_ne_zero (hreg this)
    intro hbot
    apply hne
    have : algebraMap R A ϖ ∈ I := Ideal.mem_map_of_mem _ hmem
    rw [hbot] at this
    exact (Ideal.mem_bot).1 this
  have hIh : 1 ≤ I.height := by
    rw [ENat.one_le_iff_ne_zero]
    intro h0
    exact hIne (Ideal.height_eq_zero_iff_eq_bot.1 h0)
  exact (Ideal.eq_of_le_of_height_le I hle (by rw [hp1]; exact hIh)).symm

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqMapMaximalIdealOfRingKrullDimEqOneStatement

section

@[expose] public section

open IsLocalRing

theorem _root_.GlobalTheory.T.eq_map_maximalIdeal_of_ringKrullDim_eq_one' : ∀ (R A : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CommRing A] [IsDomain A] [Algebra R A] [Module.Flat R A] (p : Ideal A) [p.IsPrime], (maximalIdeal R).map (algebraMap R A) ≤ p → ringKrullDim (Localization.AtPrime p) = 1 → IsDomain (A ⧸ (maximalIdeal R).map (algebraMap R A)) → p = (maximalIdeal R).map (algebraMap R A) := by
  first | exact @GlobalTheory.eq_map_maximalIdeal_of_ringKrullDim_eq_one | exact GlobalTheory.eq_map_maximalIdeal_of_ringKrullDim_eq_one | (intros; apply GlobalTheory.eq_map_maximalIdeal_of_ringKrullDim_eq_one <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDomainSectionsQuotMaximalIdealSmoothConnected

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory

theorem abLawCst_eq_smallExtLiftCst {X : Scheme} {R : Type} [CommRing R]
    (f : X ⟶ Spec (CommRingCat.of R)) (U : X.Opens) :
    GlobalTheory.AbLaw.cst f U = GlobalTheory.SmallExtLift.cst f U := by
  ext r
  simp only [GlobalTheory.AbLaw.cst, GlobalTheory.SmallExtLift.cst, GlobalTheory.AbLaw.rs, Scheme.Hom.appLE,
    CommRingCat.hom_comp, RingHom.comp_apply, Scheme.Hom.appTop]
  rfl

theorem isDomain_quot_maximalIdeal_of_smooth :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Sp R)), Smooth G.hom →
      GeometricallyConnected G.hom → ∀ (U : G.left.Opens), IsAffineOpen U → ∀ y ∈ U,
        G.hom y = closedPoint R →
          IsDomain (Γ(G.left, U) ⧸ (maximalIdeal R).map (GlobalTheory.AbLaw.cst G.hom U)) := by
  intro R _ _ G hsm hgc U hU y hyU hy
  haveI := hsm
  haveI := hgc
  let f : G.left ⟶ Spec (CommRingCat.of R) := G.hom
  let g : Spec (CommRingCat.of (ResidueField R)) ⟶ Spec (CommRingCat.of R) :=
    Spec.map (CommRingCat.ofHom (residue R))
  haveI hI : IsIntegral (pullback f g) := GlobalTheory.isIntegral_specialFibre_of_smooth f
  let q := pullback.fst f g
  have H : IsPullback q (pullback.snd f g) f g := IsPullback.of_hasPullback f g
  have hsurj : Function.Surjective (q.app U).hom :=
    GlobalTheory.SmallExtLift.app_surj (residue_surjective) H hU
  have hker : RingHom.ker (q.app U).hom = (maximalIdeal R).map (GlobalTheory.AbLaw.cst G.hom U) := by
    rw [abLawCst_eq_smallExtLiftCst]
    apply le_antisymm
    · intro a ha
      have := GlobalTheory.SmallExtLift.mem_of_app_eq_zero (residue_surjective) H hU a ha
      rwa [ker_residue] at this
    · rw [Ideal.map_le_iff_le_comap]
      intro r hr
      rw [Ideal.mem_comap, RingHom.mem_ker, GlobalTheory.SmallExtLift.app_cst H.w,
        (residue_eq_zero_iff r).2 hr, map_zero]
  have hne : Nonempty (q ⁻¹ᵁ U) := by
    have hpt : f y = g (closedPoint (ResidueField R)) := by
      rw [show f y = G.hom y from rfl, hy]
      exact (IsLocalRing.comap_closedPoint (residue R)).symm
    obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback y _ hpt
    exact ⟨⟨z, show q z ∈ U from hz ▸ hyU⟩⟩
  haveI : IsDomain Γ(pullback f g, q ⁻¹ᵁ U) := inferInstance
  rw [← hker]
  exact (RingHom.quotientKerEquivOfSurjective hsurj).toMulEquiv.isDomain

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDomainSectionsQuotMaximalIdealSmoothConnectedStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

theorem _root_.GlobalTheory.T.isDomain_sections_quot_maximalIdeal_smooth_connected : ∀ (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Sp R)), Smooth G.hom → GeometricallyConnected G.hom → ∀ (U : G.left.Opens), IsAffineOpen U → ∀ y ∈ U, G.hom y = closedPoint R → IsDomain (Γ(G.left, U) ⧸ (maximalIdeal R).map (GlobalTheory.AbLaw.cst G.hom U)) := by
  first | exact @GlobalTheory.isDomain_quot_maximalIdeal_of_smooth | exact GlobalTheory.isDomain_quot_maximalIdeal_of_smooth | (intros; apply GlobalTheory.isDomain_quot_maximalIdeal_of_smooth <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueFieldLinearIndependentClosedFibreGenericP

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

noncomputable section

namespace GlobalTheory.Desc.ResInj

theorem cst_eq_fnOf {X : Scheme.{0}} [IsIntegral X] {R : Type} [CommRing R] (p : X ⟶ Sp R) (V : X.Opens)
    (hV : genericPoint X ∈ V) (r : R) : GlobalTheory.Desc.cst p r = fnOf V hV (GlobalTheory.AbLaw.cst p V r) := by
  simp only [GlobalTheory.Desc.cst, GlobalTheory.AbLaw.cst, fnOf, RingHom.comp_apply, Scheme.Hom.appLE, CommRingCat.hom_comp]
  rw [TopCat.Presheaf.germ_res_apply]

theorem zeroAt_fnOf_iff {X : Scheme.{0}} [IsIntegral X] {U : X.Opens} {x : X} (hx : x ∈ U) (b : Γ(X, U)) :
    ZeroAt x (fnOf U (gen_mem hx) b) ↔ (X.presheaf.germ U x hx).hom b ∈ maximalIdeal (X.presheaf.stalk x) := by
  refine ⟨fun ⟨a, ha, e⟩ => ?_, fun h => ⟨_, h, algebraMap_germ hx b⟩⟩
  rwa [IsFractionRing.injective (X.presheaf.stalk x) X.functionField (e.trans (algebraMap_germ hx b).symm)] at ha

theorem cst_zeroAt (R : Type) [CommRing R] [IsLocalRing R] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp R) (x : X)
    (hx : p x = closedPoint R) (r : R) (hr : r ∈ maximalIdeal R) : ZeroAt x (GlobalTheory.Desc.cst p r) := by
  have hreg : RegAt x (GlobalTheory.Desc.cst p r) := regAt_fnOf (U := ⊤) trivial trivial _
  refine zeroAt_iff.2 ⟨hreg, fun hu => ?_⟩
  have h1 := (unitAt_fnOf_iff (U := ⊤) trivial trivial _).1 hu
  have h2 : x ∈ p ⁻¹ᵁ (Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r) := by
    rw [Scheme.Hom.preimage_basicOpen]; exact h1
  have h3 : p x ∈ (Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r) := h2
  rw [basicOpen_eq_of_affine, hx] at h3
  exact (PrimeSpectrum.mem_basicOpen _ _).1 h3 hr

end GlobalTheory.Desc.ResInj

theorem GlobalTheory.Desc.ResInj.exists_affine_fnOf : ∀ (X : Scheme.{0}) [IsIntegral X] (x : X) (n : ℕ) (u : Fin n → X.functionField), (∀ i, GlobalTheory.Cartier.RegAt x (u i)) → ∃ (U : X.Opens) (hx : x ∈ U), IsAffineOpen U ∧ ∃ s : Fin n → Γ(X, U), ∀ i, GlobalTheory.Cartier.fnOf U (GlobalTheory.Cartier.gen_mem hx) (s i) = u i := by
  intro X _ x n u hu
  choose W hxW s hs using fun i => (hu i).exists_fnOf
  let W₀ : X.Opens := ⟨⋂ i, (W i : Set X), isOpen_iInter_of_finite fun i => (W i).isOpen⟩
  have hx₀ : x ∈ W₀ := Set.mem_iInter.2 hxW
  obtain ⟨U, hU, hxU, hUW⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp (Scheme.isBasis_affineOpens X)) hx₀
  have hle : ∀ i, U ≤ W i := fun i z hz => Set.mem_iInter.1 (hUW hz) i
  refine ⟨U, hxU, hU, fun i => resG X (hle i) (s i), fun i => ?_⟩
  rw [fnOf_resG, hs]

theorem GlobalTheory.Desc.ResInj.mem_map_of_germ_mem : ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (G : Over (Sp R)) [IsIntegral G.left], Smooth G.hom → GeometricallyConnected G.hom → ∀ y : G.left, G.hom y = closedPoint R → ringKrullDim (G.left.presheaf.stalk y) = 1 → ∀ (U : G.left.Opens) (hy : y ∈ U), IsAffineOpen U → ∀ b : Γ(G.left, U), (G.left.presheaf.germ U y hy).hom b ∈ maximalIdeal (G.left.presheaf.stalk y) → b ∈ (maximalIdeal R).map (GlobalTheory.AbLaw.cst G.hom U) := by
  intro R _ _ _ G _ hsm hgc y hy hdim U hyU hU b hb
  haveI : Nonempty U := ⟨⟨y, hyU⟩⟩
  letI : Algebra R Γ(G.left, U) := (GlobalTheory.AbLaw.cst G.hom U).toAlgebra
  haveI : Module.Flat R Γ(G.left, U) := GlobalTheory.AbLaw.flat_cst G.hom hU
  let p := hU.primeIdealOf ⟨y, hyU⟩
  letI : Algebra Γ(G.left, U) (G.left.presheaf.stalk y) := G.left.presheaf.algebra_section_stalk ⟨y, hyU⟩
  haveI hloc := hU.isLocalization_stalk ⟨y, hyU⟩
  have hmem : ∀ c : Γ(G.left, U), (G.left.presheaf.germ U y hyU).hom c ∈ maximalIdeal (G.left.presheaf.stalk y) ↔ c ∈ p.asIdeal := by
    intro c
    exact IsLocalization.AtPrime.to_map_mem_maximal_iff (G.left.presheaf.stalk y) p.asIdeal c
  have hle : (maximalIdeal R).map (algebraMap R Γ(G.left, U)) ≤ p.asIdeal := by
    rw [Ideal.map_le_iff_le_comap]
    intro t ht
    rw [Ideal.mem_comap, ← hmem, ← GlobalTheory.Desc.ResInj.zeroAt_fnOf_iff hyU]
    have := GlobalTheory.Desc.ResInj.cst_zeroAt R G.left G.hom y hy t ht
    rwa [GlobalTheory.Desc.ResInj.cst_eq_fnOf G.hom U (gen_mem hyU)] at this
  have hd : ringKrullDim (Localization.AtPrime p.asIdeal) = 1 := by
    rw [← hdim]
    exact ringKrullDim_eq_of_ringEquiv (IsLocalization.algEquiv p.asIdeal.primeCompl (Localization.AtPrime p.asIdeal) (G.left.presheaf.stalk y)).toRingEquiv
  have e := GlobalTheory.T.eq_map_maximalIdeal_of_ringKrullDim_eq_one' R Γ(G.left, U) p.asIdeal hle hd (GlobalTheory.T.isDomain_sections_quot_maximalIdeal_smooth_connected R G hsm hgc U hU y hyU hy)
  have : b ∈ p.asIdeal := (hmem b).1 hb
  rw [e] at this
  exact this

theorem GlobalTheory.Desc.ResInj.residue_linearIndependent : ∀ (T D : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [CommRing D] [IsDomain D] [IsDiscreteValuationRing D] (a : T →+* D), a.Flat → (maximalIdeal T).map a = maximalIdeal D → ∀ (H : Over (Sp T)) [GrpObj H] [IsIntegral H.left] (H' : Over (Sp D)) [GrpObj H'] [IsIntegral H'.left] (π : H'.left ⟶ H.left) (θ : H.left.functionField →+* H'.left.functionField), IsSemiAbelian H → IsPullback π H'.hom H.hom (spMap a) → PFF (𝟙 _) π θ → ∀ (y : H.left) (y' : H'.left), H.hom y = closedPoint T → H'.hom y' = closedPoint D → ringKrullDim (H.left.presheaf.stalk y) = 1 → ringKrullDim (H'.left.presheaf.stalk y') = 1 → ∀ (n : ℕ) (u : Fin n → H.left.functionField), (∀ i, GlobalTheory.Cartier.RegAt y (u i)) → (∀ c : Fin n → T, GlobalTheory.Cartier.ZeroAt y (∑ i, GlobalTheory.Desc.cst H.hom (c i) * u i) → ∀ i, c i ∈ maximalIdeal T) → ∀ d : Fin n → D, GlobalTheory.Cartier.ZeroAt y' (∑ i, GlobalTheory.Desc.cst H'.hom (d i) * θ (u i)) → ∀ i, d i ∈ maximalIdeal D := by
  intro T D _ _ _ _ _ _ a ha hm H _ _ H' _ _ π θ hH hpb hpff y y' hy hy' hdy hdy' n u hu hind d hz
  have hπy : π y' = y := GlobalTheory.T.baseChange_sends_closedFibre_genericPoint_dvr T D a ha hm H H' π θ hH hpb hpff y y' hy hy' hdy hdy'
  obtain ⟨U, hyU, hUa, x, hx⟩ := GlobalTheory.Desc.ResInj.exists_affine_fnOf H.left y n u hu
  set V : H'.left.Opens := π ⁻¹ᵁ U with hVdef
  have hy'V : y' ∈ V := by show π y' ∈ U; rw [hπy]; exact hyU
  have hgU : genericPoint H.left ∈ U := gen_mem hyU
  have hgV : genericPoint H'.left ∈ V := gen_mem hy'V
  letI : Algebra T D := a.toAlgebra
  letI : Algebra T Γ(H.left, U) := (GlobalTheory.AbLaw.cst H.hom U).toAlgebra
  letI : Algebra D Γ(H'.left, V) := (GlobalTheory.AbLaw.cst H'.hom V).toAlgebra
  letI : Algebra Γ(H.left, U) Γ(H'.left, V) := (π.app U).hom.toAlgebra
  letI : Algebra T Γ(H'.left, V) := ((GlobalTheory.AbLaw.cst H'.hom V).comp a).toAlgebra
  haveI : IsScalarTower T D Γ(H'.left, V) := .of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower T Γ(H.left, U) Γ(H'.left, V) := .of_algebraMap_eq fun r => by
    have e := GlobalTheory.AbLaw.appLE_cst hpb.w (V := U) (V' := V) le_rfl r
    rw [Scheme.Hom.appLE_eq_app] at e
    exact e.symm
  haveI : Algebra.IsPushout T D Γ(H.left, U) Γ(H'.left, V) := by
    have po := GlobalTheory.AbLaw.isPushout_cst hpb hUa (V' := V) rfl
    rw [Scheme.Hom.appLE_eq_app] at po
    exact CommRingCat.isPushout_iff_isPushout.mp po
  have hsm : Smooth H'.hom := MorphismProperty.of_isPullback hpb hH.smooth
  have hgc : GeometricallyConnected H'.hom := MorphismProperty.of_isPullback hpb hH.geomConnected

  have hindA : ∀ c : Fin n → T, ∑ i, c i • x i ∈ (maximalIdeal T).map (algebraMap T Γ(H.left, U)) →
      ∀ i, c i ∈ maximalIdeal T := by
    intro c hc
    apply hind c
    have hle : (maximalIdeal T).map (algebraMap T Γ(H.left, U)) ≤
        Ideal.comap (H.left.presheaf.germ U y hyU).hom (maximalIdeal _) := by
      rw [Ideal.map_le_iff_le_comap]
      intro t ht
      rw [Ideal.mem_comap, Ideal.mem_comap, ← GlobalTheory.Desc.ResInj.zeroAt_fnOf_iff hyU]
      have := GlobalTheory.Desc.ResInj.cst_zeroAt T H.left H.hom y hy t ht
      rwa [GlobalTheory.Desc.ResInj.cst_eq_fnOf H.hom U hgU] at this
    have h1 := hle hc
    rw [Ideal.mem_comap, ← GlobalTheory.Desc.ResInj.zeroAt_fnOf_iff hyU] at h1
    convert h1 using 1

    simp only [map_sum, Algebra.smul_def, map_mul, hx]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [GlobalTheory.Desc.ResInj.cst_eq_fnOf H.hom U hgU]
    rfl

  have hd := GlobalTheory.T.pushout_residue_linearIndependent' T D Γ(H.left, U) Γ(H'.left, V) hm n x hindA d
  apply hd
  apply GlobalTheory.Desc.ResInj.mem_map_of_germ_mem D H' hsm hgc y' hy' hdy' V hy'V (GlobalTheory.AbLaw.isAffineOpen_preimage_of_isPullback hpb hUa)
  rw [← GlobalTheory.Desc.ResInj.zeroAt_fnOf_iff hy'V]
  convert hz using 1

  simp only [map_sum, Algebra.smul_def, map_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← hx i, ← GlobalTheory.Desc.fnOf_app_of_pff H.left H'.left π θ hpff U hgU hgV, GlobalTheory.Desc.ResInj.cst_eq_fnOf H'.hom V hgV]
  rfl
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueFieldLinearIndependentClosedFibreGenericPStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

theorem _root_.GlobalTheory.T.residueField_linearIndependent_closedFibre_genericPoints : ∀ (T D : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [CommRing D] [IsDomain D] [IsDiscreteValuationRing D] (a : T →+* D), a.Flat → (maximalIdeal T).map a = maximalIdeal D → ∀ (H : Over (Sp T)) [GrpObj H] [IsIntegral H.left] (H' : Over (Sp D)) [GrpObj H'] [IsIntegral H'.left] (π : H'.left ⟶ H.left) (θ : H.left.functionField →+* H'.left.functionField), IsSemiAbelian H → IsPullback π H'.hom H.hom (spMap a) → PFF (𝟙 _) π θ → ∀ (y : H.left) (y' : H'.left), H.hom y = closedPoint T → H'.hom y' = closedPoint D → ringKrullDim (H.left.presheaf.stalk y) = 1 → ringKrullDim (H'.left.presheaf.stalk y') = 1 → ∀ (n : ℕ) (u : Fin n → H.left.functionField), (∀ i, GlobalTheory.Cartier.RegAt y (u i)) → (∀ c : Fin n → T, GlobalTheory.Cartier.ZeroAt y (∑ i, GlobalTheory.Desc.cst H.hom (c i) * u i) → ∀ i, c i ∈ maximalIdeal T) → ∀ d : Fin n → D, GlobalTheory.Cartier.ZeroAt y' (∑ i, GlobalTheory.Desc.cst H'.hom (d i) * θ (u i)) → ∀ i, d i ∈ maximalIdeal D := by
  first | exact @GlobalTheory.Desc.ResInj.residue_linearIndependent | exact GlobalTheory.Desc.ResInj.residue_linearIndependent | (intros; apply GlobalTheory.Desc.ResInj.residue_linearIndependent <;> assumption)
end
end
