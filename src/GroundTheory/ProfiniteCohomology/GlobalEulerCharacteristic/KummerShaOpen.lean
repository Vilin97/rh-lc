module

public import GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.KummerSeq
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseTransportGS
public import GroundTheory.ProfiniteCohomology.PoitouTate.PtCompactDualMapEqZeroOfPtCompactToGlobalEqZero
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseKummerDefs
import GroundTheory.ProfiniteCohomology.CupProducts.Projection
import GroundTheory.ProfiniteCohomology.CohomologicalDimension.SubsingletonCohomologyOfPrimaryOfFinite
import GroundTheory.ProfiniteCohomology.GaloisCohomology.Kummer
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseKummer
import GroundTheory.ProfiniteCohomology.RestrictedRamification.Brauer
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BrauerSplit
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
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
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
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.FiniteOpen
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

-- Source module: GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.KummerSha

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IsDedekindDomain GroundTheory.Global

noncomputable section

local notation "ℚ̄" => AlgebraicClosure ℚ

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1)))
  (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))
  (ℓ : ℕ) [NeZero ℓ] (hℓS : ∀ v ∉ S, ((ℓ : ℕ) : 𝓞 K.1) ∉ v.asIdeal)

def gsRootsLocalUnitsMor (v : S) :
    Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S ℓ) ⟶
      galUnits ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
        (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) :=
  gsRootsOmegaMor S ιs ℓ v ≫
    (kummerSequence ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
      (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) ℓ).f

theorem gsRootsLocalUnitsMor_eq (v : S) :
    gsRootsLocalUnitsMor S ιs ℓ v =
      (Rep.resFunctor (gsFinFamily S ιs v).toMonoidHom).map
        (rootsOfUnityToSUnits S (maxUnramifiedOutside K.1 ℚ̄ S) ℓ) ≫ gsSUnitsLocalMor S ιs v :=
  (gsKummerLocalMap S ιs ℓ v).comm₁₂.symm


include hℓS in
theorem cohomologyMap_gsRootsLocalUnitsMor_injective (v : S) :
    Function.Injective (cohomologyMap (gsRootsLocalUnitsMor S ιs ℓ v) 2).hom := by
  have h2 := cohomologyMap_f_injective_of_subsingleton (localKummer_shortExact S ℓ v) 1
    subsingleton_cohomology_one_galUnits
  have h1 : Function.Injective (cohomologyMap (gsRootsOmegaMor S ιs ℓ v) 2).hom := by
    have hbij : Function.Bijective (gsRootsOmegaMor S ιs ℓ v).hom := by
      obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot ℚ̄ ℓ
      have hzS : z ∈ maxUnramifiedOutside K.1 ℚ̄ S :=
        mem_maxUnramifiedOutside_of_pow_eq_one S (NeZero.ne ℓ) hℓS hz.pow_eq_one
      have hzS' : IsPrimitiveRoot (⟨z, hzS⟩ : maxUnramifiedOutside K.1 ℚ̄ S) ℓ :=
        hz.of_map_of_injective (f := (maxUnramifiedOutside K.1 ℚ̄ S).val) Subtype.val_injective
      have hF := bijective_restrictRootsOfUnity_of_isPrimitiveRoot ℓ
        ((ιs v).comp (maxUnramifiedOutside K.1 ℚ̄ S).val).toRingHom hzS'
      exact Additive.ofMul.bijective.comp (hF.comp Additive.toMul.bijective)
    have hc := congrArg (fun φ => cohomologyMap φ 2)
      (comp_repInvOfBijective (gsRootsOmegaMor S ιs ℓ v) hbij)
    have hc' := (cohomologyMap_comp _ _ 2).symm.trans (hc.trans (cohomologyMap_id 2))
    refine Function.LeftInverse.injective (g := (cohomologyMap (repInvOfBijective
      (gsRootsOmegaMor S ιs ℓ v) hbij) 2).hom) fun a => ?_
    exact congrArg (fun φ => φ.hom a) hc'
  have e := cohomologyMap_comp (gsRootsOmegaMor S ιs ℓ v)
    (kummerSequence ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
      (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) ℓ).f 2
  intro a b hab
  have hab' := (congrArg (fun φ => φ.hom a) e).symm.trans ((hab : _).trans (congrArg (fun φ => φ.hom b) e))
  exact h1 (h2 hab')


include hℓS in
theorem ptRes_eq_zero_iff (v : S) (x : cohomology (gsRoots S ℓ) 2) :
    ptRes (gsFinFamily S ιs) (gsRoots S ℓ) v 2 x = 0 ↔
      (cohomologyMapAlong (gsFinFamily S ιs v).toMonoidHom (continuous_toMonoidHom _)
        (gsSUnitsLocalMor S ιs v) 2).hom
        ((cohomologyMap (rootsOfUnityToSUnits S (maxUnramifiedOutside K.1 ℚ̄ S) ℓ) 2).hom x) = 0 := by
  have e1 := cohomologyMap_cohomologyMapAlong (gsFinFamily S ιs v).toMonoidHom
    (continuous_toMonoidHom _) (𝟙 _) (gsRootsLocalUnitsMor S ιs ℓ v) (p := 2) x
  have e2 := cohomologyMapAlong_cohomologyMap (gsFinFamily S ιs v).toMonoidHom
    (continuous_toMonoidHom _) (rootsOfUnityToSUnits S (maxUnramifiedOutside K.1 ℚ̄ S) ℓ)
    (gsSUnitsLocalMor S ιs v) (p := 2) x
  have e3 := congrArg (fun m => (cohomologyMapAlong (gsFinFamily S ιs v).toMonoidHom
    (continuous_toMonoidHom _) m 2).hom x)
    ((Category.id_comp (gsRootsLocalUnitsMor S ιs ℓ v)).trans (gsRootsLocalUnitsMor_eq S ιs ℓ v))
  have key : (cohomologyMap (gsRootsLocalUnitsMor S ιs ℓ v) 2).hom
      (ptRes (gsFinFamily S ιs) (gsRoots S ℓ) v 2 x) =
      (cohomologyMapAlong (gsFinFamily S ιs v).toMonoidHom (continuous_toMonoidHom _)
        (gsSUnitsLocalMor S ιs v) 2).hom
        ((cohomologyMap (rootsOfUnityToSUnits S (maxUnramifiedOutside K.1 ℚ̄ S) ℓ) 2).hom x) :=
    e1.trans (e3.trans e2.symm)
  constructor
  · intro h
    exact key.symm.trans ((congrArg (cohomologyMap (gsRootsLocalUnitsMor S ιs ℓ v) 2).hom h).trans
      (map_zero _))
  · intro h
    exact cohomologyMap_gsRootsLocalUnitsMor_injective S ιs ℓ hℓS v ((key.trans h).trans (map_zero _).symm)

variable {ℓ} (hℓ : ℓ.Prime)



omit [NeZero ℓ] in
include hℓS hℓ in
theorem eq_zero_of_gsSUnitsLocalMor_eq_zero (hK : Odd ℓ ∨ IsTotallyComplex K.1)
    (y : cohomology (galSUnitsMax K.1 ℚ̄ S) 2) (hy : ℓ • y = 0)
    (hloc : ∀ v : S, (cohomologyMapAlong (gsFinFamily S ιs v).toMonoidHom (continuous_toMonoidHom _)
      (gsSUnitsLocalMor S ιs v) 2).hom y = 0) : y = 0 := by
  classical
  have hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S := fun v hv => by
    by_contra h
    exact hℓS v h hv
  have hy1 : ℓ ^ 1 • y = 0 := by rw [pow_one]; exact hy
  refine eq_zero_of_sUnitsBrauer_eq_zero K S ℓ hℓ hS y 1 hy1 ?_
  refine eq_zero_of_brauerLocal_apply_eq_zero (gsLocalEmbeddings S ιs) _ fun w => ?_
  rcases w with w | w
  · apply placeInv_injective (K := K) (.inl w)
    refine (placeInv_inl_eq_zero (ℓ ^ 1) (hK.imp (fun h => h.pow) id) w _ ?_).trans (map_zero _).symm
    have e : ℓ ^ 1 • brauerLocal (gsLocalEmbeddings S ιs) (sUnitsBrauer K S y) = 0 := by
      rw [← map_nsmul, ← map_nsmul, hy1, map_zero, map_zero]
    exact (map_nsmul (DFinsupp.evalAddMonoidHom (β := fun w => localGaloisCohomology K 2 w)
      (Sum.inl w : Place K.1)) (ℓ ^ 1) _).symm.trans
      ((congrArg (DFinsupp.evalAddMonoidHom (β := fun w => localGaloisCohomology K 2 w)
        (Sum.inl w : Place K.1)) e).trans (map_zero _))
  · by_cases hw : w ∈ S
    · refine (congrArg (fun z => brauerLocal (gsLocalEmbeddings S ιs) z (.inr w))
        (sUnitsBrauer_apply K S _)).trans ?_
      refine (brauerLocal_gsBrauerInfl_inr K S (gsLocalEmbeddings S ιs) w _).trans ?_
      have hfin : (gsLocalEmbeddings S ιs).fin w = ιs ⟨w, hw⟩ := gsLocalEmbeddings_fin S ιs ⟨w, hw⟩
      rw [hfin]
      refine (gsLocalRes_sUnitsToUnits_eq S ιs ⟨w, hw⟩ _).trans ?_
      rw [hloc ⟨w, hw⟩, map_zero, map_zero]
      rfl
    · exact brauerLocal_sUnitsBrauer_inr K S _ _ w hw


include hℓS hℓ in
theorem mem_ptSha_iff_cohomologyMap_eq_zero (hK : Odd ℓ ∨ IsTotallyComplex K.1)
    (x : cohomology (gsRoots S ℓ) 2) :
    x ∈ ptSha (gsFinFamily S ιs) (gsRoots S ℓ) 2 ↔
      (cohomologyMap (rootsOfUnityToSUnits S (maxUnramifiedOutside K.1 ℚ̄ S) ℓ) 2).hom x = 0 := by
  rw [mem_ptSha]
  constructor
  · intro hx
    have hloc : ∀ v : S, (cohomologyMapAlong (gsFinFamily S ιs v).toMonoidHom (continuous_toMonoidHom _)
        (gsSUnitsLocalMor S ιs v) 2).hom
        ((cohomologyMap (rootsOfUnityToSUnits S (maxUnramifiedOutside K.1 ℚ̄ S) ℓ) 2).hom x) = 0 :=
      fun v => (ptRes_eq_zero_iff S ιs ℓ hℓS v x).1 (congrFun hx v)
    have h0 : (cohomologyMap (ℓ • 𝟙 (galSUnitsMax K.1 ℚ̄ S)) 2).hom
        ((cohomologyMap (rootsOfUnityToSUnits S (maxUnramifiedOutside K.1 ℚ̄ S) ℓ) 2).hom x) = 0 :=
      cohomologyMap_g_cohomologyMap_f_apply
        (S := sUnitsKummerSequence S (maxUnramifiedOutside K.1 ℚ̄ S) ℓ) 2 x
    exact eq_zero_of_gsSUnitsLocalMor_eq_zero S ιs hℓS hℓ hK _
      ((cohomologyMap_nsmul_id_apply (galSUnitsMax K.1 ℚ̄ S) ℓ 2 _).symm.trans h0) hloc
  · intro hy
    funext v
    exact (ptRes_eq_zero_iff S ιs ℓ hℓS v x).2 ((congrArg _ hy).trans (map_zero _))


end

end GroundTheory.ProfCoh
end
end

-- Source module: GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.KummerShaOpen

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IsDedekindDomain GroundTheory.Global

noncomputable section

attribute [local instance 2000] Rep.hV2

local notation "ℚ̄" => AlgebraicClosure ℚ

local instance kummerShaOpenScalarTower {K L : FiniteSubfield} [Fact (K ≤ L)] :
    IsScalarTower K.1 L.1 ℚ̄ :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

variable {K L : FiniteSubfield} [Fact (K ≤ L)] {S : Set (HeightOneSpectrum (𝓞 K.1))}
  (hL : ∀ x : L.1, algebraMap L.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S)
  (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))



theorem ptCompactToGlobal_gsMackeyCompactIso (ℓ : ℕ)
    (c : compactCohomologyRes (gsFinFamily (placesOver S) (gsMackeyEmbeddings hL ιs))
      (gsRoots (placesOver S : Set (HeightOneSpectrum (𝓞 L.1))) ℓ) 2) :
    (ptCompactToGlobal (mackeyFamily (gsOpenSubgroup S hL) (gsFinFamily S ιs))
      (Rep.res (gsSubtype S hL) (gsRoots S ℓ)) 2).hom
        ((gsMackeyCompactIso hL ιs (gsRootsOfUnityIso S hL ℓ).symm 2).hom.hom c) =
      (gsRootsOfUnityCohomologyIso S hL ℓ 2).hom.hom
        ((ptCompactToGlobal (gsFinFamily (placesOver S) (gsMackeyEmbeddings hL ιs))
          (gsRoots (placesOver S : Set (HeightOneSpectrum (𝓞 L.1))) ℓ) 2).hom c) := by
  have hT := compactTransport_compactToGlobal (mackeyFamily (gsOpenSubgroup S hL) (gsFinFamily S ιs))
    (gsFinFamily (placesOver S) (gsMackeyEmbeddings hL ιs)) (gsBaseChange S hL) (mackeyPlaceEquiv S hL ιs)
    (fun p => gsMackeyLocalEquiv hL ιs p.1 p.2.out) (gsBaseChange_mackeyFamily_eq hL ιs)
    (gsRootsOfUnityIso S hL ℓ).symm.hom 2
  have hG : (gsRootsOfUnityCohomologyIso S hL ℓ 2).hom =
      cohomologyMapAlong (gsBaseChange S hL).toMulEquiv.toMonoidHom
        (continuous_mulEquiv_toMonoidHom (gsBaseChange S hL)) (gsRootsOfUnityIso S hL ℓ).symm.hom 2 :=
    cohomologyIsoOfContinuousMulEquiv_hom _ _ 2
  have hC : (gsMackeyCompactIso hL ιs (gsRootsOfUnityIso S hL ℓ).symm 2).hom =
      compactTransport (mackeyFamily (gsOpenSubgroup S hL) (gsFinFamily S ιs))
        (gsFinFamily (placesOver S) (gsMackeyEmbeddings hL ιs)) (gsBaseChange S hL) (mackeyPlaceEquiv S hL ιs)
        (fun p => gsMackeyLocalEquiv hL ιs p.1 p.2.out) (gsBaseChange_mackeyFamily_eq hL ιs)
        (gsRootsOfUnityIso S hL ℓ).symm.hom 2 :=
    gsMackeyCompactIso_hom hL ιs _ 2
  have s1 := congrArg (fun ψ => (ptCompactToGlobal (mackeyFamily (gsOpenSubgroup S hL) (gsFinFamily S ιs))
    (Rep.res (gsSubtype S hL) (gsRoots S ℓ)) 2).hom (ψ.hom c)) hC
  have s3 := congrArg (fun ψ => ψ.hom ((ptCompactToGlobal (gsFinFamily (placesOver S) (gsMackeyEmbeddings hL ιs))
        (gsRoots (placesOver S : Set (HeightOneSpectrum (𝓞 L.1))) ℓ) 2).hom c)) hG
  have s2 := congrArg (fun φ => φ.hom c) hT
  exact s1.trans (s2.trans s3.symm)



theorem mem_ptSha_mackey_iff (ℓ : ℕ)
    (x : cohomology (gsRoots (placesOver S : Set (HeightOneSpectrum (𝓞 L.1))) ℓ) 2) :
    (gsRootsOfUnityCohomologyIso S hL ℓ 2).hom.hom x ∈
        ptSha (mackeyFamily (gsOpenSubgroup S hL) (gsFinFamily S ιs))
          (Rep.res (gsSubtype S hL) (gsRoots S ℓ)) 2 ↔
      x ∈ ptSha (gsFinFamily (placesOver S) (gsMackeyEmbeddings hL ιs))
        (gsRoots (placesOver S : Set (HeightOneSpectrum (𝓞 L.1))) ℓ) 2 := by
  constructor
  · intro hx
    obtain ⟨c, hc⟩ := exists_ptCompactToGlobal_eq_of_mem_ptSha
      (mackeyFamily (gsOpenSubgroup S hL) (gsFinFamily S ιs)) (Rep.res (gsSubtype S hL) (gsRoots S ℓ)) hx
    obtain ⟨c', hc'⟩ := (gsMackeyCompactIso hL ιs (gsRootsOfUnityIso S hL ℓ).symm 2).toLinearEquiv.surjective c
    have h1 := (ptCompactToGlobal_gsMackeyCompactIso hL ιs ℓ c').symm.trans
      ((congrArg (ptCompactToGlobal (mackeyFamily (gsOpenSubgroup S hL)
        (gsFinFamily S ιs)) (Rep.res (gsSubtype S hL) (gsRoots S ℓ)) 2).hom hc').trans hc)
    have h2 := (gsRootsOfUnityCohomologyIso S hL ℓ 2).toLinearEquiv.injective h1
    exact (congrArg (· ∈ ptSha (gsFinFamily (placesOver S) (gsMackeyEmbeddings hL ιs))
      (gsRoots (placesOver S : Set (HeightOneSpectrum (𝓞 L.1))) ℓ) 2) h2).mp
      (ptCompactToGlobal_mem_ptSha (gsFinFamily (placesOver S) (gsMackeyEmbeddings hL ιs))
        (gsRoots (placesOver S : Set (HeightOneSpectrum (𝓞 L.1))) ℓ) c')
  · intro hx
    have hc := exists_ptCompactToGlobal_eq_of_mem_ptSha _ _ hx
    obtain ⟨c', hc'⟩ := hc
    have h1 := (ptCompactToGlobal_gsMackeyCompactIso hL ιs ℓ c').trans
      (congrArg (gsRootsOfUnityCohomologyIso S hL ℓ 2).hom.hom hc')
    exact (congrArg (· ∈ ptSha (mackeyFamily (gsOpenSubgroup S hL) (gsFinFamily S ιs))
      (Rep.res (gsSubtype S hL) (gsRoots S ℓ)) 2) h1).mp
      (ptCompactToGlobal_mem_ptSha (mackeyFamily (gsOpenSubgroup S hL) (gsFinFamily S ιs))
        (Rep.res (gsSubtype S hL) (gsRoots S ℓ))
        ((gsMackeyCompactIso hL ιs (gsRootsOfUnityIso S hL ℓ).symm 2).hom.hom c'))

theorem gsRootsOfUnityIso_symm_comp_rootsOfUnityToSUnits (ℓ : ℕ) [NeZero ℓ] :
    (gsRootsOfUnityIso S hL ℓ).symm.hom ≫ (Rep.resFunctor (gsSubtype S hL)).map
        (rootsOfUnityToSUnits S (maxUnramifiedOutside K.1 ℚ̄ S) ℓ) =
      (Rep.resFunctor (gsBaseChange S hL).toMulEquiv.toMonoidHom).map
        (rootsOfUnityToSUnits (placesOver S) (maxUnramifiedOutside L.1 ℚ̄ (placesOver S)) ℓ) ≫
        (gsSUnitsIso S hL).symm.hom :=
  Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun _ => rfl))



theorem cohomologyMap_rootsOfUnityToSUnits_gsRootsOfUnityCohomologyIso (ℓ : ℕ) [NeZero ℓ]
    (x : cohomology (gsRoots (placesOver S : Set (HeightOneSpectrum (𝓞 L.1))) ℓ) 2) :
    (cohomologyMap ((Rep.resFunctor (gsSubtype S hL)).map
        (rootsOfUnityToSUnits S (maxUnramifiedOutside K.1 ℚ̄ S) ℓ)) 2).hom
        ((gsRootsOfUnityCohomologyIso S hL ℓ 2).hom.hom x) =
      (gsSUnitsCohomologyIso S hL 2).hom.hom
        ((cohomologyMap (rootsOfUnityToSUnits (placesOver S)
          (maxUnramifiedOutside L.1 ℚ̄ (placesOver S)) ℓ) 2).hom x) := by
  have hG : (gsRootsOfUnityCohomologyIso S hL ℓ 2).hom =
      cohomologyMapAlong (gsBaseChange S hL).toMulEquiv.toMonoidHom
        (continuous_mulEquiv_toMonoidHom (gsBaseChange S hL)) (gsRootsOfUnityIso S hL ℓ).symm.hom 2 :=
    cohomologyIsoOfContinuousMulEquiv_hom _ _ 2
  have hO : (gsSUnitsCohomologyIso S hL 2).hom =
      cohomologyMapAlong (gsBaseChange S hL).toMulEquiv.toMonoidHom
        (continuous_mulEquiv_toMonoidHom (gsBaseChange S hL)) (gsSUnitsIso S hL).symm.hom 2 :=
    cohomologyIsoOfContinuousMulEquiv_hom _ _ 2
  have s1 := congrArg (fun ψ => (cohomologyMap ((Rep.resFunctor (gsSubtype S hL)).map
    (rootsOfUnityToSUnits S (maxUnramifiedOutside K.1 ℚ̄ S) ℓ)) 2).hom (ψ.hom x)) hG
  have s4 := congrArg (fun ψ => ψ.hom ((cohomologyMap (rootsOfUnityToSUnits (placesOver S)
    (maxUnramifiedOutside L.1 ℚ̄ (placesOver S)) ℓ) 2).hom x)) hO
  have s2 := cohomologyMap_cohomologyMapAlong (gsBaseChange S hL).toMulEquiv.toMonoidHom
    (continuous_mulEquiv_toMonoidHom (gsBaseChange S hL)) (gsRootsOfUnityIso S hL ℓ).symm.hom
    ((Rep.resFunctor (gsSubtype S hL)).map (rootsOfUnityToSUnits S (maxUnramifiedOutside K.1 ℚ̄ S) ℓ))
    (p := 2) x
  have s3 := cohomologyMapAlong_cohomologyMap (gsBaseChange S hL).toMulEquiv.toMonoidHom
    (continuous_mulEquiv_toMonoidHom (gsBaseChange S hL))
    (rootsOfUnityToSUnits (placesOver S) (maxUnramifiedOutside L.1 ℚ̄ (placesOver S)) ℓ)
    (gsSUnitsIso S hL).symm.hom (p := 2) x
  have s5 := congrArg (fun m => (cohomologyMapAlong (gsBaseChange S hL).toMulEquiv.toMonoidHom
    (continuous_mulEquiv_toMonoidHom (gsBaseChange S hL)) m 2).hom x)
    (gsRootsOfUnityIso_symm_comp_rootsOfUnityToSUnits hL ℓ)
  exact s1.trans (s2.trans (s5.trans (s3.symm.trans s4.symm)))

theorem gsRootsOfUnityCohomologyIso_hom_inv_apply (ℓ : ℕ)
    (x : cohomology (Rep.res (gsSubtype S hL) (gsRoots S ℓ)) 2) :
    (gsRootsOfUnityCohomologyIso S hL ℓ 2).hom.hom ((gsRootsOfUnityCohomologyIso S hL ℓ 2).inv.hom x) = x :=
  congrArg (fun φ => φ.hom x) (gsRootsOfUnityCohomologyIso S hL ℓ 2).inv_hom_id



theorem mem_ptSha_mackey_iff_of_eq (ℓ : ℕ)
    {x' : cohomology (gsRoots (placesOver S : Set (HeightOneSpectrum (𝓞 L.1))) ℓ) 2}
    {x : cohomology (Rep.res (gsSubtype S hL) (gsRoots S ℓ)) 2}
    (hx : (gsRootsOfUnityCohomologyIso S hL ℓ 2).hom.hom x' = x) :
    x ∈ ptSha (mackeyFamily (gsOpenSubgroup S hL) (gsFinFamily S ιs))
        (Rep.res (gsSubtype S hL) (gsRoots S ℓ)) 2 ↔
      x' ∈ ptSha (gsFinFamily (placesOver S) (gsMackeyEmbeddings hL ιs))
        (gsRoots (placesOver S : Set (HeightOneSpectrum (𝓞 L.1))) ℓ) 2 := by
  subst hx
  exact mem_ptSha_mackey_iff hL ιs ℓ x'



theorem cohomologyMap_rootsOfUnityToSUnits_eq_zero_iff_of_eq (ℓ : ℕ) [NeZero ℓ]
    {x' : cohomology (gsRoots (placesOver S : Set (HeightOneSpectrum (𝓞 L.1))) ℓ) 2}
    {x : cohomology (Rep.res (gsSubtype S hL) (gsRoots S ℓ)) 2}
    (hx : (gsRootsOfUnityCohomologyIso S hL ℓ 2).hom.hom x' = x) :
    (cohomologyMap (rootsOfUnityToSUnits (placesOver S)
      (maxUnramifiedOutside L.1 ℚ̄ (placesOver S)) ℓ) 2).hom x' = 0 ↔
      (cohomologyMap ((Rep.resFunctor (gsSubtype S hL)).map
        (rootsOfUnityToSUnits S (maxUnramifiedOutside K.1 ℚ̄ S) ℓ)) 2).hom x = 0 := by
  subst hx
  rw [cohomologyMap_rootsOfUnityToSUnits_gsRootsOfUnityCohomologyIso hL ℓ x']
  constructor
  · intro h0
    rw [h0, map_zero]
  · intro h0
    exact (gsSUnitsCohomologyIso S hL 2).toLinearEquiv.injective (h0.trans (map_zero _).symm)



theorem mem_ptSha_mackey_iff_exists_kummerModN {ℓ : ℕ} [NeZero ℓ] (hℓ : ℓ.Prime)
    (hℓS : ∀ v ∉ S, ((ℓ : ℕ) : 𝓞 K.1) ∉ v.asIdeal) (hK : Odd ℓ ∨ IsTotallyComplex L.1)
    (x : cohomology (Rep.res (gsSubtype S hL) (gsRoots S ℓ)) 2) :
    x ∈ ptSha (mackeyFamily (gsOpenSubgroup S hL) (gsFinFamily S ιs))
        (Rep.res (gsSubtype S hL) (gsRoots S ℓ)) 2 ↔
      ∃ y, kummerModNHom (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
        (gsKummer_shortExact S ℓ hℓS) 1 y = x := by
  have hn : ∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S := fun v hv => by
    by_contra h
    exact hℓS v h hv
  have hℓS' : ∀ w ∉ (placesOver S : Set (HeightOneSpectrum (𝓞 L.1))), ((ℓ : ℕ) : 𝓞 L.1) ∉ w.asIdeal :=
    natCast_not_mem_of_not_mem_placesOver hn
  have hx' := gsRootsOfUnityCohomologyIso_hom_inv_apply hL ℓ x
  refine (mem_ptSha_mackey_iff_of_eq hL ιs ℓ hx').trans
    ((mem_ptSha_iff_cohomologyMap_eq_zero (K := L) (placesOver S : Set (HeightOneSpectrum (𝓞 L.1)))
      (gsMackeyEmbeddings hL ιs) hℓS' hℓ hK ((gsRootsOfUnityCohomologyIso S hL ℓ 2).inv.hom x)).trans
    ((cohomologyMap_rootsOfUnityToSUnits_eq_zero_iff_of_eq hL ℓ hx').trans
    (Iff.trans ?_ (kummerTorsHom_eq_zero_iff (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
      (gsKummer_shortExact S ℓ hℓS) 1 x))))
  exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩

end

end GroundTheory.ProfCoh
end
end
