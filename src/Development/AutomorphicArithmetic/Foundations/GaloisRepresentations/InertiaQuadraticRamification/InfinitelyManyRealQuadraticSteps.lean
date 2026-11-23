module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.InertiaGenAlt
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.ThreeApartOf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.AllUnr
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.ApartUp
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.ConjOfSqNonneg
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.DecPow
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.Double
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.ExistsPlaceOfPrime
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.FreshChar
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.FreshPrime
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.InclOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.InertiaGenAlt
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.InertiaGen
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.InfOf
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAbelianOverSubfield
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSolvableCmExtensionAbelianCompletion
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSolvableCmExtensionSplitPlace
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.GelfandKazhdanReal
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.NormRam
import Mathlib.Algebra.Order.Star.Int
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.QuadraticCharTwistOfExistsOfInfinity
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.RootMod
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.BaseChangeIsomorphicFields
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspRepSatakeIffLocalComponentSatakeStatement
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.FormsFiniteGL
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.QuadraticCharTwistOfExistsOfInfinity
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.ValuationLeOneOfInteger
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.SplitIff
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.SplitPlace
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.SqrtFix
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.UnrLarge

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.IndexComap

section

section

namespace UpperTheory.Gal.UnramifiedFromSplittingCriterion

theorem indexComap : IndexComap := by
  intro Γ Γ' _ _ f H H' hc hle hp ⟨τ, hτ, hτ'⟩
  have hN : H'.Normal := by
    refine ⟨fun n hn g => ?_⟩
    have h1 : g * n * g⁻¹ * n⁻¹ ∈ H' :=
      hc (Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top n))
    have h2 : g * n * g⁻¹ = (g * n * g⁻¹ * n⁻¹) * n := by group
    rw [h2]
    exact H'.mul_mem h1 hn
  rw [Subgroup.relIndex_comap]
  set J := (H.comap f).map f with hJ
  have hJH : J ≤ H := Subgroup.map_comap_le _ _
  have hmul : H'.relIndex (H' ⊔ J) * (H' ⊔ J).relIndex H = H'.relIndex H :=
    Subgroup.relIndex_mul_relIndex _ _ _ le_sup_left (sup_le hle hJH)
  rw [Subgroup.relIndex_sup_left] at hmul
  have hne : H'.relIndex J ≠ 1 := by
    intro h
    rw [Subgroup.relIndex_eq_one] at h
    exact hτ' (h ⟨τ, hτ, rfl⟩)
  exact (hp.eq_one_or_self_of_dvd _ ⟨_, hmul.symm⟩).resolve_left hne

end UpperTheory.Gal.UnramifiedFromSplittingCriterion
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.LayerOf

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published
open UpperTheory.Gal.UnramifiedFromSplittingCriterion

theorem UpperTheory.Gal.UnramifiedFromSplittingCriterion.layerOf :
    InclOf → IndexComap → LayerOf := by
  intro hIncl hIdx
  unfold LayerOf
  intro E Ω _ _ _ _ _ _ S H H' hH' hle hp X Y hX hY u hS hDec hτex
  obtain ⟨A, hA, τ, hτ, hτ'⟩ := hτex
  unfold Cuts at hX hY
  have overUnder : ∀ (B : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)), IsPlaceOver B w →
      IsPlaceOver B (w.under (𝓞 (maximalRealSubfield E))) := by
    intro B w hB x
    rw [HeightOneSpectrum.under_asIdeal, Ideal.under, Ideal.mem_comap, ← hB]
    rfl
  have resLift : ∀ (g : G (maximalRealSubfield E) Ω) (hg : Fixes E g),
      AlgEquiv.restrictScalarsHom (maximalRealSubfield E) (GlobalTheory.AboveL.DecRes.lift (E := E) g hg) = g :=
    fun g hg => AlgEquiv.ext fun x => rfl
  have hτD := Ine_le_Dec A hτ
  obtain ⟨hτE, hτH⟩ := hDec A hA τ hτD
  obtain ⟨τ', hres⟩ : ∃ τ' : G E Ω, AlgEquiv.restrictScalarsHom (maximalRealSubfield E) τ' = τ :=
    ⟨_, resLift τ hτE⟩
  have fY : fixGrp E Ω Y.K = H'.comap (AlgEquiv.restrictScalarsHom (maximalRealSubfield E)) :=
    Subgroup.ext fun g => hY g
  have fX : fixGrp E Ω X.K = H.comap (AlgEquiv.restrictScalarsHom (maximalRealSubfield E)) :=
    Subgroup.ext fun g => hX g
  have hidx := hIdx (G (maximalRealSubfield E) Ω) (G E Ω)
    (AlgEquiv.restrictScalarsHom (maximalRealSubfield E)) H H' hH'.comm hle hp
    ⟨τ', by rw [hres]; exact hτH, by rw [hres]; exact hτ'⟩
  obtain ⟨x0, t0E, t0Ω, hgal, hfin⟩ := hIncl E Ω X Y (by rw [fY, fX]; exact Subgroup.comap_mono hle)
  rw [fY, fX, hidx] at hfin
  obtain ⟨w, hw⟩ := GlobalTheory.AbOverSubfield.exists_place_between (F := maximalRealSubfield E) (K := E) hA
  have hwu : w.under (𝓞 (maximalRealSubfield E)) = u := eq_of_isPlaceOver (overUnder A w hw) hA
  have hfixX : Fixes X.K τ' := (hX τ').2 (by rw [hres]; exact hτH)
  refine ⟨⟨x0, t0E, t0Ω, hgal, by rw [hfin]; exact hp, w, ?_, ?_, A, hw,
    GlobalTheory.AboveL.DecRes.lift (E := X.K) τ' hfixX, ?_, ?_⟩, ?_⟩
  · intro hwS
    exact hS w hwS hwu
  · intro B hB g hg
    have hBu : IsPlaceOver B u := by
      rw [← hwu]
      exact overUnder B w hB
    obtain ⟨hgE, hgH⟩ := hDec B hBu g hg
    refine ⟨hgE, ?_⟩
    have h1 := (hX (GlobalTheory.AboveL.DecRes.lift (E := E) g hgE)).2 (by rw [resLift]; exact hgH)
    exact h1
  · subst hres
    rw [mem_Ine]
    have hτI := (mem_Ine (A := A)).1 hτ
    exact ⟨(GlobalTheory.AboveL.mem_dec_congr A _ _ (fun x => rfl)).2 hτI.1, hτI.2⟩
  · intro hfix
    exact hτ' (by rw [← hres]; exact (hY τ').1 hfix)
  · intro x1 t1
    have hx : x1 = x0 := by
      refine Algebra.algebra_ext _ _ fun r => (algebraMap Y.K Ω).injective ?_
      rw [← @IsScalarTower.algebraMap_apply X.K Y.K Ω _ _ _ x1 _ _ t1 r,
        ← @IsScalarTower.algebraMap_apply X.K Y.K Ω _ _ _ x0 _ _ t0Ω r]
    subst hx
    exact hfin
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.PowChar

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published
open UpperTheory.Gal.UnramifiedFromSplittingCriterion

theorem UpperTheory.Gal.UnramifiedFromSplittingCriterion.powChar :
    PowChar := by
  intro p _ n hn hdvd
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  have hcard : Nat.card (ZMod p)ˣ = p - 1 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units]
  have hog : orderOf g = p - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, hcard]
  have hprim := Complex.isPrimitiveRoot_exp n hn.ne'
  obtain ⟨ω, hωc⟩ := hprim.isUnit hn.ne'
  have hωp : IsPrimitiveRoot ω n := by
    rw [← IsPrimitiveRoot.coe_units_iff, hωc]
    exact hprim
  have hωo : orderOf ω = n := hωp.eq_orderOf.symm
  have hnd : n ∣ p - 1 := Dvd.dvd.trans (Dvd.intro_left 2 rfl) hdvd
  have hd : orderOf ω ∣ orderOf g := by rw [hωo, hog]; exact hnd
  let lam : (ZMod p)ˣ →* ℂˣ := monoidHomOfForallMemZpowers hg hd
  have hlg : lam g = ω := monoidHomOfForallMemZpowers_apply_gen hg hd
  have hωn : ω ^ n = 1 := hωp.pow_eq_one
  have hpow : ∀ a, (lam a) ^ n = 1 := by
    intro a
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg a)
    rw [map_zpow, hlg, ← zpow_natCast, zpow_comm, zpow_natCast, hωn, one_zpow]
  refine ⟨lam, ?_, ?_, ?_⟩
  · ext1 a
    rw [MonoidHom.pow_apply, hpow, MonoidHom.one_apply]
  · obtain ⟨c, hc⟩ := hdvd
    have hcpos : 0 < c := by
      rcases Nat.eq_zero_or_pos c with h | h
      · subst h
        omega
      · exact h
    have hx2 : (g ^ (n * c)) ^ 2 = 1 := by
      rw [← pow_mul, show n * c * 2 = p - 1 by rw [hc]; ring, ← hog, pow_orderOf_eq_one]
    have hx1 : g ^ (n * c) ≠ 1 := by
      intro h
      have h1 := orderOf_dvd_of_pow_eq_one h
      rw [hog, hc] at h1
      have h2 := Nat.le_of_dvd (Nat.mul_pos hn hcpos) h1
      have h3 : 0 < n * c := Nat.mul_pos hn hcpos
      nlinarith
    have hxm : g ^ (n * c) = -1 := by
      have h4 : (((g ^ (n * c) : (ZMod p)ˣ)) : ZMod p) ^ 2 = 1 := by
        rw [← Units.val_pow_eq_pow_val, hx2, Units.val_one]
      rw [sq] at h4
      rcases mul_self_eq_one_iff.mp h4 with h | h
      · exact absurd (Units.ext (by rw [h, Units.val_one])) hx1
      · exact Units.ext (by rw [h, Units.val_neg, Units.val_one])
    rw [← hxm, map_pow, hlg, pow_mul, hωn, one_pow]
  · intro a ha
    have htop : Subgroup.zpowers a = ⊤ := by
      apply Subgroup.eq_top_of_card_eq
      rw [Nat.card_zpowers, ha, hcard]
    have hga : g ∈ Subgroup.zpowers a := by rw [htop]; trivial
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hga
    have hωa : (lam a) ^ j = ω := by rw [← map_zpow, hlg]
    apply Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one (hpow a))
    rw [← hωo]
    apply orderOf_dvd_of_pow_eq_one
    rw [← hωa, ← zpow_natCast, zpow_comm, zpow_natCast, pow_orderOf_eq_one, one_zpow]
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.SatSplit

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published

namespace UpperTheory.Gal.UnramifiedFromSplittingCriterion

theorem satSplit : SatSplit := by
  intro K M Ω _ _ _ _ _ _ _ _ _ _ _ _ A v w hv hw hD a π P hP B hB
  obtain ⟨i, hi, hi', hiv⟩ := splitIso_holds K M Ω A v w hv hw hD
  obtain ⟨σ, hσ, -⟩ := GlobalTheory.CuspRep.LocEx.exists_isLocComp UpperTheory.V.Af.formsFiniteGL K a π v
  obtain ⟨σ', hσ', -⟩ := GlobalTheory.CuspRep.LocEx.exists_isLocComp UpperTheory.V.Af.formsFiniteGL M a P w
  obtain ⟨e, he⟩ := hP v w i hi hi' σ σ' hσ hσ'
  obtain ⟨φ, hφ⟩ := exists_isFrob hv
  have hq : normV w = normV v ^ 1 := degOf K M Ω A v w hv hw (fun τ hτ => hD τ (Ine_le_Dec A hτ)) φ 1 one_pos hφ
    fun k => ⟨fun _ => one_dvd k, fun _ => hD _ (pow_mem (show φ ∈ Dec (F := K) A from hφ.1) k)⟩
  rw [pow_one] at hq
  refine ((GlobalTheory.T.cuspRep_satake_iff_localComponent_satake M a P w σ' hσ').1 B).2 (GlobalTheory.IsoPull.hasSatGL_of_ringEquiv i hiv ?_ e (fun g x => (he g x).symm)
    (((GlobalTheory.T.cuspRep_satake_iff_localComponent_satake K a π v σ hσ).1 B).1 hB))
  first | exact hq | (unfold normV at hq; simp only [Formalism.UG.qV, Ideal.absNorm_apply, Submodule.cardQuot_apply]; exact hq)

end UpperTheory.Gal.UnramifiedFromSplittingCriterion
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.InfinitelyManyRealQuadraticSteps

section

@[expose] public section

namespace UpperTheory.Gal.UnramifiedFromSplittingCriterion

theorem freshChar_holds : FreshChar := freshChar powChar inertiaGen decPow (freshPrime splitPlace rootMod)
theorem layerOf_holds : LayerOf := layerOf inclOf indexComap
theorem noSelfTwist_holds : NoSelfTwist := noSelfTwist_of normRam
theorem infinitely_many_real_quadratic_steps : Quad0 := quadraticCharTwist_of_exists_of_infinity (quad0Ex sqrtFix mkQ unrLarge) infOf
theorem allUnr_holds : AllUnr := allUnr splitIff
theorem threeApart_holds : ThreeApart := threeApart_of double apartUp
theorem satSplit_holds : SatSplit := satSplit

end UpperTheory.Gal.UnramifiedFromSplittingCriterion
end
end
