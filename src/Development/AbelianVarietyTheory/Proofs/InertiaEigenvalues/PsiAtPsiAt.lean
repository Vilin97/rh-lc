module

public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CommutingEndomorphismCondition
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConductorRootSubOneLengthLeTameValueStatement
public import Formalism.LocalRingCardinality.DataNChTie
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LatticeConditions
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CrystallineCocycleTransportConjugation
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
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TypeChangeInjectiveCoefficients
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NlenLeLenN
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SPiTopEqSTLoc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedRhoConjLatTpsi
import Mathlib.RingTheory.PiTensorProduct
import Std.Tactic.BVDecide.Normalize.Prop
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.TwoPowS0EqTwoPartModulus

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.SameCharacterCommonExtension

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions

namespace GlobalTheory.Proof.dvr_of_reflects_facts

theorem dvr_of_reflects {O A : Type} [CommRing O] [IsDomain O] [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] (g : O →+* A) (hg : Function.Injective g)
    (hd : ∀ x y, g x ∣ g y → x ∣ y) (t : O) (ht0 : t ≠ 0) (ht : ¬ IsUnit t) :
    IsDiscreteValuationRing O := by
  haveI : ValuationRing O := ValuationRing.iff_dvd_total.2
    ⟨fun x y => (ValuationRing.dvd_total (g x) (g y)).imp (hd x y) (hd y x)⟩
  haveI : WfDvdMonoid O := by
    refine Subrelation.wf (r := InvImage DvdNotUnit g) ?_ (InvImage.wf g wellFounded_dvdNotUnit)
    rintro x y ⟨hx, c, hc, rfl⟩
    refine ⟨fun h => hx (hg (by simpa using h)), g c, fun h => hc ?_, by simp⟩
    exact isUnit_of_dvd_one (hd c 1 (by simpa using h.dvd))
  haveI : IsPrincipalIdealRing O := ((IsBezout.tfae (R := O)).out 4 2).1 ‹WfDvdMonoid O›
  refine { not_a_field' := fun h => ht0 ?_ }
  have : t ∈ IsLocalRing.maximalIdeal O := ht
  rw [h] at this
  simpa using this

theorem common_of_field {O₀ A B K : Type} [CommRing O₀] [IsDomain O₀] [IsDiscreteValuationRing O₀]
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Field K]
    (fA : O₀ →+* A) (fB : O₀ →+* B) (hAi : fA.IsIntegral) (hB : Function.Injective fB)
    (hBl : IsLocalHom fB) (f₀ : O₀ →+* K) (jA : K →+* FractionRing A) (jB : K →+* FractionRing B)
    (hjA : ∀ c, jA (f₀ c) = algebraMap A _ (fA c)) (hjB : ∀ c, jB (f₀ c) = algebraMap B _ (fB c)) :
    ∃ (O₁ : Subring K) (_ : IsDiscreteValuationRing O₁) (f : O₀ →+* O₁) (gA : O₁ →+* A) (gB : O₁ →+* B),
      (∀ x, x ∈ O₁ ↔ ∃ a, algebraMap A _ a = jA x) ∧
      (∀ x, algebraMap A _ (gA x) = jA x) ∧ (∀ x, algebraMap B _ (gB x) = jB x) ∧
      Function.Injective gA ∧ Function.Injective gB ∧ IsLocalHom gA ∧ IsLocalHom gB ∧
      gA.comp f = fA ∧ gB.comp f = fB := by
  have iA := IsFractionRing.injective A (FractionRing A)
  have iB := IsFractionRing.injective B (FractionRing B)
  let O₁ : Subring K := (algebraMap A (FractionRing A)).range.comap jA
  have hmem : ∀ x, x ∈ O₁ ↔ ∃ a, algebraMap A _ a = jA x := fun x => Iff.rfl
  let f : O₀ →+* O₁ := f₀.codRestrict O₁ (fun c => (hmem _).2 ⟨fA c, (hjA c).symm⟩)
  have hf : ∀ c, (f c : K) = f₀ c := fun c => rfl
  have lift : ∀ {C : Type} [CommRing C] [IsDomain C] (j : K →+* FractionRing C),
      (∀ x : O₁, ∃ a, algebraMap C _ a = j x) → ∃ g : O₁ →+* C, ∀ x, algebraMap C _ (g x) = j x := by
    intro C _ _ j h
    have iC := IsFractionRing.injective C (FractionRing C)
    choose g hg using h
    exact ⟨{ toFun := g
             map_one' := iC (by simp [hg])
             map_mul' := fun x y => iC (by simp [hg])
             map_zero' := iC (by simp [hg])
             map_add' := fun x y => iC (by simp [hg]) }, hg⟩
  obtain ⟨gA, hgA⟩ := lift jA (fun x => (hmem x).1 x.2)
  have gAi : Function.Injective gA := fun x y h =>
    Subtype.ext (jA.injective (by rw [← hgA, ← hgA, h]))
  have cA : gA.comp f = fA := RingHom.ext fun c => iA (by rw [RingHom.comp_apply, hgA, hf, hjA])
  have hint : ∀ x : O₁, ∃ a, algebraMap B _ a = jB x := by
    intro x
    obtain ⟨p, hp, hpx⟩ := hAi (gA x)
    have h1 : p.eval₂ f x = 0 := gAi (by rw [Polynomial.hom_eval₂, cA, hpx, map_zero])
    have h2 := congrArg (jB.comp O₁.subtype) h1
    rw [Polynomial.hom_eval₂, map_zero] at h2
    refine IsIntegrallyClosed.algebraMap_eq_of_integral ⟨p.map fB, hp.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    have e : (algebraMap B (FractionRing B)).comp fB = (jB.comp O₁.subtype).comp f :=
      RingHom.ext fun c => (hjB c).symm
    rw [e]
    exact h2
  obtain ⟨gB, hgB⟩ := lift jB hint
  have gBi : Function.Injective gB := fun x y h =>
    Subtype.ext (jB.injective (by rw [← hgB, ← hgB, h]))
  have cB : gB.comp f = fB := RingHom.ext fun c => iB (by rw [RingHom.comp_apply, hgB, hf, hjB])
  have hd : ∀ x y, gA x ∣ gA y → x ∣ y := by
    rintro x y ⟨c, hc⟩
    by_cases hx : x = 0
    · have : y = 0 := gAi (by rw [hc, hx]; simp)
      simp [this]
    have hx' : (x : K) ≠ 0 := fun h => hx (Subtype.ext h)
    have hx'' : jA x ≠ 0 := by simpa using hx'
    refine ⟨⟨y / x, (hmem _).2 ⟨c, ?_⟩⟩, Subtype.ext ?_⟩
    · rw [map_div₀, eq_div_iff hx'', ← hgA, ← hgA, hc, map_mul, mul_comm]
    · simp [mul_div_cancel₀ _ hx']
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O₀
  have hcB : ∀ c, gB (f c) = fB c := fun c => by rw [← cB]; rfl
  have hnu : ¬ IsUnit (gB (f ϖ)) := fun h => hϖ.not_isUnit (hBl.map_nonunit _ (hcB ϖ ▸ h))
  have ht0 : f ϖ ≠ 0 := fun h => hϖ.ne_zero (hB (by rw [← hcB, h, map_zero, map_zero]))
  haveI hD : IsDiscreteValuationRing O₁ :=
    dvr_of_reflects gA gAi hd (f ϖ) ht0 (fun h => hnu (h.map gB))
  refine ⟨O₁, hD, f, gA, gB, hmem, hgA, hgB, gAi, gBi,
    ⟨fun x h => isUnit_of_dvd_one (hd x 1 (by simpa using h.dvd))⟩, ⟨fun x h => ?_⟩, cA, cB⟩
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O₁
  by_contra hx
  have hπx : π ∣ x := by
    have : x ∈ IsLocalRing.maximalIdeal O₁ := hx
    rwa [hπ.maximalIdeal_eq, Ideal.mem_span_singleton] at this
  have hu : IsUnit (gB π) := isUnit_of_dvd_unit (map_dvd gB hπx) h
  obtain ⟨n, u, hn⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ht0 hπ
  apply hnu
  rw [hn, map_mul, map_pow]
  exact (u.isUnit.map gB).mul (hu.pow n)

theorem common : ∀ (Γ O₀ A B : Type) [Group Γ] [CommRing O₀] [IsDomain O₀] [IsDiscreteValuationRing O₀] [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] (fA : O₀ →+* A) (fB : O₀ →+* B), Function.Injective fA → fA.IsIntegral → Function.Injective fB → IsLocalHom fB → ∀ (ψA : Γ →* Aˣ) (ψB : Γ →* Bˣ), SameChar fA fB ψA ψB → ∃ (O₁ : Type) (_ : CommRing O₁) (_ : IsDomain O₁) (_ : IsDiscreteValuationRing O₁) (f : O₀ →+* O₁) (gA : O₁ →+* A) (gB : O₁ →+* B) (ψ : Γ →* O₁ˣ), Function.Injective gA ∧ Function.Injective gB ∧ IsLocalHom gA ∧ IsLocalHom gB ∧ gA.comp f = fA ∧ gB.comp f = fB ∧ (Units.map gA.toMonoidHom).comp ψ = ψA ∧ (Units.map gB.toMonoidHom).comp ψ = ψB := by
  intro Γ O₀ A B _ _ _ _ _ _ _ _ _ _ fA fB _ hAi hB hBl ψA ψB hS
  have iA := IsFractionRing.injective A (FractionRing A)
  have iB := IsFractionRing.injective B (FractionRing B)
  letI : Algebra O₀ A := fA.toAlgebra
  letI : Algebra O₀ B := fB.toAlgebra
  let αA : MonoidAlgebra O₀ Γ →+* A :=
    (MonoidAlgebra.lift O₀ A Γ ((Units.coeHom A).comp ψA)).toRingHom
  let αB : MonoidAlgebra O₀ Γ →+* B :=
    (MonoidAlgebra.lift O₀ B Γ ((Units.coeHom B).comp ψB)).toRingHom
  have hker : ∀ F, αA F = 0 ↔ αB F = 0 := by
    intro F
    simp only [αA, αB, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MonoidAlgebra.lift_apply, Algebra.smul_def]
    exact hS _
  have aA : ∀ c, αA (algebraMap O₀ _ c) = fA c := fun c => AlgHom.commutes _ c
  have aB : ∀ c, αB (algebraMap O₀ _ c) = fB c := fun c => AlgHom.commutes _ c
  have oA : ∀ g, αA (MonoidAlgebra.of O₀ Γ g) = ψA g := fun g => MonoidAlgebra.lift_of _ g
  have oB : ∀ g, αB (MonoidAlgebra.of O₀ Γ g) = ψB g := fun g => MonoidAlgebra.lift_of _ g
  let R : Subring A := αA.range
  let q : MonoidAlgebra O₀ Γ →+* R := αA.rangeRestrict
  have hq : Function.Surjective q := αA.rangeRestrict_surjective
  let φ : R →+* B := q.liftOfSurjective hq ⟨αB, fun F hF =>
    (hker F).1 (congrArg Subtype.val (RingHom.mem_ker.1 hF))⟩
  have hφ : ∀ F, φ (q F) = αB F := fun F => RingHom.liftOfRightInverse_comp_apply _ _ _ _ F
  have φi : Function.Injective φ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro r hr
    obtain ⟨F, rfl⟩ := hq r
    exact Subtype.ext ((hker F).2 (by rw [← hφ, hr]))
  let K := FractionRing R
  let jA : K →+* FractionRing A := IsFractionRing.lift (g := (algebraMap A _).comp R.subtype)
    (iA.comp Subtype.val_injective)
  let jB : K →+* FractionRing B := IsFractionRing.lift (g := (algebraMap B _).comp φ)
    (iB.comp φi)
  let p : MonoidAlgebra O₀ Γ →+* K := (algebraMap R K).comp q
  have pA : ∀ F, jA (p F) = algebraMap A _ (αA F) := fun F => IsFractionRing.lift_algebraMap _ _
  have pB : ∀ F, jB (p F) = algebraMap B _ (αB F) := fun F => by
    rw [← hφ]; exact IsFractionRing.lift_algebraMap _ _
  obtain ⟨O₁, hD, f, gA, gB, hmem, hgA, hgB, gAi, gBi, lA, lB, cA, cB⟩ :=
    common_of_field fA fB hAi hB hBl (p.comp (algebraMap O₀ _)) jA jB
      (fun c => by rw [RingHom.comp_apply, pA, aA]) (fun c => by rw [RingHom.comp_apply, pB, aB])
  let p₁ : MonoidAlgebra O₀ Γ →+* O₁ := p.codRestrict O₁ (fun F => (hmem _).2 ⟨_, (pA F).symm⟩)
  let ψ : Γ →* O₁ˣ := (p₁.toMonoidHom.comp (MonoidAlgebra.of O₀ Γ)).toHomUnits
  refine ⟨O₁, inferInstance, inferInstance, hD, f, gA, gB, ψ, gAi, gBi, lA, lB, cA, cB, ?_, ?_⟩
  · ext g
    apply iA
    rw [← oA, ← pA]
    exact hgA _
  · ext g
    apply iB
    rw [← oB, ← pB]
    exact hgB _

end GlobalTheory.Proof.dvr_of_reflects_facts
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocalHomOfNatCast

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.PtCore
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions GlobalTheory.TwistedSelmerCompare

namespace GlobalTheory.SelmerSameChar

theorem isLocalHom_of_natCast {O B : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing B]
    (f : O →+* B) (l : ℕ) (h0 : (l : O) ≠ 0) (h : ¬ IsUnit (l : B)) : IsLocalHom f := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hu : ¬ IsUnit (f ϖ) := fun hu => h (by
    obtain ⟨n, u, hn⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h0 hϖ
    rw [← map_natCast f, hn, map_mul, map_pow]
    exact (u.isUnit.map f).mul (hu.pow n))
  refine ⟨fun x hx => ?_⟩
  by_contra hn
  have hm : x ∈ IsLocalRing.maximalIdeal O := hn
  rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton'] at hm
  obtain ⟨c, rfl⟩ := hm
  rw [map_mul] at hx
  exact hu (isUnit_of_mul_isUnit_right hx)

theorem isIntegral_of_finite {l₁ l₂ : ℕ} [i₁ : Fact l₁.Prime] [i₂ : Fact l₂.Prime] (h : l₁ = l₂) {O₀ O : Type}
    [CommRing O₀] [Algebra ℤ_[l₁] O₀] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l₂] O]
    [Module.Finite ℤ_[l₂] O] (f : O₀ →+* O) : f.IsIntegral := by
  subst h
  cases Subsingleton.elim i₁ i₂
  refine RingHom.IsIntegral.tower_top (algebraMap ℤ_[l₁] O₀) f ?_
  rw [padicInt_hom_ext (natCast_mem_maximalIdeal O) (f.comp (algebraMap ℤ_[l₁] O₀)) (algebraMap ℤ_[l₁] O)]
  exact algebraMap_isIntegral_iff.2 inferInstance

variable (D : D7)

theorem sT_congr (i : D.ntw.Tw) (s : D.ntw.Sig i) (Q : Finset (PlE D.host)) {O : Type} [CommRing O] [IsDomain O]
    {f f' : D.ntw.O0 i →+* O} (hf : Function.Injective f) (hf' : Function.Injective f')
    {ψ ψ' : Formalism.MainNotions.N.GE D.nd →* Oˣ} (h1 : f = f') (h2 : ψ = ψ') :
    sT D.loc D.ntwbr i s Q f hf ψ = sT D.loc D.ntwbr i s Q f' hf' ψ' := by
  subst h1 h2
  rfl

theorem toOk_local (i : D.ntw.Tw) (k : ℕ) : IsLocalHom (toOk D.ntw i k) := by
  have : CharZero (FractionRing (D.ntw.O0 i)) :=
    ((D.ntw.emb0 _).charZero_iff (D.ntw.emb0 _).injective).1 inferInstance
  have : CharZero (D.ntw.O0 i) := (algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i))).charZero
  refine isLocalHom_of_natCast _ (D.ntw.l i) (Nat.cast_ne_zero.2 (D.ntw.lPrime i).out.ne_zero) fun hu => ?_
  have := D.ntw.Ok_fin i k
  have := RingHom.IsIntegral.isLocalHom (f := algebraMap (D.ntw.O i) (D.ntw.Ok i k))
    (algebraMap_isIntegral_iff.2 inferInstance) (D.ntw.Ok_inj i k)
  rw [← map_natCast (algebraMap (D.ntw.O i) (D.ntw.Ok i k))] at hu
  exact D.ntw.O_l i (isUnit_of_map_unit _ _ hu)

theorem sTLoc_eq : ∀ (D : D7) (a : D.nd.Loc) (s : D.ntw.Sig (D.ntw.twOf a)) (k : ℕ) (ψ : Formalism.MainNotions.N.GE D.nd →* (D.ntw.Ok (D.ntw.twOf a) k)ˣ), GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.SameChar (D.ntw.twist₂ a) (GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.toOk D.ntw (D.ntw.twOf a) k) (D.ntw.psiL a) ψ → GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.sTLoc D a s = GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.sT D.loc D.ntwbr (D.ntw.twOf a) s (D.nd.Q a) (GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.toOk D.ntw (D.ntw.twOf a) k) (GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.toOk_inj D.ntw (D.ntw.twOf a) k) ψ := by
  intro D a s k ψ h
  obtain ⟨O₁, _, _, _, f, gA, gB, χ, iA, iB, lA, lB, cA, cB, eA, eB⟩ :=
    GlobalTheory.Proof.dvr_of_reflects_facts.common _ _ _ _ (D.ntw.twist₂ a) (toOk D.ntw _ k) (twO_inj D.ntw a)
      (isIntegral_of_finite (D.ntw.twOf_l a) _) (toOk_inj D.ntw _ k) (toOk_local D _ k) _ _ h
  have hf : Function.Injective f := Function.Injective.of_comp (f := gA) (by
    rw [← RingHom.coe_comp, cA]; exact twO_inj D.ntw a)
  exact (sT_congr D _ s _ _ (iA.comp hf) cA.symm eA.symm).trans
    ((GlobalTheory.SelmerFlat.sT_map_eq D _ s _ O₁ _ f hf gA iA χ).trans
      ((GlobalTheory.SelmerFlat.sT_map_eq D _ s _ O₁ _ f hf gB iB χ).symm.trans
        (sT_congr D _ s _ (iB.comp hf) _ cB eB)))

end GlobalTheory.SelmerSameChar
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SameCharEqOne

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.PtCore

namespace GlobalTheory.PtSel

theorem sameChar_eq_one {O₀ O₁ O₂ Γ : Type} [CommRing O₀] [CommRing O₁] [CommRing O₂] [Group Γ]
    {f₁ : O₀ →+* O₁} {f₂ : O₀ →+* O₂} {ψ₁ : Γ →* O₁ˣ} {ψ₂ : Γ →* O₂ˣ}
    (h : GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.SameChar f₁ f₂ ψ₁ ψ₂) (g : Γ) (hg : ψ₁ g = 1) : ψ₂ g = 1 := by
  have h1 := h (Finsupp.single g 1 + Finsupp.single 1 (-1))
  rw [Finsupp.sum_add_index' (by simp) (by intros; simp [add_mul]),
    Finsupp.sum_add_index' (by simp) (by intros; simp [add_mul])] at h1
  simp only [Finsupp.sum_single_index, map_zero, zero_mul, map_one, one_mul, map_neg, hg, Units.val_one,
    mul_one, add_neg_cancel, true_iff] at h1
  ext
  rw [Units.val_one]
  exact add_neg_eq_zero.1 h1

theorem sel_at (hC : GlobalTheory.TwSys.Cheb) (D : D7) (hT : TriplesGood D) (hG : GoodPtRow D) (hR : ResAbsIrr D)
    (a : D.nd.Loc) (ρ : D.nd.X a → (Formalism.MainNotions.N.GE D.nd →* GL (Fin D.R.r) (D.nd.O a))) (π : D.nd.X a)
    (hπ : π ∈ D.nd.Zgood a) (hρ : GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.IsRhoPt D a π (ρ π))
    (j : D.ntw.Tw) (hj : D.ntw.twOf a = j) (k : ℕ) (ψ : Formalism.MainNotions.N.GE D.nd →* (D.ntw.Ok j k)ˣ)
    (f : D.ntw.O0 j →+* D.nd.O a) (hf : HEq f (D.ntw.twist₂ a))
    (hS : GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.SameChar f (BlochKatoReduction.Gen.phiK D.ntw j k) (D.ntw.psiL a) ψ) :
    ∃ s : D.ntw.Sig j, BlochKatoReduction.Gen.goodS (BlochKatoReduction.bk0 D) j s ∧ D.ntw.side _ s = D.ntw.twSide a ∧
      (BlochKatoReduction.Gen.sLen (BlochKatoReduction.bk0 D) j s k (D.nd.Q a) ψ ≠ ⊤ → Br.sFin D.loc D.nbr a ρ π) ∧
      ENNReal.ofReal (Br.sPi D.loc D.nbr a ρ π : ℝ) ≤ BlochKatoReduction.Gen.sLen (BlochKatoReduction.bk0 D) j s k (D.nd.Q a) ψ ∧
      AttachedIn D a π j s := by
  subst hj
  obtain rfl := eq_of_heq hf
  obtain ⟨σ, Sg, hrow, hW, hX⟩ := hG a π hπ
  obtain ⟨s, htr, hgood⟩ := hT a σ Sg hrow hW
  obtain ⟨U, hU⟩ := GlobalTheory.PtCore.twistedRho_conj_latTpsi hC D a π ρ s Sg hρ hX htr (hR a π hπ _ hρ)
  have e1 := GlobalTheory.ConjLatticeSelmer.sPiTop_eq_sTLoc D a π ρ s U hU
  have e2 := GlobalTheory.SelmerSameChar.sTLoc_eq D a s k ψ hS
  have hψ : ∀ v ∈ placesOver D.host.E (D.ntw.l (D.ntw.twOf a)),
      ∀ g ∈ Dec (F := D.host.E) (D.nd.plOm.1 v), ψ g = 1 := by
    intro v hv g hg
    rw [D.ntw.twOf_l] at hv
    exact sameChar_eq_one hS g (D.ntw.psiL_l a v hv _ (D.nd.plOm.2 v) g hg)
  obtain ⟨h1, h2⟩ := GlobalTheory.SelTwistLe.sT_le_sLen D _ s k (D.nd.Q a) ψ hψ
  rw [← e2, ← e1] at h1 h2
  refine ⟨s, hgood, htr.2.1, ?_, ?_, ⟨rfl, σ, Sg, hrow, hW, hX, htr⟩⟩
  · intro hne
    have h3 := h1 hne
    unfold Br.sFin
    rw [lt_top_iff_ne_top]
    intro h4
    exact h3 (by simp only [GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.sPiTop, GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.nlen, h4, if_true])
  · by_cases h4 : Module.length (D.nd.O a) ↥(Br.selPi D.loc D.nbr a ρ π) = ⊤
    · have h5 : BlochKatoReduction.Gen.sLen (BlochKatoReduction.bk0 D) _ s k (D.nd.Q a) ψ = ⊤ := by
        by_contra hne
        exact h1 hne (by simp only [GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.sPiTop, GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.nlen, h4, if_true])
      rw [h5]
      exact le_top
    · exact h2 _ (by simp only [GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.sPiTop, GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.nlen, h4, if_false, Br.sPi])

theorem selCore : GlobalTheory.TwSys.Cheb → ∀ (D : D7) (C : NChoice D), NChTie D C → TriplesGood D → GoodPtRow D →
    ResAbsIrr D → SameTwist D C →
    ∀ ρ : ∀ i : D.nd.Loc, D.nd.X i → (Formalism.MainNotions.N.GE D.nd →* GL (Fin D.R.r) (D.nd.O i)),
      (∀ i, ∀ π ∈ D.nd.Zgood i, GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.IsRhoPt D i π (ρ i π)) → SelCore D C ρ := by
  intro hC D C hTie hT hG hR hS ρ hρ i π hπ
  obtain ⟨f, hf, hs⟩ := hS.exists_heq i
  obtain ⟨s, h1, h2, h3⟩ := sel_at hC D hT hG hR i (ρ i) π hπ (hρ i π hπ) _ (hTie.twOf_eq i) _ _ f hf hs
  rw [hTie.Q_eq i] at h3
  exact ⟨s, h1, h2.trans (hTie.twSide_eq i), h3⟩

end GlobalTheory.PtSel

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PsiAtPsiAt

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

namespace GlobalTheory.JointSix

theorem psiAt_psiW {D : D7} (C : NChoice D) (w : D.what₂.places.Pl) :
    BlochKatoReduction.Gen.psiAt (C.sd w) (KillingConditions.psiW C w) = GlobalTheory.PtCore.psiG D C w := by
  unfold KillingConditions.psiW GlobalTheory.PtCore.psiG
  cases h : C.sd w
  · ext g
    simp [BlochKatoReduction.Gen.psiAt]
  · simp [BlochKatoReduction.Gen.psiAt]

theorem main : GlobalTheory.TwSys.Cheb → ∀ (D : D7) (C : NChoice D)
    (r : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))),
    GlobalTheory.PtCore.PtFam D r ρ → NChTie D C → GlobalTheory.PtCore.TriplesGood D → GlobalTheory.PtCore.SameTwist D C →
    GlobalTheory.PtCore.GoodPtRow D → GlobalTheory.PtCore.ResAbsIrr D → KillingConditions.SignatureChoiceCondition ρ C := by
  intro hC D C r ρ hF hT hTr hS hG hR i _
  have hsel := GlobalTheory.PtSel.selCore hC D C hT hTr hG hR hS ρ
    (fun i π hπ => hF.pt i π (Formalism.L2.zgoodSub D i hπ))
  refine ⟨fun π hπ => ?_, ?_⟩
  · obtain ⟨s, h1, h2, h3, h4, -⟩ := hsel i π hπ
    refine ⟨s, h1, ?_⟩
    rw [h2, psiAt_psiW]
    exact ⟨h3, h4⟩
  · rw [Rat.cast_sum, ← hT.Q_eq i]
    exact Finset.sum_le_sum fun v hv => GlobalTheory.T.conductorRoot_sub_one_length_le_tameValue D C hT i v hv

end GlobalTheory.JointSix

end
end
end
