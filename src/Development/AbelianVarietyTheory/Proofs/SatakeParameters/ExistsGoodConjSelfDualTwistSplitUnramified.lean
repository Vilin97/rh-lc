module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsWeight
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SatakeParametersOfTwist
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAlgebraicHeckeCharSplitStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharUnrAtOfSphericalAndTwistSphericalStatement
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousAdeleNorm
public import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms.BaseChange
public import GroundTheory.LocalFields.ExistsUnitFiltrationUnitsLeRangeNormUnits
public import GroundTheory.GlobalFields.IdeleGroups.LocalNormGroups
public import GroundTheory.GlobalFields.NormResidueSymbol.FunctorialFinite
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Linter.Style
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsWeight
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsAlgebraicHeckeCharOfRegularAlgebraicPolarizedP
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualIsConjByOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalComponentsThetaPull
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousRetractionOntoUnitaryLocalPoints
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.QuadraticHeckeCharUnramifiedOfIsUnramifiedAt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.CsdTwist
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.HeckeCharAlgebraicOfSign
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.HeckeCharParallelWeight
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharUnrAtUnderOfCompNormUnramified

section

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published

noncomputable section
open scoped GroundTheory.Global.AdeleBaseChange GroundTheory.Global.SemiLocal
namespace GlobalTheory.NormBelow
open GlobalTheory.UnitaryHeckeBaseChange

theorem ideleNorm_eq_found (E : Type) [Field E] [NumberField E] [IsCMField E] (x : (AdeleRing (𝓞 E) E)ˣ) :
    ideleNorm E x = GroundTheory.Global.ideleNorm (maximalRealSubfield E) E x := by
  apply Units.ext
  obtain ⟨z, hz⟩ := (adeleEquiv (isCMExt_real E)).surjective (x : AdeleRing (𝓞 E) E)
  have h : adeleNorm E (adeleEquiv (isCMExt_real E) z) = Algebra.norm _ z :=
    congrArg (Algebra.norm _) ((adeleEquiv (isCMExt_real E)).symm_apply_apply z)
  have h2 : ∀ z, toAdele (maximalRealSubfield E) E z =
      GroundTheory.Global.AdeleBaseChange.adeleTensorAlgEquivLeft (maximalRealSubfield E) E z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul a l =>
      rw [toAdele_tmul, GroundTheory.Global.AdeleBaseChange.adeleTensorAlgEquivLeft_tmul]
      have hm : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap
          (maximalRealSubfield E) E = GroundTheory.Global.AdeleBaseChange.adeleMap
          (maximalRealSubfield E) E := by
        ext a : 1
        apply Prod.ext
        · funext w
          open scoped NumberField.LiesOver in
          change AbsoluteValue.Completion.map _ _ _ = algebraMap _ _ _
          rw [AbsoluteValue.Completion.algebraMap_eq_of_liesOver]
        · apply FiniteAdeleRing.ext
          intro w
          change GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteCompletionMap _ _ w _ =
            GroundTheory.Global.SemiLocal.completionMap _ w _
          rfl
      rw [hm, mul_comm]
    | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]
  change adeleNorm E (x : AdeleRing (𝓞 E) E) = _
  rw [GroundTheory.Global.coe_ideleNorm, ← hz, h]
  have h3 : adeleEquiv (isCMExt_real E) z = _ := h2 z
  rw [h3]
  exact (Algebra.norm_eq_of_algEquiv _ _).symm

theorem ideleNorm_localIdele (E : Type) [Field E] [NumberField E] [IsCMField E] (w : HeightOneSpectrum (𝓞 E))
    (y : (w.adicCompletion E)ˣ) :
    ideleNorm E (localIdele E w y) = localIdele (maximalRealSubfield E) (w.under (𝓞 (maximalRealSubfield E)))
      (GroundTheory.LocalField.normUnits _ (w.adicCompletion E) y) := by
  rw [ideleNorm_eq_found]
  exact GroundTheory.Global.ideleNorm_finiteEmbedding (K := maximalRealSubfield E) w y

end GlobalTheory.NormBelow

namespace GlobalTheory.NormBelow
open GlobalTheory.UnitaryHeckeBaseChange

theorem unrAt_under_of_compNorm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (χ : HChar (maximalRealSubfield E)) (w : HeightOneSpectrum (𝓞 E)), ¬ GlobalTheory.UnitaryBC.IsSplitAt w →
    Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal → (compNorm E χ).UnrAt w →
    χ.UnrAt (w.under (𝓞 (maximalRealSubfield E))) := by
  intro E _ _ _ χ w _ hur hχ x hx
  have he : w.asIdeal.ramificationIdx (𝓞 (maximalRealSubfield E)) = 1 :=
    Ideal.ramificationIdx_eq_one w.asIdeal (𝓞 (maximalRealSubfield E))
  haveI : w.asIdeal.LiesOver (w.under (𝓞 (maximalRealSubfield E))).asIdeal := ⟨rfl⟩
  have hxm : x ∈ (Submonoid.ofClass ((w.under (𝓞 (maximalRealSubfield E))).adicCompletionIntegers
      (maximalRealSubfield E))).units := by
    unfold IsUnitAt at hx
    refine (Submonoid.mem_units_iff _ _).2 ⟨?_, ?_⟩
    · exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 hx.le
    · refine (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 ?_
      rw [Units.val_inv_eq_inv_val, map_inv₀, hx, inv_one]
  obtain ⟨y, hy, hyn⟩ := GroundTheory.Global.IdeleNorm.exists_norm_eq_of_ramificationIdx_eq_one _ w he hxm
  have hyu : IsUnitAt w y := by
    obtain ⟨h1, h2⟩ := (Submonoid.mem_units_iff _ _).1 hy
    have h1' := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 h1
    have h2' := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 h2
    unfold IsUnitAt
    refine le_antisymm h1' ?_
    have e : Valued.v (y : w.adicCompletion E) * Valued.v ((y⁻¹ : (w.adicCompletion E)ˣ) : w.adicCompletion E) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    calc (1 : _) = _ := e.symm
      _ ≤ Valued.v (y : w.adicCompletion E) := mul_le_of_le_one_right' h2'
  have key : χ.loc (w.under (𝓞 (maximalRealSubfield E))) x = (compNorm E χ).loc w y := by
    show χ.1 (localIdele _ _ x) = χ.1 (ideleNorm E (localIdele E w y))
    rw [ideleNorm_localIdele]
    congr 2
    apply Units.ext
    rw [GroundTheory.LocalField.coe_normUnits]
    exact hyn.symm
  rw [key]
  exact hχ y hyu

end GlobalTheory.NormBelow
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharUnrAtUnderOfCompNormUnramifiedStatement

section

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published


theorem _root_.GlobalTheory.T.heckeChar_unrAt_under_of_compNorm_unramified : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (χ : HChar (maximalRealSubfield E)) (w : HeightOneSpectrum (𝓞 E)), ¬ GlobalTheory.UnitaryBC.IsSplitAt w → Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal → (compNorm E χ).UnrAt w → χ.UnrAt (w.under (𝓞 (maximalRealSubfield E))) := by
  first | exact @GlobalTheory.NormBelow.unrAt_under_of_compNorm | exact GlobalTheory.NormBelow.unrAt_under_of_compNorm | (intros; apply GlobalTheory.NormBelow.unrAt_under_of_compNorm <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSphericalTwistOfContragredientConjugate

section

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published

noncomputable section

namespace GlobalTheory.ContraPair.SphTwist

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ}

theorem conjFin_locGL_mem (w : HeightOneSpectrum (𝓞 E))
    (hw : conjSrc (IsCMField.complexConj E).toRingEquiv w = w) (k : GL (Fin a) (w.adicCompletion E))
    (hk : k ∈ GlobalTheory.LFun.KGL w (n := a)) : ∃ k' ∈ GlobalTheory.LFun.KGL w (n := a),
      Matrix.GeneralLinearGroup.map (conjFin (IsCMField.complexConj E).toRingEquiv) (locGL E a w k) = locGL E a w k' := by
  have key : ∀ u (h : conjSrc (IsCMField.complexConj E).toRingEquiv w = u) (k : GL (Fin a) (u.adicCompletion E)),
      k ∈ GlobalTheory.LFun.KGL u (n := a) → ∃ k' ∈ GlobalTheory.LFun.KGL w (n := a),
        Matrix.GeneralLinearGroup.map (conjFin (IsCMField.complexConj E).toRingEquiv) (locGL E a u k) = locGL E a w k' := by
    intro u h k hk
    subst h
    refine ⟨_, ?_, GlobalTheory.ConjPairLoc.conjFin_locGL _ w k⟩
    obtain ⟨k0, rfl⟩ := hk
    let r : Formalism.UG.Ov E (conjSrc (IsCMField.complexConj E).toRingEquiv w) →+* Formalism.UG.Ov E w :=
      (conjLoc (IsCMField.complexConj E).toRingEquiv w).restrict _ _ fun x hx => by
        change _ ∈ w.adicCompletionIntegers E
        change x ∈ (conjSrc (IsCMField.complexConj E).toRingEquiv w).adicCompletionIntegers E at hx
        rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hx ⊢
        rw [(conjLoc_spec _ w).2.2]
        exact hx
    refine ⟨Matrix.GeneralLinearGroup.map r k0, ?_⟩
    ext i j
    rfl
  exact key w hw k hk

end GlobalTheory.ContraPair.SphTwist


open GlobalTheory.ContraPair.SphTwist in
theorem GlobalTheory.ContraPair.isSpherical_twist_of_dualIsConjBy : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ), 1 ≤ a → ∀ (π : CuspSub E a) (ψ : HChar E), GlobalTheory.ContraPair.DualIsConjBy π ψ → ∀ w : HeightOneSpectrum (𝓞 E), ¬ GlobalTheory.UnitaryBC.IsSplitAt w → (∃ B, (CG.mk π).HasSat w B) → GlobalTheory.LGrp.IsSpherical ((π.twist ψ⁻¹).locRep w) (GlobalTheory.LFun.KGL w (n := a)) := by
  intro E _ _ _ a _ π ψ hP w hns hS
  obtain ⟨B0, hB0⟩ := hS
  obtain ⟨B, -, hB2, hfin, -, -⟩ := hP
  have hsat : GlobalTheory.LFun.HasSatGL w (π.locRep w) B0 := (CG.hasSat_mk π w B0).1 hB0
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 hsat.1
  obtain ⟨y, hy⟩ : ∃ y, B y x ≠ 0 := by
    by_contra h
    push_neg at h
    exact hx0 (hB2 x h)
  have hw : conjSrc (IsCMField.complexConj E).toRingEquiv w = w := by
    by_contra h
    exact hns ⟨_, h, GlobalTheory.DefU.LocRet.under_conjSrc w⟩
  have hL : ∀ k ∈ GlobalTheory.LFun.KGL w (n := a), B.flip x ((π.twist ψ⁻¹).locRep w k y) = B.flip x y := by
    intro k hk
    obtain ⟨k', hk', e⟩ := GlobalTheory.ContraPair.SphTwist.conjFin_locGL_mem w hw k hk
    have hx' : π.op (.fin (locGL E a w k')) x = x := GlobalTheory.LGrp.mem_fixed.1 hx k' hk'
    have h1 := hfin (locGL E a w k) y x
    change B ((π.twist ψ⁻¹).op (.fin (locGL E a w k)) y) x = B y x
    conv_lhs => rw [← hx']
    rw [← e]
    exact h1
  obtain ⟨v, hv, hve⟩ := GlobalTheory.SmGL.IwahoriOnto.exists_fixed_map_eq ((π.twist ψ⁻¹).isSmooth_locRep w)
    (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a).2 (B.flip x) y hL
  refine (Submodule.ne_bot_iff _).2 ⟨v, hv, fun h => hy ?_⟩
  have : B.flip x v = B y x := hve
  rw [← this, h, map_zero]
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSphericalTwistOfContragredientConjugateStatement

section

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published


theorem _root_.GlobalTheory.T.isSpherical_twist_of_contragredient_conjugate : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ), 1 ≤ a → ∀ (π : CuspSub E a) (ψ : HChar E), GlobalTheory.ContraPair.DualIsConjBy π ψ → ∀ w : HeightOneSpectrum (𝓞 E), ¬ GlobalTheory.UnitaryBC.IsSplitAt w → (∃ B, (CG.mk π).HasSat w B) → GlobalTheory.LGrp.IsSpherical ((π.twist ψ⁻¹).locRep w) (GlobalTheory.LFun.KGL w (n := a)) := by
  first | exact @GlobalTheory.ContraPair.isSpherical_twist_of_dualIsConjBy | exact GlobalTheory.ContraPair.isSpherical_twist_of_dualIsConjBy | (intros; apply GlobalTheory.ContraPair.isSpherical_twist_of_dualIsConjBy <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.QuadraticHeckeCharUnramifiedOfIsUnramifiedAtStatement

section

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published


theorem _root_.GlobalTheory.T.quadraticHeckeChar_unramified_of_isUnramifiedAt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : HeightOneSpectrum (𝓞 E)), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal → (quadChar E).UnrAt (w.under (𝓞 (maximalRealSubfield E))) := by
  first | exact @GlobalTheory.QuadCharUnr.quadChar_unrAt_of_isUnramifiedAt | exact GlobalTheory.QuadCharUnr.quadChar_unrAt_of_isUnramifiedAt | (intros; apply GlobalTheory.QuadCharUnr.quadChar_unrAt_of_isUnramifiedAt <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsGoodConjSelfDualTwistSplitUnramified

section

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published

noncomputable section
namespace GlobalTheory.GoodCsdTwist

open GlobalTheory.ContraPair

theorem unrAt_mul {K : Type} [Field K] [NumberField K] {χ χ' : HChar K} {v : HeightOneSpectrum (𝓞 K)}
    (h : χ.UnrAt v) (h' : χ'.UnrAt v) : (χ * χ').UnrAt v := fun x hx => by
  change χ.loc v x * χ'.loc v x = 1
  rw [h x hx, h' x hx, mul_one]

theorem unrAt_inv {K : Type} [Field K] [NumberField K] {χ : HChar K} {v : HeightOneSpectrum (𝓞 K)}
    (h : χ.UnrAt v) : (χ⁻¹).UnrAt v := fun x hx => by
  change (χ.loc v x)⁻¹ = 1
  rw [h x hx, inv_one]

theorem unrAt_pow {K : Type} [Field K] [NumberField K] {χ : HChar K} {v : HeightOneSpectrum (𝓞 K)}
    (h : χ.UnrAt v) : ∀ k : ℕ, (χ ^ k).UnrAt v
  | 0 => fun _ _ => rfl
  | k + 1 => by rw [pow_succ]; exact unrAt_mul (unrAt_pow h k) h

theorem isAlgPos_mul {F : Type} [Field F] [NumberField F] {χ χ' : HChar F} {n n' : (F →+* ℂ) → ℤ}
    (h : IsAlgPos χ n) (h' : IsAlgPos χ' n') : IsAlgPos (χ * χ') (n + n') := fun k hk => by
  have e : (χ * χ').inf k = χ.inf k * χ'.inf k := rfl
  rw [e, Units.val_mul, h k hk, h' k hk, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun φ _ => (zpow_add₀ ((map_ne_zero φ).2 k.ne_zero) _ _).symm

theorem regAlg_twist {K : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] {n : ℕ} {P : CuspSub K n}
    (h : (CG.mk P).IsRegAlg) {κ : HChar K} {m : (K →+* ℂ) → ℤ} (hκ : κ.IsAlg m) : (CG.mk (P.twist κ)).IsRegAlg := (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => by
  have e := ((ParLaws.hasInfChar_infChar (CG.mk P) τ).twist κ).infChar_eq
  rw [CG.twist_mk] at e
  rw [e, (InfType.expo_of_infType K κ).1 m hκ τ]
  refine ⟨(h τ).1.map (add_left_injective _), fun z hz => ?_⟩
  obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hz
  obtain ⟨k, rfl⟩ := (h τ).2 y hy
  exact ⟨k + m τ, by push_cast; ring⟩

theorem neg_one_zpow_natAbs (z : ℤ) : ((-1 : ℂˣ) ^ z.natAbs) = (-1 : ℂˣ) ^ (-z) := by
  rcases Int.even_or_odd z with h | h
  · rw [h.neg.neg_one_zpow, (Int.natAbs_even.2 h).neg_one_pow]
  · rw [h.neg.neg_one_zpow, (Int.natAbs_odd.2 h).neg_one_pow]

theorem exists_goodCsd_twist : AutomorphicFormsFiniteGL → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l a : ℕ), 1 ≤ a →
    ∀ (π : CuspSub E a) (χ : HChar (maximalRealSubfield E)), InScope .good l π χ → ∀ w₀ : HeightOneSpectrum (𝓞 E),
    GlobalTheory.UnitaryBC.IsSplitAt w₀ → ∃ (κ : HChar E) (m : (E →+* ℂ) → ℤ), κ.IsAlg m ∧ κ.UnrAt w₀ ∧
    InScope .csd l (π.twist κ) (quadChar E ^ a) := by
  intro _ E _ _ _ l a ha π χ ⟨hreg, hpol, hgood⟩ w₀ hw₀
  obtain ⟨n, hn⟩ := GlobalTheory.RegAlgCharAlg.isAlgPos_of_polarizedPair E a ha π χ hreg hpol
  obtain ⟨φ₀⟩ : Nonempty (maximalRealSubfield E →+* ℂ) := inferInstance
  have hb : IsAlgPos χ (fun _ => n φ₀) := by
    rw [show (fun _ => n φ₀) = n from funext fun φ => UpperTheory.heckeChar_parallel_weight _ χ n hn φ₀ φ]
    exact hn
  have hinv : IsAlgPos χ⁻¹ (fun _ => -n φ₀) := fun k hk => by
    rw [HChar.inf_inv, Units.val_inv_eq_inv_val, hb k hk, ← Finset.prod_inv_distrib]
    exact Finset.prod_congr rfl fun φ _ => (zpow_neg _ _).symm
  have ho : (quadChar E ^ (a + (n φ₀).natAbs)).OrderDvd 2 := by
    unfold HChar.OrderDvd
    rw [← pow_mul, mul_comm, pow_mul]
    have : (quadChar E) ^ 2 = 1 := by
      refine Subtype.ext (MonoidHom.ext fun x => ?_)
      change (Units.map (Int.castRingHom ℂ).toMonoidHom (GlobalTheory.IdeleNormChar.normSign E x)) ^ 2 = 1
      rw [← map_pow, Int.units_sq, map_one]
    rw [this, one_pow]
  have hpos := isAlgPos_mul hinv (isAlgPos_zero_of_orderDvd two_pos ho)
  rw [add_zero] at hpos
  have hsign : ∀ v, (χ⁻¹ * quadChar E ^ (a + (n φ₀).natAbs)).locInf v (-1) = (-1) ^ (-n φ₀) := fun v => by
    change (χ.locInf v (-1))⁻¹ * ((quadChar E ^ (a + (n φ₀).natAbs)).locInf v (-1)) = _
    rw [locInf_pow, quadChar_locInf]
    rw [hpol.sign v, pow_add, inv_mul_cancel_left, neg_one_zpow_natAbs]
  have halg := UpperTheory.heckeChar_algebraic_of_sign _ _ (-n φ₀) hpos hsign
  have hunr : ∀ w : HeightOneSpectrum (𝓞 E), ¬ GlobalTheory.UnitaryBC.IsSplitAt w →
      Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal ∧
      (χ⁻¹ * quadChar E ^ (a + (n φ₀).natAbs)).UnrAt (w.under (𝓞 (maximalRealSubfield E))) := fun w hw => by
    obtain ⟨-, hu, hsat⟩ := hgood.2.2 w hw
    have h1 := GlobalTheory.T.heckeChar_unrAt_of_spherical_and_twist_spherical E a ha π _ w hsat (GlobalTheory.T.isSpherical_twist_of_contragredient_conjugate E a ha π _ hpol.dual w hw hsat)
    replace h1 := unrAt_inv h1
    rw [inv_inv] at h1
    exact ⟨hu, unrAt_mul (unrAt_inv (GlobalTheory.T.heckeChar_unrAt_under_of_compNorm_unramified E χ w hw hu h1)) (unrAt_pow (GlobalTheory.T.quadraticHeckeChar_unramified_of_isUnramifiedAt E w hu) _)⟩
  obtain ⟨κ, m, hκ, hres, hκ0, hκu⟩ := GlobalTheory.T.exists_algebraic_hecke_char_split E _ (-n φ₀) halg hunr w₀ hw₀
  refine ⟨κ, m, hκ, hκ0, regAlg_twist hreg hκ, ⟨fun v => ?_, ?_⟩, ⟨hgood.1, hgood.2.1, fun w hw => ?_⟩, rfl⟩
  · rw [locInf_pow, quadChar_locInf]
  · rw [map_pow, compNorm_quadChar, one_pow, dualIsConjBy_one]
    exact UpperTheory.V.Af.Cq.csdTwist E a π _ κ hpol.dual
      (by rw [hres, map_mul, map_inv, map_pow, compNorm_quadChar, one_pow, mul_one])
  · obtain ⟨h1, h2, B, hB⟩ := hgood.2.2 w hw
    refine ⟨h1, h2, B.map (· * κ.val w), ?_⟩
    rw [CG.hasSat_mk] at hB ⊢
    exact GlobalTheory.SphGal.hasSatGL_twist E a π κ w B (hκu w hw) hB

end GlobalTheory.GoodCsdTwist
end
end
end
