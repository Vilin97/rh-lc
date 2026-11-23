module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BcDefs
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GaloisRepOfPolarizedCuspidal
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
public import Formalism.ConjugateSelfDual.Statement
public import Mathlib.RingTheory.RamificationInertia.Inertia
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEqAlt
import Formalism.LocalRingCardinality.SpanPowerMembership.Primes
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.GaloisValuations.GlobalA
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousRestrictScalarsHomMaximalRealSubfieldStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DegreeOnePrimeCMFieldOverSplitMaxRealSubfieldStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisCharacterEqOneOfTrivialDegreeOneFrobeniusStatement
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousAdeleNorm
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeCharRestrictMaxRealValEqProdAboveStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyNatCastNotMem
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ContinuousIdeleCharLocalFactorization
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ApplyIdeleMapInfIdeleNegOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenKerOfInfConn
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AdTransfer
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AbsNormUnderEqOfInertiaDegOne

section

@[expose] public section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeightCounting GlobalTheory.Pst
  GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory

namespace GlobalTheory.NormDegOne

theorem normV_under_eq : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (w : HeightOneSpectrum (𝓞 L)), w.asIdeal.inertiaDeg ℤ = 1 → normV (w.under (𝓞 K)) = normV w := by
  intro K L _ _ _ _ _ w h
  classical
  set P := w.asIdeal with hP
  set Q := (w.under (𝓞 K)).asIdeal with hQ
  have hQP : Q = P.under (𝓞 K) := rfl
  have : P.IsPrime := w.isPrime
  have : Q.IsPrime := (w.under (𝓞 K)).isPrime
  have hlo : P.LiesOver Q := ⟨hQP⟩
  have htow := Ideal.inertiaDeg_tower (R := ℤ) Q P
  rw [h] at htow
  have hQ1 : Q.inertiaDeg ℤ = 1 := Nat.eq_one_of_mul_eq_one_right htow.symm
  have hunder : Q.under ℤ = P.under ℤ := by rw [hQP, Ideal.under_under]
  have e1 := Ideal.absNorm_pow_inertiaDeg (P.under ℤ) P
  have : Q.LiesOver (P.under ℤ) := ⟨hunder.symm⟩
  have e2 := Ideal.absNorm_pow_inertiaDeg (P.under ℤ) Q
  rw [h, pow_one] at e1
  rw [hQ1, pow_one] at e2
  change Nat.card (𝓞 K ⧸ Q) = Nat.card (𝓞 L ⧸ P)
  rw [← Ideal.absNorm_eq_natCard Q, ← Ideal.absNorm_eq_natCard P]
  rw [← e1, ← e2]

end GlobalTheory.NormDegOne
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AbsNormUnderEqOfInertiaDegOneStatement

section

@[expose] public section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeightCounting GlobalTheory.Pst
  GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory


theorem _root_.GlobalTheory.T.absNorm_under_eq_of_inertiaDeg_one : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (w : HeightOneSpectrum (𝓞 L)), w.asIdeal.inertiaDeg ℤ = 1 → normV (w.under (𝓞 K)) = normV w := by
  first | exact @GlobalTheory.NormDegOne.normV_under_eq | exact GlobalTheory.NormDegOne.normV_under_eq | (intros; apply GlobalTheory.NormDegOne.normV_under_eq <;> assumption)
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeCharLocalEqOneOfTrivialOnNormsSplit

section

@[expose] public section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeightCounting GlobalTheory.Pst
  GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory

namespace GlobalTheory.NormKill

theorem loc_eq_one_of_compNorm_eq_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (ε : Formalism.L2.Host.HChar (maximalRealSubfield E)),
    compNorm E ε = 1 → ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v →
    ∀ x, ε.loc v x = 1 := by
  intro E _ _ _ ε hε v hv x
  have h2 : Module.finrank (maximalRealSubfield E) E = 2 :=
    Algebra.IsQuadraticExtension.finrank_eq_two _ _

  have hnorm : Neutral.B1.localIdele (maximalRealSubfield E) v x ∈
      GlobalTheory.QuadSymbol.normGroup (maximalRealSubfield E) E
        (AdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E)) := by
    rw [GlobalTheory.IdeleNormChar.mem_normGroup_iff_everywhereNorm]
    refine ⟨fun w => ?_, fun w => ?_⟩
    · by_cases hw : w = v
      · subst hw
        have hx : GlobalTheory.IdeleNormChar.finComp (Neutral.B1.localIdele (maximalRealSubfield E) w x) w = x :=
          Units.ext (Neutral.B1.localIdele_snd_self _ w x)
        rw [hx]
        exact GlobalTheory.LFun.mem_normGroup_of_isSplit h2 hv x
      · have h1 : GlobalTheory.IdeleNormChar.finComp (Neutral.B1.localIdele (maximalRealSubfield E) v x) w = 1 := by
          apply Units.ext
          show (Neutral.B1.finiteSingle (maximalRealSubfield E) v (x : v.adicCompletion _)) w = 1
          exact GlobalTheory.LFun.finSingle_ne hw _
        rw [h1]
        exact one_mem _
    · have h1 : GlobalTheory.IdeleNormChar.infComp (Neutral.B1.localIdele (maximalRealSubfield E) v x) w = 1 :=
        Units.ext rfl
      rw [h1]
      exact one_mem _

  obtain ⟨z, hz⟩ := hnorm
  let y : (AdeleRing (𝓞 E) E)ˣ :=
    Units.map (GlobalTheory.UnitaryHeckeBaseChange.adeleEquiv (GlobalTheory.GalOfCusp.isCMExt_real E)).toRingHom.toMonoidHom z
  have hy : GlobalTheory.GalOfCusp.ideleNorm E y = Neutral.B1.localIdele (maximalRealSubfield E) v x := by
    apply Units.ext
    show Algebra.norm _ ((GlobalTheory.UnitaryHeckeBaseChange.adeleEquiv (GlobalTheory.GalOfCusp.isCMExt_real E)).symm
      ((GlobalTheory.UnitaryHeckeBaseChange.adeleEquiv (GlobalTheory.GalOfCusp.isCMExt_real E)) (z : _))) = _
    rw [RingEquiv.symm_apply_apply]
    exact congrArg Units.val hz
  have key : (GlobalTheory.GalOfCusp.compNorm E ε).1 y = (1 : Formalism.L2.Host.HChar E).1 y :=
    congrArg (fun χ : Formalism.L2.Host.HChar E => χ.1 y) hε
  rw [GlobalTheory.GalOfCusp.compNorm_apply, hy] at key
  exact key

end GlobalTheory.NormKill
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeCharLocalEqOneOfTrivialOnNormsSplitStatement

section

@[expose] public section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeightCounting GlobalTheory.Pst
  GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory


theorem _root_.GlobalTheory.T.heckeChar_local_eq_one_of_trivial_on_norms_split : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (ε : Formalism.L2.Host.HChar (maximalRealSubfield E)),
    compNorm E ε = 1 → ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v →
    ∀ x, ε.loc v x = 1 := by
  first | exact @GlobalTheory.NormKill.loc_eq_one_of_compNorm_eq_one | exact GlobalTheory.NormKill.loc_eq_one_of_compNorm_eq_one | (intros; apply GlobalTheory.NormKill.loc_eq_one_of_compNorm_eq_one <;> assumption)
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LadicCharacterRestrictCmFieldEqCyclotomicPow

section

@[expose] public section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeightCounting GlobalTheory.Pst
  GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory

namespace GlobalTheory.PolCharRes

theorem val_below_of_degree_one (E : Type) [Field E] [NumberField E] [IsCMField E] (ν : Formalism.L2.Host.HChar E) (s : ℝ)
    (hν : ν.IsAbsPow s) (χ : Formalism.L2.Host.HChar (maximalRealSubfield E))
    (hχ : compNorm E χ = ν * (GlobalTheory.ThetaPull.thetaChar ν)⁻¹) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, w.asIdeal.inertiaDeg ℤ = 1 → w.asIdeal.ramificationIdx ℤ = 1 →
      χ.UnrAt (w.under (𝓞 (maximalRealSubfield E))) ∧
      ((χ.val (w.under (𝓞 (maximalRealSubfield E))) : ℂˣ) : ℂ) = ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-(2 * s : ℂ)) := by
  have hr : compNorm E (GlobalTheory.PolChar.resReal ν) = ν * (GlobalTheory.ThetaPull.thetaChar ν)⁻¹ := by
    refine Subtype.ext (MonoidHom.ext fun x => ?_)
    change ν.1 (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap _ E (GlobalTheory.GalOfCusp.ideleNorm E x)) =
      ν.1 x * ((ν.1 (Units.map (GlobalTheory.UnitaryBC.conjAd E).toMonoidHom x))⁻¹)⁻¹
    rw [GlobalTheory.GalOfCusp.ideleMap_ideleNorm, map_mul, GlobalTheory.PolChar.ideleConj_eq, inv_inv]
  set ε := χ * (GlobalTheory.PolChar.resReal ν)⁻¹ with hε
  have hεc : compNorm E ε = 1 := by rw [hε, map_mul, map_inv, hχ, hr, mul_inv_cancel]
  have hχe : χ = GlobalTheory.PolChar.resReal ν * ε := by rw [hε, mul_comm χ, mul_inv_cancel_left]
  filter_upwards [(GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.tendsto_under (maximalRealSubfield E) E).eventually
    (GlobalTheory.HeckeSplit.eventually_unrAt χ.1 χ.2.1)] with w hu hf he
  obtain ⟨hsp, hcard, hw'⟩ := GlobalTheory.T.degreeOne_prime_CMField_over_split_maxRealSubfield E w hf he
  refine ⟨hu, ?_⟩
  have hεv : ε.val (w.under (𝓞 (maximalRealSubfield E))) = 1 := GlobalTheory.T.heckeChar_local_eq_one_of_trivial_on_norms_split E ε hεc _ hsp _
  rw [hχe, Formalism.L2.Host.HChar.val_mul, hεv, mul_one, GlobalTheory.T.heckeCharRestrictMaxReal_val_eq_prod_above E ν _ (fun w' h => ⟨hν.1 w', (hw' w' h).2⟩),
    Units.coe_prod, Finset.prod_congr rfl (fun w' h => by rw [hν.2.1 w', (hw' w' h).1]), Finset.prod_const, hcard,
    ← Complex.cpow_nat_mul]
  congr 1
  push_cast
  ring

theorem restrict_eq_cycBar_pow : ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (ν : Formalism.L2.Host.HChar E) (s : ℝ), ν.IsAbsPow s →
    ∀ ψ : Formalism.L2.Host.HChar (maximalRealSubfield E), compNorm E ψ = ν * (GlobalTheory.ThetaPull.thetaChar ν)⁻¹ →
    ∀ (k : ℕ) (μ : G (maximalRealSubfield E) Ω →* (Qbar l)ˣ), IsLAdicCharOf ι (ψ * quadChar E ^ k) μ →
    ∀ m : ℤ, (m : ℝ) = 2 * s → μ.comp (AlgEquiv.restrictScalarsHom (maximalRealSubfield E)) = cycBar E Ω l ^ m := by
  intro E Ω _ _ _ _ _ _ l _ ι ν s hν ψ hψ k μ hμ m hm
  obtain ⟨hμc, art, n, hart, -, hlad⟩ := hμ
  have hχ : compNorm E (ψ * quadChar E ^ k) = ν * (GlobalTheory.ThetaPull.thetaChar ν)⁻¹ := by
    rw [map_mul, map_pow, compNorm_quadChar, one_pow, mul_one, hψ]
  have hcyc : Continuous (cycBar E Ω l) :=
    (Continuous.units_map _ (show Continuous (fun x : ℤ_[l] => algebraMap ℚ_[l] (Qbar l) (x : ℚ_[l])) from
      (continuous_algebraMap ℚ_[l] (Qbar l)).comp continuous_subtype_val)).comp (ReciprocityTheory.Gal.continuous_cycZ E Ω l)
  rw [← div_eq_one]
  refine GlobalTheory.T.galoisCharacter_eq_one_of_trivial_degreeOne_frobenius E Ω l _ ((hμc.comp (GlobalTheory.T.continuous_restrictScalarsHom_maximalRealSubfield E Ω)).div' (hcyc.zpow m)) ?_
  filter_upwards [val_below_of_degree_one E ν s hν _ hχ, GlobalTheory.HeightCounting.eventually_natCast_notMem E l] with w h1 hl hf he A σ hA hσ
  obtain ⟨hu, hv⟩ := h1 hf he
  set F := maximalRealSubfield E
  have hA' : IsPlaceOver (F := F) A (w.under (𝓞 F)) := fun x => by
    rw [IsScalarTower.algebraMap_apply F E Ω]
    exact hA (algebraMap (𝓞 F) (𝓞 E) x)
  have hσ' : IsFrob (F := F) A (normV (w.under (𝓞 F))) (AlgEquiv.restrictScalarsHom F σ) := by
    rw [GlobalTheory.T.absNorm_under_eq_of_inertiaDeg_one F E w hf]
    exact ⟨hσ.1, hσ.2⟩
  have hl' : ((l : ℕ) : 𝓞 F) ∉ (w.under (𝓞 F)).asIdeal := fun h => hl (by
    have := (Ideal.mem_comap).1 h
    simpa using this)
  have e1 := hlad.frob_unr hart (Or.inl hl') hu hA' hσ'
  have e2 := ReciprocityTheory.Gal.cycZ_of_isFrob hl hA hσ
  rw [MonoidHom.div_apply, div_eq_one]
  apply Units.ext
  rw [MonoidHom.comp_apply, e1, hv]
  have hN : (Ideal.absNorm w.asIdeal : ℕ) = normV w := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl
  have hmC : (-(2 * (s : ℂ))) = (((-m : ℤ)) : ℂ) := by
    have : (2 * (s : ℂ)) = ((m : ℝ) : ℂ) := by rw [hm]; push_cast; ring
    rw [this]; push_cast; ring
  have e3 : ((cycBar E Ω l σ : (Qbar l)ˣ) : Qbar l) = (normV w : Qbar l) := by
    change algebraMap ℚ_[l] (Qbar l) (((ReciprocityTheory.Gal.cycZ E Ω l σ : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) = _
    rw [e2]; simp
  rw [hN, hmC, Complex.cpow_intCast, map_zpow₀, map_natCast, ← zpow_neg, neg_neg]
  change _ = (((cycBar E Ω l σ) ^ m : (Qbar l)ˣ) : Qbar l)
  rw [Units.val_zpow_eq_zpow_val, e3]

end GlobalTheory.PolCharRes

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LadicCharacterRestrictCmFieldEqCyclotomicPowStatement

section

@[expose] public section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeightCounting GlobalTheory.Pst
  GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory

theorem _root_.GlobalTheory.T.ladicCharacter_restrict_cmField_eq_cyclotomicPow : ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (ν : Formalism.L2.Host.HChar E) (s : ℝ), ν.IsAbsPow s →
    ∀ ψ : Formalism.L2.Host.HChar (maximalRealSubfield E), compNorm E ψ = ν * (GlobalTheory.ThetaPull.thetaChar ν)⁻¹ →
    ∀ (k : ℕ) (μ : G (maximalRealSubfield E) Ω →* (Qbar l)ˣ), IsLAdicCharOf ι (ψ * quadChar E ^ k) μ →
    ∀ m : ℤ, (m : ℝ) = 2 * s → μ.comp (AlgEquiv.restrictScalarsHom (maximalRealSubfield E)) = cycBar E Ω l ^ m := by
  first | exact @GlobalTheory.PolCharRes.restrict_eq_cycBar_pow | exact GlobalTheory.PolCharRes.restrict_eq_cycBar_pow | (intros; apply GlobalTheory.PolCharRes.restrict_eq_cycBar_pow <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.HeckeCharSignFixed

section

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published

private theorem isAlgPos_mul {F : Type} [Field F] [NumberField F] {χ χ' : HChar F} {n n' : (F →+* ℂ) → ℤ}
    (h : IsAlgPos χ n) (h' : IsAlgPos χ' n') : IsAlgPos (χ * χ') (n + n') := fun k hk => by
  have e : (χ * χ').inf k = χ.inf k * χ'.inf k := rfl
  rw [e, Units.val_mul, h k hk, h' k hk, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun φ _ => (zpow_add₀ ((map_ne_zero φ).2 k.ne_zero) _ _).symm

private theorem quadChar_order (E : Type) [Field E] [NumberField E] [IsCMField E] : (quadChar E).OrderDvd 2 := by
  refine Subtype.ext (MonoidHom.ext fun x => ?_)
  change (Units.map (Int.castRingHom ℂ).toMonoidHom (GlobalTheory.IdeleNormChar.normSign E x)) ^ 2 = 1
  rw [← map_pow, Int.units_sq, map_one]

private theorem place_eq {F : Type} [Field F] [NumberField F] (h : Function.Surjective (algebraMap ℚ F))
    (v v' : InfinitePlace F) : v = v' := by
  rw [← v.mk_embedding, ← v'.mk_embedding]
  congr 1
  ext x
  obtain ⟨q, rfl⟩ := h x
  simp

private theorem exists_sign {F : Type} [Field F] [NumberField F] (h : Function.Surjective (algebraMap ℚ F))
    (χ : HChar F) : ∃ m : ℕ, ∀ v : InfinitePlace F, χ.locInf v (-1) = (-1) ^ m := by
  obtain ⟨v₀⟩ : Nonempty (InfinitePlace F) := inferInstance
  have h2 : χ.locInf v₀ (-1) ^ 2 = 1 := by rw [← map_pow, neg_one_sq, map_one]
  have h3 : ((χ.locInf v₀ (-1) : ℂˣ) : ℂ) ^ 2 = 1 := by rw [← Units.val_pow_eq_pow_val, h2, Units.val_one]
  rcases sq_eq_one_iff.1 h3 with e | e
  · exact ⟨0, fun v => by rw [place_eq h v v₀, pow_zero]; exact Units.ext e⟩
  · exact ⟨1, fun v => by rw [place_eq h v v₀, pow_one]; exact Units.ext e⟩

theorem UpperTheory.heckeChar_sign_fixed :
    UpperTheory.V.Af.Bc.SignFix := by
  intro E Ω _ _ _ hE _ _ _ l _ ι χ μ ⟨hμc, art, a, ha, hχ, hL⟩ n
  obtain ⟨m, hm⟩ := exists_sign (surjective_algebraMap_real E hE) χ
  have ho : (quadChar E ^ (m + n)).OrderDvd 2 := by
    have := quadChar_order E
    unfold HChar.OrderDvd at this ⊢
    rw [← pow_mul, mul_comm, pow_mul, this, one_pow]
  have hη := isAlgPos_zero_of_orderDvd two_pos ho
  obtain ⟨δ, hδc, hδ⟩ := ha.exists_isLAdicOf ι hη
  have h0 : (1 : HChar E).IsAbsPow 0 := ⟨fun v x _ => rfl, fun v => by simp [HChar.val, HChar.locK, HChar.loc],
    fun k => by simp [HChar.inf]⟩
  have h1 : compNorm E 1 = 1 * (GlobalTheory.ThetaPull.thetaChar (1 : HChar E))⁻¹ := by
    rw [map_one, one_mul, eq_comm, inv_eq_one]
    exact Subtype.ext (MonoidHom.ext fun x => inv_one)
  have hres := GlobalTheory.T.ladicCharacter_restrict_cmField_eq_cyclotomicPow E Ω l ι 1 0 h0 1 h1 (m + n) δ (by rw [one_mul]; exact ⟨hδc, art, 0, ha, hη, hδ⟩) 0 (by simp)
  refine ⟨χ * quadChar E ^ (m + n), μ * δ, ⟨hμc.mul hδc, art, a + 0, ha, isAlgPos_mul hχ hη, hL.mul hδ⟩, ?_, ?_, fun v => ?_⟩
  · rw [map_mul, map_pow, compNorm_quadChar, one_pow, mul_one]
  · rw [MonoidHom.mul_comp, hres, zpow_zero, mul_one]
  · change χ.locInf v (-1) * (quadChar E ^ (m + n)).locInf v (-1) = (-1) ^ n
    rw [locInf_pow, hm, quadChar_locInf, ← pow_add, ← add_assoc, pow_add, ← two_mul, pow_mul]
    simp
end
end
