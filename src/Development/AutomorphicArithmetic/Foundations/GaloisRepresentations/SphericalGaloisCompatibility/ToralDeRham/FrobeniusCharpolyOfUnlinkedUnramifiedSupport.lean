module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalGaloisCompatibility.Chl
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIsPlaceOverFiniteExtensionOfIsPlaceOverStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSmoothCharCompNormU
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalArtinExistsHolds
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsWeilGroupRestrictExtension
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalArtinCompNormCompat
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
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CyclicStrongAtCusp
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsWeight
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RestrictsSelf
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFormsFiniteGL
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DistribHaarCharNorm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIsWeight
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SatWDCharPolChars
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupercuspidalSupportTwistNuCharacters
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CyclicStrongAtCusp
import GroundTheory.LocalFields.LocalFourierHaar
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Linter.Style
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalGaloisCompatibility.ToralDeRham.LocalComponentsOfSmoothCharacters
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalGaloisCompatibility.ToralDeRham.NormEqOneOfIsUnitarisable
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalGaloisCompatibility.ToralDeRham.WeaklyAttachedToralOfCmLift
import GroundTheory.LocalFields.PadicLogSeries

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnramifiedCompNormOfKilledInertiaFixing

section

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RoadU

theorem unram_comp_normU_of_fix : ∀ (Ω : Type) [Field Ω] (E : Type) [Field E] [NumberField E] [Algebra E Ω] [IsAlgClosure E Ω] (M : Type) [Field M] [NumberField M] [Algebra M Ω] [IsAlgClosure M Ω] [Algebra E M] [IsScalarTower E M Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (u : HeightOneSpectrum (𝓞 M)) (h : IsPlaceOver A w) (h' : IsPlaceOver A u) [u.asIdeal.LiesOver w.asIdeal] (n : ℕ) (ξ : Fin n → ((w.adicCompletion E)ˣ →* ℂˣ)) (a : Weil h →* (w.adicCompletion E)ˣ), IsLocalArtin h a → (∀ t : Weil h, deg t = 0 → (∀ x : M, (t : G E Ω) (algebraMap M Ω x) = algebraMap M Ω x) → ∀ j, ξ j (a t) = 1) → ∀ j (x : (u.adicCompletion M)ˣ), Valued.v (x : u.adicCompletion M) = 1 → ξ j (GlobalTheory.BCChar.normU w u x) = 1 := by
  intro Ω _ E _ _ _ _ M _ _ _ _ _ _ A w u h h' _ n ξ a ha H j x hx
  obtain ⟨a', ha'⟩ := GlobalTheory.localArtinExists_holds M Ω A u h'
  have h1 : ValuativeRel.valuation (u.adicCompletion M) (x : u.adicCompletion M) = 1 := by
    have : (Valued.v : Valuation (u.adicCompletion M) (WithZero (Multiplicative ℤ))).Compatible :=
      Valuation.Compatible.ofValuation _
    exact (ValuativeRel.isEquiv (ValuativeRel.valuation (u.adicCompletion M))
      (Valued.v : Valuation (u.adicCompletion M) (WithZero (Multiplicative ℤ)))).eq_one_iff_eq_one.2 hx
  obtain ⟨τ, rfl⟩ := ha'.surj x
  have hdeg : deg τ = 0 := by
    have := ha'.ord_eq τ
    rw [GlobalTheory.SmGL.ord_eq_zero_iff.2 h1] at this
    omega
  obtain ⟨t, ht, hd⟩ := GlobalTheory.AboveL.exists_weil_restrict E M Ω A w u h h' τ
  rw [← GlobalTheory.ArtinNormU.localArtin_normU E M Ω A w u h h' a a' ha ha' t τ ht]
  exact H t (hd.2 hdeg) (fun y => by rw [ht]; exact AlgEquiv.commutes _ y) j

end GlobalTheory.RoadU
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnramifiedCompNormOfKilledInertiaFixingStatement

section

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.unramified_comp_norm_of_killed_inertia_fixing : ∀ (Ω : Type) [Field Ω] (E : Type) [Field E] [NumberField E] [Algebra E Ω] [IsAlgClosure E Ω] (M : Type) [Field M] [NumberField M] [Algebra M Ω] [IsAlgClosure M Ω] [Algebra E M] [IsScalarTower E M Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (u : HeightOneSpectrum (𝓞 M)) (h : IsPlaceOver A w) (h' : IsPlaceOver A u) [u.asIdeal.LiesOver w.asIdeal] (n : ℕ) (ξ : Fin n → ((w.adicCompletion E)ˣ →* ℂˣ)) (a : Weil h →* (w.adicCompletion E)ˣ), IsLocalArtin h a → (∀ t : Weil h, deg t = 0 → (∀ x : M, (t : G E Ω) (algebraMap M Ω x) = algebraMap M Ω x) → ∀ j, ξ j (a t) = 1) → ∀ j (x : (u.adicCompletion M)ˣ), Valued.v (x : u.adicCompletion M) = 1 → ξ j (GlobalTheory.BCChar.normU w u x) = 1 := by
  first | (exact @GlobalTheory.RoadU.unram_comp_normU_of_fix) | (exact GlobalTheory.RoadU.unram_comp_normU_of_fix) | (intros; apply GlobalTheory.RoadU.unram_comp_normU_of_fix  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnlinkedCharsCompNormU

section

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RoadU

theorem unlinked_chars_comp_normU : ∀ (E M : Type) [Field E] [NumberField E] [Field M] [NumberField M] [Algebra E M] (w : HeightOneSpectrum (𝓞 E)) (u : HeightOneSpectrum (𝓞 M)) [u.asIdeal.LiesOver w.asIdeal] (n : ℕ) (c : ℝ), ∀ (ξ : Fin n → ((w.adicCompletion E)ˣ →* ℂˣ)) (hξ : ∀ j, IsSmoothChar (ξ j)), (∀ j, ∃ e : ℝ, |e| < 1 / 2 ∧ ∀ x, ‖((ξ j x : ℂˣ) : ℂ)‖ = ‖((absPow (w.adicCompletion E) ((e - c : ℝ) : ℂ) x : ℂˣ) : ℂ)‖) → Unlinked (chars (fun j => (ξ j).comp (GlobalTheory.BCChar.normU w u)) fun j => GlobalTheory.BCChar.isSmoothChar_comp_normU w u (hξ j)) := by
  intro E M _ _ _ _ _ w u _ n c ξ hξ he
  letI : Algebra (w.adicCompletion E) (u.adicCompletion M) := (GroundTheory.Global.adicCompletionMap w u).toAlgebra
  have hf := GroundTheory.Global.continuous_adicCompletionMap w u
  haveI : ContinuousSMul (w.adicCompletion E) (u.adicCompletion M) := _root_.continuousSMul_of_algebraMap _ _ hf
  haveI : IsScalarTower E (w.adicCompletion E) (u.adicCompletion M) :=
    .of_algebraMap_eq fun x => by
      show _ = GroundTheory.Global.adicCompletionMap w u _
      rw [GroundTheory.Global.adicCompletionMap_algebraMap, IsScalarTower.algebraMap_apply E M (u.adicCompletion M)]
  haveI : FiniteDimensional (w.adicCompletion E) (u.adicCompletion M) := GroundTheory.Global.finite_adicCompletion w u
  haveI : IsModuleTopology (w.adicCompletion E) (u.adicCompletion M) := by
    letI : NontriviallyNormedField (w.adicCompletion E) := Valued.toNontriviallyNormedField _ _
    exact isModuleTopologyOfFiniteDimensional
  have hN : ∀ t : ℂ, (absPow (w.adicCompletion E) t).comp (GlobalTheory.BCChar.normU w u) = absPow (u.adicCompletion M) t :=
    fun t => GlobalTheory.LBCNu.absPow_comp_norm t
  have hval : ∀ (s : ℝ) (x : (u.adicCompletion M)ˣ), ‖((absPow (u.adicCompletion M) (s : ℂ) x : ℂˣ) : ℂ)‖ =
      nabs (u.adicCompletion M) x ^ s := fun s x => by
    rw [val_absPow_ofReal, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (nabs_pos' _ x).le _)]
  have key : ∀ j, ∃ e : ℝ, |e| < 1 / 2 ∧ ∀ x, ‖(((ξ j).comp (GlobalTheory.BCChar.normU w u) x : ℂˣ) : ℂ)‖ =
      nabs (u.adicCompletion M) x ^ (e - c) := by
    intro j
    obtain ⟨e, he1, he2⟩ := he j
    refine ⟨e, he1, fun x => ?_⟩
    rw [MonoidHom.comp_apply, he2, ← MonoidHom.comp_apply, hN, hval]
  intro y hy z hz hyz
  simp only [chars, Multiset.mem_map, Finset.mem_val, Finset.mem_univ, true_and] at hy hz
  obtain ⟨i, rfl⟩ := hy
  obtain ⟨j, rfl⟩ := hz
  rw [IrrGL.nu, IrrGL.tw_ofChar, IrrGL.ofChar_inj] at hyz
  obtain ⟨a, ha, ha'⟩ := key i
  obtain ⟨b, hb, hb'⟩ := key j
  have h1 : absPow (u.adicCompletion M) ((a - b - 1 : ℝ) : ℂ) = 1 := by
    ext x
    have hx := congrArg (fun χ : (u.adicCompletion M)ˣ →* ℂˣ => ‖((χ x : ℂˣ) : ℂ)‖) hyz
    simp only [MonoidHom.mul_apply, Units.val_mul, norm_mul] at hx
    have h1' : ‖((absPow (u.adicCompletion M) 1 x : ℂˣ) : ℂ)‖ = nabs (u.adicCompletion M) x ^ (1 : ℝ) := by
      rw [← hval]; simp
    rw [ha', hb', h1'] at hx
    have ht := nabs_pos' (u.adicCompletion M) x
    rw [val_absPow_ofReal, MonoidHom.one_apply, Units.val_one]
    have : nabs (u.adicCompletion M) x ^ (a - b - 1) = 1 := by
      rw [show a - b - 1 = (a - c) - ((b - c) + 1) by ring, Real.rpow_sub ht, Real.rpow_add ht, hx,
        div_self (by positivity)]
    rw [this, Complex.ofReal_one]
  have h2 := (absPow_ofReal_eq_one (k := u.adicCompletion M)).1 h1
  rw [abs_lt] at ha hb
  linarith [ha.1, ha.2, hb.1, hb.2]

end GlobalTheory.RoadU
end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalGaloisCompatibility.ToralDeRham.FrobeniusCharpolyEqSatakeOfPlaceAbove

section

@[expose] public section

open GlobalTheory.RoadU

namespace GalTw
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RoadU.TorLift

theorem hasSat_charPol_above : UpperTheory.Gal.ToralGalois.Inq → ∀ (Ω : Type) [Field Ω] (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra E Ω] [IsAlgClosure E Ω] (M : Type) [Field M] [NumberField M] [IsCMField M] [Algebra M Ω] [IsAlgClosure M Ω] [Algebra E M] [IsScalarTower E M Ω] (l : ℕ) [Fact l.Prime] (n : ℕ), 1 ≤ n → ∀ (π : CuspSub E n) (χ : HChar (maximalRealSubfield E)), InScope .all l π χ → ∀ (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (u : HeightOneSpectrum (𝓞 M)) (h : IsPlaceOver A w) (h' : IsPlaceOver A u) [u.asIdeal.LiesOver w.asIdeal], ∀ σ : SmIrr (GL (Fin n) (w.adicCompletion E)), π.IsLocComp w σ → ∀ (ξ : Fin n → ((w.adicCompletion E)ˣ →* ℂˣ)) (hξ : ∀ j, IsSmoothChar (ξ j)), HasSupport (algNorm σ).rep (chars ξ hξ) → Unlinked (chars ξ hξ) → ∀ a : Weil h →* (w.adicCompletion E)ˣ, IsLocalArtin h a → ∀ P : CuspSub M n, CharLift π P → (∀ j (x : (u.adicCompletion M)ˣ), Valued.v (x : u.adicCompletion M) = 1 → (ξ j * absPow (w.adicCompletion E) (-((((1 : ℝ) - n) / 2 : ℝ) : ℂ))) (GlobalTheory.BCChar.normU w u x) = 1) → ∃ B : Multiset ℂˣ, (CG.mk P).HasSat u B ∧ ∀ (g₀ : Weil h) (g' : Weil h'), (∀ z : Ω, (g₀ : G E Ω) z = (g' : G M Ω) z) → (satWD h' n B).charPol g' = ∏ j, (X - C ((ξ j (a g₀) : ℂˣ) : ℂ)) := by
  intro hI Ω _ E _ _ _ _ _ M _ _ _ _ _ _ _ l _ n hn π χ hsc A w u h h' _ σ hσ ξ hξ hsup hun a ha P hcl hunr
  classical
  haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  set s₀ : ℂ := ((((1 : ℝ) - n) / 2 : ℝ) : ℂ) with hs₀
  let ξ0 : Fin n → ((w.adicCompletion E)ˣ →* ℂˣ) := fun j => ξ j * absPow (w.adicCompletion E) (-s₀)
  have hξ0 : ∀ j, IsSmoothChar (ξ0 j) := fun j => (hξ j).mul (isSmoothChar_absPow _)
  have hback : ∀ j, ξ j = ξ0 j * absPow (w.adicCompletion E) s₀ := fun j => by
    simp only [ξ0, mul_assoc, ← absPow_add, neg_add_cancel, absPow_zero, mul_one]

  have hN : ∀ t : ℂ, (absPow (w.adicCompletion E) t).comp (GlobalTheory.BCChar.normU w u) = absPow (u.adicCompletion M) t := by
    letI : Algebra (w.adicCompletion E) (u.adicCompletion M) := (GroundTheory.Global.adicCompletionMap w u).toAlgebra
    have hf := GroundTheory.Global.continuous_adicCompletionMap w u
    haveI : ContinuousSMul (w.adicCompletion E) (u.adicCompletion M) := continuousSMul_of_algebraMap _ _ hf
    haveI : IsScalarTower E (w.adicCompletion E) (u.adicCompletion M) :=
      .of_algebraMap_eq fun x => by
        show _ = GroundTheory.Global.adicCompletionMap w u _
        rw [GroundTheory.Global.adicCompletionMap_algebraMap, IsScalarTower.algebraMap_apply E M (u.adicCompletion M)]
    haveI : FiniteDimensional (w.adicCompletion E) (u.adicCompletion M) := GroundTheory.Global.finite_adicCompletion w u
    haveI : IsModuleTopology (w.adicCompletion E) (u.adicCompletion M) := by
      letI : NontriviallyNormedField (w.adicCompletion E) := Valued.toNontriviallyNormedField _ _
      exact isModuleTopologyOfFiniteDimensional
    exact fun t => GlobalTheory.LBCNu.absPow_comp_norm t

  have hx := (GlobalTheory.RoadU.TwistSupp.supp_nu_chars (w.adicCompletion E) (IrrGL.of σ.ρ σ.smooth σ.irred) n ξ0 ξ hξ0 hξ s₀
    hback).1
  have hsupσ : HasSupport σ.ρ (chars ξ0 hξ0) :=
    (hx.2 hsup).of_equiv (IrrGL.equivOf σ.ρ σ.smooth σ.irred).symm

  obtain ⟨T, hT, -⟩ := LocEx.exists_isLocComp GlobalTheory.automorphicFormsFiniteGL M n P u
  have hsupT := hcl.2 w u σ T hσ hT ξ0 hξ0 hsupσ

  obtain ⟨wt, hwt⟩ := GlobalTheory.PolarizedWeight.exists_isWeight E l n hn π χ hsc
  have hwin := GlobalTheory.RoadU.window hI E l n hn π χ hsc wt hwt w σ hσ ξ hξ hsup hun
  have hunlN := GlobalTheory.RoadU.unlinked_chars_comp_normU E M w u n ((wt : ℝ) / 2) ξ hξ hwin
  have hunl0 : Unlinked (chars (fun j => (ξ0 j).comp (GlobalTheory.BCChar.normU w u))
      fun j => GlobalTheory.BCChar.isSmoothChar_comp_normU w u (hξ0 j)) := by
    rw [GlobalTheory.RoadU.TwistSupp.chars_eq_map_nu (fun j => (ξ j).comp (GlobalTheory.BCChar.normU w u))
      (fun j => (ξ0 j).comp (GlobalTheory.BCChar.normU w u)) (fun j => GlobalTheory.BCChar.isSmoothChar_comp_normU w u (hξ j))
      (fun j => GlobalTheory.BCChar.isSmoothChar_comp_normU w u (hξ0 j)) (-s₀) (fun j => by
        rw [← hN (-s₀)]
        ext x
        rfl), GlobalTheory.RoadU.TwistSupp.unlinked_map_nu]
    exact hunlN

  obtain ⟨ϖ0, hϖ0⟩ := u.valuation_exists_uniformizer M
  have hv : Valued.v ((ϖ0 : M) : u.adicCompletion M) = WithZero.exp (-1 : ℤ) := by
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hϖ0]
  have hne : ((ϖ0 : M) : u.adicCompletion M) ≠ 0 := (Valuation.ne_zero_iff _).1 (by rw [hv]; exact WithZero.exp_ne_zero)
  let ϖ' : (u.adicCompletion M)ˣ := Units.mk0 _ hne
  have hϖ' : Valued.v (ϖ' : u.adicCompletion M) = WithZero.exp (-1 : ℤ) := hv
  have hunrN : ∀ j (x : (u.adicCompletion M)ˣ), Valued.v (x : u.adicCompletion M) = 1 →
      (ξ0 j).comp (GlobalTheory.BCChar.normU w u) x = 1 := hunr
  have hsat := GlobalTheory.SphUnr.hasSat_of_unlinked_unr hI M n hn P u T hT (fun j => (ξ0 j).comp (GlobalTheory.BCChar.normU w u))
    (fun j => GlobalTheory.BCChar.isSmoothChar_comp_normU w u (hξ0 j)) hsupT hunl0 hunrN ϖ' hϖ'
  refine ⟨_, hsat, ?_⟩

  obtain ⟨a', ha'⟩ := GlobalTheory.localArtinExists_holds M Ω A u h'
  intro g₀ g' hgg
  rw [GlobalTheory.SatChar.satWD_charPol_chars Ω M u A h' n (fun j => (ξ0 j).comp (GlobalTheory.BCChar.normU w u))
    (fun j => (ξ0 j).comp (GlobalTheory.BCChar.normU w u) * absPow (u.adicCompletion M) s₀) (fun j => rfl) hunrN ϖ' hϖ' a' ha' g']
  have hart := GlobalTheory.ArtinNormU.localArtin_normU E M Ω A w u h h' a a' ha ha' g₀ g' hgg
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [hart, hback j, ← hN s₀]
  rfl

end GlobalTheory.RoadU.TorLift

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem GlobalTheory.T.frobenius_charpoly_eq_satake_of_place_above : UpperTheory.Gal.ToralGalois.Inq → ∀ (Ω : Type) [Field Ω] (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra E Ω] [IsAlgClosure E Ω] (M : Type) [Field M] [NumberField M] [IsCMField M] [Algebra M Ω] [IsAlgClosure M Ω] [Algebra E M] [IsScalarTower E M Ω] (l : ℕ) [Fact l.Prime] (n : ℕ), 1 ≤ n → ∀ (π : CuspSub E n) (χ : HChar (maximalRealSubfield E)), InScope .all l π χ → ∀ (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (u : HeightOneSpectrum (𝓞 M)) (h : IsPlaceOver A w) (h' : IsPlaceOver A u) [u.asIdeal.LiesOver w.asIdeal], ∀ σ : SmIrr (GL (Fin n) (w.adicCompletion E)), π.IsLocComp w σ → ∀ (ξ : Fin n → ((w.adicCompletion E)ˣ →* ℂˣ)) (hξ : ∀ j, IsSmoothChar (ξ j)), HasSupport (algNorm σ).rep (chars ξ hξ) → Unlinked (chars ξ hξ) → ∀ a : Weil h →* (w.adicCompletion E)ˣ, IsLocalArtin h a → ∀ P : CuspSub M n, CharLift π P → (∀ j (x : (u.adicCompletion M)ˣ), Valued.v (x : u.adicCompletion M) = 1 → (ξ j * absPow (w.adicCompletion E) (-((((1 : ℝ) - n) / 2 : ℝ) : ℂ))) (GlobalTheory.BCChar.normU w u x) = 1) → ∃ B : Multiset ℂˣ, (CG.mk P).HasSat u B ∧ ∀ (g₀ : Weil h) (g' : Weil h'), (∀ z : Ω, (g₀ : G E Ω) z = (g' : G M Ω) z) → (satWD h' n B).charPol g' = ∏ j, (X - C ((ξ j (a g₀) : ℂˣ) : ℂ)) := by
  first | (exact @GlobalTheory.RoadU.TorLift.hasSat_charPol_above) | (exact GlobalTheory.RoadU.TorLift.hasSat_charPol_above) | (intros; apply GlobalTheory.RoadU.TorLift.hasSat_charPol_above  <;> assumption)

end
end
end GalTw
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalGaloisCompatibility.ToralDeRham.FrobeniusCharpolyOfUnlinkedUnramifiedSupport

section

@[expose] public section

open GlobalTheory.RoadU

namespace GalTw
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RoadU

theorem liesOver_of_isPlaceOver {E M Ω : Type} [Field E] [NumberField E] [Field M] [NumberField M] [Field Ω]
    [Algebra E Ω] [Algebra M Ω] [Algebra E M] [IsScalarTower E M Ω] {A : ValuationSubring Ω}
    {w : HeightOneSpectrum (𝓞 E)} {u : HeightOneSpectrum (𝓞 M)} (h : IsPlaceOver A w) (h' : IsPlaceOver A u) :
    u.asIdeal.LiesOver w.asIdeal := by
  refine ⟨Ideal.ext fun x => ?_⟩
  rw [Ideal.under, Ideal.mem_comap, ← h x, ← h' _]
  have : algebraMap M Ω ((algebraMap (𝓞 E) (𝓞 M) x : 𝓞 M) : M) = algebraMap E Ω (x : E) := by
    rw [IsScalarTower.algebraMap_apply E M Ω]
    rfl
  rw [this]

theorem exists_sph_lift_of_toral : UpperTheory.Gal.ToralGalois.Inq → ∀ (Ω : Type) [Field Ω] (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ), 1 ≤ n → ∀ (π : CuspSub E n) (χ : HChar (maximalRealSubfield E)), InScope .all l π χ → ∀ r : G E Ω →* GL (Fin n) (Qbar l), Weak π ι r → ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : IsPlaceOver A w), ∀ σ : SmIrr (GL (Fin n) (w.adicCompletion E)), π.IsLocComp w σ → ∀ (ξ : Fin n → ((w.adicCompletion E)ˣ →* ℂˣ)) (hξ : ∀ j, IsSmoothChar (ξ j)), HasSupport (algNorm σ).rep (chars ξ hξ) → Unlinked (chars ξ hξ) → ∀ a : Weil h →* (w.adicCompletion E)ˣ, IsLocalArtin h a → ∀ g : Weil h, deg g ≠ 0 → ∃ (M : Type) (_ : Field M) (_ : NumberField M) (_ : IsCMField M) (_ : Algebra M Ω) (_ : IsAlgClosure M Ω) (_ : Algebra E M) (_ : IsScalarTower E M Ω) (u : HeightOneSpectrum (𝓞 M)) (h' : IsPlaceOver A u) (P : CuspSub M n) (χ' : HChar (maximalRealSubfield M)), InScope .all l P χ' ∧ IsLift π P ∧ (∀ x : M, (g : G E Ω) (algebraMap M Ω x) = algebraMap M Ω x) ∧ ∃ B : Multiset ℂˣ, (CG.mk P).HasSat u B ∧ ∀ (g₀ : Weil h) (g' : Weil h'), (∀ z : Ω, (g₀ : G E Ω) z = (g' : G M Ω) z) → (satWD h' n B).charPol g' = ∏ j, (X - C ((ξ j (a g₀) : ℂˣ) : ℂ)) := by
  intro hI Ω _ E _ _ _ _ _ l _ ι n hn π χ hπ r hr w A h σ hσ ξ hξ hsupp hunl a ha g hg
  let ξ₀ : Fin n → ((w.adicCompletion E)ˣ →* ℂˣ) := fun j =>
    ξ j * absPow (w.adicCompletion E) (-((((1 : ℝ) - n) / 2 : ℝ) : ℂ))
  have hξ₀ : ∀ j, IsSmoothChar (ξ₀ j) := fun j => (hξ j).mul (isSmoothChar_absPow _)
  obtain ⟨M, _, _, _, _, _, _, _, P, χ', hP, hcl, hfix, hkill⟩ :=
    GlobalTheory.T.weaklyAttached_toral_of_cm_lift hI Ω E l ι n hn π χ hπ r hr w A h ξ₀ hξ₀ a ha g hg
  obtain ⟨u, h', -⟩ := GlobalTheory.T.exists_isPlaceOver_finiteExtension_of_isPlaceOver E M Ω A w h
  haveI := liesOver_of_isPlaceOver (M := M) h h'
  have hunr := GlobalTheory.T.unramified_comp_norm_of_killed_inertia_fixing Ω E M A w u h h' n ξ₀ a ha hkill
  obtain ⟨B, hB, hch⟩ :=
    GlobalTheory.T.frobenius_charpoly_eq_satake_of_place_above hI Ω E M l n hn π χ hπ A w u h h' σ hσ ξ hξ hsupp hunl a ha P hcl hunr
  exact ⟨M, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    u, h', P, χ', hP, hcl.1, hfix, B, hB, hch⟩

end GlobalTheory.RoadU

end

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem GlobalTheory.T.frobenius_charpoly_of_unlinked_unramified_support : UpperTheory.Gal.ToralGalois.Inq → ∀ (Ω : Type) [Field Ω] (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ), 1 ≤ n → ∀ (π : CuspSub E n) (χ : HChar (maximalRealSubfield E)), InScope .all l π χ → ∀ r : G E Ω →* GL (Fin n) (Qbar l), Weak π ι r → ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : IsPlaceOver A w), ∀ σ : SmIrr (GL (Fin n) (w.adicCompletion E)), π.IsLocComp w σ → ∀ (ξ : Fin n → ((w.adicCompletion E)ˣ →* ℂˣ)) (hξ : ∀ j, IsSmoothChar (ξ j)), HasSupport (algNorm σ).rep (chars ξ hξ) → Unlinked (chars ξ hξ) → ∀ a : Weil h →* (w.adicCompletion E)ˣ, IsLocalArtin h a → ∀ g : Weil h, deg g ≠ 0 → ∃ (M : Type) (_ : Field M) (_ : NumberField M) (_ : IsCMField M) (_ : Algebra M Ω) (_ : IsAlgClosure M Ω) (_ : Algebra E M) (_ : IsScalarTower E M Ω) (u : HeightOneSpectrum (𝓞 M)) (h' : IsPlaceOver A u) (P : CuspSub M n) (χ' : HChar (maximalRealSubfield M)), InScope .all l P χ' ∧ IsLift π P ∧ (∀ x : M, (g : G E Ω) (algebraMap M Ω x) = algebraMap M Ω x) ∧ ∃ B : Multiset ℂˣ, (CG.mk P).HasSat u B ∧ ∀ (g₀ : Weil h) (g' : Weil h'), (∀ z : Ω, (g₀ : G E Ω) z = (g' : G M Ω) z) → (satWD h' n B).charPol g' = ∏ j, (X - C ((ξ j (a g₀) : ℂˣ) : ℂ)) := by
  first | (exact @GlobalTheory.RoadU.exists_sph_lift_of_toral) | (exact GlobalTheory.RoadU.exists_sph_lift_of_toral) | (intros; apply GlobalTheory.RoadU.exists_sph_lift_of_toral  <;> assumption)

end
end GalTw
end
end
