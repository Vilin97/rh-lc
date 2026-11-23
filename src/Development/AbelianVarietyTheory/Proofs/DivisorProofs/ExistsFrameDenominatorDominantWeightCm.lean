module

public import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.BarCompSubsetClosure
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClearDenominatorsFramePolynomialAtPrime
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AbelianVarietyTheory.Definitions.Divisors.CommGroupMulMulEqMulInvMulMulMul
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
import Development.AbelianVarietyTheory.Definitions.Divisors.LinearIndependentBasisCoords
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnitaryWeightExponentVectorSignatureWeightMuZero
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsCmPointLocalModelOverDvrStatement
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsCompleteDVRCompletionIntegralIffStatement
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsIntegralEigenbasisOfFrameAtLocalModelStatement
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUnitIntegralGeneratorPrincipalLocalModelStatement
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieLetterIntegralInIntegralEigenbasisStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmPointEigenbasisChangeDetIntegralAlmostAllPrimeStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramePolynomialCoeffBoundedByDeterminantsStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFramedPointBaseChangeAlgebraMap
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniqueFrameChangeByMatrices
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDetNeZeroEvalFrNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightedSectionExponentShift
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameChangeExistsUniqueOfSamePoint
import Mathlib.Tactic.Basify
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LevelCarrying
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCoprimeOfNatCast
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRightActFunPull
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Development.AbelianVarietyTheory.Definitions.Divisors.Multiplier

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClearDenominatorsFramePolynomialAtPrimeStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

open GlobalTheory.LamT (CMPt)

theorem _root_.GlobalTheory.T.exists_clear_denominators_framePolynomial_at_prime : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (z : CMPt Xo c) (f : ℕ) (La : ℝ), z.Good f La →
    ∀ (e : Formalism.L2.Pj.Ix Dw → ℤ) (k : (E →+* ℂ) → ℕ), e none = 0 → ∀ p : IsDedekindDomain.HeightOneSpectrum (𝓞 z.K),
    ∃ x : 𝓞 z.K, x ≠ 0 ∧ ∀ F ∈ GlobalTheory.AllWt.secZ Xo c e, (∀ v, ∀ w ∈ valSet Xo c (algCls Xo c) v, 0 ≤ w F) →
      ∀ G : MvPolynomial (Formalism.L2.LamCM.FrVar Dw.mult) z.K, (∀ (y' : FrPt Xo c z.K) (Y : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) z.K) (s : z.Kˣ),
          (∀ b, (Y b).det ≠ 0) → GlobalTheory.Frames.FrChg (fun b => (Y b).transpose) (s : z.K) z.y y' →
          (∏ b, (Y b).det ^ k b) * evR Xo c F y' = Formalism.L2.LamCM.evalFr G Y) →
        ∀ μ, p.valuation z.K ((x : z.K) * AddMonoidAlgebra.coeff G μ) ≤ 1 := by
  first | exact @GlobalTheory.CoeffDenom.exists_clear_coeff_at_prime | exact GlobalTheory.CoeffDenom.exists_clear_coeff_at_prime | (intros; apply GlobalTheory.CoeffDenom.exists_clear_coeff_at_prime <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramePolynomialCoeffIntegralAlmostAllPrimes

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

open GlobalTheory.LamT (CMPt)
open GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.CoeffInt

theorem coeff_valuation_le_one_almost_all : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (z : CMPt Xo c) (f : ℕ) (La : ℝ), z.Good f La →
    ∀ (e : Formalism.L2.Pj.Ix Dw → ℤ) (k : (E →+* ℂ) → ℕ), e none = 0 →
    ∃ S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 z.K)), ∀ p ∉ S,
      ∀ F ∈ GlobalTheory.AllWt.secZ Xo c e, (∀ v, ∀ w ∈ valSet Xo c (algCls Xo c) v, 0 ≤ w F) →
      ∀ G : MvPolynomial (Formalism.L2.LamCM.FrVar Dw.mult) z.K, (∀ (y' : FrPt Xo c z.K) (Y : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) z.K) (s : z.Kˣ),
          (∀ b, (Y b).det ≠ 0) → GlobalTheory.Frames.FrChg (fun b => (Y b).transpose) (s : z.K) z.y y' →
          (∏ b, (Y b).det ^ k b) * evR Xo c F y' = Formalism.L2.LamCM.evalFr G Y) →
        ∀ μ, p.valuation z.K (AddMonoidAlgebra.coeff G μ) ≤ 1 := by
  intro E _ _ _ H Dw l Xo c _ z f La hz e k he
  classical
  obtain ⟨S₁, hS₁⟩ := GlobalTheory.T.cmPoint_eigenbasis_change_det_integral_almost_all_primes E H Dw l Xo c z f La hz
  have hfin : (⋃ j, {p : IsDedekindDomain.HeightOneSpectrum (𝓞 z.K) |
      FractionalIdeal.count z.K p (z.ℓ j).I ≠ 0}).Finite :=
    Set.finite_iUnion fun j => Filter.eventually_cofinite.1 (FractionalIdeal.finite_factors (z.ℓ j).I)
  refine ⟨S₁ ∪ hfin.toFinset, fun p hp F hF hv G hG μ => ?_⟩
  simp only [Finset.mem_union, not_or, Set.Finite.mem_toFinset, Set.mem_iUnion, Set.mem_setOf_eq, not_exists,
    not_not] at hp
  obtain ⟨hp1, hp2⟩ := hp
  have hgen : ∀ j, Formalism.L2.LamCM.IsLocGen p (1 : z.K) (z.ℓ j).I := fun j =>
    ⟨one_ne_zero, by rw [FractionalIdeal.spanSingleton_one, FractionalIdeal.count_one, hp2 j]⟩
  obtain ⟨T, iK, hT, hiK⟩ := GlobalTheory.T.exists_completeDVR_completion_integral_iff z.K p
  obtain ⟨M⟩ := (GlobalTheory.T.exists_cmPoint_localModel_over_dvr E H Dw l Xo c z T iK).1 fun a => (hiK _).2 (p.valuation_le_one a)
  let io : c.F →+* T.Fr := iK.comp (algebraMap c.F z.K)
  letI := io.toAlgebra
  let φ : z.K →ₐ[c.F] T.Fr := { iK with commutes' := fun _ => rfl }
  obtain ⟨yT, hyT⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c _ _ φ z.y
  have hyx : yT.x = spMap iK ≫ z.x := by rw [hyT.1, hz.2.2.2.1]
  obtain ⟨g, hg, hgL⟩ := (GlobalTheory.T.exists_integralEigenbasis_of_frame_at_localModel E H Dw l Xo c T io M.G.t M.t'.t _ M.m1 M.m2 yT hyx).1
  obtain ⟨s, hsS⟩ := GlobalTheory.T.exists_unit_integral_generator_principal_local_model E H Dw l Xo c T io M.G M.t'.t _ M.m1 M.m2 yT hyx
  obtain ⟨y', hy', -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c T.Fr yT g s hg
  have hL := hgL _ _ hy'
  have hS := hsS _ _ hy'
  have hinv : ∀ b j i, (g b)⁻¹ j i ∈ Set.range (algebraMap T.V T.Fr) := fun b j i => by
    have := GlobalTheory.T.lieLetter_integral_in_integral_eigenbasis E H Dw l Xo c z f La hz p T iK M hiK φ yT y' g s rfl hyT hy' hg hL b j i 1 (hgen _)
    rwa [map_one, _root_.one_mul] at this
  have hR : ∀ x : T.Fr, x ∈ Set.range (algebraMap T.V T.Fr) ↔ x ∈ (algebraMap T.V T.Fr).range :=
    fun x => (RingHom.mem_range).symm
  have hdetinv : ∀ b, ((g b).det)⁻¹ ∈ (algebraMap T.V T.Fr).range := fun b => by
    choose N hN using hinv b
    have e1 : (g b)⁻¹ = (Matrix.of N).map (algebraMap T.V T.Fr) := by
      ext j i; exact (hN j i).symm
    have e2 : ((g b).det)⁻¹ = ((g b)⁻¹).det := by
      rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
    rw [e2, e1]
    exact ⟨(Matrix.of N).det, by rw [RingHom.map_det]; rfl⟩
  have hall := (hR _).1 (hS₁ p hp1 T iK hT hiK M φ yT y' g s rfl hyT hy' hg hL)
  have hdet : ∀ b, (g b).det ∈ (algebraMap T.V T.Fr).range := fun b => by
    have hne : (∏ b' ∈ Finset.univ.erase b, (g b').det) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun b' _ => (hg b').ne_zero
    have e3 : (g b).det = (∏ b', (g b').det) * ∏ b' ∈ Finset.univ.erase b, ((g b').det)⁻¹ := by
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ b), Finset.prod_inv_distrib, _root_.mul_assoc,
        mul_inv_cancel₀ hne, _root_.mul_one]
    rw [e3]
    exact Subring.mul_mem _ hall (Subring.prod_mem _ fun b' _ => hdetinv b')
  have hτ : (∏ b, (g b).det ^ k b) ∈ (algebraMap T.V T.Fr).range :=
    Subring.prod_mem _ fun b _ => Subring.pow_mem _ (hdet b) _
  obtain ⟨w, hw⟩ := GlobalTheory.T.framePolynomial_coeff_bounded_by_determinants E H Dw l Xo c z f La hz e k he p T iK hT hiK M φ yT y' g s rfl hyT hy' s.ne_zero hg hL
    hS (fun _ _ => 1) (fun b j i => by rw [_root_.one_mul]; exact hinv b j i) F hF hv G
    (fun y' Y hY hch => hG y' Y 1 hY (by rw [Units.val_one]; exact hch)) μ
  simp only [one_pow, Finset.prod_const_one, _root_.mul_one] at hw
  refine (hiK _).1 ((hR _).2 ?_)
  rw [hw]
  exact Subring.mul_mem _ hτ (RingHom.mem_range_self _ _)

end GlobalTheory.CoeffInt
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramePolynomialCoeffIntegralAlmostAllPrimesStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

open GlobalTheory.LamT (CMPt)

theorem _root_.GlobalTheory.T.framePolynomial_coeff_integral_almost_all_primes : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (z : CMPt Xo c) (f : ℕ) (La : ℝ), z.Good f La →
    ∀ (e : Formalism.L2.Pj.Ix Dw → ℤ) (k : (E →+* ℂ) → ℕ), e none = 0 →
    ∃ S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 z.K)), ∀ p ∉ S,
      ∀ F ∈ GlobalTheory.AllWt.secZ Xo c e, (∀ v, ∀ w ∈ valSet Xo c (algCls Xo c) v, 0 ≤ w F) →
      ∀ G : MvPolynomial (Formalism.L2.LamCM.FrVar Dw.mult) z.K, (∀ (y' : FrPt Xo c z.K) (Y : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) z.K) (s : z.Kˣ),
          (∀ b, (Y b).det ≠ 0) → GlobalTheory.Frames.FrChg (fun b => (Y b).transpose) (s : z.K) z.y y' →
          (∏ b, (Y b).det ^ k b) * evR Xo c F y' = Formalism.L2.LamCM.evalFr G Y) →
        ∀ μ, p.valuation z.K (AddMonoidAlgebra.coeff G μ) ≤ 1 := by
  first | exact @GlobalTheory.CoeffInt.coeff_valuation_le_one_almost_all | exact GlobalTheory.CoeffInt.coeff_valuation_le_one_almost_all | (intros; apply GlobalTheory.CoeffInt.coeff_valuation_le_one_almost_all <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonDenomFramePolynomialsCmPoint

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

open GlobalTheory.LamT (CMPt)

namespace GlobalTheory.LatFull.CMInt

theorem exists_coeff_denom_intWt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (z : CMPt Xo c) (f : ℕ) (La : ℝ), z.Good f La →
    ∀ (e : Formalism.L2.Pj.Ix Dw → ℤ) (k : (E →+* ℂ) → ℕ), e none = 0 →
    ∃ t : 𝓞 z.K, t ≠ 0 ∧ ∀ F ∈ GlobalTheory.AllWt.secZ Xo c e, (∀ v, ∀ w ∈ valSet Xo c (algCls Xo c) v, 0 ≤ w F) →
      ∀ G : MvPolynomial (Formalism.L2.LamCM.FrVar Dw.mult) z.K,
        (∀ (y' : FrPt Xo c z.K) (Y : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) z.K) (s : z.Kˣ),
          (∀ b, (Y b).det ≠ 0) → GlobalTheory.Frames.FrChg (fun b => (Y b).transpose) (s : z.K) z.y y' →
          (∏ b, (Y b).det ^ k b) * evR Xo c F y' = Formalism.L2.LamCM.evalFr G Y) →
        ∀ μ, IsIntegral ℤ ((t : z.K) * AddMonoidAlgebra.coeff G μ) := by
  intro E _ _ _ H Dw l Xo c _ z f La hz e k he0
  classical
  obtain ⟨S, hS⟩ := GlobalTheory.T.framePolynomial_coeff_integral_almost_all_primes E H Dw l Xo c z f La hz e k he0
  choose x hx0 hx using GlobalTheory.T.exists_clear_denominators_framePolynomial_at_prime E H Dw l Xo c z f La hz e k he0
  refine ⟨∏ p ∈ S, x p, Finset.prod_ne_zero_iff.2 fun p _ => hx0 p, fun F hF hv G hG μ => ?_⟩
  have hint : ∀ r : 𝓞 z.K, ∀ p : IsDedekindDomain.HeightOneSpectrum (𝓞 z.K), p.valuation z.K (r : z.K) ≤ 1 :=
    fun r p => p.valuation_le_one r
  have hv1 : ∀ p : IsDedekindDomain.HeightOneSpectrum (𝓞 z.K),
      p.valuation z.K (((∏ q ∈ S, x q : 𝓞 z.K) : z.K) * AddMonoidAlgebra.coeff G μ) ≤ 1 := by
    intro p
    by_cases hp : p ∈ S
    · rw [← Finset.mul_prod_erase S x hp]
      have e1 : (((x p * ∏ q ∈ S.erase p, x q : 𝓞 z.K)) : z.K) * AddMonoidAlgebra.coeff G μ =
          ((∏ q ∈ S.erase p, x q : 𝓞 z.K) : z.K) * (((x p : 𝓞 z.K) : z.K) * AddMonoidAlgebra.coeff G μ) := by
        push_cast; ring
      rw [e1, map_mul]
      exact mul_le_one' (hint _ p) (hx p F hF hv G hG μ)
    · rw [map_mul]
      exact mul_le_one' (hint _ p) (hS p hp F hF hv G hG μ)
  obtain ⟨r, hr⟩ := IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one z.K _ hv1
  rw [← hr]
  exact RingOfIntegers.isIntegral_coe r

end GlobalTheory.LatFull.CMInt
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonDenomFramePolynomialsCmPointStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

open GlobalTheory.LamT (CMPt)

theorem _root_.GlobalTheory.T.exists_commonDenom_framePolynomials_cmPoint : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (z : CMPt Xo c) (f : ℕ) (La : ℝ), z.Good f La →
    ∀ (e : Formalism.L2.Pj.Ix Dw → ℤ) (k : (E →+* ℂ) → ℕ), e none = 0 →
    ∃ t : 𝓞 z.K, t ≠ 0 ∧ ∀ F ∈ GlobalTheory.AllWt.secZ Xo c e, (∀ v, ∀ w ∈ valSet Xo c (algCls Xo c) v, 0 ≤ w F) →
      ∀ G : MvPolynomial (Formalism.L2.LamCM.FrVar Dw.mult) z.K,
        (∀ (y' : FrPt Xo c z.K) (Y : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) z.K) (s : z.Kˣ),
          (∀ b, (Y b).det ≠ 0) → GlobalTheory.Frames.FrChg (fun b => (Y b).transpose) (s : z.K) z.y y' →
          (∏ b, (Y b).det ^ k b) * evR Xo c F y' = Formalism.L2.LamCM.evalFr G Y) →
        ∀ μ, IsIntegral ℤ ((t : z.K) * AddMonoidAlgebra.coeff G μ) := by
  first | exact @GlobalTheory.LatFull.CMInt.exists_coeff_denom_intWt | exact GlobalTheory.LatFull.CMInt.exists_coeff_denom_intWt | (intros; apply GlobalTheory.LatFull.CMInt.exists_coeff_denom_intWt <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrameDenominatorDominantWeightCm

section

@[expose] public section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.GeometryOfNumbersTheory TopologicalSpace Limits
open GlobalTheory.HSApp
open GlobalTheory.LamT (CMPt)

open GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic

namespace GlobalTheory.LatFull.CMInt

theorem exists_frame_denom_dominant : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (z : CMPt Xo c) (f : ℕ) (La : ℝ), z.Good f La → ∀ y : FrPt Xo c z.K, y.x = z.x → 1 ≤ (Dw).p → 1 ≤ (Dw).q → ∀ la : GlobalTheory.AllWt.Weight (Dw), (∀ τ, Antitone (la τ)) → (∀ τ, 1 ≤ gap (la τ) ((Dw).p - 1)) → ∃ N : z.K, N ≠ 0 ∧ ∀ F ∈ GlobalTheory.AllWt.secZ Xo c (GlobalTheory.AllWt.exOf Dw la 0), (∀ v, ∀ w ∈ valSet Xo c (algCls Xo c) v, 0 ≤ w F) → IsIntegral ℤ (N * evR Xo c F y) := by
  intro E _ _ _ H Dw l Xo c _ z f La hz y hy _hp _hq la _hanti _hgap
  classical
  set e : Formalism.L2.Pj.Ix Dw → ℤ := GlobalTheory.AllWt.exOf Dw la 0 with he
  have he0 : e none = 0 := by
    simp [he, GlobalTheory.AllWt.exOf, GlobalTheory.AllWt.wtOf, exZ]
  let k : (E →+* ℂ) → ℕ := fun b => ∑ i : Fin (Dw.mult b), (-(e (some ⟨b, i⟩))).toNat
  let a : ∀ b : E →+* ℂ, Fin (Dw.mult b) → ℕ := fun b i => (e (some ⟨b, i⟩) + (k b : ℤ)).toNat
  have hak : ∀ (b : E →+* ℂ) (i : Fin (Dw.mult b)), e (some ⟨b, i⟩) + (k b : ℤ) = (a b i : ℤ) := by
    intro b i
    have h1 : (-(e (some ⟨b, i⟩))).toNat ≤ k b :=
      Finset.single_le_sum (f := fun i : Fin (Dw.mult b) => (-(e (some ⟨b, i⟩))).toNat)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    simp only [a]
    omega
  obtain ⟨t, ht0, ht⟩ := GlobalTheory.T.exists_commonDenom_framePolynomials_cmPoint E H Dw l Xo c z f La hz e k he0
  obtain ⟨g, s, hg, hgs⟩ := (GlobalTheory.Frames.frChg_exists_unique E H Dw l Xo c z.K z.y y).1 (hy.trans hz.2.2.2.1.symm)
  let Y : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) z.K := fun b => (g b).transpose
  have hYd : ∀ b, (Y b).det ≠ 0 := fun b => by
    simp only [Y, Matrix.det_transpose]; exact (hg b).ne_zero
  have hgY : (fun b => (Y b).transpose) = g := funext fun b => Matrix.transpose_transpose _
  have htK : (t : z.K) ≠ 0 := fun h => ht0 (RingOfIntegers.coe_eq_zero_iff.1 h)
  obtain ⟨N₀, hN₀, hint⟩ := GlobalTheory.LatFull.CMInt.exists_denom_eval
    (fun _ : Formalism.L2.LamCM.FrVar Dw.mult →₀ ℕ => FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 z.K)) ((t : z.K)⁻¹))
    (fun v : Formalism.L2.LamCM.FrVar Dw.mult => Y v.1 v.2.2 v.2.1) (∑ b, ∑ i, a b i)
  refine ⟨N₀ * ∏ b, (Y b).det ^ k b, mul_ne_zero hN₀ (Finset.prod_ne_zero_iff.2 fun b _ => pow_ne_zero _ (hYd b)),
    fun F hF hv => ?_⟩
  obtain ⟨G, hGh, hG⟩ := GlobalTheory.FieldPolyZ.exists_isHomogeneous_secZ E H Dw l Xo c z.K z.y e k a he0 hak F hF
  have h1 := hG y Y s hYd (by rw [hgY]; exact hgs)
  have h2 : N₀ * (∏ b, (Y b).det ^ k b) * evR Xo c F y = N₀ * Formalism.L2.LamCM.evalFr G Y := by
    rw [mul_assoc, h1]
  rw [h2]
  refine hint G hGh fun μ => ?_
  rw [FractionalIdeal.mem_spanSingleton]
  refine ⟨⟨_, ht F hF hv G (fun y' Y' s' hY' h' => hG y' Y' s' hY' h') μ⟩, ?_⟩
  change (t : z.K) * AddMonoidAlgebra.coeff G μ * (t : z.K)⁻¹ = _
  field_simp

end GlobalTheory.LatFull.CMInt
end
end
