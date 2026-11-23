module

public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ModelsAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsotropicCoefficientSplitting
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GenericPointMemModuliOfMeetsAbelianLocus
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcDatumSectionValueCoeffEqFourierJacobi
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsAnalyticModelOnFrameOrbitIsolatingStatement
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsCmArcDataDescentNumberFieldStatement
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsCmLatticeDataAbelianPartSplitPointStatement
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsCmObjBaseChange
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPointOfIsPeriod
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PointEqIffIsometryClosed
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TensorObjectAndCurveExistsIff
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FamilyUnifExpUnique
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.PrimAn
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.NonemptyGtAnOfToric
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsComplexArcDatumCmFibre
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsNormAnOnOrbit
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsScaled
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicArcAgreesAnalyticDictionaryStatement
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PointExpEqOfIsometry
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RelabelEmbeddingsGoodBijectiveConjCompat
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsTauCanonicalTrivialisationIffNormalisedArc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsotropicIndexSums
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ExistsChartComplexPoint

-- Source module: Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsCmObjOfPeriod

section

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

noncomputable section

namespace GlobalTheory.ArcCM.PeriodObj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {D D' : Datum H}
  {g : ℕ} {ty : Fin g → (E →+* ℂ)} {P : D.La →+ (Fin g → ℂ)} {P' : D'.La →+ (Fin g → ℂ)}

theorem mem_lat_iff (hP : IsPeriod D ty P) (ρ : ℂ) (a : D.La) :
    a ∈ PureType.lat hP ρ ↔ P (H.rt • a) = ρ • P a := by
  refine ⟨fun h => funext fun j => ?_, fun h j hj => ?_⟩
  · rw [hP.1, Pi.smul_apply, smul_eq_mul]
    by_cases hj : ty j (H.rt : E) = ρ
    · rw [hj]
    · rw [h j hj, mul_zero, mul_zero]
  · have := congrFun h j
    rw [hP.1, Pi.smul_apply, smul_eq_mul] at this
    exact (mul_eq_mul_right_iff.1 this).resolve_left hj

theorem exists_lat_move (hP : IsPeriod D ty P) (hP' : IsPeriod D' ty P') (gam : D.La ≃ₗ[𝓞 E] D'.La)
    (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (hE : ∀ a b, D'.EF (gam a) (gam b) = D.EF a b)
    (hh : ∀ a, P' (gam a) = h (P a)) {p q : ℕ} (Z : GlobalTheory.CM.CMLat hP p q) :
    ∃ Z' : GlobalTheory.CM.CMLat hP' p q, Z'.hh = Z.hh :=
  ⟨{ D₁ := Z.D₁
     sigP := Z.sigP
     sigM := Z.sigM
     f := fun j => gam.toLinearMap ∘ₗ Z.f j
     pure := fun j a => by
       refine (mem_lat_iff hP' _ _).2 ?_
       show P' (H.rt • gam (Z.f j a)) = _ • P' (gam (Z.f j a))
       rw [← map_smul, hh, hh, (mem_lat_iff hP _ _).1 (Z.pure j a), map_smul]
     hh := Z.hh
     form := fun j a b => (hE _ _).trans (Z.form j a b)
     span := by
       obtain ⟨n, hn, hs⟩ := Z.span
       refine ⟨n, hn, fun a => ?_⟩
       obtain ⟨x, hx⟩ := hs (gam.symm a)
       refine ⟨x, ?_⟩
       have := congrArg gam hx

       rw [map_nsmul, gam.apply_symm_apply, map_sum] at this
       exact this }, rfl⟩

theorem isExp_move {R : Type} [CommRing R] {T : GlobalTheory.CM.PAT H (Sp R)} {σ : R →+* ℂ} (hP : IsPeriod D ty P)
    (gam : D.La ≃ₗ[𝓞 E] D'.La) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (hE : ∀ a b, D'.EF (gam a) (gam b) = D.EF a b)
    (hh : ∀ a, P' (gam a) = h (P a)) {e : (Fin g → ℂ) → (Over.mk (spMap σ) ⟶ T.t.G)}
    (he : GlobalTheory.CM.IsExp T σ D' ty P' e) : GlobalTheory.CM.IsExp T σ D ty P fun z => e (h z) := by
  obtain ⟨hP', hol, add, onto, ker, lin, weil⟩ := he
  have hd : Differentiable ℂ h := h.toContinuousLinearEquiv.differentiable
  refine ⟨hP, fun U f => ⟨?_, ?_⟩, fun z w => ?_, onto.comp h.surjective, fun z => ?_, fun a z => ?_,
    fun k a b c hk hc => ?_⟩
  · exact (hol U f).1.preimage hd.continuous
  · exact (hol U f).2.comp hd.differentiableOn fun z hz => hz
  · beta_reduce
    rw [map_add (f := _), add]
  · refine (ker _).trans ⟨?_, ?_⟩
    · rintro ⟨a, ha⟩
      exact ⟨gam.symm a, h.injective (by rw [← hh, gam.apply_symm_apply, ha])⟩
    · rintro ⟨a, rfl⟩
      exact ⟨gam a, hh a⟩
  · let m : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) :=
      LinearMap.pi fun k => (LinearMap.mulLeft ℝ (ty k (a : E))).comp (LinearMap.proj k)
    have hm : ∀ z, m z = fun k => ty k (a : E) * z k := fun _ => rfl
    have hc : h.toLinearMap.restrictScalars ℝ ∘ₗ m = m ∘ₗ h.toLinearMap.restrictScalars ℝ :=
      LinearMap.ext_on_range hP.2.2.2.1 fun x => by
        show h (m (P x)) = m (h (P x))
        rw [← hh, hm, hm, ← funext (hP.1 a x), ← funext (hP'.1 a (gam x)), ← hh, map_smul]
    have hz : h (m z) = m (h z) := LinearMap.congr_fun hc z
    show e (h (m z)) = _
    rw [hz, hm, lin]
  · beta_reduce
    rw [map_smul, map_smul, ← hh, ← hh]
    exact weil k _ _ c hk (by rw [hE]; exact hc)

end GlobalTheory.ArcCM.PeriodObj

namespace GlobalTheory.ArcCM

theorem exists_cmObj_of_period : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H) (c : Coeff l) (DB : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (PB : DB.La →+ (Fin g → ℂ)) (hP : IsPeriod DB ty PB) (Z : GlobalTheory.CM.CMLat hP DB.p DB.q), 1 ≤ DB.p + DB.q → IsTypeFn H DB.p DB.q ty → l.A = 1 → ∃ (K : Type) (_ : Field K) (_ : NumberField K) (_ : Algebra c.F K) (σ₁ : K →+* ℂ) (ρ : 𝓞 K) (X : GlobalTheory.CM.CMObj H K ρ σ₁ DB.p DB.q) (ex : (Fin g → ℂ) → (Over.mk (spMap (σ₁.comp (algebraMap (𝓞 K) K))) ⟶ X.B.t.G)), σ₁.comp (algebraMap c.F K) = c.F.val.toRingHom ∧ σ₁ (ρ : K) = H.rt0 ∧ X.hh = Z.hh ∧ GlobalTheory.CM.IsExp X.B (σ₁.comp (algebraMap (𝓞 K) K)) DB ty PB ex := by
  intro kn E _ _ _ H l c DB g ty PB hP Z hpq hty hA
  obtain ⟨Xo⟩ := kn.n1ab E H DB l hpq
  obtain ⟨FU⟩ := kn.n1c E H DB l Xo (algebraMap (KA l) ℂ) g ty hpq rfl hty
  have hζ : algebraMap (KA l) ℂ (baseKA l).ζ =
      Complex.exp (-(2 * Real.pi * Complex.I) * (((1 : ℤ) : ℂ)) / l.A) := by
    show zeta l.A = _
    rw [hA, zeta]
    simp [Complex.exp_neg]
  obtain ⟨y, e, he⟩ := GlobalTheory.Moduli.exists_point_of_isPeriod kn.theta kn.laws E H DB l Xo (algebraMap (KA l) ℂ) g ty hpq
    rfl hty DB LinearMap.id PB ⟨rfl, rfl, fun _ => LinearMap.id, fun _ => 1, fun n m _ _ a => ⟨0, by simp⟩,
      fun n _ => ⟨fun a => Iff.rfl, fun a => ⟨a, 0, by simp⟩⟩, fun n _ a a' => by simp, hζ, rfl⟩ hP
  obtain ⟨i, P', hP', hy⟩ := FU.onto y he.1
  obtain ⟨gam, h, hE, -, -, hh⟩ := (GlobalTheory.UnifPoint.point_eq_iff_isometry_closed kn.theta kn.laws E H DB l Xo
    (algebraMap (KA l) ℂ) g ty hpq rfl hty DB (FU.Di i) LinearMap.id (FU.t i) PB P' y (FU.u i P') e (FU.ex i P') he
    ⟨FU.over_σ i P' hP', hP', ⟨FU.ex_add i P' hP', FU.ex_onto i P' hP', ExpUniqFamily.isHolTo_ex FU i P' hP',
      (FU.ex_diff i P' hP').1, (FU.ex_diff i P' hP').2⟩, FU.ex_ker i P' hP', FU.ex_lin i P' hP', FU.ex_weil i P' hP',
      FU.ex_eta i P' hP', FU.ex_etaA i P' hP'⟩).1 hy.symm
  obtain ⟨Z', hZ'⟩ := PeriodObj.exists_lat_move hP hP' gam h hE hh Z
  obtain ⟨K, _, hk, ρ, X, y₀, t₀, m, m', gA, tyA, PA, eA, F, hle, hρ, hX, -, hy₀, -⟩ :=
    kn.cm E H DB l Xo g ty FU i P' hP' Z' c.F c.fin
  obtain ⟨eB, heB, -⟩ := GlobalTheory.CM.ExCompare.exists_isExp_of_family FU i hP' (algebraMap (𝓞 K) K) (algebraMap K ℂ)
    X.B m m' hy₀
  exact ⟨K, inferInstance, inferInstance, (IntermediateField.inclusion hle).toRingHom.toAlgebra, algebraMap K ℂ, ρ, X,
    fun z => eB (h z), RingHom.ext fun _ => rfl, hρ, hX.trans hZ', PeriodObj.isExp_move hP gam h hE hh heB⟩

end GlobalTheory.ArcCM
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsComplexArcDatumCmFibreStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

theorem _root_.GlobalTheory.T.exists_complexArcDatum_cmFibre : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (Uw : UnfWit U) (k : U.Comp) (ξ' : Fin r → E) (x : Frame (U.X k).Ψ r) (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (B : GlobalTheory.CM.PAT H (Sp R)) (σR : R →+* ℂ), GoodEmb c σ → IsUnf U → l.A = 1 → letI := H.starRing; ∀ (A : AnArc (𝓞 E)) (gam : (Uw.F.Di (Uw.ik k)).La ≃ₗ[𝓞 E] A.La) (ξ : Module.Dual ℤ A.X) (DB : Datum H) (tyB : Fin A.gB → (E →+* ℂ)) (eB : DB.La ≃+ A.abelian₂) (ex : (Fin A.gB → ℂ) → (Over.mk (spMap σR) ⟶ B.t.G)), OnOrbit Uw k ξ' x A gam ξ → Module.finrank (𝓞 E) A.X = 1 → (∀ y y', (2 * l.M' : ℤ) ∣ A.be y y') → PrimAn H A → AbDat H A DB tyB eB → DB.p = Dw.p - 1 → DB.q = Dw.q - 1 → 1 ≤ Dw.p → 1 ≤ Dw.q → GlobalTheory.CM.IsExp B σR DB tyB (A.abelian₂.subtype.toAddMonoidHom.comp eB.toAddMonoidHom) ex → ∃ (aC : ArcIn Dw l (RingHom.id c.F) ℂ σ) (Λ : GtAn aC) (hA : Λ.A = A) (φ : aC.D₀.P.A.left ⟶ B.pol.A.left), IsPolFibre σR B.pol aC.D₀.P φ ∧ (∀ a, (aC.oa.onB.act a).left ≫ φ = φ ≫ (B.t.act.act a).left) ∧ ∀ v, Λ.toGtAn₀.Lifts (aC.eta v) (cast (congrArg AnArc.La hA.symm) (gam (Uw.F.t (Uw.ik k) v))) := by
  first | exact @GlobalTheory.ArcCM.CxFibre.exists_arcIn_fibre | exact GlobalTheory.ArcCM.CxFibre.exists_arcIn_fibre | (intros; apply GlobalTheory.ArcCM.CxFibre.exists_arcIn_fibre <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicArcMatchesFrameOfModelOnOrbit

section

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

namespace GlobalTheory.ArcCM

theorem tieC_of_onOrbit : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (Uw : UnfWit U) (k : U.Comp) (ξ' : Fin r → E) (x : Frame (U.X k).Ψ r) (aC : ArcIn Dw l (RingHom.id c.F) ℂ σ) (Λ : GtAn₀ aC) (ξC : Module.Dual ℤ aC.D₀.X), GoodEmb c σ → IsUnf U → (U.X k).IsIso ξ' → x ∈ (U.X k).dom → l.A = 1 → letI := H.starRing; ∀ (gam : (Uw.F.Di (Uw.ik k)).La ≃ₗ[𝓞 E] Λ.A.La) (ξ : Module.Dual ℤ Λ.A.X), OnOrbit Uw k ξ' x Λ.A gam ξ → (∀ y, ξC (Λ.eX y) = ξ y) → (∀ v, Λ.Lifts (aC.eta v) (gam (Uw.F.t (Uw.ik k) v))) → ∀ (O : Type) [CommRing O] (β : O →+* c.F), TieC Uw (aC.restrict β) ξC k ξ' x := by
  intro hK E _ _ _ H Dw l Xo c _ _ σ r U Uw k ξ' x aC Λ ξC hσ hU hξ hx hA gam ξ hO hξC hL O _ β Y χ W Ha
  let := H.starRing
  let Λ' : GtAn₀ (aC.restrict β) := ⟨Λ.toGtDict, Λ.be_eq⟩
  obtain ⟨g₁, h₁, e1, e2, e3, e4⟩ := GlobalTheory.T.holomorphicArc_agrees_analyticDictionary hK E H Dw l Xo c σ O β Y (aC.restrict β) χ W Uw.g _ Uw.F Ha Λ'
  obtain ⟨o1, ⟨t', o2, o3⟩, T₀, o4⟩ := hO
  have hw : max Ha.T T₀ < (((max Ha.T T₀ + 1 : ℝ) : ℂ) * Complex.I).im := by simp
  generalize (((max Ha.T T₀ + 1 : ℝ) : ℂ) * Complex.I) = w at hw
  obtain ⟨hw1, hw2⟩ := max_lt_iff.1 hw
  obtain ⟨s, hs, h, hh⟩ := o4 w hw2
  let gm : (Uw.F.Di Ha.i).La ≃ₗ[𝓞 E] (Uw.F.Di (Uw.ik k)).La := g₁.trans gam.symm
  let L : (Fin Uw.g → ℂ) ≃ₗ[ℂ] (Fin Uw.g → ℂ) := h₁.trans h.symm
  have hgm : ∀ u, gam (gm u) = g₁ u := fun u => gam.apply_symm_apply _
  have hEF : ∀ u v, (Uw.F.Di (Uw.ik k)).EF (gm u) (gm v) = (Uw.F.Di Ha.i).EF u v := fun u v => by
    rw [← o1, hgm, hgm]; exact e4 u v
  have hP : ∀ u, Uw.Pm k ⟨_, hs⟩ (gm u) = L (Ha.Pw w u) := fun u => by
    apply h.injective
    rw [hh, hgm]
    exact (e3 w u).symm.trans (h.apply_symm_apply _).symm
  have hpq : 1 ≤ Dw.p + Dw.q := by
    rw [← hU.1]
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · exact absurd (Subsingleton.elim _ _) hξ.2.2
    · exact hr
  have hty := (GlobalTheory.Relab.relab_good E H l c σ hσ).2.2.2 Dw Uw.g Uw.e
  have hlev : ∀ v ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La),
      ∃ e, gm (Uw.F.t Ha.i v) = Uw.F.t (Uw.ik k) v + l.M • e := by
    intro v hv
    obtain ⟨q, q1, q2, q3⟩ := Ha.levelM v hv
    have hq : q = Λ.toGtDict.qk l.M (g₁ (Uw.F.t Ha.i v)) := by
      refine TorusExt.qk_ext (q1.trans (e2 _).symm) (q2.trans ?_)
      have h0 : h₁ (Ha.P₀ (Uw.F.t Ha.i v)) = Λ.A.P0 (g₁ (Uw.F.t Ha.i v)) := by
        have := e3 0 (Uw.F.t Ha.i v)
        rw [Ha.Pw_eq, zero_smul, add_zero] at this
        exact this.trans (by rw [AnArc.Pw_apply, zero_smul, add_zero])
      rw [← e1, map_smul, h0]
      rfl
    have l1 : Λ.Lifts (aC.eta v) (g₁ (Uw.F.t Ha.i v)) := fun q' hq' => hq ▸ q3 q' hq'
    obtain ⟨la, hla⟩ := Λ.exists_lifts (aC.eta v)
    obtain ⟨m₁, hm₁⟩ := (hla _).1 l1
    obtain ⟨m₂, hm₂⟩ := (hla _).1 (hL v)
    refine ⟨gam.symm (m₁ - m₂), gam.injective ?_⟩
    rw [hgm, map_add (f := _), map_nsmul, gam.apply_symm_apply, hm₂, nsmul_sub]
    exact hm₁.trans (by abel)
  obtain ⟨p1, p2⟩ := GlobalTheory.ArcCM.point_exp_eq_of_isometry hK E H Dw l Xo _ Uw.g _ Uw.F Ha.i (Uw.ik k) (Ha.Pw w) (Uw.Pm k ⟨_, hs⟩) gm L hpq hσ hty hA
    (Ha.period w hw1) (Uw.period k _) hEF hlev hP
  refine ⟨w, s, hs, L, gm.symm t', t', hw1, fun v' => ?_, o2, ?_, p1, p2⟩
  · rw [← hEF, gm.apply_symm_apply, o3, ← hξC, hgm, ← e2]
    rfl
  · rw [← hP, gm.apply_symm_apply]

end GlobalTheory.ArcCM
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicArcMatchesFrameOfModelOnOrbitStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

theorem _root_.GlobalTheory.T.holomorphicArc_matches_frame_of_model_on_orbit : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (Uw : UnfWit U) (k : U.Comp) (ξ' : Fin r → E) (x : Frame (U.X k).Ψ r) (aC : ArcIn Dw l (RingHom.id c.F) ℂ σ) (Λ : GtAn₀ aC) (ξC : Module.Dual ℤ aC.D₀.X), GoodEmb c σ → IsUnf U → (U.X k).IsIso ξ' → x ∈ (U.X k).dom → l.A = 1 → letI := H.starRing; ∀ (gam : (Uw.F.Di (Uw.ik k)).La ≃ₗ[𝓞 E] Λ.A.La) (ξ : Module.Dual ℤ Λ.A.X), OnOrbit Uw k ξ' x Λ.A gam ξ → (∀ y, ξC (Λ.eX y) = ξ y) → (∀ v, Λ.Lifts (aC.eta v) (gam (Uw.F.t (Uw.ik k) v))) → ∀ (O : Type) [CommRing O] (β : O →+* c.F), TieC Uw (aC.restrict β) ξC k ξ' x := by
  first | exact @GlobalTheory.ArcCM.tieC_of_onOrbit | exact GlobalTheory.ArcCM.tieC_of_onOrbit | (intros; apply GlobalTheory.ArcCM.tieC_of_onOrbit <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsCmArcDataAtSplitIsotropicPoint

section

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

namespace GlobalTheory.ArcCM.Exist

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem exists_lift_fibre {R R₂ K : Type} [CommRing R] [CommRing R₂] [Field K] {B : GlobalTheory.CM.PAT H (Sp R)}
    {B₂ : GlobalTheory.CM.PAT H (Sp R₂)} {j : R →+* R₂} (m : SABMap B₂.t B.t (spMap j)) {f : R →+* K} {f₂ : R₂ →+* K}
    (hf : f₂.comp j = f) {P : Out.PolAV (Sp K)} {ψ : P.A.left ⟶ B.pol.A.left} (hψ : IsPolFibre f B.pol P ψ)
    (act : 𝓞 E → (P.A ⟶ P.A)) (hact : ∀ x, (act x).left ≫ ψ = ψ ≫ (B.t.act.act x).left) :
    ∃ ψ₂ : P.A.left ⟶ B₂.pol.A.left, IsPolFibre f₂ B₂.pol P ψ₂ ∧
      ∀ x, (act x).left ≫ ψ₂ = ψ₂ ≫ (B₂.t.act.act x).left := by
  have hs : spMap f₂ ≫ spMap j = spMap f := (GlobalTheory.ArcId.sp_comp _ _).trans (congrArg spMap hf)
  have w : ψ ≫ B.t.G.hom = (P.A.hom ≫ spMap f₂) ≫ spMap j :=
    hψ.2.1.1.w.trans (by rw [Category.assoc, hs])
  obtain ⟨ψ₂, h₁, h₂⟩ : ∃ ψ₂ : P.A.left ⟶ B₂.t.G.left, ψ₂ ≫ m.φ = ψ ∧ ψ₂ ≫ B₂.t.G.hom = P.A.hom ≫ spMap f₂ :=
    ⟨_, m.cart.1.lift_fst _ _ w, m.cart.1.lift_snd _ _ w⟩
  have g₂ : IsGrpPullback P.A B₂.t.G (spMap f₂) ψ₂ := m.cart.cancel (hψ.2.1.congr hs.symm h₁.symm) h₂
  refine ⟨ψ₂, ⟨?_, g₂, ?_⟩, fun x => ?_⟩
  · exact H1.dim_unique P.A.hom P.smoothDim
      ((smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback g₂.1 B₂.dim)
      (eSec P.A (IsLocalRing.closedPoint K))
  · have e : LBIso (B₂.t.PP.L.pull ψ₂) (B.t.PP.L.pull ψ) :=
      GlobalTheory.LN.GenericPoint.lbIso_pull (GlobalTheory.LN.GenericPoint.lbIso_of_sabMap m) ψ₂ h₁.symm
    exact LBIso.trans (pull_isLB B₂.t.PP.isLB _) (pull_isLB B.t.PP.isLB _) P.isLB e hψ.2.2
  · apply m.cart.1.hom_ext
    · have e := m.act x
      change ((act x).left ≫ ψ₂) ≫ m.φ = (ψ₂ ≫ (B₂.t.act.act x).left) ≫ m.φ
      rw [Category.assoc, Category.assoc, h₁, hact, e, ← Category.assoc, h₁]
    · rw [Category.assoc, Category.assoc, h₂, Over.w (B₂.t.act.act x), h₂, ← Category.assoc, Over.w (act x)]

theorem one_le_of_isIso {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}
    {U : Unf Xo c σ r} (hU : IsUnf U) {k : U.Comp} {ξ' : Fin r → E} (hξ : (U.X k).IsIso ξ') :
    1 ≤ Dw.p ∧ 1 ≤ Dw.q := by
  obtain ⟨τ⟩ : Nonempty (U.X k).Ψ := by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    by_cases h : τ ∈ (U.X k).Ψ
    · exact ⟨⟨τ, h⟩⟩
    · exact ⟨⟨_, by_contra fun h' => h (((U.X k).cmType τ).2 h')⟩⟩
  have h := IsotropicIndexSums.isotropicIndex_bounds (U.X k) hξ.2.1 hξ.2.2 τ
  have h1 := hU.1
  have h2 := (hU.2.1 k).1
  omega

theorem exists_cmIn_tie : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (r : ℕ) (U : Unf Xo c c.F.val.toRingHom r) (Uw : UnfWit U) (k : U.Comp) (ξ' : Fin r → E) (x : Frame (U.X k).Ψ r) (Xx : DataX E r) (hX : Xx.toData = U.X k) (𝔄 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (La₀ La c₁ : ℝ) (lam : Fin (r - 2) → Fin r → E) (n' : ℕ) (ν₀ : E), IsUnf U → l.A = 1 → 3 ≤ r → (U.X k).IsIso ξ' → x ∈ (U.X k).dom → 𝔄 ≠ 0 → Xx.Λ = Submodule.span (𝓞 E) {v | ∃ a ∈ 𝔄, ∃ u ∈ Xx.L', v = a • u} → SplitData Xx ξ' La₀ (hX ▸ x) lam → La₀ ^ 2 ≤ La ^ 2 → 0 < n' → (∀ m ∈ (U.X k).Λp ξ', ∃ e : E, e • ξ' ∈ (U.X k).Λ ∧ (n' : ℂ) • (U.X k).aproj x ξ' ((U.X k).embV m) = (U.X k).embV (e • ξ')) → cc ν₀ = ν₀ → (∀ τ : E →+* ℂ, 0 ≤ (τ ν₀).re) → (∀ s : E, cc s = s → (∀ v ∈ (U.X k).Λ, ∃ u ∈ (U.X k).Λ, (transvMat (U.X k).Gm ξ' (s * (U.X k).κ0)).mulVec v - v = (l.M' : E) • u) → ∃ m : ℤ, Algebra.trace ℚ E (ν₀ * s) = m) → ((Algebra.trace ℚ E ν₀ : ℚ) : ℝ) / 2 ≤ c₁ → ∃ (K₁ : Type) (_ : Field K₁) (_ : NumberField K₁) (_ : Algebra c.F K₁) (em : K₁ →+* ℂ) (a : ArcIn Dw l (RingHom.id c.F) K₁ (algebraMap c.F K₁)) (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR K₁)) (th : a.D₀.P.L.Sec) (jj : ℤ) (s : CMIn a e th jj n' La c₁), em.comp (algebraMap c.F K₁) = c.F.val.toRingHom ∧ s.ν₀ = ν₀ ∧ Comparison₂ Uw a em s.ξ k ξ' x := by
  intro hK E _ _ _ H Dw l Xo c _ _ r U Uw k ξ' x Xx hX 𝔄 La₀ La c₁ lam n' ν₀ hU hA hr hξ hx h𝔄 hΛ hS hLa hn hap hν hν₀
    hint htr
  letI := H.starRing
  have hg : GoodEmb c c.F.val.toRingHom := rfl
  obtain ⟨hp, hq⟩ := one_le_of_isIso hU hξ
  have hpq : 3 ≤ Dw.p + Dw.q := hU.1 ▸ hr
  obtain ⟨A, gam, ξ, jj, DB, tyB, eB, hO, hξ0, hrk, hdvd, hbeta, hprim, hct, hab, hDp, hDq⟩ :=
    GlobalTheory.T.exists_analytic_model_on_frame_orbit_isolating E H Dw l Xo c _ r U Uw k ξ' x n' ν₀ hg hU hξ hx hap hν hν₀ hint
  obtain ⟨A', gam', ξ₁, eX, hO', hprim', hnorm', hξ₁, hbe', hab'⟩ :=
    GlobalTheory.ArcShift.exists_normAn_onOrbit E H Dw l Xo c _ r U Uw k ξ' x n' hg hU hξ hx hn A gam ξ hO hξ0 hrk hprim hct
  obtain ⟨tyB', eB', hB'⟩ := hab' DB ⟨tyB, eB, hab⟩
  have hrk' : Module.finrank (𝓞 E) A'.X = 1 := eX.finrank_eq.trans hrk
  obtain ⟨Z, hZ⟩ := GlobalTheory.T.exists_cm_lattice_data_abelianPart_split_point E H Dw l Xo c _ r U Uw k ξ' x Xx hX 𝔄 La₀ lam hg hU hξ hx h𝔄 hΛ hS A' gam' ξ₁ DB
    tyB' eB' hO' hrk' hDp hDq hB'
  obtain ⟨K, _, _, _, σ₁, ρ, X, ex, hσ₁, hρ, hhh, hex⟩ :=
    GlobalTheory.ArcCM.exists_cmObj_of_period hK E H l c DB _ tyB' _ hB'.2.2.2.2 Z (by omega) hB'.2.1 hA
  obtain ⟨aC, Λ, hΛA, φ, hφ, hφa, hlift⟩ := GlobalTheory.T.exists_complexArcDatum_cmFibre hK E H Dw l Xo c _ r U Uw k ξ' x (𝓞 K) X.B _ hg hU hA A' gam'
    ξ₁ DB tyB' eB' ex hO' hrk' (fun y y' => (hbe' y y').symm ▸ hdvd _ _) hprim' hB' hDp hDq hp hq hex
  subst hΛA
  have htau : TauCan aC.D₀ n' := (GlobalTheory.KappaAn.tauCan_iff_normAn E H Dw l c _ _ _ aC Λ.toGtAn₀ n').2 hnorm'
  let fC : aC.D₀.X ≃ₗ[𝓞 E] A.X := Λ.eX.symm.trans eX
  let ξC : Module.Dual ℤ aC.D₀.X := ξ.comp (fC.toLinearMap.restrictScalars ℤ)
  have htie := GlobalTheory.T.holomorphicArc_matches_frame_of_model_on_orbit hK E H Dw l Xo c _ r U Uw k ξ' x aC Λ.toGtAn₀ ξC hg hU hξ hx hA gam' ξ₁ hO'
    (fun y => by rw [hξ₁]; exact congrArg (fun z => ξ (eX z)) (Λ.eX.symm_apply_apply y)) hlift
  obtain ⟨K₂, _, _, _, i, σ₂, a, p, ψ, hσ₂, hbc, htau₂, hψ, hψa⟩ :=
    GlobalTheory.T.exists_cmArcData_descent_numberField hK E H Dw l c K σ₁ _ X.B aC φ n' hσ₁ hn hφ hφa htau
  obtain ⟨ρ₂, X₂, m, hρ₂, hh₂⟩ := GlobalTheory.ArcCM.exists_cmObj_baseChange hK E H K ρ σ₁ _ _ X K₂ i σ₂ hσ₂
  obtain ⟨ψ₂, hψ₂, hψa₂⟩ := exists_lift_fibre m (f₂ := algebraMap (𝓞 K₂) K₂) (RingHom.ext fun _ => rfl) hψ
    a.oa.onB.act hψa
  let f : aC.D₀.X ≃ₗ[𝓞 E] a.D₀.X := { p.xe with map_smul' := hbc.2.1 }
  let g : a.D₀.X ≃ₗ[𝓞 E] A.X := f.symm.trans fC
  have hem : σ₂.comp (algebraMap c.F K₂) = c.F.val.toRingHom := by
    rw [← hσ₁, ← hσ₂]
    exact RingHom.ext fun y => congrArg σ₂ (i.commutes y).symm
  have hbe : ∀ y z, a.be y z = A.be (g y) (g z) := fun y z => by
    obtain ⟨y, rfl⟩ := (Λ.eX.trans f).surjective y
    obtain ⟨z, rfl⟩ := (Λ.eX.trans f).surjective z
    refine (hbc.2.2.1 _ _).symm.trans ((Λ.be_eq _ _).trans ((hbe' _ _).trans ?_))
    simp [g, fC]
  have hhh₂ : ∀ j (τ : E →+* ℂ), ‖τ (X₂.hh j : E)‖ ≤ La ^ 2 := fun j τ => by
    rw [hh₂, hhh]; exact (hZ j τ).trans hLa
  have hρ' : σ₂ (ρ₂ : K₂) = H.rt0 := by rw [hρ₂, ← hρ, ← hσ₂]; rfl
  clear m hh₂
  generalize DB.p = p₁, DB.q = q₁ at X₂ hDp hDq hhh₂ ψ₂ hψ₂ hψa₂
  subst hDp hDq
  obtain ⟨e, th, s, hs, hsν⟩ := GlobalTheory.ArcCM.Letters.exists_cmIn hK E H Dw l c K₂ a ρ₂ σ₂ X₂ ψ₂ n' La c₁
    (ξ.comp (g.toLinearMap.restrictScalars ℤ)) ν₀ jj hp hq hpq hem hρ' hhh₂ hψ₂ hψa₂ hn htau₂
    (g.finrank_eq.trans hrk)
    (fun h => hξ0 (LinearMap.ext fun y => by
      obtain ⟨y, rfl⟩ := g.surjective y
      exact LinearMap.congr_fun h y))
    (GlobalTheory.ArcId.betaAt_comp g ξ hbe hbeta) htr
  refine ⟨K₂, _, _, _, σ₂, a, e, th, jj, s, hem, hsν, aC, p, ξC, hbc, fun y => ?_, htie⟩
  rw [hs]
  exact congrArg (fun z => ξ (fC z)) (f.symm_apply_apply y).symm

end GlobalTheory.ArcCM.Exist
end
end
