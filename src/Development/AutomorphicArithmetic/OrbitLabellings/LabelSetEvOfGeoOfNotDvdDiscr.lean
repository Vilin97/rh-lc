module

public import Formalism.LocalToGlobal.CharacterGerms.SelfConjugateRowData
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
public import Formalism.LocalToGlobal.CharacterGerms.RowTieUpFBrI
public import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsFormalGroupJetsChart
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.StarRingExtOfStar
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsFiniteExtPelUnif
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
import Formalism.IncomingBounds.IncomingBound
public import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsLocalHomValuationExtension
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Formalism.LocalToGlobal.CharacterGerms.CharacterHypothesisUnramified
import Formalism.LocalToGlobal.CharacterGerms.RowTiePEmbIntSt
public import Formalism.LocalToGlobal.CharacterGerms.RowTieUpFBrFin
import Mathlib.Tactic.Linter.HaveILetI
import Development.AutomorphicArithmetic.OrbitLabellings.RowDefs
import Formalism.LocalToGlobal.CharacterGerms.ContentZeroAt

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsRestBis

section

@[expose] public section

open NumberField IsLocalRing Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory

namespace GlobalTheory.IntegralChartCover

theorem cover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (lv : Level H) (Xo : Moduli Dw lv) (c : Coeff lv) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C3 : IntChart T io y), ∃ (T' : CDVR) (φ : T.V →+* T'.V) (t' : SAB H (Sp T'.V)), Function.Injective φ ∧ φ.Finite ∧ UpFBr.GeoJ T'.V t'.G (𝓞 E) (fun a => t'.act.act a) (chD C3.ch) (fun i => MvPowerSeries.map φ (C3.FT i)) (fun a i => MvPowerSeries.map φ (C3.actT a i)) := by
  intro E _ _ _ H Dw lv Xo c inst hstar T io y C3
  obtain rfl : inst = H.starRing := GlobalTheory.PowGerm.starRing_ext_of_star inst H.starRing hstar
  letI := H.starRing
  letI := io.toAlgebra
  obtain ⟨T', φ, t', m, hi, hf, ⟨P⟩⟩ := GlobalTheory.ChartCharacters.exists_finite_ext_pelUnif Xo T C3.I.G C3.I.t' C3.I.m2 _ C3.I.m1
  obtain ⟨F', x', act', hF, hA, hx, ha⟩ := GlobalTheory.integralChart_baseChange E H Dw lv Xo c T io y C3 T' φ t' m
  exact ⟨T', φ, t', hi, hf, P.D, P.A, P.U.toUnifPre, F', x', _, t'.act.toRingAct, P.oD, P.oA, act', hF, funext hA, fun _ => rfl, hx, P.lin, ha⟩

end GlobalTheory.IntegralChartCover
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsRestTer

section

@[expose] public section

open NumberField IsLocalRing Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF
attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory

namespace GlobalTheory.UpperBoundDescent

theorem desc : ∀ (p : ℕ) [Fact p.Prime] (T T' : CDVR) (φ : T.V →+* T'.V), Function.Injective φ → φ.Finite → ¬ IsUnit (p : T.V) → ∀ (OE : Type) [CommRing OE] [StarRing OE] (dd : ℕ) (FT : Fin dd → PS T.V 2 dd) (actT : OE → Fin dd → PS T.V 1 dd), UpFBr.UpFLaw p T'.V OE dd (fun i => MvPowerSeries.map φ (FT i)) (fun a i => MvPowerSeries.map φ (actT a i)) → UpFBr.UpFLaw p T.V OE dd FT actT := by
  intro p _ T T' φ hφ hfin hp OE _ _ dd FT actT h C _ _ _ v O _ _ hv _ _ _ _ iota hloc w _ t hb hf r W hW j
  have hinj : Function.Injective ((algebraMap O C).comp iota) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    by_contra h0
    have hp0 : (p : T.V) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible T.V
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h0 hϖ
    obtain ⟨m, u', hm⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hp0 hϖ
    have h1 : ((algebraMap O C).comp iota) ϖ = 0 := by
      rw [map_mul, map_pow, mul_eq_zero] at ha
      rcases ha with ha | ha
      · exact absurd ha (u.isUnit.map _).ne_zero
      · exact pow_eq_zero_iff'.1 ha |>.1
    have hm0 : m ≠ 0 := by
      rintro rfl
      exact hp (by rw [hm]; simp)
    have h2 := congrArg ((algebraMap O C).comp iota) hm
    rw [map_natCast, map_mul, map_pow, h1, zero_pow hm0, mul_zero] at h2
    exact (Fact.out : p.Prime).ne_zero (by exact_mod_cast h2)
  obtain ⟨ι', hl, hc⟩ := GlobalTheory.CharDepth.exists_local_extension_of_integral v hv φ hφ hfin.to_isIntegral iota hinj
  have key : ∀ {σ : Type} (f : MvPowerSeries σ T.V),
      MvPowerSeries.map ι' (MvPowerSeries.map φ f) = MvPowerSeries.map iota f := by
    intro σ f
    ext n
    simp only [MvPowerSeries.coeff_map, ← hc, RingHom.comp_apply]
  have := h C v O hv ι' hl w t hb hf r W (by simpa only [key] using hW) j
  simpa only [key] using this

end GlobalTheory.UpperBoundDescent
end
end

-- Source module: Development.AutomorphicArithmetic.OrbitLabellings.LabelSetEvOfGeoOfNotDvdDiscr

section

@[expose] public section

open scoped BigOperators
open Classical
open Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.RF UpperTheory.G2 NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

theorem UpperTheory.labelSet_ev_of_geo_of_not_dvd_discr :
    (∀ (p : ℕ) [Fact p.Prime], ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.UpFSt p) →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (lv : Level H)
    (Xo : Moduli Dw lv) (c : Coeff lv) [StarRing (𝓞 E)], (∀ x : 𝓞 E, star x = H.bar x) →
    ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C3 : IntChart T io y) (C : Type) [Field C] [CharZero C] (V : VF C)
    (ι : T.Fr →+* C), EmbOK T V ι → ∀ (k : ℕ) (Y : FBChart C V (𝓞 E) (chD C3.ch)), IsBC C3 ι k Y →
    y.IsAlg →
    ∀ (Orb : Type) [Fintype Orb] (d : ℕ) [NeZero d] (lab : Formalism.L2.FormalSeriesBounds.LabS E C Orb d) (ha : LabSArith V io ι lab),
    ∀ (hg : LabSGeo C3 ι Y lab), ¬ (V.l : ℤ) ∣ NumberField.discr E → Even d → lab.RankOK Dw → (∀ o s, lab.big o 0 s ↔ Even s.val) →
    ∀ (o : Orb) (Hc : ∀ g, (Y.rawSelf (selfOfLab ha hg o)).CartHyp V g), RawChart.CHSt Hc := by
  intro hup E _ _ _ H Dw lv Xo c _ hstar T io y C3 C _ _ V ie hie k Y hY _ Orb _ d _ lab ha hg hdisc _ hr _ o Hc
  haveI : Fact V.l.Prime := ⟨V.l_prime⟩
  have hd : ¬ ((V.l : ℤ) ∣ Algebra.discr ℤ (Module.Free.chooseBasis ℤ (𝓞 E))) := by
    rwa [NumberField.discr_eq_discr E (Module.Free.chooseBasis ℤ (𝓞 E))]
  obtain ⟨T', φ, t', hi, hf, hG⟩ := GlobalTheory.IntegralChartCover.cover E H Dw lv Xo c hstar T io y C3
  have hp : ¬ IsUnit ((V.l : ℕ) : T.V) :=
    UpFBr.not_isUnit_l (ie.comp (algebraMap T.V T.Fr)) fun t => embIntSt_holds T C V ie hie t
  have hp' : ¬ IsUnit ((V.l : ℕ) : T'.V) := fun h => by
    letI := φ.toAlgebra
    haveI : Algebra.IsIntegral T.V T'.V := ⟨hf.to_isIntegral⟩
    haveI : FaithfulSMul T.V T'.V := (faithfulSMul_iff_algebraMap_injective _ _).2 hi
    exact hp (isUnit_of_map_unit (algebraMap T.V T'.V) _ (by rwa [map_natCast]))
  have hL := GlobalTheory.UpperBoundDescent.desc V.l T T' φ hi hf hp _ _ _ _
    (UpFBr.upFLaw_of_geoJ (hup V.l) Y.l_odd T'.V hp' t'.G _ _ _ hG hd)
  exact UpFBr.chStSelf_of_upChar Y (selfOfLab ha hg o) (rankHyp_ofLabS ha hg hr o) Hc
    (UpFBr.upCharS_chartL hL hie hd hY ha hg hr o Hc)
end
end
