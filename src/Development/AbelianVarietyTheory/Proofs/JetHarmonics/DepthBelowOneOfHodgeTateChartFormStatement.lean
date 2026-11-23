module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
public import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
public import Development.AbelianVarietyTheory.Definitions.Jets.ColValMonomial
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsCharactersBoundedMinorsOfHodgeTateChartBou
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
import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
import Formalism.LocalToGlobal.ProjectiveLattices.SubConstMemOrig
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.BidegreeTwoJet
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.BoxTuple
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpBijectiveUniformisation
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermCut
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.LemmaBStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifBaseChangeSt
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.CanonGaugeExists
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DepthBoundFromCharactersPointDatumStatement
public import Formalism.LocalToGlobal.ProjectiveLattices.ChartDirectionsIntegral
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsWeightBasisFiltration
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ConnectionKillsSeries
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIntegralTypesAndDirections
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralChartColumnsToTupleHarmonicValues
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralChartFormalBiext
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MinorStProdRange
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MinorsDisjointColumnsHarmonic
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.StarRingExtOfStar
public import Mathlib.RingTheory.AdicCompletion.Topology
import Mathlib.Tactic.Basify
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TwistBaseChangeAndValuationStatements

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsCharactersBoundedMinorsOfHodgeTateChartBouStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
open IsDedekindDomain

theorem _root_.GlobalTheory.T.exists_characters_boundedMinors_of_hodgeTateChartBound : (∀ (p : ℕ) [Fact p.Prime], ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.HTFSt p) → ∀ (p : ℕ) [Fact p.Prime], ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra (FractionRing V) F] [Algebra V F] [IsScalarTower V (FractionRing V) F] (y : FamGerm.Pt1 E H V F), letI := H.starRing; IsAdicComplete (Ideal.span {(p : TWO.Ov y.v)}) (TWO.Ov y.v) → ¬ IsUnit (p : TWO.Ov y.v) → ∀ a : 𝓞 E, a * star a = (p : 𝓞 E) → (∃ u u' : 𝓞 E, u * a + u' * star a = 1) → ∀ (T : Type) [Fintype T] [DecidableEq T] (rk : T → ℕ) (τ : T → 𝓞 E →+* TWO.Ov y.v) (e : (Σ t, Fin (rk t)) → Fin y.d → TWO.Ov y.v), (∀ (c : 𝓞 E) l, (dAct F y.B c).mulVec (fun i => (e l i : F)) = (τ l.1 c : F) • fun i => (e l i : F)) → (∀ t, τ t a ∈ Ideal.span {(p : TWO.Ov y.v)}) → (∀ t, ∃ lam : Fin (rk t) → Fin y.d → TWO.Ov y.v, ∀ i i', ∑ s, lam i s * e ⟨t, i'⟩ s = if i = i' then 1 else 0) → (∃ ε : T → 𝓞 E, ∀ t t', τ t' (ε t) - (if t = t' then 1 else 0) ∈ Ideal.span {(p : TWO.Ov y.v)}) → ∀ c : TWO.Ov y.v, (p - 1) • y.v (c : F) = y.v (p : F) → ∀ (n : ℕ) (col : ∀ t, Fin (rk t) → Fin n), (∀ t, Function.Injective (col t)) → ∃ yy : (Σ t, Fin (rk t)) × Fin n → TWO.Ov y.v, (∀ b, y.CharAt a p e (fun l => yy (l, b))) ∧ ∀ t (s : Fin (rk t)), y.v (((Matrix.of fun a i : Fin (s.val + 1) => yy (⟨t, Fin.castLE s.isLt a⟩, col t (Fin.castLE s.isLt i))).det : TWO.Ov y.v) : F) ≤ (s.val + 1) • y.v (c : F) := by
  first | exact @GlobalTheory.ChartCharacter.characters_exist_of_chartBound | exact GlobalTheory.ChartCharacter.characters_exist_of_chartBound | (intros; apply GlobalTheory.ChartCharacter.characters_exist_of_chartBound <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIntegralTypesAndDirectionsStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

theorem _root_.GlobalTheory.T.exists_integral_types_and_directions' : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y) (ϖ : T.V), Irreducible ϖ → ∀ (g : ℕ), g.Prime → ¬ IsUnit ((g : ℕ) : T.V) → (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(g : 𝓞 E)})).card = Module.finrank ℚ E → (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(g : 𝓞 E)})).Nodup → ∀ (F : Type) [Field F] [CharZero F] [Algebra T.Fr F] [Algebra T.V F] [IsScalarTower T.V T.Fr F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v → letI := io.toAlgebra; ∃ (σ : (E →+* ℂ) → 𝓞 E →+* TWO.Ov v) (e : Lt1 Dw → Fin (chD C.ch) → TWO.Ov v), (∀ τ a, (σ τ a : F) = algebraMap T.Fr F (io (embK c τ a))) ∧ (∀ ℓ i, (e ℓ i : F) = algebraMap T.V F (C.uvecT ℓ i)) ∧ (∀ ℓ i, (e ℓ i : F) = algebraMap T.Fr F (C.ch.uvec ℓ i)) ∧ (∀ (a : 𝓞 E) ℓ, (dAct F C.ch.B a).mulVec (fun i => (e ℓ i : F)) = (σ ℓ.1 a : F) • fun i => (e ℓ i : F)) ∧ (∀ τ a, (0 < v (σ τ a : F) → σ τ a ∈ Ideal.span {((g : ℕ) : TWO.Ov v)}) ∧ (¬ 0 < v (σ τ a : F) → IsUnit (σ τ a))) ∧ (∀ τ a, σ (ComplexEmbedding.conjugate τ) a = σ τ (star a)) ∧ (open Classical in ∃ lam : Lt1 Dw → Fin (chD C.ch) → TWO.Ov v, ∀ l l', ∑ s, lam l s * e l' s = if l = l' then 1 else 0) ∧ (open Classical in ∃ ε : (E →+* ℂ) → 𝓞 E, ∀ τ τ', σ τ' (ε τ) - (if τ = τ' then 1 else 0) ∈ Ideal.span {((g : ℕ) : TWO.Ov v)}) ∧ ¬ IsUnit ((g : ℕ) : TWO.Ov v) := by
  first | exact @GlobalTheory.PowGerm.exists_integral_types_and_directions | exact GlobalTheory.PowGerm.exists_integral_types_and_directions | (intros; apply GlobalTheory.PowGerm.exists_integral_types_and_directions <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralChartColumnsToTupleHarmonicValuesStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

theorem _root_.GlobalTheory.T.integralChart_columns_to_tuple_harmonicValues : Laws → Laws2 → Laws4 → TwistBaseChangeStatement → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), FrTrunc C.I.G (𝟙 (Sp T.V)) (chD C.ch) C.xT C.eT → ∀ (P : PELUnif (maximalIdeal T.V) C.I.G) (tors : P.TorsionIso) (ϖ : T.V) (hϖ : Irreducible ϖ) (Q : P.D.toPre.X → ℤ) (hQ : IsQ P.D.toPre ϖ Q) (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra T.Fr F] [Algebra T.V F] [IsScalarTower T.V T.Fr F] (v : AddValuation F (WithTop ℚ)) (hv : ValOver ϖ F v), letI := io.toAlgebra; ∃ x hx j hj u hu B hB ρ hρ, B.G.F = C.FT ∧ B.A.act = C.actT ∧ ∀ (g g' : ℕ) (π : 𝓞 E), 1 ≤ g → 1 ≤ g' → π * star π = (g : 𝓞 E) → ∀ (n : ℕ) (D' : DegData T.V (maximalIdeal T.V)) (A' : PolAV (Spec (CommRingCat.of T.Fr))) (G' : Over (Sp T.V)) [GrpObj G'] [IsCommMonObj G'] (pD : IsPowDeg D'.toPre P.D.toPre n) (pA : IsPowPolAV A' P.A n) (pG : IsPowGrp G' C.I.G.G n) (U' : Unif (maximalIdeal T.V) D' A' G') (PU : UnifPowOf3 pD pA pG U' P.U) [Module (𝓞 E) D'.toPre.X] (oD' : D'.toPre.OAct (𝓞 E)), (∀ (a : 𝓞 E) (x : D'.toPre.X) (i : Fin n), pD.xe (a • x) i = a • pD.xe x i) → (∀ (a : 𝓞 E) (i : Fin n), oD'.onB.act a ≫ pD.pw.pr i = pD.pw.pr i ≫ P.oD.onB.act a) → ∀ (s : Fin n → Fam P.D.toPre F g') (s' t : Fin n → Fam P.D.toPre F (g' * g)) (f : Fin n → PS F 1 (chD C.ch)), (∀ b, NuGe P.D Q F v g' (s b) 0 ∧ PullAl P.D F P.oD (star π) g' g (s b) (s' b) ∧ (FamGerm.Pt1.mk ϖ hϖ T.cpl C.I.G P tors Q hQ v hv (chD C.ch) x hx j hj u hu B hB ρ hρ : FamGerm.Pt1 E H T.V F).Transl (g' * g) π (s' b) (t b) ∧ (FamGerm.Pt1.mk ϖ hϖ T.cpl C.I.G P tors Q hQ v hv (chD C.ch) x hx j hj u hu B hB ρ hρ : FamGerm.Pt1 E H T.V F).Germ (g' * g) (t b) (f b)) → ∃ (S : Fam D'.toPre F g') (S₂ : Fam D'.toPre F (g' * g)) (p' : QkPt D'.toPre F (g' * g)) (w' : LB.Gen (LB.LinComb D'.toPre.P.L (DegPre.lineφ D'.toPre F p'.g.b) (DegPre.lineε (g' * g)))) (ζ' : F) (x' : TFK (R := T.V) F ⟶ A'.A) (T₀ T₁ : Fam D'.toPre F (g' * g)) (σ' : U'.toUnifPre.SecGF F (g' * g)) (h : PS F n (chD C.ch)) (un : PS T.V 1 (chD C.ch)), BoxTup C P Q F v g g' π pG PU oD' S S₂ p' w' ζ' x' T₀ T₁ σ' h ∧ MvPowerSeries.constantCoeff un = 1 ∧ h = boxSer (fun b => f b * MvPowerSeries.map (algebraMap T.V F) un) ∧ ∀ h₀ : PS F 2 (chD C.ch), B.IsCanonGauge F h₀ → ∀ (rk : (E →+* ℂ) → ℕ) (hrk : ∀ τ, rk τ ≤ Dw.mult τ) (Pp : MvPolynomial ((Σ τ : E →+* ℂ, Fin (rk τ)) × Fin n) F), (∀ (τ : E →+* ℂ) (i : Fin (rk τ)) (i' : Fin (rk (ComplexEmbedding.conjugate τ))), ∑ b : Fin n, MvPolynomial.pderiv ((⟨τ, i⟩ : Σ τ : E →+* ℂ, Fin (rk τ)), b) (MvPolynomial.pderiv ((⟨ComplexEmbedding.conjugate τ, i'⟩ : Σ τ : E →+* ℂ, Fin (rk τ)), b) Pp) = 0) → nabValN C.ch.B F (MvPowerSeries.map (algebraMap T.Fr F) C.ch.h) H.w0 (g' * g) h (fun ℓ : LtN Dw n => ℓ.2.2) (fun (ℓ : LtN Dw n) i => algebraMap T.Fr F (C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩ i)) (MvPolynomial.rename (fun p : (Σ τ : E →+* ℂ, Fin (rk τ)) × Fin n => (⟨p.1.1, (Fin.castLE (hrk p.1.1) p.1.2, p.2)⟩ : LtN Dw n)) Pp) = (FamGerm.Pt1.mk ϖ hϖ T.cpl C.I.G P tors Q hQ v hv (chD C.ch) x hx j hj u hu B hB ρ hρ : FamGerm.Pt1 E H T.V F).colVal h₀ (g' * g) (fun (l : Σ τ : E →+* ℂ, Fin (rk τ)) i => algebraMap T.V F (C.uvecT ⟨l.1, Fin.castLE (hrk l.1) l.2⟩ i)) Pp f := by
  first | exact @GlobalTheory.transfer_columns | exact GlobalTheory.transfer_columns | (intros; apply GlobalTheory.transfer_columns <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsUnitIffNotIsUnitOfCoprime

section

@[expose] public section

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory.PowGerm

theorem isAdicComplete_ov_of_range {F : Type} [Field F] (v : AddValuation F (WithTop ℚ)) (O : Type) [CommRing O]
    [Algebra O F] (hinj : Function.Injective (algebraMap O F))
    (hr : ∀ z : F, 0 ≤ v z ↔ z ∈ (algebraMap O F).range) (g : ℕ)
    (hc : IsAdicComplete (Ideal.span {((g : ℕ) : O)}) O) :
    IsAdicComplete (Ideal.span {((g : ℕ) : TWO.Ov v)}) (TWO.Ov v) := by
  let φ : O →+* TWO.Ov v := (algebraMap O F).codRestrict (TWO.Ov v) fun a => (hr _).2 ⟨a, rfl⟩
  have hφ : Function.Bijective φ := by
    refine ⟨fun a b h => hinj (congrArg Subtype.val h), fun z => ?_⟩
    obtain ⟨a, ha⟩ := (hr z).1 z.2
    exact ⟨a, Subtype.ext ha⟩
  have h := (IsAdicComplete.congr_ringEquiv (Ideal.span {((g : ℕ) : O)}) (RingEquiv.ofBijective φ hφ)).2 hc
  rwa [Ideal.map_span, Set.image_singleton, map_natCast] at h

theorem isUnit_iff_not_isUnit_of_coprime {R : Type} [CommRing R] [IsLocalRing R] {x y u u' : R}
    (h : ¬ IsUnit (x * y)) (h1 : u * x + u' * y = 1) : IsUnit x ↔ ¬ IsUnit y := by
  refine ⟨fun hx hy => h (hx.mul hy), fun hy => ?_⟩
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one h1 with h2 | h2
  · exact isUnit_of_mul_isUnit_right h2
  · exact absurd (isUnit_of_mul_isUnit_right h2) hy

theorem card_filter_val_lt (n₁ n₂ : ℕ) :
    (Finset.univ.filter fun b : Fin (n₁ + n₂) => b.val < n₁).card = n₁ := by
  rw [Fin.card_filter_val_lt]; omega

theorem lemmaBT_of_characters : Laws → Laws2 → Laws4 → TwistBaseChangeStatement → (∀ (p : ℕ) [Fact p.Prime], ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra (FractionRing V) F] [Algebra V F] [IsScalarTower V (FractionRing V) F] (y : FamGerm.Pt1 E H V F), letI := H.starRing; IsAdicComplete (Ideal.span {(p : TWO.Ov y.v)}) (TWO.Ov y.v) → ¬ IsUnit (p : TWO.Ov y.v) → ∀ a : 𝓞 E, a * star a = (p : 𝓞 E) → (∃ u u' : 𝓞 E, u * a + u' * star a = 1) → ∀ (T : Type) [Fintype T] [DecidableEq T] (rk : T → ℕ) (τ : T → 𝓞 E →+* TWO.Ov y.v) (e : (Σ t, Fin (rk t)) → Fin y.d → TWO.Ov y.v), (∀ (c : 𝓞 E) l, (dAct F y.B c).mulVec (fun i => (e l i : F)) = (τ l.1 c : F) • fun i => (e l i : F)) → (∀ t, τ t a ∈ Ideal.span {(p : TWO.Ov y.v)}) → (∀ t, ∃ lam : Fin (rk t) → Fin y.d → TWO.Ov y.v, ∀ i i', ∑ s, lam i s * e ⟨t, i'⟩ s = if i = i' then 1 else 0) → (∃ ε : T → 𝓞 E, ∀ t t', τ t' (ε t) - (if t = t' then 1 else 0) ∈ Ideal.span {(p : TWO.Ov y.v)}) → ∀ c : TWO.Ov y.v, (p - 1) • y.v (c : F) = y.v (p : F) → ∀ (n : ℕ) (col : ∀ t, Fin (rk t) → Fin n), (∀ t, Function.Injective (col t)) → ∃ yy : (Σ t, Fin (rk t)) × Fin n → TWO.Ov y.v, (∀ b, y.CharAt a p e (fun l => yy (l, b))) ∧ ∀ t (s : Fin (rk t)), y.v (((Matrix.of fun a i : Fin (s.val + 1) => yy (⟨t, Fin.castLE s.isLt a⟩, col t (Fin.castLE s.isLt i))).det : TWO.Ov y.v) : F) ≤ (s.val + 1) • y.v (c : F)) → LemmaBT := by
  intro L1 L2 L4 TB hch E _ _ _ H Dw l Xo c inst hst
  obtain rfl := starSt E H inst hst
  letI := H.starRing
  intro T io y hy C hfr P tors ϖ hϖ Q hQ g g' hg hg' hne og og' π π' hπ hπ' hcop hcop' hcard hnd hnu F _ _ _ _ _ _ v hv
    O _ _ _ _ hinj hO hOc I Φ M0 r b hΦ hb1 hb2 n₁ n₂ hn D' A' G' _ _ pD pA pG U' PU _ oD' hx1 hx2 m hm hd1 hd2 hd3 ρg hρg
  letI := io.toAlgebra
  classical
  haveI : Fact g.Prime := ⟨hg⟩
  obtain ⟨σ, e, hσ, he1, -, heig, hval, hconj, ⟨lam, hlam⟩, hε, hgu⟩ :=
    GlobalTheory.T.exists_integral_types_and_directions' E H Dw l Xo c T io y C ϖ hϖ g hg hnu hcard hnd F v hv
  obtain ⟨x, hx, j, hj, u, hu, B, hB, ρ, hρ, -, hact, htr⟩ :=
    GlobalTheory.T.integralChart_columns_to_tuple_harmonicValues L1 L2 L4 TB E H Dw l Xo c T io y C hfr P tors ϖ hϖ Q hQ F v hv
  obtain ⟨BT, -, hBT, -, -, -, -, hBF⟩ := integralChart_formalBiext E H Dw l Xo c T io y C
  have hdA : ∀ a, dAct F B a = dAct F C.ch.B a := by
    intro a
    have h1 : B.actK F a = C.ch.B.actK F a := by
      rw [← (hBF F).2.1 a]
      unfold FB.actK
      rw [hact, hBT]
    unfold dAct
    rw [h1]
  obtain ⟨rk, hrk, col, m', hcol, hty, hdeg, hmin⟩ :=
    minorSt E H Dw F (fun τ => 0 < v (algebraMap T.Fr F (io (embK c τ (star π))))) m n₁ n₂ (by convert hm)
  obtain ⟨h₀, hh₀⟩ := canonGauge_exists T.V (chD C.ch) (𝓞 E) F B
  have hππ : star π * star (star π) = (g : 𝓞 E) := by rw [star_star, mul_comm, hπ]
  obtain ⟨u₁, u₂, hu12⟩ := hcop
  have hg'0 : (0 : ℝ) < g' := by exact_mod_cast hg'.pos
  have hred : (FamGerm.Pt1.mk ϖ hϖ T.cpl C.I.G P tors Q hQ v hv (chD C.ch) x hx j hj u hu B hB ρ hρ :
      FamGerm.Pt1 E H T.V F).Red r b Φ (max M0 0) := by
    refine ⟨hΦ, le_max_right _ _, hb1, fun i z => ?_⟩
    have h1 := hb2 i z
    have h2 : (0 : ℝ) ≤ Q z := by
      by_cases hz : z = 0
      · rw [hz, Q_zero hϖ P.D hQ, Int.cast_zero]
      · have h3 := Q_pos hϖ P.D hQ hz
        exact_mod_cast (by omega : 0 ≤ Q z)
    exact h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) h2)
  obtain ⟨s, s', t, f, gm, hs, hgm, hle⟩ := GlobalTheory.T.depth_bound_from_characters_pointDatum L1 L2 L4 TB hch g E H T.V F
    (FamGerm.Pt1.mk ϖ hϖ T.cpl C.I.G P tors Q hQ v hv (chD C.ch) x hx j hj u hu B hB ρ hρ)
    (isAdicComplete_ov_of_range v O hinj hO g hOc) hgu Dw I r b Φ (max M0 0) hred (star π) g' hππ
    ⟨u₂, u₁, by rw [star_star, add_comm, hu12]⟩ ((Nat.coprime_primes hg hg').2 hne) (E →+* ℂ) rk σ
    (fun l => e ⟨l.1, Fin.castLE (hrk l.1) l.2⟩)
    (fun a l => by rw [show dAct F _ a = dAct F C.ch.B a from hdA a]; exact heig a _)
    (fun τ => 0 < v (algebraMap T.Fr F (io (embK c τ (star π)))))
    (fun τ h => (hval τ _).1 (by rw [hσ]; exact h)) (fun τ h => (hval τ _).2 (by rw [hσ]; exact h))
    ⟨fun l => lam ⟨l.1, Fin.castLE (hrk l.1) l.2⟩, fun l l' => by
      refine (hlam _ _).trans (if_congr ?_ rfl rfl)
      obtain ⟨τ, i⟩ := l
      obtain ⟨τ', i'⟩ := l'
      constructor
      · intro h
        obtain rfl : τ = τ' := congrArg Sigma.fst h
        have h2 := eq_of_heq (Sigma.mk.inj h).2
        obtain rfl : i = i' := Fin.castLE_injective _ h2
        rfl
      · intro h
        rw [h]⟩
    (by convert hε) (n₁ + n₂) (Finset.univ.filter fun b => b.val < n₁) col m' hcol
    (fun τ i => by rw [Finset.mem_filter, ← hty τ i]; simp) (degOf Dw m) hdeg.symm hd1 hd2
    (by
      rcases le_total M0 0 with h | h
      · rw [max_eq_right h, mul_zero]; exact hg'0
      · rw [max_eq_left h]; exact hd3)
    h₀ hh₀ ρg hρg
  simp only [star_star] at hs
  obtain ⟨S, S₂, p', w', ζ', x', T₀, T₁, σ', h, un, hbox, -, -, hvl⟩ :=
    htr g g' π hg.one_le hg'.one_le hπ (n₁ + n₂) D' A' G' pD pA pG U' PU oD' hx1 hx2 s s' t f hs
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9⟩ := hbox
  refine ⟨S, S₂, p', w', ζ', x', T₀, T₁, σ', h, gm, b1, b2, b3, b4, b5, b6, b7, b8, b9, ?_, ?_⟩
  · rw [hmin, hvl h₀ hh₀ rk hrk (FamGerm.minorsP F col m') ?_, ← hgm]
    · simp only [he1]
    · intro τ
      refine minors_disjoint_columns_harmonic F _ rk _ col m' _ rfl τ _ fun i i' hii => ?_
      have k1 := hty τ i
      have k2 := hty _ i'
      rw [hii, k2, ← hσ, ← hσ, hconj, star_star] at k1
      have k3 : ∀ a, 0 < v (σ τ a : F) ↔ ¬ IsUnit (σ τ a) := fun a =>
        ⟨fun h hu => hgu (isUnit_of_dvd_unit (Ideal.mem_span_singleton.1 ((hval τ a).1 h)) hu),
          fun h => by_contra fun h' => h ((hval τ a).2 h')⟩
      rw [k3, k3] at k1
      have k4 : IsUnit (σ τ π) ↔ ¬ IsUnit (σ τ (star π)) :=
        isUnit_iff_not_isUnit_of_coprime (u := σ τ u₁) (u' := σ τ u₂) (by rw [← map_mul, hπ, map_natCast]; exact hgu)
          (by rw [← map_mul, ← map_mul, ← map_add (f := _), hu12, map_one])
      tauto
  · rw [card_filter_val_lt] at hle
    have h1 : (0 : ℝ) ≤ (degOf Dw m : ℝ) ^ 2 * Φ / g' := by positivity
    have h2 : 2 * (degOf Dw m : ℝ) ^ 2 * Φ / g' = 2 * ((degOf Dw m : ℝ) ^ 2 * Φ / g') := by ring
    rw [h2, mul_comm (ρg : ℝ)]
    linarith

end GlobalTheory.PowGerm
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.DepthBelowOneOfHodgeTateChartForm

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
open IsDedekindDomain

namespace GlobalTheory.PowGerm

theorem lemmaBT_of_hodgeTate_chart : (∀ (p : ℕ) [Fact p.Prime], ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.HTFSt p) → LemmaBT := fun h =>
  lemmaBT_of_characters GlobalTheory.firstFiveLaws.1 GlobalTheory.firstFiveLaws.2.1 GlobalTheory.firstFiveLaws.2.2.2.1
    GlobalTheory.twistBaseChange_and_valuation_statements.1 (GlobalTheory.T.exists_characters_boundedMinors_of_hodgeTateChartBound h)

end GlobalTheory.PowGerm
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.DepthBelowOneOfHodgeTateChartFormStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
open IsDedekindDomain

theorem _root_.GlobalTheory.T.depthBelowOne_of_hodgeTate_chart_form : (∀ (p : ℕ) [Fact p.Prime], ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.HTFSt p) → LemmaBT := by
  first | exact @GlobalTheory.PowGerm.lemmaBT_of_hodgeTate_chart | exact GlobalTheory.PowGerm.lemmaBT_of_hodgeTate_chart | (intros; apply GlobalTheory.PowGerm.lemmaBT_of_hodgeTate_chart <;> assumption)
end
end
