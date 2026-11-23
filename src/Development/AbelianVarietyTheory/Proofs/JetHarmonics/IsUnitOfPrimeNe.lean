module

public import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.OLinBaseChangeSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValuationMultiplicationInvariance
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifBaseChangeSt
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.EqZeroOfSval
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.OperatorOnPullbackEqSum
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.StalkMapInjectiveOfFlat
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
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsPelUnifOfUnifPow
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBasisOfCoord
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.TwistingStatementsOfLaws
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ValuationThetaRatioEqBilinear
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorsionIsoOfLinearUniformisationTripleStatement
import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsGermLinearMap
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FrameNStHolds
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ImportsTer
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.PowPELOfLaws
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.UniversalJetsPowerProductStatement
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.UniversalStatementStatement
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBasisOfCoord
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.PsiWeightZeroProduct
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.TwistingStatementsOfLaws
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.BOfNsmulLeft
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.CmLiftConditionOfLaws

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.DescentOneGenerator

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.OneGenerator

theorem transport_level {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {t : SAB H (Sp V)}
    (P : PELUnif (maximalIdeal V) t) {F : Type} [Field F] [Algebra (FractionRing V) F] {n m : ℕ} (h : n = m)
    (θ r₀ r : Fam P.D.toPre F n) (p : QkPt P.D.toPre F n)
    (w : LB.Gen (LB.LinComb P.D.toPre.P.L (DegPre.lineφ P.D.toPre F p.g.b) (DegPre.lineε n))) (ζ : F)
    (x : TFK (R := V) F ⟶ P.A.A) (hx : P.ToA F n p x) (hw : w.IsGen) (hf : FinOrd P.D F n p w ζ)
    (hΦ : PhiRel P.D.toPre F n p w θ r₀) (hs : Fam.IsSmul P.D.toPre F ζ r₀ r) :
    ∃ (θ' r₀' r' : Fam P.D.toPre F m) (p' : QkPt P.D.toPre F m)
      (w' : LB.Gen (LB.LinComb P.D.toPre.P.L (DegPre.lineφ P.D.toPre F p'.g.b) (DegPre.lineε m))),
      HEq θ θ' ∧ P.ToA F m p' x ∧ w'.IsGen ∧ FinOrd P.D F m p' w' ζ ∧ PhiRel P.D.toPre F m p' w' θ' r₀' ∧
        Fam.IsSmul P.D.toPre F ζ r₀' r' ∧ HEq r r' := by
  subst h
  exact ⟨θ, r₀, r, p, w, HEq.rfl, hx, hw, hf, hΦ, hs, HEq.rfl⟩

end GlobalTheory.OneGenerator

namespace GlobalTheory


open OneGenerator in
theorem descent_one_generator : Laws → Laws2 → Laws4 → TwistBaseChangeStatement → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (t : SAB H (Sp V)) (P : PELUnif (maximalIdeal V) t), P.TorsionIso → letI := H.starRing; ∀ (a a' : 𝓞 E) (g g' : ℕ), 1 ≤ g → 1 ≤ g' → Nat.Coprime g g' → a * star a = (g : 𝓞 E) → a' * star a' = (g' : 𝓞 E) → ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] [IsAlgClosed F] (θ : Fam P.D.toPre F 1) (θα : Fam P.D.toPre F (1 * g')), PullAl P.D F P.oD a' 1 g' θ θα → ∀ (pb : QkPt P.D.toPre F (1 * g')) (wb : LB.Gen (LB.LinComb P.D.toPre.P.L (DegPre.lineφ P.D.toPre F pb.g.b) (DegPre.lineε (1 * g')))) (ζb : F) (xb : TFK (R := V) F ⟶ P.A.A) (tb₀ tb : Fam P.D.toPre F (1 * g')), P.ToA F (1 * g') pb xb → xb ≫ P.oA.act (star a') = 1 → wb.IsGen → ζb ≠ 0 → FinOrd P.D F (1 * g') pb wb ζb → PhiRel P.D.toPre F (1 * g') pb wb θα tb₀ → Fam.IsSmul P.D.toPre F ζb tb₀ tb → ∀ (p : QkPt P.D.toPre F (1 * g' * g)) (w : LB.Gen (LB.LinComb P.D.toPre.P.L (DegPre.lineφ P.D.toPre F p.g.b) (DegPre.lineε (1 * g' * g)))) (ζ : F) (x : TFK (R := V) F ⟶ P.A.A), w.IsGen → ζ ≠ 0 → FinOrd P.D F (1 * g' * g) p w ζ → P.ToA F (1 * g' * g) p x → x ≫ P.oA.act (star a) = 1 → ∀ (s₂ t₀ r : Fam P.D.toPre F (1 * g' * g)), PullAl P.D F P.oD a (1 * g') g tb s₂ → PhiRel P.D.toPre F (1 * g' * g) p w s₂ t₀ → Fam.IsSmul P.D.toPre F ζ t₀ r → ∃ (θα₂ : Fam P.D.toPre F (1 * (g' * g))) (p₂ : QkPt P.D.toPre F (1 * (g' * g))) (w₂ : LB.Gen (LB.LinComb P.D.toPre.P.L (DegPre.lineφ P.D.toPre F p₂.g.b) (DegPre.lineε (1 * (g' * g))))) (ζ₂ : F) (x₂ : TFK (R := V) F ⟶ P.A.A) (r₀ r₂ : Fam P.D.toPre F (1 * (g' * g))), PullAl P.D F P.oD (a * a') 1 (g' * g) θ θα₂ ∧ P.ToA F (1 * (g' * g)) p₂ x₂ ∧ x₂ ≫ P.oA.act (star (a * a')) = 1 ∧ w₂.IsGen ∧ ζ₂ ≠ 0 ∧ FinOrd P.D F (1 * (g' * g)) p₂ w₂ ζ₂ ∧ PhiRel P.D.toPre F (1 * (g' * g)) p₂ w₂ θα₂ r₀ ∧ Fam.IsSmul P.D.toPre F ζ₂ r₀ r₂ ∧ HEq r r₂ := by
  intro hL _ _ _ V _ _ _ _ E _ _ _ H t P hT
  letI := H.starRing
  intro a a' g g' hg hg' hco haa haa' F _ _ _ θ θα hθ pb wb ζb xb tb₀ tb hxb hxba hwb hζb hfb hΦb hsb
    p w ζ x hw hζ hf hx hxa s₂ t₀ r hs₂ hΦ hr
  have hk : 1 ≤ 1 * g' := by omega
  have hkN : 1 ≤ 1 * g' * g := Nat.mul_pos hk hg
  obtain ⟨π, -, hπ⟩ := PullLin.exists_pull_linearMap hL V P.D F (𝓞 E) P.oD H.w0 P.w0 a g (1 * g') hg hk haa
  have key : ∃ (p₂ : QkPt P.D.toPre F (1 * g' * g))
      (w₂ : LB.Gen (LB.LinComb P.D.toPre.P.L (DegPre.lineφ P.D.toPre F p₂.g.b) (DegPre.lineε (1 * g' * g))))
      (ζ₂ : F) (x₂ : TFK (R := V) F ⟶ P.A.A) (r₀ : Fam P.D.toPre F (1 * g' * g)),
      P.ToA F (1 * g' * g) p₂ x₂ ∧ x₂ ≫ P.oA.act (star (a' * a)) = 1 ∧ w₂.IsGen ∧ ζ₂ ≠ 0 ∧
        FinOrd P.D F (1 * g' * g) p₂ w₂ ζ₂ ∧ PhiRel P.D.toPre F (1 * g' * g) p₂ w₂ (π θα) r₀ ∧
        Fam.IsSmul P.D.toPre F ζ₂ r₀ r := by
    by_cases h0 : θα = 0
    · obtain ⟨Φ, hΦ'⟩ := phiFun_of hL V _ P.D F (1 * g') hk pb wb hwb
      have e₀ : tb = 0 := by
        rw [(DVR.isSmul_iff _ _ _).1 hsb, (hΦ' _ _).1 hΦb, h0, map_zero, smul_zero]
      have e₁ : s₂ = π θα := by rw [(hπ _ _).1 hs₂, e₀, h0]
      refine ⟨p, w, ζ, x, t₀, hx, ?_, hw, hζ, hf, e₁ ▸ hΦ, hr⟩
      have := P.oA.hom (star a')
      rw [star_mul', P.oA.map_mul, ← Category.assoc, hxa, MonObj.one_comp]
    · obtain ⟨p₂, x₂, w₂, ζ₂, t₂, k₁, k₂, k₃, k₄, k₅⟩ := operator_on_pullback_eq_sum hL E H V t P hT a a' g g'
        hg hg' hco haa haa' F θα tb (π θα) s₂ t₀ r h0 ((hπ _ _).2 rfl) hs₂ 1 (fun _ => 1) (fun _ => pb)
        (fun _ => xb) (fun _ => wb) (fun _ => ζb) (fun _ => tb)
        ⟨fun _ => hxb, fun _ => hxba, fun _ => ⟨hwb, hζb, hfb⟩, fun _ => ⟨tb₀, hΦb, hsb⟩, by simp⟩
        p x w ζ hx hxa hw hζ hf hΦ hr
      obtain ⟨r₀, l₁, l₂⟩ := k₄ 0
      have e : r = t₂ 0 := by simpa using k₅
      exact ⟨p₂ 0, w₂ 0, ζ₂ 0, x₂ 0, r₀, k₁ 0, k₂ 0, (k₃ 0).1, (k₃ 0).2.1, (k₃ 0).2.2, l₁, e ▸ l₂⟩
  obtain ⟨p₂, w₂, ζ₂, x₂, r₀, k₁, k₂, k₃, k₄, k₅, k₆, k₇⟩ := key
  obtain ⟨θ', r₀', r', p', w', m₁, m₂, m₃, m₄, m₅, m₆, m₇⟩ :=
    transport_level P (Nat.mul_assoc 1 g' g) (π θα) r₀ r p₂ w₂ ζ₂ x₂ k₁ k₃ k₅ k₆ k₇
  have hc := pullAl_comp hL V P.D F (𝓞 E) P.oD H.w0 P.w0 a a' g g' 1 hg hg' le_rfl haa haa' θ θα (π θα) θ' hθ
    ((hπ _ _).2 rfl) m₁
  rw [_root_.mul_comm a' a] at hc k₂
  exact ⟨θ', p', w', ζ₂, x₂, r₀', r', hc, m₂, k₂, m₃, k₄, m₄, m₅, m₆, m₇⟩

end GlobalTheory
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.DescentIdFOfLaws

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

namespace GlobalTheory.PowDescent

theorem eq_famCast_of_heq {R : Type} [CommRing R] [IsDomain R] {Dp : DegPre R} {F : Type} [Field F]
    [Algebra (FractionRing R) F] {k k' : ℕ} (e : k = k') (r : Fam Dp F k') (s : Fam Dp F k) (h : HEq r s) :
    r = famCast e s := by
  subst e
  exact eq_of_heq h

theorem descent_cast (hL : Laws) (hL2 : Laws2) (hL4 : Laws4) (hT : TwistBaseChangeStatement)
    (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V]
    (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (t : SAB H (Sp V))
    (P : PELUnif (maximalIdeal V) t) (hP : P.TorsionIso) :
    letI := H.starRing
    ∀ (a a' : 𝓞 E) (g g' k : ℕ) (e : 1 * g' = k), 1 ≤ g → 1 ≤ g' → Nat.Coprime g g' →
      a * star a = (g : 𝓞 E) → a' * star a' = (g' : 𝓞 E) →
    ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] [IsAlgClosed F] (θ : Fam P.D.toPre F 1)
      (θα : Fam P.D.toPre F (1 * g')), PullAl P.D F P.oD a' 1 g' θ θα →
    ∀ (pb : QkPt P.D.toPre F (1 * g'))
      (wb : LB.Gen (LB.LinComb P.D.toPre.P.L (DegPre.lineφ P.D.toPre F pb.g.b) (DegPre.lineε (1 * g'))))
      (ζb : F) (xb : TFK (R := V) F ⟶ P.A.A) (tb₀ tb : Fam P.D.toPre F (1 * g')),
      P.ToA F (1 * g') pb xb → xb ≫ P.oA.act (star a') = 1 → wb.IsGen → ζb ≠ 0 →
      FinOrd P.D F (1 * g') pb wb ζb → PhiRel P.D.toPre F (1 * g') pb wb θα tb₀ →
      Fam.IsSmul P.D.toPre F ζb tb₀ tb →
    ∀ (p : QkPt P.D.toPre F (k * g))
      (w : LB.Gen (LB.LinComb P.D.toPre.P.L (DegPre.lineφ P.D.toPre F p.g.b) (DegPre.lineε (k * g))))
      (ζ : F) (x : TFK (R := V) F ⟶ P.A.A), w.IsGen → ζ ≠ 0 → FinOrd P.D F (k * g) p w ζ →
      P.ToA F (k * g) p x → x ≫ P.oA.act (star a) = 1 →
    ∀ (s₂ t₀ r : Fam P.D.toPre F (k * g)), PullAl P.D F P.oD a k g (famCast (Dp := P.D.toPre) (F := F) e tb) s₂ →
      PhiRel P.D.toPre F (k * g) p w s₂ t₀ → Fam.IsSmul P.D.toPre F ζ t₀ r →
    ∃ (θα₂ : Fam P.D.toPre F (1 * (g' * g))) (p₂ : QkPt P.D.toPre F (1 * (g' * g)))
      (w₂ : LB.Gen (LB.LinComb P.D.toPre.P.L (DegPre.lineφ P.D.toPre F p₂.g.b) (DegPre.lineε (1 * (g' * g)))))
      (ζ₂ : F) (x₂ : TFK (R := V) F ⟶ P.A.A) (r₀ r₂ : Fam P.D.toPre F (1 * (g' * g))),
      PullAl P.D F P.oD (a * a') 1 (g' * g) θ θα₂ ∧ P.ToA F (1 * (g' * g)) p₂ x₂ ∧
      x₂ ≫ P.oA.act (star (a * a')) = 1 ∧ w₂.IsGen ∧ ζ₂ ≠ 0 ∧ FinOrd P.D F (1 * (g' * g)) p₂ w₂ ζ₂ ∧
      PhiRel P.D.toPre F (1 * (g' * g)) p₂ w₂ θα₂ r₀ ∧ Fam.IsSmul P.D.toPre F ζ₂ r₀ r₂ ∧ HEq r r₂ := by
  letI := H.starRing
  intro a a' g g' k e
  subst e
  exact descent_one_generator hL hL2 hL4 hT V E H t P hP a a' g g'

theorem descentIdF_of_laws :
    Laws → Laws2 → Laws3 → Laws4 → Laws5 → TwistBaseChangeStatement → DescentIdF := by
  intro hL hL2 hL3 hL4 hL5 hT E _ _ _ H Dw l Xo c n
  letI := H.starRing
  intro T io y _ C P _ g g' hg hg' hne _ _ π π' hπ hπ' _ _ _ F _ _ _ _ _ _ v ϖ _ _ Q _ D' A' G' gr cm pD pA pG U' PU
    md oD' hx hoD oA' hoA θ θα hθ pb wb ζb xb tb₀ tb hxb hxba hwb hζb hfb hΦb hsb p w ζ x hw hζ hf hpx hxπ
    s₂ t₀ r hs₂ hΦ hr
  obtain ⟨oA'', hoA'', t', P', e₁, e₂, e₃, e₄, e₅, e₆, e₇, e₈, e₉⟩ :=
    exists_pelUnif_of_unifPow hL hL2 hL4 hT T.V E H C.I.G P n D' A' G' pD pA pG U' PU oD' hx hoD
  have hact : ∀ a, oA'.act a = oA''.act a := fun a =>
    Fan.IsLimit.hom_ext pA.lim _ _ fun i => (hoA a i).trans (hoA'' a i).symm
  have hxa : x ≫ oA''.act (star (star π)) = 1 := by
    refine Fan.IsLimit.hom_ext pA.lim _ _ fun i => ?_
    have := pA.hom i
    change (x ≫ oA''.act (star (star π))) ≫ pA.pr i = 1 ≫ pA.pr i
    rw [star_star, Category.assoc, hoA'', hxπ, MonObj.one_comp]
  have htors : P'.TorsionIso :=
    GlobalTheory.T.torsionIso_of_linear_uniformisation_triple ⟨hL, hL2, hL3, hL4, hL5⟩ (twistBCSpan_of hT) GlobalTheory.RatioVal.main
      (twisting_statements_of_laws hL hT).1 (GlobalTheory.UnitBallFree.main hL.globalFns hT) E H T.V (maximalIdeal T.V)
      ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩ t' P'
  rw [hact] at hxba
  simp only [hact]
  clear hoA hact hoA'' hxπ hx hoD PU pD pA pG
  subst e₁ e₄ e₇
  cases e₂
  cases e₃
  cases e₅
  cases e₆
  cases e₈
  cases e₉
  obtain ⟨θα₂, p₂, w₂, ζ₂, x₂, r₀, r₂, k₁, k₂, k₃, k₄, k₅, k₆, k₇, k₈, k₉⟩ :=
    descent_cast hL hL2 hL4 hT T.V E H t' P' htors (star π) (star π') g g' g' (one_mul g') hg.one_le hg'.one_le
      ((Nat.coprime_primes hg hg').2 hne) (by rw [star_star, _root_.mul_comm, hπ])
      (by rw [star_star, _root_.mul_comm, hπ']) F θ θα hθ pb wb ζb xb tb₀ tb hxb hxba hwb hζb hfb hΦb hsb
      p w ζ x hw hζ hf hpx hxa s₂ t₀ r hs₂ hΦ hr
  exact ⟨θα₂, p₂, w₂, ζ₂, x₂, r₀, r₂, k₁, k₂, k₃, k₄, k₅, k₆, k₇, k₈, eq_famCast_of_heq _ _ _ k₉⟩

end GlobalTheory.PowDescent
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsUnitOfPrimeNe

section

@[expose] public section

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory.GeneratorsAtPoint

theorem isUnit_of_prime_ne {V : Type} [CommRing V] [IsLocalRing V] {g g' : ℕ} (hg : g.Prime) (hg' : g'.Prime)
    (hne : g ≠ g') (hn : ¬ IsUnit ((g : ℕ) : V)) : IsUnit ((g' : ℕ) : V) := by
  have hz : IsCoprime (g : ℤ) (g' : ℤ) := Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hg hg').2 hne)
  obtain ⟨a, b, hab⟩ : IsCoprime ((g : ℕ) : V) ((g' : ℕ) : V) := by
    simpa using hz.map (Int.castRingHom V)
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one hab with h₁ | h₁
  · exact absurd (isUnit_of_mul_isUnit_right h₁) hn
  · exact isUnit_of_mul_isUnit_right h₁

section Cast
variable {R : Type} [CommRing R] [IsDomain R] {Dp : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem famCast_symm {k k' : ℕ} (e : k = k') (s : Fam Dp F k') : famCast e (famCast e.symm s) = s := by
  subst e; rfl

theorem famCast_sum {k k' : ℕ} (e : k = k') {m : ℕ} (a : Fin m → F) (b : Fin m → Fam Dp F k) :
    famCast e (∑ i, a i • b i) = ∑ i, a i • famCast e (b i) := by
  subst e; rfl

end Cast

theorem nuGe_famCast {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    {Dd : DegData V (maximalIdeal V)} {Q : Dd.toPre.X → ℤ} {K : Type} [Field K] [Algebra (FractionRing V) K]
    {v : AddValuation K (WithTop ℚ)} {k k' : ℕ} (e : k = k') {s : Fam Dd.toPre K k} {r : ℚ}
    (h : NuGe Dd Q K v k s r) : NuGe Dd Q K v k' (famCast e s) r := by
  subst e; exact h

theorem unitBall_spanned (hL : Laws) (hT : TwistBaseChangeStatement)
    (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] (D' : DegData V (maximalIdeal V)) (A' : PolAV (Spec (CommRingCat.of (FractionRing V))))
    (G' : Over (Sp V)) [gr : GrpObj G'] [cm : IsCommMonObj G'] (U' : Unif (maximalIdeal V) D' A' G')
    [md : Module (𝓞 E) D'.toPre.X] :
    letI := H.starRing
    ∀ (oD' : D'.toPre.OAct (𝓞 E)) (oA' : A'.OAct (𝓞 E)) (t' : SAB H (Sp V)) (P' : PELUnif (maximalIdeal V) t'),
      P'.TorsionIso → t'.G = G' → HEq t'.grp gr → HEq t'.comm cm → P'.D = D' → HEq P'.mod md → HEq P'.oD oD' →
      P'.A = A' → HEq P'.oA oA' → HEq P'.U U' →
    ∀ (α : 𝓞 E) (N : ℕ), 1 ≤ N → α * star α = (N : 𝓞 E) → (∃ u u' : 𝓞 E, u * α + u' * star α = 1) →
      IsUnit ((N : ℕ) : V) →
    ∀ (ϖ : V), Irreducible ϖ → ∀ (Q : D'.toPre.X → ℤ), IsQ D'.toPre ϖ Q →
    ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)),
      ValOver ϖ F v →
    ∀ (Dw : Datum H) (_I : TateIso Dw F (TFK (R := V) F ⟶ A'.A) (fun a g => g ≫ oA'.act a)
        (fun n g g' c => WeilIs A'.A A'.L n g g' (unitOn c))),
    ∀ θ : Fam D'.toPre F 1, NuGe D' Q F v 1 θ 0 → ThFrame D' ϖ F θ →
    ∀ θα : Fam D'.toPre F (1 * N), PullAl D' F oD' α 1 N θ θα →
    ∀ s : Fam D'.toPre F (1 * N), NuGe D' Q F v (1 * N) s 0 →
      ∃ (m : ℕ) (p : Fin m → QkPt D'.toPre F (1 * N)) (x : Fin m → (TFK (R := V) F ⟶ A'.A))
        (w : ∀ i, LB.Gen (LB.LinComb D'.toPre.P.L (DegPre.lineφ D'.toPre F (p i).g.b) (DegPre.lineε (1 * N))))
        (ζ : Fin m → F) (t : Fin m → Fam D'.toPre F (1 * N)) (a : Fin m → F),
        (∀ i, QkToAkU U'.toUnifPre F (1 * N) (p i) (x i)) ∧
        (∀ i, x i ≫ oA'.act (star α) = 1) ∧
        (∀ i, (w i).IsGen ∧ ζ i ≠ 0 ∧ FinOrd D' F (1 * N) (p i) (w i) (ζ i)) ∧
        (∀ i, ∃ t' : Fam D'.toPre F (1 * N),
          PhiRel D'.toPre F (1 * N) (p i) (w i) θα t' ∧ Fam.IsSmul D'.toPre F (ζ i) t' (t i)) ∧
        (∀ i, (0 : WithTop ℚ) ≤ v (a i)) ∧
        s = ∑ i, a i • t i := by
  let _ := H.starRing
  intro oD' oA' t' P' hP e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉
  subst e₁ e₄ e₇
  cases e₂
  cases e₃
  cases e₅
  cases e₆
  cases e₈
  cases e₉
  exact ReciprocityTheory.ChartRestriction.G.H1.cmLiftCondition_of_laws hL n1c (GlobalTheory.twisting_statements_of_laws hL hT).1
    (GlobalTheory.UnitBallFree.main hL.globalFns hT) E H V t' P' hP

theorem main : Laws → Laws2 → Laws3 → Laws4 → Laws5 → TwistBaseChangeStatement → GenPointT := by
  intro hL hL2 hL3 hL4 hL5 hT E _ _ _ H Dw l Xo c
  let _ := H.starRing
  intro T io y C hTr P hP hy ϖ hϖ Q hQ g g' hg hg' hne hgo hg'o π π' hπ hπ' hcop hcop' hgnu F _ _ _ _ _ _ v hv I n
    D' A' G' _ _ pD pA pG U' PU _ oD' hx hact s s₂ p w ζ x t₀ t σ' h hbox
  obtain ⟨hs, hs₂, ⟨hw, hζ, hfo⟩, hqx, hxk, hphi, hsm, hexp, hgerm⟩ := hbox
  have hq : 1 ≤ g' * g := Nat.mul_pos hg'.pos hg.pos
  have hπb : star π * star (star π) = (g : 𝓞 E) := by rw [star_star, _root_.mul_comm]; exact hπ
  have hπb' : star π' * star (star π') = (g' : 𝓞 E) := by rw [star_star, _root_.mul_comm]; exact hπ'
  have hw0 : TraceFormTwistIso D'.toPre oD' H.w0 := GlobalTheory.PsiWZeroProd.main T.V n P.D.toPre D'.toPre pD (𝓞 E)
    (fun a x => funext fun i => hx a x i) P.oD oD' hact H.w0 P.w0
  obtain ⟨pl, -, hpl⟩ := PullLin.exists_pull_linearMap hL T.V D' F (𝓞 E) oD' H.w0 hw0 (star π) g g' hg.pos hg'.pos hπb
  obtain ⟨pl₂, -, hpl₂⟩ := PullLin.exists_pull_linearMap hL T.V D' F (𝓞 E) oD' H.w0 hw0 (star π * star π') (g' * g) 1 hq
    le_rfl (by rw [star_mul', Nat.cast_mul, ← hπb, ← hπb']; ring)
  obtain ⟨Φ, hΦ⟩ := phiFun_of hL T.V _ D' F (g' * g) hq p w hw
  obtain ⟨τ, hτ, hτT, hiff⟩ := frameNSt_holds E H T.V C.I.G P _ C.FT C.actT C.ph1T C.ph2T C.syT C.adT C.tgT C.xT C.eT
    C.wPT C.chartT C.frameT C.primT n D' A' G' pD pA pG U' PU
  have hz := GlobalTheory.T.universalJets_power_product T.V C.I.G.G G' n _ pG C.xT (GlobalTheory.T.universal_statement E H Dw l Xo c T io y C)
  obtain ⟨gm, hgm, hgmex⟩ := PairingLinear.exists_germ_linearMap hL hL2 hL4 hT T.V D' A' G' U' _ _ hz τ hτ (hτT hTr) F
    (g' * g) hq
  obtain ⟨θ, θα, hθν, hθF, hθα⟩ := PowThetaFrame.main hL hL2 hL4 hT E H Dw l Xo c n T io y hy C P hP g g' hg hg' hne hgo
    hg'o π π' hπ hπ' hcop hcop' hgnu F v ϖ hϖ hv Q hQ D' A' G' pD pA pG U' PU oD' hx hact
  obtain ⟨oA', hoA, hQ', ⟨Dw', ⟨I'⟩⟩, t', P', hP', e₁, e₂, e₃, e₄, e₅, e₆, e₇, e₈, e₉⟩ :=
    powPEL_of_laws hL hL2 hL3 hL4 hL5 hT E H Dw l Xo c n T io y hy C P hP g g' hg hg' hne hgo
      hg'o π π' hπ hπ' hcop hcop' hgnu F v ϖ hϖ hv I Q hQ D' A' G' pD pA pG U' PU oD' hx hact
  have hcopb : ∃ u u' : 𝓞 E, u * star π' + u' * star (star π') = 1 := by
    obtain ⟨u, u', hu⟩ := hcop'
    exact ⟨u', u, by rw [star_star, ← hu]; ring⟩
  obtain ⟨m, pb, xb, wb, ζb, tb, a, hpx, hxb, hwb, htb, ha, hsum⟩ :=
    unitBall_spanned hL hT E H T.V D' A' G' U' oD' oA' t' P' hP' e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ (star π') g' hg'.pos hπb' hcopb
      (isUnit_of_prime_ne hg hg' hne hgnu) ϖ hϖ _ hQ' F v hv Dw' I' θ hθν hθF θα hθα
      (famCast (Dp := D'.toPre) (F := F) (one_mul g').symm s) (nuGe_famCast _ hs)
  have hs' : s = ∑ i, a i • famCast (Dp := D'.toPre) (F := F) (one_mul g') (tb i) := by
    rw [← famCast_sum, ← hsum, famCast_symm]
  let Λ : Fam D'.toPre F g' →ₗ[F] Fam D'.toPre F (g' * g) := (ζ • Φ) ∘ₗ pl
  refine ⟨θ, pl₂ θ, m, a, fun i => gm (Λ (famCast (Dp := D'.toPre) (F := F) (one_mul g') (tb i))), hθν, hθF,
    (hpl₂ _ _).2 rfl, ha, ?_, fun i => ?_⟩
  · have ht : t = Λ s := by
      rw [(DVR.isSmul_iff _ _ _).1 hsm, (hΦ _ _).1 hphi, (hpl _ _).1 hs₂]
      rfl

    rw [hgm t σ' h hexp ((hiff F _ σ' h).1 hgerm), ht, hs', map_sum, map_sum]
    simp only [map_smul]
  · obtain ⟨tb₀, h₁, h₂⟩ := htb i
    obtain ⟨θα₂, p₂, w₂, ζ₂, x₂, r₀, r₂, k₁, k₂, k₃, k₄, k₅, k₆, k₇, k₈, k₉⟩ :=
      PowDescent.descentIdF_of_laws hL hL2 hL3 hL4 hL5 hT E H Dw l Xo c n T io y hy C P hP g g' hg hg' hne hgo
        hg'o π π' hπ hπ' hcop hcop' hgnu F v ϖ hϖ hv Q hQ D' A' G' pD pA pG U' PU oD' hx hact oA' hoA θ θα hθα
        (pb i) (wb i) (ζb i) (xb i) tb₀ (tb i) (hpx i) (hxb i) (hwb i).1 (hwb i).2.1 (hwb i).2.2 h₁ h₂
        p w ζ x hw hζ hfo hqx hxk _ _ (Λ (famCast (Dp := D'.toPre) (F := F) (one_mul g') (tb i)))
        ((hpl _ _).2 rfl) ((hΦ _ _).2 rfl) ((DVR.isSmul_iff _ _ _).2 rfl)
    obtain ⟨σ₂, j₁, j₂⟩ := hgmex (Λ (famCast (Dp := D'.toPre) (F := F) (one_mul g') (tb i)))
    refine ⟨p₂, w₂, ζ₂, x₂, r₀, r₂, σ₂, k₂, fun b => ?_, k₄, k₅, k₆, (hpl₂ _ _).1 k₁ ▸ k₇, k₈, k₉ ▸ j₁,
      (hiff F _ σ₂ _).2 j₂⟩
    have := pA.hom b
    rw [← hoA, ← Category.assoc, k₃, MonObj.one_comp]

end GlobalTheory.GeneratorsAtPoint
end
end
end
