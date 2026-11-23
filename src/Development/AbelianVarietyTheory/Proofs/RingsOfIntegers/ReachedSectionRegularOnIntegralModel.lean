module

public import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsThetaGrpPullback
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsTwistPullBaseChange
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsAlgClosedValuedFieldOverCompleteDVR
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValuationMultiplicationInvariance
public import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ThetaFrameExpansionFramedPointGeneratorStatement
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFramedPointBaseChangeAlgebraMap
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.BOfNsmulLeft
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NormalisedPullbackSectionExpandsFamilyStatement
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsUniqueCompatibleSectionExpansionIntegralFrStatement
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.TwistingStatementsOfLaws
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TwistedPrincipalPolarisationSectionsBaseChange
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullFEInst
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SectionRegularOnModelOfNuNonnegStatement
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsMulEquivUniformisedPointsUniversal
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SymmetricLiftActsRootOfUnityOnExpansionsStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ConstBFMul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.ClosedPointWeilPower
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.PhiPow
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.PullSec
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SpanEqTopOfFunctionals

-- Source module: Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.GeneratorSectionExpansionNuNonneg

section

@[expose] public section

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm
namespace GlobalTheory.GeneratorNu

theorem nuGe_of_thFrame {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V} (hϖ : Irreducible ϖ)
    (D : DegData V (maximalIdeal V)) (Q : D.toPre.X → ℤ) (hQ : IsQ D.toPre ϖ Q) (F : Type) [Field F]
    [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)) (hv : ValOver ϖ F v) (θ : Fam D.toPre F 1)
    (hθ : GlobalTheory.PowGerm.ThFrame D ϖ F θ) : NuGe D Q F v 1 θ 0 := by
  obtain ⟨g, gF, hg, he, -⟩ := hθ
  refine (n1a V ϖ hϖ D Q hQ F v hv 1 le_rfl {0} (fun χ => ⟨0, Finset.mem_singleton_self _, χ, by simp⟩) θ 0).2 ?_
  intro α hα
  rw [Finset.mem_singleton] at hα
  subst hα
  refine ⟨1, fun _ => 1, fun _ => g, fun _ => gF, fun _ => hg, fun _ => ?_, fun j => ?_⟩
  · rw [QForm.Q_zero hϖ D hQ]; simp
  · simp [DegPre.constBF, he j]

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (I : IntData Xo c T io y.1) (P : PELUnif (maximalIdeal T.V) I.G), P.TorsionIso → ∀ (ϖ : T.V), Irreducible ϖ → ∀ (Q : P.D.toPre.X → ℤ), IsQ P.D.toPre ϖ Q → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra T.Fr F] [Algebra T.V F] [IsScalarTower T.V T.Fr F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v → ∀ (xF : Sp F ⟶ Xo.X) (h : ptO Xo xF ⟶ ptO Xo (xOf y)), h.left = spMap (algebraMap T.Fr F) → ∀ hh : SecN Xo xF 1, IsPullSec Xo.univ.t.G Xo.univ.t.PP.L ((1 : ℕ) : ℤ) (h ▷ Xo.univ.t.G) (whiskerRight_snd _ _) (sOf1 y) hh → (∀ σ s, SecTieF I P F xF 1 σ hh → P.U.toUnifPre.ExpandsG F 1 σ s → NuGe P.D Q F v 1 s 0) := by
  intro E _ _ _ H Dw l Xo c T io y I P _ ϖ hϖ Q hQ F _ _ _ _ _ v hv xF h hl hh hpull σ s htie hexp
  letI := io.toAlgebra
  letI : Algebra c.F F := ((algebraMap T.Fr F).comp io).toAlgebra
  let φ : T.Fr →ₐ[c.F] F := { algebraMap T.Fr F with commutes' := fun _ => rfl }
  obtain ⟨z, hz⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c _ _ φ y.1
  have hx : xF = z.x := by
    have := Over.w h
    rw [hl] at this
    exact this.symm.trans hz.1.symm
  subst hx
  have hs : ∀ j, hh.f j = z.s.f j := by
    obtain ⟨-, -, pm, h1, h2, h3⟩ := hz
    have e : pm = (h ▷ Xo.univ.t.G).left := by
      apply pullback.hom_ext
      · refine h2.trans ?_
        have := congrArg Over.Hom.left (whiskerRight_fst h Xo.univ.t.G)
        rw [Over.comp_left, Over.comp_left, hl] at this
        exact this.symm
      · refine h1.trans ?_
        have := congrArg Over.Hom.left (whiskerRight_snd h Xo.univ.t.G)
        rw [Over.comp_left] at this
        exact this.symm
    subst e
    intro j
    exact (hpull j).trans (h3 j _)
  have hs' : hh = z.s := by
    cases hh
    rcases hzs : z.s with ⟨f, hf⟩
    rw [hzs] at hs
    congr
    exact funext hs
  subst hs'
  exact nuGe_of_thFrame hϖ P.D Q hQ F v hv s (GlobalTheory.T.thetaFrame_expansion_framedPoint_generator E H Dw l Xo c T io y.1 I P ϖ hϖ F φ rfl z hz σ s htie hexp)

end GlobalTheory.GeneratorNu
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.GeneratorSectionExpansionNuNonnegStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm

theorem _root_.GlobalTheory.T.generator_section_expansion_nu_nonneg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (I : IntData Xo c T io y.1) (P : PELUnif (maximalIdeal T.V) I.G), P.TorsionIso → ∀ (ϖ : T.V), Irreducible ϖ → ∀ (Q : P.D.toPre.X → ℤ), IsQ P.D.toPre ϖ Q → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra T.Fr F] [Algebra T.V F] [IsScalarTower T.V T.Fr F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v → ∀ (xF : Sp F ⟶ Xo.X) (h : ptO Xo xF ⟶ ptO Xo (xOf y)), h.left = spMap (algebraMap T.Fr F) → ∀ hh : SecN Xo xF 1, IsPullSec Xo.univ.t.G Xo.univ.t.PP.L ((1 : ℕ) : ℤ) (h ▷ Xo.univ.t.G) (whiskerRight_snd _ _) (sOf1 y) hh → (∀ σ s, SecTieF I P F xF 1 σ hh → P.U.toUnifPre.ExpandsG F 1 σ s → NuGe P.D Q F v 1 s 0) := by
  first | exact @GlobalTheory.GeneratorNu.main | exact GlobalTheory.GeneratorNu.main | (intros; apply GlobalTheory.GeneratorNu.main <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.NormalisedPullbackSectionNuNonneg

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm

namespace GlobalTheory.NuPull

theorem nuGe_zero_of_pulls : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (I : IntData Xo c T io y.1) (P : PELUnif (maximalIdeal T.V) I.G), P.TorsionIso → ∀ (ϖ : T.V), Irreducible ϖ → ∀ (Q : P.D.toPre.X → ℤ), IsQ P.D.toPre ϖ Q → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra T.Fr F] [Algebra T.V F] [IsScalarTower T.V T.Fr F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v → ∀ (xF : Sp F ⟶ Xo.X) (h : ptO Xo xF ⟶ ptO Xo (xOf y)), h.left = spMap (algebraMap T.Fr F) → ∀ (k N k' : ℕ) (a : 𝓞 E) (hh : SecN Xo xF k) (hh' : SecN Xo xF k'), (k = 1 ∨ 4 ≤ k) → 0 < N → a * H.bar a = (N : 𝓞 E) → k' = k * N → Pulls Xo a hh hh' → (∀ σ s, SecTieF I P F xF k σ hh → P.U.toUnifPre.ExpandsG F k σ s → NuGe P.D Q F v k s 0) → (∀ σ s, SecTieF I P F xF k' σ hh' → P.U.toUnifPre.ExpandsG F k' σ s → NuGe P.D Q F v k' s 0) := by
  intro E _ _ _ H Dw l Xo c T io y I P hT ϖ hϖ Q hQ F _ _ _ _ _ v hv xF h hl k N k' a hh hh' hk hN ha e hP h0 σ' s' ht' hs'
  letI := H.starRing
  subst e
  have hL : Laws := GlobalTheory.firstFiveLaws.1
  have hk₁ : 1 ≤ k := by omega
  have ha' : a * star a = (N : 𝓞 E) := ha
  have hex := GlobalTheory.T.existsUnique_compatibleSection_expansion_integralFramedPoint E H Dw l Xo c T io y I P hT ϖ hϖ Q hQ F v hv xF h hl
  obtain ⟨⟨σ, hσ, -⟩, hu⟩ := hex k hk₁ hh
  obtain ⟨s, hs, -⟩ := hu σ hσ
  obtain ⟨uΨ, huΨ, -, -⟩ := P.w0
  have hLB : P.D.toPre.P.L.IsLB := P.D.toPre.P.isLB
  obtain ⟨s'', hs''⟩ := exists_pullAl P.D F hLB P.oD H.w0 uΨ huΨ a N ha' hN k s
    (pullSecs_fe' P.D F hL.globalFns hLB P.oD H.w0 P.w0 uΨ huΨ a N ha' hN k s)
  have hE := GlobalTheory.T.normalisedPullback_section_expands_family E H Dw l Xo c T io y.1 I P F xF hσ.1 a N k (k * N) rfl ha' hN hk σ hh s σ' hh' s''
    hσ hs hP ht' hs''
  obtain rfl : s' = s'' := ((hex (k * N) (Nat.mul_pos hk₁ hN) hh').2 σ' ht').unique hs' hE
  exact (GlobalTheory.twisting_statements_of_laws hL GlobalTheory.twistBaseChange).2.2 T.V ϖ hϖ P.D Q hQ F v hv (𝓞 E) P.oD H.w0 P.w0
    a N hN ha' (by rw [_root_.mul_comm]; exact ha') k hk₁ s s' hs'' 0 (h0 σ s hσ hs)

end GlobalTheory.NuPull
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.NormalisedPullbackSectionNuNonnegStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm

theorem _root_.GlobalTheory.T.normalised_pullback_section_nu_nonneg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (I : IntData Xo c T io y.1) (P : PELUnif (maximalIdeal T.V) I.G), P.TorsionIso → ∀ (ϖ : T.V), Irreducible ϖ → ∀ (Q : P.D.toPre.X → ℤ), IsQ P.D.toPre ϖ Q → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra T.Fr F] [Algebra T.V F] [IsScalarTower T.V T.Fr F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v → ∀ (xF : Sp F ⟶ Xo.X) (h : ptO Xo xF ⟶ ptO Xo (xOf y)), h.left = spMap (algebraMap T.Fr F) → ∀ (k N k' : ℕ) (a : 𝓞 E) (hh : SecN Xo xF k) (hh' : SecN Xo xF k'), (k = 1 ∨ 4 ≤ k) → 0 < N → a * H.bar a = (N : 𝓞 E) → k' = k * N → Pulls Xo a hh hh' → (∀ σ s, SecTieF I P F xF k σ hh → P.U.toUnifPre.ExpandsG F k σ s → NuGe P.D Q F v k s 0) → (∀ σ s, SecTieF I P F xF k' σ hh' → P.U.toUnifPre.ExpandsG F k' σ s → NuGe P.D Q F v k' s 0) := by
  first | exact @GlobalTheory.NuPull.nuGe_zero_of_pulls | exact GlobalTheory.NuPull.nuGe_zero_of_pulls | (intros; apply GlobalTheory.NuPull.nuGe_zero_of_pulls <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SymmetricTorsionTranslateSectionNuNonneg

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm

namespace GlobalTheory.PlaceInt

theorem zero_le_val_of_pow_eq_one {F : Type} [Field F] (v : AddValuation F (WithTop ℚ)) {u : F} {m : ℕ} (hm : 0 < m)
    (hu : u ^ m = 1) : ((0 : ℚ) : WithTop ℚ) ≤ v u := by
  have h : m • v u = 0 := by rw [← v.map_pow, hu, v.map_one]
  cases hc : v u with
  | top => exact le_top
  | coe q =>
    rw [hc, ← WithTop.coe_nsmul, WithTop.coe_eq_zero, smul_eq_zero] at h
    rcases h with h | h
    · omega
    · rw [h]

theorem nuGe_zero_of_moves : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (I : IntData Xo c T io y.1) (P : PELUnif (maximalIdeal T.V) I.G), P.TorsionIso → ∀ (ϖ : T.V), Irreducible ϖ → ∀ (Q : P.D.toPre.X → ℤ), IsQ P.D.toPre ϖ Q → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra T.Fr F] [Algebra T.V F] [IsScalarTower T.V T.Fr F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v → ∀ (xF : Sp F ⟶ Xo.X) (h : ptO Xo xF ⟶ ptO Xo (xOf y)), h.left = spMap (algebraMap T.Fr F) → ∀ (k : ℕ) (b : ptO Xo xF ⟶ Xo.univ.t.G) (hh hh' : SecN Xo xF k), 1 ≤ k → Moves Xo b hh hh' → (∀ σ s, SecTieF I P F xF k σ hh → P.U.toUnifPre.ExpandsG F k σ s → NuGe P.D Q F v k s 0) → (∀ σ s, SecTieF I P F xF k σ hh' → P.U.toUnifPre.ExpandsG F k σ s → NuGe P.D Q F v k s 0) := by
  intro E _ _ _ H Dw l Xo c T io y I P hT ϖ hϖ Q hQ F _ _ _ _ _ v hv xF h hl k b hh hh' hk hmv hν σ' s' hσ' hs'
  have hL : Laws := GlobalTheory.firstFiveLaws.1
  have h3 : FiniteOrderValuationInvariance := (GlobalTheory.twisting_statements_of_laws hL GlobalTheory.twistBaseChange).2.1
  have hx := hσ'.base
  obtain ⟨⟨σ, hσ, -⟩, hex⟩ := GlobalTheory.T.existsUnique_compatibleSection_expansion_integralFramedPoint E H Dw l Xo c T io y I P hT ϖ hϖ Q hQ F v hv xF h hl k hk hh
  obtain ⟨s, hs, -⟩ := hex σ hσ
  obtain ⟨s₁, -, hu'⟩ := (GlobalTheory.T.existsUnique_compatibleSection_expansion_integralFramedPoint E H Dw l Xo c T io y I P hT ϖ hϖ Q hQ F v hv xF h hl k hk hh').2 σ' hσ'
  obtain ⟨e, he, -⟩ := GlobalTheory.PtTie.exists_mulEquiv_ptTieF E H Dw l Xo c T io y.1 I P F xF hx
  have hxk : (e.symm b) ^ k = 1 := by rw [← map_pow, hmv.1, map_one]
  obtain ⟨f, hf, hsurj, -⟩ := hT F k hk
  obtain ⟨p, hp⟩ := hsurj _ hxk
  obtain ⟨w, hw⟩ : ∃ w : LB.Gen (LB.LinComb P.D.toPre.P.L (DegPre.lineφ P.D.toPre F p.g.b) (DegPre.lineε k)), w.IsGen :=
    ReciprocityTheory.ChartRestriction.G.H1.ClosedPointWeilPower.gen_local_linComb P.D.toPre.P.L P.D.toPre.P.isLB _ _
  obtain ⟨ζ, hζ, hfin⟩ := ReciprocityTheory.ChartRestriction.G.H1.finOrdExists_of_laws hL T.V P.D F k hk p w hw
  obtain ⟨Φ, hΦ⟩ := phiFun_of hL T.V (maximalIdeal T.V) P.D F k hk p w hw
  have h1 : PhiRel P.D.toPre F k p w s (Φ s) := (hΦ _ _).2 rfl
  have h2 : Fam.IsSmul P.D.toPre F ζ (Φ s) (ζ • Φ s) := (ReciprocityTheory.ChartRestriction.G.DVR.isSmul_iff _ _ _).2 rfl
  obtain ⟨u, t', ⟨m, hm, hum⟩, hut, ht'⟩ := GlobalTheory.T.symmetric_lift_acts_root_of_unity_on_expansions E H Dw l Xo c T io y.1 I P F xF hx k hk σ σ' hh hh' s (Φ s) (ζ • Φ s)
    (e.symm b) b p w ζ hσ hσ' hs hmv ((he _ _).2 (e.apply_symm_apply b).symm) ((hf _ _).2 hp.symm) hw hfin h1 h2
  have h4 := (h3 T.V ϖ hϖ P.D Q hQ F v hv k hk p w hw ζ hζ hfin s _ _ h1 h2 0).1 (hν σ s hσ hs)
  have h5 := NuGe.smul Q (zero_le_val_of_pow_eq_one v hm hum) hut h4
  rw [add_zero] at h5
  rw [hu' s' hs', ← hu' t' ht']
  exact h5

end GlobalTheory.PlaceInt
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SymmetricTorsionTranslateSectionNuNonnegStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm

theorem _root_.GlobalTheory.T.symmetric_torsion_translate_section_nu_nonneg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (I : IntData Xo c T io y.1) (P : PELUnif (maximalIdeal T.V) I.G), P.TorsionIso → ∀ (ϖ : T.V), Irreducible ϖ → ∀ (Q : P.D.toPre.X → ℤ), IsQ P.D.toPre ϖ Q → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra T.Fr F] [Algebra T.V F] [IsScalarTower T.V T.Fr F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v → ∀ (xF : Sp F ⟶ Xo.X) (h : ptO Xo xF ⟶ ptO Xo (xOf y)), h.left = spMap (algebraMap T.Fr F) → ∀ (k : ℕ) (b : ptO Xo xF ⟶ Xo.univ.t.G) (hh hh' : SecN Xo xF k), 1 ≤ k → Moves Xo b hh hh' → (∀ σ s, SecTieF I P F xF k σ hh → P.U.toUnifPre.ExpandsG F k σ s → NuGe P.D Q F v k s 0) → (∀ σ s, SecTieF I P F xF k σ hh' → P.U.toUnifPre.ExpandsG F k σ s → NuGe P.D Q F v k s 0) := by
  first | exact @GlobalTheory.PlaceInt.nuGe_zero_of_moves | exact GlobalTheory.PlaceInt.nuGe_zero_of_moves | (intros; apply GlobalTheory.PlaceInt.nuGe_zero_of_moves <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ReachedSectionRegularOnIntegralModel

section

@[expose] public section

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm
open ReciprocityTheory.ChartRestriction.G.PullbackSections (endT exists_isPullSec)

namespace GlobalTheory.ReachRegular

section BC
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] (L : RigLB A) {T T' : Over S} (h : T' ⟶ T)

theorem isNormPull_baseChange (φ : A ⟶ A) (a b : ℤ) {s : LB.Sec (LPow A L.L b T)} {t : LB.Sec (LPow A L.L a T)}
    {s' : LB.Sec (LPow A L.L b T')} {t' : LB.Sec (LPow A L.L a T')} (H : IsNormPull A L φ a b s t)
    (hs : IsPullSec A L.L b (h ▷ A) (whiskerRight_snd _ _) s s')
    (ht : IsPullSec A L.L a (h ▷ A) (whiskerRight_snd _ _) t t') : IsNormPull A L φ a b s' t' := by
  have hL := L.isLB
  obtain ⟨α₀, α, h0, hn, hc, htw⟩ := H
  have key : ∀ U : Over S, ∃ β : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(snd U A).left, (snd U A ≫ φ).left] ![a, -b]),
      β.IsGen ∧ LB.Gen.Corr L.L _ _ _ _ β (LB.pullGen L.L _ _ α₀ (snd U A).left) := fun U => by
    obtain ⟨α, hα, hv⟩ := exists_gen hL (φ' := ![(snd U A).left, (snd U A ≫ φ).left]) (ε' := ![a, -b])
      (fun U _ f => by
        refine Finset.prod_congr rfl fun i _ => ?_
        fin_cases i
        · exact congrArg (fun q => f q ^ a) (Category.comp_id _)
        · rfl)
      (LB.pullGen L.L ![𝟙 A.left, φ.left] ![a, -b] α₀ (snd U A).left)
      (DVR.pullGen_isGen _ _ _ _ h0 _)
    exact ⟨α, hα, corr_of_val hL fun y J hJ => hv _ _ y J hJ⟩
  obtain ⟨α', hα', hc'⟩ := key T'
  refine ⟨α₀, α', h0, hn, hc', ?_⟩
  have e : endT A T' φ ≫ h ▷ A = h ▷ A ≫ endT A T φ := by ext1 <;> simp [endT]
  obtain rfl := GlobalTheory.TwistBaseChange.eq_pullS_of_isPullSec A b h hs
  obtain rfl := GlobalTheory.TwistBaseChange.eq_pullS_of_isPullSec A a h ht
  refine GlobalTheory.VVRank.isTwistPull_of_sv A hL hα' fun y J hJ => ?_
  have v : val α' (𝟙 _) y J = val α (𝟙 _ ≫ (h ▷ A).left) y J := by
    rw [val_corr hJ hc', val_pull hJ, val_corr hJ hc, val_pull hJ, Category.assoc _ (h ▷ A).left,
      ← Over.comp_left, whiskerRight_snd]
  rw [GlobalTheory.VVRank.sv_pullS A a h t _ y hJ, GlobalTheory.VVRank.sv_pullS A b h s _ y hJ, v,
    GlobalTheory.VVRank.sv_of_isTwistPull A htw _ y hJ, Category.assoc, Category.assoc, ← Over.comp_left,
    ← Over.comp_left, e]

theorem isSymAct_baseChange (N : ℕ) (b : T ⟶ A) {s t : LB.Sec (LPow A L.L (N : ℤ) T)}
    {s' t' : LB.Sec (LPow A L.L (N : ℤ) T')} (H : IsSymAct A L N b s t)
    (hs : IsPullSec A L.L N (h ▷ A) (whiskerRight_snd _ _) s s')
    (ht : IsPullSec A L.L N (h ▷ A) (whiskerRight_snd _ _) t t') : IsSymAct A L N (h ≫ b) s' t' := by
  obtain ⟨hb, U, hU, hact⟩ := H
  obtain ⟨U', -, -, h1, h2⟩ := GlobalTheory.ThetaPullback.exists_thetaGrp_pullback S A L.L L.isLB N T T' h U
  exact ⟨by rw [← MonObj.comp_pow, hb, MonObj.comp_one], U', h1 _ _ hU, h2 _ _ _ _ hact hs ht⟩
end BC



theorem regular_of_reach : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), Good3 C → ∀ (k : ℕ) (F : SecN Xo (xOf y) k), Reach Xo (sOf1 y) k F → Regular C k F := by
  intro E _ _ _ H Dw l Xo c _ _ T io y C hC k F₀ hR
  obtain ⟨-, P, hP⟩ := hC
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible T.V
  have hQ : ∃ Q : P.D.toPre.X → ℤ, IsQ P.D.toPre ϖ Q := by
    choose Q hQ using exists_QVal hϖ P.D
    exact ⟨Q, hQ⟩
  obtain ⟨Q, hQ⟩ := hQ
  have hch : CharZero T.Fr := charZero_of_injective_ringHom io.injective
  obtain ⟨F, _, _, _, _, _, _, v, hv, -⟩ := GlobalTheory.ClosedValuedField.exists_field_over_cdvr T ϖ hϖ hch
  let xF : Sp F ⟶ Xo.X := spMap (algebraMap T.Fr F) ≫ xOf y
  let h : ptO Xo xF ⟶ ptO Xo (xOf y) := Over.homMk (spMap (algebraMap T.Fr F)) rfl
  have hh : h.left = spMap (algebraMap T.Fr F) := rfl
  have main : 1 ≤ k ∧ ∀ G : SecN Xo xF k,
      IsPullSec Xo.univ.t.G Xo.univ.t.PP.L ((k : ℕ) : ℤ) (h ▷ Xo.univ.t.G) (whiskerRight_snd _ _) F₀ G →
      ∀ σ s, SecTieF C.I P F xF k σ G → P.U.toUnifPre.ExpandsG F k σ s → NuGe P.D Q F v k s 0 := by
    induction hR with
    | base => exact ⟨le_rfl, GlobalTheory.T.generator_section_expansion_nu_nonneg E H Dw l Xo c T io y C.I P hP ϖ hϖ Q hQ F v hv xF h hh⟩
    | pull k N k' a F₁ F₂ _ hk hN ha hk' hp ih =>
      refine ⟨hk' ▸ Nat.mul_pos ih.1 hN.pos, fun G hG => ?_⟩
      obtain ⟨G₁, hG₁⟩ := exists_isPullSec Xo.univ.t.G Xo.univ.t.PP.L (k : ℤ) (h ▷ Xo.univ.t.G) (whiskerRight_snd _ _) F₁
      exact GlobalTheory.T.normalised_pullback_section_nu_nonneg E H Dw l Xo c T io y C.I P hP ϖ hϖ Q hQ F v hv xF h hh k N k' a G₁ G hk hN.pos ha hk'
        (isNormPull_baseChange _ h _ _ _ hp hG₁ hG) (ih.2 G₁ hG₁)
    | move k b F₁ F₂ _ hm ih =>
      refine ⟨ih.1, fun G hG => ?_⟩
      obtain ⟨G₁, hG₁⟩ := exists_isPullSec Xo.univ.t.G Xo.univ.t.PP.L (k : ℤ) (h ▷ Xo.univ.t.G) (whiskerRight_snd _ _) F₁
      exact GlobalTheory.T.symmetric_torsion_translate_section_nu_nonneg E H Dw l Xo c T io y C.I P hP ϖ hϖ Q hQ F v hv xF h hh k (h ≫ b) G₁ G ih.1
        (isSymAct_baseChange _ h _ b hm hG₁ hG) (ih.2 G₁ hG₁)
  obtain ⟨G, hG⟩ := exists_isPullSec Xo.univ.t.G Xo.univ.t.PP.L (k : ℤ) (h ▷ Xo.univ.t.G) (whiskerRight_snd _ _) F₀
  exact GlobalTheory.T.section_regular_on_model_of_nu_nonneg E H Dw l Xo c T io y C.I P hP ϖ hϖ Q hQ F v hv xF h hh k F₀ G main.1 hG (main.2 G hG)

end GlobalTheory.ReachRegular
end
end
end
