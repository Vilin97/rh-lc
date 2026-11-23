module

public import Development.AbelianVarietyTheory.BlockTheory.JetGauges.ThetaSpanAdjoint
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.IsHermForm
public import Formalism.LocalToGlobal.IndefiniteReal.ThPinsR
public import Formalism.LocalToGlobal.ProjectiveLattices.FullExists
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ShortThetaValueExistsUniqueNaturalOfLaws
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.HarmonicGermValueChartIndependentStatement
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.HostFieldGaloisDegreeDiscrConjMovesPrimes
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ShortRuleChangeOfCongr
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.TotalDegreeLeOfRowDeg
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FixesDatumOfCongAt
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.PushforwardPreservesHarmonicPolynomialsAndLattic
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IntMIffInt
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaValueWeightTriangularFrame
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CmHostIdempotentTraceEqOne
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsAnFibAllPoints
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.PushforwardPreservesHarmonicPolynomialsAndLattic
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RatioMemRange
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ReflexNormMulConj
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.RingTheory.WittVector.IsPoly
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
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Formalism.LocalToGlobal.Columns.AdelicLemmas
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon

-- Source module: Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaChangeOfRepRootOfUnityOfChartIndependence

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict GlobalTheory.Phase GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence

namespace GlobalTheory

theorem changeRoot_scalar_isMu (t b b' D : ℂ) (A A' m : ℕ) (hb' : b' ≠ 0) (hA : A ≠ 0) (hm : 0 < m)
    (h1 : (b ^ 2 * (A' : ℂ)) ^ m = (b' ^ 2 * (A : ℂ) * D) ^ m) (h2 : IsMu (t ^ 2 * D)) :
    IsMu (t * b * ((Real.sqrt (A' : ℝ) : ℝ) : ℂ) / (b' * ((Real.sqrt (A : ℝ) : ℝ) : ℂ))) := by
  obtain ⟨k, hk, h2⟩ := h2
  have e : ∀ B : ℕ, ((Real.sqrt (B : ℝ) : ℝ) : ℂ) ^ 2 = (B : ℂ) := fun B => by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg B)]; simp
  have hA' : (A : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hA
  refine ⟨2 * m * k, by positivity, ?_⟩
  have e2 : (t * b * ((Real.sqrt (A' : ℝ) : ℝ) : ℂ) / (b' * ((Real.sqrt (A : ℝ) : ℝ) : ℂ))) ^ 2 =
      t ^ 2 * (b ^ 2 * (A' : ℂ)) / (b' ^ 2 * (A : ℂ)) := by
    rw [div_pow, mul_pow, mul_pow, mul_pow, e, e, _root_.mul_assoc]
  have hne : (b' ^ 2 * (A : ℂ)) ^ m ≠ 0 := pow_ne_zero _ (mul_ne_zero (pow_ne_zero _ hb') hA')
  have e3 : (t ^ 2 * (b ^ 2 * (A' : ℂ)) / (b' ^ 2 * (A : ℂ))) ^ m = (t ^ 2 * D) ^ m := by
    rw [div_pow, mul_pow (t ^ 2), h1, mul_pow _ D, div_eq_iff hne, mul_pow (t ^ 2) D]; ring
  rw [pow_mul, pow_mul, e2, e3, ← pow_mul, mul_comm m k, pow_mul, h2, one_pow]

theorem changeRoot_complex (hC : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2) (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ]
    [StarRing (𝓞 E)] (nab : NabV Xo c) (hnab : IsNab Xo c nab) (n : ℕ) (hn : Even n)
    (hfib : ∃ (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r)
      (e : Fin g ≃ Lt1 Dw) (hr : X.p0 + Dw.p = r) (eL : LtN Dw n ≃ Harm.Var X.Ψ Dw.p X.p0 (Fin n)),
      IsSympl X bas ∧ r = Dw.p + Dw.q ∧
      (∀ ℓ, letterDir X hr idx (eL ℓ) = Pi.single ℓ.2.2 (Pi.single (e.symm ⟨ℓ.1, ℓ.2.1⟩) 1)) ∧
      (∀ j, rowType X (idx j) = Formalism.L2.PjFree.relab c (algebraMap c.F ℂ) (e j).1) ∧
      ∀ y : FrPt Xo c ℂ, ∃ (y₀ : FrPt Xo c ℂ) (t : Ix Dw → ℂˣ) (x : Frame X.Ψ r) (L : Lt E r),
        FrBor t y₀ y ∧ x ∈ X.dom ∧ SelfD X L ∧ Nonempty (AnFib X bas idx e x L y₀))
    (Λ : GenLat E n) (h : Matrix (Fin n) (Fin n) E) (b b' : c.F) (hU : Λ.Unimod) (hh : IsUnitaryM h)
    (hT : Λ.TrivAt l.M) (hT' : (actLat h Λ).TrivAt l.M) (hb : IsBeta Dw c Λ b) (hb' : IsBeta Dw c (actLat h Λ) b') :
    ∃ z : ℂ, IsMu z ∧ ∀ (w : (Fin n → LevQ Dw l) → c.F), FixesDatum c h w →
      ∀ N N' : ℕ, Λ.LevOK N l.M → (actLat h Λ).LevOK N' l.M → ∀ (a : (E →+* ℂ) × ℕ → ℕ),
      ∀ P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)),
      ∀ (y : FrPt Xo c ℂ) (v v' : ℂ), ShortValAt Xo c nab w Λ b N P y v →
        ShortValAt Xo c nab w (actLat h Λ) b' N' (pushLet c h P) y v' → v' = z * v := by
  obtain ⟨r, g, X, bas, idx, e, hr, eL, hS, hr', hL, hrow, hy⟩ := hfib
  by_cases hne : Nonempty (FrPt Xo c ℂ)
  swap
  · exact ⟨1, isMu_one, fun _ _ _ _ _ _ _ _ _ y => (hne ⟨y⟩).elim⟩
  obtain ⟨y1⟩ := hne
  have hLaws : Out.Laws := GlobalTheory.firstFiveLaws.1
  obtain ⟨t, -, ht⟩ := GlobalTheory.Phase.ChangePt.change_at_point hC E H Dw l Xo c r g X bas idx e Dw.p n hr eL hS hr' hn hL hrow nab hnab
    Λ h hU hh hT hT'
  obtain ⟨m, hm, hbeta⟩ := GlobalTheory.BetaChange.beta_sq_compare E H Dw l c n Λ h b b' hU hh hb hb'
  obtain ⟨hP, hΛ⟩ : _ ∧ _ := ⟨fun a => (GlobalTheory.PushKeeps.push_keeps E H Dw l c n a h hh).1,
    ((GlobalTheory.PushKeeps.push_keeps E H Dw l c n 0 h hh).2 Λ).1 hU⟩
  set A := ((Λ).Ln.toAddSubgroup.addSubgroupOf (Λ).La.toAddSubgroup).index ^ (Dw.p + Dw.q) with hAdef
  set A' := ((actLat h Λ).Ln.toAddSubgroup.addSubgroupOf (actLat h Λ).La.toAddSubgroup).index ^ (Dw.p + Dw.q)
    with hA'def
  have hb0 : algebraMap c.F ℂ b ≠ 0 := (map_ne_zero _).2 hb.1
  have hb0' : algebraMap c.F ℂ b' ≠ 0 := (map_ne_zero _).2 hb'.1
  have hA : A ≠ 0 := by
    intro h0
    have h1 := hb.2.2 (algebraMap c.F ℂ)
    rw [← Nat.cast_pow, ← hAdef, h0, Nat.cast_zero, pow_eq_zero_iff two_ne_zero, norm_eq_zero] at h1
    exact hb0 h1
  have hsq : ((Real.sqrt (A : ℝ) : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]
    exact (Real.sqrt_pos.2 (Nat.cast_pos.2 (Nat.pos_of_ne_zero hA))).ne'
  obtain ⟨y₀, t₀, x, L, -, hx, hSD, ⟨F⟩⟩ := hy y1
  have hmu := (ht x L y₀ F hx hSD).1
  have hbeta' := congrArg (algebraMap c.F ℂ) hbeta
  simp only [map_pow, map_mul, map_natCast, map_prod] at hbeta'
  refine ⟨_, changeRoot_scalar_isMu t _ _ _ A A' m hb0' hA hm hbeta' hmu, ?_⟩
  intro w hw N N' hN hN' a P hPa y v v' hv hv'
  obtain ⟨y₀, t₀, x, L, hB, hx, hSD, ⟨F⟩⟩ := hy y
  have ex1 := (GlobalTheory.shortThetaValue_existsUnique_natural hLaws hC E H Dw l Xo c nab hnab n Λ N hU hT hN a P hPa w b).1 ℂ
  have ex2 := (GlobalTheory.shortThetaValue_existsUnique_natural hLaws hC E H Dw l Xo c nab hnab n (actLat h Λ) N' hΛ hT' hN' a _ (hP a P hPa) w b').1 ℂ
  obtain ⟨u, hu, -⟩ := ex1 y₀
  obtain ⟨u', hu', -⟩ := ex2 y₀
  have k1 := (ex1 y).unique hv
    ((GlobalTheory.thetaValue_weight hLaws hC E H Dw l Xo c nab hnab ℂ y₀ y t₀ hB n a P).2 hPa w Λ b N u hu)
  have k2 := (ex2 y).unique hv'
    ((GlobalTheory.thetaValue_weight hLaws hC E H Dw l Xo c nab hnab ℂ y₀ y t₀ hB n a _).2 (hP a P hPa) w _ b' N' u' hu')
  have k3 := (ht x L y₀ F hx hSD).2 w hw N N' hN hN' a P hPa b b' u u' hb.1 hb'.1 hu hu'
  have k4 : u' = t * algebraMap c.F ℂ b * ((Real.sqrt (A' : ℝ) : ℝ) : ℂ) /
      (algebraMap c.F ℂ b' * ((Real.sqrt (A : ℝ) : ℝ) : ℂ)) * u := by
    rw [div_mul_eq_mul_div, eq_div_iff (mul_ne_zero hb0' hsq), ← _root_.mul_assoc]
    exact k3
  rw [k1, k2, k4]; ring

theorem changeRoot_of_chartIndep : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (nab : NabV Xo c) (n : ℕ), ChangeRoot Xo c nab n := by
  intro hC E _ _ _ H Dw l Xo c _ nab n hs bad hbad Λ h b b' hU hh hT hT' hb hb'
  obtain ⟨-, hodd, hn, hnab⟩ := hs
  have hLaws : Out.Laws := GlobalTheory.firstFiveLaws.1
  have triv : ∀ Λ : GenLat E n, Λ.TrivAt bad → Λ.TrivAt l.M := fun Λ ⟨k, hk, h1⟩ =>
    ⟨k, hk.coprime_dvd_right hbad.2.2.1, h1⟩
  have hT := triv _ hT
  have hT' := triv _ hT'
  obtain ⟨s, hfib⟩ := GlobalTheory.Dict.exists_anFib_all_points E H Dw l Xo c hodd.pos n hn
  obtain ⟨z, hz, hid⟩ := @changeRoot_complex hC E _ _ _ H Dw l Xo c s.toAlgebra _ nab hnab n hn hfib
    Λ h b b' hU hh hT hT' hb hb'
  have hP := fun a => (GlobalTheory.PushKeeps.push_keeps E H Dw l c n a h hh).1
  have hΛ := ((GlobalTheory.PushKeeps.push_keeps E H Dw l c n 0 h hh).2 Λ).1 hU
  let J : Type := {p : ((Fin n → LevQ Dw l) → c.F) × ℕ × ℕ × ((E →+* ℂ) × ℕ → ℕ) × MvPolynomial (LtN Dw n) c.F //
    FixesDatum c h p.1 ∧ Λ.LevOK p.2.1 l.M ∧ (actLat h Λ).LevOK p.2.2.1 l.M ∧
      p.2.2.2.2 ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => p.2.2.2.1 (τ, i))}
  have ex1 := fun j : J => GlobalTheory.shortThetaValue_existsUnique_natural hLaws hC E H Dw l Xo c nab hnab n Λ j.1.2.1 hU hT j.2.2.1 j.1.2.2.2.1
    j.1.2.2.2.2 j.2.2.2.2 j.1.1 b
  have ex2 := fun j : J => GlobalTheory.shortThetaValue_existsUnique_natural hLaws hC E H Dw l Xo c nab hnab n (actLat h Λ) j.1.2.2.1 hΛ hT' j.2.2.2.1
    j.1.2.2.2.1 _ (hP _ _ j.2.2.2.2) j.1.1 b'
  choose u hu using fun (j : J) (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) => ((ex1 j).1 S y).exists
  choose u' hu' using fun (j : J) (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) => ((ex2 j).1 S y).exists
  obtain ⟨z₀, hz₀, hfin⟩ := GlobalTheory.ConstRatio.exists_ratio E H Dw l Xo c s J u u'
    (fun j S T _ _ _ _ φ y y' hy => (ex1 j).2 S T φ y y' hy _ _ (hu j S y) (hu j T y'))
    (fun j S T _ _ _ _ φ y y' hy => (ex2 j).2 S T φ y y' hy _ _ (hu' j S y) (hu' j T y')) z hz
    (fun j y => hid j.1.1 j.2.1 _ _ j.2.2.1 j.2.2.2.1 _ _ j.2.2.2.2 y _ _
      (@hu j ℂ _ s.toAlgebra y) (@hu' j ℂ _ s.toAlgebra y))
  refine ⟨z₀, hz₀, ?_⟩
  intro w hw N N' hN hN' a P hPa S _ _ y v v' hv hv'
  let j : J := ⟨(w, N, N', a, P), hw, hN, hN', hPa.1⟩
  rw [((ex1 j).1 S y).unique hv (hu j S y), ((ex2 j).1 S y).unique hv' (hu' j S y)]
  exact hfin j S y

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaChangeOfRepRootOfUnityOfChartIndependenceStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict GlobalTheory.Phase GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence

theorem _root_.GlobalTheory.T.thetaChangeOfRepRootOfUnity_of_chartIndependence : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (nab : NabV Xo c) (n : ℕ), ChangeRoot Xo c nab n := by
  first | exact @GlobalTheory.changeRoot_of_chartIndep | exact GlobalTheory.changeRoot_of_chartIndep | (intros; apply GlobalTheory.changeRoot_of_chartIndep <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShortRuleChangeMat

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false


namespace GlobalTheory.OrbitAdapt

open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence GlobalTheory.ShortMove

theorem shortRule_change_mat (D : D7) (T : Full D) (hF : LawsFull T) (j : ℕ) (hj : InR D j) (n : ℕ)
    (Λ : GenLat D.host.E n) (g : Matrix (Fin n) (Fin n) D.host.E) (b : ℕ) (a : (D.host.E →+* ℂ) × ℕ → ℕ)
    (P : MvPolynomial (LtN (T.Q.Dw j) n) T.Q.c.F) (hg : IsUnitaryM g) (hb : (T.dδ j n).l₂.M ∣ b)
    (hcg : GlobalTheory.UnRep.CongAt (stdLat D.host.E n) b b g)
    (hev : Even n) (hU : Λ.Unimod) (hU' : (actLat g Λ).Unimod) (hT : Λ.TrivAt (badN D))
    (hT' : (actLat g Λ).TrivAt (badN D)) (hM : Λ.TrivAt (T.dδ j n).l₂.M) (hM' : (actLat g Λ).TrivAt (T.dδ j n).l₂.M)
    (hP : P ∈ harmL T.Q.c Λ a) :
    ∃ (P' : MvPolynomial (LtN (T.Q.Dw j) n) T.Q.c.F) (ζ : T.Q.c.F), P' ∈ harmL T.Q.c (actLat g Λ) a ∧ ζ ≠ 0 ∧
      (∃ m : ℕ, 0 < m ∧ ζ ^ m = 1) ∧
      ∀ (x0 : Fin n → (T.Q.Dw j).La) (N N' : ℕ) (f : Rul (T.Q.Xo j) T.Q.c),
        Λ.LevOK N (T.dδ j n).l₂.M → (actLat g Λ).LevOK N' (T.dδ j n).l₂.M →
        IsShortRule (T.Q.Xo j) T.Q.c (T.dδ j n) Λ N x0 P f →
        IsShortRule (T.Q.Xo j) T.Q.c (T.dδ j n) (actLat g Λ) N' x0 P' (ζ • f) := by
  set d := T.dδ j n with hd
  obtain ⟨_, hnab⟩ := hF.sh.dNab j hj n
  have hCI := GlobalTheory.T.harmonic_germ_value_chart_independent
  have hbad := GlobalTheory.ShortChange.badOK_host D T.Q.H d.l₂
  have hdv : D.host.QS * D.host.q * D.host.d ∣ badN D := Dvd.intro _ rfl
  have hb1 : D.host.QS * D.host.q * D.host.d * d.l₂.M ≠ 1 := fun h => by
    have := hbad.2.1
    omega
  have hB := GlobalTheory.ShortChange.trivAt_mul (trivAt_of_dvd hdv hT) hM
  have hB' := GlobalTheory.ShortChange.trivAt_mul (trivAt_of_dvd hdv hT') hM'
  have hK := hF.p.kPsi j hj
  obtain ⟨ze, ⟨k, hk, hze⟩, hrep⟩ := GlobalTheory.T.thetaChangeOfRepRootOfUnity_of_chartIndependence hCI D.host.E T.Q.H (T.Q.Dw j) d.l₂ d.Xo₂ d.c₂ d.nab₂ n
    ⟨(GlobalTheory.PlaceInt.host_galois_discr_moves D T.Q.H).1, GlobalTheory.ShortChange.odd_rank T hF j hj, hev, hnab⟩ _ hbad
    Λ g _ _ hU hg hB hB' (isBeta_cover d hK hb1 Λ hU hB) (isBeta_cover d hK hb1 _ hU' hB')
  have hP' := ((GlobalTheory.PushKeeps.push_keeps D.host.E T.Q.H (T.Q.Dw j) T.Q.l T.Q.c n a g hg).2 Λ).2.2.2 P hP
  have hz : d.eF.symm ze ^ k = 1 := by rw [← map_pow, hze, map_one]
  refine ⟨pushLet T.Q.c g P, d.eF.symm ze, hP', fun h0 => ?_, ⟨k, hk, hz⟩,
    fun x0 N N' f hN hN' hR K _ _ _ _ hKe y y₂ hy => ?_⟩
  · rw [h0, zero_pow hk.ne'] at hz
    exact zero_ne_one hz
  obtain ⟨v, hv, hval⟩ := hR K hKe y y₂ hy
  have h₂ := (((GlobalTheory.PlaceInt.eF_transfer D.host.E T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c n d Λ).2.1 a P hP).1)
  have h₂' := (((GlobalTheory.PlaceInt.eF_transfer D.host.E T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c n d _).2.1 a _ hP').1)
  obtain ⟨v', hv', -⟩ := (GlobalTheory.shortThetaValue_existsUnique_natural GlobalTheory.firstFiveLaws.1 hCI D.host.E T.Q.H (T.Q.Dw j)
    d.l₂ d.Xo₂ d.c₂ d.nab₂ hnab n _ N' hU' hM' hN' a _ h₂'.1 (d.w x0)
    (d.eF (betaH (Dw := T.Q.Dw j) T.Q.c (actLat g Λ)))).1 K y₂
  refine ⟨v', hv', ?_⟩
  rw [map_pushLet] at hv'
  have hvv := hrep (d.w x0) (fixesDatum_of_congAt d.c₂ hb hcg _) N N' hN hN' a _ h₂ K y₂ v v' hv hv'
  have hs : evR (T.Q.Xo j) T.Q.c (d.eF.symm ze • f) y =
      algebraMap T.Q.c.F K (d.eF.symm ze) * evR (T.Q.Xo j) T.Q.c f y :=
    evR_mul (T.Q.Xo j) T.Q.c _ f _ (fun p y => Algebra.smul_def _ _) y
  rw [hs, hval, hvv, ← hKe, AlgEquiv.apply_symm_apply]
  ring

theorem congAt_of_cols {E : Type} [Field E] [NumberField E] {n : ℕ} (gm : Matrix (Fin n) (Fin n) E) (m : ℕ)
    (h : ∀ j : Fin n, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence.CongAt m (fun i => gm i j)
      fun i => (((1 : Matrix (Fin n) (Fin n) (𝓞 E)) i j : 𝓞 E) : E)) :
    GlobalTheory.UnRep.CongAt (stdLat E n) m m gm := by
  choose k hk b hb using h
  refine ⟨∏ j, k j, Nat.Coprime.prod_left fun j _ => hk j, fun v hv => ?_⟩
  have hv' : ∀ i, ∃ y : 𝓞 E, (y : E) = v i := fun i => by
    have := (Submodule.mem_pi.1 hv) i (Set.mem_univ _)
    obtain ⟨y, hy⟩ := Submodule.mem_one.1 this
    exact ⟨y, hy⟩
  choose y hy using hv'
  refine ⟨fun i => ((∑ j, ((∏ l ∈ Finset.univ.erase j, k l : ℕ) : 𝓞 E) * b j i * y j : 𝓞 E) : E), ?_, ?_⟩
  · refine Submodule.mem_pi.2 fun i _ => Submodule.mem_one.2 ⟨_, rfl⟩
  · funext i
    have e1 : ∀ j, ((∏ l, k l : ℕ) : E) * (gm i j - (((1 : Matrix (Fin n) (Fin n) (𝓞 E)) i j : 𝓞 E) : E)) =
        ((∏ l ∈ Finset.univ.erase j, k l : ℕ) : E) * ((m : E) * (b j i : E)) := fun j => by
      have hp : (∏ l, k l) = k j * ∏ l ∈ Finset.univ.erase j, k l :=
        (Finset.mul_prod_erase (s := Finset.univ) (f := k) (Finset.mem_univ j)).symm
      rw [hp]
      push_cast
      have h' := hb j i
      simp only at h'
      linear_combination (∏ l ∈ Finset.univ.erase j, ((k l : ℕ) : E)) * h'
    have e2 : (gm.mulVec v - v) i = ∑ j, (gm i j - (((1 : Matrix (Fin n) (Fin n) (𝓞 E)) i j : 𝓞 E) : E)) * v j := by
      simp only [Pi.sub_apply, Matrix.mulVec, dotProduct, sub_mul, Finset.sum_sub_distrib]
      congr 1
      simp [Matrix.one_apply]
    simp only [Pi.smul_apply, nsmul_eq_mul, e2]
    push_cast
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hy j]
    have h' := e1 j
    push_cast at h'
    linear_combination ((y j : 𝓞 E) : E) * h'

theorem plc_prime {K : Type} [Field K] [NumberField K] (lam : HeightOneSpectrum (𝓞 K)) : (Formalism.EigenvalueLevelCeiling.plc lam).Prime := by
  unfold Formalism.EigenvalueLevelCeiling.plc
  haveI : lam.asIdeal.IsPrime := lam.isPrime
  have hne : Ideal.absNorm lam.asIdeal ≠ 0 := fun h => lam.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  have hz : ((Ideal.absNorm lam.asIdeal : ℕ) : 𝓞 K ⧸ lam.asIdeal) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk lam.asIdeal), Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.absNorm_mem _
  have hd : ringChar (𝓞 K ⧸ lam.asIdeal) ∣ Ideal.absNorm lam.asIdeal :=
    (ringChar.spec (𝓞 K ⧸ lam.asIdeal) _).1 hz
  rcases CharP.char_is_prime_or_zero (𝓞 K ⧸ lam.asIdeal) (ringChar (𝓞 K ⧸ lam.asIdeal)) with h | h
  · exact h
  · rw [h, zero_dvd_iff] at hd
    exact absurd hd hne



attribute [local instance] Formalism.BasicNotions.Host.cmStar in
theorem star_mem_one (D : D7) {x : D.host.E} (hx : x ∈ (1 : Submodule (𝓞 D.host.E) D.host.E)) :
    star x ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := by
  obtain ⟨y, rfl⟩ := Submodule.mem_one.1 hx
  exact Submodule.mem_one.2 ⟨⟨star (algebraMap _ _ y),
    (RingOfIntegers.isIntegral_coe y).map (starRingEnd D.host.E).toIntAlgHom⟩, rfl⟩


attribute [local instance] Formalism.BasicNotions.Host.cmStar in
theorem zero_case (D : D7) (V : Formalism.BasicNotions.TH.HSp D) (hL : Formalism.IndefR.Bridge.hLat V 1 = stdLat D.host.E V.rank)
    (Λ : GenLat D.host.E V.rank) (hT : Λ.TrivAt 0) :
    (∀ w, w ∈ Λ.La ↔ (fun b => star (w b)) ∈ Formalism.IndefR.Bridge.hLat V (Formalism.IndefR.FWT.fin V 1)) ∧
      (∀ b, Formalism.IndefR.FWT.SplitOffBad V b 1) ∧ ∀ m, Λ.TrivAt m := by
  obtain ⟨k, hk, h1, h2⟩ := hT
  obtain rfl : k = 1 := (Nat.coprime_zero_right k).1 hk
  simp only [Nat.cast_one, Ideal.span_singleton_one, Submodule.top_smul] at h1 h2
  have hΛ : Λ.La = stdLat D.host.E V.rank := le_antisymm h1 h2
  refine ⟨fun w => ?_, fun b => ?_, fun m => ⟨1, Nat.coprime_one_left m, by simpa using h1, by simpa using h2⟩⟩
  · have hf : Formalism.IndefR.FWT.fin V (1 : Formalism.L2.Theta.GA D V) = 1 := map_one _
    rw [hf, hL, hΛ]
    constructor
    · intro hw
      exact Submodule.mem_pi.2 fun i _ => star_mem_one D ((Submodule.mem_pi.1 hw) i (Set.mem_univ _))
    · intro hw
      refine Submodule.mem_pi.2 fun i _ => ?_
      have := star_mem_one D ((Submodule.mem_pi.1 hw) i (Set.mem_univ _))
      simpa only [star_star] using this
  · refine ⟨one_mem _, 0, ∅, ⟨⟨fun _ => 0, by simp, by simp⟩, by simp⟩, by simp, fun a c => ?_⟩
    have : Formalism.L2.Theta.mt V (1 : Formalism.L2.Theta.GA D V) = 1 := by simp [Formalism.L2.Theta.mt]
    simp [this]

end GlobalTheory.OrbitAdapt
end
end
