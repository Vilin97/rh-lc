module

public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.EvaluationLawsGenericFramesAtlasHold
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.NaturalRuleValueBaseChangeOfIsReduced
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FrameChangeComposeInvertBaseChangeTriangularStatement
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FrameChangeExistsUniqueInvertibleStatement
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FramedPointEvalNaturalWeightScaling
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.FinitePlaceArcs.BeSumStatement
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.Divisibility.WeightAlgebra
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LowerTriIsUnitDet
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ScaledBaseChangeFibreSectionCalculus
import Formalism.LocalToGlobal.ProjectiveLattices.IntAllProofFree
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.FibrePushforward
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.KerScheme
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsPointedOfIsHkIsog
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsCan

-- Source module: Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.EvRBaseChangeOfFromTest

section

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions

namespace GlobalTheory.ArcQ

section General

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem evR_frBor_of_isReduced (hL : GlobalTheory.Reg.EvLaws Xo c) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ}
    {F : Rul Xo c} (hF : F ∈ sec Xo c a n) {S : Type} [CommRing S] [Algebra c.F S] [IsReduced S]
    (t : Ix Dw → Sˣ) (y y' : FrPt Xo c S) (h : FrBor t y y') :
    evR Xo c F y' = wchar (ex Dw a n) t * evR Xo c F y := by
  rw [← sub_eq_zero]
  apply IsReduced.eq_zero
  rw [nilpotent_iff_mem_prime]
  intro P hP
  let φ : S →ₐ[c.F] S ⧸ P := Ideal.Quotient.mkₐ c.F P
  obtain ⟨z, hz⟩ := hL.bc _ _ φ y
  obtain ⟨z', hz'⟩ := hL.bc _ _ φ y'
  obtain ⟨g, hg1, hg2, hg⟩ := ((GlobalTheory.T.frameChange_compose_invert_baseChange_triangular E H Dw l Xo c S).2.2.2 t y y').1 h
  have hc := ((GlobalTheory.T.frameChange_compose_invert_baseChange_triangular E H Dw l Xo c S).2.2.1 _ φ g _ y y' z z' hg hz).1 hz'
  let t' : Ix Dw → (S ⧸ P)ˣ := fun i => Units.map (φ : S →* S ⧸ P) (t i)
  have hb : FrBor t' z z' :=
    ((GlobalTheory.T.frameChange_compose_invert_baseChange_triangular E H Dw l Xo c (S ⧸ P)).2.2.2 t' z z').2
      ⟨fun τ => (g τ).map φ, fun τ i => by simp [t', hg1], fun τ i j hij => by simp [hg2 τ i j hij], hc⟩
  have hw := evR_frBor_of_isDomain hL hF t' z z' hb
  rw [GlobalTheory.Reg.evR_baseChange_of_isReduced E H Dw l Xo c hL a n F hF S _ φ y z hz,
    GlobalTheory.Reg.evR_baseChange_of_isReduced E H Dw l Xo c hL a n F hF S _ φ y' z' hz'] at hw
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  change φ _ = 0
  rw [map_sub, hw, map_mul, sub_eq_zero]
  congr 1
  simp [wchar, t']

theorem evR_scale_of_isReduced (hL : GlobalTheory.Reg.EvLaws Xo c) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ}
    {F : Rul Xo c} (hF : F ∈ sec Xo c a n) {A T : Type} [CommRing A] [Algebra c.F A] [IsReduced A]
    [CommRing T] [Algebra c.F T] (φ : A →ₐ[c.F] T) (g : Tˣ) (y : FrPt Xo c A) (z z' : FrPt Xo c T)
    (hm : FrMap φ y z) (hb : FrBor (fun i => i.elim g fun _ => 1) z z') :
    evR Xo c F z' = (g : T) ^ n * φ (evR Xo c F y) := by
  classical
  obtain ⟨G, hG1, hG2, hG⟩ := ((GlobalTheory.T.frameChange_compose_invert_baseChange_triangular E H Dw l Xo c T).2.2.2 _ z z').1 hb
  let ι := Option (Σ τ : E →+* ℂ, Fin (Dw.mult τ) × Fin (Dw.mult τ))
  let R := MvPolynomial ι A
  let B := Localization.Away (MvPolynomial.X none : R)
  let v : ι → T := fun i => i.elim (g : T) fun x => G x.1 x.2.1 x.2.2
  let k₀ : R →ₐ[c.F] T := MvPolynomial.aevalTower φ v
  have hk₀ : IsUnit (k₀ (MvPolynomial.X none)) := by simp [k₀, v, R]
  let k : B →ₐ[c.F] T := IsLocalization.liftAlgHom (M := Submonoid.powers (MvPolynomial.X none : R)) (f := k₀)
    (by rintro ⟨_, m, rfl⟩; simpa only [map_pow] using hk₀.pow m)
  have hk : ∀ r : R, k (algebraMap R B r) = k₀ r := fun r => IsLocalization.lift_eq _ r
  let π : A →ₐ[c.F] B := IsScalarTower.toAlgHom c.F A B
  have hπ : k.comp π = φ := by
    ext x
    change k (algebraMap A B x) = φ x
    rw [IsScalarTower.algebraMap_apply A R B, hk]
    simp [k₀, R]
  have hu : IsUnit (algebraMap R B (MvPolynomial.X none)) := IsLocalization.Away.algebraMap_isUnit _
  let M : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) B := fun τ => Matrix.of fun i j =>
    if i = j then 1 else if i < j then 0 else algebraMap R B (MvPolynomial.X (some ⟨τ, i, j⟩))
  have hM1 : ∀ τ i, M τ i i = 1 := fun τ i => by simp [M]
  have hM2 : ∀ τ i j, i < j → M τ i j = 0 := fun τ i j hij => by simp [M, hij, hij.ne]
  have hMk : ∀ τ, (M τ).map k = G τ := fun τ => by
    ext i j
    by_cases h1 : i = j
    · subst h1; simp [hM1, hG1]
    · by_cases h2 : i < j
      · simp [hM2 τ i j h2, hG2 τ i j h2]
      · simp only [M, Matrix.map_apply, Matrix.of_apply, if_neg h1, if_neg h2, hk]
        simp [k₀, v, R]
  have hdet : ∀ τ, IsUnit (M τ).det := fun τ => by
    rw [Matrix.det_of_isLowerTriangular (M τ) (fun i j hij => hM2 τ i j hij)]
    simp [hM1]
  obtain ⟨u₀, hu₀⟩ := hL.bc _ _ π y
  obtain ⟨u, hchg⟩ := (GlobalTheory.T.frameChange_exists_unique_invertible E H Dw l Xo c B M _ u₀).1 hdet hu
  have h0 : FrMap k u₀ z := frMap_cancel (Xo := Xo) (c := c) _ _ _ π k y u₀ z hu₀ (by rw [hπ]; exact hm)
  have h1 : FrMap k u z' := by
    refine ((GlobalTheory.T.frameChange_compose_invert_baseChange_triangular E H Dw l Xo c B).2.2.1 _ k M _ u₀ u z z' hchg h0).2 ?_
    have e : k (algebraMap R B (MvPolynomial.X none)) = (g : T) := by rw [hk]; simp [k₀, v, R]
    rw [e, show (fun τ => (M τ).map k) = G from funext hMk]
    exact hG
  let t : Ix Dw → Bˣ := fun i => i.elim hu.unit fun _ => 1
  have hbu : FrBor t u₀ u :=
    ((GlobalTheory.T.frameChange_compose_invert_baseChange_triangular E H Dw l Xo c B).2.2.2 t u₀ u).2 ⟨M, fun τ i => by simp [t, hM1], hM2, hchg⟩
  rw [GlobalTheory.Reg.evR_baseChange_of_isReduced E H Dw l Xo c hL a n F hF B _ k u z' h1,
    evR_frBor_of_isReduced hL hF t u₀ u hbu,
    GlobalTheory.Reg.evR_baseChange_of_isReduced E H Dw l Xo c hL a n F hF A _ π y u₀ hu₀, map_mul, ← hπ]
  congr 1
  have e : wchar (ex Dw a n) t = algebraMap R B (MvPolynomial.X none) ^ n := by
    simp [wchar, t, ex, Fintype.prod_option]
  rw [e, map_pow, hk]
  simp [k₀, v, R]

end General

end GlobalTheory.ArcQ
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.SectionValueAtMultipleOfBaseChangedGenerator

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)

noncomputable section

namespace GlobalTheory.HkValueMul

theorem fibreSectionScale_zero {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) (i : (PPx x).ι) : Formalism.L2.Pj.scal x (0 : S) i = 0 := by
  simp only [Formalism.L2.Pj.scal, ReciprocityTheory.ChartRestriction.G.Out.liftFun, map_zero]

theorem fibreSectionScale_one {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) (i : (PPx x).ι) : Formalism.L2.Pj.scal x (1 : S) i = 1 := by
  simp only [Formalism.L2.Pj.scal, ReciprocityTheory.ChartRestriction.G.Out.liftFun, map_one]

theorem evR_of_secBC_mul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ f ∈ sec Xo c a n, ∀ (T Ω : Type) [CommRing T] [IsReduced T] [Algebra c.F T] [Field Ω] [Algebra c.F Ω] (χ : T →ₐ[c.F] Ω) (z₀ : FrPt Xo c T) (z₁ : FrPt Xo c Ω) (a₀ : T), z₁.x = spMap χ.toRingHom ≫ z₀.x → (∀ τ j, z₁.u τ j = spMap (dualMap χ.toRingHom) ≫ z₀.u τ j) → SecBC χ.toRingHom a₀ z₀.x z₁.x z₀.s z₁.s → evR Xo c f z₁ = χ (a₀ ^ n * evR Xo c f z₀) := by
  intro E _ _ _ H Dw l Xo c a n f hf T Ω _ _ _ _ _ χ z₀ z₁ a₀ hx hu hs
  have hL := (GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c).1
  obtain ⟨w, hw⟩ := hL.bc T Ω χ z₀
  have key : ∃ g : Ωˣ, (g : Ω) = χ a₀ ∧ FrBor (fun i => i.elim g fun _ => 1) w z₁ := by
    have hw' := hw
    obtain ⟨wx, wo, wu, wtan, weig, wbas, ws, wgen⟩ := w
    obtain ⟨zx, zo, zu, ztan, zeig, zbas, zs, zgen⟩ := z₁
    obtain ⟨hwx, hwu, pm, hp1, hp2, hp3⟩ := hw'
    dsimp only at hx hu hs hwx hwu hp1 hp2 hp3 ⊢
    subst hx
    subst hwx
    have hSw : GlobalTheory.Frames.SecBC χ.toRingHom 1 z₀.x (spMap χ.toRingHom ≫ z₀.x) z₀.s ws :=
      ⟨pm, hp1, hp2, fun i h => by rw [show Formalism.L2.Pj.scal z₀.x (1 : T) i = 1 from fibreSectionScale_one z₀.x i, _root_.one_mul]; exact hp3 i h⟩
    have hcalc := GlobalTheory.Frames.SecCalc.sec_calc E H Dw l Xo T Ω Ω χ.toRingHom (RingHom.id Ω) z₀.x
      (spMap χ.toRingHom ≫ z₀.x) (spMap χ.toRingHom ≫ z₀.x) rfl (by simp [spMap])
    have hz : ∀ i, zs.f i = Formalism.L2.Pj.scal (spMap χ.toRingHom ≫ z₀.x) (χ a₀) i * ws.f i :=
      (hcalc.2.2.1 a₀ z₀.s ws zs hSw).1 hs
    have hne : χ a₀ ≠ 0 := by
      intro h0
      have hz0 : ∀ i, zs.f i = 0 := fun i => by rw [hz i, h0, show Formalism.L2.Pj.scal (spMap χ.toRingHom ≫ z₀.x) (0 : Ω) i = 0 from fibreSectionScale_zero _ i, MulZeroClass.zero_mul]
      obtain ⟨b, -, hb⟩ := zgen zs
      have e0 := hb 0 (fun i => by rw [hz0 i, MulZeroClass.mul_zero])
      have e1 := hb 1 (fun i => by rw [hz0 i, MulZeroClass.mul_zero])
      exact zero_ne_one (e0.trans e1.symm)
    have hcalc' := GlobalTheory.Frames.SecCalc.sec_calc E H Dw l Xo Ω Ω Ω (RingHom.id Ω) (RingHom.id Ω)
      (spMap χ.toRingHom ≫ z₀.x) (spMap χ.toRingHom ≫ z₀.x) (spMap χ.toRingHom ≫ z₀.x)
      (by simp [spMap]) (by simp [spMap])
    refine ⟨Units.mk0 _ hne, rfl, (GlobalTheory.Frames.frBor_iff_frChg _ _ _).2
      ⟨fun τ => 1, fun τ i j hij => Matrix.one_apply_ne hij.ne, fun τ i => by simp, rfl, fun τ i => ?_, ?_⟩⟩
    · have e : (1 : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) Ω) i = Pi.single i 1 := by
        ext j
        simp [Matrix.one_apply, Pi.single_apply, eq_comm]
      show IsCombAt _ (wu τ) ((1 : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) Ω) i) (zu τ i)
      rw [e, (hu τ i).trans (hwu τ i).symm]
      exact Formalism.L2.PjFree.isCombAt_single (wtan τ) i
    · exact (hcalc'.2.1 _ ws zs).2 (by simpa using hz)
  obtain ⟨g, hg, hb⟩ := key
  rw [GlobalTheory.ArcQ.evR_scale_of_isReduced hL hf χ g z₀ w z₁ hw hb, hg, map_mul, map_pow]

end GlobalTheory.HkValueMul
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.SectionValueAtMultipleOfBaseChangedGeneratorStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)

theorem _root_.GlobalTheory.T.section_value_at_multiple_of_baseChanged_generator : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ f ∈ sec Xo c a n, ∀ (T Ω : Type) [CommRing T] [IsReduced T] [Algebra c.F T] [Field Ω] [Algebra c.F Ω] (χ : T →ₐ[c.F] Ω) (z₀ : FrPt Xo c T) (z₁ : FrPt Xo c Ω) (a₀ : T), z₁.x = spMap χ.toRingHom ≫ z₀.x → (∀ τ j, z₁.u τ j = spMap (dualMap χ.toRingHom) ≫ z₀.u τ j) → SecBC χ.toRingHom a₀ z₀.x z₁.x z₀.s z₁.s → evR Xo c f z₁ = χ (a₀ ^ n * evR Xo c f z₀) := by
  first | exact @GlobalTheory.HkValueMul.evR_of_secBC_mul | exact GlobalTheory.HkValueMul.evR_of_secBC_mul | (intros; apply GlobalTheory.HkValueMul.evR_of_secBC_mul <;> assumption)
end
end
