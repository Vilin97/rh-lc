module

public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GenRelNeZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsConstantEigenbasisTangentArc
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsIsArcFr
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsNeZeroIff
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FrameChangeExistsUniqueInvertible
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameChangeExistsUniqueOfSamePoint
public import Formalism.LocalToGlobal.ProjectiveLattices.SectionOfLineBundleOne
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
public import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.ArcLineFunctions.ArcSPin
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc

-- Source module: Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.MemOfEqMulInvPow

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.JointModelGuards

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem mem_of_eq_mul_inv_pow (W : ValuationSubring ℂ) {x a : ℂ} (ha : a ∈ W) (n : ℕ) (h : x = a * x⁻¹ ^ n) :
    x ∈ W := by
  rcases W.mem_or_inv_mem x with hx | hx
  · exact hx
  · rw [h]; exact mul_mem ha (pow_mem hx n)

theorem exists_root_and_zeta (l : Level H) (c : Coeff l) (W : ValuationSubring ℂ) :
    ∃ r z : c.V W, (((c.V W).subtype r : c.F) : ℂ) = H.rt0 ∧ (((c.V W).subtype z : c.F) : ℂ) = zeta l.A := by
  apply GlobalTheory.MatchRigid.exists_rt_zeta <;> assumption

end GlobalTheory.JointModelGuards
end
end

-- Source module: Formalism.LocalToGlobal.ProjectiveLattices.ArcPtX

section

@[expose] public section

noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

lemma arcι_X_isUnit (Dw : Datum H) (K₁ : Type) [Field K₁] : IsUnit (arcι Dw K₁ PowerSeries.X) := by
  have h : IsUnit (HahnSeries.ofPowerSeries ℤ K₁ PowerSeries.X) := by
    rw [isUnit_iff_ne_zero]
    first
      | (rw [HahnSeries.ofPowerSeries_X]; exact HahnSeries.single_ne_zero one_ne_zero)
      | (intro h0
         exact PowerSeries.X_ne_zero ((map_eq_zero_iff _ HahnSeries.ofPowerSeries_injective).mp h0))
      | (simp; done)
  exact (h.map (MvPolynomial.C (σ := ArcLt Dw))).map
    (algebraMap (MvPolynomial (ArcLt Dw) (LaurentSeries K₁)) (ArcS Dw K₁))

lemma arc_pt_X (Dw : Datum H) (K₁ : Type) [Field K₁] (q : Sp (ArcS Dw K₁)) :
    PowerSeries.X ∉ ((spMap (arcι Dw K₁)) q).asIdeal := by
  intro hX
  have h1 : arcι Dw K₁ PowerSeries.X ∈ q.asIdeal := by
    first
      | exact hX
      | (simpa using hX)
  exact q.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h1 (arcι_X_isUnit Dw K₁))

theorem arcPt_point (Y : Model Xo c β) {K₁ : Type} [Field K₁] (b : O →+* K₁) [Algebra c.F (ArcS Dw K₁)]
    (hcomp : (algebraMap c.F (ArcS Dw K₁)).comp β = (arcι Dw K₁).comp ((PowerSeries.C (R := K₁)).comp b))
    (χ : Sp (PowerSeries K₁) ⟶ Y.X) (hχs : χ ≫ Y.s = spMap (PowerSeries.C (R := K₁)) ≫ spMap b)
    (hj : ∀ x : Sp (PowerSeries K₁), PowerSeries.X ∉ x.asIdeal → χ x ∈ Set.range Y.j) :
    ∃ z : Sp (ArcS Dw K₁) ⟶ Xo.XF c, z ≫ Y.j = spMap (arcι Dw K₁) ≫ χ ∧
      z ≫ Y.jQ ≫ pullback.snd _ _ = spMap (algebraMap c.F (ArcS Dw K₁)) := by
  haveI := Y.jQ_open
  have hw : (spMap (arcι Dw K₁) ≫ χ) ≫ Y.s = spMap (algebraMap c.F (ArcS Dw K₁)) ≫ spMap β := by
    rw [Category.assoc, hχs, ← spMap_comp, ← spMap_comp, ← spMap_comp, hcomp]
  let g : Sp (ArcS Dw K₁) ⟶ pullback Y.s (spMap β) :=
    pullback.lift (spMap (arcι Dw K₁) ≫ χ) (spMap (algebraMap c.F (ArcS Dw K₁))) hw
  have hg : Set.range g ⊆ Set.range Y.jQ := by
    rintro _ ⟨q, rfl⟩
    rw [← Y.ab_gen]
    have e1 : (pullback.fst Y.s (spMap β)) (g q) = χ ((spMap (arcι Dw K₁)) q) := by
      have := congrArg (fun f : Sp (ArcS Dw K₁) ⟶ Y.X => f q) (pullback.lift_fst _ _ hw)
      first
        | exact this
        | (simpa using this)
    show (pullback.fst Y.s (spMap β)) (g q) ∈ abLocus Y.t.G
    rw [e1]
    obtain ⟨p, hp⟩ := hj _ (arc_pt_X Dw K₁ q)
    rw [← hp]
    have h2 : Y.jQ p ∈ (pullback.fst Y.s (spMap β)) ⁻¹' abLocus Y.t.G := by
      rw [Y.ab_gen]
      exact ⟨p, rfl⟩
    exact h2
  refine ⟨IsOpenImmersion.lift Y.jQ g hg, ?_, ?_⟩
  · show IsOpenImmersion.lift Y.jQ g hg ≫ Y.jQ ≫ pullback.fst _ _ = _
    rw [← Category.assoc, IsOpenImmersion.lift_fac, pullback.lift_fst]
  · rw [← Category.assoc, IsOpenImmersion.lift_fac, pullback.lift_snd]

end Formalism.L2.Pj
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.SecEqOfSecBCIdOne

section

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open MonoidalCategory CartesianMonoidalCategory

namespace GlobalTheory.ArcDatumExists

theorem isUnit_det_letM {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (Dw : Datum H)
    (K : Type) [Field K] (τ : E →+* ℂ) : IsUnit (letM Dw K τ).det := by
  have h1 : IsUnit (algebraMap (MvPolynomial (ArcLt Dw) (LaurentSeries K)) (ArcS Dw K) (arcDet Dw K)) :=
    IsLocalization.Away.algebraMap_isUnit _
  have h2 : Matrix.det (Matrix.of fun i k : Fin (Dw.mult τ) =>
      (MvPolynomial.X (⟨τ, i, k⟩ : ArcLt Dw) : MvPolynomial (ArcLt Dw) (LaurentSeries K))) ∣ arcDet Dw K :=
    Finset.dvd_prod_of_mem (fun τ : E →+* ℂ => Matrix.det (Matrix.of fun i k : Fin (Dw.mult τ) =>
      (MvPolynomial.X (⟨τ, i, k⟩ : ArcLt Dw) : MvPolynomial (ArcLt Dw) (LaurentSeries K)))) (Finset.mem_univ τ)
  have h3 := isUnit_of_dvd_unit
    (map_dvd (algebraMap (MvPolynomial (ArcLt Dw) (LaurentSeries K)) (ArcS Dw K)) h2) h1
  rw [RingHom.map_det] at h3
  exact h3

theorem flat_of_field {K S : Type} [Field K] [CommRing S] (f : K →+* S) : f.Flat := by
  let _ := f.toAlgebra
  exact (inferInstance : Module.Flat K S)

theorem appLE_id_apply {X : Scheme.{0}} (U : X.Opens) (h : U ≤ 𝟙 X ⁻¹ᵁ U) (r : Γ(X, U)) :
    (Scheme.Hom.appLE (𝟙 X) U U h).hom r = r :=
  GlobalTheory.Frames.ChgOf.appLE_id' U h r

theorem sec_eq_of_secBC_id_one {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) (s s' : LB.Sec (PPx x))
    (h : SecBC (RingHom.id S) 1 x x s s') (i : (PPx x).ι) : s'.f i = s.f i := by
  simpa only [GlobalTheory.Frames.ChgOf.scal_one', one_mul] using
    (GlobalTheory.Frames.ChgOf.secBC_id_iff x 1 s s').mp h i

theorem isArcPt3At_of_frChg {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
    {K₁ : Type} [Field K₁] [Algebra c.F K₁] {b : O →+* K₁} {a : ArcIn Dw l β K₁ b} {χ : Sp (PowerSeries K₁) ⟶ Y.X}
    {W : Wit Y a χ} {e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR K₁)} {th : a.D₀.P.L.Sec}
    [Algebra c.F (ArcS Dw K₁)] {y₀ yF : FrPt Xo c (ArcS Dw K₁)} (hth : ∃ j, th.f j ≠ 0)
    (hfr : IsArcFr W e th (arcι Dw K₁) y₀) (hchg : FrChg (letM Dw K₁) 1 y₀ yF) : IsArcPt3At Y a χ W yF th := by
  obtain ⟨x, xo, u, tan, eig, bas, s, gen⟩ := yF
  obtain ⟨hx, hu, hs⟩ := hchg
  dsimp only at hx hu hs
  subst hx
  obtain ⟨z, t', m1, m2, φ, -, -, -, h0, hm, -, θ, w1, w2, σ', s1, θ2, hθ, r1, r2, i1, i2, ps, hg⟩ := hfr
  obtain ⟨σ, fam, θ', a1, a2, a3, a4⟩ := hθ
  refine ⟨σ, fam, θ', θ, hth, a1, a2, a3, a4, t', m1, m2, w1, w2, σ', s1, θ2, ⟨φ, h0, hm⟩, r1, r2, i1, i2, ps, ?_⟩
  intro g g1 g2 j h
  rw [hg g g1 g2 j h]
  exact congrArg _ (sec_eq_of_secBC_id_one _ _ _ hs _).symm

theorem exists_arcDatum : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K₁ : Type) [Field K₁] [Algebra c.F K₁] (Wp : ValuationSubring ℂ) (Y : Model Xo c (c.V Wp).subtype), Y.N4 → ∀ a : ArcIn Dw l (RingHom.id c.F) K₁ (algebraMap c.F K₁), ∃ (χ : Sp (PowerSeries K₁) ⟶ Y.X) (W : Wit Y (a.restrict (c.V Wp).subtype) χ), (∃ e, ArcLieBasis W e) ∧ ∀ e, ArcLieBasis W e → ∀ th : a.D₀.P.L.Sec, (∃ j, th.f j ≠ 0) → ∀ (μ : ArcLt Dw →₀ ℕ) (jj : ℤ), ∃ d : ArcDatum Xo c K₁, d.Wp = Wp ∧ HEq d.Y Y ∧ d.a = a ∧ HEq d.e e ∧ HEq d.th th ∧ d.μ = μ ∧ d.jj = jj ∧ d.OverBase ∧ d.Normal 1 := by
  intro hL hL2 E _ _ _ H Dw l Xo c K₁ _ _ Wp Y hN4 a
  have : CharZero K₁ := charZero_of_injective_algebraMap (algebraMap c.F K₁).injective
  obtain ⟨χ, hχ, -⟩ := hN4 K₁ ((algebraMap c.F K₁).comp (c.V Wp).subtype) 1
    (a.restrict (c.V Wp).subtype) (Or.inl ⟨Field.toIsField K₁, rfl⟩)
  obtain ⟨hs, -, hj, hW⟩ := (hχ χ).1 rfl
  obtain ⟨W⟩ := (Y.hasArcData_iff _ _ _ _ χ).1 hW
  refine ⟨χ, W, ?_, fun e he th hth μ jj => ?_⟩
  · obtain ⟨e, -, he⟩ := GlobalTheory.ConstBasis.exists_arcBasis hL hL2 E H Dw l Xo c _ _ Y K₁ _ (a.restrict (c.V Wp).subtype) χ W
      (fun τ => (algebraMap c.F K₁).comp (embK c τ))
      ((algebraMap K₁ (FractionRing K₁)).comp (algebraMap c.F K₁)) rfl (fun _ _ => rfl)
      (GlobalTheory.JointModelGuards.exists_root_and_zeta l c Wp)
    exact ⟨e, he⟩
  · have hcomp : (algebraMap c.F (ArcS Dw K₁)).comp (c.V Wp).subtype =
        (arcι Dw K₁).comp ((PowerSeries.C (R := K₁)).comp ((algebraMap c.F K₁).comp (c.V Wp).subtype)) := by
      ext r
      simp only [RingHom.comp_apply]
      exact arcS_pin Dw K₁ ((c.V Wp).subtype r)
    obtain ⟨z, hz1, hz2⟩ := arcPt_point (Dw := Dw) Y ((algebraMap c.F K₁).comp (c.V Wp).subtype)
      hcomp χ hs (fun x hx => hj x (by rwa [map_one, one_mul]))
    have hnz : ThNZ th := (GlobalTheory.ThetaOverField.nonzero_generates hL hL2 K₁ a.D₀ th).1.1 hth
    have hflat : ((arcι Dw K₁).comp (PowerSeries.C (R := K₁))).Flat := flat_of_field _
    have hz3 : z ≫ pullback.fst _ _ ≫ Xo.s = sOf c (ArcS Dw K₁) := by
      rw [Y.jQ_over] at hz2
      rw [pullback.condition, ← Category.assoc, hz2, ← spMap_comp]
      rfl
    obtain ⟨y₀, -, hy₀⟩ := GlobalTheory.ArcQ.exists_isArcFr hL hL2 E H Dw l Xo c _ _ Y K₁ _ (a.restrict (c.V Wp).subtype) χ W
      (fun τ => (algebraMap c.F K₁).comp (embK c τ)) e th he hnz (Or.inl (Field.toIsField K₁))
      (ArcS Dw K₁) (arcι Dw K₁) z hflat hz1 hz3 (fun τ x => arcS_pin Dw K₁ (embK c τ x))
    obtain ⟨yF, hyF⟩ := (GlobalTheory.ArcQ.frChg_exists_unique_units E H Dw l Xo c (ArcS Dw K₁) (letM Dw K₁) 1 y₀).1
      (isUnit_det_letM Dw K₁) isUnit_one
    have h12 := hy₀.isFramedPoint_changed_by_letters hyF hs
    have h3 := isArcPt3At_of_frChg (W := W) (e := e) hth hy₀ hyF
    refine ⟨⟨Wp, Y, a, χ, W, e, yF, th, h12, h3, μ, jj⟩, rfl, HEq.rfl, rfl, HEq.rfl, HEq.rfl, rfl, rfl, hs,
      y₀, hy₀, ?_⟩
    have h1 : GlobalTheory.ArcQ.cst Dw (1 : K₁) = 1 := by simp only [GlobalTheory.ArcQ.cst, map_one]
    rw [h1]
    exact hyF

end GlobalTheory.ArcDatumExists
end
end
