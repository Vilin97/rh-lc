module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
public import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsModelOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
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
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
public import Formalism.LocalToGlobal.ProjectiveLattices.PetersonNormSubspace
public import Development.WeilBound.CoreStatements.MinimalPrimeDimensions.FinSmallGen
public import Development.WeilBound.CoreStatements.MinimalPrimeDimensions.WeightSectionsHeightEstimate
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecZEqZeroOfGenVal
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.GenFrExAndGenFromTest
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Development.AbelianVarietyTheory.Definitions.Divisors.FirstChernLeviEqConstant
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoices

-- Source module: Development.AbelianVarietyTheory.Definitions.Divisors.NotIsChowFormIntLineZero

section

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompHt.Test

open MvPolynomial NumberField IsDedekindDomain Module Filter GlobalTheory.ChowHt GlobalTheory.AllWt GlobalTheory.CompHt
open scoped ENNReal


set_option autoImplicit false in
open MvPolynomial NumberField IsDedekindDomain Module Filter in
open scoped ENNReal in
theorem _root_.GlobalTheory.CompHt.Test.imageDeg_zero {K V Ω : Type} [Field K] [AddCommGroup V] [Module K V]
    [Field Ω] [Algebra K Ω] (D : ℕ) :
    _root_.GlobalTheory.CompHt.imageDeg (0 : V →ₗ[K] Ω) D = 0 := by
  by_contra hne
  obtain ⟨N, b, f, hf⟩ := (_root_.GlobalTheory.CompHt.imageDeg_pos_iff _ D).1 (Nat.pos_of_ne_zero hne)
  obtain ⟨y, hy, hI⟩ := hf.exists_point
  apply hy
  funext i
  have hX : (X i : MvPolynomial (Fin N) K) ∈ _root_.GlobalTheory.CompHt.imageIdeal (0 : V →ₗ[K] Ω) b := by
    unfold _root_.GlobalTheory.CompHt.imageIdeal
    rw [_root_.GlobalTheory.CompHt.mem_coneIdeal_of_isHomogeneous _ (isHomogeneous_X K i)]
    simp
  simpa using hI _ hX

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

variable (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)

end GlobalTheory.CompHt.Test
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsRatSecOfPull

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar
open scoped Pointwise

namespace GlobalTheory.TrueGeo.SmallSec

variable {F : Type} [Field F] [NumberField F]

section Local

variable {Z : Scheme.{0}} [IsIntegral Z] {D : CartierDiv Z} {x : Z} {u g : Z.functionFieldˣ}
  {f : Z.functionField} {k τ : ℕ}

end Local

variable {C : CxSt F} {Y : Var F} (A : Adl C Y) {k τ : ℕ} {f : Y.Fn}

theorem isRatSec_pow {Z : Scheme.{0}} [IsIntegral Z] {L : LB Z} {r : L.ι → Z.functionFieldˣ}
    (hr : IsRatSec L r) (τ : ℕ) : IsRatSec (lbPow L τ) fun c => r (c PUnit.unit) ^ τ :=
  fun c c' h => by
  have l : (lbPow L τ).U c ⊓ (lbPow L τ).U c' ≤ L.U (c PUnit.unit) ⊓ L.U (c' PUnit.unit) :=
    fun _ hx => ⟨Set.mem_iInter.1 hx.1 PUnit.unit, Set.mem_iInter.1 hx.2 PUnit.unit⟩
  have e : (lbPow L τ).g c c' = res l (L.g (c PUnit.unit) (c' PUnit.unit)) ^ τ := by
    change ∏ _k : PUnit, _ = _
    refine (Fintype.prod_unique _).trans ((zpow_natCast _ _).trans ?_)
    rfl
  rw [e, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, map_pow,
    ← mul_pow, hr _ _ (l h)]
  exact congrArg (fun a => (a * _) ^ τ) (fnOf_resG l h _).symm


end GlobalTheory.TrueGeo.SmallSec
end
end
end

-- Source module: Development.WeilBound.CoreStatements.NefModelVolumes.InjectivityWeightSectionsOf

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical

set_option autoImplicit false

noncomputable section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Points GlobalTheory.ChartGlue GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

namespace PositivityTheory.Xj7N.Inj

open GlobalTheory

section Generic

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

theorem exists_rat_small (L : HermLB p) (s₀ : L.B.Sec) (hs₀ : genericPoint X ∈ nonzeroLocus s₀) (τ : ℕ) (t : ℝ) :
    ∃ R : (lbPow L.B τ).Sec → X.functionField, Function.Injective R ∧ ∀ h : X.functionField,
      (∀ (c : L.B.ι) (x : X) (hx : x ∈ L.B.U c), RegAt x (h * fnOf (L.B.U c) (gen_mem hx) (s₀.f c) ^ τ)) →
      (∀ (σ : k →+* ℂ) (y : CxPts p σ) (c : L.B.ι) (hy : y ∈ ptsIn p σ (L.B.U c)),
        RegAt (under y) (h * fnOf (L.B.U c) (gen_mem (mem_ptsIn.1 hy)) (s₀.f c) ^ τ) →
        ‖ratVal (h * fnOf (L.B.U c) (gen_mem (mem_ptsIn.1 hy)) (s₀.f c) ^ τ) y‖ ^ 2 *
          Real.exp (-((τ : ℝ) * (L.φ σ).φ c y)) ≤ Real.exp (2 * (τ : ℝ) * t)) →
      ∃ S ∈ ((L.shift (fun _ => t) (fun _ => rfl)).pow τ).smallSec, R S = h := by
  have hr := isRatSec_ratOfSec s₀ hs₀
  have hrτ := GlobalTheory.TrueGeo.SmallSec.isRatSec_pow hr τ
  have hPr := presents_divOfRatSec (L.pow τ).isLB hrτ
  refine ⟨hPr.rat, hPr.rat_injective, fun h hreg hb => ?_⟩
  have hsec : h ∈ (divOfRatSec (L.pow τ).isLB hrτ).sections := by
    refine CartierDiv.mem_sections.2 fun x => ?_
    obtain ⟨c, hc⟩ := exists_chart (L.pow τ).isLB x
    have hx : x ∈ L.B.U (c PUnit.unit) := Set.mem_iInter.1 hc PUnit.unit
    refine ⟨_, hPr.isEqn c x hc, ?_⟩
    rw [Units.val_pow_eq_pow_val, val_ratOfSec (gen_mem hx)]
    exact hreg _ x hx
  obtain ⟨S, hS⟩ := hPr.exists_rat_eq hsec
  refine ⟨S, fun σ y => ?_, hS⟩
  let Lτ := (L.shift (fun _ => t) (fun _ => rfl)).pow τ
  obtain ⟨c, hc⟩ := exists_chart Lτ.isLB (under y)
  have hy : y ∈ ptsIn p σ (Lτ.B.U c) := mem_ptsIn.2 hc
  have hy1 : y ∈ ptsIn p σ (L.B.U (c PUnit.unit)) := mem_ptsIn.2 (Set.mem_iInter.1 hc PUnit.unit)
  have hgen : genericPoint X ∈ Lτ.B.U c := gen_mem hc
  have e0 : fnOf (Lτ.B.U c) hgen ((S : Lτ.B.Sec).f c) =
      h * fnOf _ (gen_mem (mem_ptsIn.1 hy1)) (s₀.f (c PUnit.unit)) ^ τ := by
    have := hPr.rat_mul S c hgen
    rw [hS, Units.val_pow_eq_pow_val, val_ratOfSec (gen_mem (mem_ptsIn.1 hy1))] at this
    exact this.symm
  have e1 : ev p σ (Lτ.B.U c) ((S : Lτ.B.Sec).f c) y =
      ratVal (h * fnOf _ (gen_mem (mem_ptsIn.1 hy1)) (s₀.f (c PUnit.unit)) ^ τ) y := by
    rw [← e0]; exact (ratVal_fnOf hy hgen ((S : Lτ.B.Sec).f c)).symm
  have e2 : (Lτ.φ σ).φ c y = (τ : ℝ) * ((L.φ σ).φ (c PUnit.unit) y + 2 * t) := by
    have := Weight.zpow_φ ((L.φ σ).addFn fun _ => 2 * t) (τ : ℤ) c y
    exact this.trans (by push_cast; rfl)
  have hb' := hb σ y (c PUnit.unit) hy1 (hreg _ _ (mem_ptsIn.1 hy1))
  have hn := Weight.nsq_eq (Lτ.φ σ) (secVal_mem (p := p) (σ := σ) (S : Lτ.B.Sec)) hy
  show (Lτ.φ σ).nsq (secVal p σ (S : Lτ.B.Sec)) y ≤ 1
  refine hn.le.trans ?_
  have e4 : secVal p σ (S : Lτ.B.Sec) c y = ev p σ (Lτ.B.U c) ((S : Lτ.B.Sec).f c) y := by
    erw [secVal_apply]; rfl
  rw [e4, e1, e2]
  have e3 : Real.exp (-((τ : ℝ) * ((L.φ σ).φ (c PUnit.unit) y + 2 * t))) =
      Real.exp (-((τ : ℝ) * (L.φ σ).φ (c PUnit.unit) y)) * (Real.exp (2 * (τ : ℝ) * t))⁻¹ := by
    rw [← Real.exp_neg, ← Real.exp_add]; ring_nf
  rw [e3, ← mul_assoc, mul_inv_le_iff₀ (Real.exp_pos _), one_mul]
  exact hb'

end Generic

theorem eq_zero_of_genVal' {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r}
    {Z : Comp Xo c} {G : WTZ E} {f : Rul Xo c} (hf : f ∈ cuspOn U Z G) (h0 : genVal Z f = 0) : f = 0 := by
  refine secZ_eq_zero_of_genVal hf.1.1 fun Z' => ?_
  by_cases hZ : Z' = Z
  · rw [hZ, h0]
  · exact evC_eq_zero (GlobalTheory.Reg.genFrEx_and_genFromTest _ _ _ _ _ _).1 hZ hf.2


end PositivityTheory.Xj7N.Inj

end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.SmallSectionsInjectiveOfSelfIntersectionBound

section

@[expose] public section

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Points GlobalTheory.ChartGlue GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
namespace PositivityTheory.Xj7N.Inj
open GlobalTheory
section Generic
variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}
end Generic
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 100000 in
theorem small_sections_injective_of_self_intersection_bound (hK : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (u : GlobalTheory.AllWt.Weight (T.Q.Dw j)) (X : AlgebraicGeometry.Scheme.{0}) [AlgebraicGeometry.IsIntegral X] (p : X ⟶ Sp (𝓞 Y.d.c₂.F)) (L : GlobalTheory.HermLB p) (ψ : Om Z →+* X.functionField) (s : latOn Y.U Z (wtOf (T.Q.Dw j) u 0) → L.B.Sec) (t : ℝ), GoodOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0) → GlobalTheory.DegVal.BirOn Y.U Z (wtOf (T.Q.Dw j) u 0) → NoBase Y.U Z (wtOf (T.Q.Dw j) u 0) → 0 < Y.dg u Z → GlobalTheory.ImageModel.IsModelOf (normOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0)) (latOn Y.U Z (wtOf (T.Q.Dw j) u 0)) (genPoint Z (cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0))) (dimFlag (T.Q.Dw j)) p L ψ s → ∀ i : ℕ, 1 ≤ i → ∀ f ∈ smallL Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0) (8 * i) t, ∀ w : latOn Y.U Z (wtOf (T.Q.Dw j) u 0), genVal Z ((w : cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0)) : Rul Y.d.Xo₂ Y.d.c₂) ≠ 0 → ∀ (σ : 𝓞 Y.d.c₂.F →+* ℂ) (y : GlobalTheory.CxPts p σ) (k : L.B.ι) (hy : y ∈ GlobalTheory.CxPts.ptsIn p σ (L.B.U k)), GlobalTheory.Cartier.RegAt (GlobalTheory.Cartier.under y) (ψ (genVal Z (f : Rul Y.d.Xo₂ Y.d.c₂)) * (ψ (genVal Z ((w : cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0)) : Rul Y.d.Xo₂ Y.d.c₂)))⁻¹ ^ (8 * i) * fnOf (L.B.U k) (gen_mem (GlobalTheory.CxPts.mem_ptsIn.1 hy)) ((s w).f k) ^ (8 * i)) → ‖GlobalTheory.Cartier.ratVal (ψ (genVal Z (f : Rul Y.d.Xo₂ Y.d.c₂)) * (ψ (genVal Z ((w : cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0)) : Rul Y.d.Xo₂ Y.d.c₂)))⁻¹ ^ (8 * i) * fnOf (L.B.U k) (gen_mem (GlobalTheory.CxPts.mem_ptsIn.1 hy)) ((s w).f k) ^ (8 * i)) y‖ ^ 2 * Real.exp (-(((8 * i : ℕ) : ℝ) * (L.φ σ).φ k y)) ≤ Real.exp (2 * ((8 * i : ℕ) : ℝ) * t)) : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (u : GlobalTheory.AllWt.Weight (T.Q.Dw j)) (X : AlgebraicGeometry.Scheme.{0}) [AlgebraicGeometry.IsIntegral X] (p : X ⟶ Sp (𝓞 Y.d.c₂.F)) (L : GlobalTheory.HermLB p) (ψ : Om Z →+* X.functionField) (s : latOn Y.U Z (wtOf (T.Q.Dw j) u 0) → L.B.Sec) (t : ℝ), GoodOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0) → GlobalTheory.DegVal.BirOn Y.U Z (wtOf (T.Q.Dw j) u 0) → NoBase Y.U Z (wtOf (T.Q.Dw j) u 0) → 0 < Y.dg u Z → GlobalTheory.ImageModel.IsModelOf (normOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0)) (latOn Y.U Z (wtOf (T.Q.Dw j) u 0)) (genPoint Z (cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0))) (dimFlag (T.Q.Dw j)) p L ψ s → ∀ i : ℕ, 1 ≤ i → (smallL Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0) (8 * i) t).encard ≤ ((L.shift (fun _ => t) (fun _ => rfl)).pow (8 * i)).smallSec.encard := by
  intro hP D T j Y e o hY hE Z u X _ p L ψ s t hGood hBir hNB hdg hM i hi
  have hex : ∃ w : latOn Y.U Z (wtOf (T.Q.Dw j) u 0),
      genVal Z ((w : cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0)) : Rul Y.d.Xo₂ Y.d.c₂) ≠ 0 := by
    by_contra hno
    push Not at hno
    have hz : genPoint Z (cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0)) = 0 := by
      have hle : Submodule.span Y.d.c₂.F (latOn Y.U Z (wtOf (T.Q.Dw j) u 0) : Set (cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0))) ≤
          LinearMap.ker (genPoint Z (cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0))) :=
        Submodule.span_le.2 fun v hv => by
          simpa [genPoint] using hno ⟨v, hv⟩
      rw [hGood.2.2] at hle
      exact LinearMap.ext fun v => hle Submodule.mem_top
    have h0 : Y.dg u Z = 0 := by
      show ((compDeg Y.U Z (wtOf (T.Q.Dw j) u 0) : ℕ) : ℝ) = 0
      rw [compDeg, hz, GlobalTheory.CompHt.Test.imageDeg_zero, Nat.cast_zero]
    exact absurd hdg (by rw [h0]; exact lt_irrefl 0)
  obtain ⟨w, hw⟩ : ∃ w, genericPoint X ∈ nonzeroLocus (s w) := by
    have h : genericPoint X ∈ (⨆ w, nonzeroLocus (s w) : X.Opens) := by
      rw [hM.bpf]; trivial
    rw [← SetLike.mem_coe, TopologicalSpace.Opens.coe_iSup, Set.mem_iUnion] at h
    exact h
  obtain ⟨k₀, hk₀⟩ := exists_chart L.isLB (genericPoint X)
  have hw0 : genVal Z ((w : cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0)) : Rul Y.d.Xo₂ Y.d.c₂) ≠ 0 := by
    intro h0
    obtain ⟨w₁, hw₁⟩ := hex
    have hr := hM.ratio w₁ w k₀ hk₀
    have e0 : ψ ((genPoint Z (cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0))) (w : cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0))) = 0 := by
      have : (genPoint Z (cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0))) (w : cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0)) = 0 := h0
      rw [this, map_zero]
    have h1 : ψ ((genPoint Z (cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0))) (w₁ : cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0))) ≠ 0 :=
      (map_ne_zero_iff ψ hM.bij.1).2 hw₁
    exact mul_ne_zero h1 (fnOf_sec_ne_zero hw hk₀) (hr.trans (by rw [e0, zero_mul]))
  have hψinj : Function.Injective ψ := hM.bij.1
  obtain ⟨R, hRinj, hR⟩ := exists_rat_small L (s w) hw (8 * i) t
  have key : ∀ f ∈ smallL Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0) (8 * i) t,
      ∃ S ∈ ((L.shift (fun _ => t) (fun _ => rfl)).pow (8 * i)).smallSec, R S = ψ (genVal Z (f : Rul Y.d.Xo₂ Y.d.c₂)) *
          (ψ (genVal Z ((w : cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0)) : Rul Y.d.Xo₂ Y.d.c₂)))⁻¹ ^ (8 * i) := by
    intro f hf
    have hreg := _root_.ChowFormHeightComparison₂.RegularPointExistence.reg_of_val
      hM (8 * i) (genVal Z (f : Rul Y.d.Xo₂ Y.d.c₂))
      (fun la O h1 h2 => _root_.ChowFormHeightComparison₂.RegularPointExistence.fin_small_gen
        Y.U Z _ hGood.2.1 hGood.2.2 hBir la O.valuation h1 h2 (8 * i) f fun v hv => hf.1 la v hv)
      w hw0
    exact hR _ hreg (hK hP D T j Y e o hY hE Z u X p L ψ s t hGood hBir hNB hdg hM i hi f hf w hw0)
  choose! Sf hSf hRf using key
  have hinj : Set.InjOn Sf (smallL Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0) (8 * i) t) := by
    intro f hf g hg hfg
    have h1 := (hRf f hf).symm.trans ((congrArg R hfg).trans (hRf g hg))
    have hψw : ψ (genVal Z ((w : cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0)) : Rul Y.d.Xo₂ Y.d.c₂)) ≠ 0 :=
      (map_ne_zero_iff ψ hψinj).2 hw0
    have hc : (ψ (genVal Z ((w : cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0)) : Rul Y.d.Xo₂ Y.d.c₂)))⁻¹ ^ (8 * i) ≠ 0 :=
      pow_ne_zero _ (inv_ne_zero hψw)
    have h2 := hψinj (mul_right_cancel₀ hc h1)
    have h3 : genVal Z ((f : Rul Y.d.Xo₂ Y.d.c₂) - (g : Rul Y.d.Xo₂ Y.d.c₂)) = 0 := by
      rw [map_sub, h2, sub_self]
    exact Subtype.ext (sub_eq_zero.1 (eq_zero_of_genVal' (Submodule.sub_mem _ f.2 g.2) h3))
  rw [← hinj.encard_image]
  exact Set.encard_le_encard (Set.image_subset_iff.2 fun f hf => hSf f hf)
end PositivityTheory.Xj7N.Inj
end
end
end
end
