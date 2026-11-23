module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PhiAt
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NotSteepOnOfGermZero
public import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.CommGroupMulMulEqMulInvMulMulMul
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsChartOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
import Development.AbelianVarietyTheory.Definitions.Divisors.LinearIndependentBasisCoords
import Development.AbelianVarietyTheory.Definitions.Divisors.MemSubPtsCutBaseChangeIff
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnitaryWeightExponentVectorSignatureWeightMuZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CommuteInvLeft
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Formalism.LocalRingCardinality.SpanPowerMembership.HasStrictFDerivAtExpZero
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.EllipsoidStA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsCuspValueLePhiOfHilbertSamuel
public import Development.AbelianVarietyTheory.Definitions.Divisors.BarCompSubsetClosure
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartFrameChangeDiagonalUnitsIntegralFrameStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentredPointPhiPositiveWeights

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HSApp

theorem vV_algebraMap_unit (T : CDVR) (u : T.Vˣ) : vV T.V (algebraMap T.V T.Fr (u : T.V)) = 0 := by
  have h1 : valV T.V (algebraMap T.V T.Fr (u : T.V)) = 1 := by
    unfold valV
    rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
    refine (IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff).2 ?_
    show (u : T.V) ∉ IsLocalRing.maximalIdeal T.V
    exact fun h => h u.isUnit
  simp [vV, h1]

theorem log_ofAdd_neg (m : ℤ) :
    WithZero.log ((Multiplicative.ofAdd (-m) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) = -m := by
  first | rfl | simp [WithZero.log] | exact WithZero.log_coe _

theorem isLocalHom_of_centred {Y : Scheme.{0}} {y : Y} {ν : Valuation (Y.presheaf.stalk y) (WithZero (Multiplicative ℤ))}
    (hν : Centred y ν) (T : CDVR) (g : Y.presheaf.stalk y →+* T.V) (ρ : ℝ) (hρ : 0 < ρ)
    (hval : ∀ a, ν a ≠ 0 → -((WithZero.log (ν a) : ℤ) : ℝ) = ρ * (vV T.V (algebraMap T.V T.Fr (g a)) : ℝ)) :
    IsLocalHom g := by
  refine ⟨fun a ha => ?_⟩
  by_contra hna
  have hm : a ∈ IsLocalRing.maximalIdeal _ := hna
  have h0 : ν a ≠ 0 := by
    intro h
    rw [hν.2.2 a h, map_zero] at ha
    exact not_isUnit_zero ha
  have hlt := hν.2.1 a hm
  have hlog : WithZero.log (ν a) < 0 := by
    have := (WithZero.log_lt_log h0 one_ne_zero).2 hlt
    simpa using this
  have hv := hval a h0
  obtain ⟨u, hu⟩ := ha
  rw [← hu, vV_algebraMap_unit] at hv
  have : (0 : ℝ) < -((WithZero.log (ν a) : ℤ) : ℝ) := by
    have : ((WithZero.log (ν a) : ℤ) : ℝ) < 0 := by exact_mod_cast hlog
    linarith
  rw [hv] at this
  simp at this


end GlobalTheory.HSApp
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralFrameStalkCompatibility

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSApp

theorem top_le_fromSpecStalk {Y : Scheme.{0}} (y : Y) {R : Type} [CommRing R] (ψ : Y.presheaf.stalk y →+* R) (U : Y.Opens) (hy : y ∈ U) : ⊤ ≤ (Spec.map (CommRingCat.ofHom ψ) ≫ Y.fromSpecStalk y) ⁻¹ᵁ U := by
  intro s _
  show (Y.fromSpecStalk y) ((Spec.map (CommRingCat.ofHom ψ)) s) ∈ U
  have h : (Y.fromSpecStalk y) ((Spec.map (CommRingCat.ofHom ψ)) s) ∈ Set.range (Y.fromSpecStalk y) := ⟨_, rfl⟩
  rw [Scheme.range_fromSpecStalk] at h
  exact h.mem_open U.isOpen hy

theorem val_fromSpecStalk {Y : Scheme.{0}} {k : Type} [CommRing k] {p : Y ⟶ Sp k} {B : LB Y} (y : Y) (i : B.ι)
    (hi : y ∈ B.U i) {R : Type} [CommRing R] (ψ : Y.presheaf.stalk y →+* R) (f : H0 p B ⊤)
    (hO : ⊤ ≤ (Spec.map (CommRingCat.ofHom ψ) ≫ Y.fromSpecStalk y) ⁻¹ᵁ ⊤)
    (hj : ⊤ ≤ (Spec.map (CommRingCat.ofHom ψ) ≫ Y.fromSpecStalk y) ⁻¹ᵁ B.U i) :
    H0.val (Spec.map (CommRingCat.ofHom ψ) ≫ Y.fromSpecStalk y) i hO hj f = ψ (H0.germ i y (memTop y) hi f) := by
  rw [H0.val_apply, H0.germ_apply]
  have hV : y ∈ (⊤ : Y.Opens) ⊓ B.U i := memInf (memTop y) hi
  have h1 : ⊤ ≤ Y.fromSpecStalk y ⁻¹ᵁ ((⊤ : Y.Opens) ⊓ B.U i) := by
    intro s _
    have : Y.fromSpecStalk y s ∈ Set.range (Y.fromSpecStalk y) := ⟨s, rfl⟩
    rw [Scheme.range_fromSpecStalk] at this
    exact this.mem_open (IsOpen.inter isOpen_univ (B.U i).isOpen) hV
  rw [GlobalTheory.TangentOrigin.evalPt_spMap_comp ψ (Y.fromSpecStalk y) _ h1]
  congr 1
  have : (Y.fromSpecStalk y).appLE _ ⊤ h1 ≫ (Scheme.ΓSpecIso (Y.presheaf.stalk y)).hom =
      Y.presheaf.germ _ y hV := by
    rw [Scheme.Hom.appLE, Scheme.fromSpecStalk_app hV]
    simp only [Category.assoc, ← Functor.map_comp]
    rw [show ∀ q : (Opposite.op (⊤ : (Spec (Y.presheaf.stalk y)).Opens) ⟶ Opposite.op ⊤),
      (Spec (Y.presheaf.stalk y)).presheaf.map q = 𝟙 _ from fun q => by
        rw [Subsingleton.elim q (𝟙 _)]; exact CategoryTheory.Functor.map_id _ _]
    simp
  exact congrArg (fun q => CommRingCat.Hom.hom q _) this

theorem val_congr' {k : Type} [CommRing k] {T' : Scheme.{0}} {p : T' ⟶ Sp k} {B : LB T'} {O : T'.Opens} {R : Type}
    [CommRing R] {x x' : Sp R ⟶ T'} (e : x = x') (i : B.ι) (hO : ⊤ ≤ x ⁻¹ᵁ O) (hO' : ⊤ ≤ x' ⁻¹ᵁ O)
    (hi : ⊤ ≤ x ⁻¹ᵁ B.U i) (hi' : ⊤ ≤ x' ⁻¹ᵁ B.U i) (f : H0 p B O) : H0.val x i hO hi f = H0.val x' i hO' hi' f := by
  subst e; rfl

theorem val_restr'' {k : Type} [CommRing k] {T' : Scheme.{0}} {p : T' ⟶ Sp k} {B : LB T'} {O O' : T'.Opens}
    (h : O' ≤ O) {R : Type} [CommRing R] (x : Sp R ⟶ T') (i : B.ι) (hO : ⊤ ≤ x ⁻¹ᵁ O) (hO' : ⊤ ≤ x ⁻¹ᵁ O')
    (hi : ⊤ ≤ x ⁻¹ᵁ B.U i) (f : H0 p B O) : H0.val x i hO' hi (H0.restr h f) = H0.val x i hO hi f :=
  GlobalTheory.TangentOrigin.evalPt_res x (inf_le_inf_right _ h) (GlobalTheory.FlagMod.le_preimage_inf hO hi)
    (GlobalTheory.FlagMod.le_preimage_inf hO' hi) _



theorem evI_ofSpace_eq_prod_mul_val : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y) (Z : Comp Xo c) {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (la : AllWt.Weight Dw) (w : space X Z U la) (T : CDVR) (io : c.F →+* T.Fr), letI := io.toAlgebra; ∀ (y' : IntFr Xo c T io) (x₀ : Sp T.Fr ⟶ Y₀ X Z), (X.ptY y'.1 = x₀ ≫ inc₀ X Z) → ∀ (j' : (L₀ X Z la).ι) (hO : ⊤ ≤ x₀ ⁻¹ᵁ (⊤ : (Y₀ X Z).Opens)) (hj : ⊤ ≤ x₀ ⁻¹ᵁ (L₀ X Z la).U j') (hz : ⊤ ≤ (X.pt y'.1 ≫ X.inc) ⁻¹ᵁ X.F.U (j' PUnit.unit)) (Q : FrPt Xo c T.Fr) (t : Ix Dw → T.Frˣ), (X.F.ChartFr (j' PUnit.unit) (X.pt y'.1 ≫ X.inc) hz Q) → (FrBor t Q y'.1) → evI y' ((ofSpace X Z U la w : Cusp Z U la) : Rul Xo c) = (∏ ix, t ix ^ GlobalTheory.AllWt.exOf Dw la 0 ix).val * H0.val x₀ j' hO hj w.1 := by
  intro E _ _ _ H Dw l Xo c Y X Z r U la w T io y' x₀ hx j' hO hj hz Q t hQ ht
  letI := io.toAlgebra
  let fS : GlobalTheory.AllWt.secZ Xo c (GlobalTheory.AllWt.exOf Dw la 0) := ⟨_, cusp_le_secZ Z U la (ofSpace X Z U la w).2⟩
  have hOf : ⊤ ≤ (X.pt y'.1 ≫ X.inc) ⁻¹ᵁ flagOpen X :=
    GlobalTheory.FlagMod.le_preimage_map (z := X.pt y'.1) X.inc (top_le_inc X) le_top
  have a := evR_eq_val_secOf fS hOf hQ ht
  show evR Xo c fS.1 y'.1 = _
  rw [a]
  congr 1
  have hx' : X.pt y'.1 ≫ X.inc = x₀ ≫ inc₀ X Z := (X.pt_inc _).trans hx
  have hU₀ : ⊤ ≤ x₀ ⁻¹ᵁ U₀ X Z := by
    have h1 := hOf
    rw [hx', Scheme.Hom.comp_preimage] at h1
    exact h1
  have hk' : ⊤ ≤ (x₀ ≫ inc₀ X Z) ⁻¹ᵁ X.F.U (j' PUnit.unit) := hx' ▸ hz
  have hO' : ⊤ ≤ (x₀ ≫ inc₀ X Z) ⁻¹ᵁ flagOpen X := hx' ▸ hOf
  rw [val_congr' hx' _ hOf hO' hz hk']
  have b1 := H0.val_pull (inc₀ X Z) (le_refl (U₀ X Z)) x₀ j' hU₀ hj hO' hk' (secOf X _ fS)
  rw [← b1]
  have hs : H0.pull (inc₀ X Z) (le_refl (U₀ X Z)) (secOf X _ fS) = H0.restr le_top w.1 := cuspSec_ofSpace X Z U la w
  rw [hs, val_restr'' le_top x₀ j' hO hU₀ hj]



theorem germ_eq_unit_mul_evI_core {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y) (Z : Comp Xo c) {r : ℕ}
    (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (la : AllWt.Weight Dw) (w : space X Z U la) (y : Y₀ X Z) (T : CDVR)
    (io : c.F →+* T.Fr) (y' : IntFr Xo c T io) (g : (Y₀ X Z).presheaf.stalk y →+* T.V)
    (hpt : letI := io.toAlgebra; X.ptY y'.1 = Spec.map (CommRingCat.ofHom ((algebraMap T.V T.Fr).comp g)) ≫
      (Y₀ X Z).fromSpecStalk y ≫ inc₀ X Z)
    (j' : (L₀ X Z la).ι) (hj' : y ∈ (L₀ X Z la).U j') :
    ∃ u : T.Vˣ, algebraMap T.V T.Fr (g (H0.germ j' y (memTop y) hj' w.1)) =
      algebraMap T.V T.Fr (u : T.V) * evI y' ((ofSpace X Z U la w : Cusp Z U la) : Rul Xo c) := by
  letI := io.toAlgebra
  have hk : inc₀ X Z y ∈ X.F.U (j' PUnit.unit) := mem_pull.1 hj'
  have he : Spec.map (CommRingCat.ofHom ((algebraMap T.V T.Fr).comp g)) =
      Spec.map (CommRingCat.ofHom (algebraMap T.V T.Fr)) ≫ Spec.map (CommRingCat.ofHom g) := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
  have hx₀ : X.ptY y'.1 = (Spec.map (CommRingCat.ofHom ((algebraMap T.V T.Fr).comp g)) ≫
      (Y₀ X Z).fromSpecStalk y) ≫ inc₀ X Z := by rw [Category.assoc]; exact hpt
  have hpt' : X.ptY y'.1 = Spec.map (CommRingCat.ofHom (algebraMap T.V T.Fr)) ≫
      (Spec.map (CommRingCat.ofHom g) ≫ (Y₀ X Z).fromSpecStalk y ≫ inc₀ X Z) := by
    rw [hpt, he, Category.assoc]
  have hO := top_le_fromSpecStalk y ((algebraMap T.V T.Fr).comp g) ⊤ (memTop y)
  have hj := top_le_fromSpecStalk y ((algebraMap T.V T.Fr).comp g) ((L₀ X Z la).U j') hj'
  have hzV : ⊤ ≤ (Spec.map (CommRingCat.ofHom g) ≫ (Y₀ X Z).fromSpecStalk y ≫ inc₀ X Z) ⁻¹ᵁ
      X.F.U (j' PUnit.unit) := by
    have := top_le_fromSpecStalk y g (inc₀ X Z ⁻¹ᵁ X.F.U (j' PUnit.unit)) hk
    rw [← Category.assoc, Scheme.Hom.comp_preimage]
    exact this
  have hz : ⊤ ≤ (X.pt y'.1 ≫ X.inc) ⁻¹ᵁ X.F.U (j' PUnit.unit) := by
    rw [X.pt_inc, hpt']
    exact FlagMod.le_preimage_comp _ hzV
  obtain ⟨Q, t, hQ, ht⟩ := X.exists_chartFr_frBor y'.1 (j' PUnit.unit) hz
  have e2 := evI_ofSpace_eq_prod_mul_val X Z U la w T io y' _ hx₀ j' hO hj hz Q t hQ ht
  have e1 := val_fromSpecStalk y j' hj' ((algebraMap T.V T.Fr).comp g) w.1 hO hj
  have hu := GlobalTheory.T.chartFrame_change_diagonal_units_integral_frame X T io y' _ hpt' (j' PUnit.unit) hzV hz Q t hQ ht
  have ex : ∀ ix, ∃ u : T.Vˣ, Units.map (algebraMap T.V T.Fr : T.V →* T.Fr) u = t ix ^ GlobalTheory.AllWt.exOf Dw la 0 ix := by
    intro ix
    rcases ix with _ | ⟨σ, i⟩
    · exact ⟨1, by rw [FlagMod.exOf_none, zpow_zero, map_one]⟩
    · obtain ⟨u, hu⟩ := hu σ i
      exact ⟨u ^ GlobalTheory.AllWt.exOf Dw la 0 (some ⟨σ, i⟩), by rw [map_zpow]; congr 1; exact Units.ext hu⟩
  choose uf huf using ex
  have hP : Units.map (algebraMap T.V T.Fr : T.V →* T.Fr) (∏ ix, uf ix) = ∏ ix, t ix ^ GlobalTheory.AllWt.exOf Dw la 0 ix := by
    rw [map_prod]; exact Finset.prod_congr rfl fun ix _ => huf ix
  refine ⟨(∏ ix, uf ix)⁻¹, ?_⟩
  rw [e2, ← hP, e1, Units.coe_map, RingHom.comp_apply, ← mul_assoc, MonoidHom.coe_coe, ← map_mul, Units.inv_mul, map_one,
    one_mul]

end GlobalTheory.HSApp
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GermFactorizationUnitMulEvaluation

section

@[expose] public section



section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HSApp
theorem germ_eq_unit_mul_evaluation_ideal_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : TorFlag Y.d.Xo₂ Y.d.c₂) (la : AllWt.Weight (dat p i)) (w : space TF.X Z Y.U la) (y : Y₀ TF.X Z) (T : CDVR) (io : Y.d.c₂.F →+* T.Fr) (y' : IntFr Y.d.Xo₂ Y.d.c₂ T io) (g : (Y₀ TF.X Z).presheaf.stalk y →+* T.V), IsLocalHom g → (letI := io.toAlgebra; TF.X.ptY y'.1 = Spec.map (CommRingCat.ofHom ((algebraMap T.V T.Fr).comp g)) ≫ (Y₀ TF.X Z).fromSpecStalk y ≫ inc₀ TF.X Z) → ∀ (j' : (L₀ TF.X Z la).ι) (hj' : y ∈ (L₀ TF.X Z la).U j'), ∃ u : T.Vˣ, algebraMap T.V T.Fr (g (H0.germ j' y (memTop y) hj' w.1)) = algebraMap T.V T.Fr (u : T.V) * evI y' ((ofSpace TF.X Z Y.U la w : Cusp Z Y.U la) : Rul Y.d.Xo₂ Y.d.c₂) := by
  intro _ h2 _ _
  refine h2.imp fun Fm CH _ h => ?_
  obtain ⟨C, hC, x0, -⟩ := h
  exact ⟨C, hC, x0, fun x hx' hle ι p hp i hi Y hY Z TF la w y T io y' g _ hpt j' hj' =>
    germ_eq_unit_mul_evI_core TF.X Z Y.U la w y T io y' g hpt j' hj'⟩
end GlobalTheory.HSApp
end
end
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

theorem _root_.GlobalTheory.T.stalk_local_hom_germ_factorization : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : TorFlag Y.d.Xo₂ Y.d.c₂) (la : AllWt.Weight (dat p i)) (w : space TF.X Z Y.U la) (y : Y₀ TF.X Z) (T : CDVR) (io : Y.d.c₂.F →+* T.Fr) (y' : IntFr Y.d.Xo₂ Y.d.c₂ T io) (g : (Y₀ TF.X Z).presheaf.stalk y →+* T.V), IsLocalHom g → (letI := io.toAlgebra; TF.X.ptY y'.1 = Spec.map (CommRingCat.ofHom ((algebraMap T.V T.Fr).comp g)) ≫ (Y₀ TF.X Z).fromSpecStalk y ≫ inc₀ TF.X Z) → ∀ (j' : (L₀ TF.X Z la).ι) (hj' : y ∈ (L₀ TF.X Z la).U j'), ∃ u : T.Vˣ, algebraMap T.V T.Fr (g (H0.germ j' y (memTop y) hj' w.1)) = algebraMap T.V T.Fr (u : T.V) * evI y' ((ofSpace TF.X Z Y.U la w : Cusp Z Y.U la) : Rul Y.d.Xo₂ Y.d.c₂) := by
  first | exact @_root_.GlobalTheory.HSApp.germ_eq_unit_mul_evaluation_ideal_alt | exact _root_.GlobalTheory.HSApp.germ_eq_unit_mul_evaluation_ideal_alt | (intros; apply _root_.GlobalTheory.HSApp.germ_eq_unit_mul_evaluation_ideal_alt <;> assumption)
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsSectionOrderBoundHilbertSamuel

section

@[expose] public section



section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HSApp

theorem exists_subspace_vanishing_order_le_phi_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : TorFlag Y.d.Xo₂ Y.d.c₂), ∀ la ∈ ({(⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁, (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).ub} : Set (AllWt.Weight (dat p i))), ∀ y ∈ (U₀ TF.X Z : Set (Y₀ TF.X Z))ᶜ, ∀ ν, Centred y ν → ∀ φ : ℝ, PhiAt TF.X Z y ν φ → ∃ w ∈ space TF.X Z Y.U la, ∀ (j' : (L₀ TF.X Z la).ι) (hj' : y ∈ (L₀ TF.X Z la).U j'), ν (H0.germ j' y (memTop y) hj' w) ≠ 0 ∧ ∀ m : ℤ, ν (H0.germ j' y (memTop y) hj' w) = ((Multiplicative.ofAdd (-m) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) → (m : ℝ) ≤ φ / 2500 := by
  intro h1 h2 h3 h4
  refine ((_root_.GlobalTheory.T.exists_form_cusp_value_bound_alt h1 h2 h3 h4).and (_root_.GlobalTheory.T.stalk_local_hom_germ_factorization h1 h2 h3 h4)).imp fun Fm CH _ h => ?_
  obtain ⟨⟨C, hC, x0, hx⟩, ⟨C', hC', x1, hx1⟩⟩ := h
  refine ⟨C, hC, max x0 x1, fun x hx' hle ι p hp i hi Y hY Z TF la hla y hy ν hν φ hφ => ?_⟩
  obtain ⟨T, io, y', g, ρ, φT, hρ, hφT, rfl, hpt, hval⟩ := hφ
  haveI hg : IsLocalHom g := isLocalHom_of_centred hν T g ρ hρ hval
  obtain ⟨w, hw0, hwb⟩ := hx x hx' ((le_max_left _ _).trans hle) ι p hp i hi Y hY Z TF la hla y hy T io y' g φT hg hφT hpt
  refine ⟨w.1, w.2, fun j' hj' => ?_⟩
  obtain ⟨u, hu⟩ := hx1 x hx' ((le_max_right _ _).trans hle) ι p hp i hi Y hY Z TF la w y T io y' g hg hpt j' hj'
  have hu0 : algebraMap T.V T.Fr (u : T.V) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective T.V T.Fr)).2 u.ne_zero
  have hg0 : algebraMap T.V T.Fr (g (H0.germ j' y (memTop y) hj' w.1)) ≠ 0 := by
    rw [hu]; exact mul_ne_zero hu0 hw0
  have hgerm : H0.germ j' y (memTop y) hj' w.1 ≠ 0 := by
    intro h; rw [h, map_zero, map_zero] at hg0; exact hg0 rfl
  have hne : ν (H0.germ j' y (memTop y) hj' w.1) ≠ 0 := fun h => hgerm (hν.2.2 _ h)
  refine ⟨hne, fun m hm => ?_⟩
  have hv := hval _ hne
  rw [hm, log_ofAdd_neg, hu, vV_mul hu0 hw0, vV_algebraMap_unit, zero_add] at hv
  have e : (m : ℝ) = ρ * (vV T.V (evI y' ((ofSpace TF.X Z Y.U la w : Cusp Z Y.U la) : Rul Y.d.Xo₂ Y.d.c₂)) : ℝ) := by
    rw [← hv]; push_cast; ring
  rw [e, mul_div_assoc]
  exact mul_le_mul_of_nonneg_left hwb hρ.le
end GlobalTheory.HSApp
end
end
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

theorem _root_.GlobalTheory.T.exists_section_order_bound_hilbertSamuel_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : TorFlag Y.d.Xo₂ Y.d.c₂), ∀ la ∈ ({(⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁, (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).ub} : Set (AllWt.Weight (dat p i))), ∀ y ∈ (U₀ TF.X Z : Set (Y₀ TF.X Z))ᶜ, ∀ ν, Centred y ν → ∀ φ : ℝ, PhiAt TF.X Z y ν φ → ∃ w ∈ space TF.X Z Y.U la, ∀ (j' : (L₀ TF.X Z la).ι) (hj' : y ∈ (L₀ TF.X Z la).U j'), ν (H0.germ j' y (memTop y) hj' w) ≠ 0 ∧ ∀ m : ℤ, ν (H0.germ j' y (memTop y) hj' w) = ((Multiplicative.ofAdd (-m) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) → (m : ℝ) ≤ φ / 2500 := by
  first | exact @_root_.GlobalTheory.HSApp.exists_subspace_vanishing_order_le_phi_alt | exact _root_.GlobalTheory.HSApp.exists_subspace_vanishing_order_le_phi_alt | (intros; apply _root_.GlobalTheory.HSApp.exists_subspace_vanishing_order_le_phi_alt <;> assumption)
end
end
end
end
