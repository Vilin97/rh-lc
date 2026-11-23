module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound
public import Development.AbelianVarietyTheory.Definitions.Divisors.BarCompSubsetClosure
public import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexUniformizationLawsOfGoodDeepCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralFramePointStalk
public import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwSecOfConst
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FlagComponentFramedPointFrame
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKeySectionFourthRootPerComponentStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitSectionThetaKeyRuleWeightFourStatement
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KeyFamOne
import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.BrData
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AbelianVarietyTheory.Definitions.Divisors.CommGroupMulMulEqMulInvMulMulMul
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
import Development.AbelianVarietyTheory.Definitions.Divisors.LinearIndependentBasisCoords
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnitaryWeightExponentVectorSignatureWeightMuZero
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNumberFieldPoint
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ArchimedeanSectionIntegralFrame
import Mathlib.Tactic.Linter.Style
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FlatVal

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralFramePointStalkCompat

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

namespace GlobalTheory.FlatValZero

section Gen

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions
  GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.FlatCore GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ}

theorem nonempty_keySec (hL : Laws U x) : Nonempty (KeySec Xo c) := by
  obtain ⟨κ, k₁, k₂, -, k₄, -, k₆, -, -⟩ := GlobalTheory.KeyFamClosing.keyFam_one
  let e : Fin (Fintype.card (Σ τ : E →+* ℂ, Fin (Dw.mult τ))) ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ) :=
    (Fintype.equivFin _).symm
  obtain ⟨K, hKmem, hKval⟩ := GlobalTheory.T.exists_unit_section_thetaKeyRule_weightFour κ k₁ k₂ k₆ E H Dw l Xo c _ e hL.pos
  have hσ0 := goodEmb_goodOf c c.F.val.toRingHom
  obtain ⟨ρ, -⟩ := GlobalTheory.T.exists_keySection_fourthRoot_perComponent κ k₁ k₂ k₆ k₄ E H Dw l Xo c _ e _ r (U _) K hσ0 (hL.unf _ hσ0) hL.geo hL.pos
    hKmem hKval
  exact ⟨ρ⟩

def unitsV (T : CDVR) : Submonoid T.Fr where
  carrier := {z | z ≠ 0 ∧ vV T.V z = 0}
  one_mem' := ⟨one_ne_zero, by simp [vV]⟩
  mul_mem' := fun {a b} ha hb => ⟨mul_ne_zero ha.1 hb.1, by rw [vV_mul ha.1 hb.1, ha.2, hb.2, add_zero]⟩

end Gen

end GlobalTheory.FlatValZero

open GlobalTheory.FlatValZero


end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.IntegralFramePointStalkCompat

section

@[expose] public section

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
namespace GlobalTheory.FlatValZero
section Gen
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions
  GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.FlatCore GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ}
theorem twisted_section_flat_valuation (hP : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems) (hL : Laws U x) (hFE : FlatExists U x) (Z : Comp Xo c)
    (w : Psi H → ℤ) : ∃ t : TwSec U x Z (wtOf Dw (parWt Dw w) 0), ∀ (T : CDVR) (io : c.F →+* T.Fr)
      (y : IntFr Xo c T io), (∀ a, a ≠ 0 → vV T.V (io a) = 0) → evI y (idem Z) ≠ 0 → vV T.V (evI y t.sig) = 0 := by
  have hp : HasPts U Z := GlobalTheory.FlatLine.hasPts U hL.pos hL.good hL.unf Z
  let sF : ∀ τ, FlatSec U x Z τ := fun τ => (hFE.nonempty Z τ).some
  have hK := nonempty_keySec hL
  let s := FlatSec.shift hp sF w
  have hδ := GlobalTheory.FlatTwisting.finite_sum_flDefect (Dw := Dw) (c := c) w
  refine ⟨TwSec.ofConst s (by convert hδ) (GlobalTheory.FlatTwisting.mul_sig_mem_cuspOn hK hL.unf hL.pos s) fun G hG f hf => ?_,
    fun T io y hio hZ => ?_⟩
  · have h := GlobalTheory.FlatTwisting.mul_sig_mem_cuspOn hK hL.unf hL.pos (w := -w) (s.symm.copy rfl rfl)
      (G + wtOf Dw (parWt Dw w) 0) (Even.add hG (even_wtOf _ _)) f hf
    rw [GlobalTheory.FlatTwisting.wtOf_parWt_neg, add_neg_cancel_right] at h
    exact h
  letI := io.toAlgebra
  have hLies : LiesOn Z y.1 := by
    by_contra hn
    exact hZ ((idem_mem_suppOn Z) T.Fr y.1 ((liesOff_iff Z y.1).2 hn))
  have hid : evI y (idem Z) = 1 := by
    have e := evI_mul y (idem Z) (idem Z)
    rw [idem_mul_idem] at e
    exact mul_left_cancel₀ hZ (by rw [mul_one]; exact e.symm)
  let ev : Rul Xo c →* T.Fr :=
    ⟨⟨evI y, by rw [← mul_one (evI y 1), ← hid, ← evI_mul, one_mul]⟩, evI_mul y⟩
  have hsig : ∀ τ, ev (sF τ).sig ∈ unitsV T := fun τ => by
    have hn := _root_.GlobalTheory.FlatCore.Bdry.nval_evI_eq_zero_alt hP hP.q2 E H Dw l Xo c r U x hL Z τ
      (ArchSec.ofConst (sF τ)) T io y hio hLies
    have hev0 : evI y (sF τ).sig ≠ 0 := by
      intro h0
      rw [show (ArchSec.ofConst (sF τ)).sig = (sF τ).sig from rfl, h0, nval_zero] at hn
      exact EReal.top_ne_zero hn
    refine ⟨hev0, ?_⟩
    rw [show (ArchSec.ofConst (sF τ)).sig = (sF τ).sig from rfl, nval_of_ne hev0] at hn
    have : ((vV T.V (evI y (sF τ).sig) : ℝ) / ((1 : ℕ) : ℝ) : ℝ) = 0 := by exact_mod_cast hn
    show vV T.V (evI y (sF τ).sig) = 0
    simpa using this
  have hinv : ∀ τ, ev (sF τ).inv ∈ unitsV T := fun τ => by
    have e : ev (sF τ).sig * ev (sF τ).inv = 1 := by
      rw [← map_mul, (sF τ).mul_inv]; exact hid
    have h2 : ev (sF τ).inv ≠ 0 := right_ne_zero_of_mul_eq_one e
    refine ⟨h2, ?_⟩
    have h3 := vV_mul (V := T.V) (hsig τ).1 h2
    rw [e, (hsig τ).2, zero_add, show vV T.V (1 : T.Fr) = 0 by simp [vV]] at h3
    exact h3.symm
  have hprod : ev s.sig ∈ unitsV T := by
    rw [(FlatSec.shift_spec hp sF w).1, map_mul, map_prod]
    refine (unitsV T).mul_mem (by rw [show ev (idem Z) = 1 from hid]; exact (unitsV T).one_mem)
      ((unitsV T).prod_mem fun τ _ => ?_)
    rw [(ConstSec.zpow_spec (sF τ) (-w τ)).1, map_mul, map_mul, map_pow, map_pow]
    exact (unitsV T).mul_mem (by rw [show ev (idem Z) = 1 from hid]; exact (unitsV T).one_mem)
      ((unitsV T).mul_mem ((unitsV T).pow_mem (hsig τ) _) ((unitsV T).pow_mem (hinv τ) _))
  exact hprod.2
end Gen
end GlobalTheory.FlatValZero
open GlobalTheory.FlatValZero
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
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IntegralFramePointStalkCompat

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
namespace GlobalTheory.FlatValZero
section Gen
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions
  GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.FlatCore GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ}
end Gen
end GlobalTheory.FlatValZero
open GlobalTheory.FlatValZero

theorem GlobalTheory.FlatValZero.flat_val_zero_at_integral_point_stalk : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y _ _ => ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : TorFlag Y.d.Xo₂ Y.d.c₂) (y : Y₀ TF.X Z) (T : CDVR) (io : Y.d.c₂.F →+* T.Fr) (y' : IntFr Y.d.Xo₂ Y.d.c₂ T io) (g : (Y₀ TF.X Z).presheaf.stalk y →+* T.V), IsLocalHom g → (letI := io.toAlgebra; TF.X.ptY y'.1 = Spec.map (CommRingCat.ofHom ((algebraMap T.V T.Fr).comp g)) ≫ (Y₀ TF.X Z).fromSpecStalk y ≫ inc₀ TF.X Z) → evI y' (GlobalTheory.FlatLine.idem Z) ≠ 0 → ∀ w : AllWt.Psi p.T.Q.H → ℤ, ∃ t : GlobalTheory.FlatTw.TwSec Y.U (xiR (Fm.D x ι)) Z (AllWt.wtOf (dat p i) (GlobalTheory.FlatLine.parWt (dat p i) w) 0), vV T.V (evI y' t.sig) = 0 := by
  intro hP hD _ hF
  have F := _root_.GlobalTheory.CovTop.FlatVal.flat_val_alt hF
  unfold _root_.GlobalTheory.CovTop.CoversCondition _root_.GlobalTheory.CovTop.LiftsCondition at *
  refine (hD.and F).imp fun Fm CH _ h => ?_
  obtain ⟨⟨C1, h1, e1⟩, ⟨C2, h2, e2⟩⟩ := h
  refine ⟨C1, h1, ?_⟩
  obtain ⟨x0, hx0⟩ := e1.and e2
  refine ⟨x0, fun x hx hle ι p hp i hi Y hY Z TF y T io y' g hg hpt hZ w => ?_⟩
  obtain ⟨-, hB⟩ := hx0 x hx hle ι p hp
  have hFE := (hB i hi Y hY).2.2.1
  have hL := GlobalTheory.LawsDeep.laws_deep _ p.T _ Y _ _ p.fw.laws ⟨Nat.le_add_left _ _, i.2⟩ hY.1
  obtain ⟨t, ht⟩ := _root_.GlobalTheory.FlatValZero.twisted_section_flat_valuation hP hL hFE Z w
  refine ⟨t, ht T io y' (fun a ha => ?_) hZ⟩
  have ho : ∀ a, io a ∈ (algebraMap T.V T.Fr).range := fun a => by
    letI := io.toAlgebra
    have h1 := ptY_str TF.X y'.1
    rw [hpt, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, Category.assoc] at h1
    obtain ⟨b, hb⟩ := Spec.map_surjective
      (Spec.map (CommRingCat.ofHom g) ≫ ((Y₀ TF.X Z).fromSpecStalk y ≫ inc₀ TF.X Z) ≫ flagStr TF.X)
    rw [← hb, ← Spec.map_comp] at h1
    exact ⟨b.hom a, congrArg (fun q => CommRingCat.Hom.hom q a) (Spec.map_injective h1)⟩
  have ha' : io a ≠ 0 := (map_ne_zero io).2 ha
  have h1 := (GlobalTheory.KeyValZero.mem_range_iff T _).1 (ho a)
  have h2 := (GlobalTheory.KeyValZero.mem_range_iff T _).1 (ho a⁻¹)
  have h3 := vV_mul (V := T.V) ha' ((map_ne_zero io).2 (inv_ne_zero ha))
  rw [← map_mul, mul_inv_cancel₀ ha, map_one, show vV T.V (1 : T.Fr) = 0 by simp [vV]] at h3
  omega
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

theorem _root_.GlobalTheory.T.integral_frame_point_stalk_compat_third_place_series : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y _ _ => ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : TorFlag Y.d.Xo₂ Y.d.c₂) (y : Y₀ TF.X Z) (T : CDVR) (io : Y.d.c₂.F →+* T.Fr) (y' : IntFr Y.d.Xo₂ Y.d.c₂ T io) (g : (Y₀ TF.X Z).presheaf.stalk y →+* T.V), IsLocalHom g → (letI := io.toAlgebra; TF.X.ptY y'.1 = Spec.map (CommRingCat.ofHom ((algebraMap T.V T.Fr).comp g)) ≫ (Y₀ TF.X Z).fromSpecStalk y ≫ inc₀ TF.X Z) → evI y' (GlobalTheory.FlatLine.idem Z) ≠ 0 → ∀ w : AllWt.Psi p.T.Q.H → ℤ, ∃ t : GlobalTheory.FlatTw.TwSec Y.U (xiR (Fm.D x ι)) Z (AllWt.wtOf (dat p i) (GlobalTheory.FlatLine.parWt (dat p i) w) 0), vV T.V (evI y' t.sig) = 0 := by
  first | exact @_root_.GlobalTheory.FlatValZero.flat_val_zero_at_integral_point_stalk | exact _root_.GlobalTheory.FlatValZero.flat_val_zero_at_integral_point_stalk | (intros; apply _root_.GlobalTheory.FlatValZero.flat_val_zero_at_integral_point_stalk <;> assumption)
end
end
end
end
