module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Hypotheses2
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InterNumDetNonposSplitTorus
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
public import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
public import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ToroidalChartsForFan
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommonRestrIsoTens
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EffectiveGenerationCanonicalNefNumberField
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
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaOfTranslDiff
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Data.Nat.Choose.Multinomial
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsChartOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
import Development.AbelianVarietyTheory.Definitions.Divisors.LinearIndependentBasisCoords
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnitaryWeightExponentVectorSignatureWeightMuZero
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.EllipsoidStA
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagSpaceComponentSmoothProjectiveConnected
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyKodairaSpencerIdentificationOffBoundary
import Mathlib.Algebra.Order.Star.Int
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.BaseWeightLineBundleIsNef
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyCuspFrame
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.LogCanonicalCriterionBoundary
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.HodgeBundleAmpleOnRegularLocus
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.KodairaSpencerIsoFlagTangentPsiSet

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EffectiveGenerationCanonicalNefNumberFieldStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

theorem _root_.GlobalTheory.T.effective_generation_canonical_nef_numberField : GlobalTheory.Published.NadelVanishingAndNonKltDivisor → GlobalTheory.Published.NefNumerics → ∀ (F : Type) [Field F] [NumberField F] (Y : Scheme.{0}) (p : Y ⟶ Sp F) (D : ℕ) [SmoothOfRelativeDimension D p], IsProjOver p → GeometricallyConnected p → 1 ≤ D → letI := algebraΓOfHom p; ∀ (K : CanonLB p D) (N N' B : LB Y) (hN : N.IsLB) (hN' : N'.IsLB) (hB : B.IsLB) (a m : ℕ) (y : Y), IsNef F N → IsNef F N' → (D + 1).choose 2 < m → (∃ (N₁ N₂ : LB Y) (h₁ : N₁.IsLB) (h₂ : N₂.IsLB), 0 < a ∧ a • cls N hN = cls N₁ h₁ + cls N₂ h₂ ∧ AmpleAt N₁ y ∧ IsNef F N₂) → cls B hB = m • cls N hN + cls N' hN' → ∃ s : (tens K.bundle B).Sec, y ∈ nonzeroLocus s := by
  first | exact @GlobalTheory.EffGen.effective_generation | exact GlobalTheory.EffGen.effective_generation | (intros; apply GlobalTheory.EffGen.effective_generation <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSecCanonTensPullId

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.ModifRefl

theorem exists_sec_canon_tens_pull_id : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (D : ℕ) [SmoothOfRelativeDimension D p] [SmoothOfRelativeDimension D (𝟙 Y ≫ p)] (B : LB Y), B.IsLB → ∀ (s : H0 p (tens (CanonLB.all p D).bundle B) ⊤) (y : Y), y ∈ nonzeroLocus (toSec s) → ∃ s' : H0 (𝟙 Y ≫ p) (tens (CanonLB.all (𝟙 Y ≫ p) D).bundle (B.pull (𝟙 Y))) ⊤, y ∈ nonzeroLocus (toSec s') := by
  intro k _ Y p D _ inst2 B hB s y hy
  revert inst2
  generalize hq : 𝟙 Y ≫ p = q
  simp only [Category.id_comp] at hq
  subst hq
  intro inst2
  have hK : (CanonLB.all p D).bundle.IsLB := (CanonLB.all p D).isLB
  have hBp : (B.pull (𝟙 Y)).IsLB := LB.isLB_linComb hB _ _
  have H1 : LBIso (tens (B.pull (𝟙 Y)) (CanonLB.all p D).bundle) (tens B (CanonLB.all p D).bundle) :=
    GlobalTheory.CechPic.tens_congr_left hK (DescendedPrincipal.lbIso_pull_id hB)
  have H : LBIso (tens (CanonLB.all p D).bundle (B.pull (𝟙 Y))) (tens (CanonLB.all p D).bundle B) :=
    LBIso.trans (isLB_tens hK hBp) (isLB_tens hBp hK) (isLB_tens hK hB)
      (GlobalTheory.CechPic.tens_comm_iso hK hBp)
      (LBIso.trans (isLB_tens hBp hK) (isLB_tens hB hK) (isLB_tens hK hB) H1
        (GlobalTheory.CechPic.tens_comm_iso hB hK))
  obtain ⟨t, ht⟩ := exists_sec_nonzeroLocus_eq_of_lbIso (isLB_tens hK hBp) (isLB_tens hK hB) H (toSec s)
  refine ⟨H0.ofSec p ⊤ t, ?_⟩
  have e : toSec (H0.ofSec p ⊤ t) = t := by
    unfold toSec
    exact Equiv.ofBijective_symm_apply_apply _ _ _
  rw [e, ht]
  exact hy

end GlobalTheory.ModifRefl
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalIntegralWeightSection

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

namespace GlobalTheory.HSApp

theorem gapGe_stdWt {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H) :
    GapGe 1 (GlobalTheory.CompHt.stdWt (Psi H) (Dw.p + Dw.q) : AllWt.Weight Dw) := by
  intro τ k hk
  simp only [gap, dif_pos hk, GlobalTheory.CompHt.stdWt]
  push_cast
  omega

theorem gapGe_sub_smul {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
    (m : ℕ) (b : AllWt.Weight Dw) (h : GapGe (m : ℤ) b) :
    GapGe 0 (b - m • (GlobalTheory.CompHt.stdWt (Psi H) (Dw.p + Dw.q) : AllWt.Weight Dw)) := by
  intro τ k hk
  have h1 := h τ k hk
  simp only [gap, dif_pos hk, Pi.sub_apply, Pi.smul_apply, GlobalTheory.CompHt.stdWt] at h1 ⊢
  rw [nsmul_eq_mul, nsmul_eq_mul]
  push_cast
  linarith

theorem cls_common_nsmul {Y : Scheme.{0}} {Λ : Type} [AddCommGroup Λ] {B : Λ → LB Y} (C : Common B) (n : ℕ) (a : Λ) :
    cls (B (n • a)) (C.isLB (n • a)) = n • cls (B a) (C.isLB a) := by
  induction n with
  | zero =>
    have h := cls_common_add C 0 0
    simp only [add_zero] at h
    simp only [zero_nsmul]
    exact left_eq_add.1 h
  | succ n ih =>
    rw [succ_nsmul, cls_common_add C, ih, succ_nsmul]

end GlobalTheory.HSApp
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ExistsVanBdSectionNonzeroOfCanonicalTwistNonzero

section

@[expose] public section

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
namespace GlobalTheory.CuspNonvanishing
theorem exists_vanBd_section_nonzero_of_canonical_twist_nonzero : _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.GrothendieckDeformation → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed (Xo := Xo) (c := c) → ∀ (M : Modif (str₀ TF.X Z) (U₀ TF.X Z) (dimFlag Dw)) (ω : CanId M) (la : AllWt.Weight Dw) (g : H0 M.str (tens M.K.bundle ((L₀ TF.X Z (la - FlagTan.kap Dw)).pull M.σ)) ⊤) (z : M.X), z ∈ M.off → z ∈ nonzeroLocus (toSec g) → ∃ s ∈ vanBd TF.X Z la, M.σ z ∈ nonzeroLocus (toSec s) := by
  intro hP hG E _ _ _ H Dw l Xo c TF Z hF M ω la g z hz hg
  have hs : FlagTan.kap Dw + (la - FlagTan.kap Dw) = la := by abel
  set C := ((common₀ TF.X Z).pull M.σ).canChart M.K.isLB hs
  obtain ⟨m, hm⟩ := (M.bijective_pullOff (isLB_L₀ TF.X Z la)).2 ((C.mulEquiv ω.unit).symm (H0.restr le_top g))
  have hm' : C.mul ω.ω (M.pullOff m) = H0.restr le_top g := by
    rw [hm, ← ProdChart.mulEquiv_apply C ω.unit, LinearEquiv.apply_symm_apply]
  obtain ⟨s, hsv, hsr⟩ := (_root_.GlobalTheory.T.log_canonical_criterion_boundary hP hG E H Dw l Xo c TF Z hF M ω (la - FlagTan.kap Dw) la hs m).2 ⟨g, hm'.symm⟩
  refine ⟨s, hsv, ?_⟩
  obtain ⟨t, ha, hb, hc⟩ := C.cover z
  have e := C.germ_mul ω.ω (M.pullOff m) t z hz ha hb hc
  rw [hm', H0.germ_restr] at e
  have hu : IsUnit (H0.germ (C.c t) z (memTop z) hc g) := by
    rw [← ger_toSec]; exact (isUnit_ger_iff _ hc).2 hg
  rw [e] at hu
  have hu2 := isUnit_of_mul_isUnit_right hu
  have e2 := H0.germ_pull M.σ M.off_eq.le (C.b t) z hz hb m
  change IsUnit (H0.germ (C.b t) z hz hb (H0.pull M.σ M.off_eq.le m)) at hu2
  rw [e2] at hu2
  have hu3 := (isUnit_map_iff (M.σ.stalkMap z).hom _).1 hu2
  rw [← hsr] at hu3
  erw [H0.germ_restr] at hu3
  rw [← ger_toSec] at hu3
  exact (isUnit_ger_iff _ _).1 hu3
end GlobalTheory.CuspNonvanishing
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

theorem _root_.GlobalTheory.T.exists_form_nonvanishing_at_cusp : _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.GrothendieckDeformation → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed (Xo := Xo) (c := c) → ∀ (M : Modif (str₀ TF.X Z) (U₀ TF.X Z) (dimFlag Dw)) (ω : CanId M) (la : AllWt.Weight Dw) (g : H0 M.str (tens M.K.bundle ((L₀ TF.X Z (la - FlagTan.kap Dw)).pull M.σ)) ⊤) (z : M.X), z ∈ M.off → z ∈ nonzeroLocus (toSec g) → ∃ s ∈ vanBd TF.X Z la, M.σ z ∈ nonzeroLocus (toSec s) := by
  first | exact @_root_.GlobalTheory.CuspNonvanishing.exists_vanBd_section_nonzero_of_canonical_twist_nonzero | exact _root_.GlobalTheory.CuspNonvanishing.exists_vanBd_section_nonzero_of_canonical_twist_nonzero | (intros; apply _root_.GlobalTheory.CuspNonvanishing.exists_vanBd_section_nonzero_of_canonical_twist_nonzero <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.GloballyGeneratedOnOpenOfWeightGapGe

section

@[expose] public section

section
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
namespace GlobalTheory.HSApp
theorem exists_canonical_section_ne_zero_at : _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.NefNumerics → GlobalTheory.Published.NadelVanishingAndNonKltDivisor → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalChartsForFan → GlobalTheory.Published.SemiAbelianLieSeminegative → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed (Xo := Xo) (c := c) → 1 ≤ dimFlag Dw → ∀ (hV : IsVariety₀ TF.X Z) (la : AllWt.Weight Dw), GapGe (((dimFlag Dw + 1).choose 2 + 1 : ℕ) : ℤ) (la - FlagTan.kap Dw) → letI := hV.1; ∀ y ∈ U₀ TF.X Z, ∃ g : H0 (str₀ TF.X Z) (tens (CanonLB.all (str₀ TF.X Z) (dimFlag Dw)).bundle (L₀ TF.X Z (la - FlagTan.kap Dw))) ⊤, y ∈ nonzeroLocus (toSec g) := by
  intro hP hN hNa hS hT hL E _ _ _ H Dw l Xo c TF Z hF hD hV la hg
  letI := hV.1
  intro y hy
  set std : AllWt.Weight Dw := GlobalTheory.CompHt.stdWt (Psi H) (Dw.p + Dw.q) with hstd_def
  set m : ℕ := (dimFlag Dw + 1).choose 2 + 1 with hm_def
  have hstd : GapGe 1 std := gapGe_stdWt Dw
  have hmu : GapGe 0 (la - FlagTan.kap Dw - m • std) := gapGe_sub_smul m _ hg
  letI := algebraΓOfHom (str₀ TF.X Z)
  have nef : ∀ w : AllWt.Weight Dw, GapGe 0 w → IsNef c.F (L₀ TF.X Z w) :=
    fun w hw => _root_.GlobalTheory.T.base_weight_line_bundle_is_nef hP hN hL E H Dw l Xo c TF Z hF w hw
  obtain ⟨mu, hmu0, m', hm', hA⟩ := _root_.GlobalTheory.T.hodge_bundle_ample_on_regular_locus hP hN hS hT E H Dw l Xo c TF Z hF std hstd y hy
  have C := common₀ TF.X Z
  have e₁ : m' • cls (L₀ TF.X Z std) (isLB_L₀ TF.X Z std) =
      cls (L₀ TF.X Z (m' • std - mu)) (isLB_L₀ TF.X Z _) + cls (L₀ TF.X Z mu) (isLB_L₀ TF.X Z mu) := by
    have h := cls_common_add (common₀ TF.X Z) (m' • std - mu) mu
    rw [sub_add_cancel] at h
    rw [← h]
    exact (cls_common_nsmul (common₀ TF.X Z) m' std).symm
  have e₂ : cls (L₀ TF.X Z (la - FlagTan.kap Dw)) (isLB_L₀ TF.X Z _) =
      m • cls (L₀ TF.X Z std) (isLB_L₀ TF.X Z std) + cls (L₀ TF.X Z (la - FlagTan.kap Dw - m • std)) (isLB_L₀ TF.X Z _) := by
    have h := cls_common_add (common₀ TF.X Z) (m • std) (la - FlagTan.kap Dw - m • std)
    rw [add_sub_cancel] at h
    rw [h]
    exact congrArg (· + _) (cls_common_nsmul (common₀ TF.X Z) m std)
  obtain ⟨s, hs⟩ := GlobalTheory.T.effective_generation_canonical_nef_numberField hNa hN c.F (Y₀ TF.X Z) (str₀ TF.X Z) (dimFlag Dw) hV.2.1 hV.2.2 hD
    (CanonLB.all _ _) (L₀ TF.X Z std) (L₀ TF.X Z (la - FlagTan.kap Dw - m • std)) (L₀ TF.X Z (la - FlagTan.kap Dw))
    (isLB_L₀ TF.X Z _) (isLB_L₀ TF.X Z _) (isLB_L₀ TF.X Z _) m' m y (nef std (hstd.mono (by norm_num))) (nef _ hmu)
    (by omega) ⟨_, _, isLB_L₀ TF.X Z (m' • std - mu), isLB_L₀ TF.X Z mu, hm', e₁, hA, nef mu hmu0⟩ e₂
  refine ⟨H0.ofSec _ ⊤ s, ?_⟩
  rwa [show toSec (H0.ofSec (str₀ TF.X Z) ⊤ s) = s from H0.bijective_ofSec_top.1 (ofSec_toSec _)]
theorem globally_generated_on_open_of_weight_gap_ge : _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.NadelVanishingAndNonKltDivisor → GlobalTheory.Published.Principalisation → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalChartsForFan → GlobalTheory.Published.SemiAbelianLieSeminegative → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), FnAlgClosed (Xo := Xo) (c := c) → 1 ≤ dimFlag Dw → ∀ la : AllWt.Weight Dw, GapGe (((dimFlag Dw + 1).choose 2 + 1 : ℕ) : ℤ) (la - FlagTan.kap Dw) → CuspIso TF.X Z U la → FreeOnOpen TF.X Z U la := by
  intro hP hG hQ hNa hPr hS hT hL E _ _ _ H Dw l Xo c TF Z r U hF hD la hg hC
  have hV := @GlobalTheory.VarFlag.isVariety₀_flag E _ _ _ H Dw l Xo c TF Z hF
  have hpq : 1 ≤ Dw.p + Dw.q := by
    by_contra h
    have h0 : Dw.p + Dw.q = 0 := by omega
    have : dimFlag Dw = 0 := by
      unfold GlobalTheory.FlagTan.dimFlag
      rw [h0]
      simp
    omega
  let M : Modif (str₀ TF.X Z) (U₀ TF.X Z) (dimFlag Dw) := Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)
  obtain ⟨ω⟩ := GlobalTheory.CompHS.canId_nonempty hP.p5 E H Dw l Xo c TF.Y TF.X Z M (fun K _ _ y => _root_.GlobalTheory.T.flag_tangent_kodaira_spencer_iso hP hG E H Dw l Xo c K y hpq)
  intro y hy
  rw [mem_support_baseIdeal]
  push_neg
  obtain ⟨g, hgy⟩ := _root_.GlobalTheory.HSApp.exists_canonical_section_ne_zero_at hP hQ.nef hNa hS hT hL E H Dw l Xo c TF Z hF hD hV la hg y hy
  haveI := hV.1
  haveI : SmoothOfRelativeDimension (dimFlag Dw) (𝟙 (Y₀ TF.X Z) ≫ str₀ TF.X Z) := M.smooth
  obtain ⟨g', hg'⟩ := GlobalTheory.ModifRefl.exists_sec_canon_tens_pull_id c.F (Y₀ TF.X Z) (str₀ TF.X Z) (dimFlag Dw) _ (isLB_L₀ TF.X Z _) g y hgy
  have hyM : (y : M.X) ∈ M.off := by
    rw [M.off_eq]
    exact hy
  obtain ⟨s, hs, hsy⟩ := _root_.GlobalTheory.T.exists_form_nonvanishing_at_cusp hP hG E H Dw l Xo c TF Z hF M ω la g' y hyM hg'
  exact ⟨s, hC.2 hs, hsy⟩
end GlobalTheory.HSApp
end
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

theorem _root_.GlobalTheory.T.hodge_bundle_base_point_free_on_open : _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.NadelVanishingAndNonKltDivisor → GlobalTheory.Published.Principalisation → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalChartsForFan → GlobalTheory.Published.SemiAbelianLieSeminegative → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), FnAlgClosed (Xo := Xo) (c := c) → 1 ≤ dimFlag Dw → ∀ la : AllWt.Weight Dw, GapGe (((dimFlag Dw + 1).choose 2 + 1 : ℕ) : ℤ) (la - FlagTan.kap Dw) → CuspIso TF.X Z U la → FreeOnOpen TF.X Z U la := by
  first | exact @_root_.GlobalTheory.HSApp.globally_generated_on_open_of_weight_gap_ge | exact _root_.GlobalTheory.HSApp.globally_generated_on_open_of_weight_gap_ge | (intros; apply _root_.GlobalTheory.HSApp.globally_generated_on_open_of_weight_gap_ge <;> assumption)
end
end
end
