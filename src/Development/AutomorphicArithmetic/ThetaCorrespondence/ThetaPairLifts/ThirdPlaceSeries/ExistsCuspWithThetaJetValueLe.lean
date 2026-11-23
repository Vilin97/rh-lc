module

public import Development.AbelianVarietyTheory.Definitions.Divisors.PolyBetween
public import Development.AbelianVarietyTheory.Definitions.Divisors.BarCompSubsetClosure
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.EightDvdNCol
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExtensionDvrFlagLift
public import Development.AbelianVarietyTheory.Definitions.Foundations.NonnegOfMemCStarSet
public import Formalism.LocalToGlobal.ProjectiveLattices.ChartDirectionsIntegral
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermCut
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFramedPointBaseChangeAlgHom
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BalancedPeriodSlopeMulRamificationIndexStatement
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.GeneratesOfNonzeroOnSpecialFibre
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ThetaRuleIntegralPointValueBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IntChartFrTruncExists
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
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
import Development.AbelianVarietyTheory.Definitions.Divisors.CommGroupMulMulEqMulInvMulMulMul
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
import Development.AbelianVarietyTheory.Definitions.Divisors.LinearIndependentBasisCoords
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnitaryWeightExponentVectorSignatureWeightMuZero
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.EllipsoidStA
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsIsNabUncond
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.StarRingExtOfStar
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsThetaRuleValueLeCoverCharZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCuspOnRestrict
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaExponentsDominantLastEntryOneDegree
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaRulesExistAndCusp
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftGaps

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExtensionTruncatedFrameChartResidueCharZer

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open IsLocalRing Formalism.MainNotions.ModuliIntegralCharts.H1 ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ExtScaleZero



theorem exists_ext_all_models_uniformised_charZero (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l)
    (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (h0 : CharZero (ResidueField T.V)) :
    ∃ (T' : CDVR) (io' : c.F →+* T'.Fr) (y' : IntFr Xo c T' io') (e' : ℕ), CharZero (ResidueField T'.V) ∧ 0 < e' ∧
      (∀ I : IntData Xo c T' io' y'.1, ∃ P : PELUnif (maximalIdeal T'.V) I.G, P.TorsionIso) ∧
      letI := io.toAlgebra; letI := io'.toAlgebra; ∃ φ : T.Fr →ₐ[c.F] T'.Fr,
        (∀ a : T.Fr, a ≠ 0 → vV T'.V (φ a) = (e' : ℤ) * vV T.V a) ∧ FrMap φ y.1 y'.1 := by
  obtain ⟨G, t, m1, m2, -⟩ := y.2.2
  obtain ⟨W, _, _, _, hc, _, hf, hi, hS⟩ := GlobalTheory.UnifTrait.exists_split_baseChange T.V G.G G.semi
  have hz : CharZero W := charZero_of_injective_ringHom hi
  let T' : Formalism.L2.Pj.CDVR := { V := W }
  have : FaithfulSMul T.V W := (faithfulSMul_iff_algebraMap_injective _ _).2 hi
  have hfin : (algebraMap T.V W).Finite := RingHom.finite_algebraMap.2 hf
  have hl : IsLocalHom (algebraMap T.V W) := hfin.to_isIntegral.isLocalHom hi
  have hres : CharZero (ResidueField W) :=
    charZero_of_injective_ringHom (ResidueField.map (algebraMap T.V W)).injective
  have hj : Function.Injective ((algebraMap W (FractionRing W)).comp (algebraMap T.V W)) :=
    (IsFractionRing.injective W _).comp hi
  obtain ⟨φ, hφ⟩ : ∃ φ : T.Fr →+* T'.Fr, ∀ v, φ (algebraMap T.V T.Fr v) = algebraMap T'.V T'.Fr (algebraMap T.V W v) :=
    ⟨IsFractionRing.lift hj, IsFractionRing.lift_algebraMap hj⟩
  obtain ⟨r, hr0, hv⟩ := GlobalTheory.IntegralPull.exists_index (V' := T'.V) (algebraMap T.V W) φ hφ
  letI := io.toAlgebra
  letI := (φ.comp io).toAlgebra
  let ψ : T.Fr →ₐ[c.F] T'.Fr := { φ with commutes' := fun _ => rfl }
  obtain ⟨z, hz⟩ := GlobalTheory.FramedBaseChange.exists_frMap GlobalTheory.firstFiveLaws.1 E H Dw l Xo c _ _ ψ y.1
  obtain ⟨p, χ, y₀, hy₀⟩ := y.2.1
  let y' : IntFr Xo c T' (φ.comp io) :=
    ⟨z, ⟨p, ψ.comp χ, y₀, Formalism.L2.Pj.frMap_trans (Xo := Xo) (c := c) _ _ _ χ ψ y₀ y.1 z hy₀ hz⟩,
      GlobalTheory.IntegralPull.integral_baseChange T T' io (φ.comp io) _ hi ψ hφ y.1 z hz y.2.2⟩
  exact ⟨T', φ.comp io, y', r, hres, hr0,
    fun I => GlobalTheory.IntegralPull.exists_unif_of_split T T' _ φ hφ m1 m2 hz.1 I.m1 I.m2 hS, ψ, fun a _ => hv a, hz⟩

end GlobalTheory.ExtScaleZero

namespace GlobalTheory.ExtScaleZero



theorem exists_ext_chart_scale_charZero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io), CharZero (ResidueField T.V) → ∀ φ : ℝ, GlobalTheory.SlopeRec.HasPhi y φ → ∃ (T' : CDVR) (io' : c.F →+* T'.Fr) (y' : IntFr Xo c T' io') (r : ℕ) (C : IntegralChartA3 Xo c T' io' y') (P : PELUnif (maximalIdeal T'.V) C.I.G), CharZero (ResidueField T'.V) ∧ 0 < r ∧ FrTrunc C.I.G (𝟙 (Sp T'.V)) (chD C.ch) C.xT C.eT ∧ P.TorsionIso ∧ GlobalTheory.SlopeRec.HasPhi y' (r * φ) ∧ ∀ (nab : NabV Xo c), IsNab Xo c nab → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n e : ℕ) (s : c.F), ∀ f ∈ thGen Xo c nab a n, nval T'.V (r * e) (io' s * evI y' f) = nval T.V e (io s * evI y f) := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro T io y hy φ hφ
  obtain ⟨S', io', z', r, hz', hr, hU, ψA, hv, hm⟩ :=
    exists_ext_all_models_uniformised_charZero E H Dw l Xo c T io y hy
  have hphi : ∀ φ' : ℝ, GlobalTheory.SlopeRec.HasPhi z' φ' → φ' = r * φ := fun φ' h' =>
    GlobalTheory.T.balancedPeriodSlope_mul_ramificationIndex _ _ _ _ Xo c T S' io io' y z' r hr ⟨ψA, hv, hm⟩ φ φ' hφ h'
  letI := io.toAlgebra
  let ψ : T.Fr →+* S'.Fr := letI := io'.toAlgebra; ψA.toRingHom
  have hio : io' = ψ.comp io := by
    letI := io'.toAlgebra
    exact RingHom.ext fun a => (ψA.commutes a).symm
  have hv' : ∀ a : T.Fr, vV S'.V (ψ a) = (r : ℤ) * vV T.V a := fun a => by
    by_cases ha : a = 0
    · simp [ha, vV]
    · exact hv a ha
  have hev : ∀ (nab : NabV Xo c), IsNab Xo c nab → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ),
      ∀ f ∈ thGen Xo c nab a n, ψ (evI y f) = evI z' f := fun nab hn a n f hf =>
    GlobalTheory.T.thetaRule_integralPoint_value_baseChange _ _ _ _ Xo c nab hn T S' io io' y z' ψA hm a n f hf
  clear_value ψ
  clear hm hv ψA
  subst hio
  obtain ⟨C, hCh⟩ := GlobalTheory.IntChartTrunc.intChart_frTrunc_exists _ H _ _ Xo c (fun _ => rfl) S' _ z'
  obtain ⟨P, hP⟩ := hU C.I
  obtain ⟨φ', hφ'⟩ := GlobalTheory.SlopeRec.exists_hasPhi z' C.I.G C.I.t' C.I.m1 C.I.m2 P
  have e1 := hphi φ' hφ'
  subst e1
  refine ⟨S', ψ.comp io, z', r, C, P, hz', hr, hCh, hP, hφ', fun nab hn a n e s f hf => ?_⟩
  rw [← hev nab hn a n f hf, RingHom.comp_apply, ← map_mul, Formalism.L2.Pj.nval_bc ψ hr hv']

end GlobalTheory.ExtScaleZero
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExtensionTruncatedFrameChartResidueCharZerStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open IsLocalRing Formalism.MainNotions.ModuliIntegralCharts.H1 ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

theorem _root_.GlobalTheory.T.exists_extension_truncatedFrame_chart_residue_charZero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io), CharZero (ResidueField T.V) → ∀ φ : ℝ, GlobalTheory.SlopeRec.HasPhi y φ → ∃ (T' : CDVR) (io' : c.F →+* T'.Fr) (y' : IntFr Xo c T' io') (r : ℕ) (C : IntegralChartA3 Xo c T' io' y') (P : PELUnif (maximalIdeal T'.V) C.I.G), CharZero (ResidueField T'.V) ∧ 0 < r ∧ FrTrunc C.I.G (𝟙 (Sp T'.V)) (chD C.ch) C.xT C.eT ∧ P.TorsionIso ∧ GlobalTheory.SlopeRec.HasPhi y' (r * φ) ∧ ∀ (nab : NabV Xo c), IsNab Xo c nab → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n e : ℕ) (s : c.F), ∀ f ∈ thGen Xo c nab a n, nval T'.V (r * e) (io' s * evI y' f) = nval T.V e (io s * evI y f) := by
  first | exact @GlobalTheory.ExtScaleZero.exists_ext_chart_scale_charZero | exact GlobalTheory.ExtScaleZero.exists_ext_chart_scale_charZero | (intros; apply GlobalTheory.ExtScaleZero.exists_ext_chart_scale_charZero <;> assumption)
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaValueOnCuspNeighbourhood

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
open IsLocalRing Formalism.MainNotions.ModuliIntegralCharts.H1 ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

theorem GlobalTheory.ThetaCuspOn.theta_value_on_cusp_neighbourhood' : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : TorFlag Y.d.Xo₂ Y.d.c₂), ∀ la ∈ ({(⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁, (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).ub} : Set (AllWt.Weight (dat p i))), letI := p.T.Q.H.starRing; ∀ (nab : NabV Y.d.Xo₂ Y.d.c₂), IsNab Y.d.Xo₂ Y.d.c₂ nab → ∀ f ∈ thGen Y.d.Xo₂ Y.d.c₂ nab (GlobalTheory.RefSum.thA (dat p i) la (GlobalTheory.RefSum.nCol (dat p i))) (GlobalTheory.RefSum.nCol (dat p i)), ∀ (y : Y₀ TF.X Z) (T : CDVR) (io : Y.d.c₂.F →+* T.Fr) (y' : IntFr Y.d.Xo₂ Y.d.c₂ T io) (g : (Y₀ TF.X Z).presheaf.stalk y →+* T.V), (letI := io.toAlgebra; TF.X.ptY y'.1 = Spec.map (CommRingCat.ofHom ((algebraMap T.V T.Fr).comp g)) ≫ (Y₀ TF.X Z).fromSpecStalk y ≫ inc₀ TF.X Z) → ∃ f' ∈ AllWt.cuspOn Y.U Z (Formalism.L2.Pj.wtZ (GlobalTheory.RefSum.thA (dat p i) la (GlobalTheory.RefSum.nCol (dat p i))) (GlobalTheory.RefSum.nCol (dat p i))), evI y' f' = evI y' f := by
  intro hP hD hS hF
  have hG := _root_.GlobalTheory.LiftGaps.weights_antitone_and_gap_ge_nCol_succ hS
  unfold _root_.GlobalTheory.CovTop.CoversCondition _root_.GlobalTheory.CovTop.LiftsCondition at hG ⊢
  refine Formalism.MainNotions.Closed.imp hG ?_
  rintro eps Fm CH - ⟨C3, hC3, x3, h3⟩
  refine ⟨C3, hC3, x3, fun x hx hle ι p hp i hi Y hY => ?_⟩
  obtain ⟨hp1, hgap⟩ := h3 x hx hle ι p hp i hi Y hY
  intro Z TF la hla
  letI := p.T.Q.H.starRing
  intro nab hnab f hf y T io y' g hfac
  have hU := hY.1.unf
  obtain ⟨hanti, hgp⟩ := hgap la hla
  have hb : ∀ τ j, |(la τ j : ℝ)| ≤ ∑ τ', ∑ j', |(la τ' j' : ℝ)| := fun τ j =>
    (Finset.single_le_sum (f := fun j' => |(la τ j' : ℝ)|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun τ' => ∑ j', |(la τ' j' : ℝ)|) (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)
        (Finset.mem_univ τ))
  have hev : Even (GlobalTheory.RefSum.nCol (dat p i)) := by
    obtain ⟨k, hk⟩ := GlobalTheory.RefSum.eight_dvd_nCol (Dw := dat p i)
    exact ⟨4 * k, by omega⟩
  have hw := GlobalTheory.RefSum.thA_dominant_lastPos_degree _ _ (dat p i) la (GlobalTheory.RefSum.nCol (dat p i)) _ hp1 hev hanti hgp hb
  have hr : 1 ≤ (Fm.D x ι).R.r := by
    have := (Fm.D x ι).R.two_le_m
    have := (Fm.D x ι).R.m_add_three_le_k
    unfold Formalism.BasicNotions.Ranks.r
    omega
  have hcusp := (GlobalTheory.thetaRules_exist_and_cusp _ _ _ _ Y.d.Xo₂ Y.d.c₂ _ Y.U hr hU nab hnab).2 _ _ hw.1 hw.2.2.1 f hf
  obtain ⟨g', hg'e, -⟩ := GlobalTheory.CompRestr.exists_cuspOn_restrict _ _ _ _ Y.d.Xo₂ Y.d.c₂ _ Y.U hU Z _ ⟨f, hcusp⟩
  refine ⟨g', g'.2, ?_⟩
  letI := io.toAlgebra
  have hfac' : TF.X.ptY y'.1 = Spec.map (CommRingCat.ofHom ((algebraMap T.V T.Fr).comp g)) ≫ (Y₀ TF.X Z).fromSpecStalk y ≫ inc₀ TF.X Z := hfac
  have hL : GlobalTheory.AllWt.LiesOn Z y'.1 := by
    refine (ptY_le_iff TF.X Z y'.1).1 ?_
    rw [hfac']
    first
      | (rw [Scheme.Hom.comp_preimage, Scheme.Opens.ι_preimage_self, Scheme.Hom.preimage_top])
      | (intro s _; exact (((Spec.map (CommRingCat.ofHom ((algebraMap T.V T.Fr).comp g)) ≫ (Y₀ TF.X Z).fromSpecStalk y) s).2 : _))
      | (intro s _; simp)
  exact hg'e T.Fr y'.1 hL
end
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open IsLocalRing Formalism.MainNotions.ModuliIntegralCharts.H1 ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

theorem _root_.GlobalTheory.T.theta_cusp_value_formula_at_weight : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : TorFlag Y.d.Xo₂ Y.d.c₂), ∀ la ∈ ({(⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁, (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).ub} : Set (AllWt.Weight (dat p i))), letI := p.T.Q.H.starRing; ∀ (nab : NabV Y.d.Xo₂ Y.d.c₂), IsNab Y.d.Xo₂ Y.d.c₂ nab → ∀ f ∈ thGen Y.d.Xo₂ Y.d.c₂ nab (GlobalTheory.RefSum.thA (dat p i) la (GlobalTheory.RefSum.nCol (dat p i))) (GlobalTheory.RefSum.nCol (dat p i)), ∀ (y : Y₀ TF.X Z) (T : CDVR) (io : Y.d.c₂.F →+* T.Fr) (y' : IntFr Y.d.Xo₂ Y.d.c₂ T io) (g : (Y₀ TF.X Z).presheaf.stalk y →+* T.V), (letI := io.toAlgebra; TF.X.ptY y'.1 = Spec.map (CommRingCat.ofHom ((algebraMap T.V T.Fr).comp g)) ≫ (Y₀ TF.X Z).fromSpecStalk y ≫ inc₀ TF.X Z) → ∃ f' ∈ AllWt.cuspOn Y.U Z (Formalism.L2.Pj.wtZ (GlobalTheory.RefSum.thA (dat p i) la (GlobalTheory.RefSum.nCol (dat p i))) (GlobalTheory.RefSum.nCol (dat p i))), evI y' f' = evI y' f := by
  first | exact @_root_.GlobalTheory.ThetaCuspOn.theta_value_on_cusp_neighbourhood' | exact _root_.GlobalTheory.ThetaCuspOn.theta_value_on_cusp_neighbourhood' | (intros; apply _root_.GlobalTheory.ThetaCuspOn.theta_value_on_cusp_neighbourhood' <;> assumption)
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsCuspWithThetaJetValueLe

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
open IsLocalRing Formalism.MainNotions.ModuliIntegralCharts.H1 ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
namespace GlobalTheory.ThetaJetsT
theorem exists_cusp_with_theta_jet_value_le_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : TorFlag Y.d.Xo₂ Y.d.c₂), ∀ la ∈ ({(⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁, (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).ub} : Set (AllWt.Weight (dat p i))), ∀ cst : ℝ, GlobalTheory.RefSum.JetNum (Fm.D x ι) (DF (dat p i) (GlobalTheory.RefSum.thA (dat p i) la (GlobalTheory.RefSum.nCol (dat p i)))) cst → ∀ y ∈ (U₀ TF.X Z : Set (Y₀ TF.X Z))ᶜ, ∀ (T : CDVR) (io : Y.d.c₂.F →+* T.Fr) (y' : IntFr Y.d.Xo₂ Y.d.c₂ T io) (g : (Y₀ TF.X Z).presheaf.stalk y →+* T.V) (φT : ℝ), IsLocalHom g → GlobalTheory.SlopeRec.HasPhi y' φT → (letI := io.toAlgebra; TF.X.ptY y'.1 = Spec.map (CommRingCat.ofHom ((algebraMap T.V T.Fr).comp g)) ≫ (Y₀ TF.X Z).fromSpecStalk y ≫ inc₀ TF.X Z) → ∃ f ∈ AllWt.cuspOn Y.U Z (Formalism.L2.Pj.wtZ (GlobalTheory.RefSum.thA (dat p i) la (GlobalTheory.RefSum.nCol (dat p i))) (GlobalTheory.RefSum.nCol (dat p i))), evI y' f ≠ 0 ∧ (vV T.V (evI y' f) : ℝ) ≤ cst * φT := by
  intro h1 h2 h3 h4
  have hA := _root_.GlobalTheory.T.theta_jet_value_bound_char_zero' h1 h2 h3 h4
  have hC := _root_.GlobalTheory.T.theta_cusp_value_formula_at_weight h1 h2 h3 h4
  unfold _root_.GlobalTheory.CovTop.CoversCondition _root_.GlobalTheory.CovTop.LiftsCondition Formalism.MainNotions.Closed at hA hC ⊢
  obtain ⟨ε1, hε1, hA⟩ := hA
  obtain ⟨ε2, hε2, hC⟩ := hC
  refine ⟨min ε1 ε2, lt_min hε1 hε2, fun eps he hle => ?_⟩
  obtain ⟨K1, hK1⟩ := hA eps he (hle.trans (min_le_left _ _))
  obtain ⟨K2, hK2⟩ := hC eps he (hle.trans (min_le_right _ _))
  refine ⟨⟨max K1.pre K2.pre, fun l => max (K1.t l) (K2.t l), fun l => max (K1.mid l) (K2.mid l),
    fun l => max (K1.last l) (K2.last l)⟩, fun Fm CH hF hL => ?_⟩
  have hL1 : Fm.Large K1 CH := ⟨fun c hc => (le_max_left _ _).trans (hL.1 c hc), trivial,
    fun c hc => (le_max_left _ _).trans (hL.2.2.1 c hc), fun c hc => (le_max_left _ _).trans (hL.2.2.2 c hc)⟩
  have hL2 : Fm.Large K2 CH := ⟨fun c hc => (le_max_right _ _).trans (hL.1 c hc), trivial,
    fun c hc => (le_max_right _ _).trans (hL.2.2.1 c hc), fun c hc => (le_max_right _ _).trans (hL.2.2.2 c hc)⟩
  obtain ⟨C1, hC1, hE1⟩ := hK1 Fm CH hF hL1
  obtain ⟨C2, -, hE2⟩ := hK2 Fm CH hF hL2
  refine ⟨C1, hC1, ?_⟩
  obtain ⟨x1, hx1⟩ := hE1.and hE2
  refine ⟨x1, fun x hx hle ι p hp i hi Y hY => ?_⟩
  obtain ⟨hAi, hCi⟩ := hx1 x hx hle ι p hp
  have hA' := hAi i hi Y hY
  have hC' := hCi i hi Y hY
  intro Z TF la hla cst hJ y hy T io y' g φT hg hφ hpt
  have hch : CharZero (IsLocalRing.ResidueField T.V) := GlobalTheory.UnifTrait.charZero_residue_of_map T.V
    (Spec.map (CommRingCat.ofHom g) ≫ (Y₀ TF.X Z).fromSpecStalk y ≫ inc₀ TF.X Z ≫ TF.X.π ≫ TF.Y.s)
  obtain ⟨st, nab, hnab⟩ := GlobalTheory.CanonConn.exists_isNab_uncond _ _ _ _ Y.d.Xo₂ Y.d.c₂
  obtain rfl := GlobalTheory.PowGerm.starSt _ _ st hnab.1
  obtain ⟨T', io', y'', r, C, P, hch', hr, hC0, hP, hφ', hsc⟩ := GlobalTheory.T.exists_extension_truncatedFrame_chart_residue_charZero _ _ _ _ Y.d.Xo₂ Y.d.c₂ T io y' hch φT hφ
  obtain ⟨f, hf, hne, hle⟩ := hA' la hla cst hJ nab hnab T' io' y'' C P (r * φT) hch' hC0 hP hφ'
  have hs := hsc nab hnab _ _ 1 1 f hf
  simp only [map_one, one_mul, mul_one] at hs
  obtain ⟨f', hf', hev⟩ := hC' Z TF la hla nab hnab f hf y T io y' g hpt
  have hne' : evI y' f ≠ 0 := by
    intro h0
    rw [h0, nval_zero, nval_of_ne hne] at hs
    exact EReal.coe_ne_top _ hs
  refine ⟨f', hf', hev ▸ hne', ?_⟩
  rw [hev]
  rw [nval_of_ne hne, nval_of_ne hne', EReal.coe_eq_coe_iff] at hs
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hφ0 := hφ.nonneg
  rw [Nat.cast_one, div_one] at hs
  rw [← hs, div_le_iff₀ hr']
  nlinarith
end GlobalTheory.ThetaJetsT
end
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

theorem _root_.GlobalTheory.T.theta_jet_cusp_value_bound_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : TorFlag Y.d.Xo₂ Y.d.c₂), ∀ la ∈ ({(⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁, (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).ub} : Set (AllWt.Weight (dat p i))), ∀ cst : ℝ, GlobalTheory.RefSum.JetNum (Fm.D x ι) (DF (dat p i) (GlobalTheory.RefSum.thA (dat p i) la (GlobalTheory.RefSum.nCol (dat p i)))) cst → ∀ y ∈ (U₀ TF.X Z : Set (Y₀ TF.X Z))ᶜ, ∀ (T : CDVR) (io : Y.d.c₂.F →+* T.Fr) (y' : IntFr Y.d.Xo₂ Y.d.c₂ T io) (g : (Y₀ TF.X Z).presheaf.stalk y →+* T.V) (φT : ℝ), IsLocalHom g → GlobalTheory.SlopeRec.HasPhi y' φT → (letI := io.toAlgebra; TF.X.ptY y'.1 = Spec.map (CommRingCat.ofHom ((algebraMap T.V T.Fr).comp g)) ≫ (Y₀ TF.X Z).fromSpecStalk y ≫ inc₀ TF.X Z) → ∃ f ∈ AllWt.cuspOn Y.U Z (Formalism.L2.Pj.wtZ (GlobalTheory.RefSum.thA (dat p i) la (GlobalTheory.RefSum.nCol (dat p i))) (GlobalTheory.RefSum.nCol (dat p i))), evI y' f ≠ 0 ∧ (vV T.V (evI y' f) : ℝ) ≤ cst * φT := by
  first | exact @_root_.GlobalTheory.ThetaJetsT.exists_cusp_with_theta_jet_value_le_alt | exact _root_.GlobalTheory.ThetaJetsT.exists_cusp_with_theta_jet_value_le_alt | (intros; apply _root_.GlobalTheory.ThetaJetsT.exists_cusp_with_theta_jet_value_le_alt <;> assumption)
end
end
end
end
