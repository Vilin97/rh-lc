module

public import Development.AbelianVarietyTheory.Definitions.Jets.IsSelfOf
public import Formalism.LocalToGlobal.ProjectiveLattices.ConjNeSelfOfCM
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BlockProdMemChartFamilyAtPlacePairsStatement
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CharacterBoundPairsOfPlacesIntegralChartStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FlagOfLetterNumberingRowData
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.IsIntegralGaugedFormalGroupLawSelfConjugateSquar
public import Formalism.LocalToGlobal.CharacterGerms.RowTieAxes
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.RawChartTangentMaximalIdealOfNonDegenerateStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.AddCurveStableOfIntegralGaugedFormalGroupLaw
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.HasGaugeAdjointLieProjectorsPairDataStatement
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.IsIntegralGaugedFormalGroupLawPairData
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Basify
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
import Development.AbelianVarietyTheory.Definitions.Jets.DepthNumbersThresholdEq
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.BiextensionNondegenerateModMaximalIdealIntegralCStatement
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CartHypOfFormalBiextension
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.GeZeroOfIsIntegral
public import Formalism.LocalToGlobal.CharacterGerms.RowTieFB
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.GaugeDerivEqPairingOfIntegralGaugedLawStatement
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.GaugedFormalGroupKernelSmallOfSecondStatement
public import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.IntegralGermsIndependentOfCurveSystem
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.ProjectiveLattices.SubConstMemOrig
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.IsIntegralGaugedFormalGroupLawPairDataStatement
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.JetAt0ProdRename
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.NuLocCLeNuPlEBaseChange
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.SubstOneVariableUncurryEqSubst
public import Formalism.LocalToGlobal.CharacterGerms.RowTieAdm
import Formalism.LocalToGlobal.CharacterGerms.RowTieAxes
public import Formalism.LocalToGlobal.CharacterGerms.RowTieTop

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.NonDegenerateAndRowConditionTwoPairsOfPlaces

section

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.NonDegPair

section

open scoped BigOperators
open MvPowerSeries Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.RowLawSquare GlobalTheory.RowLawPair
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {C : Type} [Field C] {dd : ℕ}

theorem coeff_mvExp_of_van {τ : Type} {T : Set τ} {H : MvPowerSeries τ C} [CharZero C] (hH : Van T H)
    (ν : τ →₀ ℕ) (hν : ∀ w ∈ ν.support, w ∉ T) (t : τ) :
    coeff (ν + Finsupp.single t 1) (mvExp H) = coeff (ν + Finsupp.single t 1) H := by
  have h := GlobalTheory.RowLaw.AddCurve.van_pderiv_mvExp hH t ν hν
  rw [map_sub, coeff_pderiv, coeff_pderiv, ← sub_mul, mul_eq_zero] at h
  rcases h with h | h
  · exact sub_eq_zero.1 h
  · exact absurd h (Nat.cast_add_one_ne_zero _)

theorem van_add {τ : Type} {T : Set τ} {f g : MvPowerSeries τ C} (hf : Van T f) (hg : Van T g) : Van T (f + g) :=
  fun ν hν => by rw [map_add (f := _), hf ν hν, hg ν hν, add_zero]

theorem van_sub {τ : Type} {T : Set τ} {f g : MvPowerSeries τ C} (hf : Van T f) (hg : Van T g) : Van T (f - g) :=
  fun ν hν => by rw [map_sub, hf ν hν, hg ν hν, sub_zero]

theorem zc_cvAt {V : VF C} {γ : Fin dd → PowerSeries C} (hγ : IsCv V γ) (s : Fin 2) :
    Zc fun j => cvAt (X s : MvPowerSeries (Fin 2) C) (γ j) := fun j =>
  constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _)
    (fun _ => constantCoeff_X _) (hγ j).1

def toOne (b : MvPowerSeries (Fin dd) C) : PS C 1 dd := subst (pt C dd (0 : Fin 1)) b

theorem sb_toOne {τ : Type} {a : Fin dd → MvPowerSeries τ C} (ha : Zc a) (b : MvPowerSeries (Fin dd) C) :
    sb ![a] (toOne b) = subst a b := by
  unfold toOne sb
  rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero (zc_pt 0)) (hasSubst_sb (zc1 ha))]
  congr 1
  funext i
  exact sb_pt (zc1 ha) 0 i

variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] (Y : FBChart C V O dd)
  {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] (p : PairData Y d I)

theorem van_h {n : ℕ} (j : Fin n) {b : Fin dd → PS C n dd} (hb : Zc b) :
    Van {s : Fin n × Fin dd | s.1 = j} (sb ![gp C (Fin dd) j, b] Y.h) := by
  classical
  refine Van.subst {s : Fin 2 × Fin dd | s.1 = 0} (fun s => zc2 (GlobalTheory.RowLawPair.zc_gp j) hb s.1 s.2) ?_ (h_axes Y 0)
  rintro ⟨s, x⟩ hs ν hν
  obtain rfl : s = 0 := hs
  show coeff ν (X (j, x) : PS C n dd) = 0
  rw [coeff_X, if_neg]
  rintro rfl
  exact hν (j, x) (by simp) rfl

theorem sb_gp_three (f : PS C 3 dd) : sb ![gp C (Fin dd) (0 : Fin 3), gp C (Fin dd) 1, gp C (Fin dd) 2] f = f := by
  have e : (fun q : Fin 3 × Fin dd => ![gp C (Fin dd) (0 : Fin 3), gp C (Fin dd) 1, gp C (Fin dd) 2] q.1 q.2) = X := by
    funext ⟨s, x⟩
    fin_cases s <;> rfl
  unfold sb
  rw [e, subst_self]
  rfl

theorem formalGroupCocycleLinearTerm_eq_chartLinear (u : Fin dd → C) : c2 (Y.raw p) u = Y.chartLinearTerm u := by
  have z := fun j : Fin 3 => GlobalTheory.RowLawPair.zc_gp (C := C) (dd := dd) j
  have hv : Van {s : Fin 3 × Fin dd | s.1 = 0}
      (sb ![gp C (Fin dd) (0 : Fin 3), gp C (Fin dd) 1] Y.h + sb ![gp C (Fin dd) (0 : Fin 3), gp C (Fin dd) 2] Y.h -
        sb ![gp C (Fin dd) (0 : Fin 3), law Y (gp C (Fin dd) 1) (gp C (Fin dd) 2)] Y.h) :=
    van_sub (van_add (van_h Y 0 (z 1)) (van_h Y 0 (z 2))) (van_h Y 0 (zc_law Y (z 1) (z 2)))
  have e := exp_gauge_cocycle_second_variable Y (z 0) (z 1) (z 2)
  rw [sb_gp_three, ← mvExp_eq hv.const] at e
  funext μ
  unfold c2 FBChart.chartLinearTerm
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [formalAdd_eq_law Y p (z 1) (z 2), hAt_eq_sb, hAt_eq_sb, hAt_eq_sb, ← e, coeff_mvExp_of_van hv]
  intro w hw
  classical
  obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hw)
  exact Fin.succ_ne_zero _

theorem cob_eq (b : MvPowerSeries (Fin dd) C) : cob (Y.raw p) b =
    ev (n := 2) ![addOf Y.B.G.F (pt C dd 0) (pt C dd 1)] (toOne b) - ev (n := 2) ![pt C dd 0] (toOne b) -
      ev (n := 2) ![pt C dd 1] (toOne b) := by
  unfold cob
  rw [formalAdd_eq_law Y p (GlobalTheory.RowLawPair.zc_gp 0) (GlobalTheory.RowLawPair.zc_gp 1),
    ← sb_toOne (zc_law Y (GlobalTheory.RowLawPair.zc_gp 0) (GlobalTheory.RowLawPair.zc_gp 1)),
    ← sb_toOne (GlobalTheory.RowLawPair.zc_gp 0), ← sb_toOne (GlobalTheory.RowLawPair.zc_gp 1)]
  rfl

theorem nonDeg_raw (h : NDG Y) : NonDeg (Y.raw p) V := by
  rintro γ hγ hu hadd ⟨b, hb, hcob⟩
  refine h γ hγ hu (fun i μ h0 h1 => ?_) ⟨toOne b, intS_subst V (zc_pt 0) (fun _ => intS_X V _) hb, fun μ => ?_⟩
  · have e := hadd i μ h0 h1
    rw [formalAdd_eq_law Y p (zc_cvAt hγ 0) (zc_cvAt hγ 1)] at e
    have e2 : (fun q : Fin 2 × Fin dd => cvAt (X q.1 : MvPowerSeries (Fin 2) C) (γ q.2)) =
        fun q : Fin 2 × Fin dd => ![fun j => cvAt (X 0 : MvPowerSeries (Fin 2) C) (γ j),
          fun j => cvAt (X 1 : MvPowerSeries (Fin 2) C) (γ j)] q.1 q.2 := by
      funext ⟨s, x⟩
      fin_cases s <;> rfl
    rw [e2]
    exact e
  · have e := hcob μ
    rwa [formalGroupCocycleLinearTerm_eq_chartLinear, cob_eq] at e

end

open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

theorem nonDegenerate_and_rowConditionTwo_pairsOfPlaces : (∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ) (Y : FBChart C V O dd) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (p : PairData Y d I), NDG Y → NonDeg (Y.raw p) V) ∧ RankMaximalOfNondegenerate :=
  ⟨fun _ _ _ _ _ _ _ _ Y _ _ _ _ p h => nonDeg_raw Y p h,
    fun C _ _ V O _ _ dd Y d _ I _ p h _ Hc =>
      GlobalTheory.T.rawChart_tangent_maximalIdeal_of_nonDegenerate C V d I (Fin dd) (Y.raw p) (GlobalTheory.RowLawPair.rLaw_pairData C V O dd Y d I p) (GlobalTheory.T.hasGaugeAdjointLieProjectors_pairData C V O dd Y d I p)
        (nonDeg_raw Y p h) Hc⟩

end GlobalTheory.NonDegPair
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.NonDegenerateAndRowConditionTwoPairsOfPlacesStatement

section

@[expose] public section

open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

theorem _root_.GlobalTheory.T.nonDeg_raw_pairData_and_rankMaximal : (∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ) (Y : FBChart C V O dd) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (p : PairData Y d I), NDG Y → NonDeg (Y.raw p) V) ∧ RankMaximalOfNondegenerate := by
  first | exact @GlobalTheory.NonDegPair.nonDegenerate_and_rowConditionTwo_pairsOfPlaces | exact GlobalTheory.NonDegPair.nonDegenerate_and_rowConditionTwo_pairsOfPlaces | (intros; apply GlobalTheory.NonDegPair.nonDegenerate_and_rowConditionTwo_pairsOfPlaces <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.IntegralGermsIndependentOfCurveSystemStatement

section

@[expose] public section

open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

theorem _root_.GlobalTheory.T.integralGerms_independent_of_curveSystem : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ] (X : RawChart C d I κ), RLaw X V → ∀ H : ∀ g, X.CartHyp V g, RawChart.IntegralGermIndependentOfSystem H := by
  first | exact @GlobalTheory.RowLaw.intGerm_indep_of_rlaw | exact GlobalTheory.RowLaw.intGerm_indep_of_rlaw | (intros; apply GlobalTheory.RowLaw.intGerm_indep_of_rlaw <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.GermsDerivKernelOfFormal

section

@[expose] public section

open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.RowLaw

theorem germs_deriv_kernel_of_formal : IntegralGermIndependentAllCharts ∧ CEqFBSt ∧ IndependenceBoundAllCharts :=
  ⟨fun C _ _ V O _ _ dd Y d _ I _ p H =>
      GlobalTheory.T.integralGerms_independent_of_curveSystem C V d I (Fin dd) (Y.raw p) (GlobalTheory.T.isIntegralGaugedFormalGroupLaw_pairData C V O dd Y d I p) H,
    fun C _ _ V O _ _ dd Y d _ I _ p _ H =>
      GlobalTheory.T.gaugeDeriv_eq_pairing_of_integralGaugedLaw C V d I (Fin dd) (Y.raw p) (GlobalTheory.T.isIntegralGaugedFormalGroupLaw_pairData C V O dd Y d I p) H,
    fun C _ _ V O _ _ dd Y d _ I _ p hr H h2 =>
      GlobalTheory.T.gaugedFormalGroup_kernel_small_of_second C V d I (Fin dd) (Y.raw p) (GlobalTheory.T.isIntegralGaugedFormalGroupLaw_pairData C V O dd Y d I p) hr H h2⟩

end GlobalTheory.RowLaw
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.RowDataSuppliedAtPairsOfPlaces

section

@[expose] public section

set_option autoImplicit false

open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.RowAt

theorem supply_pairs : (∀ (p : ℕ) [Fact p.Prime], ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.UpFSt p) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (lv : Level H) (Xo : Moduli Dw lv) (c : Coeff lv) [StarRing (𝓞 E)], (∀ x : 𝓞 E, star x = H.bar x) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C3 : IntChart T io y) (C : Type) [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι → ∀ (k : ℕ) (Y : FBChart C V (𝓞 E) (chD C3.ch)), IsBC C3 ι k Y → y.IsAlg → ¬ (V.l : ℤ) ∣ NumberField.discr E → ∀ (Orb : Type) [Fintype Orb] (d : ℕ) [NeZero d] (lab : Lab E Orb d), LabArith V io ι lab → Function.Surjective (fun x : Orb × Fin 2 × ZMod d => lab.tau x.1 x.2.1 x.2.2) → lab.RankOK Dw → lab.j' < lab.n → (∀ o, (Even d ∧ ∀ s : ZMod d, (lab.big o 0 s ↔ Even s.val)) ∨ ∀ s, lab.big o 0 s) → ∀ (a : (E →+* ℂ) × ℕ → ℕ), DomW Dw a → ∀ (nW : ℕ) (ν : ℝ), (ν : EReal) ≤ nuLocC C3 (eOf T V) k a nW → Supply V d Orb Finset.univ lab.n (lab.j + lab.j') lab.big (fun o g s => Dw.mult (lab.tau o g s)) (fun o g s => gap (Dw.mult (lab.tau o g s)) fun i => a (lab.tau o g s, i)) nW ν := by
  intro hUp E _ _ _ H Dw lv Xo c _ hstar T io y C3 C _ _ V ι hι k Y hY hy hl Orb _ d _ lab ha hsurj hr hj hdich a hdom nW ν hν
  have hg : LabGeo C3 ι Y lab :=
    GlobalTheory.LabelledDirections.labGeoSt E H Dw lv Xo c hstar T io y C3 C V ι hι k Y hY Orb d lab ha
  have hnd : NDG Y := GlobalTheory.T.biextension_nondegenerate_mod_maximalIdeal_integral_chart E H Dw lv Xo c hstar T io y C3 C V ι hι k Y hY
  have Hy : ∀ o, (Y.raw (pairOfLab ha hg o)).Hyps V := fun o =>
    FBChart.hyps GlobalTheory.cartHyp_of_formalBiextension axesFB GlobalTheory.RowLaw.germs_deriv_kernel_of_formal.1 GlobalTheory.RowLaw.germs_deriv_kernel_of_formal.2.1 GlobalTheory.RowLaw.germs_deriv_kernel_of_formal.2.2 Y (pairOfLab ha hg o)
      (rankHyp_ofLab ha hg hr o)
      (GlobalTheory.T.nonDeg_raw_pairData_and_rankMaximal.2 C V (𝓞 E) _ Y d _ (pairOfLab ha hg o) hnd (rankHyp_ofLab ha hg hr o) _)
      (GlobalTheory.T.characterBound_pairs_of_places_integralChart hUp E H Dw lv Xo c hstar T io y C3 C V ι hι k Y hY hy hl Orb d lab ha hg hr o _)
  have hfl := fun o => GlobalTheory.flag_of_numbering C V d (fun _ => ZMod d) (fun g s => Dw.mult (lab.tau o g s))
    (fun _ => Equiv.refl _) (JJ (lab.II Dw o)) (RF.rd Y (pairOfLab ha hg) Hy o) (fun _ _ => rfl)
  have hrk : ∀ o g s, (RF.rd Y (pairOfLab ha hg) Hy o).rkF g s = Dw.mult (lab.tau o g s) := fun o => (hfl o).1
  choose F hF using fun o => (hfl o).2
  refine ⟨fun o => lab.II Dw o, fun o => JJ (lab.II Dw o), inferInstance, inferInstance,
    fun o => RF.rd Y (pairOfLab ha hg) Hy o, F, fun o => ⟨rfl, rfl⟩, fun o _ g s => ⟨Iff.rfl, hrk o g s⟩, ?_⟩
  refine RF.valBlocks_of_nuPlE Y (pairOfLab ha hg) Hy (chartLetterSystem C3 V ι a) nW F Finset.univ _ ν
    (hν.trans (GlobalTheory.nuLocC_le_nuPlE_baseChange E H Dw lv Xo c T io y C3 C V ι hι k Y hY a nW))
    (pairsSep_ofLab ha hg) (GlobalTheory.RowVal.value_eq_prod C V (𝓞 E) _ Y d Orb _ (pairOfLab ha hg) Hy _ nW) GlobalTheory.JetProd.jetProd
    (GlobalTheory.T.blockProd_mem_chartFamily_at_place_pairs E H Dw lv Xo c hstar T io y C3 C V ι hι k Y hY Orb d lab ha hg hsurj hr hj Hy F
      (fun o g s q => (hF o g s q).2) a hdom nW) ?_
  refine RF.blkAdm _ F Finset.univ _ (fun o _ => hdich o) (fun _ _ => hj) fun o _ g s q hq => ?_
  rw [hrk]
  by_contra hc
  exact hq (by unfold gap; rw [if_neg fun h => hc h.2])

end GlobalTheory.RowAt
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.RowDataSuppliedAtPairsOfPlacesStatement

section

@[expose] public section

open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

theorem _root_.GlobalTheory.T.rowData_supplied_at_pairs_of_places : (∀ (p : ℕ) [Fact p.Prime], ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.UpFSt p) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (lv : Level H) (Xo : Moduli Dw lv) (c : Coeff lv) [StarRing (𝓞 E)], (∀ x : 𝓞 E, star x = H.bar x) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C3 : IntChart T io y) (C : Type) [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι → ∀ (k : ℕ) (Y : FBChart C V (𝓞 E) (chD C3.ch)), IsBC C3 ι k Y → y.IsAlg → ¬ (V.l : ℤ) ∣ NumberField.discr E → ∀ (Orb : Type) [Fintype Orb] (d : ℕ) [NeZero d] (lab : Lab E Orb d), LabArith V io ι lab → Function.Surjective (fun x : Orb × Fin 2 × ZMod d => lab.tau x.1 x.2.1 x.2.2) → lab.RankOK Dw → lab.j' < lab.n → (∀ o, (Even d ∧ ∀ s : ZMod d, (lab.big o 0 s ↔ Even s.val)) ∨ ∀ s, lab.big o 0 s) → ∀ (a : (E →+* ℂ) × ℕ → ℕ), DomW Dw a → ∀ (nW : ℕ) (ν : ℝ), (ν : EReal) ≤ nuLocC C3 (eOf T V) k a nW → Supply V d Orb Finset.univ lab.n (lab.j + lab.j') lab.big (fun o g s => Dw.mult (lab.tau o g s)) (fun o g s => gap (Dw.mult (lab.tau o g s)) fun i => a (lab.tau o g s, i)) nW ν := by
  first | exact @GlobalTheory.RowAt.supply_pairs | exact GlobalTheory.RowAt.supply_pairs | (intros; apply GlobalTheory.RowAt.supply_pairs <;> assumption)
end
end
