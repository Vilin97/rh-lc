module

public import Development.AbelianVarietyTheory.Definitions.Jets.IsSelfOf
public import Formalism.LocalToGlobal.ProjectiveLattices.ConjNeSelfOfCM
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
public import Formalism.LocalToGlobal.CharacterGerms.BlockMembershipSelfConjugate
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BlockProdMemAtSelfConjPlaces
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
import Development.AbelianVarietyTheory.Definitions.Jets.DepthNumbersThresholdEq
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CharacterBoundSelfConjugateDegreeTwoIntegralCharStatement
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ChartValuesBoundProductsOnPlanes
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsSelfConjugatePlaceDataIntChartStatement
public import Formalism.LocalToGlobal.CharacterGerms.ContentZeroAt
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FlagOfLetterNumberingRowData
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Jets.IsSelfOf
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
import Formalism.LocalToGlobal.Divisibility.Numbers
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.RowConditionTwoSelfConjugateOfNonDegenerateStatement
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.BiextensionNondegenerateModMaximalIdealIntegralCStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.JetAt0ProdRename
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.NuLocCLeNuPlEBaseChange
public import Formalism.LocalToGlobal.CharacterGerms.RowTieSelf
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CartHypOfIntegralGaugedFormalGroupLawStatement
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.GaugeDerivEqPairingOfIntegralGaugedLawStatement
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.GaugedFormalGroupKernelSmallOfSecondStatement
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.HasGaugeAdjointLieProjectorsSelfConjugatePlaceStatement
public import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.HasGaugeAdjointTeichmullerEndSelfConjugatePlace
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.IntegralGermsIndependentOfCurveSystem
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.IsIntegralGaugedFormalGroupLawSelfConjugateSquarStatement
import Formalism.LocalToGlobal.CharacterGerms.RowTieAxes
import Formalism.LocalToGlobal.CharacterGerms.RowTieAdm
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.BlockProdMemAtSelfConjPlacesStatement

section

@[expose] public section

open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

theorem _root_.GlobalTheory.T.blockProd_mem_at_selfConj_places : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (lv : Level H) (Xo : Moduli Dw lv) (c : Coeff lv) [StarRing (𝓞 E)], (∀ x : 𝓞 E, star x = H.bar x) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C3 : IntChart T io y) (C : Type) [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι → ∀ (k : ℕ) (Y : FBChart C V (𝓞 E) (chD C3.ch)), IsBC C3 ι k Y → ∀ (Orb : Type) [Fintype Orb] (lab : LabS E Orb), ArithS V io ι lab → Function.Surjective (fun x : Orb × ZMod 2 => lab.tau x.1 x.2) → lab.RankOK Dw → lab.j' < lab.n → ∀ p : ∀ o, SelfData Y 2 (lab.II Dw o), IsSelfOf C3 ι Y lab p → ∀ (Hy : ∀ o, (Y.rawSelf (p o)).Hyps V) (F : ∀ o, RF.Flag ((Y.rawSelf (p o)).rowData (Hy o))), (∀ o g s q, (((F o).en g s q).2 : ℕ) = q) → ∀ (a : (E →+* ℂ) × ℕ → ℕ), DomW Dw a → ∀ (N n : ℕ) (pl : Fin N × Fin 2 ↪ Fin n), RF.BlockMembershipSelfConjugate (fun o => (Y.rawSelf (p o)).rowData (Hy o)) N F (imgFamS Y p (chartLetterSystem C3 V ι a) pl) (fun o s => gap (Dw.mult (lab.tau o s)) fun i => a (lab.tau o s, i)) := by
  first | exact @GlobalTheory.SelfConjMem.blkMemC_self | exact GlobalTheory.SelfConjMem.blkMemC_self | (intros; apply GlobalTheory.SelfConjMem.blkMemC_self <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.ChartValuesBoundProductsOnPlanesStatement

section

@[expose] public section

open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

theorem _root_.GlobalTheory.T.chartValues_bound_products_on_planes : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ) (Y : FBChart C V O dd) (d : ℕ) [NeZero d] (Orb : Type) [Fintype Orb] (I0 : Orb → Type) [∀ o, Fintype (I0 o)] (p : ∀ o, SelfData Y d (I0 o)) (H : ∀ o, (Y.rawSelf (p o)).Hyps V) (Ls : LetSys C dd) (N n : ℕ) (pl : Fin N × Fin 2 ↪ Fin n) (ν : ℝ), SelfSep Y p → (ν : EReal) ≤ Y.nuPlE Ls n → RF.ValO (fun o => (Y.rawSelf (p o)).rowData (H o)) N (imgFamS Y p Ls pl) ν := by
  first | exact @GlobalTheory.RowAt.valO_self | exact GlobalTheory.RowAt.valO_self | (intros; apply GlobalTheory.RowAt.valO_self <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.FlagOfLetterNumberingRowDataStatement

section

@[expose] public section

open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

theorem _root_.GlobalTheory.T.flag_of_letterNumbering_rowData : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (A : Fin 2 → Type) [∀ g, Fintype (A g)] (m : ∀ g, A g → ℕ) (ty : ∀ g, A g ≃ ZMod d) (J : Fin 2 → Type) [∀ g, Fintype (J g)] (X : RowData C V d (fun g => Σ s : A g, Fin (m g s)) J), (∀ g x, (X.G g).ty (Sum.inl x) = ty g x.1) → (∀ g s, X.rkF g (ty g s) = m g s) ∧ ∃ F : RF.Flag X, ∀ g a c, (F.en g a c).1 = (ty g).symm a ∧ ((F.en g a c).2 : ℕ) = c := by
  first | exact @GlobalTheory.flag_of_numbering | exact GlobalTheory.flag_of_numbering | (intros; apply GlobalTheory.flag_of_numbering <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.HasGaugeAdjointTeichmullerEndSelfConjugatePlaceStatement

section

@[expose] public section

open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

theorem _root_.GlobalTheory.T.hasGaugeAdjointTeichmullerEnd_selfConjugatePlace : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ) (Y : FBChart C V O dd) (d : ℕ) [NeZero d] (I0 : Type) [Fintype I0] (p : SelfData Y d I0), ∀ g, HasTeich (Y.rawSelf p) V g := by
  first | exact @GlobalTheory.hasTeich_selfData | exact GlobalTheory.hasTeich_selfData | (intros; apply GlobalTheory.hasTeich_selfData <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.RowLawFormalStatementsSelfConjugate

section

@[expose] public section

open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.RowLaw

theorem formal_statements_selfConj :
    CartSelfSt ∧ AxesSelfSt ∧ GermZeroSelfConjugate ∧ CEqSelfSt ∧ IndependenceBoundSelfConjugate := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro C _ _ V O _ _ dd Y d _ I0 _ p
    exact GlobalTheory.T.cartHyp_of_integralGaugedFormalGroupLaw C V d _ _ _ (GlobalTheory.T.isIntegralGaugedFormalGroupLaw_selfConjugateSquare C V O dd Y d I0 p) (GlobalTheory.T.hasGaugeAdjointLieProjectors_selfConjugatePlace C V O dd Y d I0 p)
      (GlobalTheory.T.hasGaugeAdjointTeichmullerEnd_selfConjugatePlace C V O dd Y d I0 p)
  · intro C _ _ V O _ _ dd Y d _ I0 _ p
    have h := GlobalTheory.T.isIntegralGaugedFormalGroupLaw_selfConjugateSquare C V O dd Y d I0 p
    exact RawChart.axes_of _ h.exc h.axes
  · intro C _ _ V O _ _ dd Y d _ I0 _ p
    exact intGerm_indep_of_rlaw C V d _ _ _ (GlobalTheory.T.isIntegralGaugedFormalGroupLaw_selfConjugateSquare C V O dd Y d I0 p)
  · intro C _ _ V O _ _ dd Y d _ I0 _ p _
    exact GlobalTheory.T.gaugeDeriv_eq_pairing_of_integralGaugedLaw C V d _ _ _ (GlobalTheory.T.isIntegralGaugedFormalGroupLaw_selfConjugateSquare C V O dd Y d I0 p)
  · intro C _ _ V O _ _ dd Y d _ I0 _ p
    exact GlobalTheory.T.gaugedFormalGroup_kernel_small_of_second C V d _ _ _ (GlobalTheory.T.isIntegralGaugedFormalGroupLaw_selfConjugateSquare C V O dd Y d I0 p)

end GlobalTheory.RowLaw
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.RowLawFormalStatementsSelfConjugateStatement

section

@[expose] public section

open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

theorem _root_.GlobalTheory.T.rowLaw_formal_statements_selfConjugate : CartSelfSt ∧ AxesSelfSt ∧ GermZeroSelfConjugate ∧ CEqSelfSt ∧ IndependenceBoundSelfConjugate := by
  first | exact @GlobalTheory.RowLaw.formal_statements_selfConj | exact GlobalTheory.RowLaw.formal_statements_selfConj | (intros; apply GlobalTheory.RowLaw.formal_statements_selfConj <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.RowDataSuppliedAtSelfConjugatePlaces

section

@[expose] public section

open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.RowAt

def pairCols (n : ℕ) : Fin (n / 2) × Fin 2 ↪ Fin n where
  toFun x := ⟨2 * x.1.val + x.2.val, by have := x.1.2; have := x.2.2; omega⟩
  inj' := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    have h1 : 2 * a.val + b.val = 2 * a'.val + b'.val := congrArg Fin.val h
    have := b.2
    have := b'.2
    exact Prod.ext (Fin.ext (by simp only; omega)) (Fin.ext (by simp only; omega))

def tyShift (g : Fin 2) : ZMod 2 ≃ ZMod 2 := if g = 0 then Equiv.refl _ else Equiv.addRight 1

theorem supplyC_selfConj : (∀ (p : ℕ) [Fact p.Prime], ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.UpFSt p) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (lv : Level H) (Xo : Moduli Dw lv) (c : Coeff lv) [StarRing (𝓞 E)], (∀ x : 𝓞 E, star x = H.bar x) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C3 : IntChart T io y) (C : Type) [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι → ∀ (k : ℕ) (Y : FBChart C V (𝓞 E) (chD C3.ch)), IsBC C3 ι k Y → y.IsAlg → ∀ (Orb : Type) [Fintype Orb] (lab : LabS E Orb), ArithS V io ι lab → Function.Surjective (fun x : Orb × ZMod 2 => lab.tau x.1 x.2) → lab.RankOK Dw → lab.j' < lab.n → ∀ (a : (E →+* ℂ) × ℕ → ℕ), DomW Dw a → ∀ (nW : ℕ) (ν : ℝ), (ν : EReal) ≤ nuLocC C3 (eOf T V) k a nW → SupplyC V Orb lab.n (lab.j + lab.j') (fun o s => Dw.mult (lab.tau o s)) (fun o s => gap (Dw.mult (lab.tau o s)) fun i => a (lab.tau o s, i)) nW ν := by
  intro hUp E _ _ _ H Dw lv Xo c _ hstar T io y C3 C _ _ V ι hι k Y hY halg Orb _ lab ha hsurj hr hj a hdom nW ν hν
  obtain ⟨p, hp, hsep, hrk⟩ := GlobalTheory.T.exists_selfConjugatePlaceData_intChart E H Dw lv Xo c hstar T io y C3 C V ι hι k Y hY Orb lab ha
  obtain ⟨hCart, hAx, hG0, hC, hR1⟩ := GlobalTheory.T.rowLaw_formal_statements_selfConjugate
  have hndg : NDG Y := GlobalTheory.T.biextension_nondegenerate_mod_maximalIdeal_integral_chart E H Dw lv Xo c hstar T io y C3 C V ι hι k Y hY
  have Hy : ∀ o, (Y.rawSelf (p o)).Hyps V := fun o =>
    { charZero := inferInstance
      algClosed := Y.algClosed
      l_odd := Y.l_odd
      k_unit := Y.k_unit
      cartH := hCart C V (𝓞 E) _ Y 2 _ (p o)
      rank := (hrk hr o).1
      axes := hAx C V (𝓞 E) _ Y 2 _ (p o)
      G0 := hG0 C V (𝓞 E) _ Y 2 _ (p o) _
      CEq := hC C V (𝓞 E) _ Y 2 _ (p o) (hrk hr o).1 _
      R1 := hR1 C V (𝓞 E) _ Y 2 _ (p o) (hrk hr o).1 _
        (GlobalTheory.T.rankMaximal_rawSelf_of_ndg C V (𝓞 E) _ Y 2 _ (p o) hndg _)
      R2 := GlobalTheory.T.rankMaximal_rawSelf_of_ndg C V (𝓞 E) _ Y 2 _ (p o) hndg _
      CH := GlobalTheory.T.characterBound_selfConjugate_degreeTwo_integralChart hUp E H Dw lv Xo c hstar T io y C3 C V ι hι k Y hY halg Orb lab ha hr p hp o _ }
  have hfl := fun o => GlobalTheory.T.flag_of_letterNumbering_rowData C V 2 (fun _ => ZMod 2) (fun _ s => Dw.mult (lab.tau o s)) tyShift
    (JJ fun _ => lab.II Dw o) ((Y.rawSelf (p o)).rowData (Hy o)) (by
      intro g x
      show (if g = 0 then (p o).ty0 x else (p o).ty0 x + (p o).hd) = _
      rw [hp.ty0, hp.hd]
      unfold tyShift
      split_ifs <;> rfl)
  have hrkF : ∀ o s, ((Y.rawSelf (p o)).rowData (Hy o)).rkF 0 s = Dw.mult (lab.tau o s) :=
    fun o s => (hfl o).1 0 s
  choose F hF using fun o => (hfl o).2
  refine ⟨fun o _ => lab.II Dw o, fun o => JJ fun _ => lab.II Dw o, inferInstance, inferInstance,
    fun o => (Y.rawSelf (p o)).rowData (Hy o), F, fun o => ⟨hp.n o, ?_, (hrk hr o).2, hrkF o⟩, ?_⟩
  · show (p o).j + (p o).j' = _
    rw [hp.j, hp.j']
  · refine RF.valBlocksC_G (n := nW / 2)
      (GlobalTheory.T.chartValues_bound_products_on_planes C V (𝓞 E) _ Y 2 Orb _ p Hy (chartLetterSystem C3 V ι a) (nW / 2) nW (pairCols nW) ν hsep
        (hν.trans (GlobalTheory.nuLocC_le_nuPlE_baseChange E H Dw lv Xo c T io y C3 C V ι hι k Y hY a nW)))
      GlobalTheory.JetProd.jetProd F nW (by omega) _
      (GlobalTheory.T.blockProd_mem_at_selfConj_places E H Dw lv Xo c hstar T io y C3 C V ι hι k Y hY Orb lab ha hsurj hr hj p hp Hy F
        (fun o g s q => (hF o g s q).2) a hdom (nW / 2) nW (pairCols nW)) ?_
    refine RF.blkAdmC _ F _ (fun o => (hrk hr o).2) (fun o => ?_) (fun o s k' hk => ?_)
    · show (p o).j' < (p o).n
      rw [hp.j', hp.n]
      exact hj
    · rw [hrkF]
      by_contra hlt
      apply hk
      unfold gap
      rw [if_neg (fun h => hlt h.2)]

end GlobalTheory.RowAt
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.RowDataSuppliedAtSelfConjugatePlacesStatement

section

@[expose] public section

open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

theorem _root_.GlobalTheory.T.rowData_supplied_at_selfConjugate_places : (∀ (p : ℕ) [Fact p.Prime], ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.UpFSt p) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (lv : Level H) (Xo : Moduli Dw lv) (c : Coeff lv) [StarRing (𝓞 E)], (∀ x : 𝓞 E, star x = H.bar x) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C3 : IntChart T io y) (C : Type) [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι → ∀ (k : ℕ) (Y : FBChart C V (𝓞 E) (chD C3.ch)), IsBC C3 ι k Y → y.IsAlg → ∀ (Orb : Type) [Fintype Orb] (lab : LabS E Orb), ArithS V io ι lab → Function.Surjective (fun x : Orb × ZMod 2 => lab.tau x.1 x.2) → lab.RankOK Dw → lab.j' < lab.n → ∀ (a : (E →+* ℂ) × ℕ → ℕ), DomW Dw a → ∀ (nW : ℕ) (ν : ℝ), (ν : EReal) ≤ nuLocC C3 (eOf T V) k a nW → SupplyC V Orb lab.n (lab.j + lab.j') (fun o s => Dw.mult (lab.tau o s)) (fun o s => gap (Dw.mult (lab.tau o s)) fun i => a (lab.tau o s, i)) nW ν := by
  first | exact @GlobalTheory.RowAt.supplyC_selfConj | exact GlobalTheory.RowAt.supplyC_selfConj | (intros; apply GlobalTheory.RowAt.supplyC_selfConj <;> assumption)
end
end
