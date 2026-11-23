module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.FramedFlatCoordinates
public import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComponentGeometricallyIrreducible
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetLineTrivialOfToroidal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchSecOfUnf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlatWeightRuleReadsNonvanishingDetSection
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsModelRuleSection
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FlatSectionAndDegree
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.BoundaryUnitValuationIntegral
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsAlgebraicOfNormConst
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.CountableFractionRingMvPolynomial
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.EvaluationLawsGenericFramesAtlasHold
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsBijectiveKappa
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.SectionEqZeroOfGenericFramedPointValues
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.Divisors.CommGroupMulMulEqMulInvMulMulMul
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsChartOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
import Development.AbelianVarietyTheory.Definitions.Divisors.LinearIndependentBasisCoords
import Development.AbelianVarietyTheory.Definitions.Divisors.MemSubPtsCutBaseChangeIff
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnitaryWeightExponentVectorSignatureWeightMuZero
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.EllipsoidStA
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HermitianCompactForm

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEqSmulIdemOfBdd

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


noncomputable section

namespace GlobalTheory.FlatLine

open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
  Formalism.L2.Pj GlobalTheory.AllWt

theorem isAlgebraic_of_norm_bdd {K Ω : Type} [Field K] [CharZero K] [Field Ω] [Algebra K Ω] [Algebra K ℂ]
    (P₀ : Ω →ₐ[K] ℂ) {b : Ω} {C : ℝ} (h : ∀ P : Ω →ₐ[K] ℂ, ‖P b‖ ≤ C) : IsAlgebraic K b := by
  by_contra hb
  have hb0 : P₀ b ≠ 0 := fun h0 => hb ((map_eq_zero P₀).1 h0 ▸ isAlgebraic_zero)
  have hpos : 0 < ‖P₀ b‖ := norm_pos_iff.2 hb0
  obtain ⟨N, hN⟩ := exists_nat_gt (C / ‖P₀ b‖)
  have hN0 : (N : K) ≠ 0 := by
    have : (0 : ℝ) < N := lt_of_le_of_lt (div_nonneg (le_trans (norm_nonneg _) (h P₀)) hpos.le) hN
    exact_mod_cast (Nat.cast_pos.1 this).ne'
  have hi : AlgebraicIndepOn K id ({b} : Set Ω) := algebraicIndependent_unique_type_iff.2 hb
  obtain ⟨T, hT, hbas⟩ := exists_isTranscendenceBasis_superset hi
  have hw : AlgebraicIndependent K fun i : T => P₀ i := hbas.1.map' P₀.injective
  have hw2 : AlgebraicIndependent K fun i : T => Polynomial.aeval (P₀ i) (Polynomial.C (N : K) * Polynomial.X) :=
    hw.polynomial_aeval_of_transcendental fun _ => Polynomial.transcendental _
      (by rw [Polynomial.natDegree_C_mul_X _ hN0]; exact one_ne_zero)
      (by rw [Polynomial.leadingCoeff_C_mul_X]; exact mem_nonZeroDivisors_of_ne_zero hN0)
  letI : Algebra (MvPolynomial T K) Ω := (MvPolynomial.aeval fun i : T => (i : Ω)).toRingHom.toAlgebra
  letI : Algebra (MvPolynomial T K) ℂ := (MvPolynomial.aeval fun i : T =>
    Polynomial.aeval (P₀ i) (Polynomial.C (N : K) * Polynomial.X)).toRingHom.toAlgebra
  haveI : FaithfulSMul (MvPolynomial T K) Ω := (faithfulSMul_iff_algebraMap_injective _ _).2 hbas.1
  haveI : FaithfulSMul (MvPolynomial T K) ℂ := (faithfulSMul_iff_algebraMap_injective _ _).2 hw2
  haveI : Algebra.IsAlgebraic (MvPolynomial T K) Ω :=
    haveI := hbas.isAlgebraic
    ⟨fun y => (IsAlgebraic.ringHom_of_comp_eq (f := hbas.1.aevalEquiv.symm.toRingHom) (g := RingHom.id Ω)
      (Algebra.IsAlgebraic.isAlgebraic y) hbas.1.aevalEquiv.symm.injective (RingHom.ext fun z => by
        obtain ⟨p, rfl⟩ := hbas.1.aevalEquiv.surjective z
        simp [RingHom.algebraMap_toAlgebra]))⟩
  let Q : Ω →ₐ[MvPolynomial T K] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  let P : Ω →ₐ[K] ℂ := { Q.toRingHom with
    commutes' := fun a => by
      have := Q.commutes (MvPolynomial.C a)
      simpa [RingHom.algebraMap_toAlgebra] using this }
  have h1 : P b = (N : ℂ) * P₀ b := by
    show Q b = _
    have := Q.commutes (MvPolynomial.X ⟨b, hT rfl⟩)
    simpa [RingHom.algebraMap_toAlgebra, map_natCast] using this
  have h2 := h P
  rw [h1, norm_mul, Complex.norm_natCast] at h2
  have h3 : C < N * ‖P₀ b‖ := (div_lt_iff₀ hpos).1 hN
  linarith

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

theorem exists_eq_smul_idem_of_bdd {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (hσ : GoodEmb c σ) (hU : IsUnf U)
    (hF : FnAlgClosed (Xo := Xo) (c := c)) {Z : Comp Xo c} {g : Rul Xo c} (hg : g ∈ secZ Xo c 0) (hs : g ∈ suppOn Z) {C : ℝ}
    (hb : ∀ z ∈ framesOn U Z, ‖rdU U g z.1 z.2‖ ≤ C) : ∃ a : c.F, g = a • idem Z := by
  obtain ⟨hL, -, h, hA⟩ := GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c
  obtain ⟨⟨P₀⟩, hP⟩ := GlobalTheory.GenericReading.embedding_read_at_frame E H Dw l Xo c σ r U hσ hU h Z
  have hi := idem_mem_secZ Z
  rw [secZ_zero_eq] at hg hi
  have key : ∀ P : Om Z →ₐ[c.F] CAt σ, ‖toC (P (evC h Z g))‖ ≤ C := fun P => by
    obtain ⟨k, x, y', t, hm, ht⟩ := hP P
    obtain ⟨w, -, hw⟩ := GlobalTheory.CompBij.rdU_eq_of_reads U h k Z x P y' t hm ht 0 0
    have hz : (⟨k, x.1⟩ : Σ k, Frame (U.X k).Ψ r) ∈ framesOn U Z :=
      ⟨x.2, liesOn_frBor ht (liesOn_frMap hm (liesOn_genFr h Z))⟩
    have h1 := hw _ hi
    have h2 : rdU U (idem Z) k x = 1 := by
      simp only [rdU, LinearMap.coe_mk, AddHom.coe_mk, x.2, dif_pos]
      exact evR_idem (S := CAt σ) hz.2 (haveI : IsReduced (CAt σ) := inferInstanceAs (IsReduced ℂ); hL.test _ _)
    have h3 : evC h Z (idem Z) = 1 := evR_idem (liesOn_genFr h Z) (hL.test _ _)
    rw [h2, h3, map_one, mul_one] at h1
    rw [← hw g hg, h1]
    exact (congrArg norm (one_mul _)).trans_le (hb _ hz)
  letI : Algebra c.F ℂ := σ.toAlgebra
  obtain ⟨a, ha⟩ := hF Z _ (isAlgebraic_of_norm_bdd (K := c.F) (b := evC h Z g) P₀ fun P => key P)
  refine ⟨a, sub_eq_zero.1 (GlobalTheory.Reg.sec_eq_zero_of_generic_values E H Dw l Xo c hL h (hA h) 0 0 _
    (sub_mem hg (Submodule.smul_mem _ _ hi)) fun Z' => ?_)⟩
  by_cases hZ : Z' = Z
  · subst hZ
    have h3 : evC h Z' (idem Z') = 1 := evR_idem (liesOn_genFr h Z') (hL.test _ _)
    have h4 := evalAt_add (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) g ((-a) • idem Z')
      (genFr h Z')
    have h5 := evalAt_smul (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (-a) (idem Z')
      (genFr h Z')
    rw [sub_eq_add_neg, ← neg_smul]
    refine h4.trans ?_
    rw [h5]
    show evC h Z' g + algebraMap _ _ (-a) * evC h Z' (idem Z') = 0
    rw [h3, ← ha, map_neg, mul_one, add_neg_cancel]
  · exact evC_eq_zero h hZ (sub_mem hs (Submodule.smul_mem _ _ (idem_mem_suppOn Z)))

end GlobalTheory.FlatLine

namespace GlobalTheory.CovTop

end GlobalTheory.CovTop
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.KoecherPrincipleUnitConstant

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

noncomputable section
namespace GlobalTheory.FlatLine
open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
  Formalism.L2.Pj GlobalTheory.AllWt
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}
end GlobalTheory.FlatLine
namespace GlobalTheory.CovTop
theorem koecher_principle_unit_constant : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (g h : Rul Y.d.Xo₂ Y.d.c₂), g ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ 0 → h ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ 0 → GlobalTheory.FlatLine.idem Z * g = g → GlobalTheory.FlatLine.idem Z * h = h → g * h = GlobalTheory.FlatLine.idem Z → (∀ σ, GoodEmb Y.d.c₂ σ → ∃ C : ℝ, ∀ z ∈ framesOn (Y.U σ) Z, GlobalTheory.AllWt.homN (Y.U σ) (xiR D) 0 g z ≤ C ∧ GlobalTheory.AllWt.homN (Y.U σ) (xiR D) 0 h z ≤ C) → ∃ a : Y.d.c₂.F, g = a • GlobalTheory.FlatLine.idem Z := by
  intro _ D T j Y e o hY _ Z g h hg _ hgi _ _ hB
  have hσ := goodEmb_goodOf Y.d.c₂ Y.d.c₂.F.val.toRingHom
  obtain ⟨C, hC⟩ := hB _ hσ
  have hs : g ∈ GlobalTheory.AllWt.suppOn Z := by
    rw [← hgi, mul_comm]
    exact GlobalTheory.AllWt.mul_mem_suppOn _ (GlobalTheory.FlatLine.idem_mem_suppOn Z)
  exact GlobalTheory.FlatLine.exists_eq_smul_idem_of_bdd (Y.U _) hσ (hY.unf _ hσ) hY.geo hg hs (C := C) fun z hz => by
    have h1 := (hC z hz).1
    rwa [GlobalTheory.FlatLine.homN_zero] at h1
end GlobalTheory.CovTop
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ExistsArchimedeanSectionWithDenominator

section

@[expose] public section

section
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatCore GlobalTheory.LineNorm GlobalTheory.FlatModel
open GlobalTheory.FlatDenom
noncomputable section
namespace GlobalTheory.FlatDenom
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
open GlobalTheory.DetLine GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal in
theorem exists_horizontal_section_flat_model (hp : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems) (hpos : 1 ≤ Dw.p + Dw.q) (hgeo : FnAlgClosed (Xo := Xo) (c := c)) (Z : Comp Xo c)
    (τ : Psi H) : ∃ (Y : Model Xo c (RingHom.id c.F)) (V : (Xo.XF c).Opens) (sig : GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.Rule Y V τ.1),
      (V : Set (Xo.XF c)) = Z ∧ sig ∈ GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.sections Y V τ.1 ∧ GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.VanishesNowhere sig ∧
        GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.IsHorizontal sig := by
  obtain ⟨Y, -⟩ := hp.p1 E H Dw hpos l Xo c
  obtain ⟨V, hV, hirr⟩ := GlobalTheory.GeomIrrComp.exists_open_irreducibleSpace_baseChange E H Dw l Xo c hgeo Z
  have hc : IsClosed (V : Set (Xo.XF c)) := hV ▸ isClosed_of_mem_irreducibleComponents _ Z.2
  have hG : GeometricallyConnected (V.ι ≫ toF Xo c) :=
    ⟨geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms.2 fun K _ _ => by
      have := hirr K (algebraMap c.F K)
      exact (inferInstance : ConnectedSpace ↑(pullback (V.ι ≫ toF Xo c) (spMap (algebraMap c.F K))))⟩
  obtain ⟨-, σ, -, -, hf, -, hY⟩ := detLineTrivial_of_toroidal hp.p1 E H Dw l Xo c V hc hG τ.1 τ.2
  obtain ⟨σb, hs, hz, hres, -⟩ := hY _ _ Y (GlobalTheory.FlatRow.isNormal_genFibre Y)
  refine ⟨Y, V, fun R _ _ a => σb R a.x a.v a.w, hV, fun R R' _ _ j j' a a' f M N h => ?_,
    fun R _ j a => hz R j _ _ _ (PeriodFlat.frY_framed a), PeriodFlat.isHorizontal_of_isFlatAt hc hres hz hf⟩
  rw [mul_comm, mul_comm _ N.det]
  exact (sec_chg hs (PeriodFlat.frY_framed a) (PeriodFlat.frY_framed a') ⟨h.2.1, h.2.2⟩).symm
variable {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ} {Z : Comp Xo c} {τ : Psi H}
theorem exists_archimedean_section_of_unramified (hP : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems) (hpq : 1 ≤ Dw.p + Dw.q) (hA : l.A = 1)
    (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ)) (hgeo : FnAlgClosed (Xo := Xo) (c := c)) (x : ℝ) (Z : Comp Xo c) (τ : Psi H) :
    ∃ (s : ArchSec U x Z (flatWt Dw τ)) (m : ℕ), 0 < m ∧
      ∀ la, ∀ v ∈ valOn Z la, 0 ≤ v ((m : c.F) • s.sig) ∧ 0 ≤ v ((m : c.F) • s.inv) := by
  obtain ⟨Y, V, sig, hV, hs, hnv, hh⟩ := _root_.GlobalTheory.FlatDenom.exists_horizontal_section_flat_model hP hpq hgeo Z τ
  obtain ⟨f, g, hf, hg, hfi, hgi, hfg, hR⟩ := GlobalTheory.BdryUnit.ReadDet.exists_reads E H Dw l Xo c Y Z V τ sig hV hs hnv
  choose b hb hb' using fun σ => const_length (U _) x (goodEmb_goodOf c σ) (hU _ (goodEmb_goodOf c σ)) hgeo hV hnv hh hR
  exact ⟨⟨f, g, hf, hg, hfi, hgi, hfg, b, hb, hb'⟩, archSec_denom hpq hA _ fun T io y₀ h0 hZ =>
    _root_.GlobalTheory.BdryUnitVal.boundary_unit_at_integral_points hP E H Dw l Xo c Y Z V τ sig f hV hs hnv hR T io y₀ h0 hZ⟩
end GlobalTheory.FlatDenom
open Formalism.BasicNotions GlobalTheory.CovTop in
theorem GlobalTheory.FlatDenom.exists_archimedean_section_with_denominator : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (τ : Psi T.Q.H), ∃ (s : GlobalTheory.FlatCore.ArchSec Y.U (xiR D) Z (GlobalTheory.FlatLine.flatWt (T.Q.Dw j) τ)) (m : ℕ), 0 < m ∧ ∀ la, ∀ v ∈ GlobalTheory.FlatLine.valOn Z la, 0 ≤ v ((m : Y.d.c₂.F) • s.sig) ∧ 0 ≤ v ((m : Y.d.c₂.F) • s.inv) := by
  intro hP D T j Y e o hG _ Z τ
  have hr : 1 ≤ D.R.r := by unfold Ranks.r; have := D.R.two_le_m; omega
  have h1 : D.R.r = (T.Q.Dw j).p + (T.Q.Dw j).q := (hG.unf Y.d.c₂.F.val.toRingHom rfl).1
  exact _root_.GlobalTheory.FlatDenom.exists_archimedean_section_of_unramified hP (by omega) hG.lev.2 hG.unf hG.geo _ Z τ
namespace GlobalTheory.FlatDenom
section Powers
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ)
  (Z : Comp Xo c)
variable {U x Z} {la la' : GlobalTheory.AllWt.Weight Dw}
end Powers
end GlobalTheory.FlatDenom
open Formalism.BasicNotions GlobalTheory.CovTop in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem GlobalTheory.FlatDenom.unit_pow_clears_denominator_flat_model : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (n : ℤ) (Z : Comp Y.d.Xo₂ Y.d.c₂) (τ : Psi T.Q.H) (s i : Rul Y.d.Xo₂ Y.d.c₂), (s ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ (Formalism.L2.Pj.exZ (T.Q.Dw j) (wtOf (T.Q.Dw j) (n • GlobalTheory.FlatLine.flatWt (T.Q.Dw j) τ) 0)) ∧ i ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ (-Formalism.L2.Pj.exZ (T.Q.Dw j) (wtOf (T.Q.Dw j) (n • GlobalTheory.FlatLine.flatWt (T.Q.Dw j) τ) 0)) ∧ GlobalTheory.FlatLine.idem Z * s = s ∧ GlobalTheory.FlatLine.idem Z * i = i ∧ s * i = GlobalTheory.FlatLine.idem Z ∧ (∀ σ, GoodEmb Y.d.c₂ σ → ∃ C : ℝ, ∀ z ∈ framesOn (Y.U σ) Z, GlobalTheory.AllWt.homN (Y.U σ) (xiR D) (wtOf (T.Q.Dw j) (n • GlobalTheory.FlatLine.flatWt (T.Q.Dw j) τ) 0) s z ≤ C ∧ GlobalTheory.AllWt.homN (Y.U σ) (xiR D) (-(wtOf (T.Q.Dw j) (n • GlobalTheory.FlatLine.flatWt (T.Q.Dw j) τ) 0)) i z ≤ C)) → ∃ m : ℕ, 0 < m ∧ ∀ la, ∀ v ∈ GlobalTheory.FlatLine.valOn Z la, 0 ≤ v ((m : Y.d.c₂.F) • s) ∧ 0 ≤ v ((m : Y.d.c₂.F) • i) := by
  intro hP D T j Y e o hY hE n Z τ s i ⟨hs, hi, hIs, hIi, hsi, hb⟩
  have h₁ : HasBddSec Y.U (xiR D) Z (flatWt (T.Q.Dw j) τ) := _root_.GlobalTheory.FlatDenom.exists_archimedean_section_with_denominator hP D T j Y e o hY hE Z τ
  obtain ⟨s₀, m₀, hm₀, h₀⟩ := h₁.zsmul n
  generalize n • GlobalTheory.FlatLine.flatWt (T.Q.Dw j) τ = la at *
  have hw : wtOf (T.Q.Dw j) la 0 + wtOf (T.Q.Dw j) (-la) 0 = 0 := by
    rw [← GlobalTheory.FlatLine.wtOf_add', add_neg_cancel, GlobalTheory.AllWt.wtOf_zero]
  have hg : s * s₀.inv ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ 0 := by
    have h := GlobalTheory.AllWt.mul_mem_secZ hs s₀.inv_mem
    have h0 : Formalism.L2.Pj.exZ (T.Q.Dw j) (wtOf (T.Q.Dw j) la 0) + -GlobalTheory.AllWt.exOf (T.Q.Dw j) la 0 = 0 :=
      add_neg_cancel _
    rwa [h0] at h
  have hh : i * s₀.sig ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ 0 := by
    have h := GlobalTheory.AllWt.mul_mem_secZ hi s₀.sig_mem
    have h0 : -Formalism.L2.Pj.exZ (T.Q.Dw j) (wtOf (T.Q.Dw j) la 0) + GlobalTheory.AllWt.exOf (T.Q.Dw j) la 0 = 0 :=
      neg_add_cancel _
    rwa [h0] at h
  have hIg : GlobalTheory.FlatLine.idem Z * (s * s₀.inv) = s * s₀.inv := by rw [← mul_assoc, hIs]
  have hIh : GlobalTheory.FlatLine.idem Z * (i * s₀.sig) = i * s₀.sig := by rw [← mul_assoc, hIi]
  have hgh : s * s₀.inv * (i * s₀.sig) = GlobalTheory.FlatLine.idem Z := by
    calc s * s₀.inv * (i * s₀.sig) = (s * i) * (s₀.sig * s₀.inv) := by ring
      _ = _ := by rw [hsi, s₀.mul_inv, GlobalTheory.FlatLine.idem_mul_idem]
  have hbd : ∀ σ, GoodEmb Y.d.c₂ σ → ∃ C : ℝ, ∀ z ∈ framesOn (Y.U σ) Z,
      GlobalTheory.AllWt.homN (Y.U σ) (xiR D) 0 (s * s₀.inv) z ≤ C ∧
        GlobalTheory.AllWt.homN (Y.U σ) (xiR D) 0 (i * s₀.sig) z ≤ C := by
    intro σ hσ
    obtain ⟨C, hC⟩ := hb σ hσ
    have hgo : Formalism.L2.Pj.goodOf Y.d.c₂ σ = σ := if_pos hσ
    have hN : ∀ σ'' (_ : Formalism.L2.Pj.goodOf Y.d.c₂ σ = σ''), ∀ z ∈ framesOn (Y.U σ'') Z,
        GlobalTheory.AllWt.homN (Y.U σ'') (xiR D) (wtOf (T.Q.Dw j) la 0) s₀.sig z = s₀.cInf σ ∧
        GlobalTheory.AllWt.homN (Y.U σ'') (xiR D) (wtOf (T.Q.Dw j) (-la) 0) s₀.inv z = (s₀.cInf σ)⁻¹ := by
      rintro _ rfl z hz
      exact ⟨homN_sig s₀ hz, homN_inv s₀ hz⟩
    have hpos := s₀.cInf_pos σ
    refine ⟨max (C * (s₀.cInf σ)⁻¹) (C * s₀.cInf σ), fun z hz => ?_⟩
    have hd : z.2 ∈ ((Y.U σ).X z.1).dom := hz.1
    obtain ⟨h1, h2⟩ := hN σ hgo z hz
    obtain ⟨c1, c2⟩ := hC z hz
    have hev : Even (-(wtOf (T.Q.Dw j) la 0)).2 := by
      simpa using (GlobalTheory.AllWt.even_wtOf (Dw := T.Q.Dw j) la 0).neg
    have e1 := GlobalTheory.AllWt.homN_mul (Y.U σ) (xiR D) (GlobalTheory.AllWt.even_wtOf la 0) (GlobalTheory.AllWt.even_wtOf (-la) 0)
      s s₀.inv z hd
    rw [hw, h2] at e1
    have e2 := GlobalTheory.AllWt.homN_mul (Y.U σ) (xiR D) hev (GlobalTheory.AllWt.even_wtOf la 0) i s₀.sig z hd
    rw [neg_add_cancel, h1] at e2
    constructor
    · rw [e1]; exact (mul_le_mul_of_nonneg_right c1 (inv_pos.2 hpos).le).trans (le_max_left _ _)
    · rw [e2]; exact (mul_le_mul_of_nonneg_right c2 hpos.le).trans (le_max_right _ _)
  obtain ⟨a, ha⟩ := _root_.GlobalTheory.CovTop.koecher_principle_unit_constant hP D T j Y e o hY hE Z _ _ hg hh hIg hIh hgh hbd
  have hsa : s = a • s₀.sig := by
    calc s = s * GlobalTheory.FlatLine.idem Z := by rw [mul_comm, hIs]
      _ = (s * s₀.inv) * s₀.sig := by rw [← s₀.mul_inv]; ring
      _ = a • s₀.sig := by rw [ha, smul_mul_assoc, s₀.idem_sig]
  by_cases ha0 : a = 0
  · refine ⟨1, one_pos, fun w v hv => ?_⟩
    exfalso
    have h1 := GlobalTheory.FlatLine.val_idem hv
    rw [← hsi, hsa, ha0, zero_smul, zero_mul, (GlobalTheory.FlatLine.isVal_valOn hv).zero] at h1
    exact EReal.top_ne_zero h1
  have hia : i = a⁻¹ • s₀.inv := by
    calc i = i * GlobalTheory.FlatLine.idem Z := by rw [mul_comm, hIi]
      _ = i * (a • s₀.sig * a⁻¹ • s₀.inv) := by rw [GlobalTheory.FlatLine.smul_mul_inv_smul ha0, s₀.mul_inv]
      _ = (s * i) * a⁻¹ • s₀.inv := by rw [← hsa]; ring
      _ = a⁻¹ • s₀.inv := by rw [hsi, mul_smul_comm, s₀.idem_inv]
  obtain ⟨n₁, hn₁, k₁⟩ := exists_nat_vAdd ha0
  obtain ⟨n₂, hn₂, k₂⟩ := exists_nat_vAdd (inv_ne_zero ha0)
  have hnat : ∀ (k : ℕ), 0 < k → ∀ w, 0 ≤ vAdd w (k : Y.d.c₂.F) := fun k hk w => by
    have := Formalism.L2.Pj.vAdd_int_nonneg w (a := (k : 𝓞 Y.d.c₂.F)) (by
      have : (k : Y.d.c₂.F) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
      simpa using this)
    simpa using this
  have key : ∀ (b : Y.d.c₂.F) (k k' : ℕ) (f : Rul Y.d.Xo₂ Y.d.c₂), b ≠ 0 → 0 < k → 0 < k' → ∀ w, ∀ v ∈ valOn Z w,
      0 ≤ vAdd w ((k : Y.d.c₂.F) * b) → 0 ≤ v ((m₀ : Y.d.c₂.F) • f) →
      0 ≤ v (((k' * k * m₀ : ℕ) : Y.d.c₂.F) • b • f) := fun b k k' f hb hk hk' w v hv h1 h2 => by
    have hV := GlobalTheory.FlatLine.isVal_valOn hv
    have e1 : ((k' * k * m₀ : ℕ) : Y.d.c₂.F) • b • f = (k' : Y.d.c₂.F) • ((k : Y.d.c₂.F) * b) • (m₀ : Y.d.c₂.F) • f := by
      simp only [smul_smul]
      congr 1
      push_cast
      ring
    rw [e1, hV.smul _ _ (Nat.cast_ne_zero.2 hk'.ne'), hV.smul _ _ (mul_ne_zero (Nat.cast_ne_zero.2 hk.ne') hb)]
    exact add_nonneg (EReal.coe_nonneg.2 (by exact_mod_cast hnat k' hk' w))
      (add_nonneg (EReal.coe_nonneg.2 (by exact_mod_cast h1)) h2)
  refine ⟨n₂ * n₁ * m₀, Nat.mul_pos (Nat.mul_pos hn₂ hn₁) hm₀, fun w v hv => ⟨?_, ?_⟩⟩
  · rw [hsa]
    exact key a n₁ n₂ _ ha0 hn₁ hn₂ w v hv (k₁ w) (h₀ w v hv).1
  · rw [hia, mul_comm n₂]
    exact key a⁻¹ n₂ n₁ _ (inv_ne_zero ha0) hn₂ hn₁ w v hv (k₂ w) (h₀ w v hv).2
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.InverseOfFlatUnitIsIntegral

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

noncomputable section
namespace GlobalTheory.FlatUnitInt
theorem flat_unit_inverse_integral : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (n : ℤ) (Z : Comp Y.d.Xo₂ Y.d.c₂) (τ : Psi T.Q.H) (s i : Rul Y.d.Xo₂ Y.d.c₂), (s ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ (Formalism.L2.Pj.exZ (T.Q.Dw j) (wtOf (T.Q.Dw j) (n • GlobalTheory.FlatLine.flatWt (T.Q.Dw j) τ) 0)) ∧ i ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ (-Formalism.L2.Pj.exZ (T.Q.Dw j) (wtOf (T.Q.Dw j) (n • GlobalTheory.FlatLine.flatWt (T.Q.Dw j) τ) 0)) ∧ GlobalTheory.FlatLine.idem Z * s = s ∧ GlobalTheory.FlatLine.idem Z * i = i ∧ s * i = GlobalTheory.FlatLine.idem Z ∧ (∀ σ, GoodEmb Y.d.c₂ σ → ∃ C : ℝ, ∀ z ∈ framesOn (Y.U σ) Z, GlobalTheory.AllWt.homN (Y.U σ) (xiR D) (wtOf (T.Q.Dw j) (n • GlobalTheory.FlatLine.flatWt (T.Q.Dw j) τ) 0) s z ≤ C ∧ GlobalTheory.AllWt.homN (Y.U σ) (xiR D) (-(wtOf (T.Q.Dw j) (n • GlobalTheory.FlatLine.flatWt (T.Q.Dw j) τ) 0)) i z ≤ C)) → ∃ m : ℕ, 0 < m ∧ ∀ la, ∀ v ∈ GlobalTheory.FlatLine.valOn Z la, 0 ≤ v ((m : Y.d.c₂.F) • s) ∧ 0 ≤ v ((m : Y.d.c₂.F) • i) :=
  _root_.GlobalTheory.FlatDenom.unit_pow_clears_denominator_flat_model
end GlobalTheory.FlatUnitInt
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


theorem _root_.GlobalTheory.T.inverse_of_flat_unit_isIntegral : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (n : ℤ) (Z : Comp Y.d.Xo₂ Y.d.c₂) (τ : Psi T.Q.H) (s i : Rul Y.d.Xo₂ Y.d.c₂), (s ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ (Formalism.L2.Pj.exZ (T.Q.Dw j) (wtOf (T.Q.Dw j) (n • GlobalTheory.FlatLine.flatWt (T.Q.Dw j) τ) 0)) ∧ i ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ (-Formalism.L2.Pj.exZ (T.Q.Dw j) (wtOf (T.Q.Dw j) (n • GlobalTheory.FlatLine.flatWt (T.Q.Dw j) τ) 0)) ∧ GlobalTheory.FlatLine.idem Z * s = s ∧ GlobalTheory.FlatLine.idem Z * i = i ∧ s * i = GlobalTheory.FlatLine.idem Z ∧ (∀ σ, GoodEmb Y.d.c₂ σ → ∃ C : ℝ, ∀ z ∈ framesOn (Y.U σ) Z, GlobalTheory.AllWt.homN (Y.U σ) (xiR D) (wtOf (T.Q.Dw j) (n • GlobalTheory.FlatLine.flatWt (T.Q.Dw j) τ) 0) s z ≤ C ∧ GlobalTheory.AllWt.homN (Y.U σ) (xiR D) (-(wtOf (T.Q.Dw j) (n • GlobalTheory.FlatLine.flatWt (T.Q.Dw j) τ) 0)) i z ≤ C)) → ∃ m : ℕ, 0 < m ∧ ∀ la, ∀ v ∈ GlobalTheory.FlatLine.valOn Z la, 0 ≤ v ((m : Y.d.c₂.F) • s) ∧ 0 ≤ v ((m : Y.d.c₂.F) • i) := by
  first | exact @_root_.GlobalTheory.FlatUnitInt.flat_unit_inverse_integral | exact _root_.GlobalTheory.FlatUnitInt.flat_unit_inverse_integral | (intros; apply _root_.GlobalTheory.FlatUnitInt.flat_unit_inverse_integral <;> assumption)
end
end
end
