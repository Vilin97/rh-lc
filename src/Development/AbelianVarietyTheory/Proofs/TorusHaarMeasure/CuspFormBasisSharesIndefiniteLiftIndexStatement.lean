module

public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.GrowthConstantBoundGcR
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.SWEqSOf
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.GlobalFamilyData
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
public import Formalism.LocalToGlobal.ProjectiveLattices.IntegralExtensionOfRegR1
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroOfReducedInputs
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.AdmissibleModuleIffLatticeQuotients
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.AnalyticFactsOfThetaDataOnModelsStatement
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsValueBasisInSpanningForms
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.InBasisIffPointValuesLinearIndependentSpanStatement
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.InContainMROfAnFacts
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.NonemptyHeightOneSpectrumRingOfIntegers
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ShareRdOfInBasis
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ShareRhoROfAnFacts
public import Formalism.LocalToGlobal.ProjectiveLattices.TieUpA
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.MemFormsLowCoeffsVanishIffFourierJacobiStatement
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.PoincarePointwiseStatement
import Formalism.LocalToGlobal.ProjectiveLattices.RosatiLatticeNorms.LinkFD
import Mathlib.Tactic.Linter.Style
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SiegelSpaceAlgebraHolds
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ModelsAt
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
import Mathlib.Algebra.Order.Star.Int
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FinrankHost
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.CuspReadingsSpanModelFormsShiftedWeightsStatement
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ThetaArchimedeanDataIndefiniteModels

-- Source module: Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.H2XNIffH2

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn

namespace GlobalTheory.RunIn

section General

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (n : SecNorm B) (X : PJ D B P j) (E : PtExt X)
  (hM : IntAtExt X E)

abbrev xN : PJ D n.base P j := PJ.tol2NormAlt n.N n.h0 n.h1 n.h2 n.h3 n.h4 (xplus X E hM)

def globalFamilyDataBaseChange {ka wL wF : WeightFamilies.Wt D j} (G : EtaleWeightGaps.GlobalFamilyData X ka wL wF) : EtaleWeightGaps.GlobalFamilyData (xN n X E hM) ka wL wF where
  N := G.N
  w := G.w
  del := G.del
  th' := G.th'
  rz := G.rz
  alz := G.alz
  th0 := G.th0
  zc := G.zc
  rq := G.rq
  th := G.th
  iet := G.iet
  et := G.et
  mx := G.mx

end General

end GlobalTheory.RunIn
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.MaximalCuspsNoLowCoefficientIffFourierJacobi

section

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.Pj.QAt Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions GlobalTheory.ArcCM GlobalTheory.Shares

namespace GlobalTheory.MaxCuspRecord

theorem mem_MggK_of_rho_eq_zero {D : D7} (X : WeightFamilies.Prov D) (CR Tt cc : ℝ) (j : ℕ) (ka : WeightFamilies.Wt D j)
    (h0 : WeightFamilies.rho D j = 0) (F : X.Cusp j ka) : F ∈ WeightFamilies.MggK X CR Tt cc j ka := by
  unfold WeightFamilies.MggK
  simp only [Submodule.mem_iInf]
  rintro cu χ ⟨xi, -, hne, -⟩
  exact absurd (funext fun i => absurd i.isLt (by omega)) hne




theorem tieMaxCusp : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ), InR D j → ∀ (ka : WeightFamilies.Wt D j) (CR Tt cc : ℝ), TieMaxCuspSt h j CR Tt cc ka := by
  intro D T h j hj ka CR Tt cc F
  rcases lt_or_eq_of_le hj.2 with hlt | hjm
  · exact (GlobalTheory.T.mem_forms_low_coeffs_vanish_iff_fourierJacobi D T.toCore h.toLawsCore j ka CR Tt cc hj hlt F).2
  · have h0 : WeightFamilies.rho D j = 0 := by
      show D.R.m - j = 0
      omega
    refine ⟨fun _ k => ?_, fun _ => mem_MggK_of_rho_eq_zero _ CR Tt cc j ka h0 F⟩
    have hU : IsUnf (T.U j T.σ₀) := h.unf j hj T.σ₀ T.good_σ₀
    have hq : (T.Q.Dw j).q = 0 := (h.pins.2.2.2 j hj).2.1.trans h0
    have hp0 : ((T.U j T.σ₀).X k).p0 = 0 := ((hU.2.1 k).1).trans hq
    have hFc : (F.1 : T.R j) ∈ cusp (T.Q.Xo j) T.Q.c (T.U j) (wtA ka) ka.n := cutR_le T.C j ka F.2
    have hcusp := ((mem_cusp (T.Q.Xo j) T.Q.c (T.U j) (wtA ka) ka.n F.1).1 hFc).2 T.σ₀ T.good_σ₀
    exact ⟨Formalism.L2.Pj.abelian₂.holSub_SS siegelSpaceAlgebra_holds _ _ hcusp k, fun ξ hξ =>
      absurd hξ (GlobalTheory.PoincareSeriesCompare.not_isIso_of_definite _ (Or.inl hp0) ξ)⟩

end GlobalTheory.MaxCuspRecord
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.MaximalCuspsNoLowCoefficientIffFourierJacobiStatement

section

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.Pj.QAt Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions GlobalTheory.ArcCM GlobalTheory.Shares

theorem _root_.GlobalTheory.T.maximalCusps_noLowCoefficient_iff_fourierJacobi : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ), InR D j → ∀ (ka : WeightFamilies.Wt D j) (CR Tt cc : ℝ), TieMaxCuspSt h j CR Tt cc ka := by
  first | exact @GlobalTheory.MaxCuspRecord.tieMaxCusp | exact GlobalTheory.MaxCuspRecord.tieMaxCusp | (intros; apply GlobalTheory.MaxCuspRecord.tieMaxCusp <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsInBasisSharesInContain

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.RunIn GlobalTheory.Shares

namespace GlobalTheory.Shares

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 1000000 in
theorem exists_inBasis_shares_inContain : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (n : SecNorm (recB h.toLawsCore)) (ka wL wF : WeightFamilies.Wt D j) (G₀ : GlobalFamilyData (recPlusN h j hj n) ka wL wF) (Tn : ℕ) (CR c : ℝ) (S : Scal n.base), addL wF wL Tn = ka → 2 ≤ WeightFamilies.dimY D j → 11 * WeightFamilies.dimY D j ^ 2 ≤ Tn → Nonempty (ArchAt h j G₀.w wF Tn (WeightFamilies.c1 D CR Tn c j)) → (∀ k : ℕ, RdOnto h j (addL wF wL k)) → MggOnto h j CR Tn c ka → LatAt n.base j ka → (∃ β : ℝ, ShortG (recPlusN h j hj n) ((recPlusN h j hj n).wF0 wL wF) ((recPlusN h j hj n).Thc S.s0 ((recPlusN h j hj n).wF0 wL wF)) β) → ∀ Sh : Set ((recB h.toLawsCore).Cusp j wF), Submodule.span (recB h.toLawsCore).KO Sh = ⊤ → ∃ (del : ℕ) (th' : Fin del → n.base.Cusp j wF), (∀ i, th' i ∈ Sh) ∧ ∀ rz alz th0 zc rq th iet et, (∀ la, InBasis (FamilyHypotheses.refill G₀ del th' rz alz th0 zc rq th iet et) la) ∧ ShareRd (D := D) (j := j) Tn del ((recPlusN h j hj n).rk ka (n.base.Mlat j ka)) ∧ ShareRhoR (FamilyHypotheses.refill G₀ del th' rz alz th0 zc rq th iet et) S Tn ((recPlusN h j hj n).rk ka (n.base.Mlat j ka)) ∧ ShareRhoP (D := D) (j := j) Tn (WeightFamilies.rhoP n.base CR Tn c j ka) ((recPlusN h j hj n).rk ka (n.base.Mlat j ka)) ∧ ∀ la, InContainMR (FamilyHypotheses.refill G₀ del th' rz alz th0 zc rq th iet et) la S CR Tn c := by
  intro D T h j hj n ka wL wF G₀ Tn CR c S hka hd2 hT hArch hRd hMgg hLat hShort Sh hSh

  obtain ⟨R, t, δ, xs, hgen, hA⟩ :=
    GlobalTheory.T.analyticFacts_of_thetaData_on_models D T h j hj n G₀.N ka wL wF G₀.w Tn CR c hka hArch hRd hMgg
      (GlobalTheory.T.maximalCusps_noLowCoefficient_iff_fourierJacobi D T h j hj ka CR (Tn : ℝ) c)

  obtain ⟨θ, hθS, hθ⟩ :=
    exists_valueBasis_in_spanning D n.base _ j (recPlusN h j hj n) ka wL wF G₀.N G₀.w R t Tn _ δ xs hA Sh hSh
  refine ⟨δ, θ, hθS, ?_⟩
  intro rz alz th0 zc rq th iet et
  have hdT : WeightFamilies.dimY D j < Tn := by nlinarith
  have hd0 : 0 < WeightFamilies.dimY D j := by omega

  have hA' : AnFacts R (FamilyHypotheses.refill G₀ δ θ rz alz th0 zc rq th iet et).w t ka wF Tn
      (WeightFamilies.MggK n.base CR Tn c j ka) xs := hA
  have hB : ∀ la, InBasis (FamilyHypotheses.refill G₀ δ θ rz alz th0 zc rq th iet et) la := fun la =>
    (GlobalTheory.T.inBasis_iff_pointValues_linearIndependent_span D n.base _ j (recPlusN h j hj n) ka wL wF (FamilyHypotheses.refill G₀ δ θ rz alz th0 zc rq th iet et)
      R t Tn _ δ xs hgen hA' hka la).2 ⟨hθ, rfl⟩

  obtain ⟨β, Sg, hSg, hspan, -⟩ := hShort
  have hle := Submodule.span_mono (R := n.base.KO) hSg
  rw [hspan] at hle
  have hTop := top_le_iff.mp hle
  obtain ⟨la₀⟩ := nonempty_heightOneSpectrum_ringOfIntegers n.base.KO
  refine ⟨hB, ?_, ?_, ?_, ?_⟩
  · exact shareRd_of_inBasis D n.base _ j (recPlusN h j hj n) ka wL wF
      (FamilyHypotheses.refill G₀ δ θ rz alz th0 zc rq th iet et) R t Tn _ δ xs hgen hA' hka hdT hd0 hLat ⟨la₀, hB la₀⟩
  · exact shareRhoR_of_anFacts D n.base _ j (recPlusN h j hj n) ka wL wF
      (FamilyHypotheses.refill G₀ δ θ rz alz th0 zc rq th iet et) R t Tn _ δ xs hgen hA' hka hd2 hT hLat S
  · exact shareRhoP_of_anFacts D n.base _ j (recPlusN h j hj n) ka wL wF G₀.N G₀.w R t Tn CR c δ xs hA hd2 hT hLat
  · intro la
    exact Contain.inContainMR_of_anFacts D n.base _ j (recPlusN h j hj n) ka wL wF
      (FamilyHypotheses.refill G₀ δ θ rz alz th0 zc rq th iet et) R t Tn CR c δ xs hgen hA' hka hdT.le S hTop la (hB la)

end GlobalTheory.Shares
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ThetaArchimedeanDataIndefiniteModelsStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin

theorem _root_.GlobalTheory.T.thetaArchimedeanData_indefiniteModels : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ) (EX : ErrX D) (p : ℕ) (S : Scal (recB h.toLawsCore)) (nus : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO) → ℝ), ParOK T EX p j → PageOK large₂ (recPJ h j hj) H C2 A2 CT ka wL wF Tn nP nW h0 → HypC large₂ (recPJ h j hj) H C2 A2 7 0 CT S ka wL wF Tn nP nW h0 nus → j < D.R.m → ∀ G : GlobalFamilyData (recPJ h j hj) ka wL wF, GenOK h j hj large₂ G S (cc D large₂ C2 A2 7 wL) → EtaOK h j hj large₂ wL G.iet G.et → Nonempty (GlobalTheory.Shares.ArchAt h j G.w wF Tn (WeightFamilies.c1 D 7 Tn (cc D large₂ C2 A2 7 wL) j)) := by
  first | exact @GlobalTheory.RunJoin.archAt_of_run | exact GlobalTheory.RunJoin.archAt_of_run | (intros; apply GlobalTheory.RunJoin.archAt_of_run <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.CuspFormBasisSharesIndefiniteLiftIndex

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin

namespace GlobalTheory.RunJoin

section General

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (n : RunIn.SecNorm B) (X : PJ D B P j) (E : PtExt X)
  (hM : IntAtExt X E)

def ownNorm (B : WeightFamilies.Prov D) : RunIn.SecNorm B :=
  ⟨B.l2NormAlt, B.l2Norm_nonneg_bis, B.l2Norm_eq_zero_iff, B.l2Norm_smul_alt, B.l2Norm_add_le', B.l2Norm_le_supNorm_alt⟩



theorem sharesAt_ownNorm {ka wL wF : WeightFamilies.Wt D j} (G : GlobalFamilyData X ka wL wF) (S : Scal B) (Tn : ℕ) (c : ℝ)
    (Sh : Set (B.Cusp j wF)) :
    SharesAt (RunIn.globalFamilyDataBaseChange (ownNorm B) X E hM G) (scalarsWithNorm (ownNorm B).N (ownNorm B).h0 (ownNorm B).h1 (ownNorm B).h2
      (ownNorm B).h3 (ownNorm B).h4 S) Tn c Sh ↔ SharesAt (gd2Xplus G E hM) S Tn c Sh :=
  Iff.rfl



theorem sharesAt_of_xplus {ka wL wF : WeightFamilies.Wt D j} (G : GlobalFamilyData X ka wL wF) (S : Scal B) (Tn : ℕ) (c : ℝ)
    (Sh : Set (B.Cusp j wF)) (h : SharesAt (gd2Xplus G E hM) S Tn c Sh) : SharesAt G S Tn c Sh := by
  obtain ⟨del, th', h1, h2⟩ := h
  refine ⟨del, th', h1, fun rz alz th0 zc rq th iet et => ?_⟩
  obtain ⟨a, b, c, d, e⟩ := h2 rz alz th0 zc rq th iet et
  exact ⟨fun la => a la, b, c, d, fun la => e la⟩



theorem shortG_xN (wL wF : WeightFamilies.Wt D j) (S : Scal B) (β : ℝ) :
    ShortG (RunIn.xN n X E hM) ((RunIn.xN n X E hM).wF0 wL wF)
      ((RunIn.xN n X E hM).Thc (scalarsWithNorm n.N n.h0 n.h1 n.h2 n.h3 n.h4 S).s0 ((RunIn.xN n X E hM).wF0 wL wF)) β ↔
    ShortG X (X.wF0 wL wF) (X.Thc S.s0 (X.wF0 wL wF)) β :=
  Iff.rfl

end General


set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem sharesAt_of_lt : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ) (EX : ErrX D) (p : ℕ) (S : Scal (recB h.toLawsCore)) (nus : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO) → ℝ), ParOK T EX p j → PageOK large₂ (recPJ h j hj) H C2 A2 CT ka wL wF Tn nP nW h0 → HypC large₂ (recPJ h j hj) H C2 A2 7 0 CT S ka wL wF Tn nP nW h0 nus → LatAt (recB h.toLawsCore) j ka → j < D.R.m → ∀ G : GlobalFamilyData (recPJ h j hj) ka wL wF, GenOK h j hj large₂ G S (cc D large₂ C2 A2 7 wL) → EtaOK h j hj large₂ wL G.iet G.et → ∀ Sh : Set ((recB h.toLawsCore).Cusp j wF), Submodule.span (recB h.toLawsCore).KO Sh = ⊤ → SharesAt G S Tn (cc D large₂ C2 A2 7 wL) Sh := by
  intro D T h j hj large₂ H C2 A2 CT ka wL wF Tn nP nW h0 EX p S nus hPar hPg hH hLat hjm G hG hE Sh hSh
  have ht : TieC (⟨1,2,1,2,1,2,1,4,7⟩ : KAdm) H 1 4 0 11 C2 A2 7 := by
    obtain ⟨a, b, c, d, e, f⟩ := hPg.tie
    exact ⟨a, b, c, d, e, rfl, rfl, f, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl⟩
  obtain ⟨-, -, -, -, hadd, h2, h11⟩ := GlobalTheory.ExtraWeight.numbers D _ _ j (recPJ h j hj) _ 1 4 0 11 large₂ H C2 A2 7 CT
    ka wL wF Tn nP nW h0 hPg.hyp ht hPg.page hjm hj.1 (le_trans (by norm_num) hPg.df)
  have hA := GlobalTheory.T.thetaArchimedeanData_indefiniteModels D T h j hj large₂ H C2 A2 CT ka wL wF Tn nP nW h0 EX p S nus hPar hPg hH hjm G hG hE
  obtain ⟨hR, hMg⟩ := GlobalTheory.T.cuspReadings_span_model_forms_shifted_weights D T h j hj large₂ H C2 A2 CT ka wL wF Tn nP nW h0 EX p hPar hPg
  obtain ⟨-, -, ⟨-, -, -, -, -, po, -, -, PL, -, -, -, hS0, -⟩, -⟩ := hH
  let n := ownNorm (recB h.toLawsCore)
  refine sharesAt_of_xplus (recPJ h j hj) (extAll h j hj) (intAtExt_extAll h j hj) G S Tn _ Sh
    ((sharesAt_ownNorm (recPJ h j hj) (extAll h j hj) (intAtExt_extAll h j hj) G S Tn _ Sh).1 ?_)
  exact GlobalTheory.Shares.exists_inBasis_shares_inContain D T h j hj n ka wL wF
    (RunIn.globalFamilyDataBaseChange n (recPJ h j hj) (extAll h j hj) (intAtExt_extAll h j hj) G) Tn 7 (cc D large₂ C2 A2 7 wL)
    (scalarsWithNorm n.N n.h0 n.h1 n.h2 n.h3 n.h4 S) hadd h2 h11 hA hR hMg hLat
    ⟨_, (shortG_xN n (recPJ h j hj) (extAll h j hj) (intAtExt_extAll h j hj) wL wF S _).2 hS0⟩ Sh hSh

end GlobalTheory.RunJoin
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.CuspFormBasisSharesIndefiniteLiftIndexStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin
set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem _root_.GlobalTheory.T.cuspFormBasisShares_indefinite_liftIndex : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ) (EX : ErrX D) (p : ℕ) (S : Scal (recB h.toLawsCore)) (nus : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO) → ℝ), ParOK T EX p j → PageOK large₂ (recPJ h j hj) H C2 A2 CT ka wL wF Tn nP nW h0 → HypC large₂ (recPJ h j hj) H C2 A2 7 0 CT S ka wL wF Tn nP nW h0 nus → LatAt (recB h.toLawsCore) j ka → j < D.R.m → ∀ G : GlobalFamilyData (recPJ h j hj) ka wL wF, GenOK h j hj large₂ G S (cc D large₂ C2 A2 7 wL) → EtaOK h j hj large₂ wL G.iet G.et → ∀ Sh : Set ((recB h.toLawsCore).Cusp j wF), Submodule.span (recB h.toLawsCore).KO Sh = ⊤ → SharesAt G S Tn (cc D large₂ C2 A2 7 wL) Sh := by
  first | exact @GlobalTheory.RunJoin.sharesAt_of_lt | exact GlobalTheory.RunJoin.sharesAt_of_lt | (intros; apply GlobalTheory.RunJoin.sharesAt_of_lt <;> assumption)
end
end
