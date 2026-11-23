module

public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.GrowthConstantBoundGcR
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.SWEqSOf
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.NormEuclideanEmbeddingEqNetNorm
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.CombBound4Of
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.JWMggWMem
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LiftIndexPowFourLeDegree
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroBundledOfLift
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroOfLocalAndSum
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroSplitOfLocal
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
import Mathlib.Topology.Sheaves.Init
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LenAtEqZeroOfSubsingleton

-- Source module: Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroOfRefinedInputs

section

@[expose] public section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions

namespace Formalism.MainNotions.Gaps.EtaleWeightGaps

theorem theorem_zero_of_refined_inputs {D : D7} {B : Formalism.MainNotions.WeightFamilies.Prov D} {P : Formalism.MainNotions.ModuliIntegralCharts.Prov D} : Conclusion1OfComb4 (D := D) (B := B) (P := P) := by
  intro large₂ X K H Ch Ah Cq Aq C2 A2 CR CT j h1 h2 S ka wL wF T nP nW h0 nus hH lA sA mA qA _ _ _ G Gc PH Prw Pet Pd
    tW tTh tZ tQ _ dH dS dL pG sRd sRho sRhoP hP iZ iM hQf hDm hM
  by_cases hj : j < D.R.m
  · obtain ⟨Qf, iB, iC, iT, iLf, hB, hHt⟩ := hQf hj
    obtain ⟨hs, hb⟩ := rLa_tsum_le_comb large₂ X K H Ch Ah Cq Aq C2 A2 CR CT h1 h2 S T nP nW h0 nus hH lA sA mA qA G Gc PH Prw
      Pet Pd tW tZ tQ dH dS dL (pageGd4_iff.mp pG) (polyDom4_iff.mp hP) Qf hHt
    have hsum := hb.trans (sumGC4 large₂ (X j h1 h2) h1 K H Ch Ah Cq Aq C2 A2 CR CT S T nP nW h0 nus hH G Gc PH Prw Pet Pd
      tTh dL sRd sRho sRhoP hP Qf hHt)
    refine concl_of_nat (X j h1 h2) S ka wL wF T nus _ (fun la => rLa (Qf la) K.CRm T (cc D large₂ C2 A2 CR wL))
      hH.2.2.2.1.1 (fun la => rLa_nonneg_comb4 hB la _ _ _) hs hsum (fun la e he V' hV => ?_)

    have hw : ∀ k, G.w k ∈ (X j h1 h2).WWc S.sW wL := fun k => tW.1 ▸ Submodule.subset_span ⟨k, rfl⟩
    have hH2 : H2 (X j h1 h2) S ka wL wF := hH.2.2.2.2.1
    have hth'M : ∀ i, G.th' i ∈ B.Mlat j wF := fun i => hH2.2.1 (tTh i).1
    have hOk : (Qf la).Ok S K.CRm T (cc D large₂ C2 A2 CR wL) := ⟨iB la, iC la, iT la, iZ la, iM la⟩
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hT0, hDT, -⟩ := hH.2.1
    exact localBound G la (Qf la) S K.CRm _ e (nus la) (ka_eq_addL_of_setC hH.2.1) lA.toIsLattice (theta_le_msup_of_hypC _ S hH)
      (span_Thc_of_hypC hH).2.2 hT0 hDT hw tW.2.1 (fun i => (tTh i).1) hth'M (fun k => (tZ.1 k).1)
      (fun k => (tZ.1 k).2.1) (fun k => (tZ.1 k).2.2.2) tZ.2.1 tZ.2.2 tQ.2.1 tQ.2.2.1 (iB la) (iC la) (iT la) (iM la)
      (vEt_nonneg_comb4 hB la) (nu_le_comb4 hj hB la (iT la)) he
      (lenBase_all j _ ka wL wF G la (Qf la) S K.CRm T _ hOk hth'M hw (hHt.1 la))
      (lenPoleL_all j _ ka wL wF G la (Qf la) S K.CRm T e _ hOk (iLf la tW (iC la) (iT la)) hw) V' hV
  · exact hM (not_lt.1 hj) (hDm (not_lt.1 hj))

end Formalism.MainNotions.Gaps.EtaleWeightGaps
end
end

-- Source module: Development.AbelianVarietyTheory.Definitions.HeightFunctions.ConclOfInputs4

section

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FinalJoin

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.MainNotions.Gaps.NetNorms Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin GlobalTheory.RunIn

variable {D : D7}

section Abstract

variable {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

structure PageRun (large₂ : SizeData₂ D) (X : PJ D B P j) (H : KHyp) (C2 A2 CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ)
    (h0 : ℝ) : Prop where
  hyp : FamilyHypotheses.HypPage large₂ X H C2 A2 7 CT ka wL wF Tn nP nW h0
  page : PageAt large₂ C2 A2
  tie : H.C1 = C2 ∧ H.A1 = A2 ∧ H.Cc = C2 ∧ H.Ac = A2 ∧ H.CRc = 7 ∧ 12 ≤ A2

def BaseIn (large₂ : SizeData₂ D) (X : PJ D B P j) (K : KAdm) (H : KHyp) (Ch Ah Cq Aq C2 A2 CR CT : ℝ) (S : Scal B)
    (ka wL wF : WeightFamilies.Wt D j) (T nP nW : ℕ) (h0 : ℝ) (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ) : Prop :=
  HypC large₂ X H C2 A2 CR 0 CT S ka wL wF T nP nW h0 nus ∧ LatAt B j ka ∧ LAMwAt large₂ B j ka K.CL K.AL ∧
    (j < D.R.m → QAt large₂ B j ka K.CRm H.CK Ch Ah Cq Aq T (cc D large₂ C2 A2 CR wL)) ∧ DeepSubMul X

def FamIn (large₂ : SizeData₂ D) {X : PJ D B P j} (K : KAdm) (H : KHyp) (Ch Ah Cq Aq C2 A2 CR : ℝ) (S : Scal B)
    {ka wL wF : WeightFamilies.Wt D j} (T : ℕ) (G : GlobalFamilyData X ka wL wF) (Gc PH Prw Pet Pd : ℝ) : Prop :=
  G.TiedW S Gc Prw ∧ G.TiedTh S Gc ∧ G.TiedEt large₂ K.Cf K.Af ∧ PageGd X ka large₂ K.CG K.AG Pd ∧ GrowthConstantBound large₂ B Gc ∧
    PageGq large₂ Gc Ch Ah ∧ ShareRd (D := D) (j := j) T G.del (X.rk ka (B.Mlat j ka)) ∧
    ShareRhoR G S T (X.rk ka (B.Mlat j ka)) ∧
    ShareRhoP (D := D) (j := j) T (WeightFamilies.rhoP B K.CRm T (cc D large₂ C2 A2 CR wL) j ka) (X.rk ka (B.Mlat j ka)) ∧
    PolyDom (j := j) D B large₂ K H C2 A2 CR Ch Ah Cq Aq Gc PH Prw Pet Pd ka ∧ (∀ la, InBasis G la) ∧
    ∀ la, InContainMR G la S K.CRm T (cc D large₂ C2 A2 CR wL)

def PtIn {X : PJ D B P j} (S : Scal B) {ka wL wF : WeightFamilies.Wt D j} (T : ℕ) (G : GlobalFamilyData X ka wL wF) (c Gc PH Prw Pet : ℝ)
    (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ) : Prop :=
  CombBound G S c nus ∧ ∃ Qf : ∀ la, LocalPointData G la, (∀ la, (Qf la).InCurve) ∧ (∀ la, (Qf la).InTie S) ∧
    (∀ la, (Qf la).InLiftC S Gc Prw T) ∧ Heights Qf Gc PH Prw Pet

def NetIn (large₂ : SizeData₂ D) (B : WeightFamilies.Prov D) (j : ℕ) (ka : WeightFamilies.Wt D j) (K : KAdm) (Pd : ℝ) : Prop :=
  ∃ (Nt : NetData B j ka) (σ₀ : B.KO →+* ℂ), NetMax Nt ∧ NetLeSup Nt ∧ NetPageG Nt large₂ K.CG K.AG ∧ NetInj Nt σ₀ ∧
    Real.log (Fintype.card (Nt.NN σ₀) : ℝ) ≤ Pd

def InputsNet (large₂ : SizeData₂ D) (X : PJ D B P j) (K : KAdm) (H : KHyp) (Ch Ah Cq Aq C2 A2 CR CT : ℝ) (S : Scal B)
    (ka wL wF : WeightFamilies.Wt D j) (T nP nW : ℕ) (h0 : ℝ) (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ) : Prop :=
  BaseIn large₂ X K H Ch Ah Cq Aq C2 A2 CR CT S ka wL wF T nP nW h0 nus ∧
    ∃ (G : GlobalFamilyData X ka wL wF) (Gc PH Prw Pet Pd : ℝ), NetIn large₂ B j ka K Pd ∧
      FamIn large₂ K H Ch Ah Cq Aq C2 A2 CR S T G Gc PH Prw Pet Pd ∧ PtIn S T G (cc D large₂ C2 A2 CR wL) Gc PH Prw Pet nus

def InputsR (large₂ : SizeData₂ D) (X : PJ D B P j) (K : KAdm) (H : KHyp) (Ch Ah Cq Aq C2 A2 CR CT : ℝ) (S : Scal B)
    (ka wL wF : WeightFamilies.Wt D j) (T nP nW : ℕ) (h0 : ℝ) (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ) : Prop :=
  BaseIn large₂ X K H Ch Ah Cq Aq C2 A2 CR CT S ka wL wF T nP nW h0 nus ∧ SupBoundByL2AtWeight large₂ B j ka K.CG K.AG ∧ DeepHerm X ka ∧
    ∃ (G : GlobalFamilyData X ka wL wF) (Gc PH Prw Pet Pd : ℝ), DeepLogD X ka Pd ∧
      FamIn large₂ K H Ch Ah Cq Aq C2 A2 CR S T G Gc PH Prw Pet Pd ∧ PtIn S T G (cc D large₂ C2 A2 CR wL) Gc PH Prw Pet nus

def Inputs4 (large₂ : SizeData₂ D) (X : PJ D B P j) (K : KAdm) (H : KHyp) (Ch Ah Cq Aq C2 A2 CR CT : ℝ) (S : Scal B)
    (ka wL wF : WeightFamilies.Wt D j) (T nP nW : ℕ) (h0 : ℝ) (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ) : Prop :=
  HypC large₂ X H C2 A2 CR 0 CT S ka wL wF T nP nW h0 nus ∧
    LatAt B j ka ∧ SupBoundByL2AtWeight large₂ B j ka K.CG K.AG ∧ LAMwAt large₂ B j ka K.CL K.AL ∧
    (j < D.R.m → QAt large₂ B j ka K.CRm H.CK Ch Ah Cq Aq T (cc D large₂ C2 A2 CR wL)) ∧
    TieC K H Ch Ah Cq Aq C2 A2 CR ∧ PageAt large₂ C2 A2 ∧ PageSupp D large₂ B C2 A2 nW S wL ∧
    ∃ (G : GlobalFamilyData X ka wL wF) (Gc PH Prw Pet Pd : ℝ),
      G.TiedW S Gc Prw ∧ G.TiedTh S Gc ∧ G.TiedZ S T Gc ∧
      G.TiedQ large₂ S K.CRm T (cc D large₂ C2 A2 CR wL) Ch Ah ∧ G.TiedEt large₂ K.Cf K.Af ∧
      DeepHerm X ka ∧ DeepSubMul X ∧ DeepLogD X ka Pd ∧ PageGd4 X ka large₂ K.CG K.AG Pd ∧
      ShareRd (D := D) (j := j) T G.del (X.rk ka (B.Mlat j ka)) ∧
      ShareRhoT (D := D) (j := j) T G.rz G.rq (X.rk ka (B.Mlat j ka)) ∧
      ShareRhoP (D := D) (j := j) T G.rq (X.rk ka (B.Mlat j ka)) ∧
      PolyDom4 (j := j) D B large₂ K H C2 A2 CR Ch Ah Cq Aq Gc PH Prw Pet Pd ka ∧
      (∀ la, InContainZ G la S T) ∧ (∀ la, InContainM G la K.CRm T (cc D large₂ C2 A2 CR wL)) ∧
      (j < D.R.m → ∃ Qf : ∀ la, LocalPointData G la,
        (∀ la, InBasis G la) ∧ (∀ la, (Qf la).InCurve) ∧ (∀ la, (Qf la).InTie S) ∧ (∀ la, (Qf la).InLiftC S Gc Prw T) ∧
        CombBound4 G Qf S (cc D large₂ C2 A2 CR wL) nus ∧ Heights Qf Gc PH Prw Pet) ∧
      (D.R.m ≤ j → DepthAtM X S wL nus) ∧
      ConclAtM large₂ X S ka wL wF T nus ∧
      (D.R.m ≤ j → ∃ Qf : ∀ la, LocalPointData G la,
        (∀ la, InBasis G la) ∧ (∀ la, (Qf la).InCurve) ∧ (∀ la, (Qf la).InTie S) ∧ (∀ la, (Qf la).InLiftC S Gc Prw T) ∧
        Heights Qf Gc PH Prw Pet)

def k4 (large₂ : SizeData₂ D) (CL : ℝ) : KAdm := ⟨1041 * zBase large₂, 2, 200000, 2, 1, 2, CL, 2, 7⟩

end Abstract

theorem concl_of_inputs4 {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} (large₂ : SizeData₂ D) (X : Prov D B P) (K : KAdm) (H : KHyp)
    (Ch Ah Cq Aq C2 A2 CR CT : ℝ) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (S : Scal B) (ka wL wF : WeightFamilies.Wt D j)
    (T nP nW : ℕ) (h0 : ℝ) (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ)
    (h : Inputs4 large₂ (X j h1 h2) K H Ch Ah Cq Aq C2 A2 CR CT S ka wL wF T nP nW h0 nus) :
    Concl (X j h1 h2) S ka wL wF T nus ((X j h1 h2).rk ka (B.Mlat j ka) * D.R.f * D.R.m * large₂.sc.b * large₂.de2) := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, G, Gc, PH, Prw, Pet, Pd, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13,
    b14, b15, b16, b17, b18, -⟩ := h
  exact theorem_zero_of_refined_inputs large₂ X K H Ch Ah Cq Aq C2 A2 CR CT j h1 h2 S ka wL wF T nP nW h0 nus a1 a2 a3 a4 a5 a6 a7 a8 G Gc PH Prw
    Pet Pd b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18

def RunHolds (x₀ : ℝ → ℝ → ℝ) {T : Top D} (h : LawsP T) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (p : ℕ) :
    Prop :=
  ∀ (j : ℕ) (hj : InR D j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ),
    PageRun large₂ (recPJ h j hj) H C2 A2 CT ka wL wF Tn nP nW h0 → x₀ H.CA H.CK ≤ large₂.sc.x →
    (∃ (n : SecNorm (recB h.toLawsCore)) (K : KAdm) (Cq : ℝ),
      Inputs4 large₂ (recPlusN h j hj n) K H 1 4 Cq 4 C2 A2 7 CT (scalOfP n.base hinj EX p ka wL wF Tn) ka wL wF Tn nP nW h0
        (nusR h j wL) ∧
      Concl (recPlusN h j hj n) (scalOfP n.base hinj EX p ka wL wF Tn) ka wL wF Tn (nusR h j wL)
        ((recPlusN h j hj n).rk ka (n.base.Mlat j ka) * D.R.f * D.R.m * large₂.sc.b * large₂.de2)) ∧
    HypC large₂ (recPJ h j hj) H C2 A2 7 0 CT (scalOfP (recB h.toLawsCore) hinj EX p ka wL wF Tn) ka wL wF Tn nP nW h0
      (nusR h j wL) ∧
    Concl (recPJ h j hj) (scalOfP (recB h.toLawsCore) hinj EX p ka wL wF Tn) ka wL wF Tn (nusR h j wL)
      ((recPJ h j hj).rk ka ((recB h.toLawsCore).Mlat j ka) * D.R.f * D.R.m * large₂.sc.b * large₂.de2)

end GlobalTheory.FinalJoin
end
end
end
