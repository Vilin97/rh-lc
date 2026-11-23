module

public import Formalism.LocalToGlobal.ProjectiveLattices.EquivariantFiniteGroup
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
public import Formalism.LocalToGlobal.ProjectiveLattices.LiftCurveSt
public import Formalism.LocalToGlobal.ProjectiveLattices.IntAtExtExtAll
public import Formalism.LocalToGlobal.ProjectiveLattices.IsGenFrGenFr
import Formalism.SharpRestriction.Divisibility.WeightAlgebra
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LevelsQDesc

-- Source module: Development.AbelianVarietyTheory.BlockTheory.HeightDefect.FullTranscendenceDegree

section

@[expose] public section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.FullTranscendenceDegree

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj
  Formalism.MainNotions.Gaps.EtaleWeightGaps

variable {D : D7} {T : Top D} (h : LawsP T) (j : ℕ) (hj : InR D j)

abbrev CuspAt (u : WeightFamilies.Wt D j) : Type := (recB h.toLawsCore).Cusp j u

abbrev XP : WeightAlgebra.PJ D (recB h.toLawsCore) T.G.P j :=
  xplus (recPJ h j hj) (extAll h j hj) (intAtExt_extAll h j hj)

def GeneratesIn {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : WeightAlgebra.PJ D B P j) {wL : WeightFamilies.Wt D j} {N : ℕ}
    (s : 𝓞 B.KO) (w : Fin N → B.Cusp j wL) : Prop :=
  Submodule.span (𝓞 B.KO) (Set.range w) = X.WWc s wL

def Generates {wL : WeightFamilies.Wt D j} {N : ℕ} (s : 𝓞 T.Q.c.F) (w : Fin N → CuspAt h j wL) : Prop :=
  GeneratesIn (XP h j hj) s w

def ptNorm (σ : T.Q.c.F →+* ℂ) (u : WeightFamilies.Wt D j) (F : CuspAt h j u) (p : FPt (T.U j σ).X) : ℝ :=
  ((T.U j σ).X p.1).pnorm (laU (T.U j σ) (wtA u) u.n p.1) (rdU (T.U j σ) (F.1 : T.R j) p.1) p.2.1

def l2Norm (σ : T.Q.c.F →+* ℂ) {wL : WeightFamilies.Wt D j} {N : ℕ} (w : Fin N → CuspAt h j wL)
    (p : FPt (T.U j σ).X) : ℝ :=
  Real.sqrt (∑ i, ptNorm h j σ wL (w i) p ^ 2)

def NoCommonZero {wL : WeightFamilies.Wt D j} {N : ℕ} (w : Fin N → CuspAt h j wL) : Prop :=
  ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ p : FPt (T.U j σ).X,
    ∃ i, rdU (T.U j σ) ((w i).1 : T.R j) p.1 p.2.1 ≠ 0

def FullTrdeg (hg : GenFrEx (T.Q.Xo j) T.Q.c) {wL : WeightFamilies.Wt D j} {N : ℕ} (w : Fin N → CuspAt h j wL) : Prop :=
  ∀ Z : Comp (T.Q.Xo j) T.Q.c, ∃ i₀, evC hg Z ((w i₀).1 : T.R j) ≠ 0 ∧
    Algebra.trdeg T.Q.c.F (IntermediateField.adjoin T.Q.c.F
      (Set.range fun i => evC hg Z ((w i).1 : T.R j) / evC hg Z ((w i₀).1 : T.R j))) = (WeightFamilies.dimY D j : Cardinal)

def SmallForm {wL : WeightFamilies.Wt D j} {N : ℕ} (w : Fin N → CuspAt h j wL) : Prop :=
  ∃ (k m₀ : ℕ) (β : CuspAt h j (WeightAlgebra.wsmul k wL)), (XP h j hj).NonZeroComp (WeightAlgebra.wsmul k wL) β ∧
    ∃ C : ℝ, ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ p : FPt (T.U j σ).X,
      ptNorm h j σ (WeightAlgebra.wsmul k wL) β p ≤ C * l2Norm h j σ w p ^ k ∧
      ptNorm h j σ (WeightAlgebra.wsmul k wL) β p ^ m₀ ≤ C * l2Norm h j σ w p ^ (k * m₀ + 1)

def BigAt (hg : GenFrEx (T.Q.Xo j) T.Q.c) {wL : WeightFamilies.Wt D j} {N : ℕ} (w : Fin N → CuspAt h j wL) : Prop :=
  NoCommonZero h j w ∧ FullTrdeg h j hg w ∧ SmallForm h j hj w

def ExistsNonzeroCuspFormOfWeightPair (wL wF : WeightFamilies.Wt D j) : Prop :=
  ∃ w₂ : WeightFamilies.Wt D j, WeightAlgebra.IsG2 wL wF w₂ ∧ ∃ θ : CuspAt h j w₂, (XP h j hj).NonZeroComp w₂ θ

def CurveModelAt (hg : GenFrEx (T.Q.Xo j) T.Q.c) {ka wL wF : WeightFamilies.Wt D j} (G : GlobalFamilyData (XP h j hj) ka wL wF)
    (S : WeightAlgebra.Scal (recB h.toLawsCore)) : Prop :=
  Generates h j hj S.sW G.w → BigAt h j hj hg G.w → ExistsNonzeroCuspFormOfWeightPair h j hj wL wF →
    ∀ (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (g₀ : CuspAt h j wF), (XP h j hj).NonZeroComp wF g₀ →
      Nonempty (CurveModel (X := recPJ h j hj) (E := extAll h j hj) (hM := intAtExt_extAll h j hj) G la g₀)

def CurveModelExists : Prop :=
  ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (hg : GenFrEx (T.Q.Xo j) T.Q.c)
    (ka wL wF : WeightFamilies.Wt D j) (G : GlobalFamilyData (XP h j hj) ka wL wF) (S : WeightAlgebra.Scal (recB h.toLawsCore)),
    CurveModelAt h j hj hg G S

theorem ptNorm_nonneg (σ : T.Q.c.F →+* ℂ) (u : WeightFamilies.Wt D j) (F : CuspAt h j u) (p : FPt (T.U j σ).X) :
    0 ≤ ptNorm h j σ u F p :=
  mul_nonneg (norm_nonneg _) (pnorm_fac_nonneg _ _ _)

end GlobalTheory.IndefiniteRowSideFullHecke.FullTranscendenceDegree
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsPosLowerBoundSections

section

@[expose] public section

noncomputable section

namespace GlobalTheory.BignessCompare

open Formalism.L2.Pj NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory.IndefiniteRowSideFullHecke.FullTranscendenceDegree (CuspAt XP Generates ptNorm l2Norm FullTrdeg SmallForm ExistsNonzeroCuspFormOfWeightPair CurveModelAt CurveModelExists
  ptNorm_nonneg)

section Model

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {κ : Type} [Fintype κ]

theorem bdd_of_mem_holSub (X : κ → Data E r) (la : ∀ c, Wt (X c).Ψ r) {P : FDSec X} (hP : P ∈ holSub X la) :
    ∃ M : ℝ, ∀ p : FPt X, (X p.1).pnorm (la p.1) (P p.1) p.2 ≤ M := by
  induction hP using Submodule.span_induction with
  | mem P hP =>
    choose C hC using fun c => (hP c).1.2
    refine ⟨∑ c, |C c|, fun p => (hC p.1 p.2 p.2.2).trans ((le_abs_self _).trans ?_)⟩
    exact Finset.single_le_sum (f := fun c => |C c|) (fun _ _ => abs_nonneg _) (Finset.mem_univ _)
  | zero => exact ⟨0, fun p => (pnorm_zero _ _ _).le⟩
  | add P Q _ _ hP hQ =>
    obtain ⟨a, ha⟩ := hP
    obtain ⟨b, hb⟩ := hQ
    exact ⟨a + b, fun p => (pnorm_add_le _ _ _ _ _).trans (add_le_add (ha p) (hb p))⟩
  | smul a P _ hP =>
    obtain ⟨b, hb⟩ := hP
    exact ⟨‖a‖ * b, fun p => (pnorm_smul _ _ a _ _).le.trans (mul_le_mul_of_nonneg_left (hb p) (norm_nonneg _))⟩

end Model

section Weights

variable {D : D7} {j : ℕ}

end Weights

section Record

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j)

variable {ι : Type} (Ω : ι → Type) [∀ Z, Field (Ω Z)] [∀ Z, Algebra B.KO (Ω Z)] (gF : ∀ Z, X.Forms →ₐ[B.KO] Ω Z)
  (hinj : ∀ (u : WeightFamilies.Wt D j) (F : B.Cusp j u), (∀ Z, gF Z (X.inc u F) = 0) → F = 0)


end Record

section Inst

variable {D : D7} {T : Formalism.L2.Pj.Top D} (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c)
  {ka wL wF : WeightFamilies.Wt D j}






end Inst

end GlobalTheory.BignessCompare
end
end
end
