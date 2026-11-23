module

public import Formalism.LocalToGlobal.GlobalTheory.GL4.ThirdPropositionOfClass
public import Formalism.LocalToGlobal.Columns.CoefficientMapHeightBound
public import Formalism.HarderNarasimhan.StatementPl
public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.SizeMu
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.HermitianLattices.StatementLat
import Formalism.LocalToGlobal.GlobalTheory.HLatOps
import Formalism.LocalToGlobal.LatticeGeometry.OperatorNormFibers.StExtInv
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Mathlib.Tactic.ENatToNat
import Formalism.GL3MeanSquares.ConcavityEquidistribution
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalToGlobal.Columns.AbelianHostFieldConditions
import Formalism.LocalToGlobal.Columns.CoefficientsModP.WeTransposeWordTransposeWord
public import Formalism.LocalToGlobal.GlobalTheory.GL4.ColumnLatticeExactSlope
public import Formalism.LocalToGlobal.GlobalTheory.GL4.FockNExtCNu
public import Formalism.LocalToGlobal.GlobalTheory.GL4.MuMaxLeMon
public import Formalism.LocalToGlobal.GlobalTheory.GL4.ShortAtMeanLog
import Formalism.SharpRestriction.GlobalSchurBounds.TotallyPositiveTraceGeOfNormDiscr
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Tactic.Linter.Style

-- Source module: Formalism.LocalToGlobal.LatticeGeometry.OperatorNormFibers.PExtInvMuB

section

@[expose] public section

open Module NumberField TensorProduct

noncomputable section

namespace Formalism.L2.Geo.ExtensionFiltration.ExtInvMu

open Formalism.BasicNotions Formalism.HN Formalism.HermitianLatticesTheory Formalism.L2.GlobalTheoryTheory.HLatOps Formalism.L2.Geo.ExtensionFiltration.ExtInvSk

section Places

variable (K K' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K']


open Classical in
theorem card_fiber [_root_.NumberField.IsTotallyComplex K] (v : InfinitePlace K) :
    (Finset.univ.filter fun v' : InfinitePlace K' => v'.comap (algebraMap K K') = v).card =
      finrank K K' := by
  classical
  have h := InfinitePlace.unramifedPlacesOver_ncard_add_eq_finrank K' v
  have h0 : InfinitePlace.ramifiedPlacesOver K' v = ∅ := by
    ext w
    simp only [InfinitePlace.ramifiedPlacesOver, Set.mem_ofPred_eq, Set.mem_empty_iff_false,
      iff_false]
    rintro ⟨_, hw⟩
    exact InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex _)
      (InfinitePlace.isRamified_iff.1 hw).2
  have h1 : InfinitePlace.unramifiedPlacesOver K' v =
      ((Finset.univ.filter fun v' : InfinitePlace K' => v'.comap (algebraMap K K') = v :
        Finset (InfinitePlace K')) : Set (InfinitePlace K')) := by
    ext w
    simp only [InfinitePlace.unramifiedPlacesOver, Set.mem_ofPred_eq, Finset.coe_filter,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hw, _⟩
      exact InfinitePlace.LiesOver.comap_eq w v
    · rintro rfl
      refine ⟨⟨?_⟩, ?_⟩
      · ext x
        rfl
      · by_contra hr
        exact InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex _)
          (InfinitePlace.isRamified_iff.1 hr).2
  rw [h0, h1, Set.ncard_empty, mul_zero, add_zero, Set.ncard_coe_finset] at h
  exact h

theorem nPl_ext [_root_.NumberField.IsTotallyComplex K] [_root_.NumberField.IsTotallyComplex K'] : nPl K' = finrank K K' * nPl K := by
  have h1 := sizeMu_finrank_eq K
  have h2 := sizeMu_finrank_eq K'
  have h3 := Module.finrank_mul_finrank ℚ K K'
  rw [h1, h2] at h3
  linarith

end Places

end Formalism.L2.Geo.ExtensionFiltration.ExtInvMu
end
end
end

-- Source module: Formalism.LocalToGlobal.Columns.MaxSlopeSummandOfFock

section

@[expose] public section

open NumberField IsDedekindDomain Module MvPolynomial
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.GlobalTheoryTheory.HLatOps Formalism.HermitianLatticesTheory Formalism.HN Formalism.HermitianLattices.TraceIntegrality

section Places

variable (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex E] [_root_.NumberField.IsTotallyComplex K]

theorem mean_over_places_comap (φ : E →+* K) (G : InfinitePlace E → ℝ) :
    (1 / (nPl K : ℝ)) * ∑ v : InfinitePlace K, G (v.comap φ) = (∑ w, G w) / (nPl E : ℝ) := by
  classical
  let _ : Algebra E K := φ.toAlgebra
  have hc := Formalism.L2.Geo.ExtensionFiltration.ExtInvMu.card_fiber E K
  have hn := Formalism.L2.Geo.ExtensionFiltration.ExtInvMu.nPl_ext E K
  have hs : ∑ v : InfinitePlace K, G (v.comap φ) = (Module.finrank E K : ℝ) * ∑ w, G w := by
    rw [← Finset.sum_fiberwise Finset.univ (fun v : InfinitePlace K => v.comap φ) (fun v => G (v.comap φ)), Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Finset.sum_congr rfl (fun v hv => congrArg G (Finset.mem_filter.1 hv).2), Finset.sum_const, nsmul_eq_mul]
    congr 2
    convert hc w
  have hK : (0 : ℝ) < (nPl K : ℝ) := by
    unfold nPl
    exact_mod_cast Fintype.card_pos
  have hE : (0 : ℝ) < (nPl E : ℝ) := by
    unfold nPl
    exact_mod_cast Fintype.card_pos
  have hn' : (nPl K : ℝ) = (Module.finrank E K : ℝ) * (nPl E : ℝ) := by exact_mod_cast hn
  have hd : (0 : ℝ) < (Module.finrank E K : ℝ) := by
    by_contra h
    have h0 : (Module.finrank E K : ℝ) = 0 := le_antisymm (not_lt.1 h) (Nat.cast_nonneg _)
    rw [h0, zero_mul] at hn'
    exact hK.ne' hn'
  rw [hs, hn']
  field_simp

end Places

section Cols

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

end Cols

end Formalism.L2.Col
end
end
end

-- Source module: Formalism.LocalToGlobal.GlobalTheory.GL4.ThirdLinkOfArchimedean

section

@[expose] public section

open Module NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.HN Formalism.MainNotions.flipTwoThree Formalism.L2.DIV Formalism.L2.GlobalTheoryTheory.HLatOps Formalism.L2.Col

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def ClassMap (D : D7) : Prop :=
  ∀ u (CV : ColVal D u) (c : (D.mem u).C.cls 0), (∃ y : Fin (D.R.N 0) → (D.sp.X 0).V, Formalism.MainNotions.flipTwoThree.ShortAt D u c y) →
    ∃ (φ : ((D.fm u).lat 0).V →ₗ[D.what₂.LL] (MonI ((D.fm u).lam 0) → D.what₂.LL))
      (I : FractionalIdeal (nonZeroDivisors (𝓞 D.what₂.LL)) D.what₂.LL) (B : InfinitePlace D.what₂.LL → ℝ),
      Set.InjOn φ (NC CV c) ∧ I ≠ 0 ∧ (∀ x ∈ NC CV c, ∀ m, φ x m ∈ (I : Submodule (𝓞 D.what₂.LL) D.what₂.LL)) ∧ (∀ v, 0 < B v) ∧
      (∀ v x, normAt (Pi.basisFun D.what₂.LL (MonI ((D.fm u).lam 0))) (fun _ => (monD ((D.fm u).lam 0))⁻¹) v (φ x) ^ 2 ≤
        B v * normAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v x ^ 2) ∧
      -(2 * Real.log (FractionalIdeal.absNorm I : ℝ) / (Module.finrank ℚ D.what₂.LL : ℝ)) +
          (1 / (nPl D.what₂.LL : ℝ)) * ∑ v, Real.log (B v) ≤
        ∑ τ, (colAbsP D u τ * Real.log ((D.R.k : ℝ) ^ 3 * (2 * D.host.v) ^ 2) - (lamCol D u τ (D.R.k - 1) : ℝ) * Real.log (Tu D u))

theorem slopeMaxClass_of_map (D : D7) (h : ClassMap D) : SlopeMaxClass D := by
  intro u CV c hy
  have := (columnHypotheses D u).tc
  obtain ⟨φ, I, B, hinj, hI0, hint, hB, hnorm, hnum⟩ := h u CV c hy
  have hne : (NC CV c).map (φ.restrictScalars (𝓞 D.what₂.LL)) ≠ ⊥ := by
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (NC_ne_bot CV c)
    intro h0
    have hm : φ.restrictScalars (𝓞 D.what₂.LL) x ∈ (NC CV c).map (φ.restrictScalars (𝓞 D.what₂.LL)) := ⟨x, hx, rfl⟩
    rw [h0, Submodule.mem_bot] at hm
    exact hx0 (hinj hx (zero_mem _) (by rw [map_zero]; exact hm))
  have hm := muMax_le_mon D.what₂.LL ((D.fm u).lam 0) ((D.fm u).lat 0).b ((D.fm u).lat 0).X ((D.fm u).lat_good 0).1 (NC CV c)
    (((D.fm u).lat_good 0).2.1.map _) φ hinj hne I hI0 hint B hB hnorm (monCnu ((D.fm u).lam 0))
    (monCnu_pos _) (monW_ge_cNu _)
  have hl := log_monCnu ((D.fm u).lam 0) (rank_zero_pos D)
  rw [hl] at hm
  have hdW : ∀ τ, (dW ((D.fm u).lam 0 τ) : ℝ) = colAbsP D u τ := fun τ => by
    unfold dW
    push_cast
    exact sum_natWeight_eq_colAbsShifted D u τ
  have hN : ((D.R.N 0 : ℕ) : ℝ) = (D.R.k : ℝ) := by rw [Ranks.N_zero]
  simp only [hdW, hN] at hm
  have hk : (0 : ℝ) < D.R.k := by exact_mod_cast columnCount_pos D
  have hv : (0 : ℝ) < D.host.v := by have := two_le_half_rootDiscr D; linarith
  have hR : (∑ τ, (colAbsP D u τ * Real.log (4 * (D.R.k : ℝ) ^ 4 * D.host.v ^ 2) +
        Real.log (cNu ((D.fm u).lam 0 τ).natW) - (lamCol D u τ (D.R.k - 1) : ℝ) * Real.log (Tu D u))) =
      (∑ τ, (colAbsP D u τ * Real.log (D.R.k : ℝ) + Real.log (cNu ((D.fm u).lam 0 τ).natW))) +
      ∑ τ, (colAbsP D u τ * Real.log ((D.R.k : ℝ) ^ 3 * (2 * D.host.v) ^ 2) - (lamCol D u τ (D.R.k - 1) : ℝ) * Real.log (Tu D u)) := by
    have e4 : Real.log (4 * (D.R.k : ℝ) ^ 4 * D.host.v ^ 2) =
        Real.log (D.R.k : ℝ) + Real.log ((D.R.k : ℝ) ^ 3 * (2 * D.host.v) ^ 2) := by
      rw [← Real.log_mul hk.ne' (by positivity)]
      congr 1
      ring
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [e4]
    ring
  show muMaxDef ((D.fm u).lat 0).b ((D.fm u).lat 0).X (NC CV c) ≤ _
  rw [hR]
  linarith

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.HN Formalism.MainNotions.flipTwoThree Formalism.L2.DIV Formalism.L2.GlobalTheoryTheory.HLatOps Formalism.L2.Col

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem shortAt_pos (D : D7) (u : D.what₂.Word) (c : (D.mem u).C.cls 0) (y : Fin (D.R.N 0) → (D.sp.X 0).V)
    (hy : Formalism.MainNotions.flipTwoThree.ShortAt D u c y) (w : InfinitePlace D.host.E) (a : Fin (D.R.N 0)) :
    0 < (w.embedding ((D.sp.X 0).hT (y a) (y a))).re := by
  obtain ⟨r, hr, he⟩ := (columnHypotheses D u).pos w.embedding (y a) (hy.2.1.ne_zero a)
  rw [he, Complex.ofReal_re]
  exact hr

def ClassMapT (D : D7) : Prop :=
  ∀ u (CV : ColVal D u) (c : (D.mem u).C.cls 0) (y : Fin (D.R.N 0) → (D.sp.X 0).V), Formalism.MainNotions.flipTwoThree.ShortAt D u c y →
    ∃ (φ : ((D.fm u).lat 0).V →ₗ[D.what₂.LL] (MonI ((D.fm u).lam 0) → D.what₂.LL))
      (I : FractionalIdeal (nonZeroDivisors (𝓞 D.what₂.LL)) D.what₂.LL) (Dv : InfinitePlace D.what₂.LL → ℝ),
      Set.InjOn φ (NC CV c) ∧ I ≠ 0 ∧ (∀ x ∈ NC CV c, ∀ m, φ x m ∈ (I : Submodule (𝓞 D.what₂.LL) D.what₂.LL)) ∧ (∀ v, 0 < Dv v) ∧
      (∀ v x, normAt (Pi.basisFun D.what₂.LL (MonI ((D.fm u).lam 0))) (fun _ => (monD ((D.fm u).lam 0))⁻¹) v (φ x) ^ 2 ≤
        ((∏ τ, (∑ a, (v.embedding (CV.rho τ ((D.sp.X 0).hT (y a) (y a)))).re) ^ dW ((D.fm u).lam 0 τ)) * Dv v) *
          normAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v x ^ 2) ∧
      -(2 * Real.log (FractionalIdeal.absNorm I : ℝ) / (Module.finrank ℚ D.what₂.LL : ℝ)) +
          (1 / (nPl D.what₂.LL : ℝ)) * ∑ v, Real.log (Dv v) ≤
        -∑ τ, (lamCol D u τ (D.R.k - 1) : ℝ) * Real.log (Tu D u)

theorem class_map_of_archimedean (D : D7) (h : ClassMapT D) : ClassMap D := by
  intro u CV c hy
  obtain ⟨y, hy⟩ := hy
  have := (columnHypotheses D u).tc
  have := (columnHypotheses D u).tcE
  have hposE := shortAt_pos D u c y hy
  obtain ⟨φ, I, Dv, hinj, hI0, hint, hD, hnorm, hnum⟩ := h u CV c y hy
  set G : InfinitePlace D.what₂.LL → D.what₂.Tau → ℝ := fun v τ => ∑ a, (v.embedding (CV.rho τ ((D.sp.X 0).hT (y a) (y a)))).re with hG
  have hN0 : 0 < D.R.N 0 := rank_zero_pos D
  have hGc : ∀ v τ, G v τ = ∑ a, ((v.comap (CV.rho τ)).embedding ((D.sp.X 0).hT (y a) (y a))).re := fun v τ =>
    Finset.sum_congr rfl fun a _ => (re_comap (CV.rho τ) v _).symm
  have hGpos : ∀ v τ, 0 < G v τ := fun v τ => by
    rw [hGc]
    exact Finset.sum_pos (fun a _ => hposE _ a) ⟨⟨0, hN0⟩, Finset.mem_univ _⟩
  refine ⟨φ, I, fun v => (∏ τ, G v τ ^ dW ((D.fm u).lam 0 τ)) * Dv v, hinj, hI0, hint,
    fun v => mul_pos (Finset.prod_pos fun τ _ => pow_pos (hGpos v τ) _) (hD v), hnorm, ?_⟩
  have hlog : ∀ v, Real.log ((∏ τ, G v τ ^ dW ((D.fm u).lam 0 τ)) * Dv v) =
      (∑ τ, (dW ((D.fm u).lam 0 τ) : ℝ) * Real.log (G v τ)) + Real.log (Dv v) := fun v => by
    rw [Real.log_mul (Finset.prod_pos fun τ _ => pow_pos (hGpos v τ) _).ne' (hD v).ne',
      Real.log_prod (fun τ _ => (pow_pos (hGpos v τ) _).ne')]
    congr 1
    exact Finset.sum_congr rfl fun τ _ => Real.log_pow _ _
  have hmean : ∀ τ, (1 / (nPl D.what₂.LL : ℝ)) * ∑ v, Real.log (G v τ) ≤ Real.log ((D.R.k : ℝ) ^ 3 * (2 * D.host.v) ^ 2) := by
    intro τ
    have h1 := mean_over_places_comap D.host.E D.what₂.LL (CV.rho τ)
      (fun w => Real.log (∑ a, (w.embedding ((D.sp.X 0).hT (y a) (y a))).re))
    have h2 : (∑ v, Real.log (G v τ)) = ∑ v : InfinitePlace D.what₂.LL,
        Real.log (∑ a, ((v.comap (CV.rho τ)).embedding ((D.sp.X 0).hT (y a) (y a))).re) :=
      Finset.sum_congr rfl fun v _ => by rw [hGc]
    rw [h2, h1]
    exact shortAt_mean_log D u c y hy hposE
  have hdW : ∀ τ, (dW ((D.fm u).lam 0 τ) : ℝ) = colAbsP D u τ := fun τ => by
    unfold dW
    push_cast
    exact sum_natWeight_eq_colAbsShifted D u τ
  have hsplit : (1 / (nPl D.what₂.LL : ℝ)) * ∑ v, Real.log ((∏ τ, G v τ ^ dW ((D.fm u).lam 0 τ)) * Dv v) =
      (∑ τ, (dW ((D.fm u).lam 0 τ) : ℝ) * ((1 / (nPl D.what₂.LL : ℝ)) * ∑ v, Real.log (G v τ))) +
        (1 / (nPl D.what₂.LL : ℝ)) * ∑ v, Real.log (Dv v) := by
    simp only [hlog, Finset.sum_add_distrib, mul_add]
    congr 1
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun v _ => by ring
  have hbound : (∑ τ, (dW ((D.fm u).lam 0 τ) : ℝ) * ((1 / (nPl D.what₂.LL : ℝ)) * ∑ v, Real.log (G v τ))) ≤
      ∑ τ, colAbsP D u τ * Real.log ((D.R.k : ℝ) ^ 3 * (2 * D.host.v) ^ 2) :=
    Finset.sum_le_sum fun τ _ => by
      rw [← hdW τ]
      exact mul_le_mul_of_nonneg_left (hmean τ) (Nat.cast_nonneg _)
  rw [hsplit]
  have e : (∑ τ, (colAbsP D u τ * Real.log ((D.R.k : ℝ) ^ 3 * (2 * D.host.v) ^ 2) -
      (lamCol D u τ (D.R.k - 1) : ℝ) * Real.log (Tu D u))) =
      (∑ τ, colAbsP D u τ * Real.log ((D.R.k : ℝ) ^ 3 * (2 * D.host.v) ^ 2)) -
        ∑ τ, (lamCol D u τ (D.R.k - 1) : ℝ) * Real.log (Tu D u) := Finset.sum_sub_distrib _ _
  rw [e]
  linarith

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
end
end
