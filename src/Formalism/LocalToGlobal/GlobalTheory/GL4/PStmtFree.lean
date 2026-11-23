module

public import Formalism.SharpRestriction.GlobalSchurBounds.SlopeMaxOpenOfHookTwoLeV
public import Formalism.LocalToGlobal.Columns.SummandSlopeOfThreeLemmas
public import Formalism.LocalToGlobal.GlobalTheory.GL4.CoeffMemOfIntSpanAt
public import Formalism.LocalToGlobal.GlobalTheory.GL4.ThirdLinkOfArchimedean
public import Formalism.LocalToGlobal.Columns.TwistedLocalisationComparable
public import Formalism.LocalToGlobal.GlobalTheory.GL4.ThirdPropositionOfClass
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
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.GlobalTheory.GL4.ColumnLatticeExactSlope
public import Formalism.LocalToGlobal.GlobalTheory.GL4.NfAllSelfEq
import Formalism.SharpRestriction.GlobalSchurBounds.TotallyPositiveTraceGeOfNormDiscr
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Formalism.LocalToGlobal.Columns.BrpStarLatLattice
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.HookBound

-- Source module: Formalism.LocalToGlobal.GlobalTheory.GL4.CfMemTwId

section

@[expose] public section

open Module NumberField IsDedekindDomain MvPolynomial
open scoped Matrix

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.HN Formalism.MainNotions.flipTwoThree Formalism.L2.DIV Formalism.L2.GlobalTheoryTheory.HLatOps Formalism.L2.Col Formalism.BasicNotions.SkeletonIndexLemmas

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Int2

variable {D : D7} {u : D.what₂.Word} (CV : ColVal D u)

theorem cf_mem_twId (c : (D.mem u).C.cls 0) (y : Fin (D.R.N 0) → (D.sp.X 0).V)
    (hy : ∀ a, y a ∈ dualSub (D.sp.X 0) (D.clsLat u 0 c)) (g : D.what₂.Tau → GL (Fin (D.R.N 0)) D.what₂.LL)
    (hg : ∀ τ, ((g τ : GL (Fin (D.R.N 0)) D.what₂.LL) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL) = gM CV c y τ)
    {x : ((D.fm u).lat 0).V} (hx : x ∈ NC CV c) (m : MonI ((D.fm u).lam 0)) :
    cfMap ((D.fm u).lam 0) g (coE CV (hTV0 D u) x c) m ∈ twId ((D.fm u).lam 0) (MQ CV c) := by
  classical
  rw [mem_twId]
  intro w B hB
  set w' := D.plEq.symm w with hw'
  have hw : D.plEq w' = w := D.plEq.apply_symm_apply w
  have hLB : ∀ τ, LocBasis D w' (CV.Q c τ) (CV.eQ c τ) (B τ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL) :=
    fun τ => locBasis_of_isBasisAt CV c τ w' (B τ) (by rw [hw]; exact hB τ)
  let γ : (D.mem u).C.cls 0 → D.what₂.Tau → Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL := fun c' τ =>
    if c' = c then (B τ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL)
    else Classical.choose (exists_locBasis w' (CV.Q c' τ) (CV.Q_good c' τ) (CV.eQ c' τ))
  have hγ : ∀ c' τ, LocBasis D w' (CV.Q c' τ) (CV.eQ c' τ) (γ c' τ) := by
    intro c' τ
    by_cases h : c' = c
    · simp only [γ, if_pos h]
      rw [h]
      exact hLB τ
    · simp only [γ, if_neg h]
      exact Classical.choose_spec (exists_locBasis w' (CV.Q c' τ) (CV.Q_good c' τ) (CV.eQ c' τ))
  have hxL : x ∈ ((D.fm u).lat 0).L := by
    obtain ⟨x', hx', rfl⟩ := hx
    exact prjC_mem CV c hx'
  have hxW : x ∈ locW D.what₂.places w' ((D.fm u).lat 0).L := Submodule.subset_span hxL
  have hP := (CV.fin w' γ hγ x).1 hxW c
  simp only [γ, if_pos rfl] at hP
  set F : Pol D.what₂.LL D.what₂.Tau (D.R.N 0) := ((coE CV (hTV0 D u) x c : VV D.what₂.LL ((D.fm u).lam 0)) :
    Pol D.what₂.LL D.what₂.Tau (D.R.N 0)) with hF
  have hFco : F = CV.co x c := coE_coe CV (hTV0 D u) x c
  have hinvB : (fun τ => (B τ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL)⁻¹) =
      fun τ => (((B⁻¹) τ : GL (Fin (D.R.N 0)) D.what₂.LL) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL) := by
    funext τ
    rw [Pi.inv_apply, Matrix.coe_units_inv]
  rw [← hFco, hinvB, actAll_eq_actP] at hP
  have hF0 : actP ((D.fm u).lam 0) B⁻¹ F ∈ (map (σ := D.what₂.Tau × Fin (D.R.N 0) × Fin (D.R.N 0)) (locRing w).subtype).range := by
    refine mem_range_of_coeff_mem _ fun m' => ?_
    rw [← hw]
    exact intW_mem_locRing w' (coeff_mem_of_intSpanAt w' _ hP m')
  have hU : ∀ τ a b, (((g * B) τ : GL (Fin (D.R.N 0)) D.what₂.LL) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL)ᵀ a b ∈
      locRing w := by
    intro τ a b
    have hcol : (fun c => (B τ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL) c a) ∈ localization₂ w.asIdeal (MQ CV c τ) := by
      rw [hB τ]
      exact le_localisation w _ (Submodule.subset_span ⟨a, rfl⟩)
    obtain ⟨s, hs, hsx⟩ := hcol
    rw [mem_locRing]
    refine ⟨s, hs, ?_⟩
    have := gM_int CV c y hy τ _ hsx b
    rw [← hg τ, Matrix.mulVec_smul] at this
    have e : (((g * B) τ : GL (Fin (D.R.N 0)) D.what₂.LL) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL)ᵀ a b =
        ((g τ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL) *ᵥ fun c => (B τ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL) c a) b := by
      simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
    rw [e]
    exact this
  have hkey := coeff_mem_of_mem_range _ (block_action_integral (locRing w) _ hU hF0) m.1
  have e : Formalism.GradedWeylDivisibility.blockAct D.what₂.LL (fun τ => (((g * B) τ : GL (Fin (D.R.N 0)) D.what₂.LL) :
      Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL)ᵀ) (actP ((D.fm u).lam 0) B⁻¹ F) =
      detTwK ((D.fm u).lam 0) B⁻¹ • trAct g F := by
    show trAct (g * B) (actP ((D.fm u).lam 0) B⁻¹ F) = _
    rw [trAct_mul]
    simp only [actP, LinearMap.smul_apply, AlgHom.toLinearMap_apply, AlgHom.comp_apply, map_smul, transpose_action_inv_right]
  rw [e, MvPolynomial.coeff_smul, smul_eq_mul, mem_locRing] at hkey
  exact hkey

end Int2

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
end
end

-- Source module: Formalism.LocalToGlobal.GlobalTheory.GL4.PacketOfFrameDegree

section

@[expose] public section

open Module NumberField IsDedekindDomain MvPolynomial
open scoped Matrix

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.HN Formalism.MainNotions.flipTwoThree Formalism.L2.DIV Formalism.L2.GlobalTheoryTheory.HLatOps Formalism.L2.Col Formalism.BasicNotions.SkeletonIndexLemmas

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def QFrameDeg (D : D7) : Prop :=
  ∀ u (CV : ColVal D u) c τ,
    (D.R.N 0 : ℝ) * (CV.Q c τ).mu =
      (D.R.N 0 : ℝ) * (latK D.what₂.LL (MQ CV c τ)).mu +
        (1 / (nPl D.what₂.LL : ℝ)) * ∑ v, Real.log (‖((CV.Q c τ).X v).det‖ ^ 2)

section T

variable {D : D7} {u : D.what₂.Word} (CV : ColVal D u)

theorem MQ_lattice (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) : Submodule.IsLattice D.what₂.LL (MQ CV c τ) := by
  exact Submodule.IsLattice.of_fg _ ((CV.Q_good c τ).2.1.map _)

theorem MQ_fullLattice (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) :
    Submodule.IsFullLattice D.what₂.LL (MQ CV c τ) := by
  refine { toIsLattice := MQ_lattice CV c τ, span_eq_top := ?_ }
  unfold MQ
  rw [Submodule.map_coe, LinearMap.coe_restrictScalars]
  rw [show ⇑(crdQ CV c τ : (CV.Q c τ).V →ₗ[D.what₂.LL] (Fin (D.R.N 0) → D.what₂.LL)) = ⇑(crdQ CV c τ) from rfl]
  rw [← LinearEquiv.coe_coe, Submodule.span_image, (CV.Q_good c τ).2.2, Submodule.map_top]
  exact LinearEquiv.range _

theorem detTwK_inv_ne (c : (D.mem u).C.cls 0) (v : InfinitePlace D.what₂.LL) :
    detTwK ((D.fm u).lam 0) (invFr CV v c)⁻¹ ≠ 0 := by
  unfold detTwK
  refine Finset.prod_ne_zero_iff.mpr fun τ _ => ?_
  unfold detPow
  exact Units.ne_zero _

theorem det_invFr_inv (v : InfinitePlace D.what₂.LL) (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) :
    ((Matrix.GeneralLinearGroup.det ((invFr CV v c)⁻¹ τ) : ℂˣ) : ℂ) = ((CV.Q c τ).X v).det := by
  simp only [Pi.inv_apply, map_inv, Units.val_inv_eq_inv_val, Matrix.GeneralLinearGroup.val_det_apply, invFr,
    brpGL]
  show ((Matrix.reindex (CV.eQ c τ) (CV.eQ c τ)) ((CV.Q c τ).X v)⁻¹).det⁻¹ = _
  rw [Matrix.det_reindex_self, Matrix.det_nonsing_inv, Ring.inverse_eq_inv, inv_inv]

theorem log_detTw (c : (D.mem u).C.cls 0) (v : InfinitePlace D.what₂.LL) :
    Real.log (‖detTwK ((D.fm u).lam 0) (invFr CV v c)⁻¹‖ ^ 2) =
      ∑ τ, (((D.fm u).lam 0 τ).detShift : ℝ) * Real.log (‖((CV.Q c τ).X v).det‖ ^ 2) := by
  unfold detTwK
  simp only [detPow, Units.val_zpow_eq_zpow_val, det_invFr_inv, norm_prod, norm_zpow]
  have hne : ∀ τ, ((CV.Q c τ).X v).det ≠ 0 := fun τ => by
    rw [← det_invFr_inv CV v c τ]
    exact Units.ne_zero _
  rw [← Finset.prod_pow, Real.log_prod]
  · refine Finset.sum_congr rfl fun τ _ => ?_
    rw [show (‖((CV.Q c τ).X v).det‖ ^ ((D.fm u).lam 0 τ).detShift) ^ 2 =
        (‖((CV.Q c τ).X v).det‖ ^ 2) ^ ((D.fm u).lam 0 τ).detShift by rw [sq, sq, mul_zpow], Real.log_zpow]
  · intro τ _
    exact pow_ne_zero _ (zpow_ne_zero _ (norm_ne_zero_iff.mpr (hne τ)))

theorem detShift_eq (τ : D.what₂.Tau) :
    ((((D.fm u).lam 0 τ).detShift : ℤ) : ℝ) = ((lamCol D u τ (D.R.k - 1) : ℚ) : ℝ) := by
  have hn := rank_zero_pos D
  have hk := columnCount_pos D
  unfold DomWeight.detShift
  rw [dite_eq_left hn]
  have := weight_eq_lamCol D u τ ⟨D.R.N 0 - 1, by omega⟩
  rw [this]
  congr 3
  simp [Ranks.N_zero]

theorem classMapT_of (h : QFrameDeg D) : ClassMapT D := by
  intro u CV c y hy
  obtain ⟨hyd, hli, -⟩ := hy
  have := (columnHypotheses D u).tc
  have hn : 0 < D.R.N 0 := rank_zero_pos D
  have hM : ∀ τ, Submodule.IsFullLattice D.what₂.LL (MQ CV c τ) := MQ_fullLattice CV c
  refine ⟨cfMap ((D.fm u).lam 0) (gG CV c y hli) ∘ₗ (LinearMap.proj c ∘ₗ (coE CV (hTV0 D u) : ((D.fm u).lat 0).V →ₗ[D.what₂.LL]
      ((D.mem u).C.cls 0 → VV D.what₂.LL ((D.fm u).lam 0)))), twIdeal ((D.fm u).lam 0) (MQ CV c) hM,
    fun v => ‖detTwK ((D.fm u).lam 0) (invFr CV v c)⁻¹‖ ^ 2, ?_, twIdeal_ne_zero _ _ hM, ?_, ?_, ?_, ?_⟩
  · exact injOn_NC CV c _ (cfMap_injective _ _)
  · intro x hx m
    rw [twIdeal_coe]
    exact cf_mem_twId CV c y hyd (gG CV c y hli) (fun τ => gG_coe CV c y hli τ) hx m
  · intro v
    exact pow_pos (norm_pos_iff.2 (detTwK_inv_ne CV c v)) 2
  · intro v x
    exact class_norm CV c y hli v x
  · rw [twisted_ideal_norm_formula D.what₂.LL hn _ _ hM]
    simp_rw [log_detTw CV c]
    have hQ := fun τ => h u CV c τ
    have hslope := fun τ => q_lattice_slope D u CV c τ
    have hk : (D.R.N 0 : ℝ) = (D.R.k : ℝ) := by rw [Ranks.N_zero]
    have hk0 : (0 : ℝ) < D.R.k := by exact_mod_cast columnCount_pos D
    have e1 : (1 / (nPl D.what₂.LL : ℝ)) * ∑ v, ∑ τ, (((D.fm u).lam 0 τ).detShift : ℝ) * Real.log (‖((CV.Q c τ).X v).det‖ ^ 2) =
        ∑ τ, (((D.fm u).lam 0 τ).detShift : ℝ) * ((1 / (nPl D.what₂.LL : ℝ)) * ∑ v, Real.log (‖((CV.Q c τ).X v).det‖ ^ 2)) := by
      rw [Finset.sum_comm, Finset.mul_sum]
      refine Finset.sum_congr rfl fun τ _ => ?_
      rw [← Finset.mul_sum]
      ring
    rw [e1, ← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
    refine le_of_eq (Finset.sum_congr rfl fun τ _ => ?_)
    rw [← mul_add, ← hQ τ, hslope τ, hk, detShift_eq]
    field_simp

end T

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
end
end

-- Source module: Formalism.LocalToGlobal.GlobalTheory.GL4.ClassMapArchimedean

section

@[expose] public section

open Module NumberField IsDedekindDomain MvPolynomial
open scoped Matrix

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.HN Formalism.MainNotions.flipTwoThree Formalism.L2.DIV Formalism.L2.GlobalTheoryTheory.HLatOps Formalism.L2.Col Formalism.BasicNotions.SkeletonIndexLemmas
open Formalism.LFunctionChainParameters.slopeLatticeData (FinPl)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section GramSelf

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem gramJ_self_det (A : HLat K) (v : InfinitePlace K) : (gramJ A A.b v).det.re = (‖(A.X v).det‖ ^ 2)⁻¹ := by
  classical
  have h : ∀ i', (A.X v)⁻¹ *ᵥ vecAt A.b v (A.b i') = fun k => (A.X v)⁻¹ k i' := by
    intro i'
    funext k
    simp [vecAt, Matrix.mulVec, dotProduct, Finsupp.single_apply]
  have e : gramJ A A.b v = ((A.X v)⁻¹)ᴴ * (A.X v)⁻¹ := by
    ext i j
    simp only [gramJ, Matrix.of_apply, majAt, fcoord, Matrix.mul_apply, Matrix.conjTranspose_apply]
    rw [h, h]
  have hz : ∀ z : ℂ, (star z * z).re = ‖z‖ ^ 2 := fun z => by
    rw [show star z * z = ((Complex.normSq z : ℝ) : ℂ) by rw [Complex.normSq_eq_conj_mul_self]; rfl,
      Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  rw [e, Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', hz, norm_inv, inv_pow]

end GramSelf

section F

variable {D : D7} {u : D.what₂.Word} (CV : ColVal D u)

theorem crd_fam (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) (B : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL)
    (a : Fin (D.R.N 0)) :
    crdQ CV c τ (∑ i, B i a • (CV.Q c τ).b ((CV.eQ c τ).symm i)) = famOf (Pi.basisFun D.what₂.LL (Fin (D.R.N 0))) B a := by
  ext j
  simp [crdQ, famOf, Basis.equivFun_apply, Finset.sum_apply, Pi.basisFun_apply,
    Finsupp.single_apply, Pi.single_apply]

theorem latOf_map_crd (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) (B : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL) :
    (latOf (K := D.what₂.LL) fun a : Fin (D.R.N 0) => ∑ i, B i a • (CV.Q c τ).b ((CV.eQ c τ).symm i)).map
        ((crdQ CV c τ : (CV.Q c τ).V →ₗ[D.what₂.LL] (Fin (D.R.N 0) → D.what₂.LL)).restrictScalars (𝓞 D.what₂.LL)) =
      latOf (K := D.what₂.LL) (famOf (Pi.basisFun D.what₂.LL (Fin (D.R.N 0))) B) := by
  simp only [latOf, Submodule.map_span, ← Set.range_comp]
  congr 1
  congr 1
  funext a
  exact crd_fam CV c τ B a

theorem q_frame_degree (D : D7) : QFrameDeg D := by
  intro u CV c τ
  classical
  have := (columnHypotheses D u).tc
  have hQ := CV.Q_good c τ
  have hn : 0 < D.R.N 0 := rank_zero_pos D
  haveI : Nonempty (Fin (D.R.N 0)) := ⟨⟨0, hn⟩⟩
  haveI : Nonempty (CV.Q c τ).ι := ⟨(CV.eQ c τ).symm ⟨0, hn⟩⟩
  have hfr : Module.finrank D.what₂.LL (CV.Q c τ).V = D.R.N 0 := by
    rw [Module.finrank_eq_card_basis (CV.Q c τ).b, Fintype.card_congr (CV.eQ c τ), Fintype.card_fin]
  choose bK hbK using fun p : FinPl D.what₂.LL => exists_basis_locP (toH p) hQ.2.1 hQ.2.2 hfr
  set g : FinPl D.what₂.LL → Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL :=
    fun p => ((CV.Q c τ).b.reindex (CV.eQ c τ)).toMatrix (bK p) with hgdef
  have hg : ∀ p, (g p).det ≠ 0 := fun p => by
    have := ((CV.Q c τ).b.reindex (CV.eQ c τ)).isUnit_det (bK p)
    rw [Basis.det_apply] at this
    exact this.ne_zero
  have hfam : ∀ p, (fun a : Fin (D.R.N 0) => ∑ i, g p i a • (CV.Q c τ).b ((CV.eQ c τ).symm i)) = bK p := fun p => by
    funext a
    have := ((CV.Q c τ).b.reindex (CV.eQ c τ)).sum_repr (bK p a)
    simpa [hgdef, Basis.toMatrix_apply, Basis.reindex_apply] using this
  have hloc : ∀ p, localization₂ (toH p).asIdeal (CV.Q c τ).L = localization₂ (toH p).asIdeal
      (latOf (K := D.what₂.LL) fun a : Fin (D.R.N 0) => ∑ i, g p i a • (CV.Q c τ).b ((CV.eQ c τ).symm i)) := fun p => by
    rw [hfam p, hbK p]
  obtain ⟨-, -, hmuQ⟩ := mu_of_frames (CV.Q c τ) hQ (ownFrame (CV.Q c τ) (CV.eQ c τ) g hg hloc)
  have hML := MQ_lattice CV c τ
  have hspan : Submodule.span D.what₂.LL (MQ CV c τ : Set (Fin (D.R.N 0) → D.what₂.LL)) = ⊤ := by
    unfold MQ
    rw [Submodule.map_coe, LinearMap.coe_restrictScalars]
    rw [show ⇑(crdQ CV c τ : (CV.Q c τ).V →ₗ[D.what₂.LL] (Fin (D.R.N 0) → D.what₂.LL)) = ⇑(crdQ CV c τ) from rfl]
    rw [← LinearEquiv.coe_coe, Submodule.span_image, hQ.2.2, Submodule.map_top]
    exact LinearEquiv.range _
  have hstdGood : (stdHL D.what₂.LL (MQ CV c τ)).Good := ⟨fun _ => by simp, hML.fg, hspan⟩
  let FS : FrameData (stdHL D.what₂.LL (MQ CV c τ)) (Fin (D.R.N 0)) :=
    { e := Pi.basisFun D.what₂.LL (Fin (D.R.N 0))
      Γ := g
      det_ne := hg
      loc := fun p => by
        show localization₂ (toH p).asIdeal (MQ CV c τ) = _
        ext z
        obtain ⟨q, rfl⟩ := (crdQ CV c τ).surjective z
        unfold MQ
        rw [mem_localization_map_equiv, hloc p, ← latOf_map_crd CV c τ (g p), mem_localization_map_equiv] }
  obtain ⟨-, -, hmuS⟩ := mu_of_frames (stdHL D.what₂.LL (MQ CV c τ)) hstdGood FS
  rw [brp_latK_mu D.what₂.LL (MQ CV c τ) hML.fg]
  have hQinf : infPart (fun v => (gramJ (CV.Q c τ) (ownFrame (CV.Q c τ) (CV.eQ c τ) g hg hloc).e v).det.re) =
      -((1 / (nPl D.what₂.LL : ℝ)) * ∑ v, Real.log (‖((CV.Q c τ).X v).det‖ ^ 2)) := by
    unfold infPart
    rw [← mul_neg, ← Finset.sum_neg_distrib]
    congr 1
    refine Finset.sum_congr rfl fun v _ => ?_
    beta_reduce
    rw [show ((ownFrame (CV.Q c τ) (CV.eQ c τ) g hg hloc).e : (CV.Q c τ).ι → (CV.Q c τ).V) = (CV.Q c τ).b from rfl,
      gramJ_self_det, Real.log_inv]
  have hSinf : infPart (fun v => (gramJ (stdHL D.what₂.LL (MQ CV c τ)) FS.e v).det.re) = 0 := by
    unfold infPart
    rw [Finset.sum_eq_zero fun v _ => ?_, mul_zero]
    beta_reduce
    rw [show (FS.e : Fin (D.R.N 0) → (Fin (D.R.N 0) → D.what₂.LL)) = (stdHL D.what₂.LL (MQ CV c τ)).b from rfl,
      gramJ_self_det]
    simp
  have hfin : finPart (fun p => ((ownFrame (CV.Q c τ) (CV.eQ c τ) g hg hloc).Γ p).det) = finPart (fun p => (FS.Γ p).det) := by
    congr 1
    funext p
    exact Matrix.det_submatrix_equiv_self _ _
  have hcQ : (Fintype.card (CV.Q c τ).ι : ℝ) = (D.R.N 0 : ℝ) := by
    rw [Fintype.card_congr (CV.eQ c τ), Fintype.card_fin]
  rw [hcQ] at hmuQ
  rw [Fintype.card_fin] at hmuS
  rw [hmuQ, hmuS, hQinf, hSinf, hfin]
  ring

theorem class_map_archimedean (D : D7) : ClassMapT D :=
  classMapT_of (q_frame_degree D)

end F

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
end
end

-- Source module: Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.UpperSlopeOfMaximalConstant

section

@[expose] public section

namespace Formalism.MainNotions.flipTwoThree

theorem hookBound_holds : HookBound := hook_length_bound

end Formalism.MainNotions.flipTwoThree
end
end

-- Source module: Formalism.LocalToGlobal.GlobalTheory.GL4.PStmtFree

section

@[expose] public section

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Formalism.BasicNotions Formalism.MainNotions.flipTwoThree

theorem slopeMaxGiven_free (D : D7) : SlopeMaxGiven D :=
  slopeMaxGiven_of_class D (slopeMaxClass_of_map D (class_map_of_archimedean D (class_map_archimedean D)))

theorem slope_inequality_constant_four (D : D7) : SlopeMaxOpenPart D 4 :=
  slope_bound_of_max_slope hookBound_holds D (slopeMaxGiven_free D)

theorem slope_inequality_family_four {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : FamilySlopeMaxOpenPart Fm 4 := by
  unfold FamilySlopeMaxOpenPart fam0
  exact ⟨0, fun _ _ _ _ => slope_inequality_constant_four _⟩

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
end
end
