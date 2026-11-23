module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.FormsPin
public import Formalism.SharpRestriction.Divisibility.OrbitPlaces
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ClassSumTermLawStabiliserTargetStatement
public import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
public import Formalism.LocalToGlobal.KernelLattices.ThDistC
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.IsAdmissibleFlagPairOfUnitriangularLeftAutomorph
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.SelfDualLatticeNorms.SelfDualComap
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.StdOK
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Tactic.NormNum.Parity
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JetLL
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelOperatorMapsStabiliserEquivariantFormsStatement
public import Formalism.LocalRingCardinality.DataKerP

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.DifferentiableSumU

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H NumberField IsDedekindDomain Classical

namespace GlobalTheory.KerFinEntire

section General

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

theorem differentiable_opU (H : Sesq V) {F : V → ℂ} (hF : Differentiable ℂ F) (x : V) :
    Differentiable ℂ (opU H x F) := by
  have h : Differentiable ℂ fun z => H z x := (LinearMap.toContinuousLinearMap (H.flip x)).differentiable
  unfold opU
  fun_prop

theorem differentiable_sumU (H : Sesq V) (α : V → ℂ) (S : Finset V) {F : V → ℂ} (hF : Differentiable ℂ F) :
    Differentiable ℂ (sumU H α S F) := by
  unfold sumU
  exact Differentiable.fun_sum fun x _ => (differentiable_opU H hF x).const_mul _

theorem differentiable_xiL (H : Sesq V) (α : V → ℂ) (vol : ℝ) (SX SA SB : Finset V) (Φ : V → ℂ) {e : V → ℂ}
    (he : Differentiable ℂ e) : Differentiable ℂ (xiL H α vol SX SA SB Φ e) := by
  unfold xiL xiS
  exact Differentiable.fun_sum fun x _ => (differentiable_opU H (differentiable_sumU H _ SB he) x).const_mul _

end General

theorem differentiable_thC {E : Type} [Field E] [NumberField E] [StarRing E] {ι : Type} [Fintype ι] {a b : ℕ}
    (emb : ι → E →+* ℂ) (δ : ℂ) (d : ℕ) (sc : ℝ) (AA0 : Submodule (𝓞 E) E) (SS : Finset (HeightOneSpectrum (𝓞 E)))
    (N : Submodule (𝓞 E) (Sp E a)) (N' : Submodule (𝓞 E) (Sp E b)) (c : ℕ) (Ξ : HomE E a b → ℂ) {θ : VV ι a b → ℂ}
    (hθ : Differentiable ℂ θ) : Differentiable ℂ (thC emb δ d sc AA0 SS N N' c Ξ θ) := by
  unfold thC xiV
  exact differentiable_xiL _ _ _ _ _ _ _ hθ

theorem kerFin_entire : ∀ (D : D7) (X : Fields) (s : Seam D X) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ), s.Ok → TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → TaylorLogMetric.IsChi D χ → ∀ (a b : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)), TaylorLogMetric.admitted D a b (s.lat N) (s.lat N') → ∀ (SS : Finset (HeightOneSpectrum (𝓞 X.E))) (c : ℕ) (Ξ : HomE X.E a b → ℂ), Differentiable ℂ (thC (X.embC (ambOf s B χ cD : Amb X).σ₀) (ambOf s B χ cD : Amb X).δ (ambOf s B χ cD : Amb X).d (ambOf s B χ cD : Amb X).sc (ambOf s B χ cD : Amb X).AA SS N N' c Ξ ((ambOf s B χ cD : Amb X).e a b N N')) := by
  intro D X s cc δ B χ cD _ hcc hδ hχ a b N N' hA SS c Ξ
  have hE : Differentiable ℂ (B.eNat χ a b (s.lat N) (s.lat N')) :=
    (B.vec_mem_ne hcc hδ (Formalism.L2.Ker.KS.Lat.delta_ne hcc hδ) (B.stdOK hcc hδ) χ hχ a b _ _ hA).1.1
  let T : VCx X.Tau a b →L[ℂ] TaylorLogMetric.VC D a b := ContinuousLinearMap.pi fun τ => ContinuousLinearMap.proj (s.iT.symm τ)
  have he : Differentiable ℂ ((ambOf s B χ cD : Amb X).e a b N N') := hE.comp T.differentiable
  exact differentiable_thC _ _ _ _ _ _ _ _ _ _ he

end GlobalTheory.KerFinEntire
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.KerTieEntire

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Forms Formalism.L2.Col Formalism.L2.DIV Formalism.HermitianLatticesTheory GlobalTheory.KerJ NumberField IsDedekindDomain Classical

namespace GlobalTheory.KerTieEntire

theorem kerTie_entire : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), ∀ u μ, ∀ i < D.R.m, ∀ c c', Differentiable ℂ ((t.O u μ).Th i c c') := by
  intro D L hT Gi Gl K Y cX ex t u μ i _ c c'
  have hEven : ∀ j, Even (D.R.N j) := fun j => D.R.k_even.add (D.R.t_odd.add_one.mul_left j)
  have hAdm : TaylorLogMetric.admitted D _ _ ((t.O u μ).lat i c).1 ((t.O u μ).lat (i + 1) c').1 :=
    ⟨hEven i, hEven (i + 1), ((t.O u μ).lat i c).2, ((t.O u μ).lat (i + 1) c').2⟩
  rw [t.O_lat u μ i c, t.O_lat u μ (i + 1) c'] at hAdm
  rw [t.O_Th u μ i c c']
  have hF := GlobalTheory.KerFinEntire.kerFin_entire D t.X t.seam t.cc t.δ t.B t.χ t.cD t.seam_ok t.cc_ok t.δ_ok t.χ_ok _ _
    ((t.rd u μ).N i c) ((t.rd u μ).N (i + 1) c') hAdm (t.rd u μ).SS (t.rd u μ).lev ((t.rd u μ).Xi i c c')
  let T : TaylorLogMetric.VC D (D.R.N i) (D.R.N (i + 1)) →L[ℂ] VCx t.X.Tau (D.R.N i) (D.R.N (i + 1)) :=
    ContinuousLinearMap.pi fun τ => ContinuousLinearMap.proj (t.seam.iT τ)
  exact hF.comp T.differentiable

end GlobalTheory.KerTieEntire
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemberFormsStableOfReferenceTuple

section

@[expose] public section

open Formalism.BasicNotions Classical

namespace GlobalTheory.KFiMu0

theorem fi_eq_range' {R : Ranks} {LL : Type} [Field LL] [NumberField LL] [StarRing LL] {embLL : LL →+* ℂ} {Pl : Rows.Places LL}
    {Tau : Type} [Fintype Tau] {hc : Tau → HCParam R} {C : ColumnChain R Tau hc} {A : ColumnsAtT R C} {P : PeriodMap R C}
    (M : MemberForms LL embLL Pl Tau hc C A P) (j : ℕ) : M.Fi j = Submodule.span ℂ (Set.range (M.emb j)) := by
  refine le_antisymm ?_ (Submodule.span_le.2 ?_)
  · rw [← (M.emb_basis j).2]
    exact Submodule.span_mono (by rintro _ ⟨a, rfl⟩; exact ⟨_, rfl⟩)
  · rintro _ ⟨x, rfl⟩

    rw [← (M.emb_basis j).2, ← (M.lat j).b.sum_repr x, map_sum]
    refine Submodule.sum_mem _ fun a _ => ?_
    rw [LinearMap.map_smulₛₗ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

theorem carries_one {R : Ranks} {LL : Type} [Field LL] [NumberField LL] [StarRing LL] {embLL : LL →+* ℂ} {Pl : Rows.Places LL}
    {Tau : Type} [Fintype Tau] {hc : Tau → HCParam R} {C C' : ColumnChain R Tau hc} (h : C' = C)
    {A : ColumnsAtT R C} {P : PeriodMap R C} {A' : ColumnsAtT R C'} {P' : PeriodMap R C'}
    (M : MemberForms LL embLL Pl Tau hc C A P) (M' : MemberForms LL embLL Pl Tau hc C' A' P')
    (e : ∀ j, j ≤ R.m → ((M.lat j).V ≃ₗ[LL] (M'.lat j).V)) (he : ∀ j hj x, HEq (M'.emb j (e j hj x)) (M.emb j x))
    (i : ℕ) (hi : i < R.m) (H : ∀ φ ∈ M'.Fi i, C'.K i φ ∈ M'.Fi (i + 1)) :
    ∀ φ ∈ M.Fi i, C.K i φ ∈ M.Fi (i + 1) := by
  subst h
  have k : ∀ j, j ≤ R.m → M.Fi j = M'.Fi j := fun j hj => by
    rw [fi_eq_range', fi_eq_range']
    congr 1
    ext φ
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨e j hj x, eq_of_heq (he j hj x)⟩
    · rintro ⟨y, rfl⟩
      obtain ⟨x, rfl⟩ := (e j hj).surjective y
      exact ⟨x, (eq_of_heq (he j hj x)).symm⟩
  intro φ hφ
  rw [k _ hi.le] at hφ
  rw [k _ hi]
  exact H φ hφ

theorem memberForms_stable_of_reference_tuple : ∀ (D : D7) (T : TwForms D) (u : D.what₂.Word), ∀ i < D.R.m,
    (∀ φ ∈ (T.fm u D.what₂.mu0).Fi i, (D.chTw u D.what₂.mu0).K i φ ∈ (T.fm u D.what₂.mu0).Fi (i + 1)) →
    ∀ φ ∈ (D.fm u).Fi i, (D.mem u).C.K i φ ∈ (D.fm u).Fi (i + 1) :=
  fun D T u i hi H => carries_one (D.memberColumns_twistedChain_base u) (D.fm u) (T.fm u D.what₂.mu0) (T.eMu0 u) (T.eMu0_emb u) i hi H

end GlobalTheory.KFiMu0
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelClassSumsCarryChainComplexForms

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker GlobalTheory.KerJ Classical

namespace GlobalTheory.KFiClose

theorem kFi_of_tie : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D)
    (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), ColSide t → FormsPin t → OrbitPlaces.KFi D ex.tw := by
  intro D L hT Gi Gl K Y cX ex t hC hF
  have second : ∀ u μ, DV.Used D μ → ∀ i < D.R.m, ∀ φ ∈ (ex.tw.fm u μ).Fi i, (D.chTw u μ).K i φ ∈ (ex.tw.fm u μ).Fi (i + 1) := by
    intro u μ hμ
    obtain ⟨G, hFA, hSP⟩ := hF u μ hμ
    exact GlobalTheory.T.kernelOperator_maps_stabiliserEquivariant_forms D u (D.chTw u μ) _ _ (ex.tw.fm u μ) (t.O u μ) G hFA (t.unf u μ)
      (fun i hi c c' => GlobalTheory.KerTieEntire.kerTie_entire D L hT Gi Gl K Y cX ex t u μ i hi c c')
      (GlobalTheory.T.classSum_term_law_stabiliser_target D L hT Gi Gl K Y cX ex t hC u μ G hSP)
  have h0 : DV.Used D D.what₂.mu0 := by
    unfold DV.Used
    exact Or.inl rfl
  exact ⟨fun u i hi => GlobalTheory.KFiMu0.memberForms_stable_of_reference_tuple D ex.tw u i hi (second u _ h0 i hi), second⟩

end GlobalTheory.KFiClose
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelClassSumsCarryChainComplexFormsStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker GlobalTheory.KerJ Classical

theorem _root_.GlobalTheory.T.kernelClassSums_carry_chainComplexForms : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), ColSide t → FormsPin t → OrbitPlaces.KFi D ex.tw := by
  first | exact @GlobalTheory.KFiClose.kFi_of_tie | exact GlobalTheory.KFiClose.kFi_of_tie | (intros; apply GlobalTheory.KFiClose.kFi_of_tie <;> assumption)
end
end
