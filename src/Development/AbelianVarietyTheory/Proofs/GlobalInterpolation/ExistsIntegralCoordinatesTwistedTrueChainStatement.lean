module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LowerTieTwAt
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsIntegralHyperplaneFormOfLocalCoordsIntegraStatement
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CoP
public import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.InvTrKEmbGLApply
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LocalBasisRepLatticeIntegralCoordsSpecStatement
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemLocWDelAtrIffStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SpanMapNabKDelK
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
import Formalism.LocalToGlobal.Columns.PolyFnLemmas
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LocalCoordsEvaluationLowerRowMapEqTensorBranchinStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HyperplaneFormIntegralLocalCoordsMemIntegralSpan

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PtIntCoord

theorem natW_shW {n : ℕ} (l : DomWeight n) (c : ℤ) : (GlobalTheory.Mem.Col2.shW l c).natW = l.natW := by
  have e : GlobalTheory.Mem.Col2.shW l c = Formalism.MainNotions.product_first_zeroth_parts.wSh l (-c) := by
    unfold GlobalTheory.Mem.Col2.shW Formalism.MainNotions.product_first_zeroth_parts.wSh
    congr 1
    funext i
    ring
  rw [e, Formalism.MainNotions.product_first_zeroth_parts.natW_wSh]

theorem coP_mem_intSpan : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (l0 : I.Law0 l) (u : B.Word) (a : I.ι) (w : B.places.Pl), ∀ z ∈ ((I.tw l l0 Z).fm u a).ptC, (∃ y ∈ ((I.tw l l0 Z).fm u a).SP w, ((I.tw l l0 Z).fm u a).ptEmb y = z) → ∀ c, GlobalTheory.PerQ.Co.coP I u a w z c ∈ Formalism.MainNotions.product_first_zeroth_parts.IntSpan (I.rec7 l Z) w ((I.rec7 l Z).fm u).sg := by
  intro B X I hI l Z l0 u a w z _hz hyz c
  obtain ⟨y, hy, rfl⟩ := hyz
  clear _hz
  have hQ : (I.perIn u a).Ok := l.per u a
  have hA : y.1 c ∈ locW B.places w (delAtr B.fields.emb (I.perIn u a).sgT
      ((I.perIn u a).S'.Lsh c.1 ((I.perIn u a).S'.rep c))) := by
    induction hy using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span (hx c)
    | zero => exact Submodule.zero_mem _
    | add x x' _ _ hx hx' => exact Submodule.add_mem _ hx hx'
    | smul r x _ hx => exact Submodule.smul_mem _ r hx
  have hB := (GlobalTheory.T.localBasisRepLattice_integralCoords_spec I hI l u a w c).1
  have key := (GlobalTheory.T.mem_locW_delAtr_iff' B.fields.emb B.embLL B.places (I.rec7 l Z).plEq (I.rec7 l Z).val_eq
    (I.perIn u a).sgT (I.perIn u a).sg (fun τ => natW_shW _ _) _ (hQ.step.lsh_full_lat c.1 _) w _ hB (y.1 c)).1 hA
  have e : GlobalTheory.PerQ.Co.coP I u a w (((I.tw l l0 Z).fm u a).ptEmb y) c =
      MvPolynomial.map B.embLL (rhoVr B.fields.emb (I.perIn u a).sgT (GlobalTheory.PerQ.Co.bP I u a w c)⁻¹ (y.1 c)).1 := by
    show actP _ _ (polOf _ _ _ (evV B.fields.emb 1 (I.perIn u a).sgT B.embLL (y.1 c))) = _
    rw [GlobalTheory.LvT.BuiltChain.polOf_evV]
    show _ = MvPolynomial.map B.embLL (actP (I.perIn u a).sgT
      (invTrK (Formalism.L2.DIV.embGL B.fields.emb (GlobalTheory.PerQ.Co.bP I u a w c)⁻¹)) (y.1 c).1)
    rw [GlobalTheory.ValCmp.use₂]
    congr 2
  rw [e]
  exact key

end GlobalTheory.PtIntCoord
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HyperplaneFormIntegralLocalCoordsMemIntegralSpanStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.hyperplaneFormIntegral_localCoords_mem_integralSpan : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (l0 : I.Law0 l) (u : B.Word) (a : I.ι) (w : B.places.Pl), ∀ z ∈ ((I.tw l l0 Z).fm u a).ptC, (∃ y ∈ ((I.tw l l0 Z).fm u a).SP w, ((I.tw l l0 Z).fm u a).ptEmb y = z) → ∀ c, GlobalTheory.PerQ.Co.coP I u a w z c ∈ Formalism.MainNotions.product_first_zeroth_parts.IntSpan (I.rec7 l Z) w ((I.rec7 l Z).fm u).sg := by
  first | exact @GlobalTheory.PtIntCoord.coP_mem_intSpan | exact GlobalTheory.PtIntCoord.coP_mem_intSpan | (intros; apply GlobalTheory.PtIntCoord.coP_mem_intSpan <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LastStepIntegralFormLocalCoordsMemIntegralSpan

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2
  GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PerQ.Co

theorem bc_invTrK_embGL {B : Base} {n : ℕ} (g : GL (Fin n) B.fields.E) :
  (fun τ => Formalism.UG.bc B.embLL (invTrK (embGL B.fields.emb g) τ)) = invTrK (embGL (Formalism.L2.Col.embAt B.embLL B.fields.emb) g) := by
  funext τ
  apply Units.ext
  ext i j
  simp [invTrK, inside₂, embGL, Formalism.UG.bc, Formalism.L2.Col.embAt]
  rw [← Matrix.map_map, ← Formalism.L2.Col.map_inv_matrix, ← Formalism.L2.Col.map_inv_matrix, ← Formalism.L2.Col.map_inv_matrix]
  rfl

theorem intSpan_smul (D : D7) {n : ℕ} (w : D.what₂.places.Pl) (lam : D.what₂.Tau → DomWeight n) (r : D.what₂.LL)
    (hr : r ∈ intW D.what₂.places w) (p : MvPolynomial (D.what₂.Tau × Fin n × Fin n) ℂ)
    (hp : p ∈ Formalism.MainNotions.product_first_zeroth_parts.IntSpan D w lam) : D.what₂.embLL r • p ∈ Formalism.MainNotions.product_first_zeroth_parts.IntSpan D w lam := by
  unfold Formalism.MainNotions.product_first_zeroth_parts.IntSpan at *
  induction hp using AddSubgroup.closure_induction with
  | mem q hq =>
    obtain ⟨r', f, hr', hf, rfl⟩ := hq
    apply AddSubgroup.subset_closure
    exact ⟨r * r', f, mul_mem hr hr', hf, by rw [map_mul, mul_smul]⟩
  | zero => rw [smul_zero]; exact zero_mem _
  | add p q _ _ hp hq => rw [smul_add]; exact add_mem hp hq
  | neg p _ hp => rw [smul_neg]; exact neg_mem hp

theorem latCo_one {B : Base} {X : PreX B.toPre} (I : TC B X) (hI : I.Ok) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word)
    (a : I.ι) (w : B.places.Pl) (c : (I.perIn u a).S'.Cl)
    (y : (((I.chIn u a).S B.R.m).hlat B.fields.emb (GlobalTheory.Mem.Col2.lamT (B.hcW u) B.R.m) ((l.fmL u a).fam B.R.m)).V) (hy : y ∈ (((I.chIn u a).S B.R.m).hlat B.fields.emb (GlobalTheory.Mem.Col2.lamT (B.hcW u) B.R.m) ((l.fmL u a).fam B.R.m)).L) :
    GlobalTheory.PerQ.Co.coM I u a w c (((I.chIn u a).S B.R.m).embF B.fields.emb B.embLL (GlobalTheory.Mem.Col2.lamT (B.hcW u) B.R.m) ((l.fmL u a).fam B.R.m) y ((I.perIn u a).tilC c)) ∈
      Formalism.MainNotions.product_first_zeroth_parts.IntSpan (I.rec7 l Z) w (((I.rec7 l Z).fm u).lam (I.rec7 l Z).R.m) := by
  set v' := ((I.chIn u a).S B.R.m).rho B.fields.emb (GlobalTheory.Mem.Col2.lamT (B.hcW u) B.R.m) (I.perIn u a).b0 (((I.chIn u a).S B.R.m).mv (I.perIn u a).b0 ((I.perIn u a).tilPt c))
          (y.1 (((I.chIn u a).S B.R.m).cl (I.perIn u a).b0 ((I.perIn u a).tilPt c))) with hv'
  have hmem := GlobalTheory.LvT.BuiltChain.rho_mv_mem B.fields.emb ((I.chIn u a).S B.R.m) (GlobalTheory.Mem.Col2.lamT (B.hcW u) B.R.m) ((l.fmL u a).fam B.R.m) y hy (I.perIn u a).b0 ((I.perIn u a).tilPt c)
  have e1 : GlobalTheory.PerQ.Co.coM I u a w c (((I.chIn u a).S B.R.m).embF B.fields.emb B.embLL (GlobalTheory.Mem.Col2.lamT (B.hcW u) B.R.m) ((l.fmL u a).fam B.R.m) y ((I.perIn u a).tilC c)) =
      actP (GlobalTheory.Mem.Col2.lamT (B.hcW u) B.R.m) (invTrK (embGL (Formalism.L2.Col.embAt B.embLL B.fields.emb) (GlobalTheory.PerQ.Co.bM I u a w c)⁻¹))
        (MvPolynomial.map B.embLL v'.1) := by
    unfold GlobalTheory.PerQ.Co.coM
    simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
    congr 1
    rw [← GlobalTheory.LvT.BuiltChain.polOf_evV B.fields.emb B.embLL]
    congr 1
    rw [hv', GlobalTheory.LvT.BuiltChain.evV_rho]
    rfl
  rw [e1, ← bc_invTrK_embGL, ← GlobalTheory.ValCmp.use₂]
  have hB := (GlobalTheory.T.localBasisRepLattice_integralCoords_spec I hI l u a w c).2.2.2
  have hM : Submodule.IsFullLattice B.fields.E (((I.chIn u a).S B.R.m).Lsh (I.perIn u a).b0 ((I.perIn u a).tilPt c)) :=
    ((l.ch u a).step B.R.m).lsh_full_lat (I.perIn u a).b0 ((I.perIn u a).tilPt c)
  have hnat : ∀ τ, ((GlobalTheory.Mem.Col2.lamT (B.hcW u) B.R.m) τ).natW = (((I.rec7 l Z).fm u).lam (I.rec7 l Z).R.m τ).natW := by
    intro τ
    show (GlobalTheory.Mem.Col2.shW (Examples₂.lamOf (B.hcW u τ) B.R.m) _).natW = (Examples₂.lamOf (B.hcW u τ) B.R.m).natW
    funext i
    have hN : 0 < B.R.N B.R.m := lt_of_le_of_lt (Nat.zero_le _) i.2
    simp only [DomWeight.natW, DomWeight.detShift, dif_pos hN, GlobalTheory.Mem.Col2.shW]
    congr 1
    ring
  exact (GlobalTheory.T.mem_locW_delAtr_iff' B.fields.emb B.embLL B.places (I.rec7 l Z).plEq (I.rec7 l Z).val_eq
    (GlobalTheory.Mem.Col2.lamT (B.hcW u) B.R.m) (((I.rec7 l Z).fm u).lam (I.rec7 l Z).R.m) hnat _ hM w _ hB v').1 (Submodule.subset_span hmem)

theorem latCo_gen {B : Base} {X : PreX B.toPre} (I : TC B X) (hI : I.Ok) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word)
    (a : I.ι) (w : B.places.Pl) (c : (I.perIn u a).S'.Cl) :
    ∀ x ∈ Submodule.span (intW B.places w) ((((I.chIn u a).S B.R.m).hlat B.fields.emb (GlobalTheory.Mem.Col2.lamT (B.hcW u) B.R.m) ((l.fmL u a).fam B.R.m)).L : Set (((I.chIn u a).S B.R.m).hlat B.fields.emb (GlobalTheory.Mem.Col2.lamT (B.hcW u) B.R.m) ((l.fmL u a).fam B.R.m)).V),
      GlobalTheory.PerQ.Co.coM I u a w c (((I.chIn u a).S B.R.m).embF B.fields.emb B.embLL (GlobalTheory.Mem.Col2.lamT (B.hcW u) B.R.m) ((l.fmL u a).fam B.R.m) x ((I.perIn u a).tilC c)) ∈
        Formalism.MainNotions.product_first_zeroth_parts.IntSpan (I.rec7 l Z) w (((I.rec7 l Z).fm u).lam (I.rec7 l Z).R.m) := by
  intro y hy
  induction hy using Submodule.span_induction with
  | mem y hy => exact latCo_one I hI l Z u a w c y hy
  | zero => rw [map_zero, Pi.zero_apply, map_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [map_add (f := _), Pi.add_apply, map_add (f := _)]; exact add_mem hy hz
  | smul r y _ hy =>
    have e : r • y = (r : B.LL) • y := rfl
    rw [e, LinearMap.map_smulₛₗ, Pi.smul_apply, map_smul]
    exact intSpan_smul (I.rec7 l Z) w _ (r : B.LL) r.2 _ hy

theorem latCo_mem_intSpan : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (l0 : I.Law0 l) (u : B.Word) (a : I.ι) (w : B.places.Pl), ∀ x ∈ ((I.tw l l0 Z).fm u a).S (I.rec7 l Z).R.m w, ∀ c, GlobalTheory.PerQ.Co.coM I u a w c (((I.tw l l0 Z).fm u a).emb (I.rec7 l Z).R.m x (((I.tw l l0 Z).fm u a).til c)) ∈ Formalism.MainNotions.product_first_zeroth_parts.IntSpan (I.rec7 l Z) w (((I.rec7 l Z).fm u).lam (I.rec7 l Z).R.m) :=
  fun I hI l Z _ u a w x hx c => latCo_gen I hI l Z u a w c x hx

end GlobalTheory.PerQ.Co

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LastStepIntegralFormLocalCoordsMemIntegralSpanStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.lastStepIntegralForm_localCoords_mem_integralSpan : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (l0 : I.Law0 l) (u : B.Word) (a : I.ι) (w : B.places.Pl), ∀ x ∈ ((I.tw l l0 Z).fm u a).S (I.rec7 l Z).R.m w, ∀ c, GlobalTheory.PerQ.Co.coM I u a w c (((I.tw l l0 Z).fm u a).emb (I.rec7 l Z).R.m x (((I.tw l l0 Z).fm u a).til c)) ∈ Formalism.MainNotions.product_first_zeroth_parts.IntSpan (I.rec7 l Z) w (((I.rec7 l Z).fm u).lam (I.rec7 l Z).R.m) := by
  first | exact @GlobalTheory.PerQ.Co.latCo_mem_intSpan | exact GlobalTheory.PerQ.Co.latCo_mem_intSpan | (intros; apply GlobalTheory.PerQ.Co.latCo_mem_intSpan <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsIntegralCoordinatesTwistedTrueChain

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr
  GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix

attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PerQ.Co

theorem pendTw_exists : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), ColIn.Ok I → ∀ (l : TC.Laws I) (Z : TC.Later B (TC.cols I l))
    (l0 : TC.Law0 I l) (u : B.Word) (a : I.ι), ∃ P : GlobalTheory.PerQ.PendTw (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) (TC.tw I l l0 Z) u a, ∀ τ,
      P.br τ = brOne ℂ (Formalism.MainNotions.product_first_zeroth_parts.Nm_succ (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R).symm (Formalism.MainNotions.product_first_zeroth_parts.lamTr (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) u τ)
        (Formalism.MainNotions.product_first_zeroth_parts.sgTr (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) u τ) := by
  intro B X I hI l Z l0 u a
  exact ⟨{ br := fun τ => brOne ℂ (Formalism.MainNotions.product_first_zeroth_parts.Nm_succ (I.rec7 l Z).R).symm (Formalism.MainNotions.product_first_zeroth_parts.lamTr (I.rec7 l Z) u τ)
              (Formalism.MainNotions.product_first_zeroth_parts.sgTr (I.rec7 l Z) u τ)
           coM := fun w c => coM I u a w c
           coP := fun w => coP I u a w
           Pt_eq := GlobalTheory.T.localCoords_evaluationLowerRowMap_eq_tensor_branching I hI l Z l0 u a
           lat_co := GlobalTheory.T.lastStepIntegralForm_localCoords_mem_integralSpan I hI l Z l0 u a
           pt_co := fun w z hz => ⟨GlobalTheory.T.hyperplaneFormIntegral_localCoords_mem_integralSpan I hI l Z l0 u a w z hz, GlobalTheory.T.exists_integralHyperplaneForm_of_localCoords_integral I hI l Z l0 u a w z hz⟩ }, fun _ => rfl⟩

end GlobalTheory.PerQ.Co
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsIntegralCoordinatesTwistedTrueChainStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_integralCoordinates_twistedTrueChain : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (l0 : I.Law0 l) (u : B.Word) (a : I.ι), ∃ P : GlobalTheory.PerQ.PendTw (I.rec7 l Z) (I.tw l l0 Z) u a, ∀ τ, P.br τ = brOne ℂ (Formalism.MainNotions.product_first_zeroth_parts.Nm_succ (I.rec7 l Z).R).symm (Formalism.MainNotions.product_first_zeroth_parts.lamTr (I.rec7 l Z) u τ) (Formalism.MainNotions.product_first_zeroth_parts.sgTr (I.rec7 l Z) u τ) := by
  first | exact @GlobalTheory.PerQ.Co.pendTw_exists | exact GlobalTheory.PerQ.Co.pendTw_exists | (intros; apply GlobalTheory.PerQ.Co.pendTw_exists <;> assumption)
end
end
