module

public import CompanionTheory.AutomorphicTheory.JacobiDiagonalBounds.NFModel
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHat
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RuleGD
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import CompanionTheory.AutomorphicTheory.NumberFieldModels.NFTieProv
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFHatProdKBStmt
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFTopDomPtw
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalMeasurabilityWeakThreshold
public import CompanionTheory.AutomorphicTheory.NumberFieldModels.HsVecProjLe
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaCutoffLimit
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellHermitian
public import Formalism.HermitianCurvature.StatementJF
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PhiBoundPartsOfRadicalParametrisation
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Lemma
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGaugeGRawSmooth
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGaugeGTrChain
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJALocOpAdj
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDJDJComm
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFCoreNExt
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFLeibAsm
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFLeibExp
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFTopDomEmpty
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LiftClosedUnderOperations
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TopFirstOfParts
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: CompanionTheory.AutomorphicTheory.JacobiDiagonalBounds.ModelLoc

section

@[expose] public section

namespace Formalism.FourierDecayAlt.P.NormalFormRelations

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr

noncomputable section

variable {P : M.Par}

def Loc (a : MA.A P (MA.DQ P)) : Prop :=
  ∀ (U : Set (MA.E P.r)), IsOpen U → ∀ f : M.Ty P → MA.SmQ P.r P.TT,
    (∀ ρ (q : MA.Qp P.r P.TT), q.1 ∈ U → MA.evQ P (f ρ) q = 0) →
    ∀ ρ (q : MA.Qp P.r P.TT), q.1 ∈ U → MA.evQ P (MA.actA P a f ρ) q = 0

def locAlg (P : M.Par) : Subalgebra ℂ (MA.A P (MA.DQ P)) where
  carrier := {a | Loc a}
  mul_mem' {a b} ha hb U hU f hf := by
    rw [Gauge.actA_mul]; exact ha U hU _ (hb U hU f hf)
  add_mem' {a b} ha hb U hU f hf ρ q hq := by
    rw [Gauge.actA_add]
    show MA.evQ P (MA.actA P a f ρ) q + MA.evQ P (MA.actA P b f ρ) q = 0
    rw [ha U hU f hf ρ q hq, hb U hU f hf ρ q hq, add_zero]
  algebraMap_mem' c U _ f hf ρ q hq := by
    rw [Algebra.algebraMap_eq_smul_one, act_smul, jdh_actA_one]
    show c * MA.evQ P (f ρ) q = 0
    rw [hf ρ q hq, mul_zero]

def evA (q : MA.Qp P.r P.TT) : MA.SmQ P.r P.TT →+ ℂ where
  toFun f := MA.evQ P f q
  map_zero' := rfl
  map_add' _ _ := rfl

theorem loc_central (X : MA.A P (MA.DQ P)) (h : ∀ i j, ∃ z : ℂ, X i j = algebraMap ℂ _ z) : X ∈ locAlg P := by
  intro U _ f hf ρ q hq
  refine (map_sum (evA q) (fun π' => (X ρ π').1 (f π')) Finset.univ).trans (Finset.sum_eq_zero fun π' _ => ?_)
  obtain ⟨z, hz⟩ := h ρ π'
  rw [hz]
  show z * MA.evQ P (f π') q = 0
  rw [hf π' q hq, mul_zero]

theorem loc_fn (g gb : MA.SmQ P.r P.TT) : MA.sc P (MA.DQ P) ((MA.DQ P).fnP g gb) ∈ locAlg P :=
  fun _ _ f hf ρ q hq => by rw [mulBy_fn, hf ρ q hq, mul_zero]

theorem euler_loc (v : M.Var P.r) {U : Set (MA.E P.r)} (hU : IsOpen U) (f : MA.SmQ P.r P.TT)
    (hf : ∀ q : MA.Qp P.r P.TT, q.1 ∈ U → MA.evQ P f q = 0) (q : MA.Qp P.r P.TT) (hq : q.1 ∈ U) :
    MA.evQ P (MA.eulerQ v f) q = 0 := by
  have h0 : MA.ext f.1 =ᶠ[nhds q.1] fun _ => 0 := by
    filter_upwards [hU.mem_nhds hq] with x hx
    unfold MA.ext
    split_ifs with h
    · exact hf ⟨x, h⟩ hx
    · rfl
  show MA.coordE v q.1 * MA.wirt v (MA.ext f.1) q.1 = 0
  simp [MA.wirt, h0.fderiv_eq]

theorem loc_ev (v : M.Var P.r) (Z : (MA.DQ P).Op) :
    MA.sc P (MA.DQ P) ((MA.DQ P).mkP ((MA.DQ P).ev v) Z) ∈ locAlg P := fun U hU f hf ρ q hq => by
  rw [act_sc]; exact euler_loc v hU (f ρ) (hf ρ) q hq

theorem loc_diag_smul (a : M.Ty P → ℂ) (x y : (MA.DQ P).Pr) (hx : MA.sc P (MA.DQ P) x ∈ locAlg P)
    (hy : MA.sc P (MA.DQ P) y ∈ locAlg P) : (Matrix.diagonal fun π => x + a π • y) ∈ locAlg P := by
  have e : (Matrix.diagonal fun π => x + a π • y) =
      MA.sc P (MA.DQ P) x + MA.kap P (MA.DQ P) a * MA.sc P (MA.DQ P) y := by
    rw [kap_diag, MA.sc, MA.sc, Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_add]
    congr 1
  rw [e]
  exact add_mem hx (mul_mem (loc_central _ (kap_central a)) hy)

theorem sc_mul' (x y : (MA.DQ P).Pr) : MA.sc P (MA.DQ P) (x * y) = MA.sc P (MA.DQ P) x * MA.sc P (MA.DQ P) y := by
  simp only [MA.sc, map_mul]

theorem loc_dz (g : MA.SmQ P.r P.TT) (v : M.Var P.r) (Z : (MA.DQ P).Op) :
    MA.sc P (MA.DQ P) ((MA.DQ P).mkP ((MA.DQ P).mulOp g * (MA.DQ P).ev v) Z) ∈ locAlg P := fun U hU f hf ρ q hq => by
  rw [act_sc]
  show MA.evQ P g q * MA.evQ P (MA.eulerQ v (f ρ)) q = 0
  rw [euler_loc v hU (f ρ) (hf ρ) q hq, mul_zero]

variable {L : LevelData (MA.A P (MA.DQ P)) P.r}

theorem loc_fns (hM : MA.IsModelLevel P (MA.DQ P) L) {f : MA.A P (MA.DQ P)} (hf : f ∈ Subring.closure L.fns) :
    f ∈ locAlg P := by
  refine (Subring.closure_le (t := (locAlg P).toSubring)).2 (fun f hf => ?_) hf
  obtain ⟨-, -, hc, hci, hcb, hcbi, hz, hzi, hzb, hzbi, hg, hgi, -⟩ := hM
  simp only [LevelData.fns, Set.mem_union, Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff] at hf
  rcases hf with ((((⟨l, rfl⟩ | ⟨l, rfl⟩) | ⟨l, rfl⟩) | ⟨l, rfl⟩) | h)
  · rw [hc]; exact loc_fn _ _
  · rw [hci]; exact loc_fn _ _
  · rw [hcb]; exact loc_fn _ _
  · rw [hcbi]; exact loc_fn _ _
  · rcases h with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hz]; exact loc_fn _ _
    · rw [hzi]; exact loc_fn _ _
    · rw [hzb]; exact loc_fn _ _
    · rw [hzbi]; exact loc_fn _ _
    · rw [hg]; exact loc_fn _ _
    · rw [hgi]; exact loc_fn _ _

theorem mat_prod_mem {A : Type} [Ring A] [Algebra ℂ A] (B : Subalgebra ℂ A) (l : List (Matrix (Fin 2) (Fin 2) A))
    (h : ∀ X ∈ l, ∀ i j, X i j ∈ B) : ∀ i j, l.prod i j ∈ B := by
  induction l with
  | nil =>
    intro i j
    rw [List.prod_nil, Matrix.one_apply]
    split_ifs
    exacts [B.one_mem, B.zero_mem]
  | cons X l ih =>
    intro i j
    rw [List.prod_cons, Matrix.mul_apply]
    exact B.sum_mem fun k _ => B.mul_mem (h X List.mem_cons_self i k)
      (ih (fun Y hY => h Y (List.mem_cons_of_mem _ hY)) k j)

theorem loc_hat (hM : MA.IsModelLevel P (MA.DQ P) L) {X : MA.A P (MA.DQ P)} (hX : X ∈ hats L) : X ∈ locAlg P := by
  have hp : ∀ l, L.p l ∈ locAlg P := fun l => by rw [hM.1]; exact loc_ev _ _
  have hpb : ∀ l, L.pb l ∈ locAlg P := fun l => by rw [hM.2.1]; exact loc_ev _ _
  have hn : L.nab ∈ locAlg P := by
    rw [hM.2.2.2.2.2.2.2.2.2.2.2.2.1]
    exact loc_diag_smul _ _ _ (loc_dz _ _ _) (by rw [sc_mul']; exact mul_mem (loc_fn _ _) (loc_fn _ _))
  have hns : L.nabs ∈ locAlg P := by
    rw [hM.2.2.2.2.2.2.2.2.2.2.2.2.2.1]
    refine loc_diag_smul _ _ _ ?_ (by rw [sc_mul']; exact mul_mem (loc_fn _ _) (loc_fn _ _))
    rw [MA.sc, map_neg]
    exact neg_mem (loc_dz _ _ _)
  have F := fun {f} (hf : f ∈ Subring.closure L.fns) => loc_fns hM hf
  have hT : ∀ Y i j, L.Tprod Y i j ∈ locAlg P := fun Y => mat_prod_mem _ _ fun X hX i j => by
    obtain ⟨l, rfl⟩ := List.mem_ofFn.1 (List.mem_reverse.1 hX)
    fin_cases i <;> fin_cases j
    · exact add_mem (Subalgebra.algebraMap_mem _ _) (hp l)
    · exact neg_mem (F (clF L (RuleGD.m_c L l)))
    · exact F (clF L (RuleGD.m_ci L l))
    · exact zero_mem _
  have hTv : ∀ Y i j, L.Tvprod Y i j ∈ locAlg P := fun Y => mat_prod_mem _ _ fun X hX i j => by
    obtain ⟨l, rfl⟩ := List.mem_ofFn.1 (List.mem_reverse.1 hX)
    fin_cases i <;> fin_cases j
    · exact sub_mem (Subalgebra.algebraMap_mem _ _) (hpb l)
    · exact neg_mem (F (clF L (RuleGD.m_cb L l)))
    · exact F (clF L (RuleGD.m_cbi L l))
    · exact zero_mem _
  rcases hX with (((⟨y, rfl⟩ | ⟨y, rfl⟩) | ⟨y, rfl⟩) | ⟨y, rfl⟩)
  · exact mul_mem (F (cDr L)) (hT y 0 0)
  · exact mul_mem (mul_mem (F (cDrb L)) (F (cGG L))) (add_mem (mul_mem (sub_mem (neg_mem hn)
      (mul_mem (Subalgebra.algebraMap_mem _ _) (mul_mem (F (cζb L)) (F (cGGi L))))) (hT y 0 0)) (hT y 1 0))
  · exact mul_mem (F (cDrb L)) (hTv y 0 0)
  · exact mul_mem (mul_mem (F (cDr L)) (F (cGG L))) (add_mem (mul_mem (sub_mem (neg_mem hns)
      (mul_mem (Subalgebra.algebraMap_mem _ _) (mul_mem (F (cζ L)) (F (cGGi L))))) (hTv y 0 0)) (hTv y 1 0))

theorem loc_BB (hM : MA.IsModelLevel P (MA.DQ P) L) {b : MA.A P (MA.DQ P)} (hb : b ∈ BB P L) : b ∈ locAlg P := by
  have F := fun {f} (hf : f ∈ Subring.closure L.fns) => loc_fns hM hf
  refine (Algebra.adjoin_le (S := locAlg P) fun x hx => ?_) hb
  rcases hx with (((hx | ⟨g, rfl⟩) | ⟨i, -, rfl⟩) | ⟨i, -, rfl⟩)
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact F (cζi L)
    · exact F (cζbi L)
    · exact mul_mem (F (cD L)) (F (cDbi L))
    · exact mul_mem (F (cDb L)) (F (cDi L))
  · exact loc_central _ (kap_central g)
  · exact mul_mem (mul_mem (F (cDrb L)) (F (cDri L))) (loc_central _ (SS_central i))
  · show star (L.Drb * L.Dri * MA.SS P (MA.DQ P) i) ∈ locAlg P
    obtain ⟨d1, d2⟩ := model_star_D hM
    have d1' : star L.Drb = L.Dr := by rw [← d1, star_star]
    rw [star_mul, star_mul, d2, d1']
    refine mul_mem (loc_central _ fun a b => ?_) (mul_mem (F (cDrbi L)) (F (cDr L)))
    obtain ⟨z, hz⟩ := SS_central (P := P) i b a
    exact ⟨star z, by rw [Matrix.star_apply, hz, algebraMap_star_comm]⟩

theorem loc_nfs (hM : MA.IsModelLevel P (MA.DQ P) L) {n : ℕ} {x : MA.A P (MA.DQ P)}
    (hx : x ∈ NFs L (BB P L) (L.Di ^ n) n) : x ∈ locAlg P := by
  refine (Submodule.span_le (p := Subalgebra.toSubmodule (locAlg P))).2 ?_ hx
  rintro y ⟨b, hb, h, -, hh, rfl⟩
  show _ ∈ locAlg P
  exact mul_mem (mul_mem (loc_BB hM hb) (pow_mem (loc_fns hM (cDi L)) n))
    (list_prod_mem fun a ha => loc_hat hM (hh a ha))

theorem Loc.congr {a : MA.A P (MA.DQ P)} (ha : Loc a) {U : Set (MA.E P.r)} (hU : IsOpen U)
    {f g : M.Ty P → MA.SmQ P.r P.TT} (h : ∀ ρ (q : MA.Qp P.r P.TT), q.1 ∈ U → MA.evQ P (f ρ) q = MA.evQ P (g ρ) q)
    (ρ : M.Ty P) (q : MA.Qp P.r P.TT) (hq : q.1 ∈ U) :
    MA.evQ P (MA.actA P a f ρ) q = MA.evQ P (MA.actA P a g ρ) q := by
  have h0 := ha U hU (f - g) (fun ρ q hq => by
    show MA.evQ P (f ρ) q - MA.evQ P (g ρ) q = 0
    rw [h ρ q hq, sub_self]) ρ q hq
  have e : MA.actA P a f = MA.actA P a (f - g) + MA.actA P a g := by rw [← jdh_actA_addR, sub_add_cancel]
  rw [e]
  show MA.evQ P (MA.actA P a (f - g) ρ) q + _ = _
  rw [h0, zero_add]
  rfl

end

end Formalism.FourierDecayAlt.P.NormalFormRelations
end
end

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.CellSmoothness

section

@[expose] public section

open Matrix MeasureTheory Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.CellSmoothness

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

lemma contDiffOn_gq (D : RealPlaceData k r Wp Wq) : ContDiffOn ℝ ∞ (fun q => gq D q) (QDom k r D.z D.z') := by
  refine Formalism.FourierDecayAlt.P.Ux10.cdm_iff.2 fun i j => ?_
  simp only [gq, bigCell]
  split_ifs with h1 h2 h3 h4 h5
  · exact ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin r => ℂ) (⟨j.val, h1⟩ : Fin r)).comp
      (ContinuousLinearMap.fst ℝ (Fin r → ℂ) ℂ)).contDiff.contDiffOn
  · exact contDiffOn_const
  · exact (D.sec.1 _ _).comp contDiff_snd.contDiffOn (fun q hq => hq.2)
  · exact contDiffOn_const
  · refine ContDiffOn.inv ?_ ?_
    · exact (Complex.conjCLE.contDiff.comp ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin r => ℂ)
        (⟨2 * r + k - j.val, by omega⟩ : Fin r)).comp (ContinuousLinearMap.fst ℝ (Fin r → ℂ) ℂ)).contDiff).contDiffOn
    · intro q hq
      simpa using hq.1 _
  · exact contDiffOn_const

end Formalism.FourierDecayAlt.P.CellSmoothness
end
end
end

-- Source module: CompanionTheory.AutomorphicTheory.JacobiDiagonalBounds.EvQTrJBFF

section

@[expose] public section

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutBP Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.Gauge Formalism.MainStatements.NFTie

namespace Formalism.FourierDecayAlt.P.NormalFormRelations

noncomputable section

def LocLift : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq)
    (J J₀ : B.Mat k r → (Wq →L[ℂ] Wp)) (g₀ : B.Mat k r),
    J ∈ Q.FFl k r Bs.z Bs.z' Bs.π Bs.π' 0 (OmB Bs) → J₀ ∈ Q.FFl k r Bs.z Bs.z' Bs.π Bs.π' 0 (OmB Bs) →
    g₀ ∈ JF.Om k r Bs.z Bs.z' → J₀ g₀ ≠ 0 →
    (∀ H : B.Mat k r → (Wq →L[ℂ] Wp), KB.CptCoef Bs H → B.JF Bs H ∈ Q.FFl k r Bs.z Bs.z' Bs.π Bs.π' 0 (OmB Bs)) →
    ∃ F₁ : B.Mat k r → (Wq →L[ℂ] Wp), KB.CptCoef Bs F₁ ∧ ∃ U : Set (B.Mat k r), IsOpen U ∧ g₀ ∈ U ∧
      ∀ g ∈ U, g ∈ B.GV k r → B.JF Bs F₁ g = J g

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem evQ_trJB_FF (p : KB.Pl P Wp Wq) {e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)} (he : IsFrameB P p.T.base e)
    {J : B.Mat P.k P.r → (Wq →L[ℂ] Wp)} (hJ : J ∈ FFKB p) (ρ : M.Ty P) (q : MA.Qp P.r P.TT) :
    MA.evQ P (trJB P p.T.base e J ρ) q = rawJ P p.T.base e J ρ q := by
  obtain ⟨h1, h2, -⟩ := gauge_transition_chain_holds Wp Wq P p.T.base p.hP p.hl.2.2 J hJ
  have h3 := raw_gauge_smoothness_holds Wp Wq P p.T.base p.hP p.hl.2.2 e he _ _ h1 ρ
  rw [← h2] at h3
  unfold trJB
  rw [toSm_of_mem P h3]
  rfl

theorem qdom (p : KB.Pl P Wp Wq) {x : MA.E P.r} :
    x ∈ MA.Qset P.r P.TT ↔ x ∈ JF.QDom P.k P.r p.T.base.z p.T.base.z' := by
  obtain ⟨_, _, _, h1, h2, _, _⟩ := p.hP
  simp only [MA.Qset, JF.QDom, Set.mem_setOf_eq, M.Par.TT, h1, h2]

theorem thrW_exists (k r m : ℕ) : ∃ A : ℝ, WeakThresholdClauses.WeakDominationThreshold k r A m := by
  refine ⟨6 * r * m + |(r : ℝ) * (4 * r + 2 * k - 1) * (6 * r + 1)| + 1, ?_⟩
  unfold WeakThresholdClauses.WeakDominationThreshold
  have h1 := le_abs_self ((r : ℝ) * (4 * r + 2 * k - 1) * (6 * r + 1))
  have h2 := abs_nonneg ((r : ℝ) * (4 * r + 2 * k - 1) * (6 * r + 1))
  constructor <;> linarith


attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
theorem tie_FF (hLL : LocLift) (p : KB.Pl P Wp Wq) {e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)} (he : IsFrameB P p.T.base e)
    (hG : GaugeQQ P p.T.base e) {Lm : R.LevelData (MA.A P (MA.DQ P)) P.r} (hM : MA.IsModelLevel P (MA.DQ P) Lm)
    {w : List C.Letter} (hw : KB.CutWord P p.l0 w) (a : Wd.Ix (Fin w.length))
    (hloc : Loc (gM P p.l0 Lm (D.positionted w) a)) {Dop : B.DiffOp P.k P.r Wp Wq}
    (hS : B.SmoothCoef (B.GPos p.T.base) Dop) (hC : B.Commutes p.T.base (B.GPos p.T.base) Dop)
    (hΘ : ∀ F, ∀ g ∈ C6.domL p.T.base ∅, p.Θ.Θ w a F g = B.opApply Dop F g)
    {J H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)} (hJ : J ∈ FFKB p)
    (hH : ∀ g ∈ JF.Om P.k P.r p.T.base.z p.T.base.z', B.opApply Dop J g = B.JF p.T.base H g)
    (q : MA.Qp P.r P.TT) (h0 : B.JF p.T.base H (B.gq p.T.base q.1) ≠ 0) (ρ : M.Ty P) :
    rawJ P p.T.base e (B.JF p.T.base H) ρ q =
      MA.evQ P (MA.actA P (gM P p.l0 Lm (D.positionted w) a) (trJB P p.T.base e J) ρ) q := by
  have hom : ∀ q' : MA.Qp P.r P.TT, B.gq p.T.base q'.1 ∈ JF.Om P.k P.r p.T.base.z p.T.base.z' := fun q' =>
    BigCellHermitian.gqDom p.T.base ((qdom p).1 q'.2)
  have hJ0 := jdc_ffl p.T.base Dop hS hJ H hH
  obtain ⟨F₁, hF₁, U, hU, hgU, hag⟩ := hLL P.k P.r Wp Wq p.T.base J _ _ hJ hJ0 (hom q) h0
    fun H hH => jf_cpt_FF p.T.base hH
  obtain ⟨⟨Φ, hΦ⟩, ht⟩ := tie_cpt p he hG hM hw a hF₁
  obtain ⟨A, hA⟩ := thrW_exists P.k P.r (B.opOrder Dop)
  obtain ⟨ε, -, hn⟩ := TLB.nice_of_cpt hF₁
  have e1 : B.JF p.T.base (p.Θ.Θ w a F₁) (B.gq p.T.base q.1) = B.JF p.T.base H (B.gq p.T.base q.1) := by
    have hd : B.gq p.T.base q.1 ∈ C6.domL p.T.base ∅ := by
      rw [nfLeib_domL_eq]; exact jdc_om_sub_gpos _ (hom q)
    rw [PBN.jf_congr_pos p.T.base (hΘ F₁) hd, ← orbital_commutes_on_open_set _ _ _ _ p.T.base A (B.opOrder Dop) F₁ Dop _ subset_rfl
      le_rfl hA (hn.2.1 A _) (fun p' hp' f' hf' g hg => hC p' hp' f' hf' g (jdc_om_sub_gpos _ hg)) _ (hom q),
      JA.LocOp.opApply_congr_GV Dop hU (fun g hg hgU => hag g hgU hg) _ (hom q).1 hgU, hH _ (hom q)]
  have hcont : ContinuousOn (fun x => B.gq p.T.base x) (MA.Qset P.r P.TT) :=
    (CellSmoothness.contDiffOn_gq p.T.base).continuousOn.mono fun x hx => (qdom p).1 hx
  have hV := hcont.isOpen_inter_preimage (MA.Qset_open _ _) hU
  rw [← hloc.congr hV (f := trJB P p.T.base e (B.JF p.T.base F₁)) (fun ρ' q' hq' => ?_) ρ q ⟨q.2, hgU⟩, ← ht,
    evQ_trJB p.hP p.hl.2.2 he hΦ]
  · simp only [rawJ, e1]
  · rw [evQ_trJB_FF p he (jf_cpt_FF p.T.base hF₁), evQ_trJB_FF p he hJ]
    simp only [rawJ, hag _ hq'.2 (hom q').1]

theorem jf_Gpow (p : KB.Pl P Wp Wq) (s : ℕ) {F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)} (hF : B.JF p.T.base F ∈ FFKB p) :
    B.JF p.T.base (fun g => ((Gf P.k P.r p.T.base.z p.T.base.z' g ^ s : ℝ) : ℂ) • F g) ∈ FFKB p := by
  obtain ⟨C₁, h⟩ := empty_operator_list_holds
  obtain ⟨Th₀, Th, -, hTh, hh⟩ := h Wp Wq P p s
  refine jdc_ffl p.T.base Th hTh.1 hF _ fun g _ => ?_
  have h := JCTx2.JF_cutF p.T.base (fun x => x ^ s) F 1 g
  unfold D.cutF at h
  simp only [div_one] at h
  rw [(hh (B.JF p.T.base F) g).2, h]

def PD {E : Type} [AddCommGroup E] [Module ℂ E] (o : ℕ) (f : ℕ → E) : Prop :=
  ∃ a : ℕ → E, ∀ s : ℕ, f s = ∑ n ∈ Finset.range (o + 1), (s : ℂ) ^ n • a n

theorem pd_list {E ι : Type} [AddCommGroup E] [Module ℂ E] {o : ℕ} (l : List ι) (f : ι → ℕ → E)
    (h : ∀ i ∈ l, PD o (f i)) : PD o fun s => (l.map fun i => f i s).sum := by
  induction l with
  | nil => exact ⟨fun _ => 0, fun s => by simp⟩
  | cons i l ih =>
    obtain ⟨a₁, h₁⟩ := h i (by simp)
    obtain ⟨a₂, h₂⟩ := ih (fun j hj => h j (by simp [hj]))
    refine ⟨fun n => a₁ n + a₂ n, fun s => ?_⟩
    simp only [List.map_cons, List.sum_cons, h₁ s, h₂ s, smul_add, Finset.sum_add_distrib]

theorem pd_mono {E : Type} [AddCommGroup E] [Module ℂ E] {o n : ℕ} (hn : n ≤ o) (x : E) :
    PD o fun s => (s : ℂ) ^ n • x := by
  refine ⟨fun m => if m = n then x else 0, fun s => ?_⟩
  simp only [smul_ite, smul_zero]
  rw [Finset.sum_ite_eq' (Finset.range (o + 1)) n, if_pos (Finset.mem_range.2 (by omega))]

theorem scoef_zero (p : KB.Pl P Wp Wq) {w : List C.Letter} {a : Wd.Ix (Fin w.length)} {Q o : ℕ}
    {L : Fin (Q + 1) → B.DiffOp P.k P.r Wp Wq} (hS : IsSCoef p w a Q L) {Dop : B.DiffOp P.k P.r Wp Wq}
    (ho : ∀ T ∈ Dop, T.word.length ≤ o)
    (hΘ : ∀ F, ∀ g ∈ C6.domL p.T.base ∅, p.Θ.Θ w a F g = B.opApply Dop F g)
    {F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)} (hF : B.CkOn ⊤ (B.GV P.k P.r) F) {g : B.Mat P.k P.r}
    (hg : g ∈ C6.domL p.T.base ∅) (qq : Fin (Q + 1)) (hq : o < qq) : B.opApply (L qq) F g = 0 := by
  have hG : 0 < Gf P.k P.r p.T.base.z p.T.base.z' g := hg.2.1
  have hpd : PD o fun s : ℕ => ∑ q : Fin (Q + 1), (s : ℂ) ^ (q : ℕ) • B.opApply (L q) F g := by
    have h1 : PD o fun s : ℕ => (Dop.map fun T => ((Gf P.k P.r p.T.base.z p.T.base.z' g ^ (-(s : ℝ)) : ℝ) : ℂ) •
        T.coef g (B.Rw T.word (fun g' => ((Gf P.k P.r p.T.base.z p.T.base.z' g' ^ (s : ℝ) : ℝ) : ℂ) • F g') g)).sum := by
      refine pd_list _ _ fun T hT => ?_
      obtain ⟨terms, ht, hexp⟩ := leibniz_expansion_holds P.k P.r Wp Wq p.T.base T.word T.word_lie
      have h2 := pd_list (o := o) terms (fun t (s : ℕ) => (s : ℂ) ^ t.1 • T.coef g ((t.2.1 g *
        ((Gf P.k P.r p.T.base.z p.T.base.z' g : ℝ) : ℂ)⁻¹ ^ t.2.2.1) • B.Rw t.2.2.2 F g))
        fun t h => pd_mono (le_trans (ht t h).1 (ho T hT)) _
      convert h2 using 2 with s
      have h3 := hexp _ (nfLeib_thChain_rpow (s : ℝ)) F hF g hg
      simp only [pow_zero, one_mul] at h3
      rw [h3, map_list_sum, List.smul_sum, List.map_map, List.map_map]
      congr 1
      refine List.map_congr_left fun t _ => ?_
      simp only [Function.comp, map_smul, smul_smul]
      congr 1
      have h4 : ((Gf P.k P.r p.T.base.z p.T.base.z' g ^ (-(s : ℝ)) : ℝ) : ℂ) *
          ((Gf P.k P.r p.T.base.z p.T.base.z' g ^ (s : ℝ) : ℝ) : ℂ) = 1 := by
        rw [← Complex.ofReal_mul, ← Real.rpow_add hG, neg_add_cancel, Real.rpow_zero, Complex.ofReal_one]
      push_cast at h4 ⊢
      linear_combination ((s : ℂ) ^ t.1 * (t.2.1 g * ((Gf P.k P.r p.T.base.z p.T.base.z' g : ℝ) : ℂ)⁻¹ ^ t.2.2.1)) * h4
    convert h1 using 2 with s
    have h5 := hS (s : ℝ) F hF g hg
    rw [hΘ _ g hg, B.opApply, List.smul_sum, List.map_map] at h5
    push_cast at h5 ⊢
    exact h5.symm
  obtain ⟨c, hc⟩ := hpd
  beta_reduce at hc
  have key := nf_coef_unique (Q + 1 + (o + 1))
    (fun i => (if h : i < Q + 1 then B.opApply (L ⟨i, h⟩) F g else 0) - (if i < o + 1 then c i else 0))
    (Set.range fun n : ℕ => (n : ℂ)) (Set.infinite_range_of_injective Nat.cast_injective) (by
      rintro _ ⟨s, rfl⟩
      simp only [smul_sub, Finset.sum_sub_distrib]
      rw [nf_sum_pad (by omega) _ fun q => B.opApply (L q) F g, hc s, sub_eq_zero,
        ← Finset.sum_subset (Finset.range_subset_range.2 (show o + 1 ≤ Q + 1 + (o + 1) by omega))]
      · exact Finset.sum_congr rfl fun i hi => by rw [if_pos (Finset.mem_range.1 hi)]
      · intro i _ hi
        rw [if_neg (by simpa using hi), smul_zero]) qq (by omega)
  simpa only [dif_pos qq.2, if_neg (show ¬ (qq : ℕ) < o + 1 by omega), sub_zero] using key

end

end Formalism.FourierDecayAlt.P.NormalFormRelations
end
end
