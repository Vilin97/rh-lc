module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairPtsClasses
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFiniteReproducingOfSubmodule
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairPtsEqSum
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MovFn
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SumProdExpansionFunctionsRowVertexInvariant
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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VecOfEqIntertwiner
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairFnUpdateLinear
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PureTensorLIntertwine
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmPureTensorOOfFinite
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridFiniteDatumVectorThetaFockVacuum
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.SumProdExpansionFunctionsRowVertexInvariantStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.RowVertexInv
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem _root_.GlobalTheory.T.sum_prod_expansion_functions_rowVertex_invariant : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} {Φ : G.Datum} {β : CosFam G t} {τ : PureDat G t →₀ ℂ} {μ₀ : T},
    L.Is μ₀ → (Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q)) → (∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) → t ∈ U → β ∈ S.supp t Φ → S.IsExpansion t Φ β τ → (∀ d ∈ τ.support, (∀ j, S.Z.HasVec (d.1 j)) ∧ ∀ i, S.Z.HasVec (d.2 i)) → ∀ (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m)), finG (G.V (.grid (j + 1) D.R.m)) k ∈ S.levRow t (j + 1) hj.le → ∀ c₁ c₂ : ℂ, W.om (.chi j D.R.m) (G.toPair (.chi j D.R.m) 1 (moved S j k)) (S.Z.vac (.chi j D.R.m)) = c₁ • S.Z.vac (.chi j D.R.m) → W.om (.chi (j + 1) D.R.m) (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1) (S.Z.vac (.chi (j + 1) D.R.m)) = c₂ • S.Z.vac (.chi (j + 1) D.R.m) → ∀ z : ∀ a, WO (G.pS (positionPair t D.R.m a)) (G.pT (positionPair t D.R.m a)), (τ.sum fun d c => c * ∏ a, (scaleAt j hj c₁ c₂ a • movFn S j hj k (fnOf d) a) (z a)) = τ.sum fun d c => c * ∏ a, fnOf d a (z a) := by
  first | exact @GlobalTheory.RowVertexInv.sum_prod_scale_movFn_eq | exact GlobalTheory.RowVertexInv.sum_prod_scale_movFn_eq | (intros; apply GlobalTheory.RowVertexInv.sum_prod_scale_movFn_eq <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExpansionTensorSumInvariantGridRowLevel

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.RowVertexInv
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.RowVertexInv

theorem sum_prod_moveV_eq : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} {Φ : G.Datum} {β : CosFam G t} {τ : PureDat G t →₀ ℂ} {μ₀ : T},
    L.Is μ₀ → (Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q)) → (∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) → t ∈ U → β ∈ S.supp t Φ → S.IsExpansion t Φ β τ → (∀ d ∈ τ.support, (∀ j, S.Z.HasVec (d.1 j)) ∧ ∀ i, S.Z.HasVec (d.2 i)) → ∀ (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m)), finG (G.V (.grid (j + 1) D.R.m)) k ∈ S.levRow t (j + 1) hj.le → ∀ z : ∀ a, WO (G.pS (positionPair t D.R.m a)) (G.pT (positionPair t D.R.m a)), (τ.sum fun d c => c * ∏ a, moveV S j hj k (vecOf S d) a (z a)) = τ.sum fun d c => c * ∏ a, vecOf S d a (z a) := by
  intro D T L sc G W U S t Φ β τ μ₀ hμ hq hQ hU hβ hE hv j hj k hk z
  obtain ⟨c₁, c₂, Tm, h1, h2, hT⟩ := GlobalTheory.RowVertexInv.FactorTheta.vecOf_eq_intertwiner S hE hv j hj k hk
  have hB := GlobalTheory.T.sum_prod_expansion_functions_rowVertex_invariant S hμ hq hQ hU hβ hE hv j hj k hk c₁ c₂ h1 h2
  let M : MultilinearMap (RingHom.id ℂ) (fun a : Fin D.R.m ⊕ Fin D.R.m => ↥(⊤ : Submodule ℂ (FactorFn G t a))) ℂ :=
    (MultilinearMap.mkPiAlgebra ℂ (Fin D.R.m ⊕ Fin D.R.m) ℂ).compLinearMap fun a =>
      (LinearMap.proj (z a)) ∘ₗ Tm a ∘ₗ (⊤ : Submodule ℂ (FactorFn G t a)).subtype
  have key := GlobalTheory.finsupp_sum_multilinear_eq_of_prod_eq (X := fun a => WO (G.pS (positionPair t D.R.m a)) (G.pT (positionPair t D.R.m a)))
    (fun a => ⊤) M τ τ (fun d a => ⟨scaleAt j hj c₁ c₂ a • movFn S j hj k (fnOf d) a, trivial⟩)
    (fun d a => ⟨fnOf d a, trivial⟩) hB
  simp only [smul_eq_mul] at key
  convert key using 1
  · refine Finsupp.sum_congr fun d hd => ?_
    congr 1
    simp only [M, MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply, LinearMap.coe_comp,
      Function.comp_apply, Submodule.coe_subtype, LinearMap.proj_apply]
    exact Finset.prod_congr rfl fun a _ => by rw [(hT d hd a).2]
  · refine Finsupp.sum_congr fun d hd => ?_
    congr 1
    simp only [M, MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply, LinearMap.coe_comp,
      Function.comp_apply, Submodule.coe_subtype, LinearMap.proj_apply]
    exact Finset.prod_congr rfl fun a _ => by rw [(hT d hd a).1]

end GlobalTheory.RowVertexInv
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExpansionTensorSumInvariantGridRowLevelStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.RowVertexInv
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem _root_.GlobalTheory.T.expansionTensorSum_invariant_gridRowLevel : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} {Φ : G.Datum} {β : CosFam G t} {τ : PureDat G t →₀ ℂ} {μ₀ : T},
    L.Is μ₀ → (Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q)) → (∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) → t ∈ U → β ∈ S.supp t Φ → S.IsExpansion t Φ β τ → (∀ d ∈ τ.support, (∀ j, S.Z.HasVec (d.1 j)) ∧ ∀ i, S.Z.HasVec (d.2 i)) → ∀ (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m)), finG (G.V (.grid (j + 1) D.R.m)) k ∈ S.levRow t (j + 1) hj.le → ∀ z : ∀ a, WO (G.pS (positionPair t D.R.m a)) (G.pT (positionPair t D.R.m a)), (τ.sum fun d c => c * ∏ a, moveV S j hj k (vecOf S d) a (z a)) = τ.sum fun d c => c * ∏ a, vecOf S d a (z a) := by
  first | exact @GlobalTheory.RowVertexInv.sum_prod_moveV_eq | exact GlobalTheory.RowVertexInv.sum_prod_moveV_eq | (intros; apply GlobalTheory.RowVertexInv.sum_prod_moveV_eq <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairFnUpdateMoveV

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.RowVertexInv
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section

namespace GlobalTheory.RowVertexInv

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

theorem negGA_mem_GfC_row (V : HSp D) {g : GA D V} (hg : g ∈ GfC V) : negGA V g ∈ GfC (negSp V) := by
  have e : matHom (negSp V) (negGA V g) = matHom V g := Units.ext (mt_negGA V g)
  simp only [GfC, MonoidHom.mem_ker, infHom, MonoidHom.comp_apply] at hg ⊢
  rw [e]
  exact hg

theorem ker_mul_row (W : G.Weil) (p : Pair T) (F : WO (G.pS p) (G.pT p) → ℂ) (g k : GA D (G.V p.small))
    (h k' : GA D (G.V p.big)) : W.ker p F (g * k) (h * k') = W.ker p (W.om p (G.toPair p k k') F) g h := by
  have e : G.toPair p (g * k) (h * k') = G.toPair p g h * G.toPair p k k' := by
    cases p <;> simp [GridData.toPair, map_mul, Prod.ext_iff]
  unfold GridData.Weil.ker
  rw [e]
  simp only [thetaKO, Prod.mk.eta, map_mul, Module.End.mul_apply]

theorem fockComp_mul_row (W : G.Weil) (B : VertexFrames G) (p : Pair T) (hp : p.InRange D.R.m)
    (f : WO (G.pS p) (G.pT p) → ℂ) (hf : IsThetaFunO W.ψ (G.pS p) (G.pT p) f) (x g : FinPt G p.small) (y h : FinPt G p.big) :
    fockComp W B p f (x * g) (y * h) = fockComp W B p (W.om p (G.toPair p g h) f) x y := by
  have hmem : (G.toPair p g h).1 ∈ GfC (G.pS p) ∧ (G.toPair p g h).2 ∈ GfC (G.pT p) := by
    cases p with
    | chi i j => exact ⟨negGA_mem_GfC_row _ h.2, g.2⟩
    | mu t i j => exact ⟨g.2, h.2⟩
    | core i => exact ⟨negGA_mem_GfC_row _ h.2, g.2⟩
    | top t j => exact ⟨g.2, h.2⟩
  have key : ∀ P, W.ker p (fockIn W B p f P) ((x : GA D (G.V p.small)) * (g : GA D (G.V p.small))) ((y : GA D (G.V p.big)) * (h : GA D (G.V p.big))) =
      W.ker p (fockIn W B p (W.om p (G.toPair p g h) f) P) x y := by
    intro P
    rw [ker_mul_row]
    congr 1
    have e := (GlobalTheory.OrientedHeis.om_pureTensorO D W.ψ W.θ _ _ _ _ (W.om p) (W.om_is p hp) W.θ_is
      (G.cartS W.cart p) (G.cartS W.cart p) (G.onS B p) (G.onS B p) (G.onT W.cart p) (G.onT W.cart p) (G.onT B p) (G.onT B p)
      (G.toPair p g h).1 (G.toPair p g h).2
      (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite W.θ τ hmem.1, Matrix.mul_one, Matrix.one_mul])
      (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite W.θ τ hmem.2, Matrix.mul_one, Matrix.one_mul])
      (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite W.θ τ hmem.1, Matrix.one_mul])
      (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite W.θ τ hmem.2, Matrix.one_mul]) f hf P).2
    simp only [Prod.mk.eta] at e
    exact e
  unfold fockComp
  congr 1
  funext k
  exact key _

theorem kkV_mul_big (S : GridChoice W U) (p : Pair T) (hp : p.InRange D.R.m) (f : WO (G.pS p) (G.pT p) → ℂ)
    (hf : IsThetaFunO W.ψ (G.pS p) (G.pT p) f) (a : FinPt G p.small) (b h : FinPt G p.big) :
    kkV S p f a (b * h) =
      kkV S p (W.om p (G.toPair p 1 (((S.N.u p.big)⁻¹ * h * S.N.u p.big : FinPt G p.big) : GA D (G.V p.big))) f) a b := by
  have e := fockComp_mul_row W S.N.frC p hp f hf (a * S.N.u _) 1 (b * S.N.u _) ((S.N.u p.big)⁻¹ * h * S.N.u p.big)
  rw [mul_one, OneMemClass.coe_one] at e
  unfold kkV
  rw [show b * h * S.N.u p.big = b * S.N.u p.big * ((S.N.u p.big)⁻¹ * h * S.N.u p.big) by group, e]

theorem kkV_mul_small (S : GridChoice W U) (p : Pair T) (hp : p.InRange D.R.m) (f : WO (G.pS p) (G.pT p) → ℂ)
    (hf : IsThetaFunO W.ψ (G.pS p) (G.pT p) f) (a g : FinPt G p.small) (b : FinPt G p.big) :
    kkV S p f (a * g) b =
      kkV S p (W.om p (G.toPair p (((S.N.u p.small)⁻¹ * g * S.N.u p.small : FinPt G p.small) : GA D (G.V p.small)) 1) f) a b := by
  have e := fockComp_mul_row W S.N.frC p hp f hf (a * S.N.u _) ((S.N.u p.small)⁻¹ * g * S.N.u p.small) (b * S.N.u _) 1
  rw [mul_one, OneMemClass.coe_one] at e
  unfold kkV
  rw [show a * g * S.N.u p.small = a * S.N.u p.small * ((S.N.u p.small)⁻¹ * g * S.N.u p.small) by group, e]

theorem pairFn_update_moveV (S : GridChoice W U) {t : T} (x : ∀ j, FinPt G (.top j)) (y : ∀ i, FinPt G (.grid i D.R.m))
    (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m)) (v : ∀ a, FactorFn G t a)
    (hv : ∀ a, v a ∈ thetaSub W.ψ (G.pS (positionPair t D.R.m a)) (G.pT (positionPair t D.R.m a))) :
    pairFn S x (Function.update y (j + 1) (y (j + 1) * k)) v = pairFn S x y (moveV S j hj k v) := by
  have e : ∀ (i : ℕ) (h : i < D.R.m), moveV S j hj k v (.inl ⟨i, h⟩) = v (.inl ⟨i, h⟩) := fun i h =>
    (Function.update_of_ne Sum.inl_ne_inr _ _).trans (Function.update_of_ne Sum.inl_ne_inr _ _)
  have hcol : colV S (moveV S j hj k v) x = colV S v x := by
    simp only [colV, e]
  have key : ∀ (i : ℕ) (hi : i < D.R.m),
      kkV S (.chi i D.R.m) (v (.inr ⟨i, hi⟩)) (Function.update y (j + 1) (y (j + 1) * k) i)
        (Function.update y (j + 1) (y (j + 1) * k) (i + 1)) =
      kkV S (.chi i D.R.m) (moveV S j hj k v (.inr ⟨i, hi⟩)) (y i) (y (i + 1)) := by
    intro i hi
    by_cases h1 : i = j
    · subst h1
      rw [Function.update_of_ne (show i ≠ i + 1 by omega), Function.update_self]
      have hm : moveV S i hj k v (.inr ⟨i, hi⟩) =
          W.om (.chi i D.R.m) (G.toPair (.chi i D.R.m) 1 (moved S i k)) (v (.inr ⟨i, hi⟩)) :=
        (Function.update_of_ne (by simp) _ _).trans (Function.update_self _ _ _)
      rw [hm]
      exact kkV_mul_big S (.chi i D.R.m) (show i + 1 ≤ D.R.m ∧ D.R.m ≤ D.R.m from ⟨by omega, le_rfl⟩) _ (hv (.inr ⟨i, hi⟩)) (y i) (y (i + 1)) k
    by_cases h2 : i = j + 1
    · subst h2
      rw [Function.update_self, Function.update_of_ne (show j + 1 + 1 ≠ j + 1 by omega)]
      have hm : moveV S j hj k v (.inr ⟨j + 1, hi⟩) =
          W.om (.chi (j + 1) D.R.m) (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1) (v (.inr ⟨j + 1, hi⟩)) :=
        Function.update_self _ _ _
      rw [hm]
      exact kkV_mul_small S (.chi (j + 1) D.R.m) (show j + 1 + 1 ≤ D.R.m ∧ D.R.m ≤ D.R.m from ⟨by omega, le_rfl⟩) _ (hv (.inr ⟨j + 1, hi⟩))
        (y (j + 1)) k (y (j + 1 + 1))
    · rw [Function.update_of_ne h2, Function.update_of_ne (show i + 1 ≠ j + 1 by omega)]
      have hm : moveV S j hj k v (.inr ⟨i, hi⟩) = v (.inr ⟨i, hi⟩) :=
        (Function.update_of_ne (by simp; omega) _ _).trans (Function.update_of_ne (by simp; omega) _ _)
      rw [hm]
  have hrow : rowV S v (Function.update y (j + 1) (y (j + 1) * k)) = rowV S (moveV S j hj k v) y := by
    simp only [rowV, key]
  rw [pairFn, pairFn, hcol, hrow]

end GlobalTheory.RowVertexInv

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.VecMemThetaSub

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.RowVertexInv
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.RowVertexInv

theorem vec_mem_thetaSub : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) {t : T} {p : Pair T}, DefPair D.R.m p → ∀ d : FinDatum G t p, S.Z.HasVec d →
    S.Z.vec d ∈ thetaSub W.ψ (G.pS p) (G.pT p) := by
  intro D T L sc G W U S t p hp d hv
  exact (GlobalTheory.FockRealVec.vec_theta_fock W S.Z hp d hv).1

end GlobalTheory.RowVertexInv
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExpansionPairingInvariantInnerVertexLevelBis

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.RowVertexInv
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.RowVertexInv

theorem pairPts_update_row : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} {Φ : G.Datum} {β : CosFam G t} {τ : PureDat G t →₀ ℂ} {μ₀ : T},
    L.Is μ₀ → (Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q)) → (∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) → t ∈ U → β ∈ S.supp t Φ → S.IsExpansion t Φ β τ →
    (∀ d ∈ τ.support, (∀ j, S.Z.HasVec (d.1 j)) ∧ ∀ i, S.Z.HasVec (d.2 i)) →
    ∀ (Ψ : FinPt G (.top 0) → VV ℂ (wt G (.top 0))) (F : FinPt G (.grid 0 D.R.m) → VV ℂ (listedWt G (.grid 0 D.R.m))),
    ∀ (x : ∀ j, FinPt G (.top j)) (y : ∀ i, FinPt G (.grid i D.R.m)) (i : ℕ) (hi : 0 < i) (him : i < D.R.m) (k : FinPt G (.grid i D.R.m)),
      finG (G.V (.grid i D.R.m)) k ∈ S.levRow t i him.le →
      pairPts S τ x (Function.update y i (y i * k)) (Ψ (x 0)) (F (Function.update y i (y i * k) 0)) = pairPts S τ x y (Ψ (x 0)) (F (y 0)) := by
  intro D T L sc G W U S t Φ β τ μ₀ hL hq hc hU hβ hτ hv Ψ F x y i hi him k hk
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  have hF : Function.update y (j + 1) (y (j + 1) * k) 0 = y 0 := Function.update_of_ne (by omega) _ _
  rw [hF, pairPts_eq_sum, pairPts_eq_sum]
  have hth : ∀ d ∈ τ.support, ∀ a, vecOf S d a ∈ thetaSub W.ψ (G.pS (positionPair t D.R.m a)) (G.pT (positionPair t D.R.m a)) := by
    intro d hd a
    cases a with
    | inl j' => exact GlobalTheory.RowVertexInv.vec_mem_thetaSub S (p := .top t j') (by show (j' : ℕ) + 1 ≤ D.R.m; omega) _ ((hv d hd).1 j')
    | inr i' => exact GlobalTheory.RowVertexInv.vec_mem_thetaSub S (p := .chi i' D.R.m) ⟨by omega, rfl⟩ _ ((hv d hd).2 i')
  have e1 : (τ.sum fun d c => c • pairFn S x (Function.update y (j + 1) (y (j + 1) * k)) (vecOf S d)) =
      τ.sum fun d c => c • pairFn S x y (moveV S j him k (vecOf S d)) :=
    Finsupp.sum_congr fun d hd => by rw [GlobalTheory.RowVertexInv.pairFn_update_moveV S x y j him k _ (hth d hd)]
  rw [e1]
  have hmv : ∀ d ∈ τ.support, ∀ a, moveV S j him k (vecOf S d) a ∈
      thetaSub W.ψ (G.pS (positionPair t D.R.m a)) (G.pT (positionPair t D.R.m a)) := by
    intro d hd a
    have h1 : (Pair.chi j D.R.m : Pair T).InRange D.R.m := ⟨by omega, le_rfl⟩
    have h2 : (Pair.chi (j + 1) D.R.m : Pair T).InRange D.R.m := ⟨by omega, le_rfl⟩
    have upd : ∀ (P : ∀ a, FactorFn G t a → Prop) (f : ∀ a, FactorFn G t a) (a' : Fin D.R.m ⊕ Fin D.R.m) (v' : FactorFn G t a'),
        (∀ a, P a (f a)) → P a' v' → ∀ a, P a (Function.update f a' v' a) := by
      intro P f a' v' hf hv' a
      by_cases h : a = a'
      · subst h; simpa using hv'
      · rw [Function.update_of_ne h]; exact hf a
    exact upd (fun a f => f ∈ thetaSub W.ψ (G.pS (positionPair t D.R.m a)) (G.pT (positionPair t D.R.m a))) _ _ _
      (upd (fun a f => f ∈ thetaSub W.ψ (G.pS (positionPair t D.R.m a)) (G.pT (positionPair t D.R.m a))) _ _ _ (hth d hd)
        ((W.om_is _ h1).om_pres _ _ (hth d hd (.inr ⟨j, by omega⟩))))
      ((W.om_is _ h2).om_pres _ _ (hth d hd (.inr ⟨j + 1, him⟩))) a
  let V := fun a : Fin D.R.m ⊕ Fin D.R.m => thetaSub W.ψ (G.pS (positionPair t D.R.m a)) (G.pT (positionPair t D.R.m a))
  let M : MultilinearMap (RingHom.id ℂ) (fun a => ↥(V a)) (VV ℂ (wt G (.top 0)) →ₗ[ℂ] VV ℂ (listedWt G (.grid 0 D.R.m)) →ₗ[ℂ] ℂ) :=
    MultilinearMap.mk' (fun v => pairFn S x y fun a => (v a : FactorFn G t a))
      (fun v a f g => by
        have e : ∀ w : V a, (fun b => ((Function.update v a w b : V b) : FactorFn G t b)) =
            Function.update (fun b => (v b : FactorFn G t b)) a (w : FactorFn G t a) := fun w => by
          funext b; exact Function.apply_update (fun b (w : V b) => (w : FactorFn G t b)) v a w b
        simp only [e, Submodule.coe_add]
        exact (GlobalTheory.RowVertexInv.pairFn_update_linear S x y _ (fun b => (v b).2) a f g f.2 g.2).1)
      (fun v a c f => by
        have e : ∀ w : V a, (fun b => ((Function.update v a w b : V b) : FactorFn G t b)) =
            Function.update (fun b => (v b : FactorFn G t b)) a (w : FactorFn G t a) := fun w => by
          funext b; exact Function.apply_update (fun b (w : V b) => (w : FactorFn G t b)) v a w b
        simp only [e, Submodule.coe_smul]
        exact (GlobalTheory.RowVertexInv.pairFn_update_linear S x y _ (fun b => (v b).2) a f f f.2 f.2).2 c)
  classical
  let φ : PureDat G t → ∀ a, V a := fun d =>
    if hd : d ∈ τ.support then fun a => ⟨moveV S j him k (vecOf S d) a, hmv d hd a⟩ else 0
  let φ' : PureDat G t → ∀ a, V a := fun d => if hd : d ∈ τ.support then fun a => ⟨vecOf S d a, hth d hd a⟩ else 0
  have key := GlobalTheory.finsupp_sum_multilinear_eq_of_prod_eq V M τ τ φ φ' (fun z => by
    refine (Finsupp.sum_congr fun d hd => ?_).trans ((GlobalTheory.T.expansionTensorSum_invariant_gridRowLevel S hL hq hc hU hβ hτ hv j him k hk z).trans (Finsupp.sum_congr fun d hd => ?_))
    · simp only [φ, dif_pos hd]
    · simp only [φ', dif_pos hd])
  have l1 : (τ.sum fun d c => c • pairFn S x y (moveV S j him k (vecOf S d))) = τ.sum fun d c => c • M (φ d) :=
    Finsupp.sum_congr fun d hd => by simp only [M, φ, dif_pos hd, MultilinearMap.mk'_apply]
  have l2 : (τ.sum fun d c => c • pairFn S x y (vecOf S d)) = τ.sum fun d c => c • M (φ' d) :=
    Finsupp.sum_congr fun d hd => by simp only [M, φ', dif_pos hd, MultilinearMap.mk'_apply]
  rw [l1, l2, key]

end GlobalTheory.RowVertexInv
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExpansionPairingInvariantInnerVertexLevelTer

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem _root_.GlobalTheory.T.expansionPairing_invariant_innerVertex_level : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} {Φ : G.Datum} {β : CosFam G t} {τ : PureDat G t →₀ ℂ} {μ₀ : T},
    L.Is μ₀ → (Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q)) → (∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) → t ∈ U → β ∈ S.supp t Φ → S.IsExpansion t Φ β τ →
    (∀ d ∈ τ.support, (∀ j, S.Z.HasVec (d.1 j)) ∧ ∀ i, S.Z.HasVec (d.2 i)) →
    ∀ (Ψ : FinPt G (.top 0) → VV ℂ (wt G (.top 0))) (F : FinPt G (.grid 0 D.R.m) → VV ℂ (listedWt G (.grid 0 D.R.m))),
    ∀ (x : ∀ j, FinPt G (.top j)) (y : ∀ i, FinPt G (.grid i D.R.m)) (i : ℕ) (hi : 0 < i) (him : i < D.R.m) (k : FinPt G (.grid i D.R.m)),
      finG (G.V (.grid i D.R.m)) k ∈ S.levRow t i him.le →
      pairPts S τ x (Function.update y i (y i * k)) (Ψ (x 0)) (F (Function.update y i (y i * k) 0)) = pairPts S τ x y (Ψ (x 0)) (F (y 0)) := by
  first | exact @GlobalTheory.RowVertexInv.pairPts_update_row | exact GlobalTheory.RowVertexInv.pairPts_update_row | (intros; apply GlobalTheory.RowVertexInv.pairPts_update_row <;> assumption)
end
end
