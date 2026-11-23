module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ColMapEqColMapV
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExpansionProductInvariantInnerVertexLevelStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfLintegralEqZero
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.KerDiag
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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairPtsClasses
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairPtsEqSum
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairPtsEq
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultilinearSumEqOfFunctionProductSumsEq
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalizedKernelOfVectorAdd
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmPureTensorOOfFinite
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLowestKTypeFockMapThetaVectors
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockCompTranslate

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.FockTranslate

theorem compAt_fin {D : D7} (θ : InfFam D) (τ : D.what₂.Tau) {V : HSp D} (g : GA D V) (hg : g ∈ Formalism.L2.Theta.GfC V) :
    Formalism.IndefR.Datum.compAt θ τ (Formalism.L2.Theta.mt V g) = 1 := by
  have h6 : (Formalism.L2.Theta.mt V g).map (Formalism.L2.Theta.infPart D) = 1 :=
    congrArg Units.val (show Formalism.L2.Theta.infHom V g = 1 from hg)
  unfold Formalism.IndefR.Datum.compAt
  rw [show (Formalism.L2.Theta.mt V g).map (fun a => θ τ (Formalism.L2.Theta.infPart D a)) =
    ((Formalism.L2.Theta.mt V g).map (Formalism.L2.Theta.infPart D)).map (θ τ) from (Matrix.map_map).symm, h6]
  exact Matrix.map_one _ (θ τ).map_zero (θ τ).map_one

theorem fockComp_translate : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (B : VertexFrames G) (t : T) (j : ℕ),
    j + 1 ≤ D.R.m → ∀ (f : WO (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T)) → ℂ),
    IsThetaFunO W.ψ (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T)) f →
    ∀ (a k₁ : FinPt G (.top j)) (b k₂ : FinPt G (.top (j + 1))),
      fockComp W B (.top t j) f (a * k₁) (b * k₂) =
        fockComp W B (.top t j) (W.om (.top t j) ((k₁ : GA D (G.V (.top j))), (k₂ : GA D (G.V (.top (j + 1))))) f) a b := by
  intro D T L sc G W B t j hj f hf a k₁ b k₂
  have hom := W.om_is (.top t j) hj
  have hcomm : ∀ P, W.om (.top t j) ((k₁ : GA D (G.V (.top j))), (k₂ : GA D (G.V (.top (j + 1)))))
      (fockIn W B (.top t j) f P) = fockIn W B (.top t j) (W.om (.top t j) ((k₁ : GA D (G.V (.top j))), (k₂ : GA D (G.V (.top (j + 1))))) f) P := by
    intro P
    unfold fockIn
    refine Formalism.IndefR.Eqv.KerDiag.comm_pureTensorO W.ψ_std W.θ W.θ_is _ _ _ _ _ (fun τ z g hg => ?_) hf P
    rw [GlobalTheory.OrientedHeis.om_dRho hom W.θ_is _ _ τ z hg, compAt_fin W.θ τ _ k₂.2, compAt_fin W.θ τ _ (inv_mem k₁.2),
      Matrix.one_mul, Matrix.mul_one]
  unfold fockComp
  congr 1
  funext M
  unfold jetTab kerFin GridData.Weil.ker
  simp only [GridData.toPair, thetaKO, Subgroup.coe_mul]
  rw [show ((a : GA D (G.V (.top j))) * k₁, (b : GA D (G.V (.top (j + 1)))) * k₂) =
    ((a : GA D (G.V (.top j))), (b : GA D (G.V (.top (j + 1))))) * ((k₁ : GA D (G.V (.top j))), (k₂ : GA D (G.V (.top (j + 1))))) from rfl,
    map_mul, Module.End.mul_apply, hcomm]

end GlobalTheory.FockTranslate

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairVEqOfProdFunEq

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.ExpansionInvariance

theorem chainTo_congr_lt {V : ℕ → Type} [∀ j, AddCommGroup (V j)] [∀ j, Module ℂ (V j)]
    {k k' : ∀ j, V j →ₗ[ℂ] V (j + 1)} : ∀ n, (∀ j, j < n → k j = k' j) → chainTo k n = chainTo k' n
  | 0, _ => rfl
  | n + 1, h => by
    show k n ∘ₗ chainTo k n = k' n ∘ₗ chainTo k' n
    rw [h n n.lt_succ_self, chainTo_congr_lt n fun j hj => h j (by omega)]

theorem chainTo_add_at {V : ℕ → Type} [∀ j, AddCommGroup (V j)] [∀ j, Module ℂ (V j)]
    {k₁ k₂ k₃ : ∀ j, V j →ₗ[ℂ] V (j + 1)} (j₀ : ℕ) (h₂ : ∀ j, j ≠ j₀ → k₂ j = k₁ j) (h₃ : ∀ j, j ≠ j₀ → k₃ j = k₁ j)
    (h : k₁ j₀ = k₂ j₀ + k₃ j₀) : ∀ n, j₀ < n → chainTo k₁ n = chainTo k₂ n + chainTo k₃ n
  | 0, hn => absurd hn (Nat.not_lt_zero _)
  | n + 1, hn => by
    show k₁ n ∘ₗ chainTo k₁ n = k₂ n ∘ₗ chainTo k₂ n + k₃ n ∘ₗ chainTo k₃ n
    rcases Nat.lt_succ_iff_lt_or_eq.mp hn with h' | h'
    · rw [chainTo_add_at j₀ h₂ h₃ h n h', h₂ n (by omega), h₃ n (by omega), LinearMap.comp_add]
    · subst h'
      rw [chainTo_congr_lt (k := k₂) (k' := k₁) j₀ (fun j hj => h₂ j (by omega)),
        chainTo_congr_lt (k := k₃) (k' := k₁) j₀ (fun j hj => h₃ j (by omega)), h, LinearMap.add_comp]

theorem chainTo_smul_at {V : ℕ → Type} [∀ j, AddCommGroup (V j)] [∀ j, Module ℂ (V j)]
    {k₁ k₂ : ∀ j, V j →ₗ[ℂ] V (j + 1)} (j₀ : ℕ) (a : ℂ) (h₂ : ∀ j, j ≠ j₀ → k₂ j = k₁ j)
    (h : k₁ j₀ = a • k₂ j₀) : ∀ n, j₀ < n → chainTo k₁ n = a • chainTo k₂ n
  | 0, hn => absurd hn (Nat.not_lt_zero _)
  | n + 1, hn => by
    show k₁ n ∘ₗ chainTo k₁ n = a • (k₂ n ∘ₗ chainTo k₂ n)
    rcases Nat.lt_succ_iff_lt_or_eq.mp hn with h' | h'
    · rw [chainTo_smul_at j₀ a h₂ h n h', h₂ n (by omega), LinearMap.comp_smul]
    · subst h'
      rw [chainTo_congr_lt (k := k₂) (k' := k₁) j₀ (fun j hj => h₂ j (by omega)), h, LinearMap.smul_comp]

theorem jetOp_mul_tab {K : Type} [Field K] {ι : Type} [Fintype ι] {a b : ℕ} (lam : ι → DomWeight a)
    (lam' : ι → DomWeight b) (c : K) (J : (Formalism.L2.Ker.DVar ι a b →₀ ℕ) → K) (n : ι → ℕ) :
    Formalism.L2.Ker.jetOp lam lam' (fun k => c * J k) n = c • Formalism.L2.Ker.jetOp lam lam' J n := by
  have e : Formalism.L2.Ker.jetLin (fun k => c * J k) = c • Formalism.L2.Ker.jetLin J := by
    refine (MvPolynomial.basisMonomials ((ι × Fin b × Fin b) ⊕ Formalism.L2.Ker.DVar ι a b) K).ext fun m => ?_
    simp only [Formalism.L2.Ker.jetLin, LinearMap.smul_apply, Module.Basis.constr_basis, MvPolynomial.smul_monomial,
      smul_eq_mul]
  ext1 P
  simp only [Formalism.L2.Ker.jetOp, Formalism.L2.Ker.jetMap, e, LinearMap.comp_apply, LinearMap.smul_apply, map_smul]

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

theorem kkVec_smul (S : GridChoice W U) (p : Pair T) (a : ℂ) (f : WO (G.pS p) (G.pT p) → ℂ) (x : FinPt G p.small)
    (y : FinPt G p.big) : GlobalTheory.TopZeroInv.kkVec S p (a • f) x y = a • GlobalTheory.TopZeroInv.kkVec S p f x y := by
  have hJ : ∀ x' y', jetTab W S.N.frC p (a • f) x' y' = fun k => a * jetTab W S.N.frC p f x' y' k := by
    intro x' y'
    funext k
    simp only [jetTab, kerFin, fockIn, GlobalTheory.FiniteFock.pureTensorO_smul, GridData.Weil.ker, thetaKO, map_smul,
      Pi.smul_apply, smul_eq_mul]
  unfold GlobalTheory.TopZeroInv.kkVec fockComp
  rw [hJ, jetOp_mul_tab, smul_comm]

def colML (S : GridChoice W U) (t : T) (x : ∀ j, FinPt G (.top j)) :
    MultilinearMap (RingHom.id ℂ) (fun j : Fin D.R.m => ↥(GlobalTheory.RowVertexInv.thetaSub W.ψ (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T))))
      (VV ℂ (wt G (.top 0)) →ₗ[ℂ] VV ℂ (wt G (.top D.R.m))) where
  toFun cc := colMapV S t (fun j => (cc j : WO _ _ → ℂ)) x
  map_update_add' := by
    intro _ cc j₀ a b
    unfold colMapV
    rw [← LinearMap.add_comp]
    congr 1
    refine chainTo_add_at j₀.1 ?_ ?_ ?_ D.R.m j₀.2
    · intro j hj
      dsimp only
      split_ifs with h
      · have hne : (⟨j, h⟩ : Fin D.R.m) ≠ j₀ := fun e => hj (congrArg Fin.val e)
        simp only [Function.update_of_ne hne]
      · rfl
    · intro j hj
      dsimp only
      split_ifs with h
      · have hne : (⟨j, h⟩ : Fin D.R.m) ≠ j₀ := fun e => hj (congrArg Fin.val e)
        simp only [Function.update_of_ne hne]
      · rfl
    · simp only [dif_pos j₀.2, Fin.eta, Function.update_self, Submodule.coe_add]
      exact GlobalTheory.TopZeroInv.kkVec_add S _ a.2 b.2 _ _
  map_update_smul' := by
    intro _ cc j₀ c a
    unfold colMapV
    rw [← LinearMap.smul_comp]
    congr 1
    refine chainTo_smul_at j₀.1 c ?_ ?_ D.R.m j₀.2
    · intro j hj
      dsimp only
      split_ifs with h
      · have hne : (⟨j, h⟩ : Fin D.R.m) ≠ j₀ := fun e => hj (congrArg Fin.val e)
        simp only [Function.update_of_ne hne]
      · rfl
    · simp only [dif_pos j₀.2, Fin.eta, Function.update_self, Submodule.coe_smul]
      exact kkVec_smul S _ c _ _ _

def rowML (S : GridChoice W U) (t : T) (y : ∀ i, FinPt G (.grid i D.R.m)) :
    MultilinearMap (RingHom.id ℂ) (fun i : Fin D.R.m => ↥(GlobalTheory.RowVertexInv.thetaSub W.ψ (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))))
      (VV ℂ (listedWt G (.grid 0 D.R.m)) →ₗ[ℂ] VV ℂ (wt G (.grid D.R.m D.R.m))) where
  toFun rr := rowMapV S (fun i => (rr i : WO _ _ → ℂ)) y
  map_update_add' := by
    intro _ rr i₀ a b
    unfold rowMapV
    rw [← LinearMap.add_comp]
    congr 1
    refine chainTo_add_at i₀.1 ?_ ?_ ?_ D.R.m i₀.2
    · intro i hi
      dsimp only
      split_ifs with h
      · have hne : (⟨i, h⟩ : Fin D.R.m) ≠ i₀ := fun e => hi (congrArg Fin.val e)
        simp only [Function.update_of_ne hne]
      · rfl
    · intro i hi
      dsimp only
      split_ifs with h
      · have hne : (⟨i, h⟩ : Fin D.R.m) ≠ i₀ := fun e => hi (congrArg Fin.val e)
        simp only [Function.update_of_ne hne]
      · rfl
    · simp only [dif_pos i₀.2, Fin.eta, Function.update_self, Submodule.coe_add]
      exact GlobalTheory.TopZeroInv.kkVec_add S _ a.2 b.2 _ _
  map_update_smul' := by
    intro _ rr i₀ c a
    unfold rowMapV
    rw [← LinearMap.smul_comp]
    congr 1
    refine chainTo_smul_at i₀.1 c ?_ ?_ D.R.m i₀.2
    · intro i hi
      dsimp only
      split_ifs with h
      · have hne : (⟨i, h⟩ : Fin D.R.m) ≠ i₀ := fun e => hi (congrArg Fin.val e)
        simp only [Function.update_of_ne hne]
      · rfl
    · simp only [dif_pos i₀.2, Fin.eta, Function.update_self, Submodule.coe_smul]
      exact kkVec_smul S _ c _ _ _

def pairRowL (S : GridChoice W U) (t : T) (y : ∀ i, FinPt G (.grid i D.R.m)) (u : VV ℂ (wt G (.top 0)))
    (v : VV ℂ (listedWt G (.grid 0 D.R.m))) :
    (VV ℂ (wt G (.top 0)) →ₗ[ℂ] VV ℂ (wt G (.top D.R.m))) →ₗ[ℂ]
      MultilinearMap (RingHom.id ℂ) (fun i : Fin D.R.m => ↥(GlobalTheory.RowVertexInv.thetaSub W.ψ (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)))) ℂ where
  toFun A := ((brPair (listedWt G (.grid D.R.m D.R.m)) G.sp.topDec.rank.symm (wt G (.top D.R.m)) (A u)).comp
    (LinearMap.applyₗ v)).compMultilinearMap (rowML S t y)
  map_add' A B := by
    ext rr
    simp only [LinearMap.add_apply, map_add (f := _), LinearMap.add_comp, MultilinearMap.add_apply]
    rfl
  map_smul' c A := by
    ext rr
    simp only [LinearMap.smul_apply, map_smul, LinearMap.smul_comp, MultilinearMap.smul_apply, RingHom.id_apply]
    rfl

def pairML (S : GridChoice W U) (t : T) (x : ∀ j, FinPt G (.top j)) (y : ∀ i, FinPt G (.grid i D.R.m))
    (u : VV ℂ (wt G (.top 0))) (v : VV ℂ (listedWt G (.grid 0 D.R.m))) :
    MultilinearMap (RingHom.id ℂ) (fun j : Fin D.R.m => ↥(GlobalTheory.RowVertexInv.thetaSub W.ψ (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T))))
      (MultilinearMap (RingHom.id ℂ) (fun i : Fin D.R.m => ↥(GlobalTheory.RowVertexInv.thetaSub W.ψ (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)))) ℂ) :=
  (pairRowL S t y u v).compMultilinearMap (colML S t x)

theorem pairML_apply (S : GridChoice W U) (t : T) (x : ∀ j, FinPt G (.top j)) (y : ∀ i, FinPt G (.grid i D.R.m))
    (u : VV ℂ (wt G (.top 0))) (v : VV ℂ (listedWt G (.grid 0 D.R.m))) (cc rr) :
    pairML S t x y u v cc rr = (brPair (listedWt G (.grid D.R.m D.R.m)) G.sp.topDec.rank.symm (wt G (.top D.R.m))).compl₁₂
      (colMapV S t (fun j => (cc j : WO _ _ → ℂ)) x) (rowMapV S (fun i => (rr i : WO _ _ → ℂ)) y) u v := rfl

theorem pairV_eq_of_prodFun_eq : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) (t : T)
    {δ : Type} (τ : δ →₀ ℂ) (c c' : δ → ∀ j : Fin D.R.m, WO (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T)) → ℂ)
    (r r' : δ → ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) → ℂ),
    (∀ d ∈ τ.support, ∀ j : Fin D.R.m, IsThetaFunO W.ψ (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T)) (c d j) ∧
      IsThetaFunO W.ψ (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T)) (c' d j)) →
    (∀ d ∈ τ.support, ∀ i : Fin D.R.m, IsThetaFunO W.ψ (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) (r d i) ∧
      IsThetaFunO W.ψ (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) (r' d i)) →
    (∀ (w : ∀ j : Fin D.R.m, WO (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T)))
      (z : ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))),
      (τ.sum fun d a => a * (∏ j, c d j (w j)) * ∏ i, r d i (z i)) = τ.sum fun d a => a * (∏ j, c' d j (w j)) * ∏ i, r' d i (z i)) →
    ∀ x y, pairV S t τ c r x y = pairV S t τ c' r' x y := by
  intro D T L sc G W U S t δ τ c c' r r' hc hr hprod x y
  classical
  refine LinearMap.ext fun u => LinearMap.ext fun v => ?_
  let f : δ → ∀ j : Fin D.R.m, ↥(GlobalTheory.RowVertexInv.thetaSub W.ψ (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T))) :=
    fun d j => if h : d ∈ τ.support then ⟨c d j, (hc d h j).1⟩ else 0
  let f' : δ → ∀ j : Fin D.R.m, ↥(GlobalTheory.RowVertexInv.thetaSub W.ψ (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T))) :=
    fun d j => if h : d ∈ τ.support then ⟨c' d j, (hc d h j).2⟩ else 0
  let g : δ → ∀ i : Fin D.R.m, ↥(GlobalTheory.RowVertexInv.thetaSub W.ψ (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))) :=
    fun d i => if h : d ∈ τ.support then ⟨r d i, (hr d h i).1⟩ else 0
  let g' : δ → ∀ i : Fin D.R.m, ↥(GlobalTheory.RowVertexInv.thetaSub W.ψ (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))) :=
    fun d i => if h : d ∈ τ.support then ⟨r' d i, (hr d h i).2⟩ else 0
  have ef : ∀ d ∈ τ.support, (fun j => (f d j : WO _ _ → ℂ)) = c d := fun d hd => funext fun j => by simp only [f, dif_pos hd]
  have ef' : ∀ d ∈ τ.support, (fun j => (f' d j : WO _ _ → ℂ)) = c' d := fun d hd => funext fun j => by simp only [f', dif_pos hd]
  have eg : ∀ d ∈ τ.support, (fun i => (g d i : WO _ _ → ℂ)) = r d := fun d hd => funext fun i => by simp only [g, dif_pos hd]
  have eg' : ∀ d ∈ τ.support, (fun i => (g' d i : WO _ _ → ℂ)) = r' d := fun d hd => funext fun i => by simp only [g', dif_pos hd]
  have key := GlobalTheory.funProd_multilinear_sum_eq (pairML S t x y u v) τ f f' g g' (fun w z => by
    rw [Finsupp.sum, Finsupp.sum]
    have h1 := hprod w z
    rw [Finsupp.sum, Finsupp.sum] at h1
    refine (Finset.sum_congr rfl fun d hd => ?_).trans (h1.trans (Finset.sum_congr rfl fun d hd => ?_))
    · rw [← ef d hd, ← eg d hd]
    · rw [← ef' d hd, ← eg' d hd])
  have hL : ∀ (cc : δ → ∀ j : Fin D.R.m, WO (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T)) → ℂ)
      (rr : δ → ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) → ℂ)
      (F : δ → ∀ j : Fin D.R.m, ↥(GlobalTheory.RowVertexInv.thetaSub W.ψ (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T))))
      (H : δ → ∀ i : Fin D.R.m, ↥(GlobalTheory.RowVertexInv.thetaSub W.ψ (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)))),
      (∀ d ∈ τ.support, (fun j => (F d j : WO _ _ → ℂ)) = cc d) → (∀ d ∈ τ.support, (fun i => (H d i : WO _ _ → ℂ)) = rr d) →
      pairV S t τ cc rr x y u v = τ.sum fun d a => a * pairML S t x y u v (F d) (H d) := by
    intro cc rr F H hF hH
    unfold pairV
    rw [Finsupp.sum, Finsupp.sum, LinearMap.sum_apply, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun d hd => ?_
    rw [LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul, pairML_apply, hF d hd, hH d hd]
  rw [hL c r f g ef eg, hL c' r' f' g' ef' eg']
  exact key

end GlobalTheory.ExpansionInvariance

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.VecIsThetaFunOAlt

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.VecThetaDef

theorem vec_isThetaFunO : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} {N : Std G U} (Z : Normal W N)
    {t : T} {p : Pair T} (d : FinDatum G t p), DefPair D.R.m p → p.InRange D.R.m → Z.HasVec d →
    IsThetaFunO W.ψ (G.pS p) (G.pT p) (Z.vec d) := by
  intro D T L sc G W U N Z t p d hp hIn h
  obtain ⟨f, hf⟩ := h
  rw [Normal.vec, FinDatum.vec_eq W hf]
  exact (W.om_is p hIn).om_pres _ _
    (GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt W.ψ_std W.θ_is hf (Z.vac_is p hp).2.theta)

end GlobalTheory.VecThetaDef
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExpansionPairingInvariantInnerVertexLevel

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.ExpansionInvariance


variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} in
theorem colMapV_congr (S : GridChoice W U) (t : T)
    (v v' : ∀ j : Fin D.R.m, WO (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T)) → ℂ) (x x' : ∀ j, FinPt G (.top j))
    (h : ∀ j (hj : j < D.R.m), fockComp W S.N.frC (.top t j) (v ⟨j, hj⟩) (x j * S.N.u _) (x (j + 1) * S.N.u _) =
      fockComp W S.N.frC (.top t j) (v' ⟨j, hj⟩) (x' j * S.N.u _) (x' (j + 1) * S.N.u _)) :
    colMapV S t v x = colMapV S t v' x' := by
  have e : (fun j => if hj : j < D.R.m then S.Z.scal 1 (.top t j) •
      fockComp W S.N.frC (.top t j) (v ⟨j, hj⟩) (x j * S.N.u _) (x (j + 1) * S.N.u _) else 0) =
      (fun j => if hj : j < D.R.m then S.Z.scal 1 (.top t j) •
      fockComp W S.N.frC (.top t j) (v' ⟨j, hj⟩) (x' j * S.N.u _) (x' (j + 1) * S.N.u _) else 0) := by
    funext j
    by_cases hj : j < D.R.m
    · rw [dite_eq_left hj, dite_eq_left hj, h j hj]
    · rw [dite_eq_right hj, dite_eq_right hj]
  unfold colMapV
  rw [e]

theorem pairPts_update_top : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} {Φ : G.Datum} {β : CosFam G t} {τ : PureDat G t →₀ ℂ} {μ₀ : T},
    L.Is μ₀ → (Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q)) → (∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) → t ∈ U → β ∈ S.supp t Φ → S.IsExpansion t Φ β τ →
    (∀ d ∈ τ.support, (∀ j, S.Z.HasVec (d.1 j)) ∧ ∀ i, S.Z.HasVec (d.2 i)) →
    ∀ (Ψ : FinPt G (.top 0) → VV ℂ (wt G (.top 0))) (F : FinPt G (.grid 0 D.R.m) → VV ℂ (listedWt G (.grid 0 D.R.m))),
    ∀ (x : ∀ j, FinPt G (.top j)) (y : ∀ i, FinPt G (.grid i D.R.m)) (j : ℕ) (hj : 0 < j) (hjm : j < D.R.m) (k : FinPt G (.top j)),
      finG (G.V (.top j)) k ∈ S.levTop t Φ β j hjm →
      pairPts S τ (Function.update x j (x j * k)) y (Ψ (Function.update x j (x j * k) 0)) (F (y 0)) = pairPts S τ x y (Ψ (x 0)) (F (y 0)) := by
  intro D T L sc G W U S t Φ β τ μ₀ hL hde hc ht hβ hτ hv Ψ F x y j hj hjm k hk
  obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  have hx0 : Function.update x (j + 1) (x (j + 1) * k) 0 = x 0 := Function.update_of_ne (by omega) _ _
  rw [hx0, pairPts_eq_pairV, pairPts_eq_pairV]
  set u := S.N.u (.top (j + 1)) with hu
  set g : FinPt G (.top (j + 1)) := u⁻¹ * k * u with hg
  have thv : ∀ d ∈ τ.support, ∀ j' : Fin D.R.m, IsThetaFunO W.ψ (G.pS (.top t j' : Pair T)) (G.pT (.top t j' : Pair T)) (S.Z.vec (d.1 j')) :=
    fun d hd j' => GlobalTheory.VecThetaDef.vec_isThetaFunO S.Z (d.1 j') (show j'.1 + 1 ≤ D.R.m by omega) (by simp [Pair.InRange, Node.InRange]; try omega) ((hv d hd).1 j')
  have hcol : ∀ d ∈ τ.support, colMapV S t (fun j' => S.Z.vec (d.1 j')) (Function.update x (j + 1) (x (j + 1) * k)) =
      colMapV S t (movedCol S d j hjm g) x := by
    intro d hd
    refine colMapV_congr S t _ _ _ _ fun j' hj' => ?_
    by_cases h1 : j = j'
    · subst h1
      have hA := GlobalTheory.FockTranslate.fockComp_translate W S.N.frC t j (by omega) _ (thv d hd ⟨j, hj'⟩) (x j * S.N.u _) 1 (x (j + 1) * u) g
      rw [mul_one] at hA
      have e1 : x (j + 1) * k * u = x (j + 1) * u * g := by rw [hg]; group
      have m1 : (⟨j, hj'⟩ : Fin D.R.m) ≠ ⟨j + 1, hjm⟩ := by intro h; simp [Fin.ext_iff] at h
      rw [Function.update_of_ne (by omega : j ≠ j + 1), Function.update_self, e1, hA, movedCol,
        Function.update_of_ne m1, Function.update_self]
      try simp only [OneMemClass.coe_one]
      all_goals rfl
    · by_cases h2 : j + 1 = j'
      · subst h2
        have hA := GlobalTheory.FockTranslate.fockComp_translate W S.N.frC t (j + 1) (by omega) _ (thv d hd ⟨j + 1, hj'⟩) (x (j + 1) * u) g (x (j + 1 + 1) * S.N.u _) 1
        rw [mul_one] at hA
        have e1 : x (j + 1) * k * u = x (j + 1) * u * g := by rw [hg]; group
        rw [Function.update_self, Function.update_of_ne (by omega : j + 1 + 1 ≠ j + 1), e1, hA, movedCol, Function.update_self]
        try simp only [OneMemClass.coe_one]
        all_goals rfl
      · have m1 : (⟨j', hj'⟩ : Fin D.R.m) ≠ ⟨j + 1, hjm⟩ := by intro h; simp [Fin.ext_iff] at h; omega
        have m2 : (⟨j', hj'⟩ : Fin D.R.m) ≠ ⟨j, by omega⟩ := by intro h; simp [Fin.ext_iff] at h; omega
        rw [Function.update_of_ne (by omega : j' ≠ j + 1), Function.update_of_ne (by omega : j' + 1 ≠ j + 1), movedCol,
          Function.update_of_ne m1, Function.update_of_ne m2]
  have key : pairV S t τ (fun d j' => S.Z.vec (d.1 j')) (fun d i => S.Z.vec (d.2 i)) (Function.update x (j + 1) (x (j + 1) * k)) y =
      pairV S t τ (fun d => movedCol S d j hjm g) (fun d i => S.Z.vec (d.2 i)) x y := by
    unfold pairV
    refine Finsupp.sum_congr fun d hd => ?_
    rw [hcol d hd]
  rw [key]
  refine congrArg (fun φ => φ (Ψ (x 0)) (F (y 0))) (GlobalTheory.ExpansionInvariance.pairV_eq_of_prodFun_eq S t τ _ _ _ _ ?_ ?_ (GlobalTheory.T.expansion_product_invariant_inner_vertex_level S hL hde hc ht hβ hτ hv j hjm k hk) x y)
  · intro d hd j'
    refine ⟨?_, thv d hd j'⟩
    by_cases h2 : j' = ⟨j + 1, hjm⟩
    · subst h2
      rw [movedCol, Function.update_self]
      exact (W.om_is _ (by simp [Pair.InRange, Node.InRange]; try omega)).om_pres _ _ (thv d hd _)
    · by_cases h1 : j' = ⟨j, by omega⟩
      · subst h1
        rw [movedCol, Function.update_of_ne h2, Function.update_self]
        exact (W.om_is _ (by simp [Pair.InRange, Node.InRange]; try omega)).om_pres _ _ (thv d hd _)
      · rw [movedCol, Function.update_of_ne h2, Function.update_of_ne h1]
        exact thv d hd j'
  · intro d hd i
    have h := GlobalTheory.VecThetaDef.vec_isThetaFunO S.Z (d.2 i) (show i.1 + 1 ≤ D.R.m ∧ D.R.m = D.R.m by omega) (show i.1 + 1 ≤ D.R.m ∧ D.R.m ≤ D.R.m by omega) ((hv d hd).2 i)
    exact ⟨h, h⟩

end GlobalTheory.ExpansionInvariance

end
end
end
