module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairPtsClasses
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowMapVUpdateZero
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowShiftTheta
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsMultilinearColumnRowKernelPairing
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
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Multilinear.Basic
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultilinearSumEqOfFunctionProductSumsEq
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowShiftTheta
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstColumnVectorSumFormula
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowShift0Model
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.LeadingCoefficientTermLawTheta

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsMultilinearColumnRowKernelPairingStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.LastVertexInv
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem _root_.GlobalTheory.T.exists_multilinear_columnRowKernelPairing : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) (t : T) (x : ∀ j, FinPt G (.top j)) (y : ∀ i, FinPt G (.grid i D.R.m)) (Ψ₀ : VV ℂ (wt G (.top 0))) (F₀ : VV ℂ (listedWt G (.grid 0 D.R.m))),
    ∃ M : MultilinearMap (RingHom.id ℂ) (fun j : Fin D.R.m => thSub W (.top t j))
        (MultilinearMap (RingHom.id ℂ) (fun i : Fin D.R.m => thSub W (.chi i D.R.m : Pair T)) ℂ),
      ∀ fs gs, M fs gs = (brPair (listedWt G (.grid D.R.m D.R.m)) G.sp.topDec.rank.symm (wt G (.top D.R.m))).compl₁₂
        (colMapV S (fun j => (fs j : WO (G.pS (.top t j)) (G.pT (.top t j)) → ℂ)) x)
        (rowMapV S (fun i => (gs i : WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) → ℂ)) y) Ψ₀ F₀ := by
  intro D T L sc G W U S t x y Ψ₀ F₀
  have chain {V : ℕ → Type} [∀ j, AddCommGroup (V j)] [∀ j, Module ℂ (V j)] :
      ∀ (m : ℕ) (A : Fin m → Type) [∀ j, AddCommGroup (A j)] [∀ j, Module ℂ (A j)]
        (k : ∀ j : Fin m, A j →ₗ[ℂ] (V j →ₗ[ℂ] V (j + 1))),
        ∃ M : MultilinearMap (RingHom.id ℂ) A (V 0 →ₗ[ℂ] V m), ∀ fs,
          M fs = chainTo (fun j => if h : j < m then k ⟨j, h⟩ (fs ⟨j, h⟩) else 0) m := by
    intro m
    induction m with
    | zero =>
      intro A _ _ k
      exact ⟨MultilinearMap.constOfIsEmpty (RingHom.id ℂ) A LinearMap.id, fun _ => rfl⟩
    | succ m ih =>
      intro A _ _ k
      obtain ⟨M, hM⟩ := ih (fun j => A j.castSucc) (fun j => k j.castSucc)
      let kl : A (Fin.last m) →ₗ[ℂ] (V m →ₗ[ℂ] V (m + 1)) := k (Fin.last m)
      refine ⟨MultilinearMap.uncurryRight
        (((LinearMap.llcomp ℂ (V 0) (V m) (V (m + 1)) ∘ₗ kl).flip).compMultilinearMap M),
        fun fs => ?_⟩
      show kl (fs (Fin.last m)) ∘ₗ M (Fin.init fs) = _ ∘ₗ chainTo _ m
      rw [hM]
      beta_reduce
      rw [dite_eq_left (Nat.lt_succ_self m)]
      congr 1
      refine GlobalTheory.ArrowMultilinear.chainTo_congr m fun j hj => ?_
      rw [dite_eq_left hj, dite_eq_left (Nat.lt_succ_of_lt hj)]
      rfl
  obtain ⟨Mc, hc⟩ := chain (V := fun j => VV ℂ (wt G (.top j))) D.R.m
    (fun j : Fin D.R.m => thSub W (.top t j))
    (fun j => S.Z.scal 1 (.top t j) •
      GlobalTheory.ArrowMultilinear.fockLin W S.N.frC (.top t j)
        (x j * S.N.u _) (x (j + 1) * S.N.u _))
  obtain ⟨Mr, hr⟩ := chain (V := fun i => VV ℂ (wt G (.grid i D.R.m))) D.R.m
    (fun i : Fin D.R.m => thSub W (.chi i D.R.m : Pair T))
    (fun i => S.Z.scal 1 (.chi i D.R.m : Pair T) •
      GlobalTheory.ArrowMultilinear.fockLin W S.N.frC (.chi i D.R.m : Pair T)
        (y i * S.N.u _) (y (i + 1) * S.N.u _))
  let col := (LinearMap.applyₗ (R := ℂ) (rhoVr (tauE D) _ (S.N.fr (.top 0))⁻¹ Ψ₀)).compMultilinearMap Mc
  let row := (LinearMap.applyₗ (R := ℂ)
    (rhoVr (tauE D) _ (S.N.fr (.grid 0 D.R.m))⁻¹ (funOf (listedWt G (.grid 0 D.R.m)) F₀))).compMultilinearMap Mr
  have hcol (fs : ∀ j : Fin D.R.m, thSub W (.top t j)) :
      col fs = colMapV S (t := t) (fun j => (fs j : WO _ _ → ℂ)) x Ψ₀ := by
    show Mc fs _ = _
    rw [hc]
    refine LinearMap.congr_fun (GlobalTheory.ArrowMultilinear.chainTo_congr
      (V := fun j => VV ℂ (wt G (.top j))) D.R.m fun j hj => ?_) _
    exact dite_congr rfl (fun _ => rfl) (fun _ => rfl)
  have hrow (gs : ∀ i : Fin D.R.m, thSub W (.chi i D.R.m : Pair T)) :
      row gs = rowMapV S (fun i => (gs i : WO _ _ → ℂ)) y F₀ := by
    show Mr gs _ = _
    rw [hr]
    refine LinearMap.congr_fun (GlobalTheory.ArrowMultilinear.chainTo_congr
      (V := fun i => VV ℂ (wt G (.grid i D.R.m))) D.R.m fun j hj => ?_) _
    exact dite_congr rfl (fun _ => rfl) (fun _ => rfl)
  let β := brPair (listedWt G (.grid D.R.m D.R.m)) G.sp.topDec.rank.symm (wt G (.top D.R.m))
  let pairWithRow : VV ℂ (wt G (.top D.R.m)) →ₗ[ℂ]
      MultilinearMap (RingHom.id ℂ) (fun i : Fin D.R.m => thSub W (.chi i D.R.m : Pair T)) ℂ :=
    { toFun := fun v => (β v).compMultilinearMap row
      map_add' := fun v v' => by
        ext gs
        change β (v + v') (row gs) = β v (row gs) + β v' (row gs)
        simp only [map_add]
        rfl
      map_smul' := fun c v => by
        ext gs
        change β (c • v) (row gs) = c • β v (row gs)
        simp only [map_smul]
        rfl }
  refine ⟨pairWithRow.compMultilinearMap col, fun fs gs => ?_⟩
  show β (col fs) (row gs) = _
  rw [hcol, hrow]
  rfl
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultilinearSumEqOfFunctionProductSumsEqStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.LastVertexInv
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem _root_.GlobalTheory.T.multilinear_sum_eq_of_function_product_sums_eq : ∀ {ι κ Δ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] {X : ι → Type} {Y : κ → Type}
    {V : ∀ i, Submodule ℂ (X i → ℂ)} {V' : ∀ j, Submodule ℂ (Y j → ℂ)}
    (M : MultilinearMap (RingHom.id ℂ) (fun i => V i)
      (MultilinearMap (RingHom.id ℂ) (fun j => V' j) ℂ)) (τ : Δ →₀ ℂ)
    (f f' : Δ → ∀ i, V i) (g g' : Δ → ∀ j, V' j),
    (∀ (x : ∀ i, X i) (y : ∀ j, Y j),
      (τ.sum fun d a => a * (∏ i, (f d i : X i → ℂ) (x i)) * ∏ j, (g d j : Y j → ℂ) (y j)) =
        τ.sum fun d a => a * (∏ i, (f' d i : X i → ℂ) (x i)) * ∏ j, (g' d j : Y j → ℂ) (y j)) →
    (τ.sum fun d a => a * M (f d) (g d)) = τ.sum fun d a => a * M (f' d) (g' d) := by
  exact @GlobalTheory.funProd_multilinear_sum_eq
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.FirstCoefficientDatumLaw

section

@[expose] public section

section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
namespace GlobalTheory.FirstRowDatum
theorem first_coefficient_datum_law : _root_.GlobalTheory.FunPr.ThetaLocalInputs → SumOKK → Big fun {D} {_Γ} _ _ {_Pl0} {T} {_A} {_Ks} _ _ _ {R} ch =>
    ∀ (t : T) a, ∀ β ∈ ch.S.supp t (ch.Phi a), ∀ τ, ch.S.IsExpansion t (ch.Phi a) β τ →
    ∀ (k : FinPt ch.G (.grid 0 D.R.m)), finG (ch.G.V (.grid 0 D.R.m)) k ∈ ch.S.levRow t 0 (Nat.zero_le _) →
    ∀ (hk : toXf k ∈ (levEnv D.sp.X' R.βX (R.datXt t)).J)
      (xs : ∀ j : Fin D.R.m, WO (ch.G.pS (.top t j)) (ch.G.pT (.top t j)))
      (ys : ∀ i : Fin D.R.m, WO (ch.G.pS (.chi i D.R.m : Pair T)) (ch.G.pT (.chi i D.R.m : Pair T))),
      (((levEnv D.sp.X' R.βX (R.datXt t)).χ ⟨toXf k, hk⟩ : ℂˣ) : ℂ) *
        (τ.sum fun d c => c * (∏ j, ch.S.Z.vec (d.1 j) (xs j)) *
          ∏ i, Function.update (fun i => ch.S.Z.vec (d.2 i)) (GlobalTheory.FirstRowVertex.firstIx D)
            (GlobalTheory.FirstRowVertex.rowShift0 ch.S.toGridChoice k (ch.S.Z.vec (d.2 (GlobalTheory.FirstRowVertex.firstIx D)))) i (ys i)) =
      τ.sum fun d c => c * (∏ j, ch.S.Z.vec (d.1 j) (xs j)) * ∏ i, ch.S.Z.vec (d.2 i) (ys i) := by
  intro hP hS
  obtain ⟨a₁, h₁⟩ := _root_.GlobalTheory.T.leading_coefficient_term_law_theta hP hS
  obtain ⟨a₂, h₂⟩ := hS
  refine ⟨max a₁ a₂, fun ε CF hC => ?_⟩
  have hb₁ := h₁ ε CF (le_of_max_le_left hC)
  have hb₂ := h₂ ε CF (le_of_max_le_right hC)
  obtain ⟨x₁, hc₁⟩ := hb₁
  obtain ⟨x₂, hc₂⟩ := hb₂
  refine ⟨max x₁ x₂, fun D large₂ e hx Γ _ _ Pl0 T A Ks _ _ _ R F s ch hi hsc => ?_⟩
  intro t a β hβ τ hτ k hkl hk xs ys
  have key := hc₁ D large₂ e (le_of_max_le_left hx) Γ Pl0 T A Ks R F s ch hi hsc t a β hβ τ hτ k hkl hk
  have hOK := hc₂ D large₂ e (le_of_max_le_right hx) Γ Pl0 T A Ks R F s ch hi hsc t a
  have hv := hOK.vec β τ hτ
  obtain ⟨e, he, hsupp, -⟩ := hτ
  have hsv := GlobalTheory.FirstRowShift.rowShift0_model (G := ch.G) (W := ch.W) (U := Set.univ) ch.S.toGridChoice s.core.lev (t := t) (e := e) (Set.mem_univ t) he k hkl
  obtain ⟨c, hc, hshift⟩ := hsv
  have hkey := key c hc
  generalize hχk : (((levEnv D.sp.X' R.βX (R.datXt t)).χ ⟨toXf k, hk⟩ : ℂˣ) : ℂ) = χk at hkey ⊢
  simp only [Finsupp.sum] at hkey ⊢
  rcases Finset.eq_empty_or_nonempty τ.support with h0 | ⟨d₀, hd₀⟩
  · simp [h0]
  have hTC : ∀ j : Fin D.R.m, ∃ Tm, IsPlaceModel ch.W.ψ (symplO _ _) (heisO ch.W.ψ _ _) e
      (latO (ch.G.pS (.top t j)) (ch.G.pT (.top t j)) (ch.S.N.latS (.top t j) : Set _) (ch.S.N.latT (.top t j) : Set _)
        fun _ => True) 1 (ch.S.Z.vac (.top t j)) Tm := by
    intro j
    obtain ⟨f, hf⟩ := (hv d₀ hd₀).1 j
    have hE := ((hsupp d₀ hd₀).1 j).2.1
    unfold FinDatum.IsTheta at hf
    rw [hE] at hf
    exact hf.1
  have hTR : ∀ i : Fin D.R.m, ∃ Tm, IsPlaceModel ch.W.ψ (symplO _ _) (heisO ch.W.ψ _ _) e
      (latO (ch.G.pS (.chi i D.R.m : Pair T)) (ch.G.pT (.chi i D.R.m : Pair T)) (ch.S.N.latS (.chi i D.R.m : Pair T) : Set _)
        (ch.S.N.latT (.chi i D.R.m : Pair T) : Set _) fun _ => True) 1 (ch.S.Z.vac (.chi i D.R.m : Pair T)) Tm := by
    intro i
    obtain ⟨f, hf⟩ := (hv d₀ hd₀).2 i
    have hE := ((hsupp d₀ hd₀).2 i).2.1
    unfold FinDatum.IsTheta at hf
    rw [hE] at hf
    exact hf.1
  choose TmC hTmC using hTC
  choose TmR hTmR using hTR
  have hvecC : ∀ d ∈ τ.support, ∀ j, ch.S.Z.vec (d.1 j) = TmC j (d.1 j).fn := by
    intro d hd j
    obtain ⟨f, hf⟩ := (hv d hd).1 j
    have hE := ((hsupp d hd).1 j).2.1
    have hz := ((hsupp d hd).1 j).2.2
    have hf' := hf
    unfold FinDatum.IsTheta at hf'
    rw [hE] at hf'
    rw [Normal.vec, FinDatum.vec_eq ch.W hf, hz, hf'.2 _ (hTmC j)]
    show ch.W.om _ 1 _ = _
    rw [map_one]; rfl
  have hvecR : ∀ d ∈ τ.support, ∀ i, ch.S.Z.vec (d.2 i) = TmR i (d.2 i).fn := by
    intro d hd i
    obtain ⟨f, hf⟩ := (hv d hd).2 i
    have hE := ((hsupp d hd).2 i).2.1
    have hz := ((hsupp d hd).2 i).2.2
    have hf' := hf
    unfold FinDatum.IsTheta at hf'
    rw [hE] at hf'
    rw [Normal.vec, FinDatum.vec_eq ch.W hf, hz, hf'.2 _ (hTmR i)]
    show ch.W.om _ 1 _ = _
    rw [map_one]; rfl
  have hext := sum_prod_map_eq_zero₂ TmC TmR (τ.support.disjSum τ.support)
    (Sum.elim (fun d => χk * c * τ d) (fun d => -τ d))
    (Sum.elim (fun d : PureDat ch.G t => fun j => (d.1 j).fn) (fun d : PureDat ch.G t => fun j => (d.1 j).fn))
    (Sum.elim (fun d : PureDat ch.G t => Function.update (fun i => (d.2 i).fn) (GlobalTheory.FirstRowVertex.firstIx D)
        (fun y => (d.2 (GlobalTheory.FirstRowVertex.firstIx D)).fn (actO (ch.G.pS (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (ch.G.pT (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (ch.G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((ch.S.N.u (.grid 0 D.R.m))⁻¹ * k * ch.S.N.u (.grid 0 D.R.m)).1 1).1⁻¹ (ch.G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((ch.S.N.u (.grid 0 D.R.m))⁻¹ * k * ch.S.N.u (.grid 0 D.R.m)).1 1).2⁻¹ y)))
      (fun d : PureDat ch.G t => fun i => (d.2 i).fn))
    (fun x y => by
      have h1 := hkey x y
      rw [Finset.mul_sum] at h1
      rw [Finset.sum_disjSum]
      simp only [Sum.elim_inl, Sum.elim_inr, neg_mul, Finset.sum_neg_distrib]
      rw [← h1, add_neg_eq_zero]
      exact Finset.sum_congr rfl fun d _ => by ring) xs ys
  rw [Finset.sum_disjSum] at hext
  simp only [Sum.elim_inl, Sum.elim_inr, neg_mul, Finset.sum_neg_distrib, add_neg_eq_zero] at hext
  refine Eq.trans ?_ (hext.trans ?_)
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun d hd => ?_
    have hsb := (d.2 (GlobalTheory.FirstRowVertex.firstIx D)).sb
    rw [((hsupp d hd).2 (GlobalTheory.FirstRowVertex.firstIx D)).2.1] at hsb
    simp only [hvecC d hd, hvecR d hd]
    rw [hshift (TmR (GlobalTheory.FirstRowVertex.firstIx D)) (hTmR _) _ hsb, GlobalTheory.FirstRowVertex.prod_update_smul]
    have hu : ∀ i, Function.update (fun i => TmR i (d.2 i).fn) (GlobalTheory.FirstRowVertex.firstIx D)
        (TmR (GlobalTheory.FirstRowVertex.firstIx D) (fun y => (d.2 (GlobalTheory.FirstRowVertex.firstIx D)).fn
          (actO (ch.G.pS (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (ch.G.pT (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (ch.G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((ch.S.N.u (.grid 0 D.R.m))⁻¹ * k * ch.S.N.u (.grid 0 D.R.m)).1 1).1⁻¹ (ch.G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((ch.S.N.u (.grid 0 D.R.m))⁻¹ * k * ch.S.N.u (.grid 0 D.R.m)).1 1).2⁻¹ y))) i (ys i) =
        TmR i (Function.update (fun i => (d.2 i).fn) (GlobalTheory.FirstRowVertex.firstIx D)
          (fun y => (d.2 (GlobalTheory.FirstRowVertex.firstIx D)).fn
            (actO (ch.G.pS (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (ch.G.pT (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (ch.G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((ch.S.N.u (.grid 0 D.R.m))⁻¹ * k * ch.S.N.u (.grid 0 D.R.m)).1 1).1⁻¹ (ch.G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((ch.S.N.u (.grid 0 D.R.m))⁻¹ * k * ch.S.N.u (.grid 0 D.R.m)).1 1).2⁻¹ y)) i) (ys i) := by
      intro i
      by_cases hi : i = GlobalTheory.FirstRowVertex.firstIx D
      · subst hi
        simp only [Function.update_self]
      · simp only [Function.update_of_ne hi]
    simp only [hu]
    ring
  · refine Finset.sum_congr rfl fun d hd => ?_
    simp only [hvecC d hd, hvecR d hd]
end GlobalTheory.FirstRowDatum
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem _root_.GlobalTheory.T.twist_first_coefficient_law : _root_.GlobalTheory.FunPr.ThetaLocalInputs → SumOKK → Big fun {D} {_Γ} _ _ {_Pl0} {T} {_A} {_Ks} _ _ _ {R} ch =>
    ∀ (t : T) a, ∀ β ∈ ch.S.supp t (ch.Phi a), ∀ τ, ch.S.IsExpansion t (ch.Phi a) β τ →
    ∀ (k : FinPt ch.G (.grid 0 D.R.m)), finG (ch.G.V (.grid 0 D.R.m)) k ∈ ch.S.levRow t 0 (Nat.zero_le _) →
    ∀ (hk : toXf k ∈ (levEnv D.sp.X' R.βX (R.datXt t)).J)
      (xs : ∀ j : Fin D.R.m, WO (ch.G.pS (.top t j)) (ch.G.pT (.top t j)))
      (ys : ∀ i : Fin D.R.m, WO (ch.G.pS (.chi i D.R.m : Pair T)) (ch.G.pT (.chi i D.R.m : Pair T))),
      (((levEnv D.sp.X' R.βX (R.datXt t)).χ ⟨toXf k, hk⟩ : ℂˣ) : ℂ) *
        (τ.sum fun d c => c * (∏ j, ch.S.Z.vec (d.1 j) (xs j)) *
          ∏ i, Function.update (fun i => ch.S.Z.vec (d.2 i)) (GlobalTheory.FirstRowVertex.firstIx D)
            (GlobalTheory.FirstRowVertex.rowShift0 ch.S.toGridChoice k (ch.S.Z.vec (d.2 (GlobalTheory.FirstRowVertex.firstIx D)))) i (ys i)) =
      τ.sum fun d c => c * (∏ j, ch.S.Z.vec (d.1 j) (xs j)) * ∏ i, ch.S.Z.vec (d.2 i) (ys i) := by
  first | exact @_root_.GlobalTheory.FirstRowDatum.first_coefficient_datum_law | exact _root_.GlobalTheory.FirstRowDatum.first_coefficient_datum_law | (intros; apply _root_.GlobalTheory.FirstRowDatum.first_coefficient_datum_law <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.VertexPairPointsTransformationLaw

section

@[expose] public section

section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
namespace GlobalTheory.FirstRowVertex
open GlobalTheory.LastVertexInv in
theorem pair_points_first_vertex_law : _root_.GlobalTheory.FunPr.ThetaLocalInputs → SumOKK → Big fun {D} {_Γ} _ _ {_Pl0} {T} {_A} {_Ks} _ _ _ {R} ch =>
    ∀ (t : T) a, ∀ β ∈ ch.S.supp t (ch.Phi a), ∀ τ, ch.S.IsExpansion t (ch.Phi a) β τ →
    ∀ (x : ∀ j, FinPt ch.G (.top j)) (y : ∀ i, FinPt ch.G (.grid i D.R.m)) (k : FinPt ch.G (.grid 0 D.R.m))
      (_ : finG (ch.G.V (.grid 0 D.R.m)) k ∈ ch.S.levRow t 0 (Nat.zero_le _)) (hk : toXf k ∈ (levEnv D.sp.X' R.βX (R.datXt t)).J)
      (v : VV ℂ (wt ch.G (.top 0))) (w : VV ℂ (listedWt ch.G (.grid 0 D.R.m))),
      GlobalTheory.ExpansionInvariance.pairPts ch.S.toGridChoice τ x (Function.update y 0 (y 0 * k)) v
        ((((levEnv D.sp.X' R.βX (R.datXt t)).χ ⟨toXf k, hk⟩ : ℂˣ) : ℂ) • w) =
      GlobalTheory.ExpansionInvariance.pairPts ch.S.toGridChoice τ x y v w := by
  intro hP hS
  obtain ⟨a₁, h₁⟩ := _root_.GlobalTheory.T.twist_first_coefficient_law hP hS
  obtain ⟨a₂, h₂⟩ := hS
  refine ⟨max a₁ a₂, fun ε CF hC => ?_⟩
  have hb₁ := h₁ ε CF (le_of_max_le_left hC)
  have hb₂ := h₂ ε CF (le_of_max_le_right hC)
  obtain ⟨x₁, hc₁⟩ := hb₁
  obtain ⟨x₂, hc₂⟩ := hb₂
  refine ⟨max x₁ x₂, fun D large₂ e hx Γ _ _ Pl0 T A Ks _ _ _ R F s ch hi hsc => ?_⟩
  intro t a β hβ τ hτ x y k hkl hk v w
  have key := hc₁ D large₂ e (le_of_max_le_left hx) Γ Pl0 T A Ks R F s ch hi hsc t a β hβ τ hτ k hkl hk
  have hOK := hc₂ D large₂ e (le_of_max_le_right hx) Γ Pl0 T A Ks R F s ch hi hsc t a
  generalize hχk : (((levEnv D.sp.X' R.βX (R.datXt t)).χ ⟨toXf k, hk⟩ : ℂˣ) : ℂ) = χk at key ⊢
  have hth : ∀ d ∈ τ.support, (∀ j, IsThetaFunO ch.W.ψ _ _ (ch.S.Z.vec (d.1 j))) ∧ ∀ i, IsThetaFunO ch.W.ψ _ _ (ch.S.Z.vec (d.2 i)) :=
    fun d hd => ⟨fun j => vec_theta ch.S.toGridChoice (defPair_top t j) (inRange_top t j) _ ((hOK.vec β τ hτ d hd).1 j),
      fun i => vec_theta ch.S.toGridChoice (defPair_chi i) (inRange_chi i) _ ((hOK.vec β τ hτ d hd).2 i)⟩
  obtain ⟨M, hM⟩ := GlobalTheory.T.exists_multilinear_columnRowKernelPairing ch.S.toGridChoice t x y v w
  have thr : ∀ d ∈ τ.support, ∀ i,
      IsThetaFunO ch.W.ψ _ _ (movedRow ch.S.toGridChoice k (fun i => ch.S.Z.vec (d.2 i)) i) := by
    intro d hd i
    by_cases hi0 : i = firstIx D
    · subst hi0
      simp only [movedRow, Function.update_self]
      exact rowShift0_theta ch.S.toGridChoice k ((hth d hd).2 _)
    · simp only [movedRow, Function.update_of_ne hi0]
      exact (hth d hd).2 i
  have thr' : ∀ d ∈ τ.support, ∀ i, IsThetaFunO ch.W.ψ _ _
      (Function.update (movedRow ch.S.toGridChoice k (fun i => ch.S.Z.vec (d.2 i))) (firstIx D)
        (χk • movedRow ch.S.toGridChoice k (fun i => ch.S.Z.vec (d.2 i)) (firstIx D)) i) := by
    intro d hd i
    by_cases hi0 : i = firstIx D
    · subst hi0
      simp only [Function.update_self]
      exact GlobalTheory.OrientedHeis.theta_smul χk (thr d hd _)
    · simp only [Function.update_of_ne hi0]
      exact thr d hd i
  have lhs : GlobalTheory.ExpansionInvariance.pairPts ch.S.toGridChoice τ x (Function.update y 0 (y 0 * k)) v w =
      τ.sum fun d c => c * M (fun j => toTh ch.W _ (ch.S.Z.vec (d.1 j)))
        (fun i => toTh ch.W _ (movedRow ch.S.toGridChoice k (fun i => ch.S.Z.vec (d.2 i)) i)) := by
    simp only [GlobalTheory.ExpansionInvariance.pairPts, Finsupp.sum, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun d hd => ?_
    congr 1
    rw [hM, colMap_eq, rowMap_eq, rowMapV_update_zero ch.S.toGridChoice _ y k ((hth d hd).2 _)]
    have e1 : (fun j : Fin D.R.m => (toTh ch.W _ (ch.S.Z.vec (d.1 j)) : WO (ch.G.pS (.top t j)) (ch.G.pT (.top t j)) → ℂ)) =
        fun j : Fin D.R.m => ch.S.Z.vec (d.1 j) :=
      funext fun j => coe_toTh ch.W _ ((hth d hd).1 j)
    have e2 : (fun i : Fin D.R.m => (toTh ch.W _ (movedRow ch.S.toGridChoice k (fun i => ch.S.Z.vec (d.2 i)) i) :
        WO (ch.G.pS (.chi i D.R.m : Pair T)) (ch.G.pT (.chi i D.R.m : Pair T)) → ℂ)) =
        movedRow ch.S.toGridChoice k (fun i => ch.S.Z.vec (d.2 i)) :=
      funext fun i => coe_toTh ch.W _ (thr d hd i)
    rw [e1, e2]
  have rhs : GlobalTheory.ExpansionInvariance.pairPts ch.S.toGridChoice τ x y v w =
      τ.sum fun d c => c * M (fun j => toTh ch.W _ (ch.S.Z.vec (d.1 j))) (fun i => toTh ch.W _ (ch.S.Z.vec (d.2 i))) := by
    simp only [GlobalTheory.ExpansionInvariance.pairPts, Finsupp.sum, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun d hd => ?_
    congr 1
    rw [hM, colMap_eq, rowMap_eq]
    have e1 : (fun j : Fin D.R.m => (toTh ch.W _ (ch.S.Z.vec (d.1 j)) : WO (ch.G.pS (.top t j)) (ch.G.pT (.top t j)) → ℂ)) =
        fun j : Fin D.R.m => ch.S.Z.vec (d.1 j) :=
      funext fun j => coe_toTh ch.W _ ((hth d hd).1 j)
    have e2 : (fun i : Fin D.R.m => (toTh ch.W _ (ch.S.Z.vec (d.2 i)) :
        WO (ch.G.pS (.chi i D.R.m : Pair T)) (ch.G.pT (.chi i D.R.m : Pair T)) → ℂ)) =
        fun i : Fin D.R.m => ch.S.Z.vec (d.2 i) :=
      funext fun i => coe_toTh ch.W _ ((hth d hd).2 i)
    rw [e1, e2]
  have hscale : ∀ d ∈ τ.support,
      M (fun j => toTh ch.W _ (ch.S.Z.vec (d.1 j)))
        (fun i => toTh ch.W _ (Function.update (movedRow ch.S.toGridChoice k (fun i => ch.S.Z.vec (d.2 i))) (firstIx D)
          (χk • movedRow ch.S.toGridChoice k (fun i => ch.S.Z.vec (d.2 i)) (firstIx D)) i)) =
      χk * M (fun j => toTh ch.W _ (ch.S.Z.vec (d.1 j)))
        (fun i => toTh ch.W _ (movedRow ch.S.toGridChoice k (fun i => ch.S.Z.vec (d.2 i)) i)) := by
    intro d hd
    have eg : (fun i : Fin D.R.m => toTh ch.W (.chi i D.R.m : Pair T)
        (Function.update (movedRow ch.S.toGridChoice k (fun i => ch.S.Z.vec (d.2 i))) (firstIx D)
          (χk • movedRow ch.S.toGridChoice k (fun i => ch.S.Z.vec (d.2 i)) (firstIx D)) i)) =
        Function.update (fun i : Fin D.R.m => toTh ch.W (.chi i D.R.m : Pair T) (movedRow ch.S.toGridChoice k (fun i => ch.S.Z.vec (d.2 i)) i))
          (firstIx D) (χk • toTh ch.W _ (movedRow ch.S.toGridChoice k (fun i => ch.S.Z.vec (d.2 i)) (firstIx D))) := by
      funext i
      by_cases hi0 : i = firstIx D
      · subst hi0
        apply Subtype.ext
        have h1 := coe_toTh ch.W _ (thr' d hd (firstIx D))
        simp only [Function.update_self] at h1 ⊢
        rw [h1, Submodule.coe_smul, coe_toTh ch.W _ (thr d hd _)]
      · simp only [Function.update_of_ne hi0]
    rw [eg, MultilinearMap.map_update_smul, Function.update_eq_self, smul_eq_mul]
    rfl
  rw [LinearMap.map_smul, smul_eq_mul, lhs, rhs, Finsupp.sum, Finset.mul_sum]
  have step1 : (∑ d ∈ τ.support, χk * (τ d * M (fun j => toTh ch.W _ (ch.S.Z.vec (d.1 j)))
        (fun i => toTh ch.W _ (movedRow ch.S.toGridChoice k (fun i => ch.S.Z.vec (d.2 i)) i)))) =
      τ.sum fun d c => c * M (fun j => toTh ch.W _ (ch.S.Z.vec (d.1 j)))
        (fun i => toTh ch.W _ (Function.update (movedRow ch.S.toGridChoice k (fun i => ch.S.Z.vec (d.2 i))) (firstIx D)
          (χk • movedRow ch.S.toGridChoice k (fun i => ch.S.Z.vec (d.2 i)) (firstIx D)) i)) := by
    refine Finset.sum_congr rfl fun d hd => ?_
    dsimp only
    rw [hscale d hd]
    ring
  rw [step1]
  refine GlobalTheory.T.multilinear_sum_eq_of_function_product_sums_eq M τ _ _ _ _ fun xs ys => ?_
  have hk' := key xs ys
  simp only [Finsupp.sum] at hk' ⊢
  refine (?_ : _ = χk * _).trans (hk'.trans (Finset.sum_congr rfl fun d hd => ?_))
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun d hd => ?_
    simp only [coe_toTh ch.W _ ((hth d hd).1 _), coe_toTh ch.W _ (thr' d hd _)]
    rw [prod_update_smul, Function.update_eq_self]
    simp only [movedRow]
    ring
  · simp only [coe_toTh ch.W _ ((hth d hd).1 _), coe_toTh ch.W _ ((hth d hd).2 _)]
end GlobalTheory.FirstRowVertex
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem _root_.GlobalTheory.T.vertex_pair_points_transformation_law : _root_.GlobalTheory.FunPr.ThetaLocalInputs → SumOKK → Big fun {D} {_Γ} _ _ {_Pl0} {T} {_A} {_Ks} _ _ _ {R} ch =>
    ∀ (t : T) a, ∀ β ∈ ch.S.supp t (ch.Phi a), ∀ τ, ch.S.IsExpansion t (ch.Phi a) β τ →
    ∀ (x : ∀ j, FinPt ch.G (.top j)) (y : ∀ i, FinPt ch.G (.grid i D.R.m)) (k : FinPt ch.G (.grid 0 D.R.m))
      (_ : finG (ch.G.V (.grid 0 D.R.m)) k ∈ ch.S.levRow t 0 (Nat.zero_le _)) (hk : toXf k ∈ (levEnv D.sp.X' R.βX (R.datXt t)).J)
      (v : VV ℂ (wt ch.G (.top 0))) (w : VV ℂ (listedWt ch.G (.grid 0 D.R.m))),
      GlobalTheory.ExpansionInvariance.pairPts ch.S.toGridChoice τ x (Function.update y 0 (y 0 * k)) v
        ((((levEnv D.sp.X' R.βX (R.datXt t)).χ ⟨toXf k, hk⟩ : ℂˣ) : ℂ) • w) =
      GlobalTheory.ExpansionInvariance.pairPts ch.S.toGridChoice τ x y v w := by
  first | exact @_root_.GlobalTheory.FirstRowVertex.pair_points_first_vertex_law | exact _root_.GlobalTheory.FirstRowVertex.pair_points_first_vertex_law | (intros; apply _root_.GlobalTheory.FirstRowVertex.pair_points_first_vertex_law <;> assumption)
end
end
end
