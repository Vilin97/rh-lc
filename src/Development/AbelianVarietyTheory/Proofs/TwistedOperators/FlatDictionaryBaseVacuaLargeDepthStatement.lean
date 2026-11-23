module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSignFlatDictionaryAtOnePlaceLargeDepthStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlippedFiniteTensorSumProdLocalPureTensorsStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalPureTensorProductExpansionAllPlacesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealLineOfPeriodsOnLine
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsModelCombL
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitLocalPlaceLocalModelsLinearSubspace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFiniteReproducingOfSubmodule
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldedVacuaAreRealDatumLargeDepthStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldedProductDependsOnDataProductStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestCombinationDependsOnProductFunction

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.CombDet

theorem row_position {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) {t : T} {p : Pair T}
    {I : Type} (S : Finset I) (e : AE D) (d : I → FinDatum G t p) (c : I → (WO (G.pS p) (G.pT p) →₀ ℂ))
    (hd : ∀ i ∈ S, (d i).e = e ∧ IsCombOf W (d i) (c i)) (f₀ : WO (G.pS p) (G.pT p) → ℂ)
    (h1 : IsThetaFunO W.ψ _ _ f₀)
    (h2 : IsLatVac (heisO W.ψ _ _) (latO (G.pS p) (G.pT p) (G.latS p : Set _) (G.latT p : Set _) fun _ => True) f₀) :
    ∃ Tm : (WO (G.pS p) (G.pT p) → ℂ) →ₗ[ℂ] (WO (G.pS p) (G.pT p) → ℂ), ∀ i ∈ S, comb W.ψ _ _ (c i) f₀ = Tm (d i).fn := by
  rcases S.eq_empty_or_nonempty with hS | ⟨i₀, hi₀⟩
  · exact ⟨0, fun i hi => by simp [hS] at hi⟩
  have key : ∀ i ∈ S, IsThetaAt W.ψ (symplO _ _) (heisO W.ψ _ _) e
      (latO (G.pS p) (G.pT p) (G.latS p : Set _) (G.latT p : Set _) fun _ => True) 1 f₀ (d i).fn (comb W.ψ _ _ (c i) f₀) := by
    intro i hi
    have h := (hd i hi).2.2.2 f₀ h1 h2
    have he := (hd i hi).1
    unfold FinDatum.IsTheta at h
    rw [he] at h
    exact h
  obtain ⟨Tm, hTm⟩ := (key i₀ hi₀).1
  exact ⟨Tm, fun i hi => (key i hi).2 Tm hTm⟩

def Spans {I Y : Type} (S : Finset I) (H : Y → I → ℂ) (g : I → ℂ) : Prop :=
  ∃ (J : Type) (P : Finset J) (a : J → ℂ) (y : J → Y), ∀ i ∈ S, g i = ∑ j ∈ P, a j * H (y j) i

theorem sum_prod_eq_zero {I ι : Type} [Fintype ι] {Y : ι → Type} (S : Finset I) (x : I → ℂ) (H : ∀ l, Y l → I → ℂ)
    (g : ι → I → ℂ) (hg : ∀ l, Spans S (H l) (g l)) (h : ∀ z : ∀ l, Y l, ∑ i ∈ S, x i * ∏ l, H l (z l) i = 0) :
    ∑ i ∈ S, x i * ∏ l, g l i = 0 := by
  classical
  choose J P a y hy using hg
  have e : ∀ i ∈ S, x i * ∏ l, g l i =
      ∑ z ∈ Fintype.piFinset P, (∏ l, a l (z l)) * (x i * ∏ l, H l (y l (z l)) i) := by
    intro i hi
    rw [Finset.prod_congr rfl fun l _ => hy l i hi, Finset.prod_univ_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [Finset.prod_mul_distrib]
    ring
  rw [Finset.sum_congr rfl e, Finset.sum_comm]
  refine Finset.sum_eq_zero fun z _ => ?_
  rw [← Finset.mul_sum, h fun l => y l (z l), mul_zero]

theorem reproducing {I X : Type} (S : Finset I) (V : Submodule ℂ (X → ℂ)) (F : I → X → ℂ) (hF : ∀ i ∈ S, F i ∈ V) :
    ∃ (P : Finset X) (u : X → X → ℂ), (∀ x, u x ∈ V) ∧ ∀ i ∈ S, F i = ∑ x ∈ P, F i x • u x := by
  classical
  obtain ⟨P, u, hu⟩ := GlobalTheory.exists_finite_reproducing_of_submodule V
    (S.attach.image fun i : {i // i ∈ S} => (⟨F i.1, hF i.1 i.2⟩ : V))
  refine ⟨P, fun x => u x, fun x => (u x).2, fun i hi => ?_⟩
  have := congrArg V.subtype (hu ⟨F i, hF i hi⟩ (Finset.mem_image.2 ⟨⟨i, hi⟩, Finset.mem_attach _ _, rfl⟩))

  simpa only [map_sum, map_smul, Submodule.subtype_apply] using this

theorem spans_linear {I X Z : Type} (S : Finset I) (F : I → X → ℂ) (Tm : (X → ℂ) →ₗ[ℂ] (Z → ℂ)) (z : Z) (g : I → ℂ)
    (hg : ∀ i ∈ S, g i = Tm (F i) z) : Spans S (fun x i => F i x) g := by
  obtain ⟨P, u, -, hu⟩ := reproducing S ⊤ F fun _ _ => trivial
  refine ⟨X, P, fun x => Tm (u x) z, id, fun i hi => ?_⟩
  rw [hg i hi]
  conv_lhs => rw [hu i hi]

  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, id]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

def vacSp {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (Λ : AddSubgroup (WO S T)) : Submodule ℂ (WO S T → ℂ) where
  carrier := {f | IsThetaFunO ψ S T f ∧ IsLatVac (heisO ψ S T) Λ f}
  add_mem' := by
    intro f g hf hg
    have key : ∀ u, heisO ψ S T u (f + g) = heisO ψ S T u f + heisO ψ S T u g := fun u => by
      funext w; simp only [heisO, Pi.add_apply, mul_add]
    refine ⟨GlobalTheory.LocMod.LinSpace.isThetaFunO_add hf.1 hg.1, fun u hu => ?_, fun e he u hu hh => ?_⟩
    · rw [key, hf.2.1 u hu, hg.2.1 u hu]
    · rw [key, hf.2.2 e he u hu hh, hg.2.2 e he u hu hh]
  zero_mem' := ⟨GlobalTheory.LocMod.LinSpace.isThetaFunO_zero ψ S T, fun u _ => by funext w; simp [heisO],
    fun e _ u _ _ => by funext w; simp [heisO]⟩
  smul_mem' := by
    intro c f hf
    have key : ∀ u, heisO ψ S T u (c • f) = c • heisO ψ S T u f := fun u => by
      funext w; simp only [heisO, Pi.smul_apply, smul_eq_mul]; ring
    refine ⟨GlobalTheory.LocMod.LinSpace.isThetaFunO_smul c hf.1, fun u hu => ?_, fun e he u hu hh => ?_⟩
    · rw [key, hf.2.1 u hu]
    · rw [key, hf.2.2 e he u hu hh]

theorem col_position {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) {t : T} (j : ℕ)
    {I : Type} (S : Finset I) (e : AE D) (d₁ : I → FinDatum G t (.top t j)) (d₂ : I → FinDatum G t (.top t (j + 1)))
    (c₁ : I → (WO (G.V (.top j)) (G.V (.top (j + 1))) →₀ ℂ)) (c₂ : I → (WO (G.V (.top (j + 1))) (G.V (.top (j + 1 + 1))) →₀ ℂ))
    (h₁ : ∀ i ∈ S, (d₁ i).e = e ∧ IsCombOf W (d₁ i) (c₁ i)) (h₂ : ∀ i ∈ S, (d₂ i).e = e ∧ IsCombOf W (d₂ i) (c₂ i))
    (C : WO (G.V (.top j)) (G.V (.top (j + 1))) → WO (G.V (.top (j + 1))) (G.V (.top (j + 1 + 1))) → ℂ)
    (hC : IsBiVac W.ψ _ _ _ (G.Λ (.top j) : Set _) (G.Λ (.top (j + 1)) : Set _) (G.Λ (.top (j + 1 + 1)) : Set _) C) (u v) :
    Spans S (fun (p : WO (G.V (.top j)) (G.V (.top (j + 1))) × WO (G.V (.top (j + 1))) (G.V (.top (j + 1 + 1)))) i =>
      (d₁ i).fn p.1 * (d₂ i).fn p.2) fun i => biComb W.ψ _ _ _ (c₁ i) (c₂ i) C u v := by
  classical
  choose Tu hTu using fun u' => row_position W S e d₂ c₂ h₂ (C u') (hC.right u').1 (hC.right u').2
  let Lm : (WO (G.V (.top (j + 1))) (G.V (.top (j + 1 + 1))) → ℂ) →ₗ[ℂ] (WO (G.V (.top j)) (G.V (.top (j + 1))) → ℂ) :=
    LinearMap.pi fun u' => (LinearMap.proj v) ∘ₗ Tu u'
  let Vac := vacSp W.ψ _ _ (latO (G.V (.top j)) (G.V (.top (j + 1))) (G.Λ (.top j) : Set _) (G.Λ (.top (j + 1)) : Set _) fun _ => True)
  have hL : ∀ i ∈ S, Lm (d₂ i).fn = fun u' => comb W.ψ _ _ (c₂ i) (C u') v := fun i hi => by
    funext u'
    exact (congrFun (hTu u' i hi) v).symm
  have hV : ∀ i ∈ S, (d₂ i).fn ∈ Vac.comap Lm := fun i hi => by
    rw [Submodule.mem_comap, hL i hi]
    have : (fun u' => comb W.ψ _ _ (c₂ i) (C u') v) =
        ∑ b ∈ (c₂ i).support, ((c₂ i) b * W.ψ (symplOH _ _ v b)) • fun u' => C u' (v + b) := by
      funext u'
      simp only [GlobalTheory.BiCombStable.comb_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_assoc]
    rw [this]
    exact Vac.sum_mem fun b _ => Vac.smul_mem _ (hC.left (v + b))
  obtain ⟨P, ε, hε, hP⟩ := reproducing S (Vac.comap Lm) (fun i => (d₂ i).fn) hV
  choose Tx hTx using fun x => row_position W S e d₁ c₁ h₁ (Lm (ε x)) (hε x).1 (hε x).2
  obtain ⟨Q, η, -, hQ⟩ := reproducing S ⊤ (fun i => (d₁ i).fn) fun _ _ => trivial
  refine ⟨_, Q ×ˢ P, fun p => Tx p.2 (η p.1) u, id, fun i hi => ?_⟩
  have e1 : biComb W.ψ _ _ _ (c₁ i) (c₂ i) C u v = GlobalTheory.BiCombStable.combL W.ψ _ _ (c₁ i) (Lm (d₂ i).fn) u := by
    rw [hL i hi]; rfl
  have e2 : ∀ x, GlobalTheory.BiCombStable.combL W.ψ _ _ (c₁ i) (Lm (ε x)) = ∑ q ∈ Q, (d₁ i).fn q • Tx x (η q) := fun x => by
    refine (hTx x i hi).trans ?_
    refine (congrArg (Tx x) (hQ i hi)).trans ?_

    simp only [map_sum, map_smul]
  have e3 : GlobalTheory.BiCombStable.combL W.ψ _ _ (c₁ i) (Lm (d₂ i).fn) =
      ∑ x ∈ P, (d₂ i).fn x • GlobalTheory.BiCombStable.combL W.ψ _ _ (c₁ i) (Lm (ε x)) := by
    refine (congrArg (fun f => GlobalTheory.BiCombStable.combL W.ψ _ _ (c₁ i) (Lm f)) (hP i hi)).trans ?_

    simp only [map_sum, map_smul]
  show biComb W.ψ _ _ _ (c₁ i) (c₂ i) C u v = _
  rw [e1, e3, Finset.sum_product_right, Finset.sum_apply]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [e2, Pi.smul_apply, Finset.sum_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul, id]
  ring

theorem prod_range_pairs (f : ℕ → ℂ) (n : ℕ) :
    ∏ j ∈ Finset.range (2 * n), f j = ∏ k ∈ Finset.range n, f (2 * k) * f (2 * k + 1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, Finset.prod_range_succ, Finset.prod_range_succ, ih,
      Finset.prod_range_succ, mul_assoc]

theorem sum_evT_eq_zero {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (ρ : RealMatch W)
    (t : T) (e : AE D) (I : Type) (S : Finset I) (x : I → ℂ) (d : I → PureDat G t) (c : I → Combs G)
    (hd : ∀ i ∈ S, (∀ j : Fin D.R.m, ((d i).1 j).e = e ∧ IsCombOf W ((d i).1 j) ((c i).1 j)) ∧
      ∀ n, ((d i).2 n).e = e ∧ IsCombOf W ((d i).2 n) ((c i).2 n))
    (h : ∀ (u : ∀ j : Fin D.R.m, WO (G.V (.top j)) (G.V (.top (j + 1)))) (y : RowPt G), (∀ j, IsHalf e (u j)) →
      (∀ n, IsHalf e (y n)) → ∑ i ∈ S, x i * ((∏ j, ((d i).1 j).fn (u j)) * ∏ n, ((d i).2 n).fn (y n)) = 0)
    (C : BiFam G) (hC : IsRealFam W C) (u : ColPt G) (y : RowPt G) :
    ∑ i ∈ S, x i * evT (combC W (c i) C) (combR ρ (c i)) u y = 0 := by
  classical
  have hm : 0 + 2 * ((D.R.m - 2) / 2) + 2 = D.R.m := top_idx
  have h' : ∀ (u : ∀ j : Fin D.R.m, WO (G.V (.top j)) (G.V (.top (j + 1)))) (y : RowPt G),
      ∑ i ∈ S, x i * ((∏ j, ((d i).1 j).fn (u j)) * ∏ n, ((d i).2 n).fn (y n)) = 0 := by
    intro u y
    by_cases hu : ∀ j, IsHalf e (u j)
    · by_cases hy : ∀ n, IsHalf e (y n)
      · exact h u y hu hy
      · obtain ⟨n, hn⟩ := not_forall.1 hy
        refine Finset.sum_eq_zero fun i hi => ?_
        have h0 : ((d i).2 n).fn (y n) = 0 := by
          by_contra h0
          exact hn (((hd i hi).2 n).1 ▸ ((d i).2 n).sb.1 _ h0)
        rw [Finset.prod_eq_zero (f := fun n => ((d i).2 n).fn (y n)) (Finset.mem_univ n) h0, mul_zero, mul_zero]
    · obtain ⟨j, hj⟩ := not_forall.1 hu
      refine Finset.sum_eq_zero fun i hi => ?_
      have h0 : ((d i).1 j).fn (u j) = 0 := by
        by_contra h0
        exact hj (((hd i hi).1 j).1 ▸ ((d i).1 j).sb.1 _ h0)
      rw [Finset.prod_eq_zero (f := fun j => ((d i).1 j).fn (u j)) (Finset.mem_univ j) h0, zero_mul, mul_zero]

  have hrow : ∀ (u : ∀ j : Fin D.R.m, WO (G.V (.top j)) (G.V (.top (j + 1)))),
      ∑ i ∈ S, (x i * ∏ j, ((d i).1 j).fn (u j)) * ∏ n, combR ρ (c i) n (y n) = 0 := by
    intro u
    refine sum_prod_eq_zero S _ (fun (n : Fin D.R.m) (z : WO (G.pS (.chi n D.R.m : Pair T)) (G.pT (.chi n D.R.m : Pair T))) i =>
      ((d i).2 n).fn z) (fun n i => combR ρ (c i) n (y n)) (fun n => ?_) fun z => ?_
    · have hv := ρ.vX_is n D.R.m n.2 le_rfl
      obtain ⟨Tm, hTm⟩ := row_position W S e (fun i => (d i).2 n) (fun i => (c i).2 n) (fun i hi => (hd i hi).2 n) _
        hv.2.theta hv.2.lat
      exact spans_linear S (fun i => ((d i).2 n).fn) Tm (y n) _ fun i hi => congrFun (hTm i hi) (y n)
    · simpa only [mul_assoc] using h' u z

  let F : I → ∀ j : ℕ, WO (G.V (.top j)) (G.V (.top (j + 1))) → ℂ := fun i j =>
    if hj : j < D.R.m then ((d i).1 ⟨j, hj⟩).fn else 0
  have hcol := sum_prod_eq_zero (ι := Fin (D.R.m / 2)) S (fun i => x i * ∏ n, combR ρ (c i) n (y n))
    (fun k (w : ColPt G) i => F i (2 * k) (w (2 * k)) * F i (2 * k + 1) (w (2 * k + 1)))
    (fun k i => combC W (c i) C (2 * k) (u (2 * k)) (u (2 * k + 1))) (fun k => ?_) fun z => ?_
  · rw [← hcol]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [evT, Finset.prod_range]
    ring
  · have k0 : 2 * (k : ℕ) < D.R.m := by have := k.2; omega
    have k1 : 2 * (k : ℕ) + 1 < D.R.m := by have := k.2; omega
    obtain ⟨J, P, a, p, hp⟩ := col_position W (2 * k) S e (fun i => (d i).1 ⟨2 * k, k0⟩) (fun i => (d i).1 ⟨2 * k + 1, k1⟩)
      (fun i => (c i).1 (2 * k)) (fun i => (c i).1 (2 * k + 1)) (fun i hi => (hd i hi).1 ⟨2 * k, k0⟩)
      (fun i hi => (hd i hi).1 ⟨2 * k + 1, k1⟩) (C (2 * k)) (hC _ (even_two_mul _) k0).1 (u (2 * k)) (u (2 * k + 1))
    refine ⟨J, P, a, fun j => Function.update (Function.update (0 : ColPt G) (2 * k) (p j).1) (2 * k + 1) (p j).2,
      fun i hi => (hp i hi).trans (Finset.sum_congr rfl fun j _ => ?_)⟩
    simp only [F, dif_pos k0, dif_pos k1, Function.update_self,
      Function.update_of_ne (show 2 * (k : ℕ) ≠ 2 * k + 1 by omega)]
  · let w : ColPt G := fun j => if hj : j / 2 < D.R.m / 2 then z ⟨j / 2, hj⟩ j else 0
    have hw : ∀ (k : Fin (D.R.m / 2)) (j : ℕ), j / 2 = (k : ℕ) → w j = z k j := by
      rintro ⟨k, hk⟩ j hj
      have hj' : j / 2 = k := hj
      subst hj'
      exact dif_pos hk
    rw [← hrow fun j => w j]
    refine Finset.sum_congr rfl fun i _ => ?_
    have e1 : ∏ j : Fin D.R.m, ((d i).1 j).fn (w j) = ∏ j ∈ Finset.range D.R.m, F i j (w j) := by
      rw [Finset.prod_range]
      exact Finset.prod_congr rfl fun j _ => by simp only [F, dif_pos j.2]
    have e2 : Finset.range D.R.m = Finset.range (2 * (D.R.m / 2)) := by congr 1; omega
    rw [e1, e2, prod_range_pairs (fun j => F i j (w j)), Finset.prod_range,
      Finset.prod_congr rfl fun (k : Fin (D.R.m / 2)) _ => show F i (2 * k) (w (2 * k)) * F i (2 * k + 1) (w (2 * k + 1)) =
        F i (2 * k) (z k (2 * k)) * F i (2 * k + 1) (z k (2 * k + 1)) by
          rw [hw k _ (by omega), hw k _ (by omega)]]
    ring

theorem comb_det : Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ t e, IsIdemSum e (locPl ch.G t) → ∀ (I : Type) (S : Finset I) (x : I → ℂ) (d : I → PureDat ch.G t) (c : I → Combs ch.G), (∀ i ∈ S, (∀ j : Fin D.R.m, ((d i).1 j).e = e ∧ IsCombOf ch.W ((d i).1 j) ((c i).1 j)) ∧ ∀ n, ((d i).2 n).e = e ∧ IsCombOf ch.W ((d i).2 n) ((c i).2 n)) → (∀ (u : ∀ j : Fin D.R.m, WO (ch.G.V (.top j)) (ch.G.V (.top (j + 1)))) (y : RowPt ch.G), (∀ j, IsHalf e (u j)) → (∀ n, IsHalf e (y n)) → ∑ i ∈ S, x i * ((∏ j, ((d i).1 j).fn (u j)) * ∏ n, ((d i).2 n).fn (y n)) = 0) → ∀ C, IsRealFam ch.W C → ∀ u y, ∑ i ∈ S, x i * evT (combC ch.W (c i) C) (combR ch.rm (c i)) u y = 0 :=
  ⟨0, fun _ _ _ => ⟨0, fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ch _ _ t e _ I S x d c hd h C hC u y =>
    sum_evT_eq_zero ch.W ch.rm t e I S x d c hd h C hC u y⟩⟩

end GlobalTheory.CombDet
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestCombinationDependsOnProductFunctionStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.rowTest_combination_depends_on_product_function : Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ t e, IsIdemSum e (locPl ch.G t) → ∀ (I : Type) (S : Finset I) (x : I → ℂ) (d : I → PureDat ch.G t) (c : I → Combs ch.G), (∀ i ∈ S, (∀ j : Fin D.R.m, ((d i).1 j).e = e ∧ IsCombOf ch.W ((d i).1 j) ((c i).1 j)) ∧ ∀ n, ((d i).2 n).e = e ∧ IsCombOf ch.W ((d i).2 n) ((c i).2 n)) → (∀ (u : ∀ j : Fin D.R.m, WO (ch.G.V (.top j)) (ch.G.V (.top (j + 1)))) (y : RowPt ch.G), (∀ j, IsHalf e (u j)) → (∀ n, IsHalf e (y n)) → ∑ i ∈ S, x i * ((∏ j, ((d i).1 j).fn (u j)) * ∏ n, ((d i).2 n).fn (y n)) = 0) → ∀ C, IsRealFam ch.W C → ∀ u y, ∑ i ∈ S, x i * evT (combC ch.W (c i) C) (combR ch.rm (c i)) u y = 0 := by
  first | exact @GlobalTheory.CombDet.comb_det | exact GlobalTheory.CombDet.comb_det | (intros; apply GlobalTheory.CombDet.comb_det <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatDictionaryRelativeBaseVacuaLargeDepth

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal

namespace GlobalTheory.LocAsm

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw



open Classical in
theorem locAt_of_placeAt : Big fun ch => ∀ s, PlaceAt ch s → ConLin ch → LocAt ch s := by
  refine big_mono ?_ (Big.and GlobalTheory.T.flippedFiniteTensor_sum_prod_local_pure_tensors (Big.and GlobalTheory.T.localPureTensor_product_expansion_all_places (Big.and GlobalTheory.T.unfoldedVacuaAreRealDatum_largeDepth GlobalTheory.T.rowTest_combination_depends_on_product_function)))
  intro D Γ _ _ Pl0 T A Ks _ _ _ R ch h s hP hcon
  obtain ⟨hR, hS, hV, hC⟩ := h
  obtain ⟨κ, z, hz, hκ, hPl⟩ := (placeAt_iff ch s).1 hP
  refine ⟨∏ w ∈ ch.G.pl.W0, κ w, fun t => ∏ w ∈ locPl ch.G t, z t w, fun t => Subgroup.prod_mem _ fun w _ => hz t w, ?_⟩
  intro t Φ τ hτ M hM β b b₀ hb hb₀ τ' c hτ' hc
  have hζ : ∀ w : locPl ch.G t, ∃ ζ : ℂ, ((w.1 ∈ ch.G.pl.W0 → ∀ i, β w i = DoubleCoset.mk _ _
      (stair (locGrid ch.G t w.1) (unifAt w.1) (cosExp ch.G w.1) (i + 1))) → ζ = κ w.1 * (z t w.1 : ℂ)⁻¹) ∧
      PlaceCl ch s t w.1 (β w) ζ := fun w => hPl t w.1 w.2 (β w)
  choose ζ hζ1 hζ2 using hζ
  refine ⟨∏ w, ζ w, fun hst => ?_, ?_⟩
  · have e1 : ∀ w : locPl ch.G t, ζ w = κ w.1 * (z t w.1 : ℂ)⁻¹ := fun w => hζ1 w (hst w)
    rw [Finset.prod_congr rfl fun w _ => e1 w, Finset.prod_mul_distrib]
    congr 1
    · rw [Finset.prod_coe_sort (locPl ch.G t) κ]
      exact (Finset.prod_subset Finset.subset_union_left fun w _ hw => hκ w hw).symm
    · rw [Finset.prod_coe_sort (locPl ch.G t) (fun w => ((z t w : ℂ))⁻¹), Units.coe_prod, Finset.prod_inv_distrib]
  · intro P p hp u y
    obtain ⟨e, he, hτe, hτ'p⟩ := hτ'
    obtain ⟨α, SA, xA, φ, fd, fr, hnat, hvec, hflat, hlhs⟩ := hR hcon t Φ τ hτ β e he
    have hS' : ∀ a ∈ SA, ∃ σ : (PureDat ch.G t × Combs ch.G) →₀ ℂ, _ := fun a ha =>
      hS s t β ζ hζ2 M hM b b₀ hb hb₀ e he (φ a) (hnat a ha) (fd a) (fr a) (hvec a ha).1 (hvec a ha).2
    choose! σ hσ1 hσ2 hσ3 using hS'
    set C₀ := conAt ch.W hM (fockD ch.W t (fun j => ch.rm.vT D.R.m j) P) (p * b₀) with hC₀
    set μ : (PureDat ch.G t × Combs ch.G) →₀ ℂ := τ'.mapDomain (fun d => (d, c d)) - ∑ a ∈ SA, xA a • σ a with hμ
    have hL : ∀ G : PureDat ch.G t × Combs ch.G → ℂ, ∑ i ∈ μ.support, μ i * G i =
        (τ'.sum fun d x => x * G (d, c d)) - ∑ a ∈ SA, xA a * (σ a).sum fun k x => x * G k := fun G => by
      have e1 : ∀ {ι : Type} (G' : ι → ℂ) (ν : ι →₀ ℂ), Finsupp.linearCombination ℂ G' ν = ν.sum fun k x => x * G' k :=
        fun G' ν => by rw [Finsupp.linearCombination_apply]; rfl
      have e2 : ∑ i ∈ μ.support, μ i * G i = Finsupp.linearCombination ℂ G μ := by rw [e1]; rfl

      rw [e2, hμ, map_sub, map_sum, Finsupp.linearCombination_mapDomain, e1]
      congr 1
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [map_smul, e1, smul_eq_mul]
    have hsupp : ∀ i ∈ μ.support, (∀ j : Fin D.R.m, (i.1.1 j).e = e ∧ IsCombOf ch.W (i.1.1 j) (i.2.1 j)) ∧
        ∀ n, (i.1.2 n).e = e ∧ IsCombOf ch.W (i.1.2 n) (i.2.2 n) := by
      intro i hi
      rcases Finset.mem_union.1 (Finsupp.support_sub hi) with h1 | h2
      · obtain ⟨d, hd, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support h1)
        exact ⟨fun j => ⟨((hτe d hd).1 j).2.1, (hc d hd).1 j⟩, fun n => ⟨((hτe d hd).2 n).2.1, (hc d hd).2 n⟩⟩
      · have hex : ∃ a ∈ SA, i ∈ (xA a • σ a).support := by
          by_contra hn
          push_neg at hn
          have hz : (∑ a ∈ SA, xA a • σ a) i = 0 := by
            simp only [Finset.sum_apply']
            apply Finset.sum_eq_zero
            intro a ha
            exact Finsupp.notMem_support_iff.mp (hn a ha)
          exact (Finsupp.mem_support_iff.mp h2) hz
        obtain ⟨a, ha, hi'⟩ := hex
        exact hσ1 a ha i (Finsupp.support_smul hi')
    have hzero := hC t e he (PureDat ch.G t × Combs ch.G) μ.support μ Prod.fst Prod.snd hsupp (fun u' y' hu hy => by
      rw [hL]
      have h1 := hτ'p u' y' hu hy
      have h2 := hflat u' y' hu hy
      rw [sub_eq_zero, Finset.sum_congr rfl fun a ha => by rw [hσ2 a ha u' y' hu hy], ← h2, ← h1]
      refine Finsupp.sum_congr fun d _ => ?_
      ring) C₀ (hV t M hM b₀ hb₀ P p hp) u y
    rw [hL, sub_eq_zero] at hzero
    rw [hlhs M hM P (p * b) u y, Finset.sum_congr rfl fun a ha => by rw [hσ3 a ha P p hp u y], hzero, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    ring

end GlobalTheory.LocAsm

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatDictionaryRelativeBaseVacuaLargeDepthStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.flat_dictionary_relative_base_vacua_large_depth : Big fun ch => ∀ s, PlaceAt ch s → ConLin ch → LocAt ch s := by
  first | exact @GlobalTheory.LocAsm.locAt_of_placeAt | exact GlobalTheory.LocAsm.locAt_of_placeAt | (intros; apply GlobalTheory.LocAsm.locAt_of_placeAt <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatDictionaryBaseVacuaLargeDepth

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowVal

theorem exists_locAt_big : Big fun ch => ∃ s, LocAt ch s :=
  GlobalTheory.RowReal.big_mono (fun ch h => by
               obtain ⟨⟨⟨s, hP⟩, hC⟩, hL⟩ := h
               exact ⟨s, hL s hP hC⟩)
    (Big.and (Big.and GlobalTheory.T.exists_sign_flatDictionaryAtOnePlace_largeDepth GlobalTheory.T.unfoldedProduct_depends_on_dataProduct) GlobalTheory.T.flat_dictionary_relative_base_vacua_large_depth)

end GlobalTheory.RowVal
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatDictionaryBaseVacuaLargeDepthStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.flat_dictionary_base_vacua_large_depth : Big fun ch => ∃ s, LocAt ch s := by
  first | exact @GlobalTheory.RowVal.exists_locAt_big | exact GlobalTheory.RowVal.exists_locAt_big | (intros; apply GlobalTheory.RowVal.exists_locAt_big <;> assumption)
end
end
