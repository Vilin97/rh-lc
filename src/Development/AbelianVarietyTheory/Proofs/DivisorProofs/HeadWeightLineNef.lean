module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExOfHeadWt
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InterNumDetNonposSplitTorus
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsChartOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsIsoQuotToImOmegaLieOfSplit
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLatticeCoordinatesStep
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LbIsoDetAffDetOm
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocallyFreeSubsheafDetIsoStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoToBidualOfLocalFrames
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LineBundleSpreadsOutFromGenericFibreProper
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Data.Nat.Choose.Multinomial
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLieBundleFramesChartsChangeBasis

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic
open Formalism.L2.Pj
open GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.GrCl GlobalTheory.Reg GlobalTheory.FlagMod
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.Twist (resM resM_resM)

namespace GlobalTheory.ChartLieFrame

theorem eq_of_loc {Z : Scheme.{0}} {W : Z.Opens} {a b : Γ(Z, W)}
    (h : ∀ p ∈ W, ∃ (N : Z.Opens) (e : N ≤ W), p ∈ N ∧ resG Z e a = resG Z e b) : a = b :=
  ext_ev_loc fun p hp => by
    obtain ⟨N, e, hpN, hab⟩ := h p hp
    exact ⟨N, hpN, fun S _ z hz hN => by rw [← ev_res z e hN hz a, ← ev_res z e hN hz b, hab]⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {Y : Model Xo c β}

def Rep (M : MChart Y) (j : Fin M.n) {U : Y.X.Opens} (hU : U ≤ M.U) (s : Γ(GlobalTheory.LieVB.Lie Y.t.G, U)) : Prop :=
  ∀ (W : Y.X.Opens) (hW : IsAffineOpen W) (h : W ≤ U) (w : Γ(GlobalTheory.LieVB.omega Y.t.G, W)),
    VB.dualApp s h w = tanEv Y.t (isTan_tv (lieBasis M (tau hW) (tau_le hW (h.trans hU)) j)) (tau_le hW le_rfl) w

theorem tanLin_res (M : MChart Y) {W W₀ V : Y.X.Opens} (hW : IsAffineOpen W) (hW₀ : IsAffineOpen W₀) (e : W ≤ W₀)
    (hM : W₀ ≤ M.U) (hV : W₀ ≤ V) {n : ℕ} (s : Fin n → Γ(GlobalTheory.LieVB.omega Y.t.G, V)) (j : Fin M.n) :
    tanLin Y.t (tau_le hW (e.trans hV)) s (lieBasis M (tau hW) (tau_le hW (e.trans hM)) j) =
      fun i => resG Y.X e (tanLin Y.t (tau_le hW₀ hV) s (lieBasis M (tau hW₀) (tau_le hW₀ hM) j) i) := by
  have φe : spMap (ev (tau hW) W₀ (tau_le hW e)) ≫ tau hW₀ = tau hW := spMap_ev (tau hW) hW₀ (tau_le hW e)
  rw [← tanPull_lieBasis M _ φe (tau_le hW₀ hM) (tau_le hW (e.trans hM)) j,
    tanLin_tanPull Y.t _ φe (tau_le hW₀ hV) (tau_le hW (e.trans hV))]
  funext i
  exact ev_tau hW e (tau_le hW e) _

theorem tanEv_res (M : MChart Y) {W W₀ : Y.X.Opens} (hW : IsAffineOpen W) (hW₀ : IsAffineOpen W₀) (e : W ≤ W₀)
    (hM : W₀ ≤ M.U) (w : Γ(GlobalTheory.LieVB.omega Y.t.G, W₀)) (j : Fin M.n) :
    tanEv Y.t (isTan_tv (lieBasis M (tau hW) (tau_le hW (e.trans hM)) j)) (tau_le hW le_rfl) (resM _ e w) =
      resG Y.X e (tanEv Y.t (isTan_tv (lieBasis M (tau hW₀) (tau_le hW₀ hM) j)) (tau_le hW₀ le_rfl) w) := by
  rw [tanEv_resM]
  exact congrFun (tanLin_res M hW hW₀ e hM le_rfl ![w] j) 0

theorem Rep.res {M : MChart Y} {j : Fin M.n} {U : Y.X.Opens} {hU : U ≤ M.U} {s : Γ(GlobalTheory.LieVB.Lie Y.t.G, U)}
    (hs : Rep M j hU s) {U' : Y.X.Opens} (e : U' ≤ U) : Rep M j (e.trans hU) (resM _ e s) := fun W hW h w => by
  rw [VB.dualApp_res]
  exact hs W hW (h.trans e) w

theorem rep_unique (M : MChart Y) (j : Fin M.n) {U : Y.X.Opens} (hU : U ≤ M.U) {s s' : Γ(GlobalTheory.LieVB.Lie Y.t.G, U)}
    (hs : Rep M j hU s) (hs' : Rep M j hU s') : s = s' :=
  VB.dual_ext fun W h w => eq_of_loc fun p hp => by
    obtain ⟨N, hN, hpN, hNW'⟩ := exists_isAffineOpen_mem_and_subset (x := p) (U := W) hp
    have hNW : N ≤ W := hNW'
    refine ⟨N, hNW, hpN, ?_⟩
    rw [← VB.dualApp_resM, ← VB.dualApp_resM, hs N hN, hs' N hN]

theorem rep_of_cover (M : MChart Y) (j : Fin M.n) {U : Y.X.Opens} (hU : U ≤ M.U) {ι : Type} (V : ι → Y.X.Opens)
    (hV : ∀ k, V k ≤ U) (hc : U ≤ iSup V) (s : Γ(GlobalTheory.LieVB.Lie Y.t.G, U))
    (H : ∀ k, Rep M j ((hV k).trans hU) (resM _ (hV k) s)) : Rep M j hU s := fun W hW h w =>
  eq_of_loc fun p hp => by
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 (hc (h hp))
    obtain ⟨N, hN, hpN, hNW⟩ := exists_isAffineOpen_mem_and_subset (x := p) (U := W ⊓ V k) ⟨hp, hk⟩
    have eW : N ≤ W := fun q hq => (hNW hq).1
    have eV : N ≤ V k := fun q hq => (hNW hq).2
    refine ⟨N, eW, hpN, ?_⟩
    rw [← VB.dualApp_resM, ← tanEv_res M hN hW eW (h.trans hU) w j]
    have := H k N hN eV (resM _ eW w)
    rw [VB.dualApp_res] at this
    exact this

def locSec (M : MChart Y) (j : Fin M.n) {n : ℕ} (C : VB.Chart (GlobalTheory.LieVB.omega Y.t.G) n) (hC : IsAffineOpen C.U)
    (hM : C.U ≤ M.U) : Γ(GlobalTheory.LieVB.Lie Y.t.G, C.U) :=
  ∑ i : Fin n, (tanLin Y.t (tau_le hC le_rfl) C.e (lieBasis M (tau hC) (tau_le hC hM) j) i : Γ(Y.X, C.U)) •
    (C.isFrame.coord i : Γ(GlobalTheory.LieVB.Lie Y.t.G, C.U))

theorem rep_locSec (M : MChart Y) (j : Fin M.n) {n : ℕ} (C : VB.Chart (GlobalTheory.LieVB.omega Y.t.G) n)
    (hC : IsAffineOpen C.U) (hM : C.U ≤ M.U) : Rep M j hM (locSec M j C hC hM) := fun W hW h w => by
  rw [locSec, VB.dualApp_sum]
  simp only [VB.dualApp_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    VB.IsFrame.dualApp_coord, smul_eq_mul]
  conv_rhs => rw [← (C.isFrame.basis h).sum_repr w]
  rw [tanEv_sum_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [VB.IsFrame.basis_apply, tanEv_resM, ev_tau_self, RingHom.id_apply, _root_.mul_comm]
  exact congrArg (((C.isFrame.basis h).repr w i) * ·) (congrFun (tanLin_res M hW hC h hM le_rfl C.e j) i).symm

theorem exists_rep (M : MChart Y) (j : Fin M.n) : ∃ s : Γ(GlobalTheory.LieVB.Lie Y.t.G, M.U), Rep M j le_rfl s := by
  haveI := Y.t.semi
  haveI := Y.t.semi.smooth
  let V : (Σ n : ℕ, {C : VB.Chart (GlobalTheory.LieVB.omega Y.t.G) n // IsAffineOpen C.U ∧ C.U ≤ M.U}) → Y.X.Opens :=
    fun k => k.2.1.U
  have hV : ∀ k, V k ≤ M.U := fun k => k.2.2.2
  have hc : M.U ≤ iSup V := fun p hp => by
    obtain ⟨U₀, n, e, hp₀, he⟩ := GlobalTheory.LieVB.exists_isFrame_omega Y.t.G p
    obtain ⟨N, hN, hpN, hNU⟩ := exists_isAffineOpen_mem_and_subset (x := p) (U := M.U ⊓ U₀) ⟨hp, hp₀⟩
    have e₁ : N ≤ M.U := fun q hq => (hNU hq).1
    have e₂ : N ≤ U₀ := fun q hq => (hNU hq).2
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨n, ⟨⟨N, fun i => resM _ e₂ (e i), he.res e₂⟩, hN, e₁⟩⟩, hpN⟩
  have hrep : ∀ k, Rep M j (hV k) (locSec M j k.2.1 k.2.2.1 k.2.2.2) := fun k => rep_locSec M j _ _ _
  obtain ⟨t, ht⟩ := Twist.exists_sec_of_cover V hV hc (fun k => locSec M j k.2.1 k.2.2.1 k.2.2.2) fun k k' =>
    rep_unique M j (inf_le_left.trans (hV k)) ((hrep k).res inf_le_left) ((hrep k').res inf_le_right)
  exact ⟨t, rep_of_cover M j le_rfl V hV hc t fun k => by rw [ht k]; exact hrep k⟩

theorem isFrame_of_rep (M : MChart Y) (f : Fin M.n → Γ(GlobalTheory.LieVB.Lie Y.t.G, M.U)) (hf : ∀ j, Rep M j le_rfl (f j)) :
    VB.IsFrame f := by
  haveI := Y.t.semi
  haveI := Y.t.semi.smooth
  refine VB.isFrame_of_forall_exists fun V h p hp => ?_
  obtain ⟨U₀, n, e, hp₀, he⟩ := GlobalTheory.LieVB.exists_isFrame_omega Y.t.G p
  obtain ⟨W, hW, hpW, hWU⟩ := exists_isAffineOpen_mem_and_subset (x := p) (U := V ⊓ U₀) ⟨hp, hp₀⟩
  have e₁ : W ≤ V := fun q hq => (hWU hq).1
  have e₂ : W ≤ U₀ := fun q hq => (hWU hq).2
  let C : VB.Chart (GlobalTheory.LieVB.omega Y.t.G) n := ⟨W, fun i => resM _ e₂ (e i), he.res e₂⟩
  refine ⟨W, e₁, hpW, ?_⟩
  let R := (C.isFrame.dual.basis (le_rfl : C.U ≤ C.U)).equivFun
  let T : (Fin M.n → Γ(Y.X, W)) → (Fin n → Γ(Y.X, W)) :=
    (tanLin Y.t (tau_le hW (le_rfl : W ≤ C.U)) C.e) ∘ (lieBasis M (tau hW) (tau_le hW (e₁.trans h))).equivFun.symm
  have hT : Function.Bijective T :=
    (HodgeCech.tanLin_bijective Y.t C (tau hW) (tau_le hW le_rfl)).comp (LinearEquiv.bijective _)
  have key : ∀ a, R (Fintype.linearCombination Γ(Y.X, W) (fun j => resM _ (e₁.trans h) (f j)) a) = T a := by
    intro a
    funext i

    simp only [R, T, Function.comp_apply, Module.Basis.equivFun_apply, VB.IsFrame.dual_basis_repr,
    Fintype.linearCombination_apply, VB.dualApp_sum, LinearMap.sum_apply, VB.dualApp_smul, LinearMap.smul_apply,
    VB.dualApp_res, Module.Basis.equivFun_symm_apply, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, GlobalTheory.LB.resG_self]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hf k W hW _ _, GlobalTheory.Twist.resM_self]
    rfl
  have hc : R ∘ (Fintype.linearCombination Γ(Y.X, W) (fun j => resM _ (e₁.trans h) (f j))) = T := funext key
  exact (Function.Bijective.of_comp_iff' R.bijective _).1 (hc ▸ hT)

theorem rep_chg (M M' : MChart Y) (f : Fin M.n → Γ(GlobalTheory.LieVB.Lie Y.t.G, M.U)) (hf : ∀ i, Rep M i le_rfl (f i))
    (j : Fin M'.n) :
    Rep M' j inf_le_right (∑ i, chg M M' i j • resM _ (inf_le_left : M.U ⊓ M'.U ≤ M.U) (f i)) := fun W hW h w => by
  have ev' : ∀ v, tanEv Y.t (isTan_tv v) (tau_le hW le_rfl) w = tanLin Y.t (tau_le hW le_rfl) ![w] v 0 := fun v => rfl
  rw [VB.dualApp_sum]
  simp only [VB.dualApp_smul, LinearMap.sum_apply, LinearMap.smul_apply, VB.dualApp_res, smul_eq_mul]

  rw [ev', ← (lieBasis M (tau hW) (tau_le hW (h.trans inf_le_left))).sum_toMatrix_smul_self
  (lieBasis M' (tau hW) (tau_le hW (h.trans inf_le_right))) j, map_sum]
  rw [Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, Pi.smul_apply, smul_eq_mul, hf i W hW (h.trans inf_le_left) w, ev']
  refine congrArg₂ (· * ·) ?_ rfl
  rw [← chg_map M M' (tau hW) (tau_le hW (h.trans inf_le_left)) (tau_le hW (h.trans inf_le_right)) (tau_le hW h),
    Matrix.map_apply, ev_tau hW h]

theorem exists_lieFrame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β), ∃ f : ∀ M : GlobalTheory.Reg.MChart Y, Fin M.n → Γ(GlobalTheory.LieVB.Lie Y.t.G, M.U), (∀ M, GlobalTheory.VB.IsFrame (f M)) ∧ ∀ (M M' : GlobalTheory.Reg.MChart Y) (j : Fin M'.n), GlobalTheory.Twist.resM _ (inf_le_right : M.U ⊓ M'.U ≤ M'.U) (f M' j) = ∑ i, GlobalTheory.FlagMod.chg M M' i j • GlobalTheory.Twist.resM _ (inf_le_left : M.U ⊓ M'.U ≤ M.U) (f M i) := by
  intro E _ _ _ H Dw l Xo c O _ β Y
  choose f hf using fun (M : MChart Y) (j : Fin M.n) => exists_rep M j
  exact ⟨f, fun M => isFrame_of_rep M (f M) (hf M), fun M M' j =>
    rep_unique M' j inf_le_right ((hf M' j).res inf_le_right) (rep_chg M M' (f M) (hf M) j)⟩

end GlobalTheory.ChartLieFrame
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLieBundleFramesChartsChangeBasisStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic
open Formalism.L2.Pj

theorem _root_.GlobalTheory.T.exists_lieBundle_frames_charts_change_basis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β), ∃ f : ∀ M : GlobalTheory.Reg.MChart Y, Fin M.n → Γ(GlobalTheory.LieVB.Lie Y.t.G, M.U), (∀ M, GlobalTheory.VB.IsFrame (f M)) ∧ ∀ (M M' : GlobalTheory.Reg.MChart Y) (j : Fin M'.n), GlobalTheory.Twist.resM _ (inf_le_right : M.U ⊓ M'.U ≤ M'.U) (f M' j) = ∑ i, GlobalTheory.FlagMod.chg M M' i j • GlobalTheory.Twist.resM _ (inf_le_left : M.U ⊓ M'.U ≤ M.U) (f M i) := by
  first | exact @GlobalTheory.ChartLieFrame.exists_lieFrame | exact GlobalTheory.ChartLieFrame.exists_lieFrame | (intros; apply GlobalTheory.ChartLieFrame.exists_lieFrame <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsLBOfChartPull

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad

namespace GlobalTheory.NefFibre

theorem isLB_of_chartPull {Y : Scheme.{0}} {A M : LB Y} (a : ChartPull A M (𝟙 Y)) (hM : M.IsLB)
    (hc : ∀ y : Y, ∃ i, y ∈ A.U i) : A.IsLB := by
  refine GlobalTheory.GenSpread.isLB_of_gm A hc ?_
  intro y i j k hi hj hk
  have hi' : y ∈ M.U (a.idx i) := a.le i hi
  have hj' : y ∈ M.U (a.idx j) := a.le j hj
  have hk' : y ∈ M.U (a.idx k) := a.le k hk
  rw [a.g y i j hi hj, a.g y j k hj hk, a.g y i k hi hk]
  exact gm_cocycle hM (𝟙 Y) y hi' hj' hk'

end GlobalTheory.NefFibre
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeadWeightLineNef

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi)
open GlobalTheory.HSApp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.NefHodge

def chartwise {X C : Scheme.{0}} (A : LB X) (g : C ⟶ X) : LB C :=
  ⟨A.ι, fun k => g ⁻¹ᵁ A.U k, fun k k' => pullU g (A.U k ⊓ A.U k') (A.g k k')⟩

theorem isLB_chartwise {X C : Scheme.{0}} {A : LB X} (hA : A.IsLB) (g : C ⟶ X) :
    (chartwise A g).IsLB ∧ LBIso (chartwise A g) (A.pull g) := by
  let a : ChartPull (chartwise A g) (A.pull g) (𝟙 C) :=
    ⟨fun k _ => k, fun k y hy => mem_pull.2 hy, fun y k k' hk hk' =>
      (gm_pull (𝟙 C) g y (A.U k ⊓ A.U k') ⟨hk, hk'⟩ _).trans
        (gm_pull_g A g (𝟙 C) y (fun _ => k) (fun _ => k') (mem_pull.2 hk) (mem_pull.2 hk')).symm⟩
  refine ⟨NefFibre.isLB_of_chartPull a (LB.isLB_pull hA g) fun y => ?_, iso_of_chart (LB.isLB_pull hA g) a⟩
  exact (Opens.mem_iSup (s := A.U)).1 (hA.cover.ge (Set.mem_univ (g y)))


open GlobalTheory.VB GlobalTheory.DualPull in
theorem isIso_theta_of_frames {X C : Scheme.{0}} {F : X.Modules} (g : C ⟶ X)
    (h : ∀ x : X, ∃ (U : X.Opens) (n : ℕ) (e : Fin n → Γ(F, U)), x ∈ U ∧ IsFrame e) : IsIso (theta g F) := by
  have := OmegaGlobal.isQuasicoherent_of_frames h
  have : (VB.dual F).IsQuasicoherent := OmegaGlobal.isQuasicoherent_of_frames fun x =>
    have ⟨U, n, _, hx, he⟩ := h x
    ⟨U, n, _, hx, he.dual⟩
  choose U n e hx he using h
  refine Twist.isIso_of_cover _ (U := fun y => g ⁻¹ᵁ U (g y))
    (top_le_iff.1 fun y _ => Opens.mem_iSup.2 ⟨y, hx (g y)⟩) fun y W hW => ?_
  have H (i : Fin (n (g y))) : (theta g F).app _ (QCoh.pullbackSections g (VB.dual F) (le_refl (g ⁻¹ᵁ U (g y)))
      ((he (g y)).coord i)) = ((he (g y)).pullback g).coord i :=
    dual_pull_ext g le_rfl fun W hW S hS e' s => by
      rw [dualApp_theta g _ hW, IsFrame.dualApp_coord, IsFrame.dualApp_coord]
      exact ((he (g y)).pullback_basis_repr g hW e' s i).symm
  have : QCoh.appLinear (theta g F) W =
      (((he (g y)).dual.pullback g).equiv ((he (g y)).pullback g).dual hW).toLinearMap :=
    (((he (g y)).dual.pullback g).basis hW).ext fun i => by
      rw [IsFrame.basis_apply, LinearEquiv.coe_coe, IsFrame.equiv_resM_frame, ← H]
      exact Twist.app_resM (theta g F) hW _
  rw [← QCoh.coe_appLinear, this]
  exact LinearEquiv.bijective _

section Step

open GlobalTheory.FlagMod GlobalTheory.Reg GlobalTheory.VB GlobalTheory.LieVB
open GlobalTheory.Twist (resM)
open GlobalTheory.QCoh (pullbackSections)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
  {Z C : Scheme.{0}} {π : Z ⟶ Y.X} (F : Frames Y π) (g : C ⟶ Z) (σ : E →+* ℂ)
  (f : ∀ M : MChart Y, Fin M.n → Γ(Lie Y.t.G, M.U))

theorem le_chart {k : F.J} {V : C.Opens} (h : V ≤ g ⁻¹ᵁ F.U k) : V ≤ (g ≫ π) ⁻¹ᵁ (F.M k).U :=
  fun _ hx => F.le k (h hx)

def vecSec (k : F.J) (V : C.Opens) (h : V ≤ g ⁻¹ᵁ F.U k) (i : Fin (Dw.mult σ)) :
    Γ((Scheme.Modules.pullback (g ≫ π)).obj (Lie Y.t.G), V) :=
  ∑ a, g.appLE (F.U k) V h (F.u k σ a i) • pullbackSections (g ≫ π) _ (le_chart F g h) (f (F.M k).toMChart a)

theorem resM_vecSec (k : F.J) {V V' : C.Opens} (h : V ≤ g ⁻¹ᵁ F.U k) (h' : V' ≤ V) (i : Fin (Dw.mult σ)) :
    resM _ h' (vecSec F g σ f k V h i) = vecSec F g σ f k V' (h'.trans h) i := by

  rw [vecSec, vecSec, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Twist.resM_smul, DualPull.resG_appLE]
  exact congrArg _ (QCoh.res_pullbackSections _ _ _ _ _)

theorem linearIndependent_vecSec (hf : ∀ M, IsFrame (f M)) (k : F.J) {V : C.Opens} (h : V ≤ g ⁻¹ᵁ F.U k) :
    LinearIndependent Γ(C, V) (vecSec F g σ f k V h) := by
  have := Y.t.semi
  have := Y.t.semi.smooth
  have : (Lie Y.t.G).IsQuasicoherent := OmegaGlobal.isQuasicoherent_of_frames fun x =>
    have ⟨U, n, _, hx, he⟩ := exists_isFrame_omega Y.t.G x
    ⟨U, n, _, hx, he.dual⟩
  let b := ((hf (F.M k).toMChart).pullback (g ≫ π)).basis (le_chart F g h)
  have hb : ∀ a, b a = pullbackSections (g ≫ π) _ (le_chart F g h) (f (F.M k).toMChart a) := fun a =>
    (IsFrame.basis_apply _ _ a).trans (QCoh.res_pullbackSections _ _ _ _ _)
  obtain ⟨w, hw⟩ := F.split k σ
  rw [Fintype.linearIndependent_iff]
  intro a ha
  simp only [vecSec, ← hb, Finset.smul_sum, smul_smul] at ha
  rw [Finset.sum_comm] at ha
  simp only [← Finset.sum_smul] at ha
  have h₁ : ((F.u k σ).map (g.appLE (F.U k) V h).hom).mulVec a = 0 := funext fun j =>
    show ∑ i, g.appLE (F.U k) V h (F.u k σ j i) * a i = 0 from
    Eq.trans (Finset.sum_congr rfl fun i _ => _root_.mul_comm _ _)
      (Fintype.linearIndependent_iff.1 b.linearIndependent _ ha j)
  have h₂ := congrArg (w.map (g.appLE (F.U k) V h).hom).mulVec h₁
  rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, hw, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec,
    Matrix.mulVec_zero] at h₂
  exact congrFun h₂

theorem vecSec_chg (hc : ∀ (M M' : MChart Y) (j : Fin M'.n), resM _ (inf_le_right : M.U ⊓ M'.U ≤ M'.U) (f M' j) =
      ∑ i, chg M M' i j • resM _ (inf_le_left : M.U ⊓ M'.U ≤ M.U) (f M i))
    (k k' : F.J) {V : C.Opens} (h : V ≤ g ⁻¹ᵁ F.U k) (h' : V ≤ g ⁻¹ᵁ F.U k') (hh : V ≤ g ⁻¹ᵁ (F.U k ⊓ F.U k'))
    (i : Fin (Dw.mult σ)) : vecSec F g σ f k' V h' i =
      ∑ j, g.appLE _ V hh (F.B k k' σ j i) • vecSec F g σ f k V h j := by
  have hM : V ≤ (g ≫ π) ⁻¹ᵁ ((F.M k).U ⊓ (F.M k').U) := fun _ hx => ⟨le_chart F g h hx, le_chart F g h' hx⟩
  have e₁ : ∀ a, pullbackSections (g ≫ π) _ (le_chart F g h') (f (F.M k').toMChart a) =
      ∑ b, (g ≫ π).appLE _ V hM (chg (F.M k).toMChart (F.M k').toMChart b a) •
        pullbackSections (g ≫ π) _ (le_chart F g h) (f (F.M k).toMChart b) := fun a => by
    have := congrArg (pullbackSections (g ≫ π) _ hM) (hc (F.M k).toMChart (F.M k').toMChart a)

    rw [map_sum] at this
    refine ((QCoh.pullbackSections_res _ _ _ _ _).symm.trans this).trans (Finset.sum_congr rfl fun b _ => ?_)
    rw [QCoh.pullbackSections_smul]
    exact congrArg _ (QCoh.pullbackSections_res _ _ _ _ _)
  have e₂ : ∀ b, ∑ a, g.appLE _ V h' (F.u k' σ a i) *
      (g ≫ π).appLE _ V hM (chg (F.M k).toMChart (F.M k').toMChart b a) =
      ∑ j, g.appLE _ V hh (F.B k k' σ j i) * g.appLE _ V h (F.u k σ b j) := fun b => by
    have e₀ : ∑ a, π.appLE ((F.M k).U ⊓ (F.M k').U) (F.U k ⊓ F.U k') (inf_le_inf (F.le k) (F.le k'))
        (chg (F.M k).toMChart (F.M k').toMChart b a) * resG Z inf_le_right (F.u k' σ a i) =
        ∑ j, resG Z inf_le_left (F.u k σ b j) * F.B k k' σ j i :=
      congrFun (congrFun (F.tri k k' σ).choose_spec.2 b) i
    have := congrArg (g.appLE _ V hh).hom e₀

    rw [map_sum, map_sum] at this
    refine (Finset.sum_congr rfl fun a _ => ?_).trans (this.trans (Finset.sum_congr rfl fun j _ => ?_))
    · rw [_root_.mul_comm, map_mul, ← Scheme.Hom.appLE_comp_appLE g π _ _ V (inf_le_inf (F.le k) (F.le k')) hh]
      exact congrArg₂ (· * ·) rfl (DualPull.appLE_resG g _ hh _).symm
    · rw [map_mul, _root_.mul_comm]
      exact congrArg₂ (· * ·) rfl (DualPull.appLE_resG g _ hh _)
  simp only [vecSec, e₁, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm, Finset.sum_comm (s := (Finset.univ : Finset (Fin (Dw.mult σ))))]
  simp only [← Finset.sum_smul, e₂]


open Classical in
theorem val_dual_LL_stepEx {j : ℕ} (hj : j ≤ Dw.mult σ) (k k' : F.J) :
    ((CechPic.dual (F.LL (NefStep.stepEx σ j))).g k k').val =
      ((F.B k k' σ).submatrix (Fin.castLE hj) (Fin.castLE hj)).det := by
  have ht : ((F.B k k' σ).submatrix (Fin.castLE hj) (Fin.castLE hj)).BlockTriangular id := fun a b h =>
    F.B_tri k k' σ (show Fin.castLE hj b < Fin.castLE hj a from h)
  rw [Matrix.det_of_upperTriangular ht]
  change ((∏ ix, F.T k k' ix ^ (-NefStep.stepEx σ j ix))⁻¹).val = _
  have e : (∏ ix, F.T k k' ix ^ (-NefStep.stepEx σ j ix))⁻¹ = ∏ i : Fin j, F.T k k' (some ⟨σ, Fin.castLE hj i⟩) := by
    rw [← Finset.prod_inv_distrib]
    refine (Finset.prod_of_injOn (fun i : Fin j => (some ⟨σ, Fin.castLE hj i⟩ : Ix Dw)) (fun a _ b _ h => ?_)
      (fun _ _ => Finset.mem_univ _) (fun ix _ h => ?_) fun i _ => ?_).symm
    · exact Fin.castLE_injective hj (eq_of_heq (Sigma.mk.inj (Option.some.inj h)).2)
    · have : NefStep.stepEx σ j ix = 0 := by
        rcases ix with _ | ⟨σ', i⟩
        · rfl
        · refine if_neg ?_
          rintro ⟨rfl, hi⟩
          exact h ⟨⟨i, hi⟩, Finset.mem_coe.2 (Finset.mem_univ _), rfl⟩
      rw [this, neg_zero, zpow_zero, inv_one]
    · have : NefStep.stepEx σ j (some ⟨σ, Fin.castLE hj i⟩ : Ix Dw) = 1 := if_pos ⟨rfl, i.2⟩
      rw [this, zpow_neg_one, inv_inv]
  rw [e, Units.coe_prod]
  rfl

theorem exists_step {j : ℕ} (hj : j ≤ Dw.mult σ) :
    ∃ (W : C.Modules) (ι : W ⟶ (Scheme.Modules.pullback (g ≫ π)).obj (Lie Y.t.G)), Mono ι ∧ IsVB W j ∧
      LBIso (chartwise (CechPic.dual (F.LL (NefStep.stepEx σ j))) g) (det W j) := by
  obtain ⟨f, hf, hc⟩ := GlobalTheory.T.exists_lieBundle_frames_charts_change_basis E H Dw l Xo c O β Y
  refine GlobalTheory.T.exists_locallyFree_subsheaf_det_iso C _ j _ (isLB_chartwise (isLB_dual (F.isLB_LL _)) g).1
    (fun k i => vecSec F g σ f k (g ⁻¹ᵁ F.U k) le_rfl (Fin.castLE hj i))
    (fun k k' => ((F.B k k' σ).submatrix (Fin.castLE hj) (Fin.castLE hj)).map (g.app (F.U k ⊓ F.U k')).hom)
    (fun k V h => ?_) (fun k k' i => ?_) fun k k' => ?_
  · have := (linearIndependent_vecSec F g σ f hf k h).comp _ (Fin.castLE_injective hj)
    exact (funext fun i => resM_vecSec F g σ f k le_rfl h (Fin.castLE hj i)) ▸ this
  · refine (resM_vecSec F g σ f k' le_rfl _ _).trans ((vecSec_chg F g σ f hc k k'
      (V := g ⁻¹ᵁ F.U k ⊓ g ⁻¹ᵁ F.U k') inf_le_left inf_le_right le_rfl _).trans ?_)
    refine (Finset.sum_of_injOn (Fin.castLE hj) (Fin.castLE_injective hj).injOn (fun _ _ => Finset.mem_univ _)
      (fun a _ h => ?_) fun a _ => ?_).symm
    · have : F.B k k' σ a (Fin.castLE hj i) = 0 := F.B_tri k k' σ (by
        by_contra h'
        exact h ⟨⟨a, lt_of_le_of_lt (not_lt.1 h') i.2⟩, Finset.mem_coe.2 (Finset.mem_univ _), rfl⟩)
      rw [this, map_zero, zero_smul]
    · exact congrArg₂ (· • ·) congr($(g.appLE_eq_app (U := F.U k ⊓ F.U k')) _).symm
        (resM_vecSec F g σ f k le_rfl _ _)
  · exact (congrArg (g.app (F.U k ⊓ F.U k')).hom (val_dual_LL_stepEx F σ hj k k')).trans (RingHom.map_det _ _)


open scoped CategoryTheory.Obj in
theorem curveTest_stepEx (hS : Published.SemiAbelianLieSeminegative) (K : Type) [Field K] [CharZero K] {j : ℕ}
    (hj : j ≤ Dw.mult σ) : NefCurveTest.CurveTest K (F.LL (NefStep.stepEx σ j)) := by
  intro C _ hs hp hc g
  obtain ⟨W, ι, _, hW, e⟩ := exists_step F g σ hj
  have := Y.t.semi
  have := Y.t.semi.smooth
  have := IsSemiAbelian.pullback (g ≫ π) Y.t.G Y.t.semi
  have hG := isGrpPullback_pullback Y.t.G (g ≫ π)
  have := isIso_theta_of_frames (g ≫ π) (exists_isFrame_omega Y.t.G)
  have : IsIso (lieBase hG) :=
    inferInstanceAs (IsIso (DualPull.theta _ (omega Y.t.G) ≫ (dualIso (asIso (omegaBase hG)).symm).hom))
  have hL := F.isLB_LL (NefStep.stepEx σ j)
  have h₁ := isLB_chartwise (isLB_dual hL) g
  refine (hS.dual_det_nonneg hs hp hc _ hW (ι ≫ lieBase hG)).trans_eq (interNum_congr_cls K _
    (isLB_vecOne (isLB_dual hW.isLB_det)) (isLB_vecOne (LB.isLB_pull hL g)) fun i => ?_)
  fin_cases i
  change cls (CechPic.dual (det W j)) (isLB_dual hW.isLB_det) =
    cls ((F.LL (NefStep.stepEx σ j)).pull g) (LB.isLB_pull hL g)
  rw [cls_dual hW.isLB_det, ← (cls_eq_iff h₁.1 hW.isLB_det).2 e,
    (cls_eq_iff h₁.1 (LB.isLB_pull (isLB_dual hL) g)).2 h₁.2, cls_pull (isLB_dual hL), cls_dual hL, map_neg, neg_neg,
    cls_pull hL]

end Step

theorem isNef_stepEx (hS : Published.SemiAbelianLieSeminegative) (hN : Published.NefProductNonneg) {E : Type} [Field E]
    [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}
    {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} (X : FlagMod.FlagCover Y) (Z : Comp Xo c) (σ : E →+* ℂ) {j : ℕ}
    (hj : j ≤ Dw.mult σ) : letI := algebraΓOfHom (str₀ X Z); IsNef c.F (LL₀ X Z (NefStep.stepEx σ j)) :=
  letI := algebraΓOfHom (str₀ X Z)
  ((curveTest_stepEx X.F σ hS _ hj).pull (X.F.isLB_LL _) _).isNef hN (LB.isLB_pull (X.F.isLB_LL _) _)

end GlobalTheory.NefHodge
end
end
end
