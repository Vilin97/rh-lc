module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanLStable
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSummandTw
public import Formalism.SharpRestriction.LevelLetterCocycles.PairedCharacterCondition
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CutCocFinsetCommon
public import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoDuality
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSummandTw
import Formalism.SharpRestriction.LevelLetterCocycles.PairedCharacterCondition
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsStableComplActK
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CentralIdemCoeff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodORingOfIntegers
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PotentiallyCrystallineModuleEqCrystallineRestricStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitOfClosure
import Mathlib.Tactic.Linter.HaveILetI
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalIntegerSpanOfImageIsStableLatticeStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EOsurjOneX

section

@[expose] public section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition GlobalTheory.Pass.LocDual GlobalTheory.Pass.LocDual.OneX

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.Pass.LocDual.OneX.PushEq

variable {D : D7} (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))

instance eOsurjOneX : RingHomSurjective (D.nbr i w hw).eO.toRingHom := ⟨(D.nbr i w hw).eO.surjective⟩

instance eOinvOneX : RingHomInvPair (D.nbr i w hw).eO.toRingHom (D.nbr i w hw).eO.symm.toRingHom :=
  ⟨by ext; simp, by ext; simp⟩

instance eOinvOneX' : RingHomInvPair (D.nbr i w hw).eO.symm.toRingHom (D.nbr i w hw).eO.toRingHom :=
  ⟨by ext; simp, by ext; simp⟩

theorem vecL_add {a : ℕ} (u v : Fin a → Fin D.R.nV → KK D.nd i) :
    vecL i w hw (u + v) = vecL i w hw u + vecL i w hw v := by
  funext j m; simp [vecL]

theorem vecL_smul {a : ℕ} (c : D.nd.O i) (u : Fin a → Fin D.R.nV → KK D.nd i) :
    vecL i w hw (c • u) = (D.nbr i w hw).eO c • vecL i w hw u := by
  funext j m
  simp only [vecL, Pi.smul_apply, Algebra.smul_def, map_mul, Br.toLLK_alg]

theorem vecL_inj {a : ℕ} : Function.Injective (vecL (D := D) i w hw (a := a)) := by
  intro u v h
  funext j m
  exact (Br.toLLK (D.nbr i w hw)).injective (congrFun (congrFun h j) m)

section Y
variable {a : ℕ} (Y : Submodule (D.nd.O i) (Fin a → Fin D.R.nV → KK D.nd i))

def toY : ↥Y →ₛₗ[(D.nbr i w hw).eO.toRingHom] ↥(spanL i w hw Y) where
  toFun y := ⟨vecL i w hw y.1, Submodule.subset_span ⟨y.1, y.2, rfl⟩⟩
  map_add' u v := Subtype.ext (vecL_add i w hw u.1 v.1)
  map_smul' c u := Subtype.ext (vecL_smul i w hw c u.1)

theorem toY_inj : Function.Injective (toY i w hw Y) := fun u v h =>
  Subtype.ext (vecL_inj i w hw (congrArg (fun z : ↥(spanL i w hw Y) => (z : Fin a → Fin D.R.nV → Br.LL D.nbr i w hw)) h))

theorem range_toY : LinearMap.range (toY i w hw Y) = latY i w hw Y := by
  apply le_antisymm
  · rintro _ ⟨y, rfl⟩
    exact Submodule.subset_span ⟨y.1, y.2, rfl⟩
  · refine Submodule.span_le.2 ?_
    rintro u ⟨y, hy, hu⟩
    exact ⟨⟨y, hy⟩, Subtype.ext hu⟩

def eY : ↥Y ≃ₛₗ[(D.nbr i w hw).eO.toRingHom] ↥(LinearMap.range (toY i w hw Y)) :=
  LinearEquiv.ofInjective _ (toY_inj i w hw Y)

variable {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i))
  (T : Submodule (Br.OLL D.nbr i w hw) ↥(spanL i w hw Y)) (hT : T = latY i w hw Y)

def phiL (φ : ↥Y →ₗ[D.nd.O i] KOG (D.nd.O i) k) :
    ↥T →ₗ[Br.OLL D.nbr i w hw] ((Fin k → Br.LL D.nbr i w hw) ⧸ (Br.locLat D.nbr i w hw M).T) :=
  ((Br.phi (D.nbr i w hw) k).comp φ).comp
    ((eY i w hw Y).symm.toLinearMap.comp
      (LinearEquiv.ofEq _ _ (hT.trans (range_toY i w hw Y).symm)).toLinearMap)

theorem phiL_eq (φ : ↥Y →ₗ[D.nd.O i] KOG (D.nd.O i) k) (v : ↥T) (y : ↥Y)
    (hv : (v : ↥(spanL i w hw Y)) = toY i w hw Y y) :
    phiL i w hw Y M T hT φ v = Br.phi (D.nbr i w hw) k (φ y) := by
  have e : (eY i w hw Y).symm (LinearEquiv.ofEq _ _ (hT.trans (range_toY i w hw Y).symm) v) = y :=
    (eY i w hw Y).symm_apply_eq.2 (Subtype.ext hv)
  change Br.phi (D.nbr i w hw) k (φ ((eY i w hw Y).symm (LinearEquiv.ofEq _ _ (hT.trans (range_toY i w hw Y).symm) v))) = _
  rw [e]

end Y

theorem phi_WKG {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (g : Br.G D.nbr i w hw)
    (z : KOG (D.nd.O i) k) :
    Br.phi (D.nbr i w hw) k (WKG M (gl i w hw g) z) =
      repD (Br.locLat D.nbr i w hw M) g (Br.phi (D.nbr i w hw) k z) := by
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  change Submodule.Quotient.mk (Br.vecS (D.nbr i w hw) k ((matRep (mapM (toK D.nd i) M) _) u)) =
    Submodule.Quotient.mk ((matRep (Br.loc D.nbr i w hw M) g) (Br.vecS (D.nbr i w hw) k u))
  congr 1
  exact (loc_mulVec i w hw M g u).symm

theorem main : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (Xs : Set (D.nd.X i)) (hr : GoodR D.nd i r) {a : ℕ} (x : Fin a → ↥Xs)
    (Y : Submodule (D.nd.O i) (Fin a → Fin D.R.nV → KK D.nd i))
    (hst : ∀ γ : GE D.nd, ∀ y ∈ Y, actK i r Xs x γ y ∈ Y) (E : Fin a → Fin D.R.nV → KK D.nd i)
    (hE : ∀ γ : GE D.nd, actK i r Xs x γ E - E ∈ Y) {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i))
    (LY : Lattice (O := Br.OLL D.nbr i w hw) (XG i w hw r Xs hr x Y hst).ρ), LY.T = latY i w hw Y →
    ∀ φ : ↥Y →ₗ[D.nd.O i] KOG (D.nd.O i) k, (∀ (γ : GE D.nd) (y : ↥Y), φ ⟨_, hst γ y.1 y.2⟩ = WKG M γ (φ y)) →
    ∃ φ' : ↥LY.T →ₗ[Br.OLL D.nbr i w hw] ((Fin k → Br.LL D.nbr i w hw) ⧸ (Br.locLat D.nbr i w hw M).T),
    BlochKatoDuality.IsGMapD LY (Br.locLat D.nbr i w hw M) φ' ∧
    ∀ y : ↥(latticeCocycles LY), (y : Br.G D.nbr i w hw → (XG i w hw r Xs hr x Y hst).V) = yfun i w hw r Xs x Y E hE →
    BlochKatoDuality.pushD LY (Br.locLat D.nbr i w hw M) φ' y =
    fun g => Br.phi (D.nbr i w hw) k (φ ⟨_, hE (gl i w hw g)⟩) := by
  intro D i w hw r Xs hr a x Y hst E hE k M LY hT φ hφ
  refine ⟨phiL i w hw Y M LY.T hT φ, ?_, ?_⟩
  · intro g v
    obtain ⟨v, hv⟩ := v
    have hm : (show ↥(spanL i w hw Y) from v) ∈ LinearMap.range (toY i w hw Y) := by
      rw [range_toY, ← hT]; exact hv
    obtain ⟨y, rfl⟩ := hm
    have h1 : (show ↥(spanL i w hw Y) from (actT LY g ⟨toY i w hw Y y, hv⟩).1) =
        toY i w hw Y ⟨_, hst (gl i w hw g) y.1 y.2⟩ :=
      Subtype.ext (sumG_vecL i w hw r Xs hr x g y.1)
    refine (phiL_eq i w hw Y M LY.T hT φ _ _ h1).trans ?_
    refine Eq.trans ?_ (congrArg (repD (Br.locLat D.nbr i w hw M) g)
      (phiL_eq i w hw Y M LY.T hT φ ⟨_, hv⟩ y rfl).symm)
    rw [hφ]
    exact phi_WKG i w hw M g (φ y)
  · intro y hy
    funext g
    have h2 : (show ↥(spanL i w hw Y) from (evT LY g y).1) = toY i w hw Y ⟨_, hE (gl i w hw g)⟩ := by
      change (y : Br.G D.nbr i w hw → (XG i w hw r Xs hr x Y hst).V) g = _
      rw [hy]
      rfl
    exact phiL_eq i w hw Y M LY.T hT φ (evT LY g y) _ h2

end GlobalTheory.Pass.LocDual.OneX.PushEq

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankSpanVecSLe

section

@[expose] public section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition GlobalTheory.Pass.LocDual GlobalTheory.Pass.LocDual.OneX

noncomputable section

namespace GlobalTheory.Pass.LocDual.OneX

section VecGen
variable {K L : Type} [Field K] [Field L] (φ : K →+* L) (a n : ℕ)

def vecS : (Fin a → Fin n → K) →ₛₗ[φ] (Fin a → Fin n → L) where
  toFun v := fun b j => φ (v b j)
  map_add' u v := by funext b j; simp
  map_smul' c v := by funext b j; simp

variable {φ a n}

theorem vecS_apply (v : Fin a → Fin n → K) (b : Fin a) (j : Fin n) : vecS φ a n v b j = φ (v b j) := rfl

theorem span_vecS_span (S : Set (Fin a → Fin n → K)) :
    Submodule.span L (vecS φ a n '' (Submodule.span K S : Set (Fin a → Fin n → K))) =
      Submodule.span L (vecS φ a n '' S) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨v, hv, rfl⟩
    induction hv using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul c x _ hx => rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ hx
  · exact Submodule.span_mono (Set.image_mono Submodule.subset_span)

theorem finrank_span_vecS_le (W : Submodule K (Fin a → Fin n → K)) :
    finrank L (Submodule.span L (vecS φ a n '' (W : Set (Fin a → Fin n → K)))) ≤ finrank K W := by
  let b := Module.finBasis K W
  let g : Fin (Module.finrank K W) → (Fin a → Fin n → L) := fun i => vecS φ a n (b i)
  have hle : Submodule.span L (vecS φ a n '' (W : Set (Fin a → Fin n → K))) ≤ Submodule.span L (Set.range g) := by
    rw [Submodule.span_le]
    rintro _ ⟨w, hw, rfl⟩
    have h : w = ∑ i, b.repr ⟨w, hw⟩ i • (b i : Fin a → Fin n → K) := by
      have := congrArg W.subtype (b.sum_repr ⟨w, hw⟩)

      rw [map_sum] at this
      exact this.symm

    rw [h, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [map_smulₛₗ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have h1 := Submodule.finrank_mono hle
  have h2 : Module.finrank L (Submodule.span L (Set.range g)) ≤ Module.finrank K W := by
    have := finrank_range_le_card (R := L) g
    simpa [Set.finrank] using this
  exact h1.trans h2

theorem span_vecS_top : Submodule.span L (Set.range (vecS φ a n)) = ⊤ := by
  rw [eq_top_iff]
  intro u _
  have e : u = ∑ b, ∑ j, u b j • vecS φ a n (fun b'' j'' => if b'' = b ∧ j'' = j then 1 else 0) := by
    funext b' j'
    simp only [Finset.sum_apply, Pi.smul_apply, vecS_apply, smul_eq_mul, apply_ite φ, map_one, map_zero, mul_ite,
      mul_one, mul_zero, ite_and]
    simp [Finset.sum_ite_eq]
  rw [e]
  exact Submodule.sum_mem _ fun b _ => Submodule.sum_mem _ fun j _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

theorem isCompl_span_vecS {W W' : Submodule K (Fin a → Fin n → K)} (h : IsCompl W W') :
    IsCompl (Submodule.span L (vecS φ a n '' (W : Set (Fin a → Fin n → K))))
      (Submodule.span L (vecS φ a n '' (W' : Set (Fin a → Fin n → K)))) := by
  set A := Submodule.span L (vecS φ a n '' (W : Set (Fin a → Fin n → K)))
  set B := Submodule.span L (vecS φ a n '' (W' : Set (Fin a → Fin n → K)))
  have hsup : A ⊔ B = ⊤ := by
    rw [eq_top_iff, ← span_vecS_top (φ := φ), Submodule.span_le]
    rintro _ ⟨v, rfl⟩
    have hv : v ∈ W ⊔ W' := by rw [h.sup_eq_top]; trivial
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hv
    rw [map_add (f := _)]
    exact add_mem (Submodule.mem_sup_left (Submodule.subset_span ⟨y, hy, rfl⟩))
      (Submodule.mem_sup_right (Submodule.subset_span ⟨z, hz, rfl⟩))
  have h1 : finrank L A ≤ finrank K W := finrank_span_vecS_le W
  have h2 : finrank L B ≤ finrank K W' := finrank_span_vecS_le W'
  have h3 := Submodule.finrank_add_eq_of_isCompl h
  have h4 := Submodule.finrank_sup_add_finrank_inf_eq A B
  rw [hsup, finrank_top] at h4
  have hK : finrank K (Fin a → Fin n → K) = a * n := by
    rw [Module.finrank_pi_fintype]; simp
  have hL : finrank L (Fin a → Fin n → L) = a * n := by
    rw [Module.finrank_pi_fintype]; simp
  have hinf : A ⊓ B = ⊥ := by
    rw [← Submodule.finrank_eq_zero]; omega
  exact ⟨disjoint_iff.2 hinf, codisjoint_iff.2 hsup⟩

end VecGen




theorem isSummandTw_XG : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (Xs : Set (D.nd.X i)) (hr : GoodR D.nd i r) {a : ℕ} (x : Fin a → ↥Xs)
    (Y : Submodule (D.nd.O i) (Fin a → Fin D.R.nV → KK D.nd i))
    (hst : ∀ γ : GE D.nd, ∀ y ∈ Y, actK i r Xs x γ y ∈ Y),
    (∃ C : Submodule (KK D.nd i) (Fin a → Fin D.R.nV → KK D.nd i),
    (∀ γ : GE D.nd, ∀ v ∈ C, actK i r Xs x γ v ∈ C) ∧
    IsCompl (Submodule.span (KK D.nd i) (Y : Set (Fin a → Fin D.R.nV → KK D.nd i))) C) →
    IsSummandTw i w hw r Xs (XG i w hw r Xs hr x Y hst) := by
  intro D i w hw r Xs hr a x Y hst ⟨C, hC, hYC⟩
  have hspan : spanL i w hw Y = Submodule.span _ (vecS (Br.toLLK (D.nbr i w hw)) a D.R.nV ''
      (Submodule.span (KK D.nd i) (Y : Set (Fin a → Fin D.R.nV → KK D.nd i)) : Set (Fin a → Fin D.R.nV → KK D.nd i))) := by
    rw [span_vecS_span]; rfl
  refine ⟨a, x, (spanL i w hw Y).subtype, Subtype.val_injective, fun g v => rfl,
    Submodule.span _ (vecL i w hw '' (C : Set (Fin a → Fin D.R.nV → KK D.nd i))), ?_, ?_⟩
  · intro g u hu
    have hle : Submodule.span (Br.LL D.nbr i w hw) (vecL i w hw '' (C : Set (Fin a → Fin D.R.nV → KK D.nd i))) ≤
        (Submodule.span (Br.LL D.nbr i w hw) (vecL i w hw '' (C : Set (Fin a → Fin D.R.nV → KK D.nd i)))).comap
          ((sumG i w hw r Xs hr x).ρ g) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨v, hv, rfl⟩
      show (sumG i w hw r Xs hr x).ρ g (vecL i w hw v) ∈
        Submodule.span (Br.LL D.nbr i w hw) (vecL i w hw '' (C : Set (Fin a → Fin D.R.nV → KK D.nd i)))
      rw [sumG_vecL]
      exact Submodule.subset_span ⟨_, hC _ v hv, rfl⟩
    exact hle hu
  · have key : IsCompl (spanL i w hw Y)
        (Submodule.span (Br.LL D.nbr i w hw) (vecL i w hw '' (C : Set (Fin a → Fin D.R.nV → KK D.nd i)))) := by
      rw [hspan]
      exact isCompl_span_vecS hYC
    convert key using 1
    exact Submodule.range_subtype _

end GlobalTheory.Pass.LocDual.OneX

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsTopRingLL

section

@[expose] public section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition GlobalTheory.Pass.LocDual GlobalTheory.Pass.LocDual.OneX

noncomputable section

namespace GlobalTheory.Pass.LocDual.OneX

variable {D : D7} (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))

theorem isTopRingLL : IsTopologicalRing (Br.LL D.nbr i w hw) :=
  (goodO_ringOfIntegers (D.nd.l i) (D.nbr i w hw).LL).2.2.2.1

theorem vecL_sub {a : ℕ} (u v : Fin a → Fin D.R.nV → KK D.nd i) :
    vecL i w hw (u - v) = vecL i w hw u - vecL i w hw v := by
  funext b j
  simp [vecL]

variable (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (Xs : Set (D.nd.X i))

theorem sumG_crys (hr : GoodR D.nd i r) (hAdm : FontaineAtPlacesOverL (D := D)) {a : ℕ} (x : Fin a → ↥Xs)
    (K' : FinExt (D.nd.l i)) (h : (D.nbr i w hw).Kw.1 ≤ K'.1)
    (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex)
    (hS : ∀ (g : ↥(GK (D.nbr i w hw).Kw)) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'),
      ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw).actB g (algebraMap ↥(K0 K') (D.loc (D.nd.l i)).R.B c) =
        algebraMap ↥(K0 K') (D.loc (D.nd.l i)).R.B c')
    (hpot : ∀ y : ↥Xs, (pc (D.loc (D.nd.l i)) h hN hF hS).IsPotCrys
      (matRep (Br.loc D.nbr i w hw (rTwO D.nd i r y)))) :
    IsCrys ((D.loc (D.nd.l i)).PD K')
      ((sumG i w hw r Xs hr x).ρ.comp (Subgroup.inclusion (GK_le h))) := by
  haveI := isTopRingLL i w hw
  have hc' : ∀ (y : ↥Xs) (v : Fin D.R.nV → Br.LL D.nbr i w hw),
      Continuous fun g => ((Br.loc D.nbr i w hw (rTwO D.nd i r y)).comp (Subgroup.inclusion (GK_le h)) g).mulVec v :=
    fun y v => (contTw i w hw r Xs hr y v).comp (continuous_inclusion (GK_le h))
  have hF' := hAdm (D.nd.l i) K' (D.nbr i w hw).LL
  have hcr : ∀ y : ↥Xs, IsCrys ((D.loc (D.nd.l i)).PD K')
      (matRep ((Br.loc D.nbr i w hw (rTwO D.nd i r y)).comp (Subgroup.inclusion (GK_le h)))) := fun y =>
    (GlobalTheory.T.potentiallyCrystalline_module_eq_crystalline_restriction (D.nd.l i) (D.loc (D.nd.l i)) (D.nbr i w hw).Kw K' (D.nbr i w hw).LL h hN hF hS _
      (matRep (Br.loc D.nbr i w hw (rTwO D.nd i r y)))).2.1 (hpot y)
  exact (cj_sum (Qp := ℚ_[D.nd.l i]) (O := ↥(OL (D.nbr i w hw).LL))
    (fun y : ↥Xs => (Br.loc D.nbr i w hw (rTwO D.nd i r y)).comp (Subgroup.inclusion (GK_le h))) hc' hF'
    (S := fun _ => Set.univ) (fun y => ⟨hcr y, fun τ b _ => Set.mem_univ _⟩) a x).1

theorem yfun_val {a : ℕ} (hr : GoodR D.nd i r) (x : Fin a → ↥Xs)
    (Y : Submodule (D.nd.O i) (Fin a → Fin D.R.nV → KK D.nd i))
    (E : Fin a → Fin D.R.nV → KK D.nd i) (hE : ∀ γ : GE D.nd, actK i r Xs x γ E - E ∈ Y)
    (g : Br.G D.nbr i w hw) :
    (spanL i w hw Y).subtype (yfun i w hw r Xs x Y E hE g) =
      (sumG i w hw r Xs hr x).ρ g (vecL i w hw E) - (show (sumG i w hw r Xs hr x).V from vecL i w hw E) := by
  rw [sumG_vecL]
  exact vecL_sub i w hw _ _

end GlobalTheory.Pass.LocDual.OneX

end




theorem GlobalTheory.Pass.LocDual.OneX.yfun_Z1fT : ∀ (D : D7), FontaineAtPlacesOverL (D := D) → ∀ (i : D.nd.Loc)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (hr : GoodR D.nd i r)
    (Xs : Set (D.nd.X i)) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (n : ℕ), PotFam i w hw (fun x : ↥Xs => rTwO D.nd i r x) n → ∀ {a : ℕ} (x : Fin a → ↥Xs) (Y : Submodule (D.nd.O i) (Fin a → Fin D.R.nV → KK D.nd i))
    (hst : ∀ γ : GE D.nd, ∀ y ∈ Y, actK i r Xs x γ y ∈ Y) (E : Fin a → Fin D.R.nV → KK D.nd i)
    (hE : ∀ γ : GE D.nd, actK i r Xs x γ E - E ∈ Y)
    (LY : Lattice (O := Br.OLL D.nbr i w hw) (XG i w hw r Xs hr x Y hst).ρ), LY.T = latY i w hw Y →
    (yfun i w hw r Xs x Y E hE : Br.G D.nbr i w hw → (XG i w hw r Xs hr x Y hst).V) ∈
    latticeFiniteCocycles (Br.PD D.loc D.nbr i w hw) LY := by
  intro D hAdm i r hr Xs w hw n hpf a x Y hst E hE LY hLY
  obtain ⟨K', h, hN, hF, hS, Sig, Fr, -, -, -, -, hall⟩ := hpf
  haveI := isTopRingLL i w hw
  have hF' := hAdm (D.nd.l i) K' (D.nbr i w hw).LL
  have hz : (yfun i w hw r Xs x Y E hE : Br.G D.nbr i w hw → (XG i w hw r Xs hr x Y hst).V) ∈
      finiteCocycles (Br.PD D.loc D.nbr i w hw) (XG i w hw r Xs hr x Y hst).ρ :=
    GlobalTheory.Pass.FinDesc.main (D.nd.l i) (D.loc (D.nd.l i)) (D.nbr i w hw).Kw K' (D.nbr i w hw).LL h hN hF
      (fun A₀ A₁ A₂ ι π h1 h2 h3 h4 h5 hA =>
        ⟨((hF'.1 A₀ A₁ A₂ ι π h1 h2 h3 h4 h5).1 hA).1, ((hF'.1 A₀ A₁ A₂ ι π h1 h2 h3 h4 h5).1 hA).2.1⟩)
      (sumG i w hw r Xs hr x) (XG i w hw r Xs hr x Y hst) (spanL i w hw Y).subtype
      (spanL i w hw Y).injective_subtype (fun g v => rfl)
      (sumG_crys i w hw r Xs hr hAdm x K' h hN hF hS (fun y => (hall y).1)) (vecL i w hw E)
      (yfun i w hw r Xs x Y E hE) (yfun_val i w hw r Xs hr x Y E hE)
  refine ⟨⟨hz.1, fun g _ => ?_⟩, hz⟩
  have hm : (yfun i w hw r Xs x Y E hE g : ↥(spanL i w hw Y)) ∈ latY i w hw Y :=
    Submodule.subset_span ⟨_, hE _, rfl⟩
  show yfun i w hw r Xs x Y E hE g ∈ LY.T
  rw [hLY]
  exact hm
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalCocyclesMemSpanPushoutSummandLattice

section

@[expose] public section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition GlobalTheory.Pass.LocDual GlobalTheory.Pass.LocDual.OneX
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.Pass.LocDual.OneX

theorem span_stable (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (Xs : Set (D.nd.X i)) {a : ℕ} (x : Fin a → ↥Xs) (Y : Submodule (D.nd.O i) (Fin a → Fin D.R.nV → KK D.nd i))
    (hst : ∀ γ : GE D.nd, ∀ y ∈ Y, actK i r Xs x γ y ∈ Y) (γ : GE D.nd) :
    ∀ v ∈ Submodule.span (KK D.nd i) (Y : Set (Fin a → Fin D.R.nV → KK D.nd i)),
      actK i r Xs x γ v ∈ Submodule.span (KK D.nd i) (Y : Set (Fin a → Fin D.R.nV → KK D.nd i)) := by
  let f : (Fin a → Fin D.R.nV → KK D.nd i) →ₗ[KK D.nd i] (Fin a → Fin D.R.nV → KK D.nd i) :=
    LinearMap.pi fun b => Matrix.toLin' (mapM (toK D.nd i) (rTwO D.nd i r (x b)) γ) ∘ₗ LinearMap.proj b
  have hf : ∀ v, f v = actK i r Xs x γ v := fun v => rfl
  intro v hv
  rw [← hf]
  have h : Submodule.span (KK D.nd i) (Y : Set (Fin a → Fin D.R.nV → KK D.nd i)) ≤
      (Submodule.span (KK D.nd i) (Y : Set (Fin a → Fin D.R.nV → KK D.nd i))).comap f := by
    refine Submodule.span_le.2 fun y hy => ?_
    rw [SetLike.mem_coe, Submodule.mem_comap, hf]
    exact Submodule.subset_span (hst γ y hy)
  exact h hv

end GlobalTheory.Pass.LocDual.OneX


set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem GlobalTheory.Pass.LocDual.OneX.main : ∀ (D : D7), FontaineAtPlacesOverL (D := D) → ∀ (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))),
    GoodR D.nd i r → ∀ (Xs : Set (D.nd.X i)) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (n : ℕ), PotFam i w hw (fun x : ↥Xs => rTwO D.nd i r x) n →
    ∀ (k : ℕ) (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (hSub : SubTw i r Xs M)
      (F : Finset (Br.G D.nbr i w hw → (Fin k → Br.LL D.nbr i w hw) ⧸ (Br.locLat D.nbr i w hw M).T)),
      (F : Set (Br.G D.nbr i w hw → (Fin k → Br.LL D.nbr i w hw) ⧸ (Br.locLat D.nbr i w hw M).T)) ⊆ cutCoc i w hw r Xs M →
      ∃ X : GRep (Br.G D.nbr i w hw) ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw),
        IsSummandTw i w hw r Xs X ∧
        Submodule.span (Br.OLL D.nbr i w hw) (F : Set (Br.G D.nbr i w hw → (Fin k → Br.LL D.nbr i w hw) ⧸ (Br.locLat D.nbr i w hw M).T)) ≤
          BlochKatoDuality.spanPush (Br.PD D.loc D.nbr i w hw) X (locU i w hw M hSub.1) (Br.locLat D.nbr i w hw M) := by
  intro D hF i r hr Xs w hw n hP k M hSub F hFs
  obtain ⟨a, x, E, Y, hYfg, hst, hE, hc⟩ := GlobalTheory.Pass.LocDual.OneX.cutCoc_finset_common D i w hw r Xs M F hFs
  have hC := GlobalTheory.BlockSum.exists_stable_compl_actK D i r Xs hr x (Submodule.span (KK D.nd i) (Y : Set _))
    (fun γ => GlobalTheory.Pass.LocDual.OneX.span_stable D i r Xs x Y hst γ)
  refine ⟨GlobalTheory.Pass.LocDual.OneX.XG i w hw r Xs hr x Y hst,
    GlobalTheory.Pass.LocDual.OneX.isSummandTw_XG D i w hw r Xs hr x Y hst hC, ?_⟩
  obtain ⟨LY, hLY⟩ := GlobalTheory.T.localIntegerSpanOfImage_is_stable_lattice D i w hw r Xs hr x Y hst hYfg
  have hy := GlobalTheory.Pass.LocDual.OneX.yfun_Z1fT D hF i r hr Xs w hw n hP x Y hst E hE LY hLY
  apply Submodule.span_le.2
  intro c hcF
  obtain ⟨φ, hφ, rfl⟩ := hc c hcF
  obtain ⟨φ', hG, hpush⟩ := GlobalTheory.Pass.LocDual.OneX.PushEq.main D i w hw r Xs hr x Y hst E hE M LY hLY φ hφ
  unfold BlochKatoDuality.spanPush
  exact Submodule.subset_span (R := Br.OLL D.nbr i w hw) (M := Br.G D.nbr i w hw → (Fin k → Br.LL D.nbr i w hw) ⧸ (Br.locLat D.nbr i w hw M).T) ⟨LY, φ', hG, ⟨_, hy.1⟩, hy, (hpush ⟨_, hy.1⟩ rfl).symm⟩
end
end
