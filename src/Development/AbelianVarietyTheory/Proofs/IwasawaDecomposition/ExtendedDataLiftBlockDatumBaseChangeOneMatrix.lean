module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlockBaseChangeAt
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBaseEnlargementFixedCoefFieldOfCoeffEnlargemen
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Forms
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseLevelLiftExtendedDataEqMapSmallerFieldStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSemilinearFormsLiftSameComplexValues
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormsLiftExtendedDataCarriesClassSumStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormsLiftExtendedDataIntertwinesFiniteGroupStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodCharactersExtendedDataEqMapSmallerDataStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralFormsReferenceTupleExtensionSpanStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftFormsReferenceTupleBasisExtendedStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftSubspaceExtendedDataEqSpanSmallerLifts
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypePrimeFiniteGroupEqExtendedDataStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormsOfSemilinear
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlockBaseChange

-- Source module: Development.AutomorphicArithmetic.SemilinearForms.LiftMatAt

section

@[expose] public section

open Module NumberField Formalism.L2.DIV Formalism.DivisionValues
open scoped Matrix

noncomputable section

namespace GlobalTheory.Mem.R3.LiftLatBC

open GlobalTheory.Mem.R3.DefLatBC

variable {K K' : Type} [Field K] [NumberField K] [StarRing K] [Field K'] [NumberField K'] [StarRing K']
  {G G' : Type} [Group G] [Fintype G] [Group G'] [Fintype G'] {Pl0 Pl0' : Type}

theorem forms_of_semilinear_at (φ : K →+* K') (e : G ≃* G') (B : BlockDat K G Pl0) (B' : BlockDat K' G' Pl0')
    (Z : Submodule K B.S.Forms) (Z' : Submodule K' B'.S.Forms) (L : B.S.Forms →+ B'.S.Forms)
    (hsm : ∀ (a : K) (f : B.S.Forms), L (a • f) = φ a • L f)
    (hli : LinearIndependent K' (fun k => L (B.S.basis k)))
    (hsp : ⊤ ≤ Submodule.span K' (Set.range fun k => L (B.S.basis k)))
    (hcs : ∀ f g : B.S.Forms, B'.S.csum (L f : B'.S.Cl → B'.S.V) (L g) = φ (B.S.csum f g))
    (hact : ∀ (g : G) (f : B.S.Forms), B'.r (e g) (L f) = L (B.r g f))
    (hnab : ∀ f' : B'.S.Forms, (∀ c, (f' : B'.S.Cl → B'.S.V) c ∈ B'.S.Nab c) ↔
      f' ∈ Submodule.span (𝓞 K') (L '' {f : B.S.Forms | ∀ c, (f : B.S.Cl → B.S.V) c ∈ B.S.Nab c}))
    (hZ : Z' = Submodule.span K' (L '' (Z : Set B.S.Forms))) :
    ∃ C : Matrix (Fin B'.S.dim) (Fin B.S.dim) K', (∀ f, GlobalTheory.Mem.R3.LiftLatBC.bcF φ B B' C f = L f) ∧ Function.Bijective C.mulVec ∧
      Cᴴ * B'.S.H * C = B.S.H.map φ ∧
      (∀ g : G, B'.S.actMat B'.r (e g) * C = C * (B.S.actMat B.r g).map φ) ∧
      B'.S.nabLat = Submodule.span (𝓞 K') ((fun x : Fin B.S.dim → K => C *ᵥ (fun k => φ (x k))) '' (B.S.nabLat : Set (Fin B.S.dim → K))) ∧
      B'.coord Z' = Submodule.span K' ((fun x : Fin B.S.dim → K => C *ᵥ (fun k => φ (x k))) '' (B.coord Z : Set (Fin B.S.dim → K))) := by
  classical
  let v : Fin B.S.dim → B'.S.Forms := fun k => L (B.S.basis k)
  let bv : Basis (Fin B.S.dim) K' B'.S.Forms := Basis.mk hli hsp
  have hbv : ∀ k, bv k = L (B.S.basis k) := fun k => Basis.mk_apply hli hsp k
  let C : Matrix (Fin B'.S.dim) (Fin B.S.dim) K' := B'.S.basis.toMatrix v
  have hCe : ∀ a i, C a i = B'.S.basis.equivFun (L (B.S.basis i)) a := by
    intro a i
    simp [C, v, Basis.toMatrix_apply]
  have hC : ∀ x, C *ᵥ x = B'.S.basis.equivFun (bv.equivFun.symm x) := by
    intro x
    ext i

    simp only [Matrix.mulVec, dotProduct, hCe, Basis.equivFun_symm_apply, hbv, map_sum, map_smul,
    Basis.equivFun_apply, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, mul_comm]
  have hL : ∀ f, L f = bv.equivFun.symm (fun k => φ (B.S.basis.equivFun f k)) := by
    intro f
    conv_lhs => rw [← B.S.basis.sum_equivFun f]

    rw [map_sum, Basis.equivFun_symm_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hsm, hbv]
  have hψ : ∀ x : Fin B.S.dim → K, C *ᵥ (fun k => φ (x k)) =
      B'.S.basis.equivFun (L (B.S.basis.equivFun.symm x)) := by
    intro x
    simp only [hL, LinearEquiv.apply_symm_apply, hC]
  have hbc : ∀ f, GlobalTheory.Mem.R3.LiftLatBC.bcF φ B B' C f = L f := by
    intro f
    simp only [GlobalTheory.Mem.R3.LiftLatBC.bcF]
    rw [hC, LinearEquiv.symm_apply_apply, hL]
  have hbij : Function.Bijective C.mulVec := by
    have he : C.mulVec = ⇑(bv.equivFun.symm.trans B'.S.basis.equivFun) := funext fun x => by
      rw [hC]
      rfl
    rw [he]
    exact LinearEquiv.bijective _
  have hH : Cᴴ * B'.S.H * C = B.S.H.map φ := by
    ext i j
    have h1 := csum_coords B'.S (B'.S.basis.equivFun (L (B.S.basis i)))
      (B'.S.basis.equivFun (L (B.S.basis j)))
    simp only [LinearEquiv.symm_apply_apply, hcs] at h1
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.map_apply, Formalism.L2.DIV.CSD.H,
      Matrix.of_apply, hCe]
    rw [h1]
    simp only [Finset.sum_mul]
    exact Finset.sum_comm
  have hrep : ∀ (T : Module.End K B.S.Forms) (f : B.S.Forms),
      LinearMap.toMatrix B.S.basis B.S.basis T *ᵥ B.S.basis.equivFun f = B.S.basis.equivFun (T f) :=
    fun T f => LinearMap.toMatrix_mulVec_repr _ _ _ _
  have hrep' : ∀ (T : Module.End K' B'.S.Forms) (f : B'.S.Forms),
      LinearMap.toMatrix B'.S.basis B'.S.basis T *ᵥ B'.S.basis.equivFun f = B'.S.basis.equivFun (T f) :=
    fun T f => LinearMap.toMatrix_mulVec_repr _ _ _ _
  have hact' : ∀ g : G, B'.S.actMat B'.r (e g) * C = C * (B.S.actMat B.r g).map φ := by
    intro g
    apply Matrix.ext_of_mulVec_single
    intro k
    have hs : (Pi.single k 1 : Fin B.S.dim → K') = fun j => φ ((Pi.single k 1 : Fin B.S.dim → K) j) := by
      funext j
      by_cases h : j = k <;> simp [h]
    have hk : (Pi.single k 1 : Fin B.S.dim → K) = B.S.basis.equivFun (B.S.basis k) := by
      funext j
      rw [Basis.equivFun_self, Pi.single_apply]
      by_cases h : j = k
      · subst h
        simp
      · simp [h, Ne.symm h]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hs]
    have hm : (B.S.actMat B.r g).map φ *ᵥ (fun j => φ ((Pi.single k 1 : Fin B.S.dim → K) j)) =
        fun i => φ (((B.S.actMat B.r g) *ᵥ Pi.single k 1) i) := by
      funext i
      exact (RingHom.map_mulVec φ _ _ i).symm
    rw [hm, hψ, hψ, hk]
    simp only [Formalism.L2.DIV.CSD.actMat, hrep, hrep', LinearEquiv.symm_apply_apply, hact]
  have hnab' : B'.S.nabLat = Submodule.span (𝓞 K')
      ((fun x : Fin B.S.dim → K => C *ᵥ (fun k => φ (x k))) '' (B.S.nabLat : Set (Fin B.S.dim → K))) := by
    have hset : (fun x : Fin B.S.dim → K => C *ᵥ (fun k => φ (x k))) '' (B.S.nabLat : Set (Fin B.S.dim → K)) =
        (fun f => B'.S.basis.equivFun (L f)) '' {f : B.S.Forms | ∀ c, (f : B.S.Cl → B.S.V) c ∈ B.S.Nab c} := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨B.S.basis.equivFun.symm x, (mem_nabLat_iff B.S x).mp hx, (hψ x).symm⟩
      · rintro ⟨f, hf, rfl⟩
        refine ⟨B.S.basis.equivFun f, (mem_nabLat_iff B.S _).mpr (by simpa using hf), ?_⟩
        simp only [hψ, LinearEquiv.symm_apply_apply]
    rw [hset]
    ext y
    rw [mem_nabLat_iff, hnab (B'.S.basis.equivFun.symm y)]
    let E := B'.S.basis.equivFun.restrictScalars (𝓞 K')
    have hE : (fun f => B'.S.basis.equivFun (L f)) '' {f : B.S.Forms | ∀ c, (f : B.S.Cl → B.S.V) c ∈ B.S.Nab c} =
        (E : B'.S.Forms →ₗ[𝓞 K'] (Fin B'.S.dim → K')) '' (L '' {f : B.S.Forms | ∀ c, (f : B.S.Cl → B.S.V) c ∈ B.S.Nab c}) := by
      rw [Set.image_image]
      rfl
    rw [hE, ← Submodule.map_span, Submodule.mem_map_equiv]
    exact Iff.rfl
  have hcoord : B'.coord Z' = Submodule.span K'
      ((fun x : Fin B.S.dim → K => C *ᵥ (fun k => φ (x k))) '' (B.coord Z : Set (Fin B.S.dim → K))) := by
    rw [hZ]
    simp only [Formalism.L2.DIV.BlockDat.coord, Submodule.map_span, Submodule.map_coe, LinearEquiv.coe_coe]
    congr 1
    rw [Set.image_image, Set.image_image]
    refine Set.image_congr fun f _ => ?_
    rw [hψ, LinearEquiv.symm_apply_apply]
  exact ⟨C, hbc, hbij, hH, hact', hnab', hcoord⟩

end GlobalTheory.Mem.R3.LiftLatBC

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExtendedDataLiftBlockDatumBaseChangeOneMatrix

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open scoped Matrix

namespace GlobalTheory.Mem.R3.LiftLatBC

private theorem app_heq {Γ Γ' W W' : Type} (hΓ : Γ' = Γ) {nW : NormedAddCommGroup W} {nW' : NormedAddCommGroup W'}
    {iW : InnerProductSpace ℂ W} {iW' : InnerProductSpace ℂ W'} (h1 : HEq W' W) (h2 : HEq nW' nW) (h3 : HEq iW' iW)
    {H : HMod (Γ → W)} {H' : HMod (Γ' → W')} (hH : HEq H' H) (inj : Function.Injective H.e)
    {Y Y' : Type} {nY : NormedAddCommGroup Y} {nY' : NormedAddCommGroup Y'}
    {iY : InnerProductSpace ℂ Y} {iY' : InnerProductSpace ℂ Y'} (g1 : Y' = Y) (g2 : HEq nY' nY) (g3 : HEq iY' iY)
    {θ : H.H →ₗ[ℂ] Y} {θ' : H'.H →ₗ[ℂ] Y'} (hθ : HEq θ' θ) {y : H.H} {y' : H'.H} (he : HEq (H'.e y') (H.e y)) :
    HEq (θ' y') (θ y) := by
  subst hΓ g1
  cases h1; cases h2; cases h3; cases hH; cases g2; cases g3; cases hθ
  rw [inj (eq_of_heq he)]



private theorem hmod_fields' {B B' : Base} (q : B'.toPre = B.toPre) {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'}
    {w : ColW B f T} {w' : ColW B' f' T'} {Z : w.Lt} {Z' : w'.Lt}
    (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m) (hi : (i : ℕ) = i')
    {S : (w.st Z).toD7.what₂.Tau → SPar} {S' : (w'.st Z').toD7.what₂.Tau → SPar}
    (M : Formalism.IndefR.Mult.DSModel (Wc (w.st Z).toD7 i) S) (M' : Formalism.IndefR.Mult.DSModel (Wc (w'.st Z').toD7 i') S')
    (a : HEq M'.H M.H) (b : HEq M'.nacg M.nacg) (c : HEq M'.ips M.ips) (d : HEq M'.σ M.σ) (l : HEq M'.lam M.lam) (e : HEq M'.ε M.ε)
    (g : HEq M'.fr M.fr) (X : HMod (Formalism.IndefR.Mult.MMap M)) (X' : HMod (Formalism.IndefR.Mult.MMap M')) (hX : HEq X' X) :
    (X'.H = X.H ∧ HEq X'.nH X.nH ∧ HEq X'.iH X.iH) ∧
      @Eq Type (Bridge.Gf (Vc (w'.st Z').toD7 i')) (Bridge.Gf (Vc (w.st Z).toD7 i)) := by
  obtain ⟨P', _⟩ := B'
  obtain ⟨P, _⟩ := B
  dsimp only at q
  subst q
  have e0 : i = i' := Fin.ext hi
  subst e0
  cases M
  cases M'
  dsimp only at a b c d l e g
  cases a; cases b; cases c; cases d; cases l; cases e; cases g
  have e' : X' = X := eq_of_heq hX
  subst e'
  exact ⟨⟨rfl, HEq.rfl, HEq.rfl⟩, rfl⟩

private theorem theta_jL {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (i : Fin D.R.m) (t : T)
    (h : R.phs i = 1) (x : A3.A.fam.amb.FL i t) :
    HEq ((R.toCx3 F).θ' i t ((R.toCx3 F).jL i t x)) (R.thG i t (R.jV i t x)) := by
  have e : Links.cj (twAt D.what₂.embLL A3.A.v0) (R.phs i) • R.thG i t (R.jV i t x) = R.thG i t (R.jV i t x) :=
    (congrArg (· • R.thG i t (R.jV i t x)) ((congrArg (Links.cj (twAt D.what₂.embLL A3.A.v0)) h).trans (map_one _))).trans (one_smul ℂ _)
  exact (by with_unfolding_all exact ((heq_of_eq e) :))



private theorem thG_extN {B B' : Base} (q : B'.toPre = B.toPre) {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'}
    {w : ColW B f T} {w' : ColW B' f' T'} {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok}
    {Wt : Set B.places.Pl} {Wt' : Set B'.places.Pl} {z : Dat (w.st Z) w.I hX T Wt} {z' : Dat (w'.st Z') w'.I hX' T' Wt'}
    (hE : ExtN z z') (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m) (hj : (j : ℕ) = j') (x) (x')
    (hx : HEq (z'.R.B.jL j' (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt'))) x')
      (z.R.B.jL j (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))) x)) :
    HEq (z'.R.thG j' (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt'))) (z'.R.jV j' (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt'))) x'))
      (z.R.thG j (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))) (z.R.jV j (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))) x)) := by
  letI := z.alg
  letI := z'.alg
  have hM := hE.MW j j' hj
  have h0 := hmod_fields' q j j' hj _ _ hM.1 hM.2.1 hM.2.2.1 hM.2.2.2.1 hM.2.2.2.2.1 hM.2.2.2.2.2.1 hM.2.2.2.2.2.2.1 _ _
    hM.2.2.2.2.2.2.2.2.1
  have s := (sgAt_mk _ z.R.hv0).symm
  have s' := (sgAt_mk _ z'.R.hv0).symm
  have key : ∀ σ σ', (w.st Z).toD7.what₂.embLL = σ → (w'.st Z').toD7.what₂.embLL = σ' →
      (z'.R.HW j' σ').H = (z.R.HW j σ).H ∧ HEq (z'.R.HW j' σ').nH (z.R.HW j σ).nH ∧ HEq (z'.R.HW j' σ').iH (z.R.HW j σ).iH :=
    fun σ σ' h h' => h ▸ h' ▸ h0.1
  have g := key _ _ s s'
  have hr := hE.ref j j' hj
  have m := z.pins.char.base.models
  have m' := z'.pins.char.base.models
  have he := HEq.trans (heq_of_eq (m'.jV j' _ x')) (HEq.trans hx (heq_of_eq (m.jV j _ x)).symm)
  exact app_heq h0.2 (hE.BV j j' hj).1 (hE.cV j j' hj).1 (hE.cV j j' hj).2 hr.2.1 (m.HV j _).1 g.1 g.2.1 g.2.2 hr.2.2.2.1 he

end GlobalTheory.Mem.R3.LiftLatBC


theorem _root_.GlobalTheory.T.extendedData_lift_blockDatum_baseChange_one_matrix : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        ∀ φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x) →
        ∃ (e : _ ≃* _) (C : Matrix (Fin ((famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).fam3.F.L j' (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).A.μ0).S.dim) (Fin ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.L j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0).S.dim) (w'.st Z').toD7.what₂.LL),
          GlobalTheory.Mem.R3.LiftLatBC.BlockBaseChangeAt φ e ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.L j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0) ((famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).fam3.F.L j' (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).A.μ0)
            ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.lvlA z.F.P0 z.F.ψ0) ((famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).fam3.F.lvlA z'.F.P0 z'.F.ψ0)
            ((zsOf z.R z.F).Zl j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0) ((zsOf z'.R z'.F).Zl j' (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).A.μ0) C ∧
          ∀ f : ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.L j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0).S.Forms,
            HEq ((z'.R.toCx3 z'.F).θ' j' (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).A.μ0 ((z'.R.toCx3 z'.F).jL j' (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).A.μ0 (GlobalTheory.Mem.R3.LiftLatBC.bcF φ _ _ C f)))
              ((z.R.toCx3 z.F).θ' j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0 ((z.R.toCx3 z.F).jL j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0 f))) := by
  intro h1 h2 h3 h4 h5 h6 h7
  refine StepW.trans (StepW.and (GlobalTheory.T.typePrimeFiniteGroup_eq_extendedData h1 h2 h3 h4 h5 h6 h7) (StepW.and (GlobalTheory.T.baseLevelLift_extendedData_eq_map_smallerField h1 h2 h3 h4 h5 h6 h7)
    (StepW.and (GlobalTheory.T.goodCharacters_extendedData_eq_map_smallerData h1 h2 h3 h4 h5 h6 h7) (StepW.and (GlobalTheory.T.exists_semilinearFormsLift_sameComplexValues h1 h2 h3 h4 h5 h6 h7) (StepW.and (GlobalTheory.T.liftForms_referenceTuple_basis_extended h1 h2 h3 h4 h5 h6 h7)
    (StepW.and (GlobalTheory.T.formsLift_extendedData_carries_classSum h1 h2 h3 h4 h5 h6 h7) (StepW.and (GlobalTheory.T.formsLift_extendedData_intertwines_finiteGroup h1 h2 h3 h4 h5 h6 h7) (StepW.and (GlobalTheory.T.integralForms_referenceTuple_extension_span h1 h2 h3 h4 h5 h6 h7)
    (GlobalTheory.T.liftSubspace_extendedData_eq_span_smallerLifts h1 h2 h3 h4 h5 h6 h7))))))))) (StepW.of_all ?_)
  intro K B' f' T' w' _ _ H B f T w hE hff hPin hpx Z hX Wt z hG hGA hFine hHL Z' hX' hG' hGA' hVol z' hFine' hExt j j' hj φ hφ
  obtain ⟨Hg, Hl, Hx, HL, Hb, Hc, Ha, Hn, Hs⟩ := H
  obtain ⟨e, he⟩ := Hg B f T w hE hff hPin hpx Z hX Wt z hG hGA hFine hHL Z' hX' hG' hGA' hVol z' hFine' hExt j j' hj φ hφ
  obtain ⟨hP, hψ⟩ := Hl B f T w hE hff hPin hpx Z hX Wt z hG hGA hFine hHL Z' hX' hG' hGA' hVol z' hFine' hExt j j' hj φ hφ e he
  have hXg := Hx B f T w hE hff hPin hpx Z hX Wt z hG hGA hFine hHL Z' hX' hG' hGA' hVol z' hFine' hExt j j' hj φ hφ e he
  obtain ⟨L, hL, hC⟩ := HL B f T w hE hff hPin hpx Z hX Wt z hG hGA hFine hHL Z' hX' hG' hGA' hVol z' hFine' hExt j j' hj φ hφ
  obtain ⟨hli, hsp⟩ := Hb B f T w hE hff hPin hpx Z hX Wt z hG hGA hFine hHL Z' hX' hG' hGA' hVol z' hFine' hExt j j' hj φ hφ L hL hC
  have hcs := Hc B f T w hE hff hPin hpx Z hX Wt z hG hGA hFine hHL Z' hX' hG' hGA' hVol z' hFine' hExt j j' hj φ hφ L hL hC
  have hac := Ha B f T w hE hff hPin hpx Z hX Wt z hG hGA hFine hHL Z' hX' hG' hGA' hVol z' hFine' hExt j j' hj φ hφ e he L hL hC
  have hnb := Hn B f T w hE hff hPin hpx Z hX Wt z hG hGA hFine hHL Z' hX' hG' hGA' hVol z' hFine' hExt j j' hj φ hφ L hL hC
  have hsb := Hs B f T w hE hff hPin hpx Z hX Wt z hG hGA hFine hHL Z' hX' hG' hGA' hVol z' hFine' hExt j j' hj φ hφ L hL hC
  obtain ⟨C, hCL, c1, c2, c3, c4, c5⟩ := GlobalTheory.Mem.R3.LiftLatBC.forms_of_semilinear_at φ e _ _ _ _ L hL hli hsp hcs hac hnb hsb
  refine ⟨e, C, ⟨c1, c2, c3, c4, c5, hXg, hP, hψ⟩, fun x => ?_⟩
  letI := z.alg
  letI := z'.alg
  have hj0 := hExt.jL j j' hj (Formalism.L2.Col.mtKOk (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 hX ((j : ℕ) + 1))
    (Formalism.L2.Col.mtKOk (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 hX' ((j' : ℕ) + 1)) _ _ (hC x)
  have hj1 : HEq (z'.R.B.jL j' (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))) ((by with_unfolding_all exact ((L x) :))))
      (z.R.B.jL j (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))) ((by with_unfolding_all exact (x :)))) :=
    HEq.trans (heq_of_eq (congrArg _ ((by with_unfolding_all exact ((LinearEquiv.apply_symm_apply (Formalism.L2.Col.GSD.res (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)) (Formalism.L2.Col.mtKOk (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 hX' ((j' : ℕ) + 1))) ((by with_unfolding_all exact ((L x) :)))).symm :)))))
      (HEq.trans hj0 (heq_of_eq (congrArg _ ((by with_unfolding_all exact ((LinearEquiv.apply_symm_apply (Formalism.L2.Col.GSD.res (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)) (Formalism.L2.Col.mtKOk (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 hX ((j : ℕ) + 1))) ((by with_unfolding_all exact (x :)))) :))))))
  have h2 := GlobalTheory.Mem.R3.LiftLatBC.thG_extN hE.1 hExt j j' hj _ _ hj1
  refine HEq.trans (heq_of_eq (congrArg (fun y => (z'.R.toCx3 z'.F).θ' j' _ ((z'.R.toCx3 z'.F).jL j' _ y)) (hCL x))) ?_
  refine HEq.trans (GlobalTheory.Mem.R3.LiftLatBC.theta_jL z'.R z'.F j' _ (z'.pins.phs j') _) (HEq.trans ?_ (GlobalTheory.Mem.R3.LiftLatBC.theta_jL z.R z.F j _ (z.pins.phs j) _).symm)
  exact (by with_unfolding_all exact (h2 :))
end
end
