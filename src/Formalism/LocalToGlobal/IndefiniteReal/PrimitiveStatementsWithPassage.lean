module

public import Formalism.LocalToGlobal.IndefiniteReal.FaceOf3
public import Formalism.LocalToGlobal.IndefiniteReal.LiftCoordinatesInGoodPartOfDefinite
public import Formalism.LocalToGlobal.IndefiniteReal.CutTuples2
public import Formalism.LocalToGlobal.Divisibility.ProjLemmas
public import Formalism.LocalToGlobal.Divisibility.RowLatLemmas
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Formalism.LocalToGlobal.Divisibility.LiftLat
public import Formalism.LocalToGlobal.IndefiniteReal.CxHecke
public import Formalism.LocalToGlobal.IndefiniteReal.RationalAdjoints.RatZOfTests
public import Formalism.LocalToGlobal.IndefiniteReal.IsometricPeriodsOfUnitHypotheses

-- Source module: Formalism.LocalToGlobal.IndefiniteReal.EigSumLeComapSemi

section

@[expose] public section

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.Cx

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV Formalism.L2.Col

section Gen

variable {K : Type} [Field K] {σ : K →+* ℂ}

def cxSys {I : Type} (σ : K →+* ℂ) (C : (I → K) → Prop) : (I → ℂ) → Prop :=
  fun y => ∃ x, C x ∧ y = fun i => σ (x i)

variable {V E : Type} [AddCommGroup V] [Module K V] [AddCommGroup E] [Module ℂ E]

theorem map_pow_sub (f : V →ₛₗ[σ] E) (T : Module.End K V) (S : Module.End ℂ E)
    (h : ∀ v, f (T v) = S (f v)) (a : K) (k : ℕ) (v : V) :
    f (((T - a • 1) ^ k) v) = ((S - σ a • 1) ^ k) (f v) := by
  induction k generalizing v with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Module.End.mul_apply, ih, pow_succ, Module.End.mul_apply]
    congr 1
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub, map_smulₛₗ, h]

theorem map_maxGen (f : V →ₛₗ[σ] E) {T : Module.End K V} {S : Module.End ℂ E}
    (h : ∀ v, f (T v) = S (f v)) {a : K} {v : V} (hv : v ∈ T.maxGenEigenspace a) :
    f v ∈ S.maxGenEigenspace (σ a) := by
  rw [Module.End.mem_maxGenEigenspace] at hv ⊢
  obtain ⟨k, hk⟩ := hv
  exact ⟨k, by rw [← map_pow_sub f T S h a k v, hk, map_zero]⟩

variable {I : Type}

theorem map_eigAt (f : V →ₛₗ[σ] E) {op : I → Module.End K V} {h : I → Module.End ℂ E}
    (hf : ∀ i v, f (op i v) = h i (f v)) {x : I → K} {v : V} (hv : v ∈ eigAt op x) :
    f v ∈ eigAt h (fun i => σ (x i)) := by
  unfold eigAt at hv ⊢
  rw [Submodule.mem_iInf] at hv ⊢
  exact fun i => map_maxGen f (hf i) (hv i)

theorem eigSum_le_comap_semi (f : V →ₛₗ[σ] E) {op : I → Module.End K V} {h : I → Module.End ℂ E}
    (hf : ∀ i v, f (op i v) = h i (f v)) (C : (I → K) → Prop) :
    eigSum op C ≤ (eigSum h (cxSys σ C)).comap f := by
  show (⨆ (x : I → K) (_ : C x), eigAt op x) ≤ _
  refine iSup₂_le fun x hx => ?_
  intro v hv
  rw [Submodule.mem_comap]
  exact eigAt_le_eigSum (op := h) ⟨x, hx, rfl⟩ (map_eigAt f hf hv)

theorem mem_eigSum_iff_map [FiniteDimensional K V] [FiniteDimensional ℂ E] (f : V →ₛₗ[σ] E)
    {op : I → Module.End K V} (hc : PairComm op) (hs : SplitOver op)
    {h : I → Module.End ℂ E} (hch : PairComm h) (hf : ∀ i v, f (op i v) = h i (f v))
    {Z : Submodule K V} (hZ : ∀ i, Z ≤ Z.comap (op i)) (hinj : ∀ z ∈ Z, f z = 0 → z = 0)
    (C : (I → K) → Prop) {v : V} (hv : v ∈ Z) :
    v ∈ eigSum op C ↔ f v ∈ eigSum h (cxSys σ C) := by
  constructor
  · intro hv'
    exact eigSum_le_comap_semi f hf C hv'
  · intro hfv
    have hpv : eigProj hc hs C v ∈ eigSum op C := eigProj_apply_mem hc hs C v
    have h2 : v - eigProj hc hs C v ∈ eigSum op (fun x => ¬ C x) := sub_eigProj_mem hc hs C v
    have hZ2 : v - eigProj hc hs C v ∈ Z := Z.sub_mem hv (eigProj_mem_of_stable hc hs C hZ hv)
    have hf1 : f (v - eigProj hc hs C v) ∈ eigSum h (cxSys σ C) := by
      rw [map_sub]
      exact Submodule.sub_mem _ hfv (eigSum_le_comap_semi f hf C hpv)
    have hf2 : f (v - eigProj hc hs C v) ∈ eigSum h (cxSys σ fun x => ¬ C x) :=
      eigSum_le_comap_semi f hf _ h2
    have hdis : Disjoint (eigSum h (cxSys σ C)) (eigSum h (cxSys σ fun x => ¬ C x)) := by
      apply disjoint_eigSum hch
      rintro y ⟨x, hx, rfl⟩ ⟨x', hx', hxx⟩
      apply hx'
      have e : x' = x := funext fun i => (σ.injective (congrFun hxx i)).symm
      rw [e]
      exact hx
    have h0 : f (v - eigProj hc hs C v) = 0 := (Submodule.disjoint_def.1 hdis) _ hf1 hf2
    have e := hinj _ hZ2 h0
    rw [sub_eq_zero] at e
    rw [e]
    exact hpv

theorem inj_of_li {ι : Type*} (b : Basis ι K V) (f : V →ₛₗ[σ] E)
    (h : LinearIndependent ℂ fun k => f (b k)) : Function.Injective f := by
  refine (injective_iff_map_eq_zero f).2 fun v hv => ?_
  have e := b.linearCombination_repr v
  rw [Finsupp.linearCombination_apply, Finsupp.sum] at e
  have h3 : ∑ i ∈ (b.repr v).support, σ (b.repr v i) • f (b i) = f v := by

    rw [← congrArg f e, map_sum]
    simp only [map_smulₛₗ]
  have hall := linearIndependent_iff'.1 h _ _ (h3.trans hv)
  have hr : b.repr v = 0 := by
    ext i
    by_contra hi
    exact hi (σ.injective ((hall i (Finsupp.mem_support_iff.2 hi)).trans (map_zero σ).symm))
  simpa using congrArg b.repr.symm hr

end Gen

variable {K : Type} [Field K] [NumberField K] [StarRing K]

namespace CxData

variable {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A)

theorem theta_jR_inj (hR : X.KFormR) (t : Bs.Tup) (z : A.FR t) (hz : z ∈ X.Z t)
    (h0 : X.Θ t (X.jR t z) = 0) : z = 0 := by
  simp only [CxData.Z, Submodule.mem_comap, LinearMap.mem_range] at hz
  obtain ⟨w, hw⟩ := hz
  have h1 : X.jR t z = 0 := by
    rw [← inner_self_eq_zero (𝕜 := ℂ), ← hw, LinearMap.adjoint_inner_left, hw, h0, inner_zero_right]
  exact inj_of_li (bR (A := A) t) (X.jR t) (hR t).1 (h1.trans (map_zero _).symm)

theorem theta_jL_inj (hL : X.KFormL) (j : Bs.J) (t : Bs.Tup) (z : A.FL j t) (hz : z ∈ X.Zl j t)
    (h0 : X.θ' j t (X.jL j t z) = 0) : z = 0 := by
  simp only [CxData.Zl, Submodule.mem_comap, LinearMap.mem_range] at hz
  obtain ⟨w, hw⟩ := hz
  have h1 : X.jL j t z = 0 := by
    rw [← inner_self_eq_zero (𝕜 := ℂ), ← hw, LinearMap.adjoint_inner_left, hw, h0, inner_zero_right]
  exact inj_of_li (bL (A := A) j t) (X.jL j t) (hL j t).1 (h1.trans (map_zero _).symm)

variable {fc : DefSub A → DefFace Bs} (cr : Crd A fc) (b : Bool)

theorem iC_cpt_eq (t : Bs.Tup) (x : Fin ((lv (fc X.zs) b).dQ t) → K) :
    X.iC cr b t (cpt Bs.v0.embedding x) = X.Θ t (X.jR t (cr.toR X.zs b t x)) := by
  have hx : x = ∑ k, x k • Pi.single k (1 : K) := by
    funext i
    simp [Finset.sum_apply, Pi.single_apply]
  conv_rhs => rw [hx]

  simp only [map_sum, map_smul, map_smulₛₗ, CxData.iC, lin, Fintype.linearCombination_apply, cpt]

theorem tC_cpt_eq (j : Bs.J) (t : Bs.Tup) (x : Fin ((lv (fc X.zs) b).dZ j t) → K) :
    X.tC cr b j t (cpt Bs.v0.embedding x) = X.θ' j t (X.jL j t (cr.toL X.zs b j t x)) := by
  have hx : x = ∑ k, x k • Pi.single k (1 : K) := by
    funext i
    simp [Finset.sum_apply, Pi.single_apply]
  conv_rhs => rw [hx]

  simp only [map_sum, map_smul, map_smulₛₗ, CxData.tC, lin, Fintype.linearCombination_apply, cpt]

end CxData

section Concrete

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ}
variable (A : FamIn K G Pl0 T m) (X : CxData A.fam.amb)

variable {A X}

theorem toF_mem_Z {B : BlockDat K G Pl0} (ℓ : Lvl K G) (Z : Submodule K B.S.Forms) (y : Fin (B.dZ ℓ Z) → K) :
    B.toF ℓ Z y ∈ Z := by
  have h1 : (B.zE ℓ Z).mulVec y ∈ B.Z0 ℓ Z := by
    rw [BlockDat.zE, subE_mulVec]
    exact Submodule.coe_mem _
  simp only [BlockDat.Z0, BlockDat.inV0, BlockDat.coord, Submodule.mem_comap, Submodule.mem_map,
    Matrix.mulVecLin_apply] at h1
  obtain ⟨w, hw, hwe⟩ := h1
  have e : B.toF ℓ Z y = w := by
    simp only [BlockDat.toF, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
      Matrix.mulVecLin_apply]
    rw [← hwe]
    simp
  rw [e]
  exact hw

variable (P0 : Subgroup G) (ψ0 : P0 →* Kˣ) (P1 : Subgroup G) (ψ1 : P1 →* Kˣ)
  (Dc : ∀ Zs : DefSub A.fam.amb, DefCols (A.side P1 ψ1 Zs)) (Sp : ∀ Zs : DefSub A.fam.amb, SPer (Dc Zs))
  (Zsc : DefSub A.fam.amb → IndefScale A.fam.base)

end Concrete

end Formalism.IndefR.Cx
end
end
end

-- Source module: Formalism.LocalToGlobal.IndefiniteReal.PrimitiveStatementsWithPassage

section

@[expose] public section

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.Cx

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV Formalism.L2.Col

variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type} {m : ℕ}

section Prims3

variable (A3 : FamIn3 K G Pl0 I0 Ty T m)

def cvOf3 (P0 : Subgroup G) (ψ0 : P0 →* Kˣ) (P1 : Subgroup G) (ψ1 : P1 →* Kˣ) : CrdV A3.fam3.amb3 where
  v0R _ b t := match b with
    | false => BlockGood.goodR (A3.A.fam.R t) (A3.A.fam.lvl P0 ψ0)
    | true => BlockGood.goodR (A3.A.fam.R t) (A3.A.fam.lvl P1 ψ1)
  v0L _ b j t := match b with
    | false => BlockGood.goodR (A3.A.fam.L j t) (A3.A.fam.lvlA P0 ψ0)
    | true => BlockGood.goodR (A3.A.fam.L j t) (A3.A.fam.lvlA P1 ψ1)
  hR t := CSDForm.csumForm (A3.A.fam.R t).S
  hL j t := CSDForm.csumForm (A3.A.fam.L j t).S

variable (X : CxData A3.fam3.amb3)

structure HeckeIntertwiningDefinite (hE : ∀ t, (A3.rowI t).OpIx → Module.End ℂ X.EE) : Prop where

  intw : ∀ t i (u : X.FC t), X.Θ t (X.opC t (Sum.inl i) u) = hE t i (X.Θ t u)

  comm : PairComm (hE A3.A.fam.μ0)

  parts : ∀ p : A3.fam3.base3.Ix,
    X.EEp p = eigSum (hE A3.A.fam.μ0) (cxSys A3.fam3.base3.v0.embedding ((A3.rowI A3.A.fam.μ0).HasRes3 p.1))

structure HeckeIntertwiningLifts (hW : ∀ j t, (A3.liftI j t).OpIx → Module.End ℂ (X.W j)) : Prop where

  intw : ∀ j t i (u : X.FLC j t), X.θ' j t (X.opLC j t (Sum.inl i) u) = hW j t i (X.θ' j t u)

  comm : ∀ j, PairComm (hW j A3.A.fam.μ0)

  parts : ∀ (j : Fin m) (p : A3.fam3.base3.Ix),
    X.Wp j p = eigSum (hW j A3.A.fam.μ0)
      (cxSys A3.fam3.base3.v0.embedding ((A3.liftI j A3.A.fam.μ0).HasRes3 (A3.fam3.tr3 j p.1)))

def GEquiv3 (gE : Representation ℂ G X.EE) : Prop :=
  ∀ t (g : G) (x : A3.fam3.amb3.FR t), X.Θ t (X.jR t (A3.fam3.amb3.opR t (Sum.inr g) x)) = gE g (X.Θ t (X.jR t x))

def LiftGroupEquivariance (gW : ∀ j, Representation ℂ G (X.W j)) : Prop :=
  ∀ j t (g : G) (x : A3.fam3.amb3.FL j t),
    X.θ' j t (X.jL j t (A3.fam3.amb3.opL j t (Sum.inr g) x)) = gW j g (X.θ' j t (X.jL j t x))

def typeSp3 (gE : Representation ℂ G X.EE) (P : Subgroup G) (ψ : P →* Kˣ) : Submodule ℂ X.EE :=
  ⨅ h : P, LinearMap.ker (gE (h : G) - (A3.A.fam.v0.embedding ((ψ h : Kˣ) : K)) • LinearMap.id)

def typeSubspace (j : Fin m) (gW : Representation ℂ G (X.W j)) (P : Subgroup G) (ψ : P →* Kˣ) : Submodule ℂ (X.W j) :=
  ⨅ h : P, LinearMap.ker (gW (h : G) - (A3.A.fam.v0.embedding ((ψ h : Kˣ) : K)) • LinearMap.id)

def LiftsEig3 (P : Subgroup G) (ψ : P →* Kˣ) (C : ∀ j : Fin m, ((A3.liftI j A3.A.fam.μ0).OpIx → K) → Prop) : Prop :=
  ∀ j, (A3.A.fam.L j A3.A.fam.μ0).Z0 (A3.A.fam.lvlA P ψ) (X.Zl j A3.A.fam.μ0) =
    (A3.A.fam.L j A3.A.fam.μ0).inV0 (A3.A.fam.lvlA P ψ) (eigSum (A3.liftI j A3.A.fam.μ0).opAll (C j))


variable {A3} in
def LiftsTyp3 (A3 : FamIn3 K G Pl0 I0 Ty T m) (C : ∀ j : Fin m, ((A3.liftI j A3.A.fam.μ0).OpIx → K) → Prop) : Prop :=
  ∀ j x, C j x → A3.fam3.IsType3 (A3.fam3.LI j A3.A.fam.μ0) (A3.fam3.tr3 j) x

variable {P1 : Subgroup G} {ψ1 : P1 →* Kˣ} {Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 P1 ψ1 Zs)}
  {Sp : ∀ Zs : DefSub A3.fam3.amb3, SPer (Dc Zs)} {Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3}

def EEg3 : Submodule ℂ X.EE := LinearMap.range (X.iC (crdOf3 A3 ⊥ 1 P1 ψ1 Dc Sp Zsc) false A3.A.fam.μ0)

def PrincipalLevelBijectivity : Prop :=
  Function.Injective (X.iC (crdOf3 A3 ⊥ 1 P1 ψ1 Dc Sp Zsc) false A3.A.fam.μ0) ∧
    ∀ t, Function.Injective (X.iC (crdOf3 A3 ⊥ 1 P1 ψ1 Dc Sp Zsc) false t) ∧
      LinearMap.range (X.iC (crdOf3 A3 ⊥ 1 P1 ψ1 Dc Sp Zsc) false t) =
        LinearMap.range (X.iC (crdOf3 A3 ⊥ 1 P1 ψ1 Dc Sp Zsc) false A3.A.fam.μ0)

def LevType3 (gE : Representation ℂ G X.EE) (b : Bool) (P : Subgroup G) (ψ : P →* Kˣ) : Prop :=
  X.EEl b = EEg3 A3 X (P1 := P1) (ψ1 := ψ1) (Dc := Dc) (Sp := Sp) (Zsc := Zsc) ⊓ typeSp3 A3 X gE P ψ

def principalFormsSubspace (j : Fin m) : Submodule ℂ (X.W j) :=
  ⨆ t, LinearMap.range (X.tC (crdOf3 A3 ⊥ 1 P1 ψ1 Dc Sp Zsc) false j t)

def LevelTypeOfLifts (gW : ∀ j, Representation ℂ G (X.W j)) (b : Bool) (P : Subgroup G) (ψ : P →* Kˣ) : Prop :=
  ∀ j, LinearMap.range (X.w0C b j) =
    principalFormsSubspace A3 X (P1 := P1) (ψ1 := ψ1) (Dc := Dc) (Sp := Sp) (Zsc := Zsc) j ⊓ typeSubspace A3 X j (gW j) P ψ⁻¹

end Prims3

structure ComplexDataConditionsExceptBaseDecomposition (A3 : FamIn3 K G Pl0 I0 Ty T m) (P0 : Subgroup G) (ψ0 : P0 →* Kˣ) (P1 : Subgroup G) (ψ1 : P1 →* Kˣ)
    (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 P1 ψ1 Zs)) (Sp : ∀ Zs : DefSub A3.fam3.amb3, SPer (Dc Zs))
    (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3) (X : CxData A3.fam3.amb3) (s : ℕ)
    (hE : ∀ t, (A3.rowI t).OpIx → Module.End ℂ X.EE)
    (hW : ∀ j t, (A3.liftI j t).OpIx → Module.End ℂ (X.W j)) (gE : Representation ℂ G X.EE)
    (gW : ∀ j, Representation ℂ G (X.W j)) : Prop where

  kFormR : X.KFormR

  kFormL : X.KFormL

  jIsoR : X.JIsoR (cvOf3 A3 P0 ψ0 P1 ψ1)

  jIsoL : X.JIsoL (cvOf3 A3 P0 ψ0 P1 ψ1)

  npTie : X.nP false = (Nat.card P0 : ℝ) ∧ X.nP true = (Nat.card P1 : ℝ)

  ok : A3.fam3.Ok3 s

  sep : A3.fam3.TypesSep3

  heckeR : ∀ t, (A3.A.fam.R t).OkH ∧ (A3.rowI t).InertRationalAdjoint

  heckeL : ∀ j t, (A3.A.fam.L j t).OkH ∧ (A3.liftI j t).InertRationalAdjoint

  thetaR : HeckeIntertwiningDefinite A3 X hE

  thetaL : HeckeIntertwiningLifts A3 X hW

  gUnit : ∀ (g : G) (x y : X.EE), ⟪gE g x, gE g y⟫_ℂ = ⟪x, y⟫_ℂ

  gEquiv : GEquiv3 A3 X gE

  lev0 : LevType3 A3 X (P1 := P1) (ψ1 := ψ1) (Dc := Dc) (Sp := Sp) (Zsc := Zsc) gE false P0 ψ0

  lev1 : LevType3 A3 X (P1 := P1) (ψ1 := ψ1) (Dc := Dc) (Sp := Sp) (Zsc := Zsc) gE true P1 ψ1

  h2P : PrincipalLevelBijectivity A3 X (P1 := P1) (ψ1 := ψ1) (Dc := Dc) (Sp := Sp) (Zsc := Zsc)

  gUnitL : ∀ j (g : G) (x y : X.W j), ⟪gW j g x, gW j g y⟫_ℂ = ⟪x, y⟫_ℂ

  gEquivL : LiftGroupEquivariance A3 X gW

  lower_level_lift_type : LevelTypeOfLifts A3 X (P1 := P1) (ψ1 := ψ1) (Dc := Dc) (Sp := Sp) (Zsc := Zsc) gW false P0 ψ0

  inBlock : X.zs.InBlock

  rowTest : Formalism.IndefR.Rat.RowTest X

  liftTest : Formalism.IndefR.Rat.LiftTest X

  pos : ∀ b, (lv (faceOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs) b).Pos

  h0 : X.H0

  h4pos : X.H4pos

  thmBop : ∀ b, X.ThmBop b

  partsE : ∀ b, X.PartsE b

  kForm : X.KForm false

  mLat : X.MLat false

  ewNorm : X.EWnorm false

  thmAop : X.ThmAop false

  partsW : X.PartsW false

  base_lift_test : Formalism.IndefR.Rat.LiftTestB X false

  galD : X.GalD (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) false

  dimParts : X.DimParts false

structure ComplexDataConditionsBaseLevel (A3 : FamIn3 K G Pl0 I0 Ty T m) (P0 : Subgroup G) (ψ0 : P0 →* Kˣ) (P1 : Subgroup G) (ψ1 : P1 →* Kˣ)
    (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 P1 ψ1 Zs)) (Sp : ∀ Zs : DefSub A3.fam3.amb3, SPer (Dc Zs))
    (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3) (X : CxData A3.fam3.amb3) (s : ℕ)
    (C0 : ∀ j : Fin m, ((A3.liftI j A3.A.fam.μ0).OpIx → K) → Prop)
    (hE : ∀ t, (A3.rowI t).OpIx → Module.End ℂ X.EE)
    (hW : ∀ j t, (A3.liftI j t).OpIx → Module.End ℂ (X.W j)) (gE : Representation ℂ G X.EE)
    (gW : ∀ j, Representation ℂ G (X.W j)) : Prop
    extends ComplexDataConditionsExceptBaseDecomposition A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X s hE hW gE gW where

  eig0 : LiftsEig3 A3 X P0 ψ0 C0

  typ0 : LiftsTyp3 A3 C0

structure PrimitiveStatementsBaseLiftsOnly (A3 : FamIn3 K G Pl0 I0 Ty T m) (P0 : Subgroup G) (ψ0 : P0 →* Kˣ) (P1 : Subgroup G) (ψ1 : P1 →* Kˣ)
    (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 P1 ψ1 Zs)) (Sp : ∀ Zs : DefSub A3.fam3.amb3, SPer (Dc Zs))
    (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3) (X : CxData A3.fam3.amb3) (s : ℕ)
    (C0 : ∀ j : Fin m, ((A3.liftI j A3.A.fam.μ0).OpIx → K) → Prop)
    (eV : ∀ t, (Fin ((faceOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Df1.nV t) → K) →ₗ[K] A3.fam3.amb3.FR t)
    (sEE : X.EE →ₗ⋆[ℂ] (faceOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Sp.HH)
    (C CH : ℝ)
    (hE : ∀ t, (A3.rowI t).OpIx → Module.End ℂ X.EE)
    (hW : ∀ j t, (A3.liftI j t).OpIx → Module.End ℂ (X.W j)) (gE : Representation ℂ G X.EE)
    (gW : ∀ j, Representation ℂ G (X.W j)) (cf : ConvFace A3.fam3.base3) : Prop
    extends ComplexDataConditionsBaseLevel A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X s C0 hE hW gE gW where

  w1 : ∀ w, X.W1 (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) ((faceOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Z.num C CH) w → w ∈ X.Tw

  l3 : (X.data (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) false).L3 ((faceOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Z.num C CH)

  on : (X.data (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) false).ON ((faceOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Z.num C CH)

  l6 : (X.data (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) true).L6 ((faceOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Z.num C CH)

  evTie : X.EVTie (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) (cvOf3 A3 P0 ψ0 P1 ψ1) eV

  seeIso : X.SEEIso sEE

  miStar : X.MIstar2 eV sEE

  conv : IndefConv A3.fam3.base3 X.μ cf

  heckeRB : Nonempty (X.HeckeRowsC (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) false cf)

  heckeWB : Nonempty (X.HeckeWC false cf)

  heckeRC : Nonempty (X.HeckeRowsC (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) true cf)

  fun0 : (X.data (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) false).FUN ((faceOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Z.num C CH)

structure PrimitiveStatementsWithPassage (A3 : FamIn3 K G Pl0 I0 Ty T m) (P0 : Subgroup G) (ψ0 : P0 →* Kˣ) (P1 : Subgroup G) (ψ1 : P1 →* Kˣ)
    (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 P1 ψ1 Zs)) (Sp : ∀ Zs : DefSub A3.fam3.amb3, SPer (Dc Zs))
    (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3) (X : CxData A3.fam3.amb3) (s : ℕ)
    (C0 : ∀ j : Fin m, ((A3.liftI j A3.A.fam.μ0).OpIx → K) → Prop)
    (eV : ∀ t, (Fin ((faceOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Df1.nV t) → K) →ₗ[K] A3.fam3.amb3.FR t)
    (sEE : X.EE →ₗ⋆[ℂ] (faceOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Sp.HH)
    (C CH : ℝ)
    (hE : ∀ t, (A3.rowI t).OpIx → Module.End ℂ X.EE)
    (hW : ∀ j t, (A3.liftI j t).OpIx → Module.End ℂ (X.W j)) (gE : Representation ℂ G X.EE)
    (gW : ∀ j, Representation ℂ G (X.W j)) (cf : ConvFace A3.fam3.base3) : Prop
    extends PrimitiveStatementsBaseLiftsOnly A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X s C0 eV sEE C CH hE hW gE gW cf where

  passage : Passage ((faceOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Z.num C CH)
    (X.data (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) false) (X.data (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) true)

end Formalism.IndefR.Cx
end
end
end
