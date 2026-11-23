module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.RowsExhaust
public import Formalism.LocalToGlobal.Divisibility.RowSideTie
public import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMtTieCoord
import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumLocalCongruenceLengthEqRationalLength
import Formalism.LocalToGlobal.Divisibility.ClassSum
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConcreteProjectorEqOrthogonalProjection

section

@[expose] public section

open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef NumberField IsDedekindDomain GlobalTheory.EtaJoin Formalism.DivisionValues

noncomputable section

namespace GlobalTheory.EtaJoin

section Gen

variable {K : Type} [Field K] [StarRing K] {n d : ℕ}

theorem hform_eq_dot (H : Matrix (Fin n) (Fin n) K) (x y : Fin n → K) :
    hform H x y = star x ⬝ᵥ H.mulVec y := by
  simp only [hform, Matrix.toLinearMapₛₗ₂'_apply, dotProduct, Matrix.mulVec, Finset.mul_sum, RingHom.id_apply]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [starRingEnd_apply, Pi.star_apply]; ring

theorem hform_orthProj (H : Matrix (Fin n) (Fin n) K) (E : Matrix (Fin n) (Fin d) K) (Pr : Matrix (Fin d) (Fin n) K)
    (h : IsOrthProj H E Pr) (u : Fin d → K) (x : Fin n → K) :
    hform H (E.mulVec u) (x - E.mulVec (Pr.mulVec x)) = 0 := by
  have e : x - E.mulVec (Pr.mulVec x) = (1 - E * Pr).mulVec x := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_mulVec]
  rw [hform_eq_dot, e, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    h.2, Matrix.zero_mulVec, dotProduct_zero]

variable {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] (σ : K →+* ℂ) (J : (Fin n → K) →ₛₗ[σ] W)

theorem semi_expand (y : Fin n → K) : J y = ∑ i, σ (y i) • J (Pi.single i 1) := by
  conv_lhs => rw [← Finset.univ_sum_single y]

  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : (Pi.single i (y i) : Fin n → K) = y i • Pi.single i 1 := by
    ext k; by_cases hk : k = i
    · subst hk; simp
    · simp [Pi.single_apply, hk]
  rw [this, LinearMap.map_smulₛₗ]

theorem semi_injective (hli : LinearIndependent ℂ fun i => J (Pi.single i 1)) : Function.Injective J := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro y hy
  rw [semi_expand σ J y] at hy
  have h0 := (Fintype.linearIndependent_iff.1 hli) (fun i => σ (y i)) hy
  funext i
  exact σ.injective (by rw [h0 i]; simp)

theorem semi_mulVec_mem (E : Matrix (Fin n) (Fin d) K) (c : Fin d → K) :
    J (E.mulVec c) ∈ Submodule.span ℂ (Set.range fun k => J (E.mulVec (Pi.single k 1))) := by
  have e : E.mulVec c = ∑ k, c k • E.mulVec (Pi.single k 1) := by
    conv_lhs => rw [← Finset.univ_sum_single c]
    rw [Matrix.mulVec_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Matrix.mulVec_smul]
    congr 1
    ext a; by_cases ha : a = k
    · subst ha; simp
    · simp [Pi.single_apply, ha]

  rw [e, map_sum]
  refine Submodule.sum_mem _ fun k _ => ?_
  rw [LinearMap.map_smulₛₗ]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

end Gen

end GlobalTheory.EtaJoin

namespace GlobalTheory.EtaJoin

section Gen2

variable {K : Type} [Field K] [NumberField K] [StarRing K] {n d : ℕ} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  {σ : K →+* ℂ} {V : Type} [AddCommGroup V] [Module K V]

theorem tied_orthProj (e : (Fin n → K) ≃ₗ[K] V) (jV : V →ₛₗ[σ] W) (H Eop : Matrix (Fin n) (Fin n) K) (op : W →ₗ[ℂ] W)
    (E : Matrix (Fin n) (Fin d) K) (Pr : Matrix (Fin d) (Fin n) K) (hP : IsOrthProj H E Pr)
    (hF : FormsTie σ (jV.comp e.toLinearMap) H Eop op) (Z : Submodule ℂ W)
    (hZ : Z = Submodule.span ℂ (Set.range fun k => jV (e (E.mulVec (Pi.single k 1))))) :
    Function.Injective (e.toLinearMap ∘ₗ E.mulVecLin) ∧ Z.comap jV = LinearMap.range (e.toLinearMap ∘ₗ E.mulVecLin) ∧
      ∀ x, e x - (e.toLinearMap ∘ₗ E.mulVecLin) (Pr.mulVec x) ∈ (Zᗮ).comap jV := by
  have hin : ∀ x y, inner ℂ (jV (e x)) (jV (e y)) = σ (hform H x y) := hF.inner
  have hJinj : Function.Injective fun x => jV (e x) := fun a b h => semi_injective σ (jV.comp e.toLinearMap) hF.li h
  have hgen : ∀ c, jV (e (E.mulVec c)) ∈ Z := by
    intro c; rw [hZ]; exact semi_mulVec_mem σ (jV.comp e.toLinearMap) E c
  have horth : ∀ x, jV (e (x - E.mulVec (Pr.mulVec x))) ∈ Zᗮ := by
    intro x
    rw [Submodule.mem_orthogonal]
    intro u hu
    rw [hZ] at hu
    induction hu using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨k, rfl⟩ := hv
      show inner ℂ (jV (e (E.mulVec (Pi.single k 1)))) _ = 0
      rw [hin, hform_orthProj _ _ _ hP, map_zero]
    | zero => exact inner_zero_left _
    | add a b _ _ ha hb => rw [inner_add_left, ha, hb, add_zero]
    | smul c a _ ha => rw [inner_smul_left, ha, mul_zero]
  have hEinj : Function.Injective E.mulVec := by
    intro a b hab
    have := congrArg Pr.mulVec hab
    simp only [Matrix.mulVec_mulVec, hP.1, Matrix.one_mulVec] at this
    exact this
  refine ⟨?_, ?_, ?_⟩
  · exact e.injective.comp hEinj
  · ext y
    constructor
    · intro hy
      rw [Submodule.mem_comap] at hy
      obtain ⟨x, rfl⟩ := e.surjective y
      have hw1 : jV (e (x - E.mulVec (Pr.mulVec x))) ∈ Z := by
        rw [map_sub, map_sub]; exact Submodule.sub_mem _ hy (hgen _)
      have hw0 : jV (e (x - E.mulVec (Pr.mulVec x))) = 0 :=
        inner_self_eq_zero.1 ((Submodule.mem_orthogonal _ _).1 (horth x) _ hw1)
      have hw : x = E.mulVec (Pr.mulVec x) := by
        refine sub_eq_zero.1 (hJinj ?_)
        simp only [map_zero]; exact hw0
      exact ⟨Pr.mulVec x, by simp only [LinearMap.comp_apply, Matrix.mulVecLin_apply, LinearEquiv.coe_coe]; rw [← hw]⟩
    · rintro ⟨c, rfl⟩
      exact hgen c
  · intro x
    rw [Submodule.mem_comap]
    have e1 : e x - (e.toLinearMap ∘ₗ E.mulVecLin) (Pr.mulVec x) = e (x - E.mulVec (Pr.mulVec x)) := by
      simp only [LinearMap.comp_apply, Matrix.mulVecLin_apply, LinearEquiv.coe_coe, map_sub]
    rw [e1]; exact horth x

end Gen2

theorem concreteProj_orth : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (m : ℕ) (A : FamIn D.what₂.LL G Pl0 T m) (P : Subgroup G) (ψ : P →* D.what₂.LLˣ) (Zs : DefSub A.fam.amb) (tup : T → D.what₂.Tup) (eMt : ∀ (i : Fin m) (t : T), (Fin (lDim D A P ψ i t) → D.what₂.LL) ≃ₗ[D.what₂.LL] D.what₂.MtL (tup t) ((i : ℕ) + 1)) (s : ℕ), A.fam.Ok s → ∀ (i : Fin m) (t : T), FormsTie D.what₂.embLL ((D.what₂.jMt (tup t) ((i : ℕ) + 1)).comp (eMt i t).toLinearMap) (lH D A P ψ i t) (lE D A P ψ i t) (D.what₂.eMt (tup t) ((i : ℕ) + 1)) → Idx.Z0 D (tup t) ((i : ℕ) + 1) = Submodule.span ℂ (Set.range fun k => (D.what₂.jMt (tup t) ((i : ℕ) + 1)) (eMt i t ((lZ0 D A P ψ Zs i t).mulVec (Pi.single k 1)))) → Function.Injective ((eMt i t).toLinearMap ∘ₗ (lZ0 D A P ψ Zs i t).mulVecLin) ∧ ratSub D (tup t) ((i : ℕ) + 1) (Idx.Z0 D (tup t) ((i : ℕ) + 1)) = LinearMap.range ((eMt i t).toLinearMap ∘ₗ (lZ0 D A P ψ Zs i t).mulVecLin) ∧ ∀ x, eMt i t x - ((eMt i t).toLinearMap ∘ₗ (lZ0 D A P ψ Zs i t).mulVecLin) ((lPrj D A P ψ Zs i t).mulVec x) ∈ ratSub D (tup t) ((i : ℕ) + 1) (Idx.Z0 D (tup t) ((i : ℕ) + 1))ᗮ := by
  intro D G _ _ Pl0 T m A P ψ Zs tup eMt s hOk i t hF hZ
  have hB : BlockHyp (A.fam.L i t) (A.fam.lvlA P ψ) A.fam.v0 s := ⟨hOk.conj, fun χ hχ => hOk.irr χ hχ, hOk.lifts i t⟩
  have hP : IsOrthProj (lH D A P ψ i t) (lZ0 D A P ψ Zs i t) (lPrj D A P ψ Zs i t) :=
    BlockDat.lf_l_proj (Z := Zs.Zl i t) hB
  exact tied_orthProj (eMt i t) (D.what₂.jMt (tup t) ((i : ℕ) + 1)) _ _ _ _ _ hP hF _ hZ

end GlobalTheory.EtaJoin
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConcreteProjectorEqOrthogonalProjectionStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef NumberField IsDedekindDomain GlobalTheory.EtaJoin

theorem _root_.GlobalTheory.T.concreteProjector_eq_orthogonalProjection : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (m : ℕ) (A : FamIn D.what₂.LL G Pl0 T m) (P : Subgroup G) (ψ : P →* D.what₂.LLˣ) (Zs : DefSub A.fam.amb) (tup : T → D.what₂.Tup) (eMt : ∀ (i : Fin m) (t : T), (Fin (lDim D A P ψ i t) → D.what₂.LL) ≃ₗ[D.what₂.LL] D.what₂.MtL (tup t) ((i : ℕ) + 1)) (s : ℕ), A.fam.Ok s → ∀ (i : Fin m) (t : T), FormsTie D.what₂.embLL ((D.what₂.jMt (tup t) ((i : ℕ) + 1)).comp (eMt i t).toLinearMap) (lH D A P ψ i t) (lE D A P ψ i t) (D.what₂.eMt (tup t) ((i : ℕ) + 1)) → Idx.Z0 D (tup t) ((i : ℕ) + 1) = Submodule.span ℂ (Set.range fun k => (D.what₂.jMt (tup t) ((i : ℕ) + 1)) (eMt i t ((lZ0 D A P ψ Zs i t).mulVec (Pi.single k 1)))) → Function.Injective ((eMt i t).toLinearMap ∘ₗ (lZ0 D A P ψ Zs i t).mulVecLin) ∧ ratSub D (tup t) ((i : ℕ) + 1) (Idx.Z0 D (tup t) ((i : ℕ) + 1)) = LinearMap.range ((eMt i t).toLinearMap ∘ₗ (lZ0 D A P ψ Zs i t).mulVecLin) ∧ ∀ x, eMt i t x - ((eMt i t).toLinearMap ∘ₗ (lZ0 D A P ψ Zs i t).mulVecLin) ((lPrj D A P ψ Zs i t).mulVec x) ∈ ratSub D (tup t) ((i : ℕ) + 1) (Idx.Z0 D (tup t) ((i : ℕ) + 1))ᗮ := by
  first | exact @GlobalTheory.EtaJoin.concreteProj_orth | exact GlobalTheory.EtaJoin.concreteProj_orth | (intros; apply GlobalTheory.EtaJoin.concreteProj_orth <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RationalFormLengthEqDefiniteFamily

section

@[expose] public section

open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef NumberField IsDedekindDomain GlobalTheory.EtaJoin

noncomputable section

namespace GlobalTheory.EtaJoin.Side

theorem length_quot_map {R M M' : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
    (f : M →ₗ[R] M') (hf : Function.Injective f) (P Q : Submodule R M) :
    Module.length R (P.map f ⧸ (Q.map f).comap (P.map f).subtype) = Module.length R (P ⧸ Q.comap P.subtype) := by
  refine (LinearEquiv.length_eq (Submodule.Quotient.equiv (Q.comap P.subtype) ((Q.map f).comap (P.map f).subtype)
    (Submodule.equivMapOfInjective f hf P) ?_)).symm
  ext ⟨y, hy⟩
  simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.subtype_apply]
  constructor
  · rintro ⟨⟨x, hx⟩, hxQ, hxy⟩
    refine ⟨x, hxQ, ?_⟩
    have := congrArg Subtype.val hxy
    simpa using this
  · rintro ⟨x, hxQ, hxy⟩
    obtain ⟨x', hx', rfl⟩ := hy
    have : x = x' := hf hxy
    subst this
    exact ⟨⟨x, hx'⟩, hxQ, rfl⟩


open scoped Formalism.L2.Col in
theorem lenUW_map {K : Type} [Field K] [NumberField K] {V V' : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']
    (φ : V →ₗ[K] V') (hφ : Function.Injective φ) (w : HeightOneSpectrum (𝓞 K)) (A B : Submodule (𝓞 K) V) :
    Formalism.L2.Col.lenUW w (A.map (φ.restrictScalars (𝓞 K))) (B.map (φ.restrictScalars (𝓞 K))) = Formalism.L2.Col.lenUW w A B := by
  unfold Formalism.L2.Col.lenUW Formalism.L2.Col.lenW
  rw [Formalism.L2.Col.atW_map, Formalism.L2.Col.atW_map,
    length_quot_map (φ.restrictScalars (Formalism.L2.Col.Ow w)) hφ]

theorem lat_eq_map (D : D7) (μ : D.what₂.Tup) (j : ℕ) {n : ℕ} (e : (Fin n → D.what₂.LL) ≃ₗ[D.what₂.LL] D.what₂.MtL μ j)
    (N : Submodule (𝓞 D.what₂.LL) (Fin n → D.what₂.LL))
    (hL : OLatTie D.what₂.embLL (D.what₂.MtLat μ j) ((D.what₂.jMt μ j).comp e.toLinearMap) N) :
    lat D μ j = N.map (e.toLinearMap.restrictScalars (𝓞 D.what₂.LL)) := by
  classical
  apply le_antisymm
  · rw [lat, Submodule.span_le]
    intro y hy
    obtain ⟨x, rfl⟩ := e.surjective y
    refine ⟨x, ?_, rfl⟩
    show x ∈ N
    rw [hL.2 x]
    refine ⟨fun v => if v = D.what₂.jMt μ j (e x) then 1 else 0, ?_⟩
    rw [Finset.sum_eq_single (D.what₂.jMt μ j (e x))]
    · simp
    · intro b _ hb
      simp [hb]
    · intro h
      exact absurd hy h
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨c, hc⟩ := (hL.2 x).1 hx
    choose! g hg using D.what₂.MtLat_sub μ j
    have hx' : e x = ∑ v ∈ (D.what₂.MtLat μ j).gen, (c v) • g v := by
      apply GlobalTheory.Mem.LiftForms.jMt_injective μ j

      rw [map_sum]
      have hc' : D.what₂.jMt μ j (e x) = ∑ v ∈ (D.what₂.MtLat μ j).gen, D.what₂.embLL (c v : D.what₂.LL) • v := hc
      rw [hc']
      refine Finset.sum_congr rfl fun v hv => ?_
      rw [← algebraMap_smul D.what₂.LL (c v) (g v), map_smulₛₗ, hg v hv]
    show e x ∈ lat D μ j
    rw [hx']
    refine Submodule.sum_mem _ fun v hv => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    show D.what₂.jMt μ j (g v) ∈ (D.what₂.MtLat μ j).gen
    rw [hg v hv]
    exact hv

theorem zRat_and_etaRat_eq : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (m : ℕ) (A : FamIn D.what₂.LL G Pl0 T m) (P : Subgroup G) (ψ : P →* D.what₂.LLˣ) (Zs : DefSub A.fam.amb) (tup : T → D.what₂.Tup) (eMt : ∀ (i : Fin m) (t : T), (Fin (lDim D A P ψ i t) → D.what₂.LL) ≃ₗ[D.what₂.LL] D.what₂.MtL (tup t) ((i : ℕ) + 1)) (s : ℕ), A.fam.Ok s → ∀ (i : Fin m) (t : T), FormsTie D.what₂.embLL ((D.what₂.jMt (tup t) ((i : ℕ) + 1)).comp (eMt i t).toLinearMap) (lH D A P ψ i t) (lE D A P ψ i t) (D.what₂.eMt (tup t) ((i : ℕ) + 1)) → OLatTie D.what₂.embLL (D.what₂.MtLat (tup t) ((i : ℕ) + 1)) ((D.what₂.jMt (tup t) ((i : ℕ) + 1)).comp (eMt i t).toLinearMap) (lNab D A P ψ i t) → Idx.Z0 D (tup t) ((i : ℕ) + 1) = Submodule.span ℂ (Set.range fun k => (D.what₂.jMt (tup t) ((i : ℕ) + 1)) (eMt i t ((lZ0 D A P ψ Zs i t).mulVec (Pi.single k 1)))) → ZRat D (tup t) ((i : ℕ) + 1) ∧ ∀ w, etaRat D (tup t) ((i : ℕ) + 1) w = A.fam.etaJ P ψ Zs i t (D.plEq w) := by
  intro D G _ _ Pl0 T m A P ψ Zs tup eMt s hOk i t hF hL hZ
  obtain ⟨hinj, hrange, hproj⟩ := GlobalTheory.T.concreteProjector_eq_orthogonalProjection D G Pl0 T m A P ψ Zs tup eMt s hOk i t hF hZ
  have hB : BlockHyp (A.fam.L i t) (A.fam.lvlA P ψ) A.v0 s := ⟨hOk.conj, hOk.irr, hOk.lifts i t⟩
  have hcut := BlockDat.lf_cut_nab (Z := Zs.Zl i t) hB
  have hlat := lat_eq_map D (tup t) ((i : ℕ) + 1) (eMt i t) _ hL
  set e := eMt i t with he
  set ψL := (e.toLinearMap ∘ₗ (lZ0 D A P ψ Zs i t).mulVecLin) with hψL
  set R := ratSub D (tup t) ((i : ℕ) + 1) (Idx.Z0 D (tup t) ((i : ℕ) + 1)) with hR
  set Rp := ratSub D (tup t) ((i : ℕ) + 1) (Idx.Z0 D (tup t) ((i : ℕ) + 1))ᗮ with hRp
  have hbot : ∀ y, y ∈ R → y ∈ Rp → y = 0 := by
    intro y h1 h2
    apply GlobalTheory.Mem.LiftForms.jMt_injective (tup t) ((i : ℕ) + 1)
    rw [map_zero]
    have h3 : D.what₂.jMt (tup t) ((i : ℕ) + 1) y ∈ Idx.Z0 D (tup t) ((i : ℕ) + 1) ⊓ (Idx.Z0 D (tup t) ((i : ℕ) + 1))ᗮ :=
      ⟨h1, h2⟩
    rw [Submodule.inf_orthogonal_eq_bot] at h3
    exact h3
  have hmemR : ∀ z, ψL z ∈ R := fun z => by rw [hrange]; exact LinearMap.mem_range_self _ z
  have hup : up D (tup t) ((i : ℕ) + 1) =
      ((A.fam.L i t).Tl (A.fam.lvlA P ψ) (Zs.Zl i t)).map (ψL.restrictScalars (𝓞 D.what₂.LL)) := by
    ext y
    constructor
    · rintro ⟨hyR, hy⟩
      obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 hy
      rw [hlat] at ha
      obtain ⟨x, hx, rfl⟩ := ha
      have hd : y - ψL ((lPrj D A P ψ Zs i t).mulVec x) = 0 := by
        apply hbot
        · exact R.sub_mem hyR (hmemR _)
        · have : y - ψL ((lPrj D A P ψ Zs i t).mulVec x) = (e x - ψL ((lPrj D A P ψ Zs i t).mulVec x)) + b := by
            rw [← hab]
            simp only [LinearMap.restrictScalars_apply, LinearEquiv.coe_coe]
            abel
          rw [this]
          exact Rp.add_mem (hproj x) hb
      refine ⟨(lPrj D A P ψ Zs i t).mulVec x, ⟨x, hx, rfl⟩, ?_⟩
      show ψL _ = y
      exact (sub_eq_zero.1 hd).symm
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      refine ⟨hmemR _, Submodule.mem_sup.2 ⟨e x, ?_, ψL ((lPrj D A P ψ Zs i t).mulVec x) - e x, ?_, ?_⟩⟩
      · rw [hlat]
        exact ⟨x, hx, rfl⟩
      · show _ ∈ Rp
        rw [← neg_sub]
        exact Rp.neg_mem (hproj x)
      · show e x + (ψL ((lPrj D A P ψ Zs i t).mulVec x) - e x) = ψL ((lPrj D A P ψ Zs i t).mulVec x)
        abel
  have hlow : low D (tup t) ((i : ℕ) + 1) =
      ((A.fam.L i t).cutZ (A.fam.lvlA P ψ) (Zs.Zl i t)).map (ψL.restrictScalars (𝓞 D.what₂.LL)) := by
    ext y
    constructor
    · rintro ⟨hy, hyR⟩
      have hyR' : y ∈ R := hyR
      rw [hrange] at hyR'
      obtain ⟨z, rfl⟩ := hyR'
      rw [hlat] at hy
      obtain ⟨x, hx, hxz⟩ := hy
      have hxz' : x = (lZ0 D A P ψ Zs i t).mulVec z := e.injective hxz
      refine ⟨z, ?_, rfl⟩
      rw [← hcut]
      show (lZ0 D A P ψ Zs i t).mulVec z ∈ lNab D A P ψ i t
      rw [← hxz']
      exact hx
    · rintro ⟨z, hz, rfl⟩
      refine ⟨?_, hmemR z⟩
      rw [hlat]
      rw [← hcut] at hz
      exact ⟨(lZ0 D A P ψ Zs i t).mulVec z, hz, rfl⟩
  refine ⟨?_, fun w => ?_⟩
  · rw [ZRat, eq_top_iff]
    intro y _
    obtain ⟨x, rfl⟩ := e.surjective y
    refine Submodule.mem_sup.2 ⟨ψL ((lPrj D A P ψ Zs i t).mulVec x), hmemR _, e x - ψL ((lPrj D A P ψ Zs i t).mulVec x),
      hproj x, ?_⟩
    abel
  · rw [etaRat, hup, hlow, lenUW_map ψL hinj]
    rfl

end GlobalTheory.EtaJoin.Side
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RationalFormLengthEqDefiniteFamilyStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef NumberField IsDedekindDomain GlobalTheory.EtaJoin

theorem _root_.GlobalTheory.T.rationalFormLength_eq_definiteFamily : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (m : ℕ) (A : FamIn D.what₂.LL G Pl0 T m) (P : Subgroup G) (ψ : P →* D.what₂.LLˣ) (Zs : DefSub A.fam.amb) (tup : T → D.what₂.Tup) (eMt : ∀ (i : Fin m) (t : T), (Fin (lDim D A P ψ i t) → D.what₂.LL) ≃ₗ[D.what₂.LL] D.what₂.MtL (tup t) ((i : ℕ) + 1)) (s : ℕ), A.fam.Ok s → ∀ (i : Fin m) (t : T), FormsTie D.what₂.embLL ((D.what₂.jMt (tup t) ((i : ℕ) + 1)).comp (eMt i t).toLinearMap) (lH D A P ψ i t) (lE D A P ψ i t) (D.what₂.eMt (tup t) ((i : ℕ) + 1)) → OLatTie D.what₂.embLL (D.what₂.MtLat (tup t) ((i : ℕ) + 1)) ((D.what₂.jMt (tup t) ((i : ℕ) + 1)).comp (eMt i t).toLinearMap) (lNab D A P ψ i t) → Idx.Z0 D (tup t) ((i : ℕ) + 1) = Submodule.span ℂ (Set.range fun k => (D.what₂.jMt (tup t) ((i : ℕ) + 1)) (eMt i t ((lZ0 D A P ψ Zs i t).mulVec (Pi.single k 1)))) → ZRat D (tup t) ((i : ℕ) + 1) ∧ ∀ w, etaRat D (tup t) ((i : ℕ) + 1) w = A.fam.etaJ P ψ Zs i t (D.plEq w) := by
  first | exact @GlobalTheory.EtaJoin.Side.zRat_and_etaRat_eq | exact GlobalTheory.EtaJoin.Side.zRat_and_etaRat_eq | (intros; apply GlobalTheory.EtaJoin.Side.zRat_and_etaRat_eq <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumLocalCongruenceLengthEqRationalLengthStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef NumberField IsDedekindDomain GlobalTheory.EtaJoin

theorem _root_.GlobalTheory.T.sum_localCongruenceLength_eq_rationalLength : ∀ (D : D7) (M : MtFam D) (T : NormalizedLocalCompatibility D M) (j : ℕ) (w : D.what₂.places.Pl), 1 ≤ j → j ≤ D.R.m → D.what₂.muAt w ≠ D.what₂.mu0 → HeckeStdTw T.B → LatStable T.B j w → ZRat D (D.what₂.muTw w) j → (∀ i ∈ D.nd.locs j w, SpecPr D i) → D.what₂.etaJ j w = etaRat D (D.what₂.muTw w) j w := by
  first | exact @GlobalTheory.EtaJoinSum.sum_etaLoc_eq_etaRat | exact GlobalTheory.EtaJoinSum.sum_etaLoc_eq_etaRat | (intros; apply GlobalTheory.EtaJoinSum.sum_etaLoc_eq_etaRat <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaJEqZeroOfUntwisted

section

@[expose] public section

open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef NumberField IsDedekindDomain GlobalTheory.EtaJoin

namespace GlobalTheory

theorem etaJ_eq_zero_of_untwisted (D : D7) (j : ℕ) (w : D.what₂.places.Pl) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m)
    (hw : D.what₂.muAt w = D.what₂.mu0) : D.what₂.etaJ j w = 0 := by
  rw [D.etaJ_tie j w h1 h2]
  refine Finset.sum_eq_zero fun i hi => ?_
  exact absurd (by rw [((D.nd.locs_mem j w i).1 hi).2]; exact hw) (D.nd.w_tw i)

theorem etaJ_join : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (m : ℕ) (A : FamIn D.what₂.LL G Pl0 T m) (P : Subgroup G) (ψ : P →* D.what₂.LLˣ) (Zs : DefSub A.fam.amb) (tup : T → D.what₂.Tup) (eMt : ∀ (i : Fin m) (t : T), (Fin (lDim D A P ψ i t) → D.what₂.LL) ≃ₗ[D.what₂.LL] D.what₂.MtL (tup t) ((i : ℕ) + 1)) (s : ℕ), A.fam.Ok s → m ≤ D.R.m → ∀ (S0 : IndefData (A.side P ψ Zs)) (M : MtFam D) (Tn : NormalizedLocalCompatibility D M), TupTie D A S0 tup → (∀ y, y ∈ S0.Tw ↔ S0.μ y ≠ A.μ0) → (∀ (i : Fin m), ∀ y ∈ S0.Tw, FormsTie D.what₂.embLL ((D.what₂.jMt (tup (S0.μ y)) ((i : ℕ) + 1)).comp (eMt i (S0.μ y)).toLinearMap) (lH D A P ψ i (S0.μ y)) (lE D A P ψ i (S0.μ y)) (D.what₂.eMt (tup (S0.μ y)) ((i : ℕ) + 1)) ∧ OLatTie D.what₂.embLL (D.what₂.MtLat (tup (S0.μ y)) ((i : ℕ) + 1)) ((D.what₂.jMt (tup (S0.μ y)) ((i : ℕ) + 1)).comp (eMt i (S0.μ y)).toLinearMap) (lNab D A P ψ i (S0.μ y)) ∧ Idx.Z0 D (tup (S0.μ y)) ((i : ℕ) + 1) = Submodule.span ℂ (Set.range fun k => (D.what₂.jMt (tup (S0.μ y)) ((i : ℕ) + 1)) (eMt i (S0.μ y) ((lZ0 D A P ψ Zs i (S0.μ y)).mulVec (Pi.single k 1))))) → HeckeStdTw Tn.B → (∀ j w, 1 ≤ j → j ≤ D.R.m → D.what₂.muAt w ≠ D.what₂.mu0 → LatStable Tn.B j w) → (∀ i, SpecPr D i) → ∀ (i : Fin m) w, D.what₂.etaJ ((i : ℕ) + 1) w = @ite _ (D.plEq w ∈ S0.Tw) (Classical.propDecidable _) (A.fam.etaJ P ψ Zs i (S0.μ (D.plEq w)) (D.plEq w)) 0 := by
  intro D G _ _ Pl0 T m A P ψ Zs tup eMt s hOk hm S0 M Tn hTup hTw hMt hH hLat hSpec i w
  have hj1 : 1 ≤ (i : ℕ) + 1 := Nat.le_add_left _ _
  have hj2 : (i : ℕ) + 1 ≤ D.R.m := Nat.lt_of_lt_of_le i.2 hm
  by_cases h : D.plEq w ∈ S0.Tw
  · rw [if_pos h]
    have hne : D.what₂.muAt w ≠ D.what₂.mu0 := by
      rw [hTup.muAt w, ← hTup.mu0]
      exact fun e => (hTw _).1 h (hTup.inj e)
    have htw : D.what₂.muTw w = tup (S0.μ (D.plEq w)) :=
      ((D.what₂.muAt_or w).resolve_left hne).symm.trans (hTup.muAt w)
    obtain ⟨hM1, hM2, hM3⟩ := hMt i _ h
    obtain ⟨hZ, hE⟩ := GlobalTheory.T.rationalFormLength_eq_definiteFamily D G Pl0 T m A P ψ Zs tup eMt s hOk i (S0.μ (D.plEq w)) hM1 hM2 hM3
    rw [GlobalTheory.T.sum_localCongruenceLength_eq_rationalLength D M Tn ((i : ℕ) + 1) w hj1 hj2 hne hH (hLat _ w hj1 hj2 hne) (htw ▸ hZ)
      (fun i' _ => hSpec i'), htw]
    exact hE w
  · rw [if_neg h]
    refine etaJ_eq_zero_of_untwisted D _ w hj1 hj2 ?_
    rw [hTup.muAt w, ← hTup.mu0]
    congr 1
    by_contra hn
    exact h ((hTw _).2 hn)

end GlobalTheory
end
end
