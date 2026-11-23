module

public import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
public import Formalism.LocalToGlobal.KernelLattices.ThDistC
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmulLatMatOf
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MulVSubRight
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
public import Mathlib.LinearAlgebra.PiTensorProduct.Generators
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Formalism.LocalToGlobal.KernelLattices.LateralTheory

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntegralDetOfStable

section

@[expose] public section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Ker GlobalTheory.RatEqui

namespace GlobalTheory.DetStab

theorem isIntegral_det_of_stable {R E : Type} [CommRing R] [IsNoetherianRing R] [Field E] [Algebra R E] {n : ℕ}
    (L : Submodule R (Fin n → E)) (hfg : L.FG) (hsp : Submodule.span E (L : Set (Fin n → E)) = ⊤)
    (γ : Matrix (Fin n) (Fin n) E) (hγ : ∀ v ∈ L, γ.mulVec v ∈ L) : IsIntegral R γ.det := by
  classical
  let N : Submodule R E := Submodule.span R {x | ∃ w : Fin n → L, x = (Matrix.of fun i => (w i : Fin n → E)).det}
  let M : Submodule R E := ⨆ j : Fin n, L.map (LinearMap.proj j : (Fin n → E) →ₗ[R] E)
  have hM : M.FG := Submodule.fg_iSup _ fun j => hfg.map (LinearMap.proj j : (Fin n → E) →ₗ[R] E)
  have hprod : ∀ (s : Finset (Fin n)) (f : Fin n → E), (∀ i, f i ∈ M) → ∏ i ∈ s, f i ∈ M ^ s.card := by
    intro s f hf
    induction s using Finset.induction_on with
    | empty =>
      rw [Finset.prod_empty, Finset.card_empty, pow_zero]
      exact Submodule.one_le.1 le_rfl
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, pow_succ']
      exact Submodule.mul_mem_mul (hf a) ih
  have hle : N ≤ M ^ (Finset.univ : Finset (Fin n)).card := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨w, rfl⟩
    rw [SetLike.mem_coe, Matrix.det_apply]
    refine Submodule.sum_mem _ fun σ _ => ?_
    rw [Units.smul_def]
    refine Submodule.smul_of_tower_mem _ _ (hprod _ _ fun i => ?_)
    exact Submodule.mem_iSup_of_mem i ⟨_, (w (σ i)).2, rfl⟩
  have hN : N.FG := (hM.pow _).of_le hle
  have hne : N ≠ ⊥ := by
    intro h
    have h0 : (Matrix.detRowAlternating (n := Fin n) (R := E)).toMultilinearMap = 0 := by
      refine MultilinearMap.ext_of_span_eq_top (g := fun _ (x : L) => (x : Fin n → E)) (fun _ => ?_) fun w => ?_
      · rw [← hsp]; congr 1; exact Subtype.range_coe
      · have : (Matrix.of fun i => (w i : Fin n → E)).det ∈ N := Submodule.subset_span ⟨w, rfl⟩
        rw [h] at this
        exact this
    have h1 := congrArg (fun f => f (1 : Matrix (Fin n) (Fin n) E)) h0
    have h2 : (1 : Matrix (Fin n) (Fin n) E).det = 0 := h1
    simp at h2
  refine isIntegral_of_smul_mem_submodule N hne hN _ fun x hx => ?_
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, rfl⟩ := hx
    refine Submodule.subset_span ⟨fun i => ⟨γ.mulVec (w i), hγ _ (w i).2⟩, ?_⟩
    rw [smul_eq_mul, mul_comm, ← Matrix.det_transpose γ, ← Matrix.det_mul]
    congr 1
    ext i j
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm]
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact N.add_mem hx hy
  | smul r x _ hx => rw [smul_comm]; exact N.smul_mem r hx

theorem prod_emb_det_eq_one (D : D7) (χ : IdE D → ℂ) (hχ : IsChi D χ) (n : ℕ)
    (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (hL : SD D L) (γ : Matrix (Fin n) (Fin n) D.host.E)
    (hu : γ * adj D γ = 1) (hs : ∀ v, v ∈ L ↔ γ.mulVec v ∈ L) : ∏ τ, embT D τ γ.det = 1 := by
  letI := D.host.cmStar
  obtain ⟨hfg, hsp, -⟩ := hL
  have hstar : ∀ x : D.host.E, star x = D.host.conj x := by
    intro x
    haveI := D.host.isCMField_hostE
    apply D.host.φ₀.injective
    rw [Formalism.HC.HostAx.conjE_apply]
    exact IsCMField.complexEmbedding_complexConj D.host.E D.host.φ₀ x
  have hd : γ.det * (adj D γ).det = 1 := by rw [← Matrix.det_mul, hu, Matrix.det_one]
  have hadj : (adj D γ).det = D.host.conj γ.det := by
    unfold adj
    rw [Matrix.det_transpose]
    exact (RingHom.map_det (D.host.conj : D.host.E →+* D.host.E) γ).symm
  have hz : γ.det ∈ unitary D.host.E := by
    rw [Unitary.mem_iff, hstar, ← hadj]
    exact ⟨by rw [mul_comm, hd], hd⟩
  have i1 := isIntegral_det_of_stable L hfg hsp γ fun v hv => (hs v).1 hv
  have i2 := isIntegral_det_of_stable L hfg hsp (adj D γ) fun v hv => (hs _).2 (by
    rw [Matrix.mulVec_mulVec, hu, Matrix.one_mulVec]; exact hv)
  obtain ⟨a, ha⟩ := (IsIntegrallyClosed.isIntegral_iff (R := 𝓞 D.host.E)).1 i1
  obtain ⟨b, hb⟩ := (IsIntegrallyClosed.isIntegral_iff (R := 𝓞 D.host.E)).1 i2
  have hspan : Submodule.span (𝓞 D.host.E) {γ.det} = Submodule.span (𝓞 D.host.E) {(1 : D.host.E)} := by
    apply le_antisymm
    · rw [Submodule.span_singleton_le_iff_mem, Submodule.mem_span_singleton]
      exact ⟨a, by rw [Algebra.smul_def, ha, mul_one]⟩
    · rw [Submodule.span_singleton_le_iff_mem, Submodule.mem_span_singleton]
      exact ⟨b, by rw [Algebra.smul_def, hb, mul_comm, hd]⟩
  have e1 := hχ.2 ⟨γ.det, hz⟩
  have e2 := hχ.2 1
  have e3 : ∏ τ, (embT D τ γ.det)⁻¹ = 1 := by
    have e1' : χ (Submodule.span (𝓞 D.host.E) {γ.det}) = ∏ τ, (embT D τ γ.det)⁻¹ := e1
    have e2' : χ (Submodule.span (𝓞 D.host.E) {(1 : D.host.E)}) = ∏ τ, (embT D τ 1)⁻¹ := e2
    rw [← e1', hspan, e2']
    simp
  rwa [Finset.prod_inv_distrib, inv_eq_one] at e3

end GlobalTheory.DetStab
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.DetUnitaryStabiliserSelfDualLatticeNormOne

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Formalism.HermitianLatticesTheory NumberField IsDedekindDomain

namespace GlobalTheory.DetFields

open GlobalTheory.Mem.Col2.JetEx.VacEqPf

theorem iE_det {D : D7} {X : Fields} (s : Seam D X) {n : ℕ} (γ : Sp X.E n ≃ₗ[X.E] Sp X.E n) :
    s.iE ((LinearEquiv.det γ : X.Eˣ) : X.E) = (matOf s γ).det := by
  rw [LinearEquiv.coe_det, ← LinearMap.det_toMatrix']
  rw [show s.iE (LinearMap.toMatrix' (γ : Sp X.E n →ₗ[X.E] Sp X.E n)).det = _ from
    RingHom.map_det (s.iE : X.E →+* D.host.E) _]
  congr 1

theorem det_of_stab : ∀ (D : D7) (X : Fields) (s : Seam D X) (χ : TaylorLogMetric.IdE D → ℂ), s.Ok → TaylorLogMetric.IsChi D χ → ∀ (n : ℕ) (N' : Submodule (𝓞 X.E) (Sp X.E n)), IsSDLat D.host.E n (s.lat N') → ∀ γ : UF X.E n, gmap γ.1 N' = N' → ((LinearEquiv.det γ.1 : X.Eˣ) : X.E) * star ((LinearEquiv.det γ.1 : X.Eˣ) : X.E) = 1 ∧ IsIntegral ℤ ((LinearEquiv.det γ.1 : X.Eˣ) : X.E) ∧ ∏ τ, TaylorLogMetric.embT D τ (s.iE ((LinearEquiv.det γ.1 : X.Eˣ) : X.E)) = 1 := by
  intro D X s χ hok hχ n N' hL γ hγ
  have hd := iE_det s γ.1
  have hSD : Formalism.MainNotions.StandardLatticesGL3.SD D (s.lat N') := hL
  have hfg : (s.lat N').FG := hL.1
  have hsp : Submodule.span D.host.E ((s.lat N' : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) : Set (Fin n → D.host.E)) = ⊤ := hL.2.1
  have hU := matOf_unitary s hok γ
  set M := matOf s γ.1 with hM

  have hMM : GlobalTheory.RatEqui.adj D M * M = 1 ∧ M * GlobalTheory.RatEqui.adj D M = 1 := by
    letI := D.host.cmStar
    have e : star M = GlobalTheory.RatEqui.adj D M := by
      ext i j
      simp [GlobalTheory.RatEqui.adj, Matrix.star_apply, star_conj]
    rw [← e]
    exact ⟨Unitary.star_mul_self_of_mem hU, Unitary.mul_star_self_of_mem hU⟩
  have hadj : M * GlobalTheory.RatEqui.adj D M = 1 := hMM.2

  have hs : ∀ v, v ∈ s.lat N' ↔ M.mulVec v ∈ s.lat N' := by
    intro v
    constructor
    · intro hv
      obtain ⟨x, hx, rfl⟩ := (mem_lat s N' v).1 hv
      refine (mem_lat s N' _).2 ⟨γ.1 x, ?_, (matOf_mulVec s γ.1 x).symm⟩
      rw [← hγ]
      exact ⟨x, hx, rfl⟩
    · intro hv
      obtain ⟨y, hy, hyv⟩ := (mem_lat s N' _).1 hv
      rw [← hγ] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      have hx' : M.mulVec (vec s x) = M.mulVec v := by
        rw [← hyv]
        exact matOf_mulVec s γ.1 x
      have hinj : vec s x = v := by
        have := congrArg (fun w => (GlobalTheory.RatEqui.adj D M).mulVec w) hx'
        simpa only [Matrix.mulVec_mulVec, hMM.1, Matrix.one_mulVec] using this
      rw [← hinj]
      exact (mem_lat s N' _).2 ⟨x, hx, rfl⟩

  have hdet : M.det * D.host.conj M.det = 1 := by
    have h1 : (GlobalTheory.RatEqui.adj D M).det = D.host.conj M.det := by
      unfold GlobalTheory.RatEqui.adj
      rw [Matrix.det_transpose]
      exact (RingHom.map_det (D.host.conj : D.host.E →+* D.host.E) M).symm
    rw [← h1, ← Matrix.det_mul, hMM.2, Matrix.det_one]
  refine ⟨?_, ?_, ?_⟩
  · apply s.iE.injective
    rw [map_mul, hok.2, hd, map_one]
    exact hdet
  · have i1 := GlobalTheory.DetStab.isIntegral_det_of_stable (s.lat N') hfg hsp M fun v hv => (hs v).1 hv
    have i2 : IsIntegral ℤ M.det := isIntegral_trans (R := ℤ) _ i1
    have i3 := map_isIntegral_int s.iE.symm.toRingHom i2
    rw [← hd] at i3
    simpa using i3
  · rw [hd]
    exact GlobalTheory.DetStab.prod_emb_det_eq_one D χ hχ n (s.lat N') hSD M hadj hs

end GlobalTheory.DetFields
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.DetUnitaryStabiliserSelfDualLatticeNormOneStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Formalism.HermitianLatticesTheory NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.det_unitaryStabiliser_selfDualLattice_normOne : ∀ (D : D7) (X : Fields) (s : Seam D X) (χ : TaylorLogMetric.IdE D → ℂ), s.Ok → TaylorLogMetric.IsChi D χ → ∀ (n : ℕ) (N' : Submodule (𝓞 X.E) (Sp X.E n)), IsSDLat D.host.E n (s.lat N') → ∀ γ : UF X.E n, gmap γ.1 N' = N' → ((LinearEquiv.det γ.1 : X.Eˣ) : X.E) * star ((LinearEquiv.det γ.1 : X.Eˣ) : X.E) = 1 ∧ IsIntegral ℤ ((LinearEquiv.det γ.1 : X.Eˣ) : X.E) ∧ ∏ τ, TaylorLogMetric.embT D τ (s.iE ((LinearEquiv.det γ.1 : X.Eˣ) : X.E)) = 1 := by
  first | exact @GlobalTheory.DetFields.det_of_stab | exact GlobalTheory.DetFields.det_of_stab | (intros; apply GlobalTheory.DetFields.det_of_stab <;> assumption)
end
end
