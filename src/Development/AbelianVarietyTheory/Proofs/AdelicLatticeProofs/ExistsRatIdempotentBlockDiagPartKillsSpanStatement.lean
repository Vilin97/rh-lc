module

public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Matrix.Mul
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.GaloisStableSubmoduleLeSpanRationalStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar

-- Source module: Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRatIdempotentOfAutStableSubspace

section

@[expose] public section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem exists_rat_idempotent_of_stable (ι : Type) [Fintype ι] [DecidableEq ι]
    (W : Submodule ℂ (ι → ℂ))
    (hW : ∀ σ : ℂ ≃+* ℂ, ∀ v ∈ W, (fun i => σ (v i)) ∈ W) :
    ∃ e : Matrix ι ι ℚ, e * e = e ∧ ∀ v, v ∈ W ↔ e.map (algebraMap ℚ ℂ) *ᵥ v = v := by
  classical

  obtain ⟨Wq, hWq⟩ : ∃ Wq : Submodule ℚ (ι → ℚ),
      ∀ q, q ∈ Wq ↔ (fun i => algebraMap ℚ ℂ (q i)) ∈ W := by
    refine ⟨{ carrier := {q | (fun i => algebraMap ℚ ℂ (q i)) ∈ W}
              add_mem' := ?_, zero_mem' := ?_, smul_mem' := ?_ }, fun q => Iff.rfl⟩
    · intro a b ha hb
      have h : (fun i => algebraMap ℚ ℂ ((a + b) i))
          = (fun i => algebraMap ℚ ℂ (a i)) + (fun i => algebraMap ℚ ℂ (b i)) := by
        ext i; simp
      show (fun i => algebraMap ℚ ℂ ((a + b) i)) ∈ W
      rw [h]; exact W.add_mem ha hb
    · show (fun i => algebraMap ℚ ℂ ((0 : ι → ℚ) i)) ∈ W
      have h : (fun i => algebraMap ℚ ℂ ((0 : ι → ℚ) i)) = 0 := by ext i; simp
      rw [h]; exact W.zero_mem
    · intro c q hq
      have h : (fun i => algebraMap ℚ ℂ ((c • q) i))
          = algebraMap ℚ ℂ c • (fun i => algebraMap ℚ ℂ (q i)) := by
        ext i; simp
      show (fun i => algebraMap ℚ ℂ ((c • q) i)) ∈ W
      rw [h]; exact W.smul_mem _ hq

  obtain ⟨C, hC⟩ := Submodule.exists_isCompl Wq
  obtain ⟨f, hf1, hf2⟩ : ∃ f : (ι → ℚ) →ₗ[ℚ] (ι → ℚ), (∀ q, f q ∈ Wq) ∧ (∀ q ∈ Wq, f q = q) :=
    ⟨Wq.subtype ∘ₗ Wq.projectionOnto C hC, fun q => (Wq.projectionOnto C hC q).2,
      fun q hq => congrArg Subtype.val (Submodule.projectionOnto_apply_left hC ⟨q, hq⟩)⟩
  have hff : f ∘ₗ f = f := LinearMap.ext fun q => hf2 _ (hf1 q)

  have hstable := GlobalTheory.T.galoisStable_submodule_le_span_rational (ι → ℂ) ι (Pi.basisFun ℂ ι) W
    (fun σ w hw => ⟨fun i => σ (w i), hW σ w hw, fun k => by simp⟩)
  refine ⟨LinearMap.toMatrix' f, ?_, ?_⟩
  · rw [← LinearMap.toMatrix'_comp, hff]

  have hA : ∀ q : ι → ℚ, (LinearMap.toMatrix' f).map (algebraMap ℚ ℂ) *ᵥ
      (fun i => algebraMap ℚ ℂ (q i)) = fun i => algebraMap ℚ ℂ (f q i) := by
    intro q
    ext i
    rw [← LinearMap.toMatrix'_mulVec f q]

    simp [Matrix.mulVec, dotProduct, map_sum, map_mul]

  have hB : ∀ v : ι → ℂ, (LinearMap.toMatrix' f).map (algebraMap ℚ ℂ) *ᵥ v ∈ W := by
    intro v
    have hcol : ∀ j, (fun i => algebraMap ℚ ℂ (LinearMap.toMatrix' f i j)) ∈ W := by
      intro j
      simp only [LinearMap.toMatrix'_apply]
      exact (hWq _).1 (hf1 _)
    have h : (LinearMap.toMatrix' f).map (algebraMap ℚ ℂ) *ᵥ v
        = ∑ j, v j • (fun i => algebraMap ℚ ℂ (LinearMap.toMatrix' f i j)) := by
      ext i
      simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
    rw [h]
    exact W.sum_mem fun j _ => W.smul_mem _ (hcol j)
  intro v
  constructor
  · intro hv
    have hspan := hstable hv
    clear hv
    induction hspan using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨hwW, hq⟩ := hw
      choose q hq using hq
      have hw : w = fun i => algebraMap ℚ ℂ (q i) := by
        ext k
        rw [← Pi.basisFun_repr ℂ ι w k, hq k]
        exact (eq_ratCast (algebraMap ℚ ℂ) (q k)).symm
      have hqW : q ∈ Wq := (hWq q).2 (by rw [← hw]; exact hwW)
      rw [hw, hA, hf2 q hqW]
    | zero => simp
    | add x y _ _ hx hy => rw [Matrix.mulVec_add, hx, hy]
    | smul c x _ hx => rw [Matrix.mulVec_smul, hx]
  · intro hv
    rw [← hv]
    exact hB v

end GlobalTheory.ClassFin
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRatIdempotentOfAutStableSubspaceStatement

section

@[expose] public section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

theorem _root_.GlobalTheory.T.exists_rat_idempotent_of_autStable_subspace : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (W : Submodule ℂ (ι → ℂ)), (∀ σ : ℂ ≃+* ℂ, ∀ v ∈ W, (fun i => σ (v i)) ∈ W) → ∃ e : Matrix ι ι ℚ, e * e = e ∧ ∀ v, v ∈ W ↔ e.map (algebraMap ℚ ℂ) *ᵥ v = v := by
  first | exact @GlobalTheory.ClassFin.exists_rat_idempotent_of_stable | exact GlobalTheory.ClassFin.exists_rat_idempotent_of_stable | (intros; apply GlobalTheory.ClassFin.exists_rat_idempotent_of_stable <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.InvariantSubspaceNotSemisimple

section

@[expose] public section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem exists_mem_mul_eq_zero_of_isNilpotent {R : Type*} [Ring R] (J : Ideal R) [J.IsTwoSided]
    (hJ : IsNilpotent J) (h0 : J ≠ ⊥) : ∃ a ∈ J, a ≠ 0 ∧ ∀ b ∈ J, b * a = 0 := by
  obtain ⟨n, hn⟩ := hJ
  by_contra hcon
  push Not at hcon
  have key : ∀ k : ℕ, J ^ (k + 1) ≠ ⊥ := by
    intro k
    induction k with
    | zero => simpa [Submodule.pow_one] using h0
    | succ k ih =>
      obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot ih
      obtain ⟨b, hb, hba⟩ := hcon a (Ideal.pow_le_self (Nat.succ_ne_zero k) ha) ha0
      intro h
      apply hba
      have : b * a ∈ J ^ (k + 1 + 1) := by
        rw [Ideal.IsTwoSided.pow_succ]
        exact Ideal.mul_mem_mul hb ha
      rw [h] at this
      simpa using this
  apply key n
  rw [Submodule.pow_succ, hn]
  simp

theorem map_mem_jacobson_of_surjective {R S : Type*} [Ring R] [Ring S] (f : R →+* S)
    (hf : Function.Surjective f) {b : R} (hb : b ∈ Ring.jacobson R) : f b ∈ Ring.jacobson S := by
  have : RingHomSurjective f := ⟨hf⟩
  exact Ring.le_comap_jacobson (f := f) hb

noncomputable def spanAlg {ι : Type} [Fintype ι] [DecidableEq ι] {Γ : Set (Matrix ι ι ℂ)} (h : IsPre Γ) :
    Subalgebra ℂ (Matrix ι ι ℂ) :=
  (Submodule.span ℂ Γ).toSubalgebra (Submodule.subset_span h.one_mem) (by
    intro x y hx hy
    have h1 := Submodule.mul_mem_mul hx hy
    rw [Submodule.span_mul_span] at h1
    refine Submodule.span_mono ?_ h1
    rintro _ ⟨a, ha, b, hb, rfl⟩
    exact h.mul_mem a ha b hb)

theorem map_mem_spanAlg {ι : Type} [Fintype ι] [DecidableEq ι] {Γ : Set (Matrix ι ι ℂ)} (h : IsPre Γ)
    (σ : ℂ ≃+* ℂ) {x : Matrix ι ι ℂ} (hx : x ∈ spanAlg h) : x.map σ ∈ spanAlg h := by
  change x ∈ Submodule.span ℂ Γ at hx
  change Matrix.map x (⇑σ : ℂ → ℂ) ∈ Submodule.span ℂ Γ
  induction hx using Submodule.span_induction with
  | mem g hg => exact Submodule.subset_span (h.aut_mem σ g hg)
  | zero =>
    have e : Matrix.map (0 : Matrix ι ι ℂ) (⇑σ : ℂ → ℂ) = 0 := by
      ext i j; simp
    rw [e]; exact Submodule.zero_mem _
  | add a b _ _ ha hb =>
    have e : Matrix.map (a + b) (⇑σ : ℂ → ℂ) = Matrix.map a (⇑σ : ℂ → ℂ) + Matrix.map b (⇑σ : ℂ → ℂ) := by
      ext i j; simp
    rw [e]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha =>
    have e : Matrix.map (c • a) (⇑σ : ℂ → ℂ) = σ c • Matrix.map a (⇑σ : ℂ → ℂ) := by
      ext i j; simp
    rw [e]; exact Submodule.smul_mem _ _ ha

noncomputable def spanAlgMap {ι : Type} [Fintype ι] [DecidableEq ι] {Γ : Set (Matrix ι ι ℂ)} (h : IsPre Γ)
    (σ : ℂ ≃+* ℂ) : spanAlg h →+* spanAlg h :=
  RingHom.codRestrict ((σ : ℂ →+* ℂ).mapMatrix.comp (spanAlg h).val.toRingHom) (spanAlg h)
    (fun x => map_mem_spanAlg h σ x.2)

theorem spanAlgMap_surjective {ι : Type} [Fintype ι] [DecidableEq ι] {Γ : Set (Matrix ι ι ℂ)} (h : IsPre Γ)
    (σ : ℂ ≃+* ℂ) : Function.Surjective (spanAlgMap h σ) := by
  intro y
  refine ⟨⟨y.1.map σ.symm, map_mem_spanAlg h σ.symm y.2⟩, ?_⟩
  apply Subtype.ext
  ext i j
  simp [spanAlgMap]

theorem ss_of_isSemisimpleRing {ι : Type} [Fintype ι] [DecidableEq ι] {Γ : Set (Matrix ι ι ℂ)} (h : IsPre Γ)
    [IsSemisimpleRing (spanAlg h)] : SS Γ := by
  intro W hW
  have hW' : ∀ x ∈ Submodule.span ℂ Γ, ∀ v ∈ W, x *ᵥ v ∈ W := by
    intro x hx v hv
    induction hx using Submodule.span_induction with
    | mem x hx => exact hW x hx v hv
    | zero => simp
    | add x y _ _ hx hy => rw [add_mulVec]; exact W.add_mem hx hy
    | smul c x _ hx => rw [smul_mulVec]; exact W.smul_mem _ hx
  let U : Submodule (spanAlg h) (ι → ℂ) :=
    { W.toAddSubmonoid with smul_mem' := fun c v hv => hW' c.1 c.2 v hv }
  obtain ⟨U', hU⟩ := exists_isCompl U
  have hsm : ∀ (x : Matrix ι ι ℂ), x ∈ spanAlg h → ∀ v ∈ U', x *ᵥ v ∈ U' :=
    fun x hx v hv => U'.smul_mem ⟨x, hx⟩ hv
  let W' : Submodule ℂ (ι → ℂ) :=
    { U'.toAddSubmonoid with
      smul_mem' := fun c v hv => by
        have := hsm (c • 1) ((spanAlg h).smul_mem (spanAlg h).one_mem c) v hv
        rwa [smul_mulVec, one_mulVec] at this }
  refine ⟨W', fun g hg v hv => hsm g (Submodule.subset_span hg) v hv, ?_, ?_⟩
  · rw [Submodule.disjoint_def]
    intro x hx hx'
    exact Submodule.disjoint_def.1 hU.disjoint x hx hx'
  · rw [codisjoint_iff, Submodule.eq_top_iff']
    intro x
    have : x ∈ U ⊔ U' := by rw [hU.sup_eq_top]; trivial
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 this
    exact Submodule.add_mem_sup hy hz

theorem exists_socle_radical_of_not_ss :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), IsPre Γ → ¬ SS Γ → ∃ W : Submodule ℂ (ι → ℂ), (∀ g ∈ Γ, ∀ v ∈ W, g *ᵥ v ∈ W) ∧ (∀ σ : ℂ ≃+* ℂ, ∀ v ∈ W, (fun i => σ (v i)) ∈ W) ∧ ∃ a ∈ Submodule.span ℂ Γ, a ≠ 0 ∧ (∀ v, a *ᵥ v ∈ W) ∧ ∀ v ∈ W, a *ᵥ v = 0 := by
  intro ι _ _ Γ h hss
  have : IsArtinianRing (spanAlg h) := IsArtinianRing.of_finite ℂ _
  have h0 : Ring.jacobson (spanAlg h) ≠ ⊥ := by
    intro h0
    have := IsArtinianRing.isSemisimpleRing_iff_jacobson.2 h0
    exact hss (ss_of_isSemisimpleRing h)
  obtain ⟨a, ha, ha0, hba⟩ := exists_mem_mul_eq_zero_of_isNilpotent (Ring.jacobson (spanAlg h))
    IsSemiprimaryRing.isNilpotent h0
  let W : Submodule ℂ (ι → ℂ) :=
    { carrier := {v | ∀ b ∈ Ring.jacobson (spanAlg h), b.1 *ᵥ v = 0}
      add_mem' := fun {x y} hx hy b hb => by rw [mulVec_add, hx b hb, hy b hb, add_zero]
      zero_mem' := fun b _ => mulVec_zero _
      smul_mem' := fun c v hv b hb => by rw [mulVec_smul, hv b hb, smul_zero] }
  refine ⟨W, ?_, ?_, a.1, a.2, fun h1 => ha0 (Subtype.ext h1), ?_, fun v hv => hv a ha⟩
  · intro g hg v hv b hb
    have hg' : g ∈ spanAlg h := Submodule.subset_span hg
    have h1 : b * (⟨g, hg'⟩ : spanAlg h) ∈ Ring.jacobson (spanAlg h) := Ideal.mul_mem_right _ _ hb
    have h2 := hv _ h1
    rw [MulMemClass.coe_mul, ← mulVec_mulVec] at h2
    exact h2
  · intro σ v hv b hb
    have h1 : spanAlgMap h σ.symm b ∈ Ring.jacobson (spanAlg h) :=
      map_mem_jacobson_of_surjective _ (spanAlgMap_surjective h σ.symm) hb
    have h2 := hv _ h1
    funext i
    have h3 := congrArg σ (congrFun h2 i)

    simpa [spanAlgMap, mulVec, dotProduct, map_sum] using h3
  · intro v b hb
    rw [mulVec_mulVec]
    have := congrArg Subtype.val (hba b hb)
    change b.1 * a.1 = 0 at this
    rw [this, zero_mulVec]

end GlobalTheory.ClassFin
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.InvariantSubspaceNotSemisimpleStatement

section

@[expose] public section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

theorem _root_.GlobalTheory.T.invariant_subspace_not_semisimple : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), IsPre Γ → ¬ SS Γ → ∃ W : Submodule ℂ (ι → ℂ), (∀ g ∈ Γ, ∀ v ∈ W, g *ᵥ v ∈ W) ∧ (∀ σ : ℂ ≃+* ℂ, ∀ v ∈ W, (fun i => σ (v i)) ∈ W) ∧ ∃ a ∈ Submodule.span ℂ Γ, a ≠ 0 ∧ (∀ v, a *ᵥ v ∈ W) ∧ ∀ v ∈ W, a *ᵥ v = 0 := by
  first | exact @GlobalTheory.ClassFin.exists_socle_radical_of_not_ss | exact GlobalTheory.ClassFin.exists_socle_radical_of_not_ss | (intros; apply GlobalTheory.ClassFin.exists_socle_radical_of_not_ss <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRatIdempotentBlockDiagPartKillsSpan

section

@[expose] public section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem exists_rat_idempotent_blk_eq_zero : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), IsPre Γ → ¬ SS Γ → ∃ e : Matrix ι ι ℚ, e * e = e ∧ (∀ g ∈ Γ, (1 - e.map (algebraMap ℚ ℂ)) * g * e.map (algebraMap ℚ ℂ) = 0) ∧ ∃ a ∈ Submodule.span ℂ Γ, a ≠ 0 ∧ blk e a = 0 := by
  intro ι _ _ Γ hΓ hss
  obtain ⟨W, hWinv, hWσ, a, ha_span, ha0, ha_into, ha_kill⟩ := GlobalTheory.T.invariant_subspace_not_semisimple ι Γ hΓ hss
  obtain ⟨e, hee, hW⟩ := GlobalTheory.T.exists_rat_idempotent_of_autStable_subspace ι W hWσ

  have hEE : e.map (algebraMap ℚ ℂ) * e.map (algebraMap ℚ ℂ) = e.map (algebraMap ℚ ℂ) := by
    rw [← Matrix.map_mul, hee]
  have hEmem : ∀ v, e.map (algebraMap ℚ ℂ) *ᵥ v ∈ W := fun v => by
    rw [hW, Matrix.mulVec_mulVec, hEE]
  have hfix : ∀ w ∈ W, e.map (algebraMap ℚ ℂ) *ᵥ w = w := fun w hw => (hW w).1 hw
  refine ⟨e, hee, ?_, a, ha_span, ha0, ?_⟩
  ·
    intro g hg
    rw [Matrix.ext_iff_mulVec]
    intro v
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec,
      hfix _ (hWinv g hg _ (hEmem v)), sub_self, Matrix.zero_mulVec]
  ·
    rw [Matrix.ext_iff_mulVec]
    intro v
    unfold blk
    rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ha_kill _ (hEmem v),
      Matrix.mulVec_zero, zero_add, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      Matrix.sub_mulVec, Matrix.one_mulVec, hfix _ (ha_into _), sub_self, Matrix.zero_mulVec]

end GlobalTheory.ClassFin
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRatIdempotentBlockDiagPartKillsSpanStatement

section

@[expose] public section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

theorem _root_.GlobalTheory.T.exists_rat_idempotent_blockDiagPart_kills_span : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), IsPre Γ → ¬ SS Γ → ∃ e : Matrix ι ι ℚ, e * e = e ∧ (∀ g ∈ Γ, (1 - e.map (algebraMap ℚ ℂ)) * g * e.map (algebraMap ℚ ℂ) = 0) ∧ ∃ a ∈ Submodule.span ℂ Γ, a ≠ 0 ∧ blk e a = 0 := by
  first | exact @GlobalTheory.ClassFin.exists_rat_idempotent_blk_eq_zero | exact GlobalTheory.ClassFin.exists_rat_idempotent_blk_eq_zero | (intros; apply GlobalTheory.ClassFin.exists_rat_idempotent_blk_eq_zero <;> assumption)
end
end
