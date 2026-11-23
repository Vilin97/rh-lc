module

public import Formalism.PeriodIntegrals.UnitaryApproxFin
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryApproximation.Development
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryApproximation.MemIntOEOfIsIntegral
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
import Mathlib.Topology.Sheaves.Init
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryApproximation.Assembly
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryApproximation.WeakApproxF
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryApproximation.EigenvalueAvoidance
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryApproximation.WeakApproximationFiniteUnitary
import Mathlib.Tactic.Linter.HaveILetI
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryApproximation.WeakApproximationFiniteUnitary

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryApproximation.ApproxE

section

@[expose] public section

noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace PI.UnitaryApproxFinWork

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_span_int : ∃ (d : ℕ) (b : Fin d → E), (∀ k, b k ∈ PI.UnitaryApproxDefs.intOE E) ∧
    ∀ e : E, ∃ f : Fin d → F, e = ∑ k, f k • b k := by
  let B := (NumberField.integralBasis E).reindex (Fintype.equivFin _)
  refine ⟨_, fun k => B k, fun k => ?_, fun e => ?_⟩
  · show B k ∈ (algebraMap (𝓞 E) E).range
    refine ⟨RingOfIntegers.basis E ((Fintype.equivFin _).symm k), ?_⟩
    simp only [B, Module.Basis.reindex_apply, NumberField.integralBasis_apply]
  · refine ⟨fun k => ((B.repr e k : ℚ) : F), ?_⟩
    conv_lhs => rw [← B.sum_repr e]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Algebra.smul_def, Algebra.smul_def, map_ratCast, eq_ratCast]

theorem tensor_decomp {d : ℕ} (b : Fin d → E) (hb : ∀ e : E, ∃ f : Fin d → F, e = ∑ k, f k • b k)
    {R : Type} [CommRing R] [Algebra F R] (x : E ⊗[F] R) :
    ∃ c : Fin d → R, x = ∑ k, b k ⊗ₜ[F] c k := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul e r =>
    obtain ⟨f, hf⟩ := hb e
    refine ⟨fun k => f k • r, ?_⟩
    rw [hf, TensorProduct.sum_tmul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [TensorProduct.smul_tmul]
  | add x y hx hy =>
    obtain ⟨c1, h1⟩ := hx
    obtain ⟨c2, h2⟩ := hy
    refine ⟨c1 + c2, ?_⟩
    simp [h1, h2, TensorProduct.tmul_add, Finset.sum_add_distrib]

theorem approxEStep : ApproxEStep := by
  intro hW
  unfold ApproxE
  intro F E _ _ _ _ _ T x D hD
  obtain ⟨d, b, hbint, hb⟩ := exists_span_int (F := F) (E := E)
  have hc : ∀ v : HeightOneSpectrum (𝓞 F), ∃ c : Fin d → v.adicCompletion F,
      x v = ∑ k, b k ⊗ₜ[F] c k := fun v => tensor_decomp b hb (x v)
  choose c hc using hc
  have ha : ∀ k, ∃ a : F, ∀ v ∈ T, ∃ t ∈ v.adicCompletionIntegers F,
      c v k - algebraMap F (v.adicCompletion F) a = algebraMap F (v.adicCompletion F) (D : F) * t :=
    fun k => hW F T (fun v => c v k) D hD
  choose a ht using ha
  refine ⟨∑ k, a k • b k, fun v hv => ?_⟩
  choose t htO hteq using fun k => ht k v hv
  refine ⟨∑ k, (1 : E) ⊗ₜ[F] t k * PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) (b k), ?_, ?_⟩
  · exact Subring.sum_mem _ fun k _ =>
      Subring.mul_mem _ (one_tmul_mem_Sv v (htO k)) (inclE_mem_Sv v (hbint k))

  · rw [hc v, map_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [PI.UnitaryApproxDefs.inclE, dv, Algebra.TensorProduct.includeLeftRingHom_apply,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
    rw [TensorProduct.smul_tmul, ← TensorProduct.tmul_sub, Algebra.smul_def (a k), mul_one, hteq k,
      ← Algebra.smul_def, ← TensorProduct.smul_tmul, Algebra.smul_def]

end PI.UnitaryApproxFinWork

end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryApproximation.BoundedRationalUnitary

section

@[expose] public section

noncomputable section

open TensorProduct NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

namespace PI.UnitaryApproxFinWork

theorem bd_int_mult {K : Type} [Field K] [NumberField K] (e : K) :
    ∃ N : ℤ, N ≠ 0 ∧ IsIntegral ℤ ((N : K) * e) := by
  have halg : IsAlgebraic ℤ e :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ K).2 (Algebra.IsAlgebraic.isAlgebraic e)
  obtain ⟨y, hy0, hyint⟩ := halg.exists_integral_multiple
  exact ⟨y, hy0, by rwa [zsmul_eq_mul] at hyint⟩

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem bd_local (v : HeightOneSpectrum (𝓞 F)) (a : v.adicCompletion F) :
    ∃ N : ℤ, N ≠ 0 ∧ Valued.v ((N : v.adicCompletion F) * a) ≤ 1 := by
  obtain ⟨b, hb, hab⟩ := adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers v a
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {b}))
  refine ⟨(Ideal.absNorm (Ideal.span {b}) : ℤ), ?_, ?_⟩
  · have h0 : Ideal.absNorm (Ideal.span {b}) ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
      exact hb0
    exact_mod_cast h0
  · have hab' : a * algebraMap F (v.adicCompletion F) (b : F) ∈ v.adicCompletionIntegers F := by
      first
      | exact hab
      | (convert hab using 2)
      | simpa using hab
    have hc' : algebraMap F (v.adicCompletion F) (c : F) ∈ v.adicCompletionIntegers F := by
      first
      | exact IsDedekindDomain.HeightOneSpectrum.coe_mem_adicCompletionIntegers v c
      | (convert IsDedekindDomain.HeightOneSpectrum.coe_mem_adicCompletionIntegers (K := F) v c using 1)
      | simpa using IsDedekindDomain.HeightOneSpectrum.coe_mem_adicCompletionIntegers (K := F) v c
    have hcast : algebraMap F (v.adicCompletion F) (c : F) * algebraMap F (v.adicCompletion F) (b : F) =
        ((Ideal.absNorm (Ideal.span {b}) : ℤ) : v.adicCompletion F) := by
      rw [← map_mul, show (c : F) * (b : F) = ((c * b : 𝓞 F) : F) from rfl, hc]
      simp
    rw [← IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, ← hcast]
    have e : algebraMap F (v.adicCompletion F) (c : F) * algebraMap F (v.adicCompletion F) (b : F) * a =
        algebraMap F (v.adicCompletion F) (c : F) * (a * algebraMap F (v.adicCompletion F) (b : F)) := by
      ring
    rw [e]
    exact mul_mem hc' hab'

theorem bd_main (v : HeightOneSpectrum (𝓞 F)) (x : E ⊗[F] v.adicCompletion F) :
    ∃ N : ℤ, N ≠ 0 ∧ (N : E ⊗[F] v.adicCompletion F) * x ∈ Sv E v := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | tmul e t =>
    obtain ⟨N₁, hN₁, h₁⟩ := bd_int_mult e
    obtain ⟨N₂, hN₂, h₂⟩ := bd_local v t
    refine ⟨N₁ * N₂, mul_ne_zero hN₁ hN₂, ?_⟩
    have hL : ((N₁ : ℤ) : E ⊗[F] v.adicCompletion F) = (N₁ : E) ⊗ₜ[F] (1 : v.adicCompletion F) := by
      rw [← Algebra.TensorProduct.includeLeftRingHom_apply, map_intCast]
    have hR : ((N₂ : ℤ) : E ⊗[F] v.adicCompletion F) = (1 : E) ⊗ₜ[F] (N₂ : v.adicCompletion F) := by
      rw [← Algebra.TensorProduct.includeRight_apply, map_intCast]
    have e1 : ((N₁ * N₂ : ℤ) : E ⊗[F] v.adicCompletion F) * (e ⊗ₜ[F] t) =
        ((N₁ : E) * e) ⊗ₜ[F] (1 : v.adicCompletion F) *
          ((1 : E) ⊗ₜ[F] ((N₂ : v.adicCompletion F) * t)) := by
      rw [Int.cast_mul, hL, hR]
      simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [e1]
    refine Subring.mul_mem _ (Subring.subset_closure (Set.mem_union_left _ ⟨⟨(N₁ : E) * e,
      RingHom.mem_range.2 ⟨⟨_, h₁⟩, rfl⟩⟩, rfl⟩))
      (Subring.subset_closure (Set.mem_union_right _ ⟨⟨(N₂ : v.adicCompletion F) * t, ?_⟩, rfl⟩))
    exact (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).2 h₂
  | add x y hx hy =>
    obtain ⟨N₁, hN₁, h₁⟩ := hx
    obtain ⟨N₂, hN₂, h₂⟩ := hy
    refine ⟨N₁ * N₂, mul_ne_zero hN₁ hN₂, ?_⟩
    have e2 : ((N₁ * N₂ : ℤ) : E ⊗[F] v.adicCompletion F) * (x + y) =
        (N₂ : E ⊗[F] v.adicCompletion F) * ((N₁ : E ⊗[F] v.adicCompletion F) * x) +
          (N₁ : E ⊗[F] v.adicCompletion F) * ((N₂ : E ⊗[F] v.adicCompletion F) * y) := by
      push_cast
      ring
    rw [e2]
    exact Subring.add_mem _ (Subring.mul_mem _ (intCast_mem _ N₂) h₁)
      (Subring.mul_mem _ (intCast_mem _ N₁) h₂)

theorem bounded_rational_unitary : BddR := by
  intro F E _ _ _ _ _ v x
  obtain ⟨N, hN, h⟩ := bd_main v x
  refine ⟨(N : 𝓞 F), by exact_mod_cast hN, ?_⟩
  have e : dv E v (N : 𝓞 F) = (N : E ⊗[F] v.adicCompletion F) := by
    unfold dv
    simp [PI.UnitaryApproxDefs.inclE]
  rw [e]
  exact h

end PI.UnitaryApproxFinWork

end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryApproximation.TopStep

section

@[expose] public section

noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace PI.UnitaryApproxFinWork

theorem topStep : TopStep := by
  unfold TopStep CayleyFin EigAvoid PI.UnitaryApproxFin.UnitaryApproxFin
  intro hC hE F E iF iNF iE iNE iA n iFt iDe σ J hσ hθ hJ hdet T g hg D hD
  obtain ⟨μ, hμ, hinv⟩ := hE F E n σ hσ hθ T (fun v => ((g v : GL n _) : Matrix n n _))
  have hμ' : μ * σ μ = 1 := by rw [mul_comm]; exact hμ
  have hab : ∀ v : HeightOneSpectrum (𝓞 F),
      PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) μ *
        PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) (σ μ) = 1 := fun v => by
    rw [← map_mul, hμ', map_one]
  have hρ : ∀ v : HeightOneSpectrum (𝓞 F),
      PI.UnitaryApproxDefs.sigR σ (v.adicCompletion F)
          (PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) μ) *
        PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) μ = 1 := fun v => by
    rw [sigR_inclE, ← map_mul, hμ, map_one]
  obtain ⟨c, hc0, hc⟩ := exists_int_mul (F := F) (σ μ)
  obtain ⟨γ', hγ', hcong⟩ := hC F E n σ J hσ hJ hdet T
    (fun v => scU (n := n) (PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) μ)
      (PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) (σ μ)) (hab v) * g v)
    (fun v hv => Subgroup.mul_mem _
      (scU_mem_UJ (n := n) (PI.UnitaryApproxDefs.sigR σ (v.adicCompletion F))
        (J.map (PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F))) _ _ _ (hρ v)) (hg v hv))
    (fun v hv => by
      simp only [Units.val_mul, scU_val, Matrix.smul_mul, Matrix.one_mul]
      exact hinv v hv)
    (D * c) (mul_ne_zero hD hc0)
  refine ⟨scU (n := n) (σ μ) μ hμ * γ',
    Subgroup.mul_mem _ (scU_mem_UJ (n := n) (σ : E →+* E) J (σ μ) μ hμ ?_) hγ', ?_⟩
  · show σ (σ μ) * σ μ = 1
    rw [hσ, hμ']
  · intro v hv i j
    obtain ⟨s, hs, hseq⟩ := hcong v hv i j
    refine ⟨PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) (algebraMap F E (c : F) * σ μ) * s,
      Subring.mul_mem _ (inclE_mem_Sv v hc) hs, ?_⟩
    have hdv : dv E v (D * c) =
        PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) (algebraMap F E (D : F)) *
          PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) (algebraMap F E (c : F)) :=
      dv_mul v D c
    have hba : PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) (σ μ) *
        PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) μ = 1 := by
      rw [← map_mul, hμ, map_one]
    simp only [Units.val_mul, scU_val, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_apply,
      smul_eq_mul] at hseq ⊢
    rw [hdv] at hseq
    simp only [map_mul]
    linear_combination PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) (σ μ) * hseq -
      ((g v : GL n (E ⊗[F] v.adicCompletion F)) : Matrix n n (E ⊗[F] v.adicCompletion F)) i j * hba

end PI.UnitaryApproxFinWork

end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryApproximation.UnitaryScalars

section

@[expose] public section

noncomputable section

open TensorProduct NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

namespace PI.UnitaryApproxFinWork

theorem unitary_scalars : UnitS := by
  intro F E _ _ _ _ _ v π hπ s hs
  classical
  let O := v.adicCompletionIntegers F
  let S := Sv E v
  have hgen2 : ∀ y : O, ((1 : E) ⊗ₜ[F] (y : v.adicCompletion F)) ∈ S := by
    intro y
    exact Subring.subset_closure (Or.inr ⟨⟨y, y.2⟩, rfl⟩)
  let ψ : O →+* E ⊗[F] v.adicCompletion F :=
    (Algebra.TensorProduct.includeRight :
      v.adicCompletion F →ₐ[F] E ⊗[F] v.adicCompletion F).toRingHom.comp O.subtype
  have hψ : ∀ y : O, ψ y = (1 : E) ⊗ₜ[F] (y : v.adicCompletion F) := fun y => rfl
  let φ : O →+* S := ψ.codRestrict S (fun y => by rw [hψ]; exact hgen2 y)
  letI : Algebra O (E ⊗[F] v.adicCompletion F) := ψ.toAlgebra
  letI : Algebra O S := φ.toAlgebra
  let f : S →ₐ[O] E ⊗[F] v.adicCompletion F := { S.subtype with commutes' := fun r => rfl }
  have hle : S ≤ (integralClosure O (E ⊗[F] v.adicCompletion F)).toSubring := by
    refine Subring.closure_le.2 ?_
    rintro _ (⟨⟨x, hx⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩)
    · obtain ⟨z, rfl⟩ := RingHom.mem_range.1 hx
      obtain ⟨p, hpm, hp⟩ := NumberField.RingOfIntegers.isIntegral_coe z
      refine ⟨p.map (Int.castRingHom O), hpm.map _, ?_⟩
      rw [Polynomial.eval₂_map]
      have hcomp : (algebraMap O (E ⊗[F] v.adicCompletion F)).comp (Int.castRingHom O) =
          (PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) (E := E)).comp (algebraMap ℤ E) :=
        RingHom.ext_int _ _
      rw [hcomp]
      have := Polynomial.hom_eval₂ p (algebraMap ℤ E) (PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) (E := E))
        (algebraMap (𝓞 E) E z)
      rw [hp, map_zero] at this
      exact this.symm
    · exact isIntegral_algebraMap (x := (⟨y, hy⟩ : O))
  have hIntS : Algebra.IsIntegral O S :=
    ⟨fun x => (isIntegral_algHom_iff f Subtype.val_injective).1 (hle x.2)⟩
  have hπv : Valued.v (algebraMap F (v.adicCompletion F) (π : F)) < 1 := by
    rw [wa_valued_algebraMap]
    exact (valuation_lt_one_iff_mem v π).2 hπ
  let πO : O := ⟨algebraMap F (v.adicCompletion F) (π : F), by
    rw [mem_adicCompletionIntegers]; exact hπv.le⟩
  have hπmax : πO ∈ IsLocalRing.maximalIdeal O := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    obtain ⟨w, hw⟩ := isUnit_iff_exists_inv.1 hu
    have h1 : Valued.v (w : v.adicCompletion F) ≤ 1 := by
      have := w.2
      rwa [mem_adicCompletionIntegers] at this
    have h2 : algebraMap F (v.adicCompletion F) (π : F) * (w : v.adicCompletion F) = 1 :=
      congrArg Subtype.val hw
    have h3 : Valued.v (algebraMap F (v.adicCompletion F) (π : F) * (w : v.adicCompletion F)) < 1 :=
      calc _ = Valued.v (algebraMap F (v.adicCompletion F) (π : F)) *
            Valued.v (w : v.adicCompletion F) := map_mul _ _ _
        _ ≤ Valued.v (algebraMap F (v.adicCompletion F) (π : F)) * 1 := mul_le_mul' le_rfl h1
        _ < 1 := by rw [mul_one]; exact hπv
    rw [h2, map_one] at h3
    exact lt_irrefl _ h3
  have hd : dv E v π = (1 : E) ⊗ₜ[F] algebraMap F (v.adicCompletion F) (π : F) := by
    simp only [dv, PI.UnitaryApproxDefs.inclE, Algebra.TensorProduct.includeLeftRingHom_apply,
      Algebra.algebraMap_eq_smul_one]
    exact TensorProduct.smul_tmul _ _ _
  have hxS : 1 + dv E v π * s ∈ S :=
    S.add_mem S.one_mem (S.mul_mem (by rw [hd]; exact hgen2 πO) hs)
  have key : IsUnit (⟨1 + dv E v π * s, hxS⟩ : S) := by
    by_contra h
    obtain ⟨M, hM, hxM⟩ := exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.2 h)
    have hP : (M.comap (algebraMap O S)).IsMaximal := by
      letI := hIntS
      exact Ideal.isMaximal_under_of_isIntegral_of_isMaximal M
    have hπM : algebraMap O S πO ∈ M := by
      have : πO ∈ M.comap (algebraMap O S) := by
        rw [IsLocalRing.eq_maximalIdeal hP]; exact hπmax
      exact this
    have e : (1 : S) = ⟨1 + dv E v π * s, hxS⟩ - algebraMap O S πO * ⟨s, hs⟩ := by
      apply Subtype.ext
      change (1 : E ⊗[F] v.adicCompletion F) = (1 + dv E v π * s) -
        ((1 : E) ⊗ₜ[F] algebraMap F (v.adicCompletion F) (π : F)) * s
      rw [hd]; ring
    have h1 : (1 : S) ∈ M := by
      rw [e]; exact M.sub_mem hxM (M.mul_mem_right _ hπM)
    exact hM.ne_top ((Ideal.eq_top_iff_one M).2 h1)
  obtain ⟨w, hw⟩ := isUnit_iff_exists_inv.1 key
  exact ⟨w, w.2, congrArg Subtype.val hw⟩

end PI.UnitaryApproxFinWork

end
end
end

-- Source module: Formalism.PeriodIntegrals.OrbitalBoundsConclusion.UnitaryApproxFin

section

@[expose] public section

theorem unitary_approximation_finite : PI.UnitaryApproxFin.UnitaryApproxFin :=
  PI.UnitaryApproxFinWork.unitaryApproxFin_of PI.UnitaryApproxFinWork.topStep
    PI.UnitaryApproxFinWork.cayleyStep PI.UnitaryApproxFinWork.approxEStep
    PI.UnitaryApproxFinWork.weak_approximation_finite_unitary PI.UnitaryApproxFinWork.bounded_rational_unitary
    PI.UnitaryApproxFinWork.unitary_scalars PI.UnitaryApproxFinWork.eigenvalue_avoidance
end
end
