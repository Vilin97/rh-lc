module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRealCoord
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CuspIntegralBasisCovolumeConstant
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.FundamentalDomainCusps.LocalPointData
import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirVolumeRatios.VolumeClassRepresentatives.DensRat
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRealCoord
import Mathlib.Data.Nat.Choose.Multinomial
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsReducedBasisBoundedTypeOfInstanceStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralVectorBasesBoundedFiniteUnitaryClasses
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CuspIntegralBasisCovolumeConstantStatement

section

@[expose] public section

open NumberField Matrix Formalism.MainNotions.S GlobalTheory.CuspGeo GlobalTheory.ClassFin
open scoped Topology

theorem _root_.GlobalTheory.T.cusp_integralBasis_covolume_constant : ∀ I : AutInst, ∃ (N : ℕ) (e : Fin N → Fin I.n → I.E) (ρ : (InfinitePlace I.F → Fin I.n → ℂ) ≃ₗ[ℝ] (Fin N → ℝ)) (d : ℝ), 0 < d ∧ IsZBasis I e ∧ IsRealCoord I ρ ∧ ∀ y : I.Ginf, |(gm I ρ y e).det| = d := by
  first | exact @GlobalTheory.CuspGeo.covolume_const | exact GlobalTheory.CuspGeo.covolume_const | (intros; apply GlobalTheory.CuspGeo.covolume_const <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCompactIntegralUnitaryFinitePart

section

@[expose] public section

open NumberField Matrix Formalism.MainNotions.S GlobalTheory.CuspGeo GlobalTheory.ClassFin
open scoped Topology

noncomputable section

namespace GlobalTheory.IntUnitCpt

open Formalism.MainNotions.LeviCoordinates


open Classical in
def red {E : Type} [Field E] [NumberField E] {n : ℕ} (M : ℕ) (A : Matrix (Fin n) (Fin n) E) :
    Fin n → Fin n → (𝓞 E ⧸ Ideal.span {(M : 𝓞 E)}) := fun i j =>
  if h : IsIntegral ℤ (A i j) then Ideal.Quotient.mk _ ⟨A i j, h⟩ else 0

theorem sub_of_red {E : Type} [Field E] [NumberField E] {n : ℕ} (M : ℕ) {A B : Matrix (Fin n) (Fin n) E}
    (hA : ∀ i j, IsIntegral ℤ (A i j)) (hB : ∀ i j, IsIntegral ℤ (B i j)) (h : red M A = red M B) :
    ∀ i j, ∃ b : E, IsIntegral ℤ b ∧ (A - B) i j = (M : E) * b := by
  intro i j
  have e := congrFun (congrFun h i) j
  simp only [red, dif_pos (hA i j), dif_pos (hB i j)] at e
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1 e)
  clear e
  refine ⟨b, RingOfIntegers.isIntegral_coe b, ?_⟩
  have := congrArg (fun z : 𝓞 E => (z : E)) hb
  simp only [map_mul, map_natCast, map_sub] at this
  rw [Matrix.sub_apply, mul_comm]
  exact this.symm

theorem mul_cong {E : Type} [Field E] [NumberField E] {n : ℕ} (M : ℕ) {C D : Matrix (Fin n) (Fin n) E}
    (hC : ∀ i j, IsIntegral ℤ (C i j)) (hD : ∀ i j, ∃ b : E, IsIntegral ℤ b ∧ D i j = (M : E) * b) :
    ∀ i j, ∃ a : E, IsIntegral ℤ a ∧ (C * D) i j = (M : E) * a := by
  intro i j
  choose b hb hb' using hD
  refine ⟨∑ k, C i k * b k j, IsIntegral.sum _ fun k _ => (hC i k).mul (hb k j), ?_⟩
  rw [Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hb' k j]; ring

theorem kset_nhds (I : AutInst) : I.Kset ∈ 𝓝 (1 : I.Gf) := by
  have ho := I.topf_open 1 le_rfl
  refine Filter.mem_of_superset (ho.mem_nhds ?_) fun x hx => hx.1
  refine ⟨(Formalism.UG.stabGL _).one_mem, fun y hy => ⟨0, Submodule.zero_mem _, by simp⟩⟩

end GlobalTheory.IntUnitCpt

namespace GlobalTheory.IntUnitCpt

def fp (I : AutInst) (γ : GL (Fin I.n) I.E) (hγ : γ ∈ Formalism.UG.UJ (starRingEnd I.E) I.J) : I.Gf :=
  ⟨Formalism.UG.bc (Formalism.UG.inclE (F := I.F) (Af I.F)) γ,
    Formalism.UG.Final.RatPtsLe I.F I.E (Fin I.n) I.cm.sig I.J (Af I.F) (Subgroup.mem_map_of_mem _ hγ)⟩

theorem fp_mul (I : AutInst) {γ δ : GL (Fin I.n) I.E} (hγ : γ ∈ Formalism.UG.UJ (starRingEnd I.E) I.J)
    (hδ : δ ∈ Formalism.UG.UJ (starRingEnd I.E) I.J) :
    fp I (γ⁻¹ * δ) (mul_mem (inv_mem hγ) hδ) = (fp I γ hγ)⁻¹ * fp I δ hδ := by
  apply Subtype.ext
  simp [fp, map_mul, map_inv]

theorem eq_of_real (I : AutInst) (v : InfinitePlace I.F) {A B : Matrix (Fin I.n) (Fin I.n) I.E}
    (h : (I.P v)⁻¹ * A.map (I.φ v) * I.P v = (I.P v)⁻¹ * B.map (I.φ v) * I.P v) : A = B := by
  have h2 : A.map (I.φ v) = B.map (I.φ v) := by
    have := congrArg (fun X => I.P v * X * (I.P v)⁻¹) h
    have hp := Formalism.MainNotions.LeviCoordinates.rrg_P_mul_inv I v
    simp only [← Matrix.mul_assoc, hp, Matrix.one_mul] at this
    simpa only [Matrix.mul_assoc, hp, Matrix.mul_one] using this
  ext i j
  exact (I.φ v).injective (congrFun (congrFun h2 i) j)

end GlobalTheory.IntUnitCpt

namespace GlobalTheory.IntUnitCpt

theorem intUnit_compact : ∀ I : AutInst, ∃ K : Set I.Gf, IsCompact K ∧ ∀ γ : GL (Fin I.n) I.E,
    γ ∈ Formalism.UG.UJ (starRingEnd I.E) I.J → (∀ i j, IsIntegral ℤ ((γ : Matrix (Fin I.n) (Fin I.n) I.E) i j)) →
    (∀ i j, IsIntegral ℤ (((γ⁻¹ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E) i j)) →
    ∃ x ∈ I.GFset, x.2 ∈ K ∧ ∀ v, uMat (x.1 v) = (I.P v)⁻¹ * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v := by
  intro I
  classical
  obtain ⟨M, hM, hcong⟩ := CompanionTheory.D.gk.RF.congruence_subgroup_compact_open I I.Kset (kset_nhds I)
  let T : Set (GL (Fin I.n) I.E) := {γ | γ ∈ Formalism.UG.UJ (starRingEnd I.E) I.J ∧
    (∀ i j, IsIntegral ℤ ((γ : Matrix (Fin I.n) (Fin I.n) I.E) i j)) ∧
    ∀ i j, IsIntegral ℤ (((γ⁻¹ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E) i j)}
  haveI : Finite (𝓞 I.E ⧸ Ideal.span {(M : 𝓞 I.E)}) := Ideal.finiteQuotientOfFreeOfNeBot _ (by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast (Nat.one_le_iff_ne_zero.1 hM))
  let Kq : (Fin I.n → Fin I.n → (𝓞 I.E ⧸ Ideal.span {(M : 𝓞 I.E)})) → Set I.Gf := fun q =>
    if h : ∃ γ, γ ∈ T ∧ red M (γ : Matrix (Fin I.n) (Fin I.n) I.E) = q then
      (fun k => fp I h.choose h.choose_spec.1.1 * k) '' I.Kset else ∅
  refine ⟨⋃ q, Kq q, isCompact_iUnion fun q => ?_, fun γ hγ hi hi' => ?_⟩
  · simp only [Kq]
    split_ifs
    · exact (Formalism.L2.SG.Closed.AutKCompact_holds I).image (continuous_const_mul _)
    · exact isCompact_empty
  · have hex : ∃ γ', γ' ∈ T ∧ red M (γ' : Matrix (Fin I.n) (Fin I.n) I.E) = red M (γ : Matrix (Fin I.n) (Fin I.n) I.E) :=
      ⟨γ, ⟨hγ, hi, hi'⟩, rfl⟩
    refine ⟨(fun v => Formalism.L2.S.S7.DensRat.ratReal I γ hγ v, fp I γ hγ), ⟨γ, hγ, fun v => rfl, rfl⟩,
      Set.mem_iUnion.2 ⟨red M (γ : Matrix (Fin I.n) (Fin I.n) I.E), ?_⟩, fun v => rfl⟩
    simp only [Kq, dif_pos hex]
    obtain ⟨hT', hr⟩ := hex.choose_spec
    set γ' := hex.choose with hγ'def
    refine ⟨(fp I γ' hT'.1)⁻¹ * fp I γ hγ, ?_, mul_inv_cancel_left _ _⟩
    have hδ : γ'⁻¹ * γ ∈ Formalism.UG.UJ (starRingEnd I.E) I.J := mul_mem (inv_mem hT'.1) hγ
    have hsub := sub_of_red M hT'.2.1 hi hr
    have c1 : CompanionTheory.D.gk.RF.Cong I M ((γ'⁻¹ * γ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E) := by
      have e : ((γ'⁻¹ * γ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E) - 1 =
          ((γ'⁻¹ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E) *
            ((γ : Matrix (Fin I.n) (Fin I.n) I.E) - (γ' : Matrix (Fin I.n) (Fin I.n) I.E)) := by
        rw [Matrix.mul_sub, Units.val_mul, ← Units.val_mul γ'⁻¹ γ', inv_mul_cancel, Units.val_one]
      intro i j
      rw [e]
      refine mul_cong M hT'.2.2 (fun k l => ?_) i j
      obtain ⟨b, hb, hb'⟩ := hsub k l
      exact ⟨-b, hb.neg, by rw [Matrix.sub_apply] at hb' ⊢; rw [← neg_sub, hb']; ring⟩
    have c2 : CompanionTheory.D.gk.RF.Cong I M (((γ'⁻¹ * γ)⁻¹ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E) := by
      have e : (((γ'⁻¹ * γ)⁻¹ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E) - 1 =
          ((γ⁻¹ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E) *
            ((γ' : Matrix (Fin I.n) (Fin I.n) I.E) - (γ : Matrix (Fin I.n) (Fin I.n) I.E)) := by
        rw [_root_.mul_inv_rev, inv_inv, Matrix.mul_sub, Units.val_mul, ← Units.val_mul γ⁻¹ γ, inv_mul_cancel, Units.val_one]
      intro i j
      rw [e]
      refine mul_cong M hi' (fun k l => ?_) i j
      obtain ⟨b, hb, hb'⟩ := hsub k l
      exact ⟨b, hb, by rw [Matrix.sub_apply] at hb' ⊢; exact hb'⟩
    obtain ⟨x, hxK, γ₀, hγ₀, hreal, hfin⟩ := hcong (fun v => Formalism.L2.S.S7.DensRat.ratReal I (γ'⁻¹ * γ) hδ v)
      ⟨γ'⁻¹ * γ, ⟨hδ, c1, c2⟩, fun v => rfl⟩
    obtain ⟨v⟩ := (inferInstance : Nonempty (InfinitePlace I.F))
    have h0 : γ₀ = γ'⁻¹ * γ := Units.ext (eq_of_real I v (hreal v).symm)
    have hx : x = fp I (γ'⁻¹ * γ) hδ := by
      apply Subtype.ext; apply Units.ext
      exact hfin.trans (by rw [h0]; rfl)
    rw [← fp_mul I hT'.1 hγ, ← hx]
    exact hxK

end GlobalTheory.IntUnitCpt
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCompactIntegralUnitaryFinitePartStatement

section

@[expose] public section

open NumberField Matrix Formalism.MainNotions.S GlobalTheory.CuspGeo GlobalTheory.ClassFin
open scoped Topology

theorem _root_.GlobalTheory.T.exists_compact_integral_unitary_finitePart : ∀ I : AutInst, ∃ K : Set I.Gf, IsCompact K ∧ ∀ γ : GL (Fin I.n) I.E, γ ∈ Formalism.UG.UJ (starRingEnd I.E) I.J → (∀ i j, IsIntegral ℤ ((γ : Matrix (Fin I.n) (Fin I.n) I.E) i j)) → (∀ i j, IsIntegral ℤ (((γ⁻¹ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E) i j)) → ∃ x ∈ I.GFset, x.2 ∈ K ∧ ∀ v, uMat (x.1 v) = (I.P v)⁻¹ * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v := by
  first | exact @GlobalTheory.IntUnitCpt.intUnit_compact | exact GlobalTheory.IntUnitCpt.intUnit_compact | (intros; apply GlobalTheory.IntUnitCpt.intUnit_compact <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralVectorBasesBoundedFiniteUnitaryClassesStatement

section

@[expose] public section

open NumberField Matrix Formalism.MainNotions.S GlobalTheory.CuspGeo GlobalTheory.ClassFin
open scoped Topology

theorem _root_.GlobalTheory.T.integralVectorBases_bounded_finite_unitaryClasses : ∀ (I : AutInst) (N : ℕ) (R : ℝ), ∃ S : Set (Fin N → Fin I.n → I.E), S.Finite ∧ (∀ e₀ ∈ S, IsZBasis I e₀) ∧ ∀ e : Fin N → Fin I.n → I.E, IsZBasis I e → BddType I R e → ∃ e₀ ∈ S, ∃ γ : GL (Fin I.n) I.E, γ ∈ Formalism.UG.UJ (starRingEnd I.E) I.J ∧ (∀ i j, IsIntegral ℤ ((γ : Matrix (Fin I.n) (Fin I.n) I.E) i j)) ∧ (∀ i j, IsIntegral ℤ (((γ⁻¹ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E) i j)) ∧ ∀ j, (γ : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ e j = e₀ j := by
  first | exact @GlobalTheory.BasesFin.bases_finite_classes | exact GlobalTheory.BasesFin.bases_finite_classes | (intros; apply GlobalTheory.BasesFin.bases_finite_classes <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.QuantitativeMahlerCriterionUnitaryGroup

section

@[expose] public section

open NumberField Matrix Formalism.MainNotions.S GlobalTheory.CuspGeo GlobalTheory.ClassFin
open scoped Topology

namespace GlobalTheory.HtMinPf

lemma uj_entry {n : ℕ} {ε : Fin n → Bool} (g : Formalism.REAL.UJ ε) (i j : Fin n) :
    ‖uMat g i j‖ = ‖uMat g⁻¹ j i‖ := by
  have hg : (uMat g)ᴴ * Formalism.REAL.Jm ε * uMat g = Formalism.REAL.Jm ε := g.2
  have h1 : uMat g * uMat g⁻¹ = 1 := by
    show ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) * (((g⁻¹ : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = 1
    rw [Subgroup.coe_inv, Units.mul_inv]
  have hJ := Formalism.REAL.Jm_mul_self ε
  have hmi : uMat g⁻¹ = Formalism.REAL.Jm ε * (uMat g)ᴴ * Formalism.REAL.Jm ε := by
    calc uMat g⁻¹ = Formalism.REAL.Jm ε * ((uMat g)ᴴ * Formalism.REAL.Jm ε * uMat g) * uMat g⁻¹ := by
            rw [hg, hJ, Matrix.one_mul]
      _ = Formalism.REAL.Jm ε * (uMat g)ᴴ * Formalism.REAL.Jm ε * (uMat g * uMat g⁻¹) := by
            simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1, Matrix.mul_one]
  rw [hmi]
  unfold Formalism.REAL.Jm
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply]
  by_cases ha : ε j <;> by_cases hb : ε i <;> simp [ha, hb]

variable (I : AutInst)

lemma vec_sum (y : I.Ginf) {N : ℕ} (z : Fin N → ℤ) (e : Fin N → Fin I.n → I.E) :
    vec I y (∑ i, z i • e i) = ∑ i, ((z i : ℝ)) • vec I y (e i) := by
  funext v
  have h : (fun k => I.φ v (∑ i, z i • e i k)) = ∑ i, ((z i : ℝ)) • fun k => I.φ v (e i k) := by
    funext k

    simp [Finset.sum_apply, map_sum, Complex.real_smul]
  simp only [CuspGeo.vec, Finset.sum_apply, Pi.smul_apply]
  rw [h, Matrix.mulVec_sum, Matrix.mulVec_sum]
  simp [Matrix.mulVec_smul]

lemma vec_one (y : I.Ginf) (u : Fin I.n → I.E) (v : InfinitePlace I.F) :
    vec I y u v = uMat (y v)⁻¹ *ᵥ vec I 1 u v := by
  have h1 : uMat ((1 : I.Ginf) v)⁻¹ = 1 := by simp [uMat]
  simp only [CuspGeo.vec]
  rw [h1, Matrix.one_mulVec]

lemma vec_trans (x₁ y : I.Ginf) (γ : GL (Fin I.n) I.E)
    (hx : ∀ v, uMat (x₁ v) = (I.P v)⁻¹ * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v)
    (u : Fin I.n → I.E) : vec I (x₁ * y) ((γ : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ u) = vec I y u := by
  funext v
  have hP : I.P v * (I.P v)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (I.P_unit v))
  have hinv : uMat (x₁ v)⁻¹ * uMat (x₁ v) = 1 := by
    show (((x₁ v)⁻¹ : Formalism.REAL.UJ (I.ε v)) : (Matrix (Fin I.n) (Fin I.n) ℂ)ˣ).val * ((x₁ v : Formalism.REAL.UJ (I.ε v)) : (Matrix (Fin I.n) (Fin I.n) ℂ)ˣ).val = 1
    rw [Subgroup.coe_inv, Units.inv_mul]
  have hφ : (fun i => I.φ v (((γ : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ u) i)) =
      (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) *ᵥ fun i => I.φ v (u i) := by
    funext i
    exact RingHom.map_mulVec _ _ _ _
  have hmul : uMat ((x₁ * y) v)⁻¹ = uMat (y v)⁻¹ * uMat (x₁ v)⁻¹ := by
    simp [uMat, Pi.mul_apply, _root_.mul_inv_rev]
  simp only [CuspGeo.vec]
  rw [hmul, hφ, ← Matrix.mulVec_mulVec]
  congr 1
  have : (I.P v)⁻¹ *ᵥ ((γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) *ᵥ fun i => I.φ v (u i)) =
      uMat (x₁ v) *ᵥ ((I.P v)⁻¹ *ᵥ fun i => I.φ v (u i)) := by
    rw [hx v, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc _ (I.P v), hP, Matrix.mul_one]
  rw [this, Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]

lemma span_of_zbasis {N : ℕ} (e₀ : Fin N → Fin I.n → I.E) (he₀ : IsZBasis I e₀)
    (w : InfinitePlace I.F → Fin I.n → ℂ) : ∃ c : Fin N → ℝ, w = ∑ l, c l • vec I 1 (e₀ l) := by
  obtain ⟨N', e', ρ, d, hd, he', -, hdet⟩ := GlobalTheory.T.cusp_integralBasis_covolume_constant I
  set G := gm I ρ 1 e' with hGdef
  have hG : G.det ≠ 0 := by
    intro h
    have := hdet 1
    rw [← hGdef, h] at this
    simp at this
    linarith
  set a := G⁻¹ *ᵥ ρ w with ha
  have hGa : G *ᵥ a = ρ w := by
    rw [ha, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hG), Matrix.one_mulVec]
  have hw : w = ∑ j, a j • vec I 1 (e' j) := by
    apply ρ.injective

    rw [← hGa, map_sum]
    funext i
    simp [hGdef, gm, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have hz : ∀ j, ∃ z : Fin N → ℤ, e' j = ∑ i, z i • e₀ i := fun j =>
    (he₀.2 (e' j)).mp ((he'.2 (e' j)).mpr ⟨Pi.single j 1, by simp [Pi.single_apply]⟩)
  choose z hz using hz
  refine ⟨fun i => ∑ j, a j * (z j i : ℝ), ?_⟩
  rw [hw]
  simp_rw [hz, vec_sum, Finset.smul_sum, smul_smul, Finset.sum_smul]
  rw [Finset.sum_comm]

open Classical in
lemma entry_bound (z : I.Ginf) {N : ℕ} (e₀ : Fin N → Fin I.n → I.E) (c : Fin N → ℝ)
    (v : InfinitePlace I.F) (i : Fin I.n)
    (hc : (Pi.single v (Pi.single i (1 : ℂ)) : InfinitePlace I.F → Fin I.n → ℂ) = ∑ l, c l • vec I 1 (e₀ l))
    (j : Fin I.n) : ‖uMat (z v)⁻¹ j i‖ ≤ ∑ l, |c l| * ‖vec I z (e₀ l)‖ := by
  have h : uMat (z v)⁻¹ j i = (∑ l, c l • vec I z (e₀ l)) v j := by
    calc uMat (z v)⁻¹ j i
        = (uMat (z v)⁻¹ *ᵥ (Pi.single v (Pi.single i (1 : ℂ)) : InfinitePlace I.F → Fin I.n → ℂ) v) j := by
          simp [Matrix.mulVec_single_one]
      _ = (uMat (z v)⁻¹ *ᵥ (∑ l, c l • vec I 1 (e₀ l)) v) j := by rw [hc]
      _ = (∑ l, c l • vec I z (e₀ l)) v j := by
          simp only [Finset.sum_apply, Pi.smul_apply, Matrix.mulVec_sum, Matrix.mulVec_smul, vec_one I z]
  rw [h, Finset.sum_apply, Finset.sum_apply]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)
  rw [Pi.smul_apply, Pi.smul_apply, norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left ((norm_le_pi_norm (vec I z (e₀ l) v) j).trans
    (norm_le_pi_norm (vec I z (e₀ l)) v)) (abs_nonneg _)

end GlobalTheory.HtMinPf


open GlobalTheory.HtMinPf in
theorem GlobalTheory.htMin_of_reduced : ∀ I : AutInst, HtMin I := by
  intro I
  classical
  obtain ⟨N, R, C, hred⟩ := GlobalTheory.T.existsReducedBasisBoundedType_of_instance I
  obtain ⟨S, hSfin, hS0, hS⟩ := GlobalTheory.T.integralVectorBases_bounded_finite_unitaryClasses I N R
  obtain ⟨K, hK, hK'⟩ := GlobalTheory.T.exists_compact_integral_unitary_finitePart I
  have hbd : ∀ e₀ : Fin N → Fin I.n → I.E, ∃ M : ℝ, e₀ ∈ S → ∀ v i, ∃ c : Fin N → ℝ,
      (Pi.single v (Pi.single i (1 : ℂ)) : InfinitePlace I.F → Fin I.n → ℂ) = ∑ l, c l • vec I 1 (e₀ l) ∧
        ∑ l, |c l| ≤ M := by
    intro e₀
    by_cases h : e₀ ∈ S
    · have := fun v i => span_of_zbasis I e₀ (hS0 e₀ h) (Pi.single v (Pi.single i (1 : ℂ)))
      choose c hc using this
      refine ⟨∑ v, ∑ i, ∑ l, |c v i l|, fun _ v i => ⟨c v i, hc v i, ?_⟩⟩
      calc ∑ l, |c v i l| ≤ ∑ i', ∑ l, |c v i' l| :=
            Finset.single_le_sum (f := fun i' => ∑ l, |c v i' l|)
              (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i)
        _ ≤ ∑ v', ∑ i', ∑ l, |c v' i' l| :=
            Finset.single_le_sum (f := fun v' => ∑ i', ∑ l, |c v' i' l|)
              (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)
              (Finset.mem_univ v)
    · exact ⟨0, fun h' => absurd h' h⟩
  choose M hM using hbd
  obtain ⟨Mt, hMt⟩ := (hSfin.image M).bddAbove
  refine ⟨N, Mt * max C 0, K, hK, ?_⟩
  intro y t ht0 ht1 hns
  obtain ⟨e, heZ, heB, hesz⟩ := hred y
  obtain ⟨e₀, he₀S, γ, hγU, hγi, hγi', hγe⟩ := hS e heZ heB
  obtain ⟨x, hxG, hxK, hx⟩ := hK' γ hγU hγi hγi'
  refine ⟨x, hxG, hxK, fun v i j => ?_⟩
  have hMle : M e₀ ≤ Mt := hMt (Set.mem_image_of_mem M he₀S)
  obtain ⟨c, hc, hcM⟩ := hM e₀ he₀S v i
  have hvec : ∀ l, vec I (x.1 * y) (e₀ l) = vec I y (e l) := fun l => by
    rw [← hγe l]
    exact vec_trans I x.1 y γ hx (e l)
  have hb := entry_bound I (x.1 * y) e₀ c v i hc j
  simp_rw [hvec] at hb
  have ht : 0 ≤ t ^ N := pow_nonneg ht0.le _
  rw [uj_entry]
  calc ‖uMat ((x.1 * y) v)⁻¹ j i‖ * t ^ N ≤ (∑ l, |c l| * ‖vec I y (e l)‖) * t ^ N :=
        mul_le_mul_of_nonneg_right hb ht
    _ = ∑ l, |c l| * (‖vec I y (e l)‖ * t ^ N) := by
        rw [Finset.sum_mul]
        simp_rw [mul_assoc]
    _ ≤ ∑ l, |c l| * max C 0 := Finset.sum_le_sum fun l _ =>
        mul_le_mul_of_nonneg_left ((hesz t ht0 ht1 hns l).trans (le_max_left _ _)) (abs_nonneg _)
    _ = (∑ l, |c l|) * max C 0 := by rw [Finset.sum_mul]
    _ ≤ Mt * max C 0 := mul_le_mul_of_nonneg_right (hcM.trans hMle) (le_max_right _ _)
end
end
