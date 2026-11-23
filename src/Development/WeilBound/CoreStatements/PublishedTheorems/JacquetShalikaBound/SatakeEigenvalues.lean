module

public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaBound.lift_levelP_alt₂
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormSatakeLeOfUnitarySphericalGL
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SymmetricFunctionAbsoluteValues
import GroundTheory.AutomorphicForms.MacdonaldRecursion
public import GroundTheory.IdeleRoots.TorusPowers.SatakeBoundAdic
public import GroundTheory.AutomorphicForms.SphericalMinuscule
public import GroundTheory.AutomorphicForms.AffineBruhat
public import GroundTheory.AutomorphicForms.MacdonaldHecke
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.ReduceModChar
public import GroundTheory.GlobalFields.LocalFieldAtPlace

-- Source module: GroundTheory.IdeleRoots.TorusPowers.SatakeBoundGroup

section

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.BlockD

namespace SatakeBound

open GroundTheory.Automorphic GroundTheory.Automorphic.Spherical GLnLocal Iwasawa Finset Matrix
open scoped ValuativeRel

attribute [local instance] GroundTheory.Automorphic.Spherical.fintypeResidue

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem exists_perm_mem_iff {N : ℕ} {A B : Finset (Fin N)} (h : A.card = B.card) :
    ∃ σ : Equiv.Perm (Fin N), ∀ x, σ x ∈ B ↔ x ∈ A := by
  classical
  have e1 : {x // x ∈ A} ≃ {x // x ∈ B} := Fintype.equivOfCardEq (by simp [h])
  have e2 : {x // x ∉ A} ≃ {x // x ∉ B} :=
    Fintype.equivOfCardEq (by rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl]; simp [h])
  refine ⟨(Equiv.sumCompl (· ∈ A)).symm.trans ((Equiv.sumCongr e1 e2).trans (Equiv.sumCompl (· ∈ B))),
    fun x => ?_⟩
  by_cases hx : x ∈ A
  · rw [Equiv.trans_apply, Equiv.trans_apply, Equiv.sumCompl_symm_apply_of_pos hx, Equiv.sumCongr_apply,
      Sum.map_inl, Equiv.sumCompl_apply_inl]
    exact ⟨fun _ => hx, fun _ => (e1 ⟨x, hx⟩).2⟩
  · rw [Equiv.trans_apply, Equiv.trans_apply, Equiv.sumCompl_symm_apply_of_neg hx, Equiv.sumCongr_apply,
      Sum.map_inr, Equiv.sumCompl_apply_inr]
    exact ⟨fun h' => absurd h' (e2 ⟨x, hx⟩).2, fun h' => absurd h' hx⟩

theorem lamS_comp_of_mem_iff {N : ℕ} {A B : Finset (Fin N)} {σ : Equiv.Perm (Fin N)}
    (hσ : ∀ x, σ x ∈ B ↔ x ∈ A) : lamS B ∘ σ = lamS A := by
  funext x
  simp only [Function.comp_apply, lamS, hσ]

section Values

variable {n : ℕ} {ω : GL (Fin n) F → ℂ}
  (hR : ∀ g, ∀ k ∈ integralGL F n, ω (g * k) = ω g)
  (hL : ∀ g, ∀ k ∈ integralGL F n, ω (k * g) = ω g)
include hR hL

end Values

section ValuesCons

variable {N : ℕ} {ω : GL (Fin (N + 1)) F → ℂ}
  (hR : ∀ g, ∀ k ∈ integralGL F (N + 1), ω (g * k) = ω g)
  (hL : ∀ g, ∀ k ∈ integralGL F (N + 1), ω (k * g) = ω g)
include hR hL

end ValuesCons

variable {n : ℕ} [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]


end SatakeBound

end GroundTheory.BlockD
end
end
end

-- Source module: GroundTheory.IdeleRoots.TorusPowers.SatakeBoundReps

section

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.BlockD

namespace SatakeBound

section Group

variable {G : Type} [Group G] {K : Subgroup G} {α : G} {R : Finset G}

end Group

open GroundTheory.Automorphic GroundTheory.Automorphic.Spherical GLnLocal Iwasawa Finset Matrix
open scoped ValuativeRel

attribute [local instance] GroundTheory.Automorphic.Spherical.fintypeResidue

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem one_apply_mem_integer (i j : Fin n) : (1 : Matrix (Fin n) (Fin n) F) i j ∈ 𝒪[F] := by
  rw [Matrix.one_apply]
  split_ifs
  · exact (𝒪[F]).one_mem
  · exact (𝒪[F]).zero_mem

theorem unipC_mem_integralGL (S : Finset (Fin n)) (c : Pairs S → 𝓀[F]) : unipC S c ∈ integralGL F n := by
  rw [mem_integralGL_iff]
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · change (1 + cMat S c) i j ∈ 𝒪[F]
    rw [Matrix.add_apply]
    exact (𝒪[F]).add_mem (one_apply_mem_integer i j) (cMat_mem c i j)
  · change (1 - cMat S c) i j ∈ 𝒪[F]
    rw [Matrix.sub_apply]
    exact (𝒪[F]).sub_mem (one_apply_mem_integer i j) (cMat_mem c i j)

theorem exists_torusPow_lamS_eq {A B : Finset (Fin n)} (h : A.card = B.card) :
    ∃ P ∈ integralGL F n, torusPow F n (lamS A) = P⁻¹ * torusPow F n (lamS B) * P := by
  obtain ⟨σ, hσ⟩ := exists_perm_mem_iff h
  refine ⟨permGL F σ, GLnLocal.permGL_mem_integralGL F n σ, ?_⟩
  rw [permGL_conj_torusPow, lamS_comp_of_mem_iff hσ]

end SatakeBound

end GroundTheory.BlockD
end
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaBound.SatakeEigenvalues

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.LFun GroundTheory.Automorphic GroundTheory.Automorphic.Spherical
open scoped ValuativeRel

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.JacquetShalikaLocal

namespace SatakeEigenvalues

open GLnLocal Iwasawa

variable {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))

theorem qF_eq : qF (w.adicCompletion E) = Ideal.absNorm w.asIdeal :=
  GlobalTheory.LFun.SatBoundGL.resCard_completion w

theorem O_eq : 𝒪[w.adicCompletion E] = Formalism.UG.Ov E w := by
  ext x
  exact GroundTheory.Global.mem_valuationInteger_iff w x

theorem KGL_eq (n : ℕ) : KGL w (n := n) = integralGL (w.adicCompletion E) n :=
  (congrArg (Formalism.UG.GLint (Fin n)) (O_eq w)).symm.trans rfl

theorem isUnifV_uniformizer :
    Formalism.UG.IsUnifV E w (uniformizer (w.adicCompletion E) : w.adicCompletion E) :=
  GroundTheory.BlockD.SatakeBound.valued_uniformizer_eq w

theorem satEig_eq {n r : ℕ} (hr : r ≤ n) (z : Fin n → ℂˣ) :
    satEig (Formalism.UG.qV E w) n (Finset.univ.val.map z) r =
      sqrtQ (w.adicCompletion E) ^ (r * (n - r)) * evalAt z (esymmL n r) := by
  unfold satEig
  rw [Multiset.map_map, Finset.esymm_map_val, GlobalTheory.CompanionTheory.JSBound.evalAt_esymmL_eq_sum_prod]
  congr 1
  have hq : (Formalism.UG.qV E w : ℂ) = ((qF (w.adicCompletion E) : ℝ) : ℂ) := by
    rw [qF_eq]
    simp [Formalism.UG.qV]
  have he : ((r : ℂ) * ((n : ℂ) - r)) / 2 = ((((r * (n - r) : ℕ) : ℝ) / 2 : ℝ) : ℂ) := by
    push_cast [Nat.cast_sub hr]
    ring
  rw [hq, he, ← Complex.ofReal_cpow (Nat.cast_nonneg _), sqrtQ, ← Complex.ofReal_pow]
  congr 1
  rw [Real.coe_sqrt, NNReal.coe_natCast, Real.sqrt_eq_rpow, ← Real.rpow_natCast,
    ← Real.rpow_mul (Nat.cast_nonneg _)]
  congr 1
  ring

theorem Tj_eq {n r : ℕ} (hr : r ≤ n) :
    Formalism.UG.Tj ℂ n (Formalism.UG.Ov E w) (uniformizer (w.adicCompletion E) : w.adicCompletion E) r =
      (minusculeSet (w.adicCompletion E) n r).indicator (fun _ => (1 : ℂ)) := by
  have hK : Formalism.UG.GLint (Fin n) (Formalism.UG.Ov E w) = integralGL (w.adicCompletion E) n := KGL_eq w n
  have hD : Formalism.UG.diagJ n (uniformizer (w.adicCompletion E) : w.adicCompletion E) r =
      ((torusPow (w.adicCompletion E) n (lamS (initSeg hr)) : GL (Fin n) (w.adicCompletion E)) :
        Matrix (Fin n) (Fin n) (w.adicCompletion E)) := by
    rw [coe_torusPow, Formalism.UG.diagJ]
    congr 1
    funext i
    rw [lamS_apply]
    by_cases h : (i : ℕ) < r <;> simp [h, mem_initSeg]
  have hα : torusPow (w.adicCompletion E) n (lamS (initSeg hr)) ∈ minusculeSet (w.adicCompletion E) n r := by
    let c₀ : Pairs (initSeg hr) → 𝓀[w.adicCompletion E] := fun _ => 0
    have e : torusPow (w.adicCompletion E) n (lamS (initSeg hr)) =
        (unipC (initSeg hr) c₀)⁻¹ * gMat (initSeg hr) c₀ * 1 := by
      rw [gMat, inv_mul_cancel_left, mul_one]
    have h := mul_mem_minusculeSet (gMat_mem_minusculeSet _ c₀)
      ((integralGL (w.adicCompletion E) n).inv_mem (GroundTheory.BlockD.SatakeBound.unipC_mem_integralGL _ c₀))
      (integralGL (w.adicCompletion E) n).one_mem
    rw [card_initSeg] at h
    rw [e]
    exact h
  have hS : {g : GL (Fin n) (w.adicCompletion E) | ∃ a ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov E w),
      ∃ b ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov E w),
      (g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) = (a : Matrix (Fin n) (Fin n) (w.adicCompletion E)) *
        Formalism.UG.diagJ n (uniformizer (w.adicCompletion E) : w.adicCompletion E) r *
          (b : Matrix (Fin n) (Fin n) (w.adicCompletion E))} = minusculeSet (w.adicCompletion E) n r := by
    ext g
    rw [hK, hD]
    constructor
    · rintro ⟨a, ha, b, hb, e⟩
      have e' : g = a * torusPow (w.adicCompletion E) n (lamS (initSeg hr)) * b :=
        Units.ext (by rw [e, Units.val_mul, Units.val_mul])
      rw [e']
      exact mul_mem_minusculeSet hα ha hb
    · intro hg
      obtain ⟨S, hS, c, hc⟩ := exists_gMat hg
      have hk : (gMat S c)⁻¹ * g ∈ integralGL (w.adicCompletion E) n := QuotientGroup.eq.1 hc
      obtain ⟨P, hP, hPe⟩ := GroundTheory.BlockD.SatakeBound.exists_torusPow_lamS_eq (F := w.adicCompletion E)
        (A := S) (B := initSeg hr) (by rw [hS, card_initSeg])
      have e1 : g = gMat S c * ((gMat S c)⁻¹ * g) := by group
      set k := (gMat S c)⁻¹ * g with hkdef
      rw [gMat, hPe] at e1
      refine ⟨unipC S c * P⁻¹, (integralGL (w.adicCompletion E) n).mul_mem
        (GroundTheory.BlockD.SatakeBound.unipC_mem_integralGL S c) ((integralGL (w.adicCompletion E) n).inv_mem hP),
        P * k, (integralGL (w.adicCompletion E) n).mul_mem hP hk, ?_⟩
      rw [← Units.val_mul, ← Units.val_mul]
      congr 1
      rw [e1]
      group
  rw [Formalism.UG.Tj, hS]
  rfl

end SatakeEigenvalues

theorem satake_eigenvalue_formula : lift_levelP_alt₂ := by
  intro E _ _ w
  refine ⟨SatakeEigenvalues.qF_eq w, ?_⟩
  intro n V _ _ ρ v z h
  obtain ⟨-, hfix, -, hT⟩ := h
  have hK := SatakeEigenvalues.KGL_eq w n
  refine ⟨fun g hg => GlobalTheory.LGrp.mem_fixed.1 hfix g (hK ▸ hg), fun r hr => ?_⟩
  have h1 := hT _ (SatakeEigenvalues.isUnifV_uniformizer w) r hr
  rw [heckeVec, SatakeEigenvalues.Tj_eq w hr, SatakeEigenvalues.satEig_eq w hr] at h1
  rw [hK] at h1
  exact h1

end PositivityTheory.JacquetShalikaLocal

end
end
end
