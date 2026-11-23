module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSumOfMemMultSpan
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Mathlib.Algebra.Module.LinearMap.Star
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Order.CompletePartialOrder
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspFormFiniteDimCompactStable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsQuadOfPlane
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.KTypeProjectionOfKFinite

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.AbstractCompleteReducibility

section

@[expose] public section

open Module

namespace GlobalTheory

theorem exists_mem_sub_orth_of_finiteDimensional {E : Type} [AddCommGroup E] [Module ℂ E]
    (b : E →ₗ⋆[ℂ] E →ₗ[ℂ] ℂ) (T : Submodule ℂ E) [FiniteDimensional ℂ T]
    (hT : ∀ t ∈ T, b t t = 0 → t = 0) (ψ : E) : ∃ s ∈ T, ∀ t ∈ T, b t (ψ - s) = 0 := by
  let bs := Module.finBasis ℂ T
  let F : E →ₗ[ℂ] (Fin (finrank ℂ T) → ℂ) := LinearMap.pi fun i => b (bs i : E)
  have key : ∀ x, F x = 0 → ∀ t ∈ T, b t x = 0 := by
    intro x hx t ht
    have h1 : (b.flip x) ∘ₛₗ T.subtype = 0 :=
      bs.ext fun i => by simpa [F] using congrFun hx i
    exact LinearMap.congr_fun h1 ⟨t, ht⟩
  have hinj : Function.Injective (F ∘ₗ T.subtype) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro z hz
    exact Subtype.ext (hT z z.2 (key z hz z z.2))
  have hsurj : Function.Surjective (F ∘ₗ T.subtype) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp)).1 hinj
  obtain ⟨z, hz⟩ := hsurj (F ψ)
  refine ⟨z, z.2, key (ψ - z) ?_⟩
  rw [map_sub, ← hz]
  simp

theorem abstract_complete_reducibility :
    ∀ {E : Type} [AddCommGroup E] [Module ℂ E] (P : Submodule ℂ E → Prop),
    (∀ s : Set (Submodule ℂ E), (∀ A ∈ s, P A) → P (sInf s)) →
    ∀ (N : Submodule ℂ E), P N → ∀ (b : E →ₗ⋆[ℂ] E →ₗ[ℂ] ℂ), (∀ x ∈ N, x ≠ 0 → 0 < (b x x).re) →
    (∀ x ∈ N, ∀ y ∈ N, star (b x y) = b y x) →
    (∀ A : Submodule ℂ E, A ≤ N → P A → P (N ⊓ ⨅ a ∈ A, LinearMap.ker (b a))) →
    ∀ (e : E →ₗ[ℂ] E), (∀ A : Submodule ℂ E, A ≤ N → P A → ∀ x ∈ A, e x ∈ A) → (∀ x ∈ N, e (e x) = e x) →
    (∀ x ∈ N, ∀ y ∈ N, b (e x) y = b x (e y)) → FiniteDimensional ℂ (N.map e) →
    ∀ ψ ∈ N, e ψ = ψ →
    ψ ∈ ⨆ (A : Submodule ℂ E) (_ : A ≤ N ∧ P A ∧ A ≠ ⊥ ∧ ∀ B : Submodule ℂ E, B ≤ A → P B → B = ⊥ ∨ B = A), A := by
  classical
  intro E _ _ P hInf N hN b hpos _hherm hperp e he hidem hsa hfin ψ hψN hψe
  let S := ⨆ (A : Submodule ℂ E) (_ : A ≤ N ∧ P A ∧ A ≠ ⊥ ∧
    ∀ B : Submodule ℂ E, B ≤ A → P B → B = ⊥ ∨ B = A), A
  show ψ ∈ S
  let V := N.map e
  have hVN : V ≤ N := by rintro _ ⟨x, hx, rfl⟩; exact he N le_rfl hN x hx
  have heV : ∀ v ∈ V, e v = v := by rintro _ ⟨x, hx, rfl⟩; exact hidem x hx
  have hψV : ψ ∈ V := ⟨ψ, hψN, hψe⟩
  have hIrrS : ∀ A : Submodule ℂ E, (A ≤ N ∧ P A ∧ A ≠ ⊥ ∧
      ∀ B : Submodule ℂ E, B ≤ A → P B → B = ⊥ ∨ B = A) → A ≤ S :=
    fun A hA => le_iSup₂_of_le (f := fun A (_ : A ≤ N ∧ P A ∧ A ≠ ⊥ ∧
      ∀ B : Submodule ℂ E, B ≤ A → P B → B = ⊥ ∨ B = A) => A) A hA le_rfl
  have hpos0 : ∀ x ∈ N, b x x = 0 → x = 0 := by
    intro x hx h0
    by_contra hne
    have := hpos x hx hne
    rw [h0] at this
    simp at this
  have hGen : ∀ x : E, ∃ G : Submodule ℂ E, x ∈ G ∧ P G ∧ ∀ A, x ∈ A → P A → G ≤ A := fun x =>
    ⟨sInf {A | x ∈ A ∧ P A}, Submodule.mem_sInf.2 fun A hA => hA.1, hInf _ fun A hA => hA.2,
      fun A hx hA => sInf_le ⟨hx, hA⟩⟩
  let C : Submodule ℂ E := sInf (insert N {X | ∃ A : Submodule ℂ E, (A ≤ N ∧ P A ∧ A ≠ ⊥ ∧
    ∀ B : Submodule ℂ E, B ≤ A → P B → B = ⊥ ∨ B = A) ∧ X = N ⊓ ⨅ a ∈ A, LinearMap.ker (b a)})
  have hCP : P C := by
    apply hInf
    rintro X (rfl | ⟨A, hA, rfl⟩)
    · exact hN
    · exact hperp A hA.1 hA.2.1
  have hCorth : ∀ x ∈ C, ∀ A : Submodule ℂ E, (A ≤ N ∧ P A ∧ A ≠ ⊥ ∧
      ∀ B : Submodule ℂ E, B ≤ A → P B → B = ⊥ ∨ B = A) → ∀ a ∈ A, b a x = 0 := by
    intro x hx A hA a ha
    have : x ∈ N ⊓ ⨅ a ∈ A, LinearMap.ker (b a) :=
      Submodule.mem_sInf.1 hx _ (Set.mem_insert_of_mem _ ⟨A, hA, rfl⟩)
    simp only [Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker] at this
    exact this.2 a ha
  have hCmem : ∀ x ∈ N, (∀ A : Submodule ℂ E, (A ≤ N ∧ P A ∧ A ≠ ⊥ ∧
      ∀ B : Submodule ℂ E, B ≤ A → P B → B = ⊥ ∨ B = A) → ∀ a ∈ A, b a x = 0) → x ∈ C := by
    intro x hx h
    refine Submodule.mem_sInf.2 ?_
    rintro X (rfl | ⟨A, hA, rfl⟩)
    · exact hx
    · simp only [Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker]
      exact ⟨hx, fun a ha => h A hA a ha⟩
  have hfinT : FiniteDimensional ℂ ↥(S ⊓ V) := Submodule.finiteDimensional_of_le inf_le_right
  obtain ⟨s, hsT, hsorth⟩ := exists_mem_sub_orth_of_finiteDimensional b (S ⊓ V)
    (fun t ht h0 => hpos0 t (hVN ht.2) h0) ψ
  have hcV : ψ - s ∈ V := V.sub_mem hψV hsT.2
  have hcC : ψ - s ∈ C := by
    refine hCmem _ (hVN hcV) fun A hA a ha => ?_
    have haN : a ∈ N := hA.1 ha
    have heaT : e a ∈ S ⊓ V := ⟨hIrrS A hA (he A hA.1 hA.2.1 a ha), ⟨a, haN, rfl⟩⟩
    rw [← heV _ hcV, ← hsa a haN _ (hVN hcV)]
    exact hsorth _ heaT
  suffices hc0 : ψ - s = 0 by
    rw [sub_eq_zero] at hc0
    rw [hc0]
    exact hsT.1
  by_contra hc0
  obtain ⟨D, hcD, hDP, hDmin⟩ := hGen (ψ - s)
  have hDC : D ≤ C := hDmin C hcC hCP
  have hDN : D ≤ N := hDmin N (hVN hcV) hN
  have hex : ∃ n, ∃ B : Submodule ℂ E, B ≤ D ∧ P B ∧ B ⊓ V ≠ ⊥ ∧ finrank ℂ ↥(B ⊓ V) = n :=
    ⟨_, D, le_rfl, hDP, (Submodule.ne_bot_iff _).2 ⟨ψ - s, ⟨hcD, hcV⟩, hc0⟩, rfl⟩
  obtain ⟨B, hBD, hBP, hBV, hBn⟩ := Nat.find_spec hex
  have hmin : ∀ B₁ : Submodule ℂ E, B₁ ≤ D → P B₁ → B₁ ⊓ V ≠ ⊥ →
      Nat.find hex ≤ finrank ℂ ↥(B₁ ⊓ V) :=
    fun B₁ h1 h2 h3 => Nat.find_min' hex ⟨B₁, h1, h2, h3, rfl⟩
  obtain ⟨β, hβBV, hβ0⟩ := (Submodule.ne_bot_iff _).1 hBV
  obtain ⟨G, hβG, hGP, hGmin⟩ := hGen β
  have hGB : G ≤ B := hGmin B hβBV.1 hBP
  have hGN : G ≤ N := hGB.trans (hBD.trans hDN)
  have hβV : β ∈ V := hβBV.2
  have hβe : e β = β := heV β hβV
  have hGirr : G ≤ N ∧ P G ∧ G ≠ ⊥ ∧ ∀ B'' : Submodule ℂ E, B'' ≤ G → P B'' → B'' = ⊥ ∨ B'' = G := by
    refine ⟨hGN, hGP, (Submodule.ne_bot_iff _).2 ⟨β, hβG, hβ0⟩, fun B'' hle hP => ?_⟩
    have hB''N : B'' ≤ N := hle.trans hGN
    by_cases hV'' : B'' ⊓ V = ⊥
    · left
      have hey : ∀ y ∈ B'', e y = 0 := by
        intro y hy
        have : e y ∈ B'' ⊓ V := ⟨he B'' hB''N hP y hy, ⟨y, hB''N hy, rfl⟩⟩
        rw [hV''] at this
        exact (Submodule.mem_bot ℂ).1 this
      have hβperp : β ∈ N ⊓ ⨅ a ∈ B'', LinearMap.ker (b a) := by
        simp only [Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker]
        refine ⟨hVN hβV, fun y hy => ?_⟩
        rw [← hβe, ← hsa y (hB''N hy) β (hVN hβV), hey y hy, map_zero, LinearMap.zero_apply]
      have hGperp := hGmin _ hβperp (hperp B'' hB''N hP)
      rw [eq_bot_iff]
      intro y hy
      have hyp := hGperp (hle hy)
      simp only [Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker] at hyp
      exact (Submodule.mem_bot ℂ).2 (hpos0 y (hB''N hy) (hyp.2 y hy))
    · right
      have hle' : B'' ⊓ V ≤ B ⊓ V := inf_le_inf_right _ (hle.trans hGB)
      have hfinBV : FiniteDimensional ℂ ↥(B ⊓ V) := Submodule.finiteDimensional_of_le inf_le_right
      have heq : B'' ⊓ V = B ⊓ V := Submodule.eq_of_le_of_finrank_le hle' (by
        rw [hBn]; exact hmin B'' (hle.trans (hGB.trans hBD)) hP hV'')
      have hβB'' : β ∈ B'' := by
        have h2 := hβBV
        rw [← heq] at h2
        exact h2.1
      exact le_antisymm hle (hGmin B'' hβB'' hP)
  exact hβ0 (hpos0 β (hVN hβV) (hCorth β (hDC (hBD hβBV.1)) G hGirr β hβG))

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.AbstractCompleteReducibilityStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.mem_iSup_irreducible_of_fixed_projector : ∀ {E : Type} [AddCommGroup E] [Module ℂ E] (P : Submodule ℂ E → Prop),
    (∀ s : Set (Submodule ℂ E), (∀ A ∈ s, P A) → P (sInf s)) →
    ∀ (N : Submodule ℂ E), P N → ∀ (b : E →ₗ⋆[ℂ] E →ₗ[ℂ] ℂ), (∀ x ∈ N, x ≠ 0 → 0 < (b x x).re) →
    (∀ x ∈ N, ∀ y ∈ N, star (b x y) = b y x) →
    (∀ A : Submodule ℂ E, A ≤ N → P A → P (N ⊓ ⨅ a ∈ A, LinearMap.ker (b a))) →
    ∀ (e : E →ₗ[ℂ] E), (∀ A : Submodule ℂ E, A ≤ N → P A → ∀ x ∈ A, e x ∈ A) → (∀ x ∈ N, e (e x) = e x) →
    (∀ x ∈ N, ∀ y ∈ N, b (e x) y = b x (e y)) → FiniteDimensional ℂ (N.map e) →
    ∀ ψ ∈ N, e ψ = ψ →
    ψ ∈ ⨆ (A : Submodule ℂ E) (_ : A ≤ N ∧ P A ∧ A ≠ ⊥ ∧ ∀ B : Submodule ℂ E, B ≤ A → P B → B = ⊥ ∨ B = A), A := by
  first | exact @GlobalTheory.abstract_complete_reducibility | exact GlobalTheory.abstract_complete_reducibility | (intros; apply GlobalTheory.abstract_complete_reducibility <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.GKSubmoduleInfimumAndIrreducibleSupremum

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical

noncomputable section

namespace GlobalTheory.CuspGK

variable {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) {V : HSp D} {S : D.what₂.Tau → SPar}
  (M : Formalism.IndefR.Mult.DSModel V S)

theorem isGKSub_sInf (s : Set (Submodule ℂ (GA D V → ℂ))) (h : ∀ A ∈ s, IsGKSub θ M A) : IsGKSub θ M (sInf s) := by
  constructor
  · intro τ g hg f hf
    exact Submodule.mem_sInf.2 fun A hA => (h A hA).k τ g hg f (Submodule.mem_sInf.1 hf A hA)
  · intro τ X hX f hf
    exact Submodule.mem_sInf.2 fun A hA => (h A hA).lie τ X hX f (Submodule.mem_sInf.1 hf A hA)


open scoped Matrix in
variable {M} in
theorem InK.inv {τ : D.what₂.Tau} {g : Matrix (Fin V.rank) (Fin V.rank) ℂ} (h : InK M τ g) : InK M τ g⁻¹ := by
  obtain ⟨hU, hk⟩ := h
  have hfd : IsUnit (M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  set k := M.fr τ * g * (M.fr τ)⁻¹ with hkdef
  have hku : k ∈ Matrix.unitaryGroup (Fin V.rank) ℂ := hk.1
  have hsk : star k * k = 1 := Matrix.mem_unitaryGroup_iff'.1 hku
  have hks : k * star k = 1 := Matrix.mem_unitaryGroup_iff.1 hku
  have hkdet : IsUnit k.det := (Matrix.isUnit_iff_isUnit_det _).1 ⟨⟨k, star k, hks, hsk⟩, rfl⟩
  have hdet : k.det = g.det := by
    rw [hkdef, Matrix.det_mul, Matrix.det_mul, mul_comm (M.fr τ).det, mul_assoc, ← Matrix.det_mul,
      Matrix.mul_nonsing_inv _ hfd, Matrix.det_one, mul_one]
  have hgd : IsUnit g.det := hdet ▸ hkdet
  have hg1 : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv _ hgd
  have hU' : gᴴ * gramAt D V τ * g = gramAt D V τ := hU
  refine ⟨?_, ?_⟩
  · show (g⁻¹)ᴴ * gramAt D V τ * g⁻¹ = gramAt D V τ
    calc (g⁻¹)ᴴ * gramAt D V τ * g⁻¹ = (g⁻¹)ᴴ * (gᴴ * gramAt D V τ * g) * g⁻¹ := by rw [hU']
      _ = (g * g⁻¹)ᴴ * gramAt D V τ * (g * g⁻¹) := by
        rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = gramAt D V τ := by rw [hg1, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  · have e1 : M.fr τ * g⁻¹ * (M.fr τ)⁻¹ = k⁻¹ := by
      rw [hkdef, Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hfd]
      simp only [Matrix.mul_assoc]
    have hinv : k⁻¹ = star k := Matrix.inv_eq_left_inv hsk
    rw [e1, hinv]
    refine ⟨Matrix.mem_unitaryGroup_iff.2 (by rw [star_star]; exact hsk), ?_⟩
    have hJ : star (Formalism.REAL.Jm (M.ε τ)) = Formalism.REAL.Jm (M.ε τ) := Formalism.REAL.Jm_conjTranspose _
    have hcomm : ∀ m : Matrix (Fin V.rank) (Fin V.rank) ℂ, m * Formalism.REAL.Jm (M.ε τ) = Formalism.REAL.Jm (M.ε τ) * m →
        star m * Formalism.REAL.Jm (M.ε τ) = Formalism.REAL.Jm (M.ε τ) * star m := fun m hm => by
      have h2 : star (m * Formalism.REAL.Jm (M.ε τ)) = star (Formalism.REAL.Jm (M.ε τ) * m) := congrArg star hm
      rw [star_mul, star_mul, hJ] at h2
      exact h2.symm
    exact hcomm k hk.2

end GlobalTheory.CuspGK

end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.CuspFormPeterssonNonvanishingGelfandKirillov

section

@[expose] public section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical
noncomputable section
namespace GlobalTheory.CuspGKPet
open Matrix GlobalTheory.PointAtPlaceHom GlobalTheory.Mem.RealTranslate GlobalTheory.CuspGK GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D}
theorem exists_petersson_pairing_gelfandKirillov_generator : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)
    (S : D.what₂.Tau → SPar) (M : Formalism.IndefR.Mult.DSModel V S), IsInfFam (D := D) θ →
    ∀ ψ : GA D V → ℂ, IsAutFunSm θ V ψ → IsCuspFun V ψ →
    (∃ W : Submodule ℂ (GA D V → ℂ), FiniteDimensional ℂ W ∧ ψ ∈ W ∧ ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ),
      M.fr τ * g * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ) → ∀ f ∈ W, rTr V (atTau θ V τ g) f ∈ W) →
    ∃ b : (GA D V → ℂ) →ₗ⋆[ℂ] (GA D V → ℂ) →ₗ[ℂ] ℂ,
      (∀ x ∈ GlobalTheory.CuspGK.gkGen θ M ψ, x ≠ 0 → 0 < (b x x).re) ∧
      (∀ x ∈ GlobalTheory.CuspGK.gkGen θ M ψ, ∀ y ∈ GlobalTheory.CuspGK.gkGen θ M ψ, star (b x y) = b y x) ∧
      (∀ τ g, GlobalTheory.CuspGK.InK M τ g → ∀ x ∈ GlobalTheory.CuspGK.gkGen θ M ψ, ∀ y ∈ GlobalTheory.CuspGK.gkGen θ M ψ,
        b x (rTr V (atTau θ V τ g) y) = b (rTr V (atTau θ V τ g⁻¹) x) y) ∧
      (∀ τ, ∀ X ∈ lieAt V τ, ∀ x ∈ GlobalTheory.CuspGK.gkGen θ M ψ, ∀ y ∈ GlobalTheory.CuspGK.gkGen θ M ψ,
        b x (Rder θ V τ X y) = -b (Rder θ V τ X x) y) := by
  intro hP D θ V S M hθ ψ h1 h2 _
  obtain ⟨b, b1, b2, b3, b4⟩ := exists_form_cuspSub (V := V) hP.cuspRapidDecay hθ
  have hle : gkGen θ M ψ ≤ cuspSub θ V := gkGen_le θ M (A := cuspSub θ V) ⟨h1, h2⟩
    ⟨fun _ _ hg _ hf => rTr_mem_cuspSub hθ hg.1 hf, fun _ _ hX _ hf => Rder_mem_cuspSub hθ hX hf⟩
  exact ⟨b, fun x hx => b1 x (hle hx), fun x hx y hy => b2 x (hle hx) y (hle hy),
    fun τ g hg x hx y hy => b3 τ g hg.1 x (hle hx) y (hle hy),
    fun τ X hX x hx y hy => b4 τ X hX x (hle hx) y (hle hy)⟩
end GlobalTheory.CuspGKPet
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical

theorem _root_.GlobalTheory.T.cusp_form_petersson_nonvanishing_gelfandKirillov : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)
    (S : D.what₂.Tau → SPar) (M : Formalism.IndefR.Mult.DSModel V S), IsInfFam (D := D) θ →
    ∀ ψ : GA D V → ℂ, IsAutFunSm θ V ψ → IsCuspFun V ψ →
    (∃ W : Submodule ℂ (GA D V → ℂ), FiniteDimensional ℂ W ∧ ψ ∈ W ∧ ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ),
      M.fr τ * g * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ) → ∀ f ∈ W, rTr V (atTau θ V τ g) f ∈ W) →
    ∃ b : (GA D V → ℂ) →ₗ⋆[ℂ] (GA D V → ℂ) →ₗ[ℂ] ℂ,
      (∀ x ∈ GlobalTheory.CuspGK.gkGen θ M ψ, x ≠ 0 → 0 < (b x x).re) ∧
      (∀ x ∈ GlobalTheory.CuspGK.gkGen θ M ψ, ∀ y ∈ GlobalTheory.CuspGK.gkGen θ M ψ, star (b x y) = b y x) ∧
      (∀ τ g, GlobalTheory.CuspGK.InK M τ g → ∀ x ∈ GlobalTheory.CuspGK.gkGen θ M ψ, ∀ y ∈ GlobalTheory.CuspGK.gkGen θ M ψ,
        b x (rTr V (atTau θ V τ g) y) = b (rTr V (atTau θ V τ g⁻¹) x) y) ∧
      (∀ τ, ∀ X ∈ lieAt V τ, ∀ x ∈ GlobalTheory.CuspGK.gkGen θ M ψ, ∀ y ∈ GlobalTheory.CuspGK.gkGen θ M ψ,
        b x (Rder θ V τ X y) = -b (Rder θ V τ X x) y) := by
  first | exact @_root_.GlobalTheory.CuspGKPet.exists_petersson_pairing_gelfandKirillov_generator | exact _root_.GlobalTheory.CuspGKPet.exists_petersson_pairing_gelfandKirillov_generator | (intros; apply _root_.GlobalTheory.CuspGKPet.exists_petersson_pairing_gelfandKirillov_generator <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.CuspFormsEqISupIrreducibleGK

section

@[expose] public section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical
noncomputable section
namespace GlobalTheory.CuspGK
variable {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) {V : HSp D} {S : D.what₂.Tau → SPar}
  (M : Formalism.IndefR.Mult.DSModel V S)
theorem cuspForm_mem_iSup_irreducible_gK : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)
    (S : D.what₂.Tau → SPar) (M : Formalism.IndefR.Mult.DSModel V S), IsInfFam (D := D) θ →
    ∀ ψ : GA D V → ℂ, IsAutFunSm θ V ψ → IsCuspFun V ψ →
    (∃ W : Submodule ℂ (GA D V → ℂ), FiniteDimensional ℂ W ∧ ψ ∈ W ∧ ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ),
      M.fr τ * g * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ) → ∀ f ∈ W, rTr V (atTau θ V τ g) f ∈ W) →
    ψ ∈ ⨆ (A : Submodule ℂ (GA D V → ℂ)) (_ : A ≤ GlobalTheory.CuspGK.gkGen θ M ψ ∧ GlobalTheory.CuspGK.IsIrrGKSub θ M A), A := by
  intro hP D θ V S M hθ ψ hA hC hW
  obtain ⟨b, hpos, hherm, hK, hL⟩ := _root_.GlobalTheory.T.cusp_form_petersson_nonvanishing_gelfandKirillov hP θ V S M hθ ψ hA hC hW
  obtain ⟨e, he1, he2, he3, he4, he5⟩ := _root_.GlobalTheory.T.kType_projection_of_kFinite hP θ V S M hθ ψ hA hC hW b hpos hherm hK hL
  refine GlobalTheory.T.mem_iSup_irreducible_of_fixed_projector (IsGKSub θ M) (isGKSub_sInf θ M) (gkGen θ M ψ) (isGKSub_gkGen θ M ψ) b
    hpos hherm (fun A hAle hAP => ?_) e he2 he3 he4 he5 ψ (mem_gkGen θ M ψ) he1
  have hperp : ∀ f ∈ gkGen θ M ψ ⊓ ⨅ a ∈ A, LinearMap.ker (b a),
      f ∈ gkGen θ M ψ ∧ ∀ a ∈ A, b a f = 0 := fun f hf => by
    rw [Submodule.mem_inf] at hf
    exact ⟨hf.1, fun a ha => LinearMap.mem_ker.1 ((Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hf.2 a) ha)⟩
  have hmk : ∀ f, f ∈ gkGen θ M ψ → (∀ a ∈ A, b a f = 0) → f ∈ gkGen θ M ψ ⊓ ⨅ a ∈ A, LinearMap.ker (b a) :=
    fun f h1 h2 => Submodule.mem_inf.2 ⟨h1, (Submodule.mem_iInf _).2 fun a => (Submodule.mem_iInf _).2 fun ha =>
      LinearMap.mem_ker.2 (h2 a ha)⟩
  refine ⟨fun τ g hg f hf => ?_, fun τ X hX f hf => ?_⟩
  · obtain ⟨hfN, hf0⟩ := hperp f hf
    refine hmk _ ((isGKSub_gkGen θ M ψ).k τ g hg f hfN) fun a ha => ?_
    rw [hK τ g hg a (hAle ha) f hfN]
    exact hf0 _ (hAP.k τ g⁻¹ hg.inv a ha)
  · obtain ⟨hfN, hf0⟩ := hperp f hf
    refine hmk _ ((isGKSub_gkGen θ M ψ).lie τ X hX f hfN) fun a ha => ?_
    rw [hL τ X hX a (hAle ha) f hfN, hf0 _ (hAP.lie τ X hX a ha), neg_zero]
end GlobalTheory.CuspGK
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical

theorem _root_.GlobalTheory.T.cuspForms_eq_iSup_irreducible_gK : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)
    (S : D.what₂.Tau → SPar) (M : Formalism.IndefR.Mult.DSModel V S), IsInfFam (D := D) θ →
    ∀ ψ : GA D V → ℂ, IsAutFunSm θ V ψ → IsCuspFun V ψ →
    (∃ W : Submodule ℂ (GA D V → ℂ), FiniteDimensional ℂ W ∧ ψ ∈ W ∧ ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ),
      M.fr τ * g * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ) → ∀ f ∈ W, rTr V (atTau θ V τ g) f ∈ W) →
    ψ ∈ ⨆ (A : Submodule ℂ (GA D V → ℂ)) (_ : A ≤ GlobalTheory.CuspGK.gkGen θ M ψ ∧ GlobalTheory.CuspGK.IsIrrGKSub θ M A), A := by
  first | exact @_root_.GlobalTheory.CuspGK.cuspForm_mem_iSup_irreducible_gK | exact _root_.GlobalTheory.CuspGK.cuspForm_mem_iSup_irreducible_gK | (intros; apply _root_.GlobalTheory.CuspGK.cuspForm_mem_iSup_irreducible_gK <;> assumption)
end
end
end
